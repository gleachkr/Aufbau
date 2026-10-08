const std = @import("std");
const TemplateExpr = @import("./rules.zig").TemplateExpr;
const Expr = @import("../trusted/expressions.zig").Expr;
const AssertionStmt = @import("parse_recovery.zig").AssertionStmt;
const ArgInfo = @import("parse_recovery.zig").ArgInfo;
const MM0Parser = @import("parse_recovery.zig").MM0Parser;
const TermStmt = @import("parse_recovery.zig").TermStmt;

pub const ExprId = u32;
pub const TheoremVarId = u32;
pub const DummyVarId = u32;
pub const PlaceholderId = u32;
pub const tracked_bound_dep_limit: u32 = @bitSizeOf(u55);

pub const VarId = union(enum) {
    theorem_var: TheoremVarId,
    dummy_var: DummyVarId,

    /// Stable `u64` key for indexing a VarId in a hash map (name tables, the
    /// used-set). The two tags occupy disjoint key spaces. Shared by the search
    /// `Namer` and the diagnostic `DiagNames` so the encoding lives in one place.
    pub fn hashKey(self: VarId) u64 {
        return switch (self) {
            .theorem_var => |idx| @as(u64, idx),
            .dummy_var => |idx| (@as(u64, 1) << 32) | @as(u64, idx),
        };
    }
};

pub const ExprNode = union(enum) {
    variable: VarId,
    placeholder: PlaceholderId,
    app: App,

    pub const App = struct {
        term_id: u32,
        args: []const ExprId,
    };
};

pub const DummyInfo = struct {
    sort_name: []const u8,
    sort_id: u8,
    deps: u55,
};

/// Discriminates the two users of the shared `PlaceholderId` space (META.md
/// Stage 2 id-space decision: one counter, a class field, no reserved ranges).
///
/// - `standard`: the historical frontend placeholder — a bound-variable
///   stand-in or witness that consumes a synthetic dep bit from the shared
///   u55 mask space (`addPlaceholderResolved`).
/// - `meta`: a search metavariable leaf minted without consuming a dep bit
///   (`addMetaPlaceholderResolved`); a reconciliation seed meta reuses the
///   bit of the hidden variable it stands for. Its assignment state lives in the
///   branch-local `MetaStore` (`compiler/inference/meta_store.zig`), never in
///   the interner node. Search-scale minting must not consume dep bits, and
///   rigid `.placeholder` matching arms / the emission leakage guard need to
///   tell the two apart.
pub const PlaceholderClass = enum {
    standard,
    meta,
};

/// What a placeholder leaf stands for, read off its `PlaceholderInfo` (see
/// `TheoremContext.placeholderKind`). The three meta kinds are exclusive by
/// construction: each mint path sets at most one of `reconciliation_meta` and
/// `meta_id`.
pub const PlaceholderKind = enum {
    /// A def-unfold dummy: the one `.standard` kind.
    dummy,
    /// An eliminator seed meta standing for a def's hidden variable
    /// (`reconciliation_meta`).
    seed_meta,
    /// A search metavariable with a stable `meta_id` (a `MetaStore` leaf).
    store_meta,
    /// Any other `.meta` leaf: an anonymous hole.
    hole,
};

pub const PlaceholderInfo = struct {
    sort_name: []const u8,
    deps: u55,
    class: PlaceholderClass = .standard,
    /// Stable cross-interner identity of a search metavariable, allocated from
    /// the owning `MetaStore`'s global counter. Unlike the interner-local
    /// `PlaceholderId` (a dense array index that `clone()` reuses across sibling
    /// clones), this survives cloning *and* cross-interner reinterning, so one
    /// shared `MetaStore` can key a meta consistently wherever its leaf appears
    /// (the carry-to-leaf witness channel). Null for non-search placeholders.
    meta_id: ?u64 = null,
    /// True for an eliminator-reconciliation seed meta: a `.meta` leaf that
    /// `makeExactRuleCandidate` minted to replace a def-unfold dummy the seed
    /// keeps (see `seed.partitionSeedBindings`). It stands for that dummy's
    /// variable, so it keeps the dummy's dep bit and leaf info reports it as
    /// bound (a substitution over it reduces as over the dummy).
    /// The meta-aware hypothesis match (`match.tryMetaAwareHypMatch`) keys
    /// on this so it resolves *only* these — never upstream carry-to-leaf/witness
    /// metas, which must stay deferred to leaf forcing. Travels with the leaf
    /// across `clone()`, so no candidate-side bookkeeping is needed.
    reconciliation_meta: bool = false,
    /// True for a `.bound_choice` search meta: it stands for a bound
    /// variable not yet named, so leaf info reports it bound with its own
    /// dependency bit, and a substitution over it reduces as over that
    /// variable (`MetaStore.mintBoundVar`).
    bound_var: bool = false,
    /// True for a hole the checker put in an inline sub-proof's expected goal
    /// (`addLineHolePlaceholder`): a line's hole or a binder the holey line
    /// leaves open. An anonymous meta otherwise; the flag tells the checker
    /// such a hint from one carrying search metas.
    line_hole: bool = false,
};

pub const ExprLeafInfo = struct {
    sort_name: []const u8,
    bound: bool,
    deps: u55,
};

/// The interner index stores ids; each overlay node's `hashExprNode` sits
/// beside it in `ExprInterner.hashes`, so neither an insert nor a grow
/// rehashes a node.
const IdContext = struct {
    interner: *const ExprInterner,

    pub fn hash(self: IdContext, id: ExprId) u64 {
        const interner = self.interner;
        return interner.hashes.items[@intCast(id - interner.base_count)];
    }

    pub fn eql(_: IdContext, a: ExprId, b: ExprId) bool {
        return a == b;
    }
};

/// Probes the index for a node with its hash computed once up front.
const NodeAdapter = struct {
    interner: *const ExprInterner,
    value: u64,

    pub fn hash(self: NodeAdapter, _: ExprNode) u64 {
        return self.value;
    }

    pub fn eql(self: NodeAdapter, key: ExprNode, id: ExprId) bool {
        return eqlExprNode(key, self.interner.node(id).*);
    }
};

const ExprIdIndex = std.HashMapUnmanaged(
    ExprId,
    void,
    IdContext,
    std.hash_map.default_max_load_percentage,
);

/// Deterministic work counters: machine-independent proxies for wall-clock
/// work, consumed by the `auto?` generation driver's global per-call budget
/// (`search/types.zig` `GlobalBudget`) and reported by the bench. Wrapping
/// arithmetic because only deltas are meaningful.
///
/// `work_ticks` counts intern probe levels (one per copy-on-write base-chain
/// hop of every lookup, hit or miss) across every `ExprInterner` on this
/// thread — the chokepoint all concrete-expression work funnels through,
/// weighted by how deep the clone chain actually made each lookup.
/// `work_ticks_sym` counts symbolic-node allocations in the def-eq engine
/// (`symbolic_engine.zig` `allocSymbolic`) — the chokepoint of
/// def-unfold/ACUI cascade work, which barely interns. The op populations
/// have different unit costs, so the budget combines them weighted (see
/// `GlobalBudget`).
/// `work_ticks_walk` counts per-node visits of the non-interning tree walks:
/// the shape builder (`search/shape.zig`), the open-generation meta walks
/// (`match.registerMetasInExpr`, `MetaStore.deref`/`hasUnsolvedMeta`),
/// suggestion rendering (`pretty_print.renderNode`), and the inference
/// solver's branch clones and structural-congruence compares
/// (`inference_solver/branch_state.zig`, `congruence.zig`).
pub threadlocal var work_ticks: u64 = 0;
pub threadlocal var work_ticks_sym: u64 = 0;
pub threadlocal var work_ticks_walk: u64 = 0;

/// A ceiling over the ticks above that a budgeted search installs for the
/// duration of one call (`search/types.zig` `GlobalBudget.workBudget`). The
/// search itself checks its budget only between candidates, so a subsystem
/// whose work per candidate is not naturally bounded — the inference solver's
/// branch fan-out and the pairwise compares that dedup it — polls this at
/// its own unit of work and aborts with `error.SearchBudgetExhausted`, which
/// the search reports the way it reports its own exhaustion. Absent outside
/// a budgeted search, so ordinary compilation never pays for a check.
pub const WorkBudget = struct {
    ctx: *anyopaque,
    check_fn: *const fn (ctx: *anyopaque) error{SearchBudgetExhausted}!void,

    pub fn check(self: WorkBudget) error{SearchBudgetExhausted}!void {
        return self.check_fn(self.ctx);
    }
};

pub const ExprInterner = struct {
    allocator: std.mem.Allocator,
    /// Copy-on-write base. A clone borrows its parent as an immutable prefix
    /// (ids `0..base_count`) and only stores newly interned nodes in its own
    /// `nodes`/`index` overlay (ids `>= base_count`). This makes `clone` O(1):
    /// cloning a theorem to try a candidate no longer copies+rehashes the whole
    /// interner, which dominated `auto?` search cost.
    ///
    /// Soundness: every clone is short-lived scratch whose parent outlives it
    /// and does not move while it is alive (all call sites follow
    /// `var c = try t.clone(); defer c.deinit();`). The interner is append-only,
    /// so base ids never change. The base MAY keep growing after a clone is
    /// taken (e.g. the shared `work_theorem` in recursive generation):
    /// `findHashed` hides any base node added after the clone with the
    /// `< base_count` range check, so the clone's id-space stays a stable
    /// snapshot.
    base: ?*const ExprInterner = null,
    base_count: ExprId = 0,
    nodes: std.ArrayListUnmanaged(ExprNode) = .{},
    /// `hashExprNode` of each overlay node, aligned with `nodes`.
    hashes: std.ArrayListUnmanaged(u64) = .{},
    index: ExprIdIndex = .empty,

    pub fn init(allocator: std.mem.Allocator) ExprInterner {
        return .{ .allocator = allocator };
    }

    pub fn deinit(self: *ExprInterner) void {
        // Only the overlay nodes are owned; base nodes belong to the parent.
        for (self.nodes.items) |expr_node| {
            switch (expr_node) {
                .variable, .placeholder => {},
                .app => |app| self.allocator.free(app.args),
            }
        }
        self.nodes.deinit(self.allocator);
        self.hashes.deinit(self.allocator);
        self.index.deinit(self.allocator);
    }

    /// O(1) copy-on-write clone: borrow `self` as an immutable base prefix.
    pub fn clone(self: *const ExprInterner) !ExprInterner {
        return .{
            .allocator = self.allocator,
            .base = self,
            .base_count = std.math.cast(ExprId, self.count()) orelse
                return error.TooManyTheoremExprs,
        };
    }

    /// Materialize a copy-on-write clone into a standalone interner (base =
    /// null), deep-copying every base node into the overlay. Required before a
    /// clone is *promoted* to replace its own base (the line-commit pattern
    /// `theorem.* = clone; old.deinit()`): without this the moved clone's `base`
    /// would point at its own freed storage. A no-op for an already-standalone
    /// interner. Cost is one full copy, paid per committed line (rare), not per
    /// search candidate.
    pub fn flatten(self: *ExprInterner) !void {
        if (self.base == null) return;
        const total = self.count();
        var fresh = ExprInterner.init(self.allocator);
        errdefer fresh.deinit();
        try fresh.nodes.ensureTotalCapacity(self.allocator, total);
        try fresh.hashes.ensureTotalCapacity(self.allocator, total);
        try fresh.index.ensureTotalCapacityContext(
            self.allocator,
            @intCast(total),
            .{ .interner = &fresh },
        );
        var id: ExprId = 0;
        while (id < total) : (id += 1) {
            const original = self.node(id).*;
            const cloned: ExprNode = switch (original) {
                .variable, .placeholder => original,
                .app => |app| .{ .app = .{
                    .term_id = app.term_id,
                    .args = try self.allocator.dupe(ExprId, app.args),
                } },
            };
            errdefer switch (cloned) {
                .variable, .placeholder => {},
                .app => |app| self.allocator.free(app.args),
            };
            fresh.nodes.appendAssumeCapacity(cloned);
            fresh.hashes.appendAssumeCapacity(hashExprNode(cloned));
            fresh.index.putAssumeCapacityNoClobberContext(
                id,
                {},
                .{ .interner = &fresh },
            );
        }
        self.deinit(); // frees only this clone's overlay; base is borrowed
        self.* = fresh;
    }

    pub fn count(self: *const ExprInterner) usize {
        return @as(usize, self.base_count) + self.nodes.items.len;
    }

    pub fn node(self: *const ExprInterner, id: ExprId) *const ExprNode {
        if (id < self.base_count) return self.base.?.node(id);
        return &self.nodes.items[@intCast(id - self.base_count)];
    }

    /// Canonical id for `key` (whose `hashExprNode` is `hash`) if already
    /// interned anywhere in this interner's id-space, else null. Checks the
    /// overlay, then walks the base chain, hiding base nodes added after this
    /// clone was taken (`< base_count`).
    fn findHashed(self: *const ExprInterner, key: ExprNode, hash: u64) ?ExprId {
        // One work tick per PROBE LEVEL (not per intern attempt): a lookup
        // through a deep copy-on-write base chain probes every level, so
        // per-hop counting is what tracks the real cost (see `work_ticks`).
        work_ticks +%= 1;
        if (self.index.getKeyAdapted(key, NodeAdapter{
            .interner = self,
            .value = hash,
        })) |id| return id;
        if (self.base) |b| {
            if (b.findHashed(key, hash)) |r| {
                if (r < self.base_count) return r;
            }
        }
        return null;
    }

    pub fn internVar(self: *ExprInterner, var_id: VarId) !ExprId {
        return try self.internNode(.{ .variable = var_id });
    }

    pub fn internPlaceholder(
        self: *ExprInterner,
        placeholder_id: PlaceholderId,
    ) !ExprId {
        return try self.internNode(.{ .placeholder = placeholder_id });
    }

    pub fn internApp(
        self: *ExprInterner,
        term_id: u32,
        args: []const ExprId,
    ) !ExprId {
        const owned = try self.allocator.dupe(ExprId, args);
        errdefer self.allocator.free(owned);
        return try self.internAppOwned(term_id, owned);
    }

    /// Intern an application whose `args` slice the caller allocated with
    /// this interner's allocator. On success the interner owns `args` (it is
    /// freed at once if an equal node already exists); on error the caller
    /// still owns it.
    pub fn internAppOwned(
        self: *ExprInterner,
        term_id: u32,
        args: []ExprId,
    ) !ExprId {
        const key = ExprNode{
            .app = .{
                .term_id = term_id,
                .args = args,
            },
        };
        const hash = hashExprNode(key);
        if (self.findHashed(key, hash)) |id| {
            self.allocator.free(args);
            return id;
        }
        return try self.insertNew(key, hash);
    }

    /// Append `key`, known absent, with its precomputed hash.
    fn insertNew(self: *ExprInterner, key: ExprNode, hash: u64) !ExprId {
        const id = std.math.cast(ExprId, self.count()) orelse {
            return error.TooManyTheoremExprs;
        };
        try self.nodes.append(self.allocator, key);
        errdefer _ = self.nodes.pop();
        try self.hashes.append(self.allocator, hash);
        errdefer _ = self.hashes.pop();
        try self.index.putNoClobberContext(
            self.allocator,
            id,
            {},
            .{ .interner = self },
        );
        return id;
    }

    fn internNode(self: *ExprInterner, key: ExprNode) !ExprId {
        const hash = hashExprNode(key);
        if (self.findHashed(key, hash)) |id| return id;
        return try self.insertNew(key, hash);
    }
};

/// The theorem-lifetime def_ops verdict memos key on the match mode as well
/// as the exprs: under `line_holes_match_anything` a line hole matches
/// anything, so a pair holding one has a different verdict there.
pub const DefCacheKey = struct {
    def_expr: ExprId,
    target_expr: ExprId,
    has_registry: bool,
    line_holes_match_anything: bool,
};

pub const AcuiCacheKey = struct {
    def_expr: ExprId,
    item_expr: ExprId,
    head_term_id: u32,
    has_registry: bool,
    line_holes_match_anything: bool,
};

/// Key for `TheoremContext.pure_reprs`. A representative also depends on the
/// match mode and on the registry, which canonicalizes it when present.
pub const PureReprKey = struct {
    expr: ExprId,
    normalized: bool,
    has_registry: bool,
    line_holes_match_anything: bool,
};

pub const TheoremContext = struct {
    allocator: std.mem.Allocator,
    interner: ExprInterner,
    parser_vars: std.AutoHashMapUnmanaged(*const Expr, VarId) = .empty,
    arg_infos: []const ArgInfo = &.{},
    theorem_vars: std.ArrayListUnmanaged(ExprId) = .{},
    theorem_hyps: std.ArrayListUnmanaged(ExprId) = .{},
    /// Borrowed from the parsed assertion (parser-arena-owned), aligned with
    /// `theorem_hyps`: binder names for binder-form hypotheses, null for
    /// arrow-form ones.
    theorem_hyp_names: []const ?[]const u8 = &.{},
    theorem_dummies: std.ArrayListUnmanaged(DummyInfo) = .{},
    theorem_placeholders: std.ArrayListUnmanaged(PlaceholderInfo) = .{},
    next_dummy_id: DummyVarId = 0,
    next_placeholder_id: PlaceholderId = 0,
    // Placeholder deps are frontend-only synthetic masks. They must stay
    // disjoint from real theorem dep bits because internal matching and
    // freshening code still reasons over one shared u55 dep universe.
    next_placeholder_dep: u32 = 0,
    next_dummy_dep: u32 = 0,
    /// Count of `.meta`-class placeholders ever minted in this context, line
    /// holes aside. Lets meta-aware matching short-circuit to "no metas
    /// anywhere" in O(1) for ordinary theorems (everything outside Stage 4
    /// open search).
    meta_placeholder_count: u32 = 0,
    /// True once a line hole is minted (`PlaceholderInfo.line_hole`). Kept
    /// apart from `meta_placeholder_count`, which the search gates read on
    /// its own (`hasMetaPlaceholders`).
    has_line_holes: bool = false,
    /// Count of `reconciliation_meta`-flagged placeholders ever minted (a subset
    /// of `meta_placeholder_count`). Lets the eliminator meta-aware match gate
    /// out candidates that carry *only* carry-to-leaf/witness metas (common —
    /// drinker/rex) in O(1), without a per-binding scan.
    reconciliation_meta_count: u32 = 0,

    /// def_ops transparent-match memoization assumes a theorem context is used
    /// with one fixed `GlobalEnv`. Registry absence/presence is part of the
    /// cache key, but all non-null registry uses must share one pointer.
    /// `assertDefOpsCacheIdentity` records the first actual identities and
    /// asserts later cached queries respect them. Clones start empty, so they
    /// establish their own identities on first use.
    def_ops_cache_env_identity_set: bool = false,
    def_ops_cache_env_addr: usize = 0,
    def_ops_cache_registry_addr: usize = 0,

    /// Pure memo for `instantiateDefTowardExpr` (def_ops transparent match).
    /// That query is pure in `(def_expr, target_expr)` under the fixed
    /// env/registry invariant above. It spins up a fresh empty `MatchSession`
    /// each call. Transient `def_ops.Context`s that ACUI common-target building
    /// creates per leaf-pair otherwise re-derive the same answers millions of
    /// times. Cleared on `clone` (correctness-neutral; drops memo benefit).
    instantiate_def_cache: std.AutoHashMapUnmanaged(DefCacheKey, ?ExprId) = .empty,

    /// Negative memo for `compareTransparent`: set of `(lhs, rhs)` pairs known
    /// to be NOT def-equal under the fixed env/registry invariant above. The
    /// doomed-match verdict is the expensive, pure part; positive plans are
    /// recomputed (they are request-arena pointers). Cleared on `clone`.
    compare_transparent_neg: std.AutoHashMapUnmanaged(DefCacheKey, void) = .empty,

    /// Pure memo for `instantiateDefTowardAcuiItem` (def coverage of an ACUI
    /// set member). Same rationale as `instantiate_def_cache`; keyed by the
    /// def/item exprs plus the ACUI head term. Cleared on `clone`.
    instantiate_acui_cache: std.AutoHashMapUnmanaged(AcuiCacheKey, ?ExprId) = .empty,

    /// Pure memo for `acui_support.Context.isDefBearing` ("does this expr
    /// contain a concrete-def term anywhere?"), populated per visited node so
    /// the hash-consed DAG is walked once instead of once per common-target
    /// probe. Pure in the expr under the fixed-env invariant above (the term
    /// table only changes between statements). Cleared on `clone`.
    def_bearing_cache: std.AutoHashMapUnmanaged(ExprId, bool) = .empty,

    /// Memo for `firstPlaceholder` (the checked-IR leakage walk and the def_ops
    /// pure-representative gate): the first placeholder id found under an app
    /// node in pre-order, or null when the subtree is placeholder-free. Node
    /// structure is immutable per id, so entries never go stale. Populated per
    /// visited node — the validation walks otherwise re-walk hash-consed
    /// shared subtrees once per occurrence (a line's rule bindings are
    /// subtrees of the line expr, so every per-candidate validation pays that
    /// at least twice). Cleared on `clone`.
    placeholder_scan_cache: std.AutoHashMapUnmanaged(ExprId, ?PlaceholderId) = .empty,

    /// Memo for `binding_validation.currentExprInfoCached`: dep mask of an app
    /// node under the CURRENT `arg_infos`. Valid for the context's lifetime:
    /// leaf deps (theorem args, dummies, placeholders) are assigned at mint
    /// and never updated, and an app's mask is the OR of its leaves. Only the
    /// current-args entry point may use it (`exprInfo` with caller-supplied
    /// binder infos stays uncached). Cleared on `clone`.
    expr_deps_cache: std.AutoHashMapUnmanaged(ExprId, u55) = .empty,

    /// def_ops representative memo: a placeholder-free expr → its plain
    /// representative, under the fixed env/registry invariant above. Such a
    /// representative reads no match-session state, so every def_ops context
    /// on this theorem computes the same one; keeping it here shares it
    /// across proof lines (`SharedContext.pureRepresentativeGet`). Cleared on
    /// `clone`.
    pure_reprs: std.AutoHashMapUnmanaged(PureReprKey, ExprId) = .empty,

    pub fn init(allocator: std.mem.Allocator) TheoremContext {
        return .{
            .allocator = allocator,
            .interner = ExprInterner.init(allocator),
        };
    }

    pub fn deinit(self: *TheoremContext) void {
        self.interner.deinit();
        self.theorem_vars.deinit(self.allocator);
        self.theorem_hyps.deinit(self.allocator);
        self.theorem_dummies.deinit(self.allocator);
        self.theorem_placeholders.deinit(self.allocator);
        self.parser_vars.deinit(self.allocator);
        self.instantiate_def_cache.deinit(self.allocator);
        self.compare_transparent_neg.deinit(self.allocator);
        self.instantiate_acui_cache.deinit(self.allocator);
        self.def_bearing_cache.deinit(self.allocator);
        self.placeholder_scan_cache.deinit(self.allocator);
        self.expr_deps_cache.deinit(self.allocator);
        self.pure_reprs.deinit(self.allocator);
    }

    pub fn assertDefOpsCacheIdentity(
        self: *TheoremContext,
        env_addr: usize,
        registry_addr: usize,
    ) void {
        if (!self.def_ops_cache_env_identity_set) {
            self.def_ops_cache_env_identity_set = true;
            self.def_ops_cache_env_addr = env_addr;
        } else {
            std.debug.assert(self.def_ops_cache_env_addr == env_addr);
        }

        // Null/non-null registry use is already separated by the cache key.
        // For non-null registries, assert that all cached queries see the same
        // registry instance; otherwise a bool key would be too coarse.
        if (registry_addr == 0) return;
        if (self.def_ops_cache_registry_addr == 0) {
            self.def_ops_cache_registry_addr = registry_addr;
            return;
        }
        std.debug.assert(self.def_ops_cache_registry_addr == registry_addr);
    }

    pub fn clone(self: *const TheoremContext) !TheoremContext {
        var copy = TheoremContext.init(self.allocator);
        errdefer copy.deinit();

        copy.interner = try self.interner.clone();
        copy.arg_infos = self.arg_infos;
        copy.theorem_hyp_names = self.theorem_hyp_names;
        try copy.theorem_vars.appendSlice(
            self.allocator,
            self.theorem_vars.items,
        );
        try copy.theorem_hyps.appendSlice(
            self.allocator,
            self.theorem_hyps.items,
        );
        try copy.theorem_dummies.appendSlice(
            self.allocator,
            self.theorem_dummies.items,
        );
        try copy.theorem_placeholders.appendSlice(
            self.allocator,
            self.theorem_placeholders.items,
        );
        copy.next_dummy_id = self.next_dummy_id;
        copy.next_placeholder_id = self.next_placeholder_id;
        copy.next_placeholder_dep = self.next_placeholder_dep;
        copy.next_dummy_dep = self.next_dummy_dep;
        copy.meta_placeholder_count = self.meta_placeholder_count;
        copy.has_line_holes = self.has_line_holes;
        copy.reconciliation_meta_count = self.reconciliation_meta_count;

        try copy.parser_vars.ensureTotalCapacity(
            self.allocator,
            self.parser_vars.count(),
        );
        var it = self.parser_vars.iterator();
        while (it.next()) |entry| {
            try copy.parser_vars.put(
                self.allocator,
                entry.key_ptr.*,
                entry.value_ptr.*,
            );
        }
        return copy;
    }

    /// Materialize a copy-on-write clone into a standalone theorem. Call before
    /// promoting a clone to replace its own base (see `ExprInterner.flatten`).
    pub fn flatten(self: *TheoremContext) !void {
        try self.interner.flatten();
    }

    // Seed a context with `count` theorem binders but without any parser-side
    // `Expr*` nodes. This is used when we need a temporary binder-indexed DAG,
    // for example to rebuild a rule's unify stream for argument inference.
    pub fn seedBinderCount(
        self: *TheoremContext,
        count: usize,
    ) !void {
        for (0..count) |idx| {
            const var_id = VarId{
                .theorem_var = std.math.cast(TheoremVarId, idx) orelse {
                    return error.TooManyTheoremVars;
                },
            };
            const expr_id = try self.interner.internVar(var_id);
            try self.theorem_vars.append(self.allocator, expr_id);
        }
    }

    pub fn seedArgs(
        self: *TheoremContext,
        arg_infos: []const ArgInfo,
        arg_exprs: []const *const Expr,
    ) !void {
        self.arg_infos = arg_infos;
        // Deps memoized under the previous arg_infos (if any) are stale now,
        // and so are representatives, whose def compression reads deps.
        self.expr_deps_cache.clearRetainingCapacity();
        self.pure_reprs.clearRetainingCapacity();
        try self.seedBinderCount(arg_exprs.len);
        var next_bound_dep: u32 = 0;
        for (arg_infos) |arg| {
            if (arg.bound) next_bound_dep += 1;
        }
        self.next_dummy_dep = next_bound_dep;
        for (arg_exprs, 0..) |arg_expr, idx| {
            try self.parser_vars.put(
                self.allocator,
                arg_expr,
                .{ .theorem_var = @intCast(idx) },
            );
        }
    }

    pub fn seedTerm(self: *TheoremContext, parser: *const MM0Parser, stmt: TermStmt) !void {
        try self.seedArgs(stmt.args, stmt.arg_exprs);
        // Explicit source allocation: dummies declared in the .mm0 source term definition.
        for (stmt.dummy_args, stmt.dummy_exprs) |arg, expr| {
            const dummy_var_id = try self.addDummyVar(parser, arg);
            const var_id = self.interner.node(dummy_var_id).*.variable;
            try self.parser_vars.put(self.allocator, expr, var_id);
        }
    }

    pub fn seedAssertion(
        self: *TheoremContext,
        stmt: AssertionStmt,
    ) !void {
        try self.seedArgs(stmt.args, stmt.arg_exprs);
        for (stmt.hyps) |hyp| {
            const hyp_id = try self.internParsedExpr(hyp);
            try self.theorem_hyps.append(self.allocator, hyp_id);
        }
        self.theorem_hyp_names = stmt.hyp_names;
    }

    pub fn addDummyVar(
        self: *TheoremContext,
        parser: *const MM0Parser,
        arg: ArgInfo,
    ) !ExprId {
        const sort_id = parser.core.sort_names.get(arg.sort_name) orelse {
            return error.UnknownSort;
        };
        return try self.addDummyVarResolved(arg.sort_name, sort_id);
    }

    /// Allocate a fresh theorem-local dummy variable. This is the low-level
    /// API that all dummy allocation routes through. It is intentionally kept
    /// for legitimate use cases:
    ///
    /// - Explicit source/user dummies: seedTerm in this file for dot binders
    ///   declared in .mm0, plus named theorem-local vars created through
    ///   @vars / @fresh when a proof line needs them.
    /// - Temporary mirror-context dummies in def_ops for copied real dummies.
    ///
    /// The accidental allocation site,
    /// materializeEscapingWitnessForDummySlot in
    /// def_ops/symbolic_engine.zig, is the footgun targeted for removal
    /// (see PLAN.md).
    /// Do NOT remove this API; only remove the accidental caller.
    fn ensureDepMaskCapacity(self: *const TheoremContext) !void {
        if (self.depSlotsLeft() == 0) return error.DependencySlotExhausted;
    }

    /// How many more dummies and placeholders the theorem can allocate, each
    /// spending one dependency bit, before `DependencySlotExhausted`.
    pub fn depSlotsLeft(self: *const TheoremContext) u32 {
        return tracked_bound_dep_limit -| (self.next_dummy_dep +| self.next_placeholder_dep);
    }

    pub fn addDummyVarResolved(
        self: *TheoremContext,
        sort_name: []const u8,
        sort_id: u8,
    ) !ExprId {
        try self.ensureDepMaskCapacity();

        const dummy_id = self.next_dummy_id;
        self.next_dummy_id = try std.math.add(DummyVarId, dummy_id, 1);
        try self.theorem_dummies.append(self.allocator, .{
            .sort_name = sort_name,
            .sort_id = sort_id,
            .deps = @as(u55, 1) << @intCast(self.next_dummy_dep),
        });
        self.next_dummy_dep = try std.math.add(u32, self.next_dummy_dep, 1);
        return try self.interner.internVar(.{ .dummy_var = dummy_id });
    }

    /// The placeholder dependency slots taken so far, for `releaseDepSlots`.
    pub fn depSlotMark(self: *const TheoremContext) u32 {
        return self.next_placeholder_dep;
    }

    /// Take here the placeholder dependency slot behind `deps`, a bit `src`
    /// minted and a placeholder copied in from it keeps (`reinternHint`), so
    /// no later mint here reuses the bit. A dummy's bit holds no slot.
    pub fn holdDepSlotFrom(
        self: *TheoremContext,
        src: *const TheoremContext,
        deps: u55,
    ) !void {
        if (deps == 0 or @ctz(deps) < src.next_dummy_dep) return;
        std.debug.assert(@popCount(deps) == 1);
        const slot = placeholderDepSlotBit(@ctz(deps));
        if (slot < self.next_placeholder_dep) return;
        if (self.next_dummy_dep +| slot >= tracked_bound_dep_limit) {
            return error.DependencySlotExhausted;
        }
        self.next_placeholder_dep = slot + 1;
    }

    /// Give back every placeholder dependency slot taken since `mark`. Only a
    /// probe that returns a verdict may call this: the placeholders it minted
    /// stay interned, but nothing may hold one, since the next mint reuses its
    /// dependency bit.
    pub fn releaseDepSlots(self: *TheoremContext, mark: u32) void {
        std.debug.assert(mark <= self.next_placeholder_dep);
        self.next_placeholder_dep = mark;
    }

    /// Give back the placeholder dependency slots taken since `mark` except
    /// those a placeholder under `roots` still holds, its own or a copy
    /// (`addReconciliationMetaPlaceholderResolved`). Slots go out in order, so
    /// this keeps every slot up to the newest one held. Only for a caller that
    /// holds its placeholders through `roots` alone.
    pub fn releaseUnheldDepSlots(
        self: *TheoremContext,
        mark: u32,
        roots: []const []const ?ExprId,
    ) void {
        if (self.next_placeholder_dep == mark) return;
        var held = HeldDepSlots{ .count = mark };
        walk: for (roots) |group| for (group) |root| {
            // Stop once every slot since `mark` is held.
            if (self.exprAny(root orelse continue, &held, HeldDepSlots.visit)) break :walk;
        };
        self.releaseDepSlots(held.count);
    }

    const HeldDepSlots = struct {
        count: u32,

        /// Raise `count` past the slot `expr` holds; true once every slot is held.
        fn visit(self: *HeldDepSlots, theorem: *const TheoremContext, expr: ExprId) bool {
            const pid = switch (theorem.interner.node(expr).*) {
                .placeholder => |pid| pid,
                else => return false,
            };
            const deps = (theorem.placeholderInfo(pid) orelse return false).deps;
            if (deps == 0) return false;
            // A placeholder's bit is always one placeholder slot's, its own or
            // a copy; a slot at or past the count is one a probe gave back.
            std.debug.assert(@popCount(deps) == 1);
            const slot = placeholderDepSlotBit(@ctz(deps));
            std.debug.assert(slot < theorem.next_placeholder_dep);
            self.count = @max(self.count, slot + 1);
            return self.count == theorem.next_placeholder_dep;
        }
    };

    /// Placeholder dependency slot `k` holds bit `tracked_bound_dep_limit - 1 -
    /// k`: slots fill the mask from the top, theorem dummies from the bottom.
    /// The map is its own inverse, so it also takes a bit to its slot.
    fn placeholderDepSlotBit(slot_or_bit: u32) u32 {
        return tracked_bound_dep_limit - 1 - slot_or_bit;
    }

    /// Allocate a frontend-only placeholder. These never reach emission, but
    /// they still participate in internal dep-sensitive matching and freshening
    /// logic. So they get synthetic dep bits from the top of the same u55 mask
    /// space while remaining disjoint from real theorem dep bookkeeping.
    pub fn addPlaceholderResolved(
        self: *TheoremContext,
        sort_name: []const u8,
    ) !ExprId {
        const deps = try self.takePlaceholderDep();
        const placeholder_id = self.next_placeholder_id;
        self.next_placeholder_id = try std.math.add(
            PlaceholderId,
            placeholder_id,
            1,
        );
        try self.theorem_placeholders.append(self.allocator, .{
            .sort_name = sort_name,
            .deps = deps,
        });
        return try self.interner.internPlaceholder(placeholder_id);
    }

    /// Spend one synthetic placeholder dependency bit (see
    /// `addPlaceholderResolved`) and return it as a mask.
    pub fn takePlaceholderDep(self: *TheoremContext) !u55 {
        try self.ensureDepMaskCapacity();
        const dep_bit = placeholderDepSlotBit(self.next_placeholder_dep);
        self.next_placeholder_dep = try std.math.add(
            u32,
            self.next_placeholder_dep,
            1,
        );
        return @as(u55, 1) << @intCast(dep_bit);
    }

    /// Allocate a bound-variable search meta (`PlaceholderInfo.bound_var`)
    /// standing for a variable with dependency bit(s) `deps`.
    pub fn addBoundVarMetaPlaceholder(
        self: *TheoremContext,
        sort_name: []const u8,
        deps: u55,
        meta_id: ?u64,
    ) !ExprId {
        return self.mintMetaPlaceholder(.{
            .sort_name = sort_name,
            .deps = deps,
            .class = .meta,
            .meta_id = meta_id,
            .bound_var = true,
        });
    }

    /// Shared mint path for every `.meta`-class leaf: advances the placeholder
    /// counter, appends `info` (caller sets sort/class/flags), bumps the meta
    /// counters, and interns. Centralizing this keeps the count bookkeeping —
    /// which `hasMetaPlaceholders`/`hasReconciliationMetas`/`clone` depend on —
    /// in exactly one place. `info.class` must be `.meta`.
    fn mintMetaPlaceholder(
        self: *TheoremContext,
        info: PlaceholderInfo,
    ) !ExprId {
        std.debug.assert(info.class == .meta);
        const placeholder_id = self.next_placeholder_id;
        self.next_placeholder_id = try std.math.add(
            PlaceholderId,
            placeholder_id,
            1,
        );
        try self.theorem_placeholders.append(self.allocator, info);
        if (info.line_hole) {
            self.has_line_holes = true;
        } else {
            self.meta_placeholder_count += 1;
        }
        if (info.reconciliation_meta) self.reconciliation_meta_count += 1;
        return try self.interner.internPlaceholder(placeholder_id);
    }

    /// Allocate a search metavariable leaf. Unlike `addPlaceholderResolved`
    /// this does NOT consume a u55 dep bit: search mints metas at scale and
    /// would exhaust the shared dep space. A meta's dependency *constraint*
    /// (which theorem binders an assignment may mention) lives in the
    /// branch-local `MetaStore`, not here.
    pub fn addMetaPlaceholderResolved(
        self: *TheoremContext,
        sort_name: []const u8,
    ) !ExprId {
        return self.mintMetaPlaceholder(.{ .sort_name = sort_name, .deps = 0, .class = .meta });
    }

    /// Allocate a line hole: an `addMetaPlaceholderResolved` leaf flagged
    /// `line_hole` (see `PlaceholderInfo`).
    pub fn addLineHolePlaceholder(
        self: *TheoremContext,
        sort_name: []const u8,
    ) !ExprId {
        return self.mintMetaPlaceholder(.{
            .sort_name = sort_name,
            .deps = 0,
            .class = .meta,
            .line_hole = true,
        });
    }

    /// Allocate an eliminator-reconciliation seed meta — an
    /// `addMetaPlaceholderResolved` leaf additionally flagged
    /// `reconciliation_meta` (see `PlaceholderInfo`). Scoped target of the
    /// meta-aware hypothesis match.
    pub fn addReconciliationMetaPlaceholderResolved(
        self: *TheoremContext,
        sort_name: []const u8,
        deps: u55,
    ) !ExprId {
        return self.mintMetaPlaceholder(.{
            .sort_name = sort_name,
            .deps = deps,
            .class = .meta,
            .reconciliation_meta = true,
        });
    }

    /// Allocate a search metavariable leaf carrying a stable cross-interner
    /// `meta_id` (see `PlaceholderInfo.meta_id`). Used by the shared `MetaStore`
    /// so a meta minted in one interner and reinterned into another resolves to
    /// the same store slot. Otherwise identical to `addMetaPlaceholderResolved`
    /// (no dep bit, `.meta` class).
    pub fn addMetaPlaceholderWithMetaId(
        self: *TheoremContext,
        sort_name: []const u8,
        meta_id: u64,
    ) !ExprId {
        return self.mintMetaPlaceholder(.{
            .sort_name = sort_name,
            .deps = 0,
            .class = .meta,
            .meta_id = meta_id,
        });
    }

    /// The stable `meta_id` of placeholder `idx`, or null when it is not a
    /// shared-store meta leaf (standard placeholder, or a meta minted without
    /// an id).
    pub fn placeholderMetaId(
        self: *const TheoremContext,
        idx: PlaceholderId,
    ) ?u64 {
        const info = self.placeholderInfo(idx) orelse return null;
        return info.meta_id;
    }

    pub fn hasMetaPlaceholders(self: *const TheoremContext) bool {
        return self.meta_placeholder_count != 0;
    }

    /// True when any line hole has been minted in this context.
    pub fn hasLineHoles(self: *const TheoremContext) bool {
        return self.has_line_holes;
    }

    /// False when no meta-class leaf can occur in this context: no search
    /// meta and no line hole has been minted.
    pub fn mayHoldMetaLeaves(self: *const TheoremContext) bool {
        return self.hasMetaPlaceholders() or self.hasLineHoles();
    }

    /// True when any `reconciliation_meta` leaf has been minted in this context.
    /// Gates the eliminator meta-aware match without a per-binding scan.
    pub fn hasReconciliationMetas(self: *const TheoremContext) bool {
        return self.reconciliation_meta_count != 0;
    }

    pub fn placeholderClass(
        self: *const TheoremContext,
        idx: PlaceholderId,
    ) PlaceholderClass {
        const info = self.placeholderInfo(idx) orelse return .standard;
        return info.class;
    }

    pub fn placeholderKind(
        self: *const TheoremContext,
        idx: PlaceholderId,
    ) PlaceholderKind {
        const info = self.placeholderInfo(idx) orelse return .dummy;
        return switch (info.class) {
            .standard => .dummy,
            .meta => if (info.reconciliation_meta)
                .seed_meta
            else if (info.meta_id != null)
                .store_meta
            else
                .hole,
        };
    }

    /// The `PlaceholderKind` of `expr` when it is a placeholder leaf, else null.
    pub fn leafPlaceholderKind(
        self: *const TheoremContext,
        expr: ExprId,
    ) ?PlaceholderKind {
        return switch (self.interner.node(expr).*) {
            .placeholder => |pid| self.placeholderKind(pid),
            .variable, .app => null,
        };
    }

    /// Pre-order OR-walk over the expression DAG: true when
    /// `pred(ctx, self, id)` holds for any node reachable from `root` (the
    /// root included). An app node is offered to the predicate before its
    /// arguments are visited, so both head predicates and leaf predicates
    /// fit. A shared app node is entered once (`DagWalk`): an expression a
    /// chain of lines builds by doubling has linear DAG size and exponential
    /// tree size. Predicates must be pure, or at least idempotent, since a
    /// node reached by two paths may still be offered twice.
    pub fn exprAny(
        self: *const TheoremContext,
        root: ExprId,
        ctx: anytype,
        comptime pred: fn (@TypeOf(ctx), *const TheoremContext, ExprId) bool,
    ) bool {
        var walk: DagWalk = .{};
        defer walk.deinit(self.allocator);
        return self.exprAnyIn(&walk, root, ctx, pred);
    }

    fn exprAnyIn(
        self: *const TheoremContext,
        walk: *DagWalk,
        id: ExprId,
        ctx: anytype,
        comptime pred: fn (@TypeOf(ctx), *const TheoremContext, ExprId) bool,
    ) bool {
        switch (self.interner.node(id).*) {
            .variable, .placeholder => return pred(ctx, self, id),
            .app => |app| {
                // A node entered before held no match, nor did anything under it.
                if (!walk.enter(self.allocator, id)) return false;
                if (pred(ctx, self, id)) return true;
                for (app.args) |arg| {
                    if (self.exprAnyIn(walk, arg, ctx, pred)) return true;
                }
                return false;
            },
        }
    }

    /// Which app nodes a DAG walk has entered. The first `plain_steps` app
    /// nodes go unrecorded, so a small expression costs no allocation; past
    /// that each app node is entered once. Memo-or-forget on OOM (the walk
    /// then degrades to a tree walk).
    const DagWalk = struct {
        const plain_steps = 64;

        steps: usize = 0,
        seen: std.AutoHashMapUnmanaged(ExprId, void) = .empty,

        fn deinit(self: *DagWalk, allocator: std.mem.Allocator) void {
            self.seen.deinit(allocator);
        }

        /// False when `id` was entered before.
        fn enter(self: *DagWalk, allocator: std.mem.Allocator, id: ExprId) bool {
            self.steps += 1;
            if (self.steps <= plain_steps) return true;
            const gop = self.seen.getOrPut(allocator, id) catch return true;
            return !gop.found_existing;
        }
    };

    /// The values a DAG walk computed for the app nodes it left, so a shared
    /// node is computed once: `get` before computing a node, `put` after.
    /// Like `DagWalk`, the first `plain_steps` app nodes go unrecorded.
    pub fn DagMemo(comptime V: type) type {
        return struct {
            const Self = @This();

            steps: usize = 0,
            values: std.AutoHashMapUnmanaged(ExprId, V) = .empty,

            pub fn deinit(self: *Self, allocator: std.mem.Allocator) void {
                self.values.deinit(allocator);
            }

            /// The value recorded for app node `id`, if any. Counts a step.
            pub fn get(self: *Self, id: ExprId) ?V {
                self.steps += 1;
                if (self.steps <= DagWalk.plain_steps) return null;
                return self.values.get(id);
            }

            pub fn put(self: *Self, allocator: std.mem.Allocator, id: ExprId, value: V) !void {
                if (self.steps <= DagWalk.plain_steps) return;
                try self.values.put(allocator, id, value);
            }
        };
    }

    /// True when `expr` is itself a placeholder leaf.
    pub fn isPlaceholder(self: *const TheoremContext, expr: ExprId) bool {
        return self.interner.node(expr).* == .placeholder;
    }

    /// True when a placeholder leaf occurs anywhere in `root`.
    pub fn containsPlaceholder(self: *const TheoremContext, root: ExprId) bool {
        return self.exprAny(root, {}, isPlaceholderPred);
    }

    fn isPlaceholderPred(_: void, self: *const TheoremContext, expr: ExprId) bool {
        return self.isPlaceholder(expr);
    }

    /// The union of the dependency bits of the leaves of `root`, the bits a
    /// binding of it carries. A placeholder counts for nothing when
    /// `!opts.placeholders`.
    pub fn exprDeps(
        self: *const TheoremContext,
        root: ExprId,
        opts: struct { placeholders: bool = true },
    ) !u55 {
        const Union = struct {
            deps: u55 = 0,
            placeholders: bool,

            fn visit(acc: *@This(), theorem: *const TheoremContext, expr: ExprId) anyerror!void {
                switch (theorem.interner.node(expr).*) {
                    .placeholder => if (acc.placeholders) {
                        acc.deps |= try theorem.leafDeps(expr);
                    },
                    .variable => acc.deps |= try theorem.leafDeps(expr),
                    .app => {},
                }
            }
        };
        var acc: Union = .{ .placeholders = opts.placeholders };
        try self.exprForEach(root, &acc, Union.visit);
        return acc.deps;
    }

    fn leafDeps(self: *const TheoremContext, leaf: ExprId) !u55 {
        const info = (try self.currentLeafInfo(leaf)) orelse return 0;
        return info.deps;
    }

    /// True when a meta-class placeholder leaf (a search meta or a line hole)
    /// occurs anywhere in `root`.
    pub fn containsMetaLeaf(self: *const TheoremContext, root: ExprId) bool {
        if (!self.mayHoldMetaLeaves()) return false;
        return self.exprAny(root, {}, isMetaLeafPred);
    }

    fn isMetaLeafPred(_: void, self: *const TheoremContext, expr: ExprId) bool {
        return switch (self.interner.node(expr).*) {
            .placeholder => |id| self.placeholderClass(id) == .meta,
            else => false,
        };
    }

    /// The first placeholder under `expr` in pre-order, or null when it is
    /// placeholder-free. Memoized per app node in `placeholder_scan_cache`;
    /// memo-or-forget on OOM.
    pub fn firstPlaceholder(self: *TheoremContext, expr: ExprId) ?PlaceholderId {
        switch (self.interner.node(expr).*) {
            .variable => return null,
            .placeholder => |id| return id,
            .app => |app| {
                if (self.placeholder_scan_cache.get(expr)) |verdict| {
                    return verdict;
                }
                var found: ?PlaceholderId = null;
                for (app.args) |arg| {
                    if (self.firstPlaceholder(arg)) |id| {
                        found = id;
                        break;
                    }
                }
                self.placeholder_scan_cache.put(
                    self.allocator,
                    expr,
                    found,
                ) catch {};
                return found;
            },
        }
    }

    /// True when a line hole (`addLineHolePlaceholder`) occurs anywhere in
    /// `root`.
    pub fn containsLineHole(self: *const TheoremContext, root: ExprId) bool {
        if (!self.hasLineHoles()) return false;
        return self.exprAny(root, {}, isLineHolePred);
    }

    fn isLineHolePred(_: void, self: *const TheoremContext, expr: ExprId) bool {
        return switch (self.interner.node(expr).*) {
            .placeholder => |id| if (self.placeholderInfo(id)) |info|
                info.line_hole
            else
                false,
            else => false,
        };
    }

    /// Side-effecting companion to `exprAny`: apply `visit` to every node
    /// reachable from `root` in pre-order (the root included), entering a
    /// shared app node once. `visit` must be idempotent. Errors from `visit`
    /// abort the walk and propagate.
    pub fn exprForEach(
        self: *const TheoremContext,
        root: ExprId,
        ctx: anytype,
        comptime visit: fn (@TypeOf(ctx), *const TheoremContext, ExprId) anyerror!void,
    ) anyerror!void {
        var walk: DagWalk = .{};
        defer walk.deinit(self.allocator);
        try self.exprForEachIn(&walk, root, ctx, visit);
    }

    fn exprForEachIn(
        self: *const TheoremContext,
        walk: *DagWalk,
        id: ExprId,
        ctx: anytype,
        comptime visit: fn (@TypeOf(ctx), *const TheoremContext, ExprId) anyerror!void,
    ) anyerror!void {
        switch (self.interner.node(id).*) {
            .variable, .placeholder => try visit(ctx, self, id),
            .app => |app| {
                if (!walk.enter(self.allocator, id)) return;
                try visit(ctx, self, id);
                for (app.args) |arg| try self.exprForEachIn(walk, arg, ctx, visit);
            },
        }
    }

    pub fn placeholderInfo(
        self: *const TheoremContext,
        idx: usize,
    ) ?PlaceholderInfo {
        if (idx >= self.theorem_placeholders.items.len) return null;
        return self.theorem_placeholders.items[idx];
    }

    pub fn requirePlaceholderInfo(
        self: *const TheoremContext,
        idx: usize,
    ) !PlaceholderInfo {
        return self.placeholderInfo(idx) orelse error.UnknownPlaceholder;
    }

    pub fn requireDummyInfo(
        self: *const TheoremContext,
        idx: usize,
    ) !DummyInfo {
        if (idx >= self.theorem_dummies.items.len) {
            return error.UnknownDummyVar;
        }
        return self.theorem_dummies.items[idx];
    }

    pub fn requireTheoremArgInfo(
        self: *const TheoremContext,
        theorem_args: []const ArgInfo,
        idx: usize,
    ) !ArgInfo {
        _ = self;
        if (idx >= theorem_args.len) {
            return error.UnknownTheoremVariable;
        }
        return theorem_args[idx];
    }

    pub fn leafInfoWithArgs(
        self: *const TheoremContext,
        theorem_args: []const ArgInfo,
        expr_id: ExprId,
    ) !?ExprLeafInfo {
        return switch (self.interner.node(expr_id).*) {
            .app => null,
            .variable => |var_id| switch (var_id) {
                .theorem_var => |idx| blk: {
                    const arg = try self.requireTheoremArgInfo(
                        theorem_args,
                        idx,
                    );
                    break :blk .{
                        .sort_name = arg.sort_name,
                        .bound = arg.bound,
                        .deps = arg.deps,
                    };
                },
                .dummy_var => |idx| blk: {
                    const dummy = try self.requireDummyInfo(idx);
                    break :blk .{
                        .sort_name = dummy.sort_name,
                        .bound = true,
                        .deps = dummy.deps,
                    };
                },
            },
            .placeholder => |idx| blk: {
                const placeholder = try self.requirePlaceholderInfo(idx);
                break :blk switch (placeholder.class) {
                    .standard => .{
                        .sort_name = placeholder.sort_name,
                        .bound = true,
                        .deps = placeholder.deps,
                    },
                    // A meta stands for an arbitrary expression of its sort,
                    // not a bound-variable stand-in, except a seed meta, which
                    // stands for a def's hidden variable, and a `.bound_choice`
                    // meta, which stands for a variable not yet named. Both
                    // carry a dep bit. A hole in a hint or query is never
                    // bound.
                    .meta => .{
                        .sort_name = placeholder.sort_name,
                        .bound = placeholder.reconciliation_meta or placeholder.bound_var,
                        .deps = placeholder.deps,
                    },
                };
            },
        };
    }

    pub fn currentLeafInfo(
        self: *const TheoremContext,
        expr_id: ExprId,
    ) !?ExprLeafInfo {
        return self.leafInfoWithArgs(self.arg_infos, expr_id);
    }

    pub fn currentLeafSortName(
        self: *const TheoremContext,
        expr_id: ExprId,
    ) ?[]const u8 {
        const info = self.currentLeafInfo(expr_id) catch return null;
        return if (info) |leaf| leaf.sort_name else null;
    }

    pub fn ensureNamedDummyParserVar(
        self: *TheoremContext,
        parser_allocator: std.mem.Allocator,
        theorem_vars: anytype,
        token: []const u8,
        sort_name: []const u8,
        sort_id: u8,
    ) !void {
        if (theorem_vars.contains(token)) return;

        const dummy_expr_id = try self.addDummyVarResolved(sort_name, sort_id);
        const var_id = self.interner.node(dummy_expr_id).*.variable;
        const dummy_id = switch (var_id) {
            .dummy_var => |id| id,
            else => unreachable,
        };
        const dummy_info = try self.requireDummyInfo(dummy_id);

        const expr = try parser_allocator.create(Expr);
        expr.* = .{
            .variable = .{
                .sort = @intCast(sort_id),
                .bound = true,
                .deps = dummy_info.deps,
            },
        };

        try self.parser_vars.put(self.allocator, expr, var_id);
        try theorem_vars.put(token, expr);
    }

    pub fn internParsedExpr(
        self: *TheoremContext,
        expr: *const Expr,
    ) !ExprId {
        return switch (expr.*) {
            .variable => blk: {
                const var_id = self.parser_vars.get(expr) orelse {
                    return error.UnknownTheoremVariable;
                };
                break :blk try self.interner.internVar(var_id);
            },
            .term => |term| blk: {
                const args = try self.allocator.alloc(ExprId, term.args.len);
                errdefer self.allocator.free(args);
                for (term.args, 0..) |arg, idx| {
                    args[idx] = try self.internParsedExpr(arg);
                }
                break :blk try self.interner.internAppOwned(term.id, args);
            },
            .hole => return error.HoleNotConcrete,
        };
    }

    /// Reverse of instantiateTemplate: given a TemplateExpr and a concrete
    /// ExprId, solve for binder values. Returns true on success.
    pub fn matchTemplate(
        self: *const TheoremContext,
        template: TemplateExpr,
        expr_id: ExprId,
        bindings: []?ExprId,
    ) bool {
        return switch (template) {
            .binder => |idx| blk: {
                if (idx >= bindings.len) break :blk false;
                if (bindings[idx]) |existing| {
                    break :blk existing == expr_id;
                } else {
                    bindings[idx] = expr_id;
                    break :blk true;
                }
            },
            .app => |app| blk: {
                const node = self.interner.node(expr_id);
                switch (node.*) {
                    .app => |concrete| {
                        if (concrete.term_id != app.term_id) break :blk false;
                        if (concrete.args.len != app.args.len) break :blk false;
                        for (app.args, concrete.args) |tmpl_arg, conc_arg| {
                            if (!self.matchTemplate(tmpl_arg, conc_arg, bindings))
                                break :blk false;
                        }
                        break :blk true;
                    },
                    else => break :blk false,
                }
            },
        };
    }

    pub fn instantiateTemplate(
        self: *TheoremContext,
        template: TemplateExpr,
        binders: []const ExprId,
    ) !ExprId {
        return switch (template) {
            .binder => |idx| blk: {
                if (idx >= binders.len) {
                    return error.TemplateBinderOutOfRange;
                }
                break :blk binders[idx];
            },
            .app => |app| blk: {
                const args = try self.allocator.alloc(ExprId, app.args.len);
                errdefer self.allocator.free(args);
                for (app.args, 0..) |arg, idx| {
                    args[idx] = try self.instantiateTemplate(arg, binders);
                }
                break :blk try self.interner.internAppOwned(
                    app.term_id,
                    args,
                );
            },
        };
    }
};

fn hashExprNode(key: ExprNode) u64 {
    const Wyhash = std.hash.Wyhash;
    return switch (key) {
        .variable => |var_id| switch (var_id) {
            .theorem_var => |id| Wyhash.hash(0, std.mem.asBytes(&id)),
            .dummy_var => |id| Wyhash.hash(1, std.mem.asBytes(&id)),
        },
        .placeholder => |id| Wyhash.hash(2, std.mem.asBytes(&id)),
        // The seed keeps the tag and term apart from the leaf seeds above.
        .app => |app| Wyhash.hash(
            (@as(u64, app.term_id) << 2) | 3,
            std.mem.sliceAsBytes(app.args),
        ),
    };
}

fn eqlExprNode(a: ExprNode, b: ExprNode) bool {
    return switch (a) {
        .variable => |lhs| switch (b) {
            .variable => |rhs| eqlVarId(lhs, rhs),
            else => false,
        },
        .placeholder => |lhs| switch (b) {
            .placeholder => |rhs| lhs == rhs,
            else => false,
        },
        .app => |lhs| switch (b) {
            .app => |rhs| blk: {
                if (lhs.term_id != rhs.term_id) break :blk false;
                if (lhs.args.len != rhs.args.len) break :blk false;
                for (lhs.args, rhs.args) |l_arg, r_arg| {
                    if (l_arg != r_arg) break :blk false;
                }
                break :blk true;
            },
            else => false,
        },
    };
}

fn eqlVarId(a: VarId, b: VarId) bool {
    return switch (a) {
        .theorem_var => |lhs| switch (b) {
            .theorem_var => |rhs| lhs == rhs,
            else => false,
        },
        .dummy_var => |lhs| switch (b) {
            .dummy_var => |rhs| lhs == rhs,
            else => false,
        },
    };
}
