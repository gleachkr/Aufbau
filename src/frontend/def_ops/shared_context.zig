const std = @import("std");
const GlobalEnv = @import("../env.zig").GlobalEnv;
const ExprId = @import("../expr.zig").ExprId;
const TheoremContext = @import("../expr.zig").TheoremContext;
const RewriteRegistry = @import("../rewrite_registry.zig").RewriteRegistry;
const Types = @import("./types.zig");
const SymbolicExpr = Types.SymbolicExpr;

/// Structural equality of two `SymbolicExpr` values, comparing `app` children
/// by *pointer*. This is exact when children are themselves interned (the
/// bottom-up construction in `allocSymbolic` guarantees canonical children in
/// the common case): interned children make structural equality equivalent to
/// pointer equality. When a child is not interned (e.g. a tree cloned in from a
/// seed via `cloneSymbolicExpr`), pointer comparison merely under-dedupes — it
/// keeps the two nodes distinct, which is always sound (never a false merge).
fn symbolicShallowEql(a: SymbolicExpr, b: SymbolicExpr) bool {
    return switch (a) {
        .binder => |x| b == .binder and b.binder == x,
        .fixed => |x| b == .fixed and b.fixed == x,
        .dummy => |x| b == .dummy and b.dummy == x,
        .app => |ax| b == .app and ax.term_id == b.app.term_id and
            ax.args.len == b.app.args.len and blk: {
            for (ax.args, b.app.args) |pa, pb| {
                if (pa != pb) break :blk false;
            }
            break :blk true;
        },
    };
}

/// Hash-cons table over the context's scratch-arena `SymbolicExpr` nodes.
/// Keyed by the interned node pointer; hash is the node's cached structural
/// hash (`Types.symbolicHash`, O(1) for `app`). See `internSymbolic`.
const SymbolicInternContext = struct {
    pub fn hash(_: SymbolicInternContext, key: *const SymbolicExpr) u64 {
        return Types.symbolicHash(key);
    }
    pub fn eql(
        _: SymbolicInternContext,
        a: *const SymbolicExpr,
        b: *const SymbolicExpr,
    ) bool {
        return symbolicShallowEql(a.*, b.*);
    }
};

/// Adapter letting `getOrPutAdapted` probe the intern table with a by-value
/// `SymbolicExpr` (the candidate node) without allocating it first, so a hit
/// costs zero arena bytes.
const SymbolicInternAdapter = struct {
    pub fn hash(_: SymbolicInternAdapter, key: SymbolicExpr) u64 {
        return Types.symbolicHash(&key);
    }
    pub fn eql(
        _: SymbolicInternAdapter,
        key: SymbolicExpr,
        stored: *const SymbolicExpr,
    ) bool {
        return symbolicShallowEql(key, stored.*);
    }
};

const SymbolicInternMap = std.HashMapUnmanaged(
    *const SymbolicExpr,
    void,
    SymbolicInternContext,
    std.hash_map.default_max_load_percentage,
);

/// Key for the whole-template expansion memo: identity of a STABLE
/// `TemplateExpr` app node (its args slice ptr/len — templates live in
/// env/registry/view storage for the context lifetime) plus the subst's
/// interned child pointers. `symbolicFromTemplateSubst` is a pure function of
/// exactly these inputs (it reads no session state — fresh-dummy minting
/// happens in its callers, BEFORE the subst is built), and its output is the
/// canonical interned node, so key-equal returns the pointer-identical result
/// a rebuild would produce. Fresh dummy slots recur deterministically across
/// snapshot restores (`restoreMatchSnapshot` truncates
/// `symbolic_dummy_infos`), so recurring expansions carry the same `.dummy`
/// subst pointers and hit; diverging slots change the key and miss — no
/// up-to-alpha reasoning involved (that refuted lever is unrelated).
pub const TemplateSubstMemoKey = struct {
    template_args_ptr: usize,
    template_args_len: usize,
    term_id: u32,
    subst: []const *const SymbolicExpr,

    fn computeHash(self: TemplateSubstMemoKey) u64 {
        var h = Types.mixHash(0x7E3A_9D4C_51B6_0F27, self.template_args_ptr);
        h = Types.mixHash(h, self.template_args_len);
        h = Types.mixHash(h, self.term_id);
        for (self.subst) |child| {
            h = Types.mixHash(h, @intFromPtr(child));
        }
        return h;
    }
};

const TemplateSubstMemoContext = struct {
    pub fn hash(_: TemplateSubstMemoContext, key: TemplateSubstMemoKey) u64 {
        return key.computeHash();
    }
    pub fn eql(
        _: TemplateSubstMemoContext,
        a: TemplateSubstMemoKey,
        b: TemplateSubstMemoKey,
    ) bool {
        if (a.template_args_ptr != b.template_args_ptr) return false;
        if (a.template_args_len != b.template_args_len) return false;
        if (a.term_id != b.term_id) return false;
        if (a.subst.len != b.subst.len) return false;
        for (a.subst, b.subst) |x, y| {
            if (x != y) return false;
        }
        return true;
    }
};

const TemplateSubstMemoMap = std.HashMapUnmanaged(
    TemplateSubstMemoKey,
    *const SymbolicExpr,
    TemplateSubstMemoContext,
    std.hash_map.default_max_load_percentage,
);

pub const SharedContext = struct {
    /// Caller-owned allocator. Used for results that escape this context
    /// (interner-owned arrays, and slices the caller frees itself, e.g.
    /// `RuleMatchSession.materializeOptionalBindings`). Do NOT route throwaway
    /// `SymbolicExpr` trees here — use `scratch()`.
    allocator: std.mem.Allocator,
    /// Per-context scratch arena for throwaway intermediate allocations (the
    /// `SymbolicExpr` nodes built during a match attempt). These never escape a
    /// `def_ops.Context` and are never freed individually, so they accumulate
    /// for the whole search under the caller's request arena. Routing them
    /// through this arena reclaims them at `deinit`, bounding peak memory.
    ///
    /// Stored by value: the arena holds no self-pointers until `allocator()` is
    /// called, and that is only ever called fresh via a stable `*SharedContext`
    /// (never captured before the construction-time copies settle), so copying
    /// the empty arena during `Context.init` is safe.
    scratch_arena: std.heap.ArenaAllocator,
    /// Hash-cons table for scratch-arena `SymbolicExpr` nodes (see
    /// `internSymbolic`). Backing store lives on `allocator`; the interned
    /// nodes themselves live in `scratch_arena`. Empty at construction, so the
    /// by-value copy in `Context.init` is safe for the same reason the arena is
    /// (no self-pointers until first use via a stable `*SharedContext`).
    symbolic_intern: SymbolicInternMap = .empty,
    /// Whole-template expansion memo (see `TemplateSubstMemoKey` and
    /// `transparent_match.symbolicFromStableTemplateSubst`). Backing store on
    /// `allocator`, stored subst copies in `scratch_arena` — same lifetime
    /// discipline as the intern table. Empty at construction, so the by-value
    /// copy in `Context.init` is safe (no self-pointers until first use).
    template_subst_memo: TemplateSubstMemoMap = .empty,
    /// Lazy index of def term ids grouped by return sort, replacing the
    /// all-terms linear scan in `representative.compressRepresentativeToDef`
    /// (the hottest line cluster on the martin_lof def-eq profile). Buckets
    /// keep ascending term-id order, so compression picks the same def the
    /// linear scan did. Keys are env-owned sort-name slices (the env outlives
    /// the context); the map and bucket arrays live on `allocator`. Empty at
    /// construction, so the by-value copy in `Context.init` is safe (no
    /// self-pointers until first use).
    def_compression_index: std.StringHashMapUnmanaged(
        std.ArrayListUnmanaged(u32),
    ) = .empty,
    def_compression_index_built: bool = false,
    /// Session-independent representative memo (one map per non-exact
    /// `BindingMode`): input expr → its plain concrete representative.
    /// Populated only when the input is placeholder-free and the computed
    /// representative came out plain (`.fixed`) — in that case the whole
    /// rebuild → canonicalize → def-compress computation never reads
    /// match-session state (witnesses, bindings, dummy slots all enter only
    /// through placeholder resymbolization), so the entry is valid for every
    /// session in this context and survives `invalidateRepresentativeCaches`,
    /// which wipes the per-session caches on every binder assignment.
    pure_transparent_reprs: std.AutoHashMapUnmanaged(ExprId, ExprId) = .empty,
    pure_normalized_reprs: std.AutoHashMapUnmanaged(ExprId, ExprId) = .empty,
    /// Memo backing `exprIsPlaceholderFree` (true = no `.placeholder` node
    /// anywhere in the expr). Sound to persist: interned exprs are immutable.
    placeholder_free: std.AutoHashMapUnmanaged(ExprId, bool) = .empty,
    theorem: *TheoremContext,
    env: *const GlobalEnv,
    registry: ?*RewriteRegistry,

    pub fn init(
        allocator: std.mem.Allocator,
        theorem: *TheoremContext,
        env: *const GlobalEnv,
    ) SharedContext {
        return .{
            .allocator = allocator,
            .scratch_arena = std.heap.ArenaAllocator.init(allocator),
            .theorem = theorem,
            .env = env,
            .registry = null,
        };
    }

    pub fn initWithRegistry(
        allocator: std.mem.Allocator,
        theorem: *TheoremContext,
        env: *const GlobalEnv,
        registry: *RewriteRegistry,
    ) SharedContext {
        return .{
            .allocator = allocator,
            .scratch_arena = std.heap.ArenaAllocator.init(allocator),
            .theorem = theorem,
            .env = env,
            .registry = registry,
        };
    }

    /// Allocator for throwaway intermediate `SymbolicExpr` trees. Reclaimed at
    /// `deinit`. Must only back allocations that do not escape this context.
    pub fn scratch(self: *SharedContext) std.mem.Allocator {
        return self.scratch_arena.allocator();
    }

    /// Hash-cons a `SymbolicExpr`: return the canonical scratch-arena node for
    /// this structure, allocating it only on first sight. Callers pass a fully
    /// built node value whose `app` children are themselves interned pointers
    /// and whose `app.hash` is already populated (see `allocSymbolic`), so the
    /// lookup is O(arity) with an O(1) hash.
    ///
    /// Sound to share across match sessions in this context because
    /// `SymbolicExpr` nodes are immutable, index-based values carrying no
    /// session-specific identity: `binder`/`dummy` are bare indices resolved
    /// against whichever session is currently matching, `fixed` is a stable
    /// interner `ExprId`, `app` is `term_id` + child pointers. (Contrast the
    /// materialized-representative cache, which embeds freshly minted theorem
    /// atoms and therefore cannot be shared — see the design note.)
    pub fn internSymbolic(
        self: *SharedContext,
        value: SymbolicExpr,
    ) !*const SymbolicExpr {
        const gop = try self.symbolic_intern.getOrPutAdapted(
            self.allocator,
            value,
            SymbolicInternAdapter{},
        );
        if (gop.found_existing) return gop.key_ptr.*;
        const node = try self.scratch().create(SymbolicExpr);
        node.* = value;
        gop.key_ptr.* = node;
        return node;
    }

    /// Hash-cons an `app` node from a *borrowed* args slice (e.g. a caller's
    /// stack buffer). The args array is copied into the scratch arena only on a
    /// miss — so a hit costs zero arena bytes, unlike passing a pre-allocated
    /// scratch args slice to `internSymbolic` (which leaks that slice on a hit).
    /// The copied children are the same interned pointers, so the node's cached
    /// hash and pointer-based structural equality are unaffected.
    pub fn internSymbolicApp(
        self: *SharedContext,
        term_id: u32,
        args: []const *const SymbolicExpr,
    ) !*const SymbolicExpr {
        const hash = Types.computeAppHash(term_id, args);
        const probe = SymbolicExpr{ .app = .{
            .term_id = term_id,
            .args = args,
            .hash = hash,
        } };
        const gop = try self.symbolic_intern.getOrPutAdapted(
            self.allocator,
            probe,
            SymbolicInternAdapter{},
        );
        if (gop.found_existing) return gop.key_ptr.*;
        const owned = try self.scratch().dupe(*const SymbolicExpr, args);
        const node = try self.scratch().create(SymbolicExpr);
        node.* = .{ .app = .{ .term_id = term_id, .args = owned, .hash = hash } };
        gop.key_ptr.* = node;
        return node;
    }

    /// Expansion-memo probe. Returns the memoized canonical node for this
    /// (stable template, subst) call, if the identical call was built before.
    pub fn templateSubstMemoGet(
        self: *const SharedContext,
        key: TemplateSubstMemoKey,
    ) ?*const SymbolicExpr {
        return self.template_subst_memo.get(key);
    }

    /// Record an expansion result. Copies the borrowed subst slice into the
    /// scratch arena so the stored key owns its pointers for the context
    /// lifetime (the caller's slice is a stack buffer or per-call scratch).
    pub fn templateSubstMemoPut(
        self: *SharedContext,
        key: TemplateSubstMemoKey,
        result: *const SymbolicExpr,
    ) !void {
        var owned = key;
        owned.subst = try self.scratch().dupe(*const SymbolicExpr, key.subst);
        try self.template_subst_memo.put(self.allocator, owned, result);
    }

    /// Def term ids whose return sort is `sort_name`, in ascending term-id
    /// order — the same candidates (in the same order) the old all-terms
    /// scan in `compressRepresentativeToDef` visited. Built once per context
    /// on first call; the env's term list does not grow within a context's
    /// lifetime (contexts live inside a single statement's elaboration).
    pub fn defCompressionCandidates(
        self: *SharedContext,
        sort_name: []const u8,
    ) ![]const u32 {
        if (!self.def_compression_index_built) {
            for (self.env.terms.items, 0..) |term, term_id| {
                if (!term.is_def or term.body == null) continue;
                const gop = try self.def_compression_index.getOrPut(
                    self.allocator,
                    term.ret_sort_name,
                );
                if (!gop.found_existing) gop.value_ptr.* = .empty;
                try gop.value_ptr.append(self.allocator, @intCast(term_id));
            }
            self.def_compression_index_built = true;
        }
        const bucket = self.def_compression_index.getPtr(sort_name) orelse
            return &.{};
        return bucket.items;
    }

    fn pureRepresentativeCache(
        self: *SharedContext,
        mode: Types.BindingMode,
    ) *std.AutoHashMapUnmanaged(ExprId, ExprId) {
        return switch (mode) {
            .exact => unreachable,
            .transparent => &self.pure_transparent_reprs,
            .normalized => &self.pure_normalized_reprs,
        };
    }

    pub fn pureRepresentativeGet(
        self: *SharedContext,
        mode: Types.BindingMode,
        expr_id: ExprId,
    ) ?ExprId {
        return self.pureRepresentativeCache(mode).get(expr_id);
    }

    pub fn pureRepresentativePut(
        self: *SharedContext,
        mode: Types.BindingMode,
        expr_id: ExprId,
        repr: ExprId,
    ) !void {
        try self.pureRepresentativeCache(mode).put(
            self.allocator,
            expr_id,
            repr,
        );
    }

    pub fn exprIsPlaceholderFree(
        self: *SharedContext,
        expr_id: ExprId,
    ) !bool {
        if (self.placeholder_free.get(expr_id)) |known| return known;
        const result: bool = switch (self.theorem.interner.node(expr_id).*) {
            .variable => true,
            .placeholder => false,
            .app => |app| blk: {
                for (app.args) |arg| {
                    if (!try self.exprIsPlaceholderFree(arg)) break :blk false;
                }
                break :blk true;
            },
        };
        try self.placeholder_free.put(self.allocator, expr_id, result);
        return result;
    }

    pub fn deinit(self: *SharedContext) void {
        self.symbolic_intern.deinit(self.allocator);
        self.template_subst_memo.deinit(self.allocator);
        self.pure_transparent_reprs.deinit(self.allocator);
        self.pure_normalized_reprs.deinit(self.allocator);
        self.placeholder_free.deinit(self.allocator);
        var index_it = self.def_compression_index.valueIterator();
        while (index_it.next()) |bucket| bucket.deinit(self.allocator);
        self.def_compression_index.deinit(self.allocator);
        self.scratch_arena.deinit();
        self.* = undefined;
    }
};
