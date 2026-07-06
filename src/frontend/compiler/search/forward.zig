//! Bounded forward saturation with universal metas.
//!
//! For each `@auto forward` rule, the saturation pass matches the rule's
//! (view) hypotheses against tuples of sources — pool refs, or refs derived
//! in an earlier layer — directly, or through bounded transparent-def
//! unfolding of the source, and records a *deferred instantiation*: the rule
//! applied to those sources with each `@recover`-deferred witness — and each
//! unresolved non-bound conclusion binder (`g ⊢ ⊥ > g ⊢ a` fires as the
//! family fact `g ⊢ ?a`) — left as a universal metavariable. No conclusion
//! is built or reduced; the derived ref's recorded surface is the
//! `@recover`-derived applied shape (the matched matrix with the recover hole
//! swapped for the meta — one structural leaf swap, no rewrite rule fires).
//!
//! Saturation runs in layers. Layer N fires tuples that use at
//! least one fact from layer N-1's frontier (so no tuple is re-attempted),
//! bounded by `ForwardOptions.max_forward_{layers,facts,rule_attempts,
//! match_tuples}`; stopping at a budget is reported distinctly from a clean
//! fixpoint (`DerivedPool.budget_exhausted`). Derived-from-derived recipes
//! share holes through the single pool store: firing a rule on `p ?t → q ?t`
//! derives `q ?t` with the *same* `?t`, so one use-time solve instantiates
//! every layer of the nested recipe consistently.
//!
//! Use-time discipline: matching a concrete goal (or a backward premise's
//! recover source) against the shape IS the `@recover` solve — where the
//! shape has the meta, the goal shows the witness. A use transiently assigns
//! the holes, materializes the concrete (possibly nested) recipe, then rolls
//! the assignments back, so each use gets an independent instantiation.
//! Soundness anchor: a derived ref is a search hint only; the materialized
//! recipe is re-checked by `tryCandidate` at the point of use, so a wrong
//! forward derivation can never yield an accepted proof.

const std = @import("std");
const types = @import("./types.zig");
const refs_mod = @import("./refs.zig");
const ref_index_mod = @import("./ref_index.zig");
const prune = @import("./backward/prune.zig");
const ExprModule = @import("../../expr.zig");
const ExprId = ExprModule.ExprId;
const VarId = ExprModule.VarId;
const PlaceholderId = ExprModule.PlaceholderId;
const TheoremContext = ExprModule.TheoremContext;
const RuleDecl = @import("../../env.zig").RuleDecl;
const TemplateExpr = @import("../../rules.zig").TemplateExpr;
const ArgInfo = @import("../../parse_recovery.zig").ArgInfo;
const ProofScript = @import("../../proof_script.zig");
const RuleApplication = ProofScript.RuleApplication;
const Ref = ProofScript.Ref;
const Span = ProofScript.Span;
const OpenTerms = @import("../inference/open_terms.zig");
const MetaStore = @import("../inference/meta_store.zig").MetaStore;
const pretty_print = @import("../../pretty_print.zig");
const interner_view = @import("../../interner_view.zig");

const Context = types.Context;
const SearchCounters = types.SearchCounters;
const DerivedPool = types.DerivedPool;
const DerivedRef = types.DerivedRef;
const DerivedRefBinding = types.DerivedRefBinding;
const DerivedSource = types.DerivedSource;
const ForwardOptions = types.ForwardOptions;
const NameExprMap = types.NameExprMap;

/// Premise matching sees through this many transparent-def unfold layers of a
/// source expression (e.g. `mono f` -> `∀ a ∀ b (…)` is one layer).
const max_premise_unfold_layers: usize = 4;

const zero_span = Span{ .start = 0, .end = 0 };

/// Run bounded forward saturation over `pool`, deriving refs into a fresh
/// `DerivedPool`. Shapes and metas are interned into `theorem` (the search
/// driver's work theorem), so their ids stay valid in every per-candidate
/// COW clone taken afterwards. Only universal metas are ever minted here, so
/// no derived ref can carry an unsolved existential. When `ref_index` is
/// present (the session's clipper-backed index, already built for backward
/// search) it pre-filters pool sources per premise slot; derived sources are
/// scanned linearly (bounded by `max_forward_facts`).
///
/// `seeds` are `@auto trigger` ground facts (sourceless `DerivedRef`s minted
/// by `trigger.zig` for the seeding retry phase; empty on every other call).
/// They enter as depth-0 derived sources so layer-1 joins fire over them,
/// and stay in the derived pool for backward use. A seed whose canonical
/// shape merely restates a pool fact (or an earlier seed) is dropped —
/// backward search already has the ref. Seeds occupy the lowest derived
/// indices, as recipe acyclicity requires (a join product referencing a seed
/// must sit at a strictly higher index).
pub fn saturate(
    context: *const Context,
    theorem: *TheoremContext,
    pool: []const refs_mod.RefPoolEntry,
    ref_index: ?*const ref_index_mod.Index,
    options: ForwardOptions,
    counters: ?*SearchCounters,
    seeds: []const DerivedRef,
) !DerivedPool {
    var result = DerivedPool{
        .arena = std.heap.ArenaAllocator.init(context.allocator),
        .store = MetaStore.init(context.allocator, context.env),
    };
    errdefer result.deinit();

    var sat = Saturator{
        .context = context,
        .theorem = theorem,
        .ref_index = ref_index,
        .options = options,
        .counters = counters,
        .store = &result.store,
        .arena = result.arena.allocator(),
        .scratch = context.allocator,
        .pool_source_idx = try context.allocator.alloc(?usize, pool.len),
        .unfold_cache = .{ .allocator = context.allocator },
    };
    defer sat.deinit();
    @memset(sat.pool_source_idx, null);

    // Seed sources from the pool, registering each expression's shape key so
    // a derived fact that merely restates an existing concrete fact is
    // dropped (backward search already has the pool ref).
    for (pool, 0..) |entry, pool_idx| {
        const expr = refs_mod.sourceRefExpr(
            context,
            theorem,
            entry.ref,
        ) catch continue;
        sat.pool_source_idx[pool_idx] = sat.sources.items.len;
        try sat.sources.append(sat.scratch, .{
            .source = .{ .pool = entry.ref },
            .expr = expr,
            .depth = 0,
        });
        _ = try sat.seen.getOrPut(sat.scratch, try sat.shapeKey(expr));
    }
    sat.pool_count = sat.sources.items.len;

    result.has_seeds = seeds.len > 0;
    for (seeds) |seed| {
        const shape_gop = try sat.seen.getOrPut(
            sat.scratch,
            try sat.shapeKey(seed.shape),
        );
        if (shape_gop.found_existing) continue;
        const idx = sat.derived.items.len;
        try sat.derived.append(sat.arena, seed);
        try sat.sources.append(sat.scratch, .{
            .source = .{ .derived = idx },
            .expr = seed.shape,
            .depth = 0,
        });
    }

    const rule_limit = @min(
        context.available_rule_count,
        context.env.rules.items.len,
    );
    var frontier_start: usize = 0;
    var layer: usize = 1;
    saturation: while (layer <= options.max_forward_layers) : (layer += 1) {
        result.layers_run = layer;
        const layer_sources = sat.sources.items.len;
        const facts_before = sat.derived.items.len;
        for (0..rule_limit) |rule_idx| {
            const rule_id: u32 = @intCast(rule_idx);
            if (!context.registry.isAutoForwardRule(rule_id)) continue;
            sat.fireRule(rule_id, frontier_start, layer_sources) catch |err|
                switch (err) {
                    error.OutOfMemory => return error.OutOfMemory,
                    error.ForwardBudgetExhausted => break :saturation,
                };
        }
        // Fixpoint: a full pass over the frontier derived nothing new.
        if (sat.derived.items.len == facts_before) break;
        for (sat.derived.items[facts_before..], facts_before..) |dref, idx| {
            try sat.sources.append(sat.scratch, .{
                .source = .{ .derived = idx },
                .expr = dref.shape,
                .depth = dref.source_depth,
            });
        }
        frontier_start = layer_sources;
        if (layer == options.max_forward_layers) {
            // Stopped by the layer cap while the frontier was still
            // productive: not a fixpoint.
            sat.exhausted = true;
        }
    }

    result.budget_exhausted = sat.exhausted;
    result.refs = try sat.derived.toOwnedSlice(sat.arena);
    if (counters) |c| {
        c.derived_ref_count += result.refs.len;
        c.forward_layers_run += result.layers_run;
        if (result.budget_exhausted) c.forward_saturation_exhausted = true;
    }
    return result;
}

const FireError = error{ OutOfMemory, ForwardBudgetExhausted };

/// Saturation state for one `saturate` run. `arena` is the result pool's
/// arena (derived refs, recipe slices, dedupe key bytes — everything that
/// must live as long as the pool); `scratch` allocations never escape.
const Saturator = struct {
    context: *const Context,
    theorem: *TheoremContext,
    ref_index: ?*const ref_index_mod.Index,
    options: ForwardOptions,
    counters: ?*SearchCounters,
    store: *MetaStore,
    arena: std.mem.Allocator,
    scratch: std.mem.Allocator,
    /// Pool index -> source index (null when the pool entry failed to
    /// resolve an expression at seed time).
    pool_source_idx: []?usize,
    /// Source expr -> its one-layer transparent-def unfolding (null = head
    /// not unfoldable). Unfolding a binder-introducing def mints a fresh
    /// placeholder per dummy from the theorem's 55-slot dep space; the cache
    /// makes that spend once per distinct expression instead of once per
    /// match attempt, and keeps repeated attempts from exhausting the space.
    unfold_cache: UnfoldCache,
    pool_count: usize = 0,
    /// Premise sources: pool refs first, then derived refs in derivation
    /// order. Layer N restricts matching to the prefix that existed when the
    /// layer started.
    sources: std.ArrayListUnmanaged(SourceEntry) = .{},
    derived: std.ArrayListUnmanaged(DerivedRef) = .{},
    /// Forward-join overlay: nested-source universal metas grounded to concrete
    /// witnesses during the current premise match (`P ?t` meets `P c` ⇒ `?t :=
    /// c`). Kept here instead of the shared pool store so the family fact stays
    /// general; baked into the produced fact's `pinned_metas`. Snapshotted by
    /// length and restored on backtrack, like the binding array.
    groundings: std.ArrayListUnmanaged(types.MetaAssignment) = .{},
    /// Dedupe set over recipe keys (rule + source tuple) and canonical shape
    /// keys.
    seen: std.StringHashMapUnmanaged(void) = .empty,
    attempts: usize = 0,
    tuples: usize = 0,
    exhausted: bool = false,

    const SourceEntry = struct {
        source: DerivedSource,
        expr: ExprId,
        depth: usize,
    };

    fn deinit(self: *Saturator) void {
        self.sources.deinit(self.scratch);
        self.seen.deinit(self.scratch);
        self.groundings.deinit(self.scratch);
        self.scratch.free(self.pool_source_idx);
        self.unfold_cache.deinit();
        self.* = undefined;
    }

    /// Fire one `@auto forward` rule over every admissible source tuple in
    /// the current layer.
    fn fireRule(
        self: *Saturator,
        rule_id: u32,
        frontier_start: usize,
        source_limit: usize,
    ) FireError!void {
        const rule = &self.context.env.rules.items[rule_id];
        const view = self.context.views.get(rule_id);
        const num_binders = if (view) |v| v.num_binders else rule.args.len;
        const hyps = if (view) |v| v.hyps else rule.hyps;
        if (hyps.len == 0) return;

        const candidates = try self.scratch.alloc([]usize, hyps.len);
        var built: usize = 0;
        defer {
            for (candidates[0..built]) |list| self.scratch.free(list);
            self.scratch.free(candidates);
        }
        for (hyps, 0..) |template, hyp_idx| {
            candidates[hyp_idx] = try self.hypCandidates(
                rule_id,
                template,
                source_limit,
            );
            built += 1;
        }

        const bindings = try self.scratch.alloc(?ExprId, num_binders);
        defer self.scratch.free(bindings);
        @memset(bindings, null);
        const snapshots = try self.scratch.alloc(
            ?ExprId,
            num_binders * hyps.len,
        );
        defer self.scratch.free(snapshots);
        const chosen = try self.scratch.alloc(usize, hyps.len);
        defer self.scratch.free(chosen);

        try self.matchPremises(
            rule_id,
            rule,
            view,
            hyps,
            candidates,
            frontier_start,
            0,
            false,
            bindings,
            snapshots,
            chosen,
        );
    }

    /// Candidate source indices for one premise slot, ascending. Pool
    /// sources are pre-filtered through the clipper-backed ref index when
    /// available — the same shape machinery the backward per-hyp lookup
    /// trusts, whose shape variants include transparent-def unfoldings (so
    /// `mono f` still surfaces for a `∀ x p` premise). Derived sources are
    /// appended unfiltered: their shapes hold meta leaves the shape builder
    /// does not model, and the list is small.
    fn hypCandidates(
        self: *Saturator,
        rule_id: u32,
        template: TemplateExpr,
        source_limit: usize,
    ) FireError![]usize {
        var list = std.ArrayListUnmanaged(usize){};
        errdefer list.deinit(self.scratch);

        var filtered = false;
        if (self.ref_index) |index| {
            const rule = &self.context.env.rules.items[rule_id];
            const arg_infos = if (self.context.views.get(rule_id)) |v|
                v.arg_infos
            else
                rule.args;
            const unbound = try self.scratch.alloc(?ExprId, arg_infos.len);
            defer self.scratch.free(unbound);
            @memset(unbound, null);
            if (index.lookupTemplate(
                self.theorem,
                template,
                arg_infos,
                unbound,
                self.counters,
            )) |lookup_result| {
                var lookup = lookup_result;
                defer lookup.deinit();
                for (lookup.indices) |pool_idx| {
                    if (pool_idx >= self.pool_source_idx.len) continue;
                    const src_idx = self.pool_source_idx[pool_idx] orelse
                        continue;
                    try list.append(self.scratch, src_idx);
                }
                std.mem.sort(usize, list.items, {}, std.sort.asc(usize));
                filtered = true;
            } else |err| switch (err) {
                error.OutOfMemory => return error.OutOfMemory,
                // Shape build failed for this template: fall back to the
                // full pool scan for this slot.
                else => {},
            }
        }
        if (!filtered) {
            for (0..self.pool_count) |src_idx| {
                try list.append(self.scratch, src_idx);
            }
        }
        for (self.pool_count..source_limit) |src_idx| {
            try list.append(self.scratch, src_idx);
        }
        return try list.toOwnedSlice(self.scratch);
    }

    /// Backtracking premise-tuple enumeration with shared binder state.
    fn matchPremises(
        self: *Saturator,
        rule_id: u32,
        rule: *const RuleDecl,
        view: ?types.ViewDecl,
        hyps: []const TemplateExpr,
        candidates: []const []const usize,
        frontier_start: usize,
        position: usize,
        used_frontier: bool,
        bindings: []?ExprId,
        snapshots: []?ExprId,
        chosen: []usize,
    ) FireError!void {
        if (position == hyps.len) {
            return self.completeTuple(rule_id, rule, view, bindings, chosen);
        }
        const last = position + 1 == hyps.len;
        const snapshot =
            snapshots[position * bindings.len ..][0..bindings.len];
        for (candidates[position]) |src_idx| {
            const in_frontier = src_idx >= frontier_start;
            // Semi-naive layering: every tuple must use at least one
            // frontier source, or it was already attempted last layer.
            if (last and !used_frontier and !in_frontier) continue;
            self.attempts += 1;
            if (self.counters) |c| c.forward_rule_attempts += 1;
            if (self.attempts > self.options.max_forward_rule_attempts) {
                self.exhausted = true;
                return error.ForwardBudgetExhausted;
            }
            @memcpy(snapshot, bindings);
            const groundings_mark = self.groundings.items.len;
            const matched = try matchForwardTemplate(
                self.context,
                self.theorem,
                &self.unfold_cache,
                self.store,
                &self.groundings,
                self.scratch,
                hyps[position],
                self.sources.items[src_idx].expr,
                bindings,
                0,
            );
            if (matched) {
                chosen[position] = src_idx;
                try self.matchPremises(
                    rule_id,
                    rule,
                    view,
                    hyps,
                    candidates,
                    frontier_start,
                    position + 1,
                    used_frontier or in_frontier,
                    bindings,
                    snapshots,
                    chosen,
                );
            }
            @memcpy(bindings, snapshot);
            self.groundings.shrinkRetainingCapacity(groundings_mark);
        }
    }

    /// One fully matched premise tuple: dedupe, derive, dedupe the surface,
    /// record.
    fn completeTuple(
        self: *Saturator,
        rule_id: u32,
        rule: *const RuleDecl,
        view: ?types.ViewDecl,
        bindings: []const ?ExprId,
        chosen: []const usize,
    ) FireError!void {
        self.tuples += 1;
        if (self.counters) |c| c.forward_match_tuples += 1;
        if (self.tuples > self.options.max_forward_match_tuples) {
            self.exhausted = true;
            return error.ForwardBudgetExhausted;
        }

        // Dedupe on recipe identity (rule + source tuple). Derivation is
        // deterministic given these, so this subsumes the shape / meta
        // structure / binding components of the stable key; failed
        // derivations are recorded too, so later layers never retry them.
        const recipe_key = try self.recipeKey(rule_id, chosen);
        const recipe_gop = try self.seen.getOrPut(self.scratch, recipe_key);
        if (recipe_gop.found_existing) return;

        if (self.derived.items.len >= self.options.max_forward_facts) {
            self.exhausted = true;
            return error.ForwardBudgetExhausted;
        }

        const mark = self.store.mark();
        const maybe_dref = self.derive(
            rule_id,
            rule,
            view,
            bindings,
            chosen,
        ) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            // Dep-slot exhaustion etc.: skip the tuple, keep saturating.
            else => {
                self.store.rollbackTo(mark);
                return;
            },
        };
        const dref = maybe_dref orelse {
            self.store.rollbackTo(mark);
            return;
        };

        // Surface-level dedupe: an identical shape (metas numbered by first
        // occurrence) — or one merely restating a pool fact — adds nothing
        // for search; the earliest (shallowest) derivation wins.
        const shape_key = try self.shapeKey(dref.shape);
        const shape_gop = try self.seen.getOrPut(self.scratch, shape_key);
        if (shape_gop.found_existing) {
            self.store.rollbackTo(mark);
            return;
        }
        try self.derived.append(self.arena, dref);
    }

    /// Build the derived ref for one matched premise tuple: defer `@recover`
    /// witnesses as universal metas, build the goal-shaped surface by the
    /// structural leaf swap, and record the recipe. Returns null when the
    /// conclusion surface cannot be built without normalization (no usable
    /// `@recover`), or when some recipe layer needs a meta the surface could
    /// never solve at use time.
    fn derive(
        self: *Saturator,
        rule_id: u32,
        rule: *const RuleDecl,
        view: ?types.ViewDecl,
        bindings_in: []const ?ExprId,
        chosen: []const usize,
    ) !?DerivedRef {
        const theorem = self.theorem;
        const store = self.store;
        const bindings = try self.scratch.dupe(?ExprId, bindings_in);
        defer self.scratch.free(bindings);

        const shape_raw: ExprId = blk: {
            if (view) |v| {
                // Defer each `@recover`-recoverable witness as a universal
                // meta and build the law's source surface by the structural
                // leaf swap.
                for (v.derived_bindings) |derived_binding| {
                    const rec = switch (derived_binding) {
                        .recover => |r| r,
                        .abstract => continue,
                    };
                    if (rec.target_view_idx >= bindings.len) continue;
                    if (rec.source_view_idx >= bindings.len) continue;
                    if (rec.pattern_view_idx >= bindings.len) continue;
                    if (rec.hole_view_idx >= bindings.len) continue;
                    if (bindings[rec.target_view_idx] != null) continue;
                    if (bindings[rec.source_view_idx] != null) continue;
                    const pattern = bindings[rec.pattern_view_idx] orelse
                        continue;
                    const hole = bindings[rec.hole_view_idx] orelse continue;
                    const meta = try store.mint(
                        theorem,
                        v.arg_infos[rec.target_view_idx].sort_name,
                        std.math.maxInt(u55),
                        .universal,
                    );
                    bindings[rec.target_view_idx] = meta;
                    bindings[rec.source_view_idx] = try leafSwap(
                        theorem,
                        pattern,
                        hole,
                        meta,
                    );
                }
                // Binders owned by the recover machinery are excluded from
                // generic deferral: a recover law that could not fire means
                // the rule derives nothing (as before), not a family fact
                // whose recipe could never validate.
                const recover_owned = try self.scratch.alloc(bool, bindings.len);
                defer self.scratch.free(recover_owned);
                @memset(recover_owned, false);
                for (v.derived_bindings) |derived_binding| {
                    const rec = switch (derived_binding) {
                        .recover => |r| r,
                        .abstract => continue,
                    };
                    if (rec.target_view_idx < recover_owned.len) {
                        recover_owned[rec.target_view_idx] = true;
                    }
                    if (rec.source_view_idx < recover_owned.len) {
                        recover_owned[rec.source_view_idx] = true;
                    }
                }
                try self.deferConclusionBinders(
                    v.concl,
                    v.arg_infos,
                    recover_owned,
                    bindings,
                );
                break :blk (try OpenTerms.instantiateTemplateConcrete(
                    theorem,
                    v.concl,
                    bindings,
                )) orelse return null;
            }
            // No view: the raw conclusion becomes the surface. Unresolved
            // non-bound conclusion binders are deferred as universal metas
            // (the bot_elim case: `g ⊢ ⊥ > g ⊢ a` fires as the family fact
            // `g ⊢ ?a`); a buried witness needing rewriting is the
            // normalization case, deliberately out of scope here. Metas
            // inherited from frontier source shapes ride along.
            try self.deferConclusionBinders(rule.concl, rule.args, null, bindings);
            break :blk (try OpenTerms.instantiateTemplateConcrete(
                theorem,
                rule.concl,
                bindings,
            )) orelse return null;
        };
        // Bake any forward-join groundings into the surface: a consequent like
        // `Q ?t` derived by joining `P ?t → Q ?t` with `P c` becomes the
        // concrete fact `Q c`. Inert (identity) when no join grounded a meta.
        const shape = try derefJoinOverlay(
            store,
            theorem,
            &self.groundings,
            shape_raw,
        );
        // A surface with no rigid root would match every goal of its sort —
        // an absorber, not a fact. Reject it; concrete shapes pass as before.
        switch (theorem.interner.node(shape).*) {
            .placeholder => |pid| if (store.info(pid) != null) return null,
            else => {},
        }

        // Project the solved/deferred values into rule-binder space for the
        // recipe's explicit bindings (ascending arg order for stable
        // rendering).
        var binding_list = std.ArrayListUnmanaged(DerivedRefBinding){};
        if (view) |v| {
            for (0..rule.args.len) |arg_idx| {
                for (v.binder_map, 0..) |maybe_rule_idx, vi| {
                    if (maybe_rule_idx != arg_idx) continue;
                    const raw = bindings[vi] orelse continue;
                    try binding_list.append(self.arena, .{
                        .arg_index = arg_idx,
                        .value = try derefJoinOverlay(
                            store,
                            theorem,
                            &self.groundings,
                            raw,
                        ),
                    });
                    break;
                }
            }
        } else {
            for (bindings, 0..) |maybe_value, arg_idx| {
                const raw = maybe_value orelse continue;
                try binding_list.append(self.arena, .{
                    .arg_index = arg_idx,
                    .value = try derefJoinOverlay(
                        store,
                        theorem,
                        &self.groundings,
                        raw,
                    ),
                });
            }
        }

        // Every meta the recipe needs solved at use time — this layer's
        // binding values plus every derived source's, recursively — must
        // occur in the shape: the use-time solve assigns exactly the metas
        // the goal match sees, so anything else could never materialize.
        var shape_metas = std.ArrayListUnmanaged(PlaceholderId){};
        defer shape_metas.deinit(self.scratch);
        try store.collectUnsolved(theorem, shape, &shape_metas);
        var required = std.ArrayListUnmanaged(PlaceholderId){};
        defer required.deinit(self.scratch);
        for (binding_list.items) |binding| {
            try store.collectUnsolved(theorem, binding.value, &required);
        }
        // A nested source's universal that this join grounded to a concrete
        // witness is *pinned* in this recipe (re-applied transiently at
        // materialize), not deferred to a use-time goal solve. Only genuinely
        // unsolved source metas stay in `required` and must occur in `shape`.
        var pinned = std.ArrayListUnmanaged(types.MetaAssignment){};
        defer pinned.deinit(self.scratch);
        for (chosen) |src_idx| {
            switch (self.sources.items[src_idx].source) {
                .pool => {},
                .derived => |child_idx| {
                    const child = self.derived.items[child_idx];
                    for (child.required_metas) |meta_id| {
                        if (groundingLookup(&self.groundings, meta_id)) |val| {
                            try appendDistinctPin(
                                &pinned,
                                self.scratch,
                                meta_id,
                                try derefJoinOverlay(
                                    store,
                                    theorem,
                                    &self.groundings,
                                    val,
                                ),
                            );
                        } else {
                            try appendDistinctMeta(
                                &required,
                                self.scratch,
                                meta_id,
                            );
                        }
                    }
                },
            }
        }
        for (required.items) |meta_id| {
            if (std.mem.indexOfScalar(
                PlaceholderId,
                shape_metas.items,
                meta_id,
            ) == null) return null;
        }

        const sources = try self.arena.alloc(DerivedSource, chosen.len);
        var depth: usize = 1;
        for (chosen, 0..) |src_idx, idx| {
            const entry = self.sources.items[src_idx];
            sources[idx] = entry.source;
            depth = @max(depth, entry.depth + 1);
        }

        return .{
            .rule_id = rule_id,
            .rule_name = rule.name,
            .declaration_order = rule_id,
            .sources = sources,
            .shape = shape,
            .bindings = try binding_list.toOwnedSlice(self.arena),
            .required_metas = try self.arena.dupe(
                PlaceholderId,
                required.items,
            ),
            .pinned_metas = try self.arena.dupe(
                types.MetaAssignment,
                pinned.items,
            ),
            .has_universal_meta = shape_metas.items.len != 0,
            .source_depth = depth,
        };
    }

    /// Defer each still-unresolved non-bound binder occurring in the
    /// conclusion template as a universal metavariable, making the derived
    /// ref a family fact (`g ⊢ ?a` from a `⊥`-elimination). The use-time
    /// goal match solves the meta exactly like a `@recover`-deferred
    /// witness. Bound-class binders are never deferred — a hidden binder
    /// needs a variable witness, not an arbitrary term — so a conclusion
    /// mentioning an unbound bound-class binder still fails instantiation
    /// (null shape) as before.
    fn deferConclusionBinders(
        self: *Saturator,
        concl: TemplateExpr,
        arg_infos: []const ArgInfo,
        excluded: ?[]const bool,
        bindings: []?ExprId,
    ) !void {
        switch (concl) {
            .binder => |idx| {
                if (idx >= bindings.len or idx >= arg_infos.len) return;
                if (bindings[idx] != null) return;
                if (excluded) |mask| if (mask[idx]) return;
                const info = arg_infos[idx];
                if (info.bound) return;
                bindings[idx] = try self.store.mint(
                    self.theorem,
                    info.sort_name,
                    std.math.maxInt(u55),
                    .universal,
                );
            },
            .app => |app| for (app.args) |arg| {
                try self.deferConclusionBinders(
                    arg,
                    arg_infos,
                    excluded,
                    bindings,
                );
            },
        }
    }

    /// Recipe identity key: rule + source tuple. Pool sources are keyed by
    /// their expression (not their label), so two refs stating the same fact
    /// collapse to one derivation.
    fn recipeKey(
        self: *Saturator,
        rule_id: u32,
        chosen: []const usize,
    ) ![]u8 {
        var out = std.ArrayListUnmanaged(u8){};
        errdefer out.deinit(self.arena);
        try out.append(self.arena, 'r');
        try appendKeyInt(&out, self.arena, rule_id);
        for (chosen) |src_idx| {
            const entry = self.sources.items[src_idx];
            switch (entry.source) {
                .pool => {
                    try out.append(self.arena, 'p');
                    try appendKeyInt(&out, self.arena, entry.expr);
                },
                .derived => |child_idx| {
                    try out.append(self.arena, 'd');
                    try appendKeyInt(&out, self.arena, child_idx);
                },
            }
        }
        return try out.toOwnedSlice(self.arena);
    }

    /// Canonical surface key: tree-serialized with universal metas numbered
    /// by first occurrence, so shapes differing only in fresh meta ids
    /// collide. Concrete pool expressions serialize through the same walk.
    fn shapeKey(self: *Saturator, shape: ExprId) ![]u8 {
        var out = std.ArrayListUnmanaged(u8){};
        errdefer out.deinit(self.arena);
        try out.append(self.arena, 's');
        var meta_numbers = std.AutoHashMapUnmanaged(PlaceholderId, u32).empty;
        defer meta_numbers.deinit(self.scratch);
        try self.appendShapeKey(&out, &meta_numbers, shape);
        return try out.toOwnedSlice(self.arena);
    }

    fn appendShapeKey(
        self: *Saturator,
        out: *std.ArrayListUnmanaged(u8),
        meta_numbers: *std.AutoHashMapUnmanaged(PlaceholderId, u32),
        expr_id: ExprId,
    ) !void {
        switch (self.theorem.interner.node(expr_id).*) {
            .variable => |var_id| switch (var_id) {
                .theorem_var => |idx| {
                    try out.append(self.arena, 'v');
                    try appendKeyInt(out, self.arena, idx);
                },
                .dummy_var => |idx| {
                    try out.append(self.arena, 'w');
                    try appendKeyInt(out, self.arena, idx);
                },
            },
            .placeholder => |pid| {
                if (self.store.info(pid) != null) {
                    const gop = try meta_numbers.getOrPut(self.scratch, pid);
                    if (!gop.found_existing) {
                        gop.value_ptr.* = @intCast(meta_numbers.count() - 1);
                    }
                    try out.append(self.arena, 'm');
                    try appendKeyInt(out, self.arena, gop.value_ptr.*);
                } else {
                    // Standard placeholders (unfold dummies) are stable
                    // leaves whose identity matters.
                    try out.append(self.arena, 'q');
                    try appendKeyInt(out, self.arena, pid);
                }
            },
            .app => |app| {
                try out.append(self.arena, 'a');
                try appendKeyInt(out, self.arena, app.term_id);
                try appendKeyInt(out, self.arena, app.args.len);
                for (app.args) |arg| {
                    try self.appendShapeKey(out, meta_numbers, arg);
                }
            },
        }
    }
};

fn appendKeyInt(
    out: *std.ArrayListUnmanaged(u8),
    allocator: std.mem.Allocator,
    value: anytype,
) !void {
    var buf: [8]u8 = undefined;
    std.mem.writeInt(u64, &buf, @intCast(value), .little);
    try out.appendSlice(allocator, &buf);
}

fn appendDistinctMeta(
    list: *std.ArrayListUnmanaged(PlaceholderId),
    allocator: std.mem.Allocator,
    meta_id: PlaceholderId,
) !void {
    if (std.mem.indexOfScalar(
        PlaceholderId,
        list.items,
        meta_id,
    ) != null) return;
    try list.append(allocator, meta_id);
}

fn appendDistinctPin(
    list: *std.ArrayListUnmanaged(types.MetaAssignment),
    allocator: std.mem.Allocator,
    meta_id: PlaceholderId,
    value: ExprId,
) !void {
    for (list.items) |pin| {
        if (pin.meta == meta_id) return;
    }
    try list.append(allocator, .{ .meta = meta_id, .value = value });
}

/// Memoized one-layer transparent-def unfoldings of source expressions. The
/// unfolding of a given expression is deterministic apart from the fresh
/// placeholders it mints, and a placeholder is a no-opinion leaf for every
/// later match — so reusing the first unfolding is semantically equivalent to
/// re-unfolding, while spending dep slots once instead of per attempt.
const UnfoldCache = struct {
    allocator: std.mem.Allocator,
    map: std.AutoHashMapUnmanaged(ExprId, ?ExprId) = .empty,

    fn deinit(self: *UnfoldCache) void {
        self.map.deinit(self.allocator);
    }
};

/// Demand-driven forward premise matcher. It behaves like
/// `TheoremContext.matchTemplate` while heads line up, but when a template app
/// meets a concrete app with a different head it unfolds the concrete head one
/// transparent-def layer and retries the same template. Binder-introducing defs
/// are allowed here because this is search-guidance extraction: unfold dummies
/// materialize as ordinary placeholders, which only loosen later matching, and
/// every emitted recipe is still checked by `tryCandidate`.
fn matchForwardTemplate(
    context: *const Context,
    theorem: *TheoremContext,
    cache: *UnfoldCache,
    store: *const MetaStore,
    groundings: *std.ArrayListUnmanaged(types.MetaAssignment),
    scratch: std.mem.Allocator,
    template: @import("../../rules.zig").TemplateExpr,
    expr_id: ExprId,
    bindings: []?ExprId,
    unfold_depth: usize,
) !bool {
    if (unfold_depth > max_premise_unfold_layers) return false;
    return switch (template) {
        .binder => |idx| blk: {
            if (idx >= bindings.len) break :blk false;
            if (bindings[idx]) |existing| {
                if (existing == expr_id) break :blk true;
                // A binder bound by an earlier premise to a meta-carrying
                // family value (`a := P ?t`) meets this concrete premise
                // (`P c`): ground the embedded nested-source metas against it
                // in the overlay (`?t := c`). The family fact stays general;
                // the witness is baked into the produced fact's recipe.
                break :blk try unifyJoinOverlay(
                    store,
                    theorem,
                    groundings,
                    scratch,
                    existing,
                    expr_id,
                );
            }
            bindings[idx] = expr_id;
            break :blk true;
        },
        .app => |app| blk: {
            const concrete = switch (theorem.interner.node(expr_id).*) {
                .app => |a| a,
                else => break :blk false,
            };
            if (concrete.term_id == app.term_id and
                concrete.args.len == app.args.len)
            {
                for (app.args, concrete.args) |tmpl_arg, conc_arg| {
                    if (!try matchForwardTemplate(
                        context,
                        theorem,
                        cache,
                        store,
                        groundings,
                        scratch,
                        tmpl_arg,
                        conc_arg,
                        bindings,
                        unfold_depth,
                    )) break :blk false;
                }
                break :blk true;
            }
            if (unfold_depth >= max_premise_unfold_layers) {
                break :blk false;
            }
            const unfolded = try unfoldConcreteHeadOnce(
                context,
                theorem,
                cache,
                expr_id,
                concrete,
            ) orelse break :blk false;
            break :blk try matchForwardTemplate(
                context,
                theorem,
                cache,
                store,
                groundings,
                scratch,
                template,
                unfolded,
                bindings,
                unfold_depth + 1,
            );
        },
    };
}

/// Look up `pid` in the forward-join overlay (linear; the overlay holds only
/// the few metas grounded by the current premise tuple).
fn groundingLookup(
    groundings: *const std.ArrayListUnmanaged(types.MetaAssignment),
    pid: PlaceholderId,
) ?ExprId {
    for (groundings.items) |g| {
        if (g.meta == pid) return g.value;
    }
    return null;
}

/// Forward-join overlay unification. `existing` is a rule-binder value bound by
/// an earlier premise that may embed a nested source's universal meta; `incoming`
/// is the (concrete) premise expression. Where `existing` shows a pool-store
/// meta with no value yet, record the witness in the local `groundings` overlay
/// rather than mutating the shared store. Consistency is checked against prior
/// store assignments and prior overlay entries. Returns false on a rigid clash
/// or an inconsistent repeat witness. Structural only (no def unfolding) — a
/// correspondence needing normalization fails cleanly, as elsewhere in search.
fn unifyJoinOverlay(
    store: *const MetaStore,
    theorem: *TheoremContext,
    groundings: *std.ArrayListUnmanaged(types.MetaAssignment),
    scratch: std.mem.Allocator,
    existing: ExprId,
    incoming: ExprId,
) !bool {
    if (existing == incoming) return true;
    switch (theorem.interner.node(existing).*) {
        .placeholder => |pid| {
            // Non-meta placeholder (unfold dummy): only an identical leaf
            // matches; identity already failed above.
            if (store.info(pid) == null) return false;
            if (store.lookup(pid)) |value| {
                return try unifyJoinOverlay(
                    store,
                    theorem,
                    groundings,
                    scratch,
                    value,
                    incoming,
                );
            }
            if (groundingLookup(groundings, pid)) |value| {
                return try unifyJoinOverlay(
                    store,
                    theorem,
                    groundings,
                    scratch,
                    value,
                    incoming,
                );
            }
            // Occurs check (mirrors `MetaStore.assign`): never record a
            // self-referential grounding, which `derefJoinOverlay` would chase
            // forever. Resolved through store + overlay so an indirect cycle is
            // caught too.
            if (overlayOccurs(store, theorem, groundings, pid, incoming)) {
                return false;
            }
            try groundings.append(scratch, .{ .meta = pid, .value = incoming });
            return true;
        },
        .variable => return false,
        .app => |ea| {
            const na = switch (theorem.interner.node(incoming).*) {
                .app => |a| a,
                else => return false,
            };
            if (ea.term_id != na.term_id or ea.args.len != na.args.len) {
                return false;
            }
            for (ea.args, na.args) |x, y| {
                if (!try unifyJoinOverlay(
                    store,
                    theorem,
                    groundings,
                    scratch,
                    x,
                    y,
                )) return false;
            }
            return true;
        },
    }
}

/// Whether `pid` is reachable from `expr_id` through the shared store and the
/// forward-join overlay — the overlay's occurs check.
fn overlayOccurs(
    store: *const MetaStore,
    theorem: *const TheoremContext,
    groundings: *const std.ArrayListUnmanaged(types.MetaAssignment),
    pid: PlaceholderId,
    expr_id: ExprId,
) bool {
    return switch (theorem.interner.node(expr_id).*) {
        .variable => false,
        .placeholder => |q| blk: {
            if (q == pid) break :blk true;
            if (store.lookup(q)) |value| {
                break :blk overlayOccurs(store, theorem, groundings, pid, value);
            }
            if (groundingLookup(groundings, q)) |value| {
                break :blk overlayOccurs(store, theorem, groundings, pid, value);
            }
            break :blk false;
        },
        .app => |app| blk: {
            for (app.args) |arg| {
                if (overlayOccurs(store, theorem, groundings, pid, arg)) {
                    break :blk true;
                }
            }
            break :blk false;
        },
    };
}

/// Dereference `expr_id` through the shared store *and* the forward-join
/// overlay, reinterning changed apps. Used by `derive` to bake the concrete
/// surface and recipe values of a join-produced fact.
fn derefJoinOverlay(
    store: *const MetaStore,
    theorem: *TheoremContext,
    groundings: *const std.ArrayListUnmanaged(types.MetaAssignment),
    expr_id: ExprId,
) !ExprId {
    // Fast path / historical-identity guarantee: during saturation the shared
    // store holds only deferred (unassigned) universals, so an empty overlay
    // can substitute nothing — the no-join path returns its input untouched
    // (allocation-free), exactly as before forward joins existed.
    if (groundings.items.len == 0) return expr_id;
    switch (theorem.interner.node(expr_id).*) {
        .variable => return expr_id,
        .placeholder => |pid| {
            if (store.lookup(pid)) |value| {
                return try derefJoinOverlay(store, theorem, groundings, value);
            }
            if (groundingLookup(groundings, pid)) |value| {
                return try derefJoinOverlay(store, theorem, groundings, value);
            }
            return expr_id;
        },
        .app => |app| {
            var changed = false;
            const args = try theorem.allocator.alloc(ExprId, app.args.len);
            for (app.args, 0..) |arg, idx| {
                args[idx] = derefJoinOverlay(
                    store,
                    theorem,
                    groundings,
                    arg,
                ) catch |err| {
                    theorem.allocator.free(args);
                    return err;
                };
                if (args[idx] != arg) changed = true;
            }
            if (!changed) {
                theorem.allocator.free(args);
                return expr_id;
            }
            return try theorem.interner.internAppOwned(app.term_id, args);
        },
    }
}

/// Unfold one transparent-def layer of a concrete app for premise matching,
/// memoized per source expression. Dep-slot exhaustion is cached as "not
/// unfoldable": the walk simply learns nothing from this head, and caching it
/// keeps every later attempt from re-tripping the limit.
fn unfoldConcreteHeadOnce(
    context: *const Context,
    theorem: *TheoremContext,
    cache: *UnfoldCache,
    expr_id: ExprId,
    app: ExprModule.ExprNode.App,
) !?ExprId {
    if (cache.map.get(expr_id)) |cached| return cached;
    const result: ?ExprId = blk: {
        const info = prune.defBodyForUnfold(
            context,
            app.term_id,
            true,
        ) orelse break :blk null;
        if (app.args.len != info.nargs) break :blk null;
        break :blk prune.unfoldDefBody(
            theorem,
            info,
            app.args,
        ) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            else => null,
        };
    };
    try cache.map.put(cache.allocator, expr_id, result);
    return result;
}

/// Structural leaf swap: `pattern` with every occurrence of the leaf `hole`
/// replaced by `replacement`. No capture analysis — a solved witness that
/// wrongly mentions an inner bound variable is rejected by ordinary
/// validation in `tryCandidate`, not by search. Shared with the
/// backward open-target construction (the same `@recover` walk applied to an
/// open hypothesis surface instead of a forward conclusion surface).
pub fn leafSwap(
    theorem: *TheoremContext,
    pattern: ExprId,
    hole: ExprId,
    replacement: ExprId,
) !ExprId {
    if (pattern == hole) return replacement;
    const app = switch (theorem.interner.node(pattern).*) {
        .app => |a| a,
        else => return pattern,
    };
    var changed = false;
    const args = try theorem.allocator.alloc(ExprId, app.args.len);
    for (app.args, 0..) |arg, idx| {
        args[idx] = leafSwap(theorem, arg, hole, replacement) catch |err| {
            theorem.allocator.free(args);
            return err;
        };
        if (args[idx] != arg) changed = true;
    }
    if (!changed) {
        theorem.allocator.free(args);
        return pattern;
    }
    return try theorem.interner.internAppOwned(app.term_id, args);
}

pub const SolveResult = enum { ok, conflict };

/// The use-time `@recover` solve: walk `pattern` (the derived shape, or a
/// recover law's pattern containing it) against the concrete `source` in
/// lockstep. Where the pattern holds an unsolved universal meta, the source
/// shows the witness — assign it (repeated occurrences are the same store
/// meta, so consistency is automatic: the second occurrence dereferences and
/// must agree). `hole` positions are skipped (that witness is recovered by
/// ordinary validation). The match is structural only: a correspondence that
/// would need def unfolding or rewriting reports `.conflict` and the branch
/// fails cleanly — the normalization boundary, expected and not a
/// bug.
///
/// TWIN: `witness.solveAcuiInner` is the ACUI-aware variant of this
/// walk for the open-target read-back. They deliberately stay separate: it
/// matches commutative regions member-wise, derefs the pattern up front,
/// threads an attempt budget, and PROPAGATES OutOfMemory (this one folds
/// every failure into `.conflict`, which callers rely on being error-free).
/// A change to the lockstep app-vs-app traversal here likely needs mirroring
/// there.
pub fn solveCorrespondence(
    store: *MetaStore,
    theorem: *TheoremContext,
    source: ExprId,
    pattern: ExprId,
    hole: ?ExprId,
) SolveResult {
    if (hole) |h| if (pattern == h) return .ok;
    switch (theorem.interner.node(pattern).*) {
        .placeholder => |pid| {
            // Standard placeholders (e.g. unfold dummies) are not metas:
            // no opinion, validation arbitrates.
            if (store.info(pid) == null) return .ok;
            if (store.lookup(pid)) |value| {
                return solveCorrespondence(store, theorem, source, value, hole);
            }
            store.assign(theorem, pid, source) catch return .conflict;
            return .ok;
        },
        .variable => return if (source == pattern) .ok else .conflict,
        .app => |pattern_app| {
            switch (theorem.interner.node(source).*) {
                // An unfilled source position may still become anything.
                .placeholder => return .ok,
                .variable => return .conflict,
                .app => |source_app| {
                    if (source_app.term_id != pattern_app.term_id) {
                        return .conflict;
                    }
                    if (source_app.args.len != pattern_app.args.len) {
                        return .conflict;
                    }
                    for (source_app.args, pattern_app.args) |s_arg, p_arg| {
                        if (solveCorrespondence(
                            store,
                            theorem,
                            s_arg,
                            p_arg,
                            hole,
                        ) == .conflict) return .conflict;
                    }
                    return .ok;
                },
            }
        },
    }
}

/// Materialize a derived ref's proof recipe at the store's current (solved)
/// assignments: dereference every recorded binder value in every layer of
/// the recipe (nested derived sources included — shared holes are the same
/// store metas, so one solve covers all layers), name any remaining
/// unfold-dummy placeholders from the theorem's variable pools, and render
/// the values as explicit `(name := $ … $)` bindings on ordinary
/// `RuleApplication`s, derived sources becoming nested inline applications.
/// One namer spans all layers, so a placeholder occurring in several layers
/// renders as one variable. Returns null when a universal meta is still
/// unsolved, a binder is unnamed, or no suitable variable exists for a dummy
/// — a clean branch failure, never a guessed allocation. Rendered strings
/// and the applications' slices live in the pool's arena.
pub fn materializeApplication(
    dpool: *DerivedPool,
    context: *const Context,
    theorem: *TheoremContext,
    theorem_vars: *const NameExprMap,
    avoid_expr: ?ExprId,
    dref: *const DerivedRef,
) !?RuleApplication {
    var scratch_arena = std.heap.ArenaAllocator.init(context.allocator);
    defer scratch_arena.deinit();
    const scratch = scratch_arena.allocator();

    // Re-apply this recipe's per-use pins (nested-source universals a forward
    // join grounded to a concrete witness) so the nested sources dereference to
    // the witness *this* derivation used. Transient: the family fact stays
    // general for other uses. Self-contained — opened and rolled back here so
    // the discipline holds for every caller; concrete resolved values are
    // captured before the rollback.
    const pin_mark = dpool.store.mark();
    const was_open = dpool.store.universal_use_open;
    dpool.store.openUniversalUse();
    defer {
        dpool.store.universal_use_open = was_open;
        dpool.store.rollbackTo(pin_mark);
    }

    // Resolved binding values per recipe layer, in deterministic parent-
    // first DFS order — naming below must not depend on hash-map iteration.
    var resolved = ResolvedRecipe{};
    if (!try resolveRecipeValues(dpool, theorem, dref, scratch, &resolved)) {
        return null;
    }

    var namer = Namer.init(context.allocator);
    defer namer.deinit();
    try namer.collectTheoremVars(theorem, theorem_vars);
    if (avoid_expr) |goal| try namer.markUsed(theorem, goal);
    for (resolved.order.items) |entry| {
        for (entry.values) |value| try namer.markUsed(theorem, value);
    }
    for (resolved.order.items) |entry| {
        for (entry.values) |value| {
            if (!try namer.choosePlaceholderNames(context, theorem, value)) {
                return null;
            }
        }
    }

    var cursor: usize = 0;
    return try renderRecipe(dpool, context, theorem, &namer, dref, &resolved, &cursor);
}

const ResolvedRecipe = struct {
    const Entry = struct {
        dref: *const DerivedRef,
        values: []ExprId,
    };
    // One entry per recipe-tree OCCURRENCE in parent-first DFS order (NOT deduped
    // by `dref`): the same family `DerivedRef` reused across layers with
    // different per-use pins resolves to different witnesses each time, so each
    // occurrence keeps its own values. `renderRecipe` walks the identical DFS and
    // consumes entries through a cursor.
    order: std.ArrayListUnmanaged(Entry) = .{},
};

/// Dereference every binding value across the recipe tree through the store's
/// current assignments, recording one value-set per occurrence in DFS order.
/// Returns false when any layer still holds an unsolved meta. Recipes are
/// acyclic by construction (a derived source always has a strictly lower pool
/// index), so visiting every occurrence terminates.
///
/// Each layer's `pinned_metas` ground the *universal* metas its nested sources
/// require (a forward join grounded a family's `?t` to a concrete witness). The
/// SAME family fact can appear under sibling/nested joins with DIFFERENT
/// groundings (e.g. `P(f(f c))` = `mp[all_elim(t:=f c), mp[all_elim(t:=c), Pc]]`,
/// both `all_elim`s sharing one family `?t`). So a pin is applied SCOPED to the
/// single source whose `required_metas` it grounds, then rolled back before the
/// next sibling — otherwise the first grounding would leak into the second
/// (rendering both witnesses identically and failing validation). The caller's
/// use-time recover solve, plus any still-active ancestor scope, remain in force
/// for this layer's own bindings.
fn resolveRecipeValues(
    dpool: *DerivedPool,
    theorem: *TheoremContext,
    dref: *const DerivedRef,
    scratch: std.mem.Allocator,
    resolved: *ResolvedRecipe,
) anyerror!bool {
    // Resolve this layer's own bindings with its pins active (rolled back before
    // descending, so a nested source re-grounding the same meta is not blocked).
    const own_mark = dpool.store.mark();
    for (dref.pinned_metas) |pin| {
        if (dpool.store.lookup(pin.meta) != null) continue;
        dpool.store.assign(theorem, pin.meta, pin.value) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            else => {},
        };
    }
    const values = try scratch.alloc(ExprId, dref.bindings.len);
    for (dref.bindings, 0..) |binding, idx| {
        const value = try dpool.store.deref(theorem, binding.value);
        if (!dpool.store.isFullySolved(theorem, value)) {
            dpool.store.rollbackTo(own_mark);
            return false;
        }
        values[idx] = value;
    }
    dpool.store.rollbackTo(own_mark);
    try resolved.order.append(scratch, .{ .dref = dref, .values = values });
    for (dref.sources) |source| {
        switch (source) {
            .pool => {},
            .derived => |child_idx| {
                const child = &dpool.refs[child_idx];
                const mark = dpool.store.mark();
                // Apply only this layer's pins that ground a meta the child
                // subtree still requires, so a sibling source's distinct
                // grounding of the same meta is not pre-empted. Skip a meta an
                // ancestor already pinned (a genuinely shared witness).
                for (dref.pinned_metas) |pin| {
                    if (std.mem.indexOfScalar(
                        PlaceholderId,
                        child.required_metas,
                        pin.meta,
                    ) == null) continue;
                    if (dpool.store.lookup(pin.meta) != null) continue;
                    dpool.store.assign(theorem, pin.meta, pin.value) catch |err|
                        switch (err) {
                            error.OutOfMemory => return error.OutOfMemory,
                            // A pin that no longer validates (sort/dep/phase)
                            // goes unapplied; the source then reads as unsolved
                            // and the recipe fails to resolve cleanly below.
                            else => {},
                        };
                }
                const ok = try resolveRecipeValues(
                    dpool,
                    theorem,
                    child,
                    scratch,
                    resolved,
                );
                dpool.store.rollbackTo(mark);
                if (!ok) return false;
            },
        }
    }
    return true;
}

/// Render one recipe layer (and, recursively, its derived sources) into the
/// pool arena using the shared namer and pre-resolved values. `cursor` walks the
/// occurrence list in the SAME parent-first DFS order `resolveRecipeValues`
/// wrote it, so each occurrence of a reused `DerivedRef` renders with its own
/// per-use witnesses.
fn renderRecipe(
    dpool: *DerivedPool,
    context: *const Context,
    theorem: *TheoremContext,
    namer: *const Namer,
    dref: *const DerivedRef,
    resolved: *const ResolvedRecipe,
    cursor: *usize,
) anyerror!?RuleApplication {
    const arena = dpool.arena.allocator();
    const rule = &context.env.rules.items[dref.rule_id];
    if (cursor.* >= resolved.order.items.len) return null;
    const entry = resolved.order.items[cursor.*];
    std.debug.assert(entry.dref == dref);
    cursor.* += 1;
    const values = entry.values;

    const arg_bindings = try arena.alloc(
        ProofScript.ArgBinding,
        dref.bindings.len,
    );
    for (dref.bindings, values, 0..) |binding, value, idx| {
        if (binding.arg_index >= rule.arg_names.len) return null;
        const name = rule.arg_names[binding.arg_index] orelse return null;
        const text = (try namer.render(arena, context, theorem, value)) orelse
            return null;
        arg_bindings[idx] = .{
            .name = name,
            .name_span = zero_span,
            .formula = .{ .text = text, .span = zero_span },
            .span = zero_span,
        };
    }

    const refs = try arena.alloc(Ref, dref.sources.len);
    for (dref.sources, 0..) |source, idx| {
        refs[idx] = switch (source) {
            .pool => |ref| ref,
            .derived => |child_idx| .{
                .application = (try renderRecipe(
                    dpool,
                    context,
                    theorem,
                    namer,
                    &dpool.refs[child_idx],
                    resolved,
                    cursor,
                )) orelse return null,
            },
        };
    }
    return RuleApplication{
        .rule_name = dref.rule_name,
        .rule_span = zero_span,
        .binding_list_span = null,
        .arg_bindings = arg_bindings,
        .refs_span = if (refs.len == 0) null else zero_span,
        .refs = refs,
        .span = zero_span,
    };
}

/// Variable naming for recipe rendering: reverse name lookup for real
/// variables, plus deterministic fresh-variable choice (sorted theorem vars
/// first, then the sort's `@vars` pool) for unfold-dummy placeholders.
/// Shared with the explicit-binding renderer in `backward/backtrack.zig`.
pub const Namer = struct {
    allocator: std.mem.Allocator,
    /// Encoded VarId -> source name.
    names: std.AutoHashMapUnmanaged(u64, []const u8) = .empty,
    /// Bound theorem vars eligible as dummy stand-ins, sorted by name.
    candidates: std.ArrayListUnmanaged(Candidate) = .{},
    /// Encoded VarIds that occur in the goal or in any rendered value (a
    /// chosen stand-in must not collide with these).
    used: std.AutoHashMapUnmanaged(u64, void) = .empty,
    chosen: std.AutoHashMapUnmanaged(PlaceholderId, []const u8) = .empty,

    const Candidate = struct {
        name: []const u8,
        key: u64,
        sort_name: []const u8,
    };

    pub fn init(allocator: std.mem.Allocator) Namer {
        return .{ .allocator = allocator };
    }

    pub fn deinit(self: *Namer) void {
        self.names.deinit(self.allocator);
        self.candidates.deinit(self.allocator);
        self.used.deinit(self.allocator);
        self.chosen.deinit(self.allocator);
        self.* = undefined;
    }

    pub fn collectTheoremVars(
        self: *Namer,
        theorem: *const TheoremContext,
        theorem_vars: *const NameExprMap,
    ) !void {
        try interner_view.invertNameMap(
            self.allocator,
            theorem,
            theorem_vars,
            &self.names,
        );
        var iter = theorem_vars.iterator();
        while (iter.next()) |entry| {
            const var_id = theorem.parser_vars.get(entry.value_ptr.*) orelse
                continue;
            switch (var_id) {
                .theorem_var => |idx| {
                    if (idx >= theorem.arg_infos.len) continue;
                    const info = theorem.arg_infos[idx];
                    // Only bound-class vars can stand in for a hidden bound
                    // dummy.
                    if (!info.bound) continue;
                    try self.candidates.append(self.allocator, .{
                        .name = entry.key_ptr.*,
                        .key = var_id.hashKey(),
                        .sort_name = info.sort_name,
                    });
                },
                .dummy_var => {},
            }
        }
        std.mem.sort(Candidate, self.candidates.items, {}, candidateLessThan);
    }

    fn candidateLessThan(_: void, lhs: Candidate, rhs: Candidate) bool {
        return std.mem.lessThan(u8, lhs.name, rhs.name);
    }

    pub fn markUsed(
        self: *Namer,
        theorem: *const TheoremContext,
        expr_id: ExprId,
    ) !void {
        switch (theorem.interner.node(expr_id).*) {
            .variable => |var_id| try self.used.put(
                self.allocator,
                var_id.hashKey(),
                {},
            ),
            .placeholder => {},
            .app => |app| for (app.args) |arg| {
                try self.markUsed(theorem, arg);
            },
        }
    }

    /// Pick a concrete variable name for every standard placeholder in
    /// `expr_id`. Returns false when some placeholder has no suitable
    /// variable (no matching theorem var or `@vars` pool entry) — the branch
    /// then fails cleanly rather than allocating a dummy.
    pub fn choosePlaceholderNames(
        self: *Namer,
        context: *const Context,
        theorem: *const TheoremContext,
        expr_id: ExprId,
    ) !bool {
        switch (theorem.interner.node(expr_id).*) {
            .variable => return true,
            .placeholder => |pid| {
                if (self.chosen.contains(pid)) return true;
                if (pid >= theorem.theorem_placeholders.items.len) return false;
                const sort_name =
                    theorem.theorem_placeholders.items[pid].sort_name;
                for (self.candidates.items) |candidate| {
                    if (!std.mem.eql(u8, candidate.sort_name, sort_name)) {
                        continue;
                    }
                    if (self.used.contains(candidate.key)) continue;
                    try self.used.put(self.allocator, candidate.key, {});
                    try self.chosen.put(self.allocator, pid, candidate.name);
                    return true;
                }
                // Fall back to the sort's @vars pool: the binding parser
                // materializes these names on demand (`ensureMathTextVars`).
                if (context.sort_vars.getPool(sort_name)) |pool| {
                    for (pool.tokens.items) |token| {
                        if (self.tokenAlreadyChosen(token)) continue;
                        if (self.nameIsTheoremVar(token)) continue;
                        try self.chosen.put(self.allocator, pid, token);
                        return true;
                    }
                }
                return false;
            },
            .app => |app| {
                for (app.args) |arg| {
                    if (!try self.choosePlaceholderNames(
                        context,
                        theorem,
                        arg,
                    )) return false;
                }
                return true;
            },
        }
    }

    fn tokenAlreadyChosen(self: *const Namer, token: []const u8) bool {
        var iter = self.chosen.valueIterator();
        while (iter.next()) |name| {
            if (std.mem.eql(u8, name.*, token)) return true;
        }
        return false;
    }

    fn nameIsTheoremVar(self: *const Namer, token: []const u8) bool {
        var iter = self.names.valueIterator();
        while (iter.next()) |name| {
            if (std.mem.eql(u8, name.*, token)) return true;
        }
        return false;
    }

    /// Name resolver for the shared `interner_view.View`. Returns `.missing`
    /// for an unnamed variable or an unchosen placeholder, which fails the
    /// render cleanly (search never fabricates a coordinate name).
    pub fn variableAtom(
        self: *const Namer,
        var_id: VarId,
    ) pretty_print.NodeInfo(ExprId) {
        if (self.names.get(var_id.hashKey())) |name| return .{ .atom = name };
        return .missing;
    }

    pub fn placeholderAtom(
        self: *const Namer,
        pid: PlaceholderId,
    ) pretty_print.NodeInfo(ExprId) {
        if (self.chosen.get(pid)) |name| return .{ .atom = name };
        return .missing;
    }

    /// Render `expr_id` as parseable math text using the declared notation
    /// (with minimal parenthesization), falling back to prefix application form
    /// (`term arg1 (inner arg) …`) for terms without notation. Variables and
    /// placeholders print by their resolved source name. Returns null for
    /// anything unrenderable (unnamed variable, leftover meta).
    pub fn render(
        self: *const Namer,
        arena: std.mem.Allocator,
        context: *const Context,
        theorem: *const TheoremContext,
        expr_id: ExprId,
    ) !?[]const u8 {
        const view = interner_view.View(*const Namer){
            .resolver = self,
            .theorem = theorem,
            .env = context.env,
        };
        return pretty_print.render(arena, context.parser, view, expr_id);
    }
};
