const std = @import("std");
const ExprId = @import("./expr.zig").ExprId;
const ExprNode = @import("./expr.zig").ExprNode;
const TheoremContext = @import("./expr.zig").TheoremContext;
const GlobalEnv = @import("./env.zig").GlobalEnv;
const RewriteRegistry = @import("./rewrite_registry.zig").RewriteRegistry;
const ResolvedStructuralCombiner =
    @import("./rewrite_registry.zig").ResolvedStructuralCombiner;
const DefOps = @import("./def_ops.zig");

pub const LeafInfo = struct {
    expr_id: ExprId,
    is_def: bool,
};

const LeafState = struct {
    old_expr: ExprId,
    new_expr: ExprId,
    is_def: bool,
};

pub const Context = struct {
    allocator: std.mem.Allocator,
    theorem: *TheoremContext,
    env: *const GlobalEnv,
    registry: *RewriteRegistry,
    /// Lazily created def_ops context reused by every def-eq query made
    /// through this support context (the whole common-target recursion and
    /// the same-side coverage loops used to build one per leaf pair, cold
    /// caches each time). Created only via a stable `*Context`, so the
    /// by-value copies of a *fresh* support context (helpers returning one)
    /// are safe: the field is still null at that point. Holders must call
    /// `deinit` (and must not copy a context after first use).
    def_ops_ctx: ?DefOps.Context = null,
    /// Lazily computed: does the environment declare any concrete def
    /// (`is_def` with a body) at all? Whole theories commonly declare none,
    /// and `isDefBearing` (hence every def-unfolding probe it gates) then
    /// short-circuits to false in O(1) instead of walking exprs and probing
    /// the def caches for answers that cannot be anything but null. Safe to
    /// snapshot per context: the term table only changes between statements,
    /// and no support context outlives the statement that created it.
    env_has_concrete_defs: ?bool = null,
    /// Per-context memos for the registry's structural-combiner resolution,
    /// including the NEGATIVE answer. The registry itself must not cache
    /// negatives (a combiner unresolved only because its assoc/unit rules
    /// aren't declared yet can resolve after a later statement), but within
    /// one statement the answer is a constant — and every semantic-compare
    /// pair otherwise re-runs the registry probes (for the sort fallback, a
    /// linear scan over all combiners) to re-learn it. Same statement-scoped
    /// lifetime argument as `env_has_concrete_defs`; sort keys are env-owned
    /// stable strings. The by-term memo is a dense term-id-indexed array —
    /// this sits under every semantic-compare node visit, where even a hash
    /// probe costs about as much as the registry lookup it replaces.
    combiner_by_term: std.ArrayListUnmanaged(CombinerMemoSlot) = .empty,
    combiner_by_sort: std.StringHashMapUnmanaged(
        ?ResolvedStructuralCombiner,
    ) = .empty,

    const CombinerMemoSlot = union(enum) {
        unknown,
        resolved: ?ResolvedStructuralCombiner,
    };

    pub fn init(
        allocator: std.mem.Allocator,
        theorem: *TheoremContext,
        env: *const GlobalEnv,
        registry: *RewriteRegistry,
    ) Context {
        return .{
            .allocator = allocator,
            .theorem = theorem,
            .env = env,
            .registry = registry,
        };
    }

    pub fn deinit(self: *Context) void {
        if (self.def_ops_ctx) |*ctx| ctx.deinit();
        self.combiner_by_term.deinit(self.allocator);
        self.combiner_by_sort.deinit(self.allocator);
    }

    fn defOps(self: *Context) *DefOps.Context {
        if (self.def_ops_ctx == null) {
            self.def_ops_ctx = DefOps.Context.initWithRegistry(
                self.allocator,
                self.theorem,
                self.env,
                self.registry,
            );
        }
        return &self.def_ops_ctx.?;
    }

    pub fn getExprSort(self: *const Context, expr_id: ExprId) ?[]const u8 {
        const node = self.theorem.interner.node(expr_id);
        return switch (node.*) {
            .app => |app| if (app.term_id < self.env.terms.items.len)
                self.env.terms.items[app.term_id].ret_sort_name
            else
                null,
            .variable, .placeholder => self.theorem.currentLeafSortName(expr_id),
        };
    }

    pub fn sharedStructuralCombiner(
        self: *Context,
        lhs: ExprId,
        rhs: ExprId,
    ) anyerror!?ResolvedStructuralCombiner {
        const lhs_node = self.theorem.interner.node(lhs);
        switch (lhs_node.*) {
            .app => |app| if (try self.resolveCombinerForTerm(
                app.term_id,
            )) |acui| {
                if (self.exprMatchesCombinerSort(rhs, acui)) return acui;
            },
            .variable => {},
            .placeholder => {},
        }
        const rhs_node = self.theorem.interner.node(rhs);
        switch (rhs_node.*) {
            .app => |app| if (try self.resolveCombinerForTerm(
                app.term_id,
            )) |acui| {
                if (self.exprMatchesCombinerSort(lhs, acui)) return acui;
            },
            .variable => {},
            .placeholder => {},
        }
        const lhs_sort = self.getExprSort(lhs) orelse return null;
        const rhs_sort = self.getExprSort(rhs) orelse return null;
        if (!std.mem.eql(u8, lhs_sort, rhs_sort)) return null;
        return try self.resolveCombinerForSort(lhs_sort);
    }

    fn resolveCombinerForTerm(
        self: *Context,
        term_id: u32,
    ) anyerror!?ResolvedStructuralCombiner {
        if (term_id < self.combiner_by_term.items.len) {
            switch (self.combiner_by_term.items[term_id]) {
                .resolved => |hit| return hit,
                .unknown => {},
            }
        }
        const resolved = try self.registry.resolveStructuralCombiner(
            self.env,
            term_id,
        );
        // Memo-or-forget on OOM.
        memo: {
            while (self.combiner_by_term.items.len <= term_id) {
                self.combiner_by_term.append(
                    self.allocator,
                    .unknown,
                ) catch break :memo;
            }
            self.combiner_by_term.items[term_id] = .{ .resolved = resolved };
        }
        return resolved;
    }

    fn resolveCombinerForSort(
        self: *Context,
        sort_name: []const u8,
    ) anyerror!?ResolvedStructuralCombiner {
        if (self.combiner_by_sort.get(sort_name)) |hit| return hit;
        const resolved = try self.registry.resolveStructuralCombinerForSort(
            self.env,
            sort_name,
        );
        // Memo-or-forget on OOM.
        self.combiner_by_sort.put(self.allocator, sort_name, resolved) catch {};
        return resolved;
    }

    pub fn exprMatchesCombinerSort(
        self: *Context,
        expr_id: ExprId,
        acui: ResolvedStructuralCombiner,
    ) bool {
        const sort_name = self.getExprSort(expr_id) orelse return false;
        if (acui.head_term_id >= self.env.terms.items.len) return false;
        return std.mem.eql(
            u8,
            sort_name,
            self.env.terms.items[acui.head_term_id].ret_sort_name,
        );
    }

    pub fn collectLeafInfos(
        self: *Context,
        expr_id: ExprId,
        head_term_id: u32,
        out: *std.ArrayListUnmanaged(LeafInfo),
    ) anyerror!void {
        const node = self.theorem.interner.node(expr_id);
        switch (node.*) {
            .app => |app| {
                if (app.term_id == head_term_id and app.args.len == 2) {
                    try self.collectLeafInfos(app.args[0], head_term_id, out);
                    try self.collectLeafInfos(app.args[1], head_term_id, out);
                    return;
                }
            },
            .variable => {},
            .placeholder => {},
        }
        try out.append(self.allocator, .{
            .expr_id = expr_id,
            .is_def = self.isDefBearing(expr_id),
        });
    }

    pub fn collectConcreteSetItems(
        self: *Context,
        expr_id: ExprId,
        acui: ResolvedStructuralCombiner,
        out: *std.ArrayListUnmanaged(ExprId),
    ) anyerror!void {
        const canonical = try self.canonicalizeAcuiExact(expr_id, acui);
        try self.collectConcreteSetItemsExact(canonical, acui, out);
    }

    fn collectConcreteSetItemsExact(
        self: *Context,
        expr_id: ExprId,
        acui: ResolvedStructuralCombiner,
        out: *std.ArrayListUnmanaged(ExprId),
    ) anyerror!void {
        const node = self.theorem.interner.node(expr_id);
        switch (node.*) {
            .variable => try self.appendSetItem(out, expr_id),
            .placeholder => try self.appendSetItem(out, expr_id),
            .app => |app| {
                if (app.term_id == acui.head_term_id and app.args.len == 2) {
                    try self.collectConcreteSetItemsExact(
                        app.args[0],
                        acui,
                        out,
                    );
                    try self.collectConcreteSetItemsExact(
                        app.args[1],
                        acui,
                        out,
                    );
                    return;
                }
                if (app.term_id == acui.unit_term_id and app.args.len == 0 and
                    acui.supportsLeftUnit() and acui.supportsRightUnit())
                {
                    return;
                }
                try self.appendSetItem(out, expr_id);
            },
        }
    }

    pub fn rebuildAcuiTree(
        self: *Context,
        items: []const ExprId,
        head_term_id: u32,
        unit_term_id: u32,
    ) anyerror!ExprId {
        if (items.len == 0) {
            return try self.theorem.interner.internApp(unit_term_id, &.{});
        }
        if (items.len == 1) return items[0];

        var current = items[items.len - 1];
        var idx = items.len - 1;
        while (idx > 0) {
            idx -= 1;
            current = try self.theorem.interner.internApp(
                head_term_id,
                &[_]ExprId{ items[idx], current },
            );
        }
        return current;
    }

    pub fn buildCanonicalAcuiFromItems(
        self: *Context,
        items: []const ExprId,
        acui: ResolvedStructuralCombiner,
    ) anyerror!ExprId {
        const sorted = try self.allocator.dupe(ExprId, items);
        defer self.allocator.free(sorted);

        var idx: usize = 1;
        while (idx < sorted.len) : (idx += 1) {
            const item = sorted[idx];
            var pos = idx;
            while (pos > 0 and compareExprIds(
                self.theorem,
                sorted[pos - 1],
                item,
            ) == .gt) : (pos -= 1) {
                sorted[pos] = sorted[pos - 1];
            }
            sorted[pos] = item;
        }

        var unique = std.ArrayListUnmanaged(ExprId){};
        defer unique.deinit(self.allocator);
        for (sorted) |item| {
            if (unique.items.len != 0 and
                compareExprIds(
                    self.theorem,
                    unique.items[unique.items.len - 1],
                    item,
                ) == .eq and acui.idem_id != null)
            {
                continue;
            }
            try unique.append(self.allocator, item);
        }
        return try self.rebuildAcuiTree(
            unique.items,
            acui.head_term_id,
            acui.unit_term_id,
        );
    }

    pub fn computeSameSideTargets(
        self: *Context,
        leaves: []const LeafInfo,
        unit_expr: ExprId,
        acui: ResolvedStructuralCombiner,
    ) anyerror![]ExprId {
        const targets = try self.allocator.alloc(ExprId, leaves.len);
        for (leaves, 0..) |leaf, idx| {
            targets[idx] = leaf.expr_id;
            if (leaf.expr_id == unit_expr or leaf.is_def) continue;
            for (leaves) |owner| {
                if (!owner.is_def) continue;
                if (try self.defCoversConcrete(
                    owner.expr_id,
                    leaf.expr_id,
                    acui,
                )) {
                    targets[idx] = owner.expr_id;
                    break;
                }
            }
        }
        return targets;
    }

    pub fn canonicalizeAcui(
        self: *Context,
        expr_id: ExprId,
        acui: ResolvedStructuralCombiner,
    ) anyerror!ExprId {
        var leaves = std.ArrayListUnmanaged(LeafInfo){};
        defer leaves.deinit(self.allocator);
        try self.collectLeafInfos(expr_id, acui.head_term_id, &leaves);

        const unit_expr = try self.theorem.interner.internApp(
            acui.unit_term_id,
            &.{},
        );
        const targets = try self.computeSameSideTargets(
            leaves.items,
            unit_expr,
            acui,
        );
        defer self.allocator.free(targets);

        const rebuilt = try self.rebuildAcuiTree(
            targets,
            acui.head_term_id,
            acui.unit_term_id,
        );
        return try self.canonicalizeAcuiExact(rebuilt, acui);
    }

    pub fn isDefBearing(self: *Context, expr_id: ExprId) bool {
        if (!self.envHasConcreteDefs()) return false;
        // The per-expr verdicts share the theorem's def-cache fixed-env
        // invariant (one env per theorem context).
        self.theorem.assertDefOpsCacheIdentity(@intFromPtr(self.env), 0);
        return self.isDefBearingMemo(expr_id);
    }

    fn envHasConcreteDefs(self: *Context) bool {
        if (self.env_has_concrete_defs == null) {
            self.env_has_concrete_defs = for (self.env.terms.items) |*term| {
                if (term.is_def and term.body != null) break true;
            } else false;
        }
        return self.env_has_concrete_defs.?;
    }

    fn isDefBearingMemo(self: *Context, expr_id: ExprId) bool {
        const node = self.theorem.interner.node(expr_id);
        const app = switch (node.*) {
            .app => |value| value,
            .variable => return false,
            .placeholder => return false,
        };
        if (self.theorem.def_bearing_cache.get(expr_id)) |cached| {
            return cached;
        }
        var result = false;
        if (app.term_id < self.env.terms.items.len) {
            const term = &self.env.terms.items[app.term_id];
            result = term.is_def and term.body != null;
        }
        if (!result) {
            for (app.args) |arg| {
                if (self.isDefBearingMemo(arg)) {
                    result = true;
                    break;
                }
            }
        }
        // Memo-or-forget on OOM: the verdict is still correct without the
        // cache entry.
        self.theorem.def_bearing_cache.put(
            self.theorem.allocator,
            expr_id,
            result,
        ) catch {};
        return result;
    }

    pub fn buildCommonTarget(
        self: *Context,
        lhs: ExprId,
        rhs: ExprId,
    ) anyerror!?ExprId {
        if (lhs == rhs) return lhs;
        // The two def-unfolding steps can only make progress through a
        // concrete def: `compareTransparent` on distinct interned exprs
        // needs `planDefToTarget` (a def-headed subterm) to get past a
        // structural mismatch, and `instantiateDefTowardExpr` bails unless
        // its expr is def-headed. Hash-consing makes "distinct ids, no def
        // anywhere" a proof that both return null, so skip their per-pair
        // cache probes entirely — semantic dedup calls this for every
        // candidate item pair, and def-free leaves are the common case.
        if (self.isDefBearing(lhs) or self.isDefBearing(rhs)) {
            if (try self.buildDirectTransparentCommonTarget(lhs, rhs)) |direct| {
                return direct;
            }
            if (try self.buildSemanticDefCommonTarget(lhs, rhs)) |semantic| {
                return semantic;
            }
        }
        if (try self.buildAcuiCommonTarget(lhs, rhs)) |acui| {
            return acui;
        }
        return try self.buildNonAcuiCommonTarget(lhs, rhs);
    }

    fn buildDirectTransparentCommonTarget(
        self: *Context,
        lhs: ExprId,
        rhs: ExprId,
    ) anyerror!?ExprId {
        const def_ops = self.defOps();

        if ((try def_ops.compareTransparent(lhs, rhs)) != null) {
            return rhs;
        }
        if ((try def_ops.compareTransparent(rhs, lhs)) != null) {
            return lhs;
        }
        return null;
    }

    fn buildSemanticDefCommonTarget(
        self: *Context,
        lhs: ExprId,
        rhs: ExprId,
    ) anyerror!?ExprId {
        if (try self.buildSemanticCommonTargetFromDef(lhs, rhs)) |target| {
            return target;
        }
        return try self.buildSemanticCommonTargetFromDef(rhs, lhs);
    }

    fn buildSemanticCommonTargetFromDef(
        self: *Context,
        def_expr: ExprId,
        other_expr: ExprId,
    ) anyerror!?ExprId {
        const def_ops = self.defOps();

        const witness = try def_ops.instantiateDefTowardExpr(
            def_expr,
            other_expr,
        ) orelse return null;
        if (witness == other_expr) return other_expr;
        return try self.buildCommonTarget(witness, other_expr);
    }

    fn buildNonAcuiCommonTarget(
        self: *Context,
        lhs: ExprId,
        rhs: ExprId,
    ) anyerror!?ExprId {
        const lhs_node = self.theorem.interner.node(lhs);
        const rhs_node = self.theorem.interner.node(rhs);
        const lhs_app = switch (lhs_node.*) {
            .app => |value| value,
            .variable => return null,
            .placeholder => return null,
        };
        const rhs_app = switch (rhs_node.*) {
            .app => |value| value,
            .variable => return null,
            .placeholder => return null,
        };
        if (lhs_app.term_id != rhs_app.term_id or
            lhs_app.args.len != rhs_app.args.len)
        {
            return null;
        }

        const target_args = try self.allocator.alloc(ExprId, lhs_app.args.len);
        defer self.allocator.free(target_args);

        var any_changed = false;
        for (lhs_app.args, rhs_app.args, 0..) |lhs_arg, rhs_arg, idx| {
            if (lhs_arg == rhs_arg) {
                target_args[idx] = lhs_arg;
                continue;
            }
            const child = try self.buildCommonTarget(lhs_arg, rhs_arg) orelse {
                return null;
            };
            target_args[idx] = child;
            any_changed = true;
        }
        if (!any_changed) return null;

        return try self.theorem.interner.internApp(lhs_app.term_id, target_args);
    }

    fn buildAcuiCommonTarget(
        self: *Context,
        lhs: ExprId,
        rhs: ExprId,
    ) anyerror!?ExprId {
        const acui = try self.sharedStructuralCombiner(lhs, rhs) orelse return null;

        var lhs_leaves = std.ArrayListUnmanaged(LeafInfo){};
        defer lhs_leaves.deinit(self.allocator);
        var rhs_leaves = std.ArrayListUnmanaged(LeafInfo){};
        defer rhs_leaves.deinit(self.allocator);
        try self.collectLeafInfos(lhs, acui.head_term_id, &lhs_leaves);
        try self.collectLeafInfos(rhs, acui.head_term_id, &rhs_leaves);

        const lhs_state = try self.initLeafState(lhs_leaves.items);
        defer self.allocator.free(lhs_state);
        const rhs_state = try self.initLeafState(rhs_leaves.items);
        defer self.allocator.free(rhs_state);

        const lhs_exact = try self.allocator.alloc(bool, lhs_state.len);
        defer self.allocator.free(lhs_exact);
        const rhs_exact = try self.allocator.alloc(bool, rhs_state.len);
        defer self.allocator.free(rhs_exact);
        const lhs_claimed = try self.allocator.alloc(bool, lhs_state.len);
        defer self.allocator.free(lhs_claimed);
        const rhs_claimed = try self.allocator.alloc(bool, rhs_state.len);
        defer self.allocator.free(rhs_claimed);
        @memset(lhs_exact, false);
        @memset(rhs_exact, false);
        @memset(lhs_claimed, false);
        @memset(rhs_claimed, false);

        var common_items = std.ArrayListUnmanaged(ExprId){};
        defer common_items.deinit(self.allocator);
        try self.cancelExactItems(
            lhs_state,
            rhs_state,
            lhs_exact,
            rhs_exact,
            &common_items,
        );
        try self.pairCommonLeaves(
            lhs_state,
            rhs_state,
            lhs_exact,
            rhs_exact,
            &common_items,
        );
        try self.claimOppositeConcreteLeaves(
            lhs_state,
            lhs_exact,
            lhs_claimed,
            rhs_state,
            rhs_exact,
            acui,
        );
        try self.claimOppositeConcreteLeaves(
            rhs_state,
            rhs_exact,
            rhs_claimed,
            lhs_state,
            lhs_exact,
            acui,
        );

        var target_items = std.ArrayListUnmanaged(ExprId){};
        defer target_items.deinit(self.allocator);
        try target_items.appendSlice(self.allocator, common_items.items);

        for (lhs_state, 0..) |leaf, idx| {
            if (lhs_exact[idx]) continue;
            if (leaf.is_def) {
                if (!lhs_claimed[idx]) return null;
                try target_items.append(self.allocator, leaf.old_expr);
                continue;
            }
            if (leaf.new_expr == leaf.old_expr) return null;
        }
        for (rhs_state, 0..) |leaf, idx| {
            if (rhs_exact[idx]) continue;
            if (leaf.is_def) {
                if (!rhs_claimed[idx]) return null;
                try target_items.append(self.allocator, leaf.old_expr);
                continue;
            }
            if (leaf.new_expr == leaf.old_expr) return null;
        }

        return try self.buildCanonicalAcuiFromItems(target_items.items, acui);
    }

    fn initLeafState(
        self: *Context,
        leaves: []const LeafInfo,
    ) anyerror![]LeafState {
        const out = try self.allocator.alloc(LeafState, leaves.len);
        for (leaves, 0..) |leaf, idx| {
            out[idx] = .{
                .old_expr = leaf.expr_id,
                .new_expr = leaf.expr_id,
                .is_def = leaf.is_def,
            };
        }
        return out;
    }

    fn cancelExactItems(
        self: *Context,
        lhs: []const LeafState,
        rhs: []const LeafState,
        lhs_exact: []bool,
        rhs_exact: []bool,
        common_items: *std.ArrayListUnmanaged(ExprId),
    ) anyerror!void {
        var lhs_idx: usize = 0;
        var rhs_idx: usize = 0;
        while (lhs_idx < lhs.len and rhs_idx < rhs.len) {
            switch (compareExprIds(
                self.theorem,
                lhs[lhs_idx].old_expr,
                rhs[rhs_idx].old_expr,
            )) {
                .lt => lhs_idx += 1,
                .gt => rhs_idx += 1,
                .eq => {
                    lhs_exact[lhs_idx] = true;
                    rhs_exact[rhs_idx] = true;
                    try common_items.append(
                        self.allocator,
                        lhs[lhs_idx].old_expr,
                    );
                    lhs_idx += 1;
                    rhs_idx += 1;
                },
            }
        }
    }

    fn pairCommonLeaves(
        self: *Context,
        lhs: []LeafState,
        rhs: []LeafState,
        lhs_exact: []bool,
        rhs_exact: []bool,
        common_items: *std.ArrayListUnmanaged(ExprId),
    ) anyerror!void {
        for (lhs, 0..) |*lhs_leaf, lhs_idx| {
            if (lhs_exact[lhs_idx]) continue;
            for (rhs, 0..) |*rhs_leaf, rhs_idx| {
                if (rhs_exact[rhs_idx]) continue;
                const common = try self.buildNonAcuiCommonTarget(
                    lhs_leaf.old_expr,
                    rhs_leaf.old_expr,
                ) orelse continue;
                lhs_exact[lhs_idx] = true;
                rhs_exact[rhs_idx] = true;
                lhs_leaf.new_expr = common;
                rhs_leaf.new_expr = common;
                try common_items.append(self.allocator, common);
                break;
            }
        }
    }

    fn claimOppositeConcreteLeaves(
        self: *Context,
        owners: []LeafState,
        owner_exact: []const bool,
        owner_claimed: []bool,
        concretes: []LeafState,
        concrete_exact: []const bool,
        acui: ResolvedStructuralCombiner,
    ) anyerror!void {
        for (owners, 0..) |owner, owner_idx| {
            if (owner_exact[owner_idx] or !owner.is_def) continue;
            for (concretes, 0..) |*concrete, concrete_idx| {
                if (concrete_exact[concrete_idx] or concrete.is_def) continue;
                if (concrete.new_expr != concrete.old_expr) continue;
                if (!try self.defCoversConcrete(
                    owner.old_expr,
                    concrete.old_expr,
                    acui,
                )) {
                    continue;
                }
                concrete.new_expr = owner.old_expr;
                owner_claimed[owner_idx] = true;
            }
        }
    }

    fn defCoversConcrete(
        self: *Context,
        def_expr: ExprId,
        concrete_expr: ExprId,
        acui: ResolvedStructuralCombiner,
    ) anyerror!bool {
        if ((try self.buildNonAcuiCommonTarget(def_expr, concrete_expr)) !=
            null)
        {
            return true;
        }

        const def_ops = self.defOps();

        const witness = try def_ops.instantiateDefTowardAcuiItem(
            def_expr,
            concrete_expr,
            acui.head_term_id,
        ) orelse return false;
        if (!self.isAcuiExpr(witness, acui.head_term_id)) return false;
        return try self.canonicalizeAcuiExact(witness, acui) == concrete_expr;
    }

    fn appendSetItem(
        self: *Context,
        out: *std.ArrayListUnmanaged(ExprId),
        expr_id: ExprId,
    ) anyerror!void {
        if (out.items.len == 0) {
            try out.append(self.allocator, expr_id);
            return;
        }

        switch (compareExprIds(
            self.theorem,
            out.items[out.items.len - 1],
            expr_id,
        )) {
            .lt => {
                try out.append(self.allocator, expr_id);
                return;
            },
            .eq => return,
            .gt => {},
        }

        var insert_at: usize = 0;
        while (insert_at < out.items.len) : (insert_at += 1) {
            switch (compareExprIds(
                self.theorem,
                out.items[insert_at],
                expr_id,
            )) {
                .lt => continue,
                .eq => return,
                .gt => break,
            }
        }

        try out.insert(self.allocator, insert_at, expr_id);
    }

    fn isAcuiExpr(
        self: *Context,
        expr_id: ExprId,
        head_term_id: u32,
    ) bool {
        const node = self.theorem.interner.node(expr_id);
        return switch (node.*) {
            .app => |app| app.term_id == head_term_id and app.args.len == 2,
            .variable => false,
            .placeholder => false,
        };
    }

    fn canonicalizeAcuiExact(
        self: *Context,
        expr_id: ExprId,
        acui: ResolvedStructuralCombiner,
    ) anyerror!ExprId {
        const node = self.theorem.interner.node(expr_id);
        const app = switch (node.*) {
            .app => |value| value,
            else => return expr_id,
        };
        if (app.term_id != acui.head_term_id or app.args.len != 2) {
            return expr_id;
        }
        return try self.mergeCanonicalExact(app.args[0], app.args[1], acui);
    }

    fn mergeCanonicalExact(
        self: *Context,
        left: ExprId,
        right: ExprId,
        acui: ResolvedStructuralCombiner,
    ) anyerror!ExprId {
        if (left == try self.unitExpr(acui) and acui.supportsLeftUnit()) {
            return right;
        }

        const left_node = self.theorem.interner.node(left);
        return switch (left_node.*) {
            .app => |left_app| if (left_app.term_id == acui.head_term_id and
                left_app.args.len == 2)
            blk: {
                const merged_tail = try self.mergeCanonicalExact(
                    left_app.args[1],
                    right,
                    acui,
                );
                break :blk try self.insertItemExact(
                    left_app.args[0],
                    merged_tail,
                    acui,
                );
            } else try self.insertItemExact(left, right, acui),
            .variable => try self.insertItemExact(left, right, acui),
            .placeholder => try self.insertItemExact(left, right, acui),
        };
    }

    fn insertItemExact(
        self: *Context,
        item: ExprId,
        canon: ExprId,
        acui: ResolvedStructuralCombiner,
    ) anyerror!ExprId {
        const unit_expr = try self.unitExpr(acui);
        if (item == unit_expr and acui.supportsLeftUnit()) return canon;
        if (canon == unit_expr and acui.supportsRightUnit()) return item;

        const canon_node = self.theorem.interner.node(canon);
        return switch (canon_node.*) {
            .variable => blk: {
                const cmp = compareExprIds(self.theorem, item, canon);
                if (cmp == .gt and acui.comm_id != null) {
                    break :blk try self.theorem.interner.internApp(
                        acui.head_term_id,
                        &[_]ExprId{ canon, item },
                    );
                }
                if (cmp == .eq and acui.idem_id != null) break :blk canon;
                break :blk try self.theorem.interner.internApp(
                    acui.head_term_id,
                    &[_]ExprId{ item, canon },
                );
            },
            .placeholder => blk: {
                const cmp = compareExprIds(self.theorem, item, canon);
                if (cmp == .gt and acui.comm_id != null) {
                    break :blk try self.theorem.interner.internApp(
                        acui.head_term_id,
                        &[_]ExprId{ canon, item },
                    );
                }
                if (cmp == .eq and acui.idem_id != null) break :blk canon;
                break :blk try self.theorem.interner.internApp(
                    acui.head_term_id,
                    &[_]ExprId{ item, canon },
                );
            },
            .app => |canon_app| blk: {
                if (canon_app.term_id != acui.head_term_id or
                    canon_app.args.len != 2)
                {
                    const cmp = compareExprIds(self.theorem, item, canon);
                    if (cmp == .gt and acui.comm_id != null) {
                        break :blk try self.theorem.interner.internApp(
                            acui.head_term_id,
                            &[_]ExprId{ canon, item },
                        );
                    }
                    if (cmp == .eq and acui.idem_id != null) {
                        break :blk canon;
                    }
                    break :blk try self.theorem.interner.internApp(
                        acui.head_term_id,
                        &[_]ExprId{ item, canon },
                    );
                }

                const head = canon_app.args[0];
                const rest = canon_app.args[1];
                const cmp = compareExprIds(self.theorem, item, head);
                if (cmp == .eq and acui.idem_id != null) break :blk canon;
                if (cmp != .gt or acui.comm_id == null) {
                    break :blk try self.theorem.interner.internApp(
                        acui.head_term_id,
                        &[_]ExprId{ item, canon },
                    );
                }
                const inserted = try self.insertItemExact(item, rest, acui);
                break :blk try self.theorem.interner.internApp(
                    acui.head_term_id,
                    &[_]ExprId{ head, inserted },
                );
            },
        };
    }

    fn unitExpr(
        self: *Context,
        acui: ResolvedStructuralCombiner,
    ) anyerror!ExprId {
        return try self.theorem.interner.internApp(acui.unit_term_id, &.{});
    }
};

pub fn compareExprIds(
    theorem: *const TheoremContext,
    lhs: ExprId,
    rhs: ExprId,
) std.math.Order {
    if (lhs == rhs) return .eq;
    const lhs_node = theorem.interner.node(lhs);
    const rhs_node = theorem.interner.node(rhs);
    return switch (lhs_node.*) {
        .variable => |lhs_var| switch (rhs_node.*) {
            .variable => |rhs_var| compareVarIds(lhs_var, rhs_var),
            .placeholder => .lt,
            .app => .lt,
        },
        .placeholder => |lhs_id| switch (rhs_node.*) {
            .variable => .gt,
            .placeholder => |rhs_id| std.math.order(lhs_id, rhs_id),
            .app => .lt,
        },
        .app => |lhs_app| switch (rhs_node.*) {
            .variable => .gt,
            .placeholder => .gt,
            .app => |rhs_app| blk: {
                const term_cmp = std.math.order(lhs_app.term_id, rhs_app.term_id);
                if (term_cmp != .eq) break :blk term_cmp;
                const len_cmp = std.math.order(lhs_app.args.len, rhs_app.args.len);
                if (len_cmp != .eq) break :blk len_cmp;
                for (lhs_app.args, rhs_app.args) |l_arg, r_arg| {
                    const cmp = compareExprIds(theorem, l_arg, r_arg);
                    if (cmp != .eq) break :blk cmp;
                }
                break :blk .eq;
            },
        },
    };
}

fn compareVarIds(lhs: anytype, rhs: @TypeOf(lhs)) std.math.Order {
    return switch (lhs) {
        .theorem_var => |lhs_id| switch (rhs) {
            .theorem_var => |rhs_id| std.math.order(lhs_id, rhs_id),
            .dummy_var => .lt,
        },
        .dummy_var => |lhs_id| switch (rhs) {
            .theorem_var => .gt,
            .dummy_var => |rhs_id| std.math.order(lhs_id, rhs_id),
        },
    };
}
