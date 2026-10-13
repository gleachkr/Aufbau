const std = @import("std");
const ArenaAllocator = @import("./arena_allocator.zig").ArenaAllocator;
const ExprId = @import("./expr.zig").ExprId;
const ExprNode = @import("./expr.zig").ExprNode;
const TheoremContext = @import("./expr.zig").TheoremContext;
const GlobalEnv = @import("./env.zig").GlobalEnv;
const RewriteRegistry = @import("./rewrite_registry.zig").RewriteRegistry;
const ResolvedStructuralCombiner =
    @import("./rewrite_registry.zig").ResolvedStructuralCombiner;
const DefOps = @import("./def_ops.zig");
const AcuiBag = @import("./acui_bag.zig");

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
    /// The two sides' sorted members, reused by every `sameMembers`.
    member_scratch: [2]std.ArrayListUnmanaged(ExprId) = .{ .empty, .empty },

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
        for (&self.member_scratch) |*list| list.deinit(self.allocator);
    }

    pub fn defOps(self: *Context) *DefOps.Context {
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

    /// Whether `lhs` and `rhs` differ only in how the members of their
    /// commutative bags are ordered, grouped and, when the bag is
    /// idempotent, repeated: the same expression outside the bags, and bags
    /// holding the same members. A bag with the unit among its members
    /// does not count.
    pub fn isRearrangement(
        self: *Context,
        lhs: ExprId,
        rhs: ExprId,
    ) anyerror!bool {
        if (lhs == rhs) return true;
        const lhs_app = switch (self.theorem.interner.node(lhs).*) {
            .app => |app| app,
            .variable, .placeholder => return false,
        };
        const rhs_app = switch (self.theorem.interner.node(rhs).*) {
            .app => |app| app,
            .variable, .placeholder => return false,
        };
        if (lhs_app.term_id != rhs_app.term_id or
            lhs_app.args.len != rhs_app.args.len)
        {
            return false;
        }
        if (lhs_app.args.len == 2) {
            if (try self.resolveCombinerForTerm(lhs_app.term_id)) |acui| {
                if (acui.comm_id == null) return false;
                const unit = try self.unitExpr(acui);
                if (self.holdsMember(lhs, unit, acui.head_term_id) or
                    self.holdsMember(rhs, unit, acui.head_term_id))
                {
                    return false;
                }
                return try self.sameMembers(lhs, rhs, acui);
            }
        }
        for (lhs_app.args, rhs_app.args) |lhs_arg, rhs_arg| {
            if (!try self.isRearrangement(lhs_arg, rhs_arg)) return false;
        }
        return true;
    }

    /// Whether two bags of `acui` hold the same members: as a multiset, or
    /// as a set when the bag is idempotent.
    pub fn sameMembers(
        self: *Context,
        lhs: ExprId,
        rhs: ExprId,
        acui: ResolvedStructuralCombiner,
    ) anyerror!bool {
        if (lhs == rhs) return true;
        const lhs_members = try self.sortedMembers(lhs, acui, 0);
        const rhs_members = try self.sortedMembers(rhs, acui, 1);
        return std.mem.eql(ExprId, lhs_members, rhs_members);
    }

    fn sortedMembers(
        self: *Context,
        bag: ExprId,
        acui: ResolvedStructuralCombiner,
        scratch_idx: usize,
    ) anyerror![]const ExprId {
        const out = &self.member_scratch[scratch_idx];
        out.clearRetainingCapacity();
        try self.collectLeaves(bag, acui.head_term_id, out);
        std.mem.sortUnstable(ExprId, out.items, {}, std.sort.asc(ExprId));
        if (acui.idem_id == null) return out.items;
        var len: usize = 0;
        for (out.items) |member| {
            if (len != 0 and out.items[len - 1] == member) continue;
            out.items[len] = member;
            len += 1;
        }
        return out.items[0..len];
    }

    /// Whether the `head_term_id` spine at `bag` has `member` as a leaf.
    pub fn holdsMember(
        self: *const Context,
        bag: ExprId,
        member: ExprId,
        head_term_id: u32,
    ) bool {
        if (bag == member) return true;
        switch (self.theorem.interner.node(bag).*) {
            .app => |app| if (app.term_id == head_term_id and
                app.args.len == 2)
            {
                return self.holdsMember(app.args[0], member, head_term_id) or
                    self.holdsMember(app.args[1], member, head_term_id);
            },
            .variable, .placeholder => {},
        }
        return false;
    }

    /// Calls `visitor.leaf(leaf)` for each leaf of the `head_term_id` spine
    /// at `expr_id`, left to right.
    pub fn visitLeaves(
        self: *const Context,
        expr_id: ExprId,
        head_term_id: u32,
        visitor: anytype,
    ) void {
        switch (self.theorem.interner.node(expr_id).*) {
            .app => |app| {
                if (app.term_id == head_term_id and app.args.len == 2) {
                    self.visitLeaves(app.args[0], head_term_id, visitor);
                    self.visitLeaves(app.args[1], head_term_id, visitor);
                    return;
                }
            },
            .variable => {},
            .placeholder => {},
        }
        visitor.leaf(expr_id);
    }

    /// How many leaves the `head_term_id` spine at `expr_id` has.
    pub fn countLeaves(
        self: *const Context,
        expr_id: ExprId,
        head_term_id: u32,
    ) usize {
        var counter: struct {
            count: usize = 0,
            pub fn leaf(c: *@This(), _: ExprId) void {
                c.count += 1;
            }
        } = .{};
        self.visitLeaves(expr_id, head_term_id, &counter);
        return counter.count;
    }

    /// Appends the leaves of the `head_term_id` spine at `expr_id`, left to
    /// right, growing `out` once.
    pub fn collectLeaves(
        self: *Context,
        expr_id: ExprId,
        head_term_id: u32,
        out: *std.ArrayListUnmanaged(ExprId),
    ) anyerror!void {
        try out.ensureTotalCapacityPrecise(
            self.allocator,
            out.items.len + self.countLeaves(expr_id, head_term_id),
        );
        const Appender = struct {
            out: *std.ArrayListUnmanaged(ExprId),
            pub fn leaf(a: @This(), leaf_id: ExprId) void {
                a.out.appendAssumeCapacity(leaf_id);
            }
        };
        self.visitLeaves(expr_id, head_term_id, Appender{ .out = out });
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

        var unique = std.ArrayListUnmanaged(ExprId).empty;
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
        return (try AcuiBag.Combiner.fromResolved(acui).build(self.theorem, unique.items)).?;
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

    pub fn canonicalizeAcuiExact(
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
        // Merging requires canonical operands, not merely a right-associated
        // tree. Callers can supply rebuilt leaves or raw def witnesses;
        // neither guarantees sorted, unit-free, deduplicated children.
        const left = try self.canonicalizeAcuiExact(app.args[0], acui);
        const right = try self.canonicalizeAcuiExact(app.args[1], acui);
        return try self.mergeCanonicalExact(left, right, acui);
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

test "ACUI canonicalization normalizes arbitrary trees and law subsets" {
    var arena = ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    var theorem = TheoremContext.init(allocator);
    defer theorem.deinit();
    var env = GlobalEnv.init(allocator);
    var registry = RewriteRegistry.init(allocator);
    var support = Context.init(allocator, &theorem, &env, &registry);
    defer support.deinit();

    const join = struct {
        fn make(t: *TheoremContext, a: ExprId, b: ExprId) !ExprId {
            return t.interner.internApp(0, &.{ a, b });
        }
    }.make;
    const unit = try theorem.interner.internApp(1, &.{});
    const a = try theorem.interner.internApp(2, &.{});
    const b = try theorem.interner.internApp(3, &.{});
    const c = try theorem.interner.internApp(4, &.{});
    const atoms = [_]ExprId{ a, b, c, unit };

    // Exhaust all four-leaf words and all five binary tree shapes. The
    // independent flat oracle applies only the declared laws: ACUI sorts
    // and deduplicates, ACU sorts, and AU preserves order and multiplicity.
    for (0..3) |mode| {
        const acui: ResolvedStructuralCombiner = .{
            .head_term_id = 0,
            .unit_term_id = 1,
            .assoc_id = 0,
            .comm_id = if (mode < 2) 1 else null,
            .idem_id = if (mode == 0) 2 else null,
            .left_unit_rule_id = 3,
            .left_unit_rule_reversed = false,
            .right_unit_rule_id = 4,
            .right_unit_rule_reversed = false,
        };
        for (0..256) |word| {
            var leaves: [4]ExprId = undefined;
            var code = word;
            for (&leaves) |*leaf| {
                leaf.* = atoms[code % atoms.len];
                code /= atoms.len;
            }
            var expected_items: [4]ExprId = undefined;
            var len: usize = 0;
            if (acui.comm_id != null) {
                for (atoms[0..3]) |atom| {
                    for (leaves) |leaf| {
                        if (leaf != atom) continue;
                        expected_items[len] = atom;
                        len += 1;
                        if (acui.idem_id != null) break;
                    }
                }
            } else {
                for (leaves) |leaf| {
                    if (leaf == unit) continue;
                    expected_items[len] = leaf;
                    len += 1;
                }
            }
            const expected = (try AcuiBag.Combiner.fromResolved(acui).build(
                &theorem,
                expected_items[0..len],
            )).?;
            const w = leaves[0];
            const x = leaves[1];
            const y = leaves[2];
            const z = leaves[3];
            const wx = try join(&theorem, w, x);
            const xy = try join(&theorem, x, y);
            const yz = try join(&theorem, y, z);
            const trees = [_]ExprId{
                try join(&theorem, try join(&theorem, wx, y), z),
                try join(&theorem, try join(&theorem, w, xy), z),
                try join(&theorem, wx, yz),
                try join(&theorem, w, try join(&theorem, xy, z)),
                try join(&theorem, w, try join(&theorem, x, yz)),
            };
            for (trees) |tree| {
                try std.testing.expectEqual(
                    expected,
                    try support.canonicalizeAcuiExact(tree, acui),
                );
            }
            try std.testing.expectEqual(
                expected,
                try support.canonicalizeAcuiExact(expected, acui),
            );
        }
    }
}
