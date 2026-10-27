//! Ground terms for the search core: canonical bags, matching a rule
//! conclusion against a goal, and building a rule's premises.
//!
//! Every expression the core works on is canonical: each commutative
//! `@acui` bag lists its members once per occurrence its law counts, in
//! `ExprId` order, so two goals equal modulo ACUI are the same `ExprId`
//! and binder agreement is an id comparison. The order is only stable
//! within one theorem's interner, which is all one core run uses.
//!
//! Matching enumerates every way a conclusion template fits a goal. A bag
//! member of the template takes a distinct goal member; each choice is an
//! alternative. The bag's rest binder takes what is left over, which is
//! the minimal complement: a set law would also allow the rest to keep a
//! member the template already claims, which this stage does not try.

const std = @import("std");
const ExprId = @import("../../../expr.zig").ExprId;
const TheoremContext = @import("../../../expr.zig").TheoremContext;
const TemplateExpr = @import("../../../rules.zig").TemplateExpr;
const RuleDecl = @import("../../../env.zig").RuleDecl;
const AcuiBag = @import("../../../acui_bag.zig");
const Context = @import("../types.zig").Context;
const catalog = @import("./catalog.zig");

pub const Error = error{
    OutOfMemory,
    TooManyTheoremExprs,
    /// The term is outside what the core reads: a bag past
    /// `AcuiBag.capacity`, or an application wider than `catalog.max_args`.
    Unsupported,
};

pub const Terms = struct {
    allocator: std.mem.Allocator,
    context: *const Context,
    theorem: *TheoremContext,
    /// The commutative bag combiner each combiner head and each unit term
    /// reads as.
    bags: std.AutoHashMapUnmanaged(u32, AcuiBag.Combiner) = .empty,
    canonical_memo: std.AutoHashMapUnmanaged(ExprId, ExprId) = .empty,

    pub fn init(
        allocator: std.mem.Allocator,
        context: *const Context,
        theorem: *TheoremContext,
    ) Error!Terms {
        var self = Terms{ .allocator = allocator, .context = context, .theorem = theorem };
        errdefer self.deinit();
        var it = context.registry.acui_by_head.keyIterator();
        while (it.next()) |head| {
            const combiner = AcuiBag.Combiner.of(context.registry, context.env, head.*) orelse continue;
            if (!combiner.law.isCommutative()) continue;
            try self.bags.put(allocator, combiner.head, combiner);
            if (combiner.unit) |unit| try self.bags.put(allocator, unit, combiner);
        }
        return self;
    }

    pub fn deinit(self: *Terms) void {
        self.bags.deinit(self.allocator);
        self.canonical_memo.deinit(self.allocator);
        self.* = undefined;
    }

    /// The commutative bag combiner that reads `term_id`: the combiner
    /// itself or its unit. A non-commutative combiner reads as an
    /// ordinary term; `supported` keeps such goals out.
    fn bagFor(self: *const Terms, term_id: u32) ?AcuiBag.Combiner {
        return self.bags.get(term_id);
    }

    /// Whether the core can search `expr`: no placeholders, definitions or
    /// non-commutative combiners. O(size of `expr`) over shared nodes.
    pub fn supported(self: *Terms, expr: ExprId) Error!bool {
        var seen = std.AutoHashMapUnmanaged(ExprId, void).empty;
        defer seen.deinit(self.allocator);
        return self.supportedWalk(expr, &seen);
    }

    fn supportedWalk(
        self: *Terms,
        expr: ExprId,
        seen: *std.AutoHashMapUnmanaged(ExprId, void),
    ) Error!bool {
        if ((try seen.getOrPut(self.allocator, expr)).found_existing) return true;
        switch (self.theorem.interner.node(expr).*) {
            .variable => return true,
            .placeholder => return false,
            .app => |app| {
                if (app.term_id >= self.context.env.terms.items.len) return false;
                if (self.context.env.terms.items[app.term_id].is_def) return false;
                if (AcuiBag.Combiner.of(self.context.registry, self.context.env, app.term_id)) |combiner| {
                    if (!combiner.law.isCommutative()) return false;
                }
                for (app.args) |arg| {
                    if (!try self.supportedWalk(arg, seen)) return false;
                }
                return true;
            },
        }
    }

    /// `expr` with every bag in canonical form.
    pub fn canonical(self: *Terms, expr: ExprId) Error!ExprId {
        if (self.canonical_memo.get(expr)) |done| return done;
        const result: ExprId = switch (self.theorem.interner.node(expr).*) {
            .variable, .placeholder => expr,
            .app => |app| blk: {
                if (self.bagFor(app.term_id)) |combiner| {
                    const members = combiner.flatten(self.theorem, expr) orelse return error.Unsupported;
                    var out: AcuiBag.ExprBag = .{};
                    for (members.slice()) |member| {
                        if (!out.append(try self.canonical(member))) return error.Unsupported;
                    }
                    break :blk try self.buildBag(combiner, &out);
                }
                if (app.args.len > catalog.max_args) return error.Unsupported;
                var args: [catalog.max_args]ExprId = undefined;
                for (app.args, 0..) |arg, idx| args[idx] = try self.canonical(arg);
                break :blk try self.theorem.interner.internApp(app.term_id, args[0..app.args.len]);
            },
        };
        try self.canonical_memo.put(self.allocator, expr, result);
        return result;
    }

    /// The canonical bag of `members`, each already canonical: sorted, and
    /// deduplicated under a set law.
    fn buildBag(self: *Terms, combiner: AcuiBag.Combiner, members: *AcuiBag.ExprBag) Error!ExprId {
        const items = members.items[0..members.len];
        std.mem.sort(ExprId, items, {}, std.sort.asc(ExprId));
        const kept = if (combiner.law.isIdempotent()) AcuiBag.mergeRepeats(items) else items;
        return (try combiner.build(self.theorem, kept)) orelse error.Unsupported;
    }

    /// `template` with `bindings` substituted, canonical when every binding
    /// is.
    pub fn instantiate(
        self: *Terms,
        template: TemplateExpr,
        bindings: []const ExprId,
    ) Error!ExprId {
        switch (template) {
            .binder => |idx| return bindings[idx],
            .app => |app| {
                if (self.bagFor(app.term_id)) |combiner| {
                    const parts = combiner.flattenTemplate(template) orelse return error.Unsupported;
                    var out: AcuiBag.ExprBag = .{};
                    for (parts.slice()) |part| {
                        const value = try self.instantiate(part, bindings);
                        const members = combiner.flatten(self.theorem, value) orelse return error.Unsupported;
                        for (members.slice()) |member| {
                            if (!out.append(member)) return error.Unsupported;
                        }
                    }
                    return self.buildBag(combiner, &out);
                }
                var args: [catalog.max_args]ExprId = undefined;
                for (app.args, 0..) |arg, idx| args[idx] = try self.instantiate(arg, bindings);
                return self.theorem.interner.internApp(app.term_id, args[0..app.args.len]);
            },
        }
    }

    /// Call `sink.match(bindings)` for every way `rule`'s conclusion fits
    /// the canonical `goal`, until it returns true. `bindings` has one
    /// entry per rule binder, all bound. Returns whether the sink stopped
    /// the enumeration.
    pub fn matchConclusion(
        self: *Terms,
        rule: *const RuleDecl,
        goal: ExprId,
        comptime Sink: type,
        sink: *Sink,
    ) (Error || Sink.Error)!bool {
        var bindings: [64]?ExprId = @splat(null);
        var matcher = Matcher(Sink){
            .terms = self,
            .rule = rule,
            .bindings = bindings[0..rule.args.len],
            .sink = sink,
        };
        try matcher.term(rule.concl, goal, null);
        return matcher.stop;
    }
};

/// What is left to match after the current step, as a stack-allocated
/// list: template/goal pairs, and the next member of a bag in progress.
const Pending = struct {
    step: union(enum) {
        pair: struct { template: TemplateExpr, expr: ExprId },
        bag: *const BagState,
    },
    next: ?*const Pending,
};

/// A bag being matched member by member: template members in match order,
/// the goal's members, which of those are taken, and the rest binder.
const BagState = struct {
    combiner: AcuiBag.Combiner,
    template: []const TemplateExpr,
    goal: []const ExprId,
    used: u64 = 0,
    index: usize = 0,
    rest: ?usize = null,
};

fn Matcher(comptime Sink: type) type {
    return struct {
        terms: *Terms,
        rule: *const RuleDecl,
        bindings: []?ExprId,
        sink: *Sink,
        stop: bool = false,

        const Self = @This();
        const MatchError = Error || Sink.Error;

        fn run(self: *Self, pending: ?*const Pending) MatchError!void {
            const node = pending orelse {
                var out: [64]ExprId = undefined;
                for (self.bindings, 0..) |binding, idx| out[idx] = binding.?;
                if (try self.sink.match(out[0..self.bindings.len])) self.stop = true;
                return;
            };
            switch (node.step) {
                .pair => |pair| try self.term(pair.template, pair.expr, node.next),
                .bag => |state| try self.bag(state.*, node.next),
            }
        }

        fn term(self: *Self, template: TemplateExpr, expr: ExprId, next: ?*const Pending) MatchError!void {
            switch (template) {
                .binder => |idx| try self.bind(idx, expr, next),
                .app => |app| {
                    if (self.terms.bagFor(app.term_id)) |combiner| {
                        return self.startBag(combiner, template, expr, next);
                    }
                    const goal_app = switch (self.terms.theorem.interner.node(expr).*) {
                        .app => |goal_app| goal_app,
                        else => return,
                    };
                    if (goal_app.term_id != app.term_id or goal_app.args.len != app.args.len) return;
                    // Bags go last, so the rigid arguments bind what they can
                    // before a bag enumerates its members.
                    var cells: [catalog.max_args]Pending = undefined;
                    var head: ?*const Pending = next;
                    var count: usize = 0;
                    for (0..2) |pass| {
                        var idx = app.args.len;
                        while (idx > 0) {
                            idx -= 1;
                            if ((pass == 0) != self.isBagTemplate(app.args[idx])) continue;
                            cells[count] = .{
                                .step = .{ .pair = .{ .template = app.args[idx], .expr = goal_app.args[idx] } },
                                .next = head,
                            };
                            head = &cells[count];
                            count += 1;
                        }
                    }
                    try self.run(head);
                },
            }
        }

        fn isBagTemplate(self: *const Self, template: TemplateExpr) bool {
            return switch (template) {
                .binder => false,
                .app => |app| self.terms.bagFor(app.term_id) != null,
            };
        }

        fn bind(self: *Self, idx: usize, expr: ExprId, next: ?*const Pending) MatchError!void {
            if (self.bindings[idx]) |value| {
                if (value == expr) try self.run(next);
                return;
            }
            self.bindings[idx] = expr;
            defer self.bindings[idx] = null;
            try self.run(next);
        }

        fn isRestBinder(self: *const Self, combiner: AcuiBag.Combiner, template: TemplateExpr) bool {
            const idx = switch (template) {
                .binder => |idx| idx,
                .app => return false,
            };
            const bag_sort = self.terms.context.env.terms.items[combiner.head].ret_sort_name;
            return std.mem.eql(u8, self.rule.args[idx].sort_name, bag_sort);
        }

        fn startBag(
            self: *Self,
            combiner: AcuiBag.Combiner,
            template: TemplateExpr,
            expr: ExprId,
            next: ?*const Pending,
        ) MatchError!void {
            const parts = combiner.flattenTemplate(template) orelse return error.Unsupported;
            const members = combiner.flatten(self.terms.theorem, expr) orelse return error.Unsupported;
            // Bound rest binders and structured members first, the unbound
            // rest binder last: it takes what the others leave.
            var ordered: AcuiBag.TemplateBag = .{};
            var rest: ?usize = null;
            for (parts.slice()) |part| {
                if (self.isRestBinder(combiner, part) and self.bindings[part.binder] == null) {
                    rest = part.binder;
                } else {
                    _ = ordered.append(part);
                }
            }
            const state = BagState{
                .combiner = combiner,
                .template = ordered.slice(),
                .goal = members.slice(),
                .rest = rest,
            };
            try self.bag(state, next);
        }

        fn bag(self: *Self, state: BagState, next: ?*const Pending) MatchError!void {
            if (state.index == state.template.len) return self.finishBag(state, next);
            const part = state.template[state.index];
            if (self.isRestBinder(state.combiner, part)) {
                // A rest binder an earlier match bound: its members must be
                // among the goal's.
                const value = self.bindings[part.binder].?;
                const members = state.combiner.flatten(self.terms.theorem, value) orelse return error.Unsupported;
                var after = state;
                after.index += 1;
                for (members.slice()) |member| {
                    after.used |= takeMember(state.combiner, state.goal, after.used, member) orelse return;
                }
                return self.bag(after, next);
            }
            for (state.goal, 0..) |member, at| {
                const bit = @as(u64, 1) << @intCast(at);
                if (state.used & bit != 0) continue;
                var after = state;
                after.used |= bit;
                after.index += 1;
                const cell = Pending{ .step = .{ .bag = &after }, .next = next };
                try self.term(part, member, &cell);
                if (self.stop) return;
            }
        }

        /// The bit of a goal member equal to `member` that `used` leaves
        /// free, or under an idempotent law one already taken; null when
        /// there is none.
        fn takeMember(combiner: AcuiBag.Combiner, goal: []const ExprId, used: u64, member: ExprId) ?u64 {
            var taken: ?u64 = null;
            for (goal, 0..) |candidate, at| {
                if (candidate != member) continue;
                const bit = @as(u64, 1) << @intCast(at);
                if (used & bit == 0) return bit;
                taken = bit;
            }
            return if (combiner.law.isIdempotent()) taken else null;
        }

        fn finishBag(self: *Self, state: BagState, next: ?*const Pending) MatchError!void {
            var left: AcuiBag.ExprBag = .{};
            for (state.goal, 0..) |member, at| {
                if (state.used & (@as(u64, 1) << @intCast(at)) == 0) _ = left.append(member);
            }
            const rest = state.rest orelse {
                if (left.len == 0) try self.run(next);
                return;
            };
            // The goal's members are canonical and in order, so the
            // leftover is canonical as it stands.
            const value = (try state.combiner.build(self.terms.theorem, left.slice())) orelse return;
            try self.bind(rest, value, next);
        }
    };
}
