//! Terms for the search core: canonical bags, matching a rule conclusion
//! against a goal, and building a rule's premises.
//!
//! Every expression the core works on is canonical: each commutative
//! `@acui` bag lists its members once per occurrence its law counts, in
//! `ExprId` order, so two ground goals equal modulo ACUI are the same
//! `ExprId`. The order is only stable within one theorem's interner, which
//! is all one core run uses. A goal holding witness variables
//! (`wvars.zig`) is canonical as written, with each wvar a leaf; once a
//! binding changes it, `resolveGoal` makes it canonical again.
//!
//! Matching enumerates every way a conclusion template fits a goal, and
//! unifies through the witness variables: a binder met twice must agree
//! with its first value, and an unbound wvar on either side takes the other
//! side's term. Each unifier is an alternative, run in place by the sink
//! while its bindings hold. A bag member of the template takes a distinct
//! goal member; each choice is an alternative. The bag's rest binder takes
//! what is left over, which is the minimal complement: a set law would
//! also allow the rest to keep a member the template already claims, which
//! the core does not try yet. Two bags holding wvars unify member by
//! member (`pairBags`). An unbound wvar facing template structure does not
//! match: the witnesses of these stages stand for terms the theory's rules
//! never take apart.

const std = @import("std");
const ExprId = @import("../../../expr.zig").ExprId;
const TheoremContext = @import("../../../expr.zig").TheoremContext;
const TemplateExpr = @import("../../../rules.zig").TemplateExpr;
const RuleDecl = @import("../../../env.zig").RuleDecl;
const AcuiBag = @import("../../../acui_bag.zig");
const Context = @import("../types.zig").Context;
const catalog = @import("./catalog.zig");
const WVars = @import("./wvars.zig").WVars;

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
    wvars: *WVars,
    /// The commutative bag combiner each combiner head and each unit term
    /// reads as.
    bags: std.AutoHashMapUnmanaged(u32, AcuiBag.Combiner) = .empty,
    canonical_memo: std.AutoHashMapUnmanaged(ExprId, ExprId) = .empty,

    pub fn init(
        allocator: std.mem.Allocator,
        context: *const Context,
        theorem: *TheoremContext,
        wvars: *WVars,
    ) Error!Terms {
        var self = Terms{ .allocator = allocator, .context = context, .theorem = theorem, .wvars = wvars };
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
    pub fn bagFor(self: *const Terms, term_id: u32) ?AcuiBag.Combiner {
        return self.bags.get(term_id);
    }

    /// Whether the core can search `expr`: no placeholders or
    /// non-commutative combiners. A definition is an ordinary term here,
    /// never unfolded. O(size of `expr`) over shared nodes.
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

    /// `expr` with the current bindings applied, canonical.
    pub fn resolveGoal(self: *Terms, expr: ExprId) Error!ExprId {
        if (!try self.wvars.holdsWVar(expr)) return expr;
        return self.canonical(try self.wvars.deref(expr, null));
    }

    /// Whether `a` and `b` are equal under the current bindings.
    fn same(self: *Terms, a: ExprId, b: ExprId) Error!bool {
        if (a == b) return true;
        return try self.resolveGoal(a) == try self.resolveGoal(b);
    }

    /// `pattern` with each free occurrence of the variable `hole` replaced
    /// by `value`, canonical: the instance a quantifier rule's view states.
    /// An occurrence under a binder of `hole` belongs to that binder and
    /// stays.
    pub fn swap(self: *Terms, pattern: ExprId, hole: ExprId, value: ExprId) Error!ExprId {
        return self.canonical(try self.swapWalk(pattern, hole, value));
    }

    fn swapWalk(self: *Terms, expr: ExprId, hole: ExprId, value: ExprId) Error!ExprId {
        if (expr == hole) return value;
        const app = switch (self.theorem.interner.node(expr).*) {
            .app => |app| app,
            .variable, .placeholder => return expr,
        };
        if (app.args.len > catalog.max_args) return error.Unsupported;
        const decl = &self.context.env.terms.items[app.term_id];
        for (app.args, 0..) |arg, idx| {
            if (idx < decl.args.len and decl.args[idx].bound and arg == hole) return expr;
        }
        var args: [catalog.max_args]ExprId = undefined;
        var changed = false;
        for (app.args, 0..) |arg, idx| {
            args[idx] = try self.swapWalk(arg, hole, value);
            if (args[idx] != arg) changed = true;
        }
        if (!changed) return expr;
        return self.theorem.interner.internApp(app.term_id, args[0..app.args.len]);
    }

    /// Append the variables `expr` binds (those in a bound argument of some
    /// application) to `out`.
    pub fn boundVariables(
        self: *Terms,
        arena: std.mem.Allocator,
        expr: ExprId,
        out: *std.ArrayListUnmanaged(ExprId),
    ) Error!void {
        const app = switch (self.theorem.interner.node(expr).*) {
            .app => |app| app,
            .variable, .placeholder => return,
        };
        const decl = &self.context.env.terms.items[app.term_id];
        for (app.args, 0..) |arg, idx| {
            if (idx < decl.args.len and decl.args[idx].bound) {
                if (std.mem.indexOfScalar(ExprId, out.items, arg) == null) try out.append(arena, arg);
            } else {
                try self.boundVariables(arena, arg, out);
            }
        }
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
    /// entry per rule binder, null for those the conclusion does not fix;
    /// wvar bindings the match made hold during the call. Returns whether
    /// the sink stopped the enumeration.
    pub fn matchConclusion(
        self: *Terms,
        rule: *const RuleDecl,
        goal: ExprId,
        comptime Sink: type,
        sink: *Sink,
    ) (Error || Sink.Error)!bool {
        // On the heap: the match stays on the stack for the rest of the
        // proof.
        const bindings = try self.allocator.alloc(?ExprId, rule.args.len);
        defer self.allocator.free(bindings);
        @memset(bindings, null);
        var matcher = Matcher(Sink){ .terms = self, .rule = rule, .bindings = bindings, .sink = sink };
        try matcher.term(rule.concl, goal, null);
        return matcher.stop;
    }

    /// Call `sink.match(&.{})` for every unifier of `a` and `b`, until it
    /// returns true. Returns whether the sink stopped the enumeration.
    pub fn unify(
        self: *Terms,
        a: ExprId,
        b: ExprId,
        comptime Sink: type,
        sink: *Sink,
    ) (Error || Sink.Error)!bool {
        var matcher = Matcher(Sink){ .terms = self, .rule = null, .bindings = &.{}, .sink = sink };
        try matcher.unify(a, b, null);
        return matcher.stop;
    }
};

/// What is left to match after the current step, as a stack-allocated
/// list: the arguments of an application from position `at` on (template
/// against goal, or two terms unified), and the next member of a bag in
/// progress. One cell stands for all of an application's remaining
/// arguments, since a match stays on the stack until the proof is done.
const Pending = struct {
    step: union(enum) {
        /// Positions count over the rigid arguments, then the bags.
        args: struct { template: []const TemplateExpr, goal: []const ExprId, at: usize },
        unify: struct { a: []const ExprId, b: []const ExprId, at: usize },
        bag: *const BagState,
        pairing: *const BagPairing,
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

/// Two bags being unified member by member: each of `a`'s members against
/// one of `b`'s, distinct ones unless the law is idempotent, and then,
/// under an idempotent law, each of `b`'s members none was paired with
/// against one of `a`'s. `index` counts over `a`, then over `b`.
const BagPairing = struct {
    idempotent: bool,
    a: []const ExprId,
    b: []const ExprId,
    paired: u64 = 0,
    index: usize = 0,
};

fn Matcher(comptime Sink: type) type {
    return struct {
        terms: *Terms,
        /// The rule whose conclusion is matched; null when only unifying.
        rule: ?*const RuleDecl,
        bindings: []?ExprId,
        sink: *Sink,
        stop: bool = false,

        const Self = @This();
        const MatchError = Error || Sink.Error;

        fn run(self: *Self, pending: ?*const Pending) MatchError!void {
            const node = pending orelse {
                if (try self.sink.match(self.bindings)) self.stop = true;
                return;
            };
            switch (node.step) {
                .args => |args| {
                    // Bags go last, so the rigid arguments bind what they
                    // can before a bag enumerates its members.
                    const len = args.template.len;
                    var at = args.at;
                    while (at < 2 * len) : (at += 1) {
                        if ((at >= len) == self.isBagTemplate(args.template[at % len])) break;
                    } else return self.run(node.next);
                    var after = node.*;
                    after.step.args.at = at + 1;
                    try self.term(args.template[at % len], args.goal[at % len], &after);
                },
                .unify => |args| {
                    if (args.at == args.a.len) return self.run(node.next);
                    var after = node.*;
                    after.step.unify.at += 1;
                    try self.unify(args.a[args.at], args.b[args.at], &after);
                },
                .bag => |state| try self.bag(state.*, node.next),
                .pairing => |state| try self.pairBags(state.*, node.next),
            }
        }

        fn term(self: *Self, template: TemplateExpr, expr: ExprId, next: ?*const Pending) MatchError!void {
            switch (template) {
                .binder => |idx| try self.bind(idx, expr, next),
                .app => |app| {
                    const target = self.terms.wvars.resolve(expr);
                    if (self.terms.bagFor(app.term_id)) |combiner| {
                        return self.startBag(combiner, template, target, next);
                    }
                    const goal_app = switch (self.terms.theorem.interner.node(target).*) {
                        .app => |goal_app| goal_app,
                        else => return,
                    };
                    if (goal_app.term_id != app.term_id or goal_app.args.len != app.args.len) return;
                    const cell = Pending{
                        .step = .{ .args = .{ .template = app.args, .goal = goal_app.args, .at = 0 } },
                        .next = next,
                    };
                    try self.run(&cell);
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
            if (self.bindings[idx]) |value| return self.unify(value, expr, next);
            self.bindings[idx] = expr;
            defer self.bindings[idx] = null;
            try self.run(next);
        }

        fn unify(self: *Self, a: ExprId, b: ExprId, next: ?*const Pending) MatchError!void {
            const wvars = self.terms.wvars;
            const lhs = wvars.resolve(a);
            const rhs = wvars.resolve(b);
            if (lhs == rhs) return self.run(next);
            // Ground terms are canonical, so distinct ids differ.
            if (!try wvars.holdsWVar(lhs) and !try wvars.holdsWVar(rhs)) return;
            if (try self.bindWVar(lhs, rhs, next)) return;
            if (try self.bindWVar(rhs, lhs, next)) return;
            const interner = &self.terms.theorem.interner;
            const lhs_app = switch (interner.node(lhs).*) {
                .app => |app| app,
                else => return,
            };
            const rhs_app = switch (interner.node(rhs).*) {
                .app => |app| app,
                else => return,
            };
            if (lhs_app.term_id != rhs_app.term_id or lhs_app.args.len != rhs_app.args.len) return;
            if (self.terms.bagFor(lhs_app.term_id)) |combiner| {
                if (try self.terms.same(lhs, rhs)) return self.run(next);
                const pairing = (try @call(.never_inline, preparePairing, .{ self, combiner, lhs, rhs })) orelse return;
                defer self.terms.allocator.free(pairing.a);
                defer self.terms.allocator.free(pairing.b);
                return self.pairBags(pairing, next);
            }
            const cell = Pending{
                .step = .{ .unify = .{ .a = lhs_app.args, .b = rhs_app.args, .at = 0 } },
                .next = next,
            };
            try self.run(&cell);
        }

        /// The members of bags `lhs` and `rhs`, copied out of the
        /// fixed-capacity bags as `prepareBag` does; null when no pairing
        /// can make them equal.
        fn preparePairing(self: *Self, combiner: AcuiBag.Combiner, lhs: ExprId, rhs: ExprId) Error!?BagPairing {
            const a = combiner.flatten(self.terms.theorem, lhs) orelse return error.Unsupported;
            const b = combiner.flatten(self.terms.theorem, rhs) orelse return error.Unsupported;
            const idempotent = combiner.law.isIdempotent();
            if (!idempotent and a.len != b.len) return null;
            const allocator = self.terms.allocator;
            const a_members = try allocator.dupe(ExprId, a.slice());
            errdefer allocator.free(a_members);
            return .{ .idempotent = idempotent, .a = a_members, .b = try allocator.dupe(ExprId, b.slice()) };
        }

        fn pairBags(self: *Self, state: BagPairing, next: ?*const Pending) MatchError!void {
            var after = state;
            after.index += 1;
            const cell = Pending{ .step = .{ .pairing = &after }, .next = next };
            if (state.index < state.a.len) {
                const member = state.a[state.index];
                // A member without wvars that the other bag holds pairs with
                // that copy alone: any other partner only adds bindings.
                if (!try self.terms.wvars.holdsWVar(member)) {
                    for (state.b, 0..) |other, at| {
                        const bit = @as(u64, 1) << @intCast(at);
                        if (other != member or (!state.idempotent and state.paired & bit != 0)) continue;
                        after.paired |= bit;
                        return self.pairBags(after, next);
                    }
                }
                for (state.b, 0..) |other, at| {
                    const bit = @as(u64, 1) << @intCast(at);
                    if (!state.idempotent and state.paired & bit != 0) continue;
                    after.paired = state.paired | bit;
                    try self.unify(member, other, &cell);
                    if (self.stop) return;
                }
                return;
            }
            const at = state.index - state.a.len;
            if (at == state.b.len) return self.run(next);
            const member = state.b[at];
            if (state.paired & (@as(u64, 1) << @intCast(at)) != 0 or
                (!try self.terms.wvars.holdsWVar(member) and std.mem.indexOfScalar(ExprId, state.a, member) != null))
            {
                return self.pairBags(after, next);
            }
            for (state.a) |other| {
                try self.unify(other, member, &cell);
                if (self.stop) return;
            }
        }

        /// When `wvar` is an unbound witness variable, run `next` with it
        /// bound to `value` if its constraints allow, and return true.
        fn bindWVar(self: *Self, wvar: ExprId, value: ExprId, next: ?*const Pending) MatchError!bool {
            const wvars = self.terms.wvars;
            const idx = wvars.of(wvar) orelse return false;
            const start = wvars.mark();
            defer wvars.rollback(start);
            if (try wvars.bind(idx, value)) try self.run(next);
            return true;
        }

        fn isRestBinder(self: *const Self, combiner: AcuiBag.Combiner, template: TemplateExpr) bool {
            const idx = switch (template) {
                .binder => |idx| idx,
                .app => return false,
            };
            const bag_sort = self.terms.context.env.terms.items[combiner.head].ret_sort_name;
            return std.mem.eql(u8, self.rule.?.args[idx].sort_name, bag_sort);
        }

        fn startBag(
            self: *Self,
            combiner: AcuiBag.Combiner,
            template: TemplateExpr,
            expr: ExprId,
            next: ?*const Pending,
        ) MatchError!void {
            const state = try @call(.never_inline, prepareBag, .{ self, combiner, template, expr });
            defer self.terms.allocator.free(state.template);
            defer self.terms.allocator.free(state.goal);
            try self.bag(state, next);
        }

        /// The bag's template members in match order and the goal's
        /// members, copied out of the fixed-capacity bags. The bag match
        /// stays on the stack for the rest of the proof, so it holds only
        /// these slices.
        fn prepareBag(self: *Self, combiner: AcuiBag.Combiner, template: TemplateExpr, expr: ExprId) Error!BagState {
            const parts = combiner.flattenTemplate(template) orelse return error.Unsupported;
            const members = combiner.flatten(self.terms.theorem, expr) orelse return error.Unsupported;
            // Bound rest binders and structured members first, the unbound
            // rest binder last: it takes what the others leave.
            var rest: ?usize = null;
            var kept: usize = 0;
            for (parts.slice()) |part| {
                if (self.isRestBinder(combiner, part) and self.bindings[part.binder] == null) {
                    rest = part.binder;
                } else {
                    kept += 1;
                }
            }
            const allocator = self.terms.allocator;
            const ordered = try allocator.alloc(TemplateExpr, kept);
            errdefer allocator.free(ordered);
            var count: usize = 0;
            for (parts.slice()) |part| {
                if (self.isRestBinder(combiner, part) and self.bindings[part.binder] == null) continue;
                ordered[count] = part;
                count += 1;
            }
            return .{
                .combiner = combiner,
                .template = ordered,
                .goal = try allocator.dupe(ExprId, members.slice()),
                .rest = rest,
            };
        }

        fn bag(self: *Self, state: BagState, next: ?*const Pending) MatchError!void {
            if (state.index == state.template.len) return self.finishBag(state, next);
            const part = state.template[state.index];
            if (self.isRestBinder(state.combiner, part)) {
                // A rest binder an earlier match bound: its members must be
                // among the goal's.
                var after = state;
                after.used = (try @call(.never_inline, takeAll, .{ self, state, self.bindings[part.binder].? })) orelse return;
                after.index += 1;
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

        /// `state.used` with a goal member taken for each member of
        /// `value`, or null when one has none.
        fn takeAll(self: *Self, state: BagState, value: ExprId) Error!?u64 {
            const members = state.combiner.flatten(self.terms.theorem, value) orelse return error.Unsupported;
            var used = state.used;
            for (members.slice()) |member| {
                used |= (try self.takeMember(state.combiner, state.goal, used, member)) orelse return null;
            }
            return used;
        }

        /// The bit of a goal member equal to `member` that `used` leaves
        /// free, or under an idempotent law one already taken; null when
        /// there is none.
        fn takeMember(self: *Self, combiner: AcuiBag.Combiner, goal: []const ExprId, used: u64, member: ExprId) Error!?u64 {
            var taken: ?u64 = null;
            for (goal, 0..) |candidate, at| {
                if (!try self.terms.same(candidate, member)) continue;
                const bit = @as(u64, 1) << @intCast(at);
                if (used & bit == 0) return bit;
                taken = bit;
            }
            return if (combiner.law.isIdempotent()) taken else null;
        }

        fn finishBag(self: *Self, state: BagState, next: ?*const Pending) MatchError!void {
            const rest = state.rest orelse {
                if (@popCount(state.used) == state.goal.len) try self.run(next);
                return;
            };
            const value = (try @call(.never_inline, leftover, .{ self, state })) orelse return;
            try self.bind(rest, value, next);
        }

        /// The bag of the goal members `state` leaves untaken.
        fn leftover(self: *Self, state: BagState) Error!?ExprId {
            var left: AcuiBag.ExprBag = .{};
            for (state.goal, 0..) |member, at| {
                if (state.used & (@as(u64, 1) << @intCast(at)) == 0) _ = left.append(member);
            }
            // The goal's members are canonical and in order, so the
            // leftover is canonical as it stands.
            return state.combiner.build(self.terms.theorem, left.slice());
        }
    };
}
