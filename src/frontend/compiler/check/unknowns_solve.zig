//! The named-unknown pre-pass: before the line walk, solve the named
//! unknowns (`?a`) of one proof block from all its lines at once, so a line
//! can use a value that only a later line fixes.
//!
//! Every rule application gives equations: its conclusion is its line's
//! statement (or, inline, its parent's premise), each premise is what its
//! reference states, and each explicit binding is its value. The unknowns
//! are the names, a fresh variable per anonymous hole, and a fresh variable
//! per rule binder of each application. The pass solves the equations by
//! first-order unification and commits only what is forced: an equation it
//! cannot decide syntactically (an `@acui` combiner, a `@rewrite` head, a
//! definition) is dropped, and dropping an equation only leaves more
//! solutions, never a wrong one. A clash anywhere solves nothing; the walk
//! then reports it where it meets it.
//!
//! Rules whose match is not their literal conclusion (`@view`, `@recover`,
//! `@abstract`, `@fresh`, `@freshen`, `@fallback`) contribute nothing; the
//! walk fills names there.

const std = @import("std");
const ExprModule = @import("../../../trusted/expressions.zig");
const Expr = ExprModule.Expr;
const ExprId = @import("../../expr.zig").ExprId;
const TheoremContext = @import("../../expr.zig").TheoremContext;
const GlobalEnv = @import("../../env.zig").GlobalEnv;
const RuleDecl = @import("../../env.zig").RuleDecl;
const MM0Parser = @import("../../parse_recovery.zig").MM0Parser;
const RewriteRegistry = @import("../../rewrite_registry.zig").RewriteRegistry;
const TemplateExpr = @import("../../rules.zig").TemplateExpr;
const SurfaceExpr = @import("../../surface_expr.zig");
const ProofScript = @import("../../proof_script.zig");
const ProofLine = ProofScript.ProofLine;
const RuleApplication = ProofScript.RuleApplication;
const TheoryState = @import("../theory_state.zig").TheoryState;
const Holes = @import("../holes.zig");
const NameExprMap = @import("./types.zig").NameExprMap;
const Unknowns = @import("./unknowns.zig");
const AcuiBag = @import("../../acui_bag.zig");

pub const Inputs = struct {
    allocator: std.mem.Allocator,
    theory: *TheoryState,
    theorem: *TheoremContext,
    theorem_vars: *NameExprMap,
    lines: []const ProofLine,
    /// The theorem's conclusion, which the last line proves.
    conclusion: ?ExprId,
};

/// Solve the block's named unknowns and bind the solved ones in `out`.
pub fn solve(inputs: Inputs, out: *Unknowns.Unknowns) !void {
    if (!mayNameUnknowns(&inputs.theory.parser, inputs.lines)) return;
    var solver = Solver{ .inputs = inputs };
    defer solver.deinit();
    // A clash, or anything else the pass cannot read, solves nothing.
    solver.run() catch |err| switch (err) {
        error.OutOfMemory => return err,
        else => return,
    };
    var it = solver.names.iterator();
    while (it.next()) |entry| {
        const value = try solver.resolveFully(entry.value_ptr.*);
        if (solver.mentionsVariable(value)) continue;
        try out.bound.put(inputs.allocator, entry.key_ptr.*, value);
    }
}

const Solver = struct {
    inputs: Inputs,
    /// Each name's variable.
    names: std.StringArrayHashMapUnmanaged(ExprId) = .empty,
    /// The pass's own variables, and what each is bound to.
    variables: std.AutoHashMapUnmanaged(ExprId, ?ExprId) = .empty,
    /// Each line's statement, by label.
    statements: std.StringHashMapUnmanaged(ExprId) = .empty,
    work: std.ArrayListUnmanaged([2]ExprId) = .empty,
    /// Bag equations not decided yet: retried while bindings are made.
    postponed: std.ArrayListUnmanaged([2]ExprId) = .empty,
    /// Bindings made so far, to tell whether a retry round made progress.
    progress: usize = 0,

    fn deinit(self: *Solver) void {
        const allocator = self.inputs.allocator;
        self.names.deinit(allocator);
        self.variables.deinit(allocator);
        self.statements.deinit(allocator);
        self.work.deinit(allocator);
        self.postponed.deinit(allocator);
    }

    fn run(self: *Solver) !void {
        const theory = self.inputs.theory;
        // Statements first: a reference may name any earlier line.
        var any_named = false;
        // The walk stops at an incomplete line; so does the pass.
        const lines = for (self.inputs.lines, 0..) |line, idx| {
            if (line.incomplete) break self.inputs.lines[0..idx];
        } else self.inputs.lines;
        for (lines) |line| {
            const parsed = Holes.parseAssertion(
                &theory.parser,
                self.inputs.theorem,
                self.inputs.theorem_vars,
                &theory.sort_vars,
                line.assertion.text,
            ) catch |err| switch (err) {
                error.OutOfMemory => return err,
                else => continue,
            };
            const statement = switch (parsed) {
                .concrete => |expr| expr,
                .holey => |surface| blk: {
                    if (Unknowns.hasNamed(surface)) any_named = true;
                    break :blk (try self.internSurface(surface)) orelse continue;
                },
            };
            try self.statements.put(self.inputs.allocator, line.label, statement);
        }
        if (!any_named) return;

        var last: ?ExprId = null;
        for (lines) |line| {
            const statement = self.statements.get(line.label) orelse {
                last = null;
                continue;
            };
            last = statement;
            try self.application(line.application, statement);
        }
        // The last line meets the conclusion only when the block is whole.
        if (lines.len == self.inputs.lines.len) if (last) |statement| if (self.inputs.conclusion) |conclusion| {
            try self.equate(statement, conclusion);
        };
        try self.drain();
        while (self.postponed.items.len != 0) {
            const before = self.progress;
            try self.work.appendSlice(self.inputs.allocator, self.postponed.items);
            self.postponed.clearRetainingCapacity();
            try self.drain();
            if (self.progress == before) break;
        }
    }

    /// The equations of `app`, whose conclusion is `goal`.
    fn application(self: *Solver, app: RuleApplication, goal: ExprId) anyerror!void {
        const theory = self.inputs.theory;
        const theorem = self.inputs.theorem;
        if (!isOrdinaryRuleName(app.rule_name)) return;
        const rule_id = theory.env.rule_names.get(app.rule_name) orelse return;
        if (!self.literalRule(rule_id)) return;
        const rule: *const RuleDecl = &theory.env.rules.items[rule_id];
        if (app.refs.len != rule.hyps.len) return;

        const allocator = self.inputs.allocator;
        const binders = try allocator.alloc(ExprId, rule.args.len);
        defer allocator.free(binders);
        for (rule.args, binders) |arg, *binder| {
            binder.* = try self.mint(arg.sort_name);
        }
        for (app.arg_bindings) |binding| {
            const idx = for (rule.arg_names, 0..) |name, i| {
                if (name != null and std.mem.eql(u8, name.?, binding.name)) break i;
            } else continue;
            const value = theory.parser.parseArgText(
                binding.formula.text,
                self.inputs.theorem_vars,
                rule.args[idx],
            ) catch |err| switch (err) {
                error.OutOfMemory => return err,
                else => continue,
            };
            try self.equate(binders[idx], try theorem.internParsedExpr(value));
        }

        try self.equate(try theorem.instantiateTemplate(rule.concl, binders), goal);
        for (app.refs, rule.hyps) |ref, hyp| {
            const premise = try theorem.instantiateTemplate(hyp, binders);
            switch (ref) {
                .hyp => |hyp_ref| {
                    const resolved = ProofScript.resolveHypRef(
                        theorem.theorem_hyp_names,
                        theorem.theorem_hyps.items.len,
                        hyp_ref,
                    );
                    switch (resolved) {
                        .index => |idx| try self.equate(premise, theorem.theorem_hyps.items[idx]),
                        .unknown, .ambiguous => {},
                    }
                },
                .line => |label| if (self.statements.get(label.label)) |stated| {
                    try self.equate(premise, stated);
                },
                .application => |child| try self.application(child, premise),
            }
        }
    }

    /// Whether `rule_id`'s literal conclusion and premises are what the
    /// checker matches.
    fn literalRule(self: *const Solver, rule_id: u32) bool {
        const theory = self.inputs.theory;
        return !theory.views.contains(rule_id) and
            !theory.fresh_bindings.contains(rule_id) and
            !theory.freshen_bindings.contains(rule_id) and
            theory.registry.getFallbackRule(rule_id) == null;
    }

    fn internSurface(self: *Solver, expr: *const Expr) !?ExprId {
        const theorem = self.inputs.theorem;
        switch (expr.*) {
            .variable => return try theorem.internParsedExpr(expr),
            .hole => |hole| {
                const sort_name = SurfaceExpr.sortNameById(&self.inputs.theory.env, hole.sort) orelse
                    return null;
                const name = hole.name orelse return try self.mint(sort_name);
                const entry = try self.names.getOrPut(self.inputs.allocator, name);
                if (!entry.found_existing) entry.value_ptr.* = try self.mint(sort_name);
                return entry.value_ptr.*;
            },
            .term => |term| {
                const args = try theorem.allocator.alloc(ExprId, term.args.len);
                defer theorem.allocator.free(args);
                for (term.args, args) |arg, *out| {
                    out.* = (try self.internSurface(arg)) orelse return null;
                }
                return try theorem.interner.internApp(term.id, args);
            },
        }
    }

    fn mint(self: *Solver, sort_name: []const u8) !ExprId {
        const variable = try self.inputs.theorem.addLineHolePlaceholder(sort_name);
        try self.variables.put(self.inputs.allocator, variable, null);
        return variable;
    }

    fn isVariable(self: *const Solver, id: ExprId) bool {
        return self.variables.contains(id);
    }

    fn resolve(self: *const Solver, id: ExprId) ExprId {
        var current = id;
        while (self.variables.get(current)) |binding| {
            current = binding orelse return current;
        }
        return current;
    }

    fn equate(self: *Solver, lhs: ExprId, rhs: ExprId) !void {
        try self.work.append(self.inputs.allocator, .{ lhs, rhs });
    }

    fn drain(self: *Solver) !void {
        const theorem = self.inputs.theorem;
        while (self.work.pop()) |pair| {
            const lhs = self.resolve(pair[0]);
            const rhs = self.resolve(pair[1]);
            if (lhs == rhs) continue;
            if (self.isVariable(lhs)) {
                try self.bind(lhs, rhs);
                continue;
            }
            if (self.isVariable(rhs)) {
                try self.bind(rhs, lhs);
                continue;
            }
            if (self.combinerOf(lhs) orelse self.combinerOf(rhs)) |combiner| {
                try self.bagStep(combiner, lhs, rhs);
                continue;
            }
            const lhs_node = theorem.interner.node(lhs).*;
            const rhs_node = theorem.interner.node(rhs).*;
            const lhs_app = switch (lhs_node) {
                .app => |app| app,
                .variable => switch (rhs_node) {
                    .app => |app| if (self.undecided(app.term_id)) continue else return error.Clash,
                    // Distinct theorem variables.
                    .variable => return error.Clash,
                    .placeholder => continue,
                },
                .placeholder => continue,
            };
            const rhs_app = switch (rhs_node) {
                .app => |app| app,
                .variable => if (self.undecided(lhs_app.term_id)) continue else return error.Clash,
                .placeholder => continue,
            };
            if (lhs_app.term_id == rhs_app.term_id and lhs_app.args.len == rhs_app.args.len) {
                if (self.undecided(lhs_app.term_id)) continue;
                for (lhs_app.args, rhs_app.args) |l, r| try self.equate(l, r);
                continue;
            }
            if (self.undecided(lhs_app.term_id) or self.undecided(rhs_app.term_id)) continue;
            return error.Clash;
        }
    }

    /// Heads whose applications may equal a different head: a definition
    /// (it unfolds) or a `@rewrite` head (it rewrites).
    fn undecided(self: *const Solver, term_id: u32) bool {
        const theory = self.inputs.theory;
        return theory.env.openableDef(term_id) != null or
            theory.registry.getRewriteRules(term_id).len != 0;
    }

    /// The `@acui` combiner `expr` is an application of, if any.
    fn combinerOf(self: *const Solver, expr: ExprId) ?AcuiBag.Combiner {
        const theory = self.inputs.theory;
        const app = switch (self.inputs.theorem.interner.node(expr).*) {
            .app => |app| app,
            else => return null,
        };
        if (app.args.len != 2) return null;
        // Read as a proof can follow it: the unit is a member like any
        // other unless unit laws remove it from both sides.
        return AcuiBag.Combiner.provable(&theory.registry, &theory.env, app.term_id);
    }

    // ---------------------------------------------------------------
    // The bag step: two bags of one combiner, equal modulo its laws.
    // Leaves are members, except the pass's own variables of the bag's
    // sort, which are rests (they stand for any part of the bag). A
    // theorem variable is a rigid member. Only forced conclusions are
    // drawn; anything else waits for more bindings (`postponed`).

    fn bagStep(self: *Solver, combiner: AcuiBag.Combiner, lhs: ExprId, rhs: ExprId) !void {
        const allocator = self.inputs.allocator;
        var left: std.ArrayListUnmanaged(ExprId) = .empty;
        defer left.deinit(allocator);
        var right: std.ArrayListUnmanaged(ExprId) = .empty;
        defer right.deinit(allocator);
        var units: [2]usize = .{ 0, 0 };
        try self.flattenBag(combiner, lhs, &left, &units[0]);
        try self.flattenBag(combiner, rhs, &right, &units[1]);
        // A leaf under a definition or `@rewrite` head may stand for any
        // number of members, and a combiner with rewrites of its own may
        // equal other bags: neither is decided by member counting.
        if (self.undecided(combiner.head) or self.anyUndecidedLeaf(left.items) or
            self.anyUndecidedLeaf(right.items))
        {
            try self.postponed.append(allocator, .{ lhs, rhs });
            return;
        }
        const done = switch (combiner.law) {
            .multiset => try self.bagMultiset(combiner, &left, &right, units),
            .set => try self.bagSet(combiner, &left, &right, units),
            // A dropped unit shifts the positions the pairing reads.
            .sequence => units[0] == 0 and units[1] == 0 and
                try self.bagSequence(combiner, left.items, right.items),
            .idempotent_sequence => false,
        };
        if (!done) try self.postponed.append(allocator, .{ lhs, rhs });
    }

    /// The leaves of `expr` under `combiner`, in order, resolved, without
    /// the unit when unit laws remove it; `units` counts the units dropped.
    fn flattenBag(
        self: *Solver,
        combiner: AcuiBag.Combiner,
        expr: ExprId,
        out: *std.ArrayListUnmanaged(ExprId),
        units: *usize,
    ) !void {
        const resolved = self.resolve(expr);
        if (!self.isVariable(resolved)) switch (self.inputs.theorem.interner.node(resolved).*) {
            .app => |app| {
                if (app.term_id == combiner.head and app.args.len == 2) {
                    try self.flattenBag(combiner, app.args[0], out, units);
                    try self.flattenBag(combiner, app.args[1], out, units);
                    return;
                }
                if (combiner.unit) |unit| if (app.term_id == unit and app.args.len == 0) {
                    units.* += 1;
                    return;
                };
            },
            else => {},
        };
        try out.append(self.inputs.allocator, resolved);
    }

    /// Split `leaves` into members and rests.
    fn partition(
        self: *Solver,
        leaves: []const ExprId,
        members: *std.ArrayListUnmanaged(ExprId),
        rests: *std.ArrayListUnmanaged(ExprId),
    ) !void {
        for (leaves) |leaf| {
            if (self.isVariable(leaf))
                try rests.append(self.inputs.allocator, leaf)
            else
                try members.append(self.inputs.allocator, leaf);
        }
    }

    /// Multiset law: cancel identical members; then, when one side has no
    /// rest, each member of the other side is a distinct member of it, and
    /// a single rest takes what is left. True when the equation is done.
    fn bagMultiset(
        self: *Solver,
        combiner: AcuiBag.Combiner,
        left: *std.ArrayListUnmanaged(ExprId),
        right: *std.ArrayListUnmanaged(ExprId),
        units: [2]usize,
    ) !bool {
        cancelIdentical(left, right);
        const allocator = self.inputs.allocator;
        var lm: std.ArrayListUnmanaged(ExprId) = .empty;
        defer lm.deinit(allocator);
        var lr: std.ArrayListUnmanaged(ExprId) = .empty;
        defer lr.deinit(allocator);
        var rm: std.ArrayListUnmanaged(ExprId) = .empty;
        defer rm.deinit(allocator);
        var rr: std.ArrayListUnmanaged(ExprId) = .empty;
        defer rr.deinit(allocator);
        try self.partition(left.items, &lm, &lr);
        try self.partition(right.items, &rm, &rr);
        if (lr.items.len != 0 and rr.items.len != 0) return false;
        const open_m, const open_r, const closed_m, const closed_units = if (lr.items.len != 0)
            .{ lm.items, lr.items, rm.items, units[1] }
        else
            .{ rm.items, rr.items, lm.items, units[0] };
        if (open_m.len > closed_m.len) return error.Clash;
        if (open_r.len == 0 and open_m.len != closed_m.len) return error.Clash;
        const assignment = (try self.uniqueMatching(open_m, closed_m)) orelse return false;
        defer allocator.free(assignment);
        const used = try allocator.alloc(bool, closed_m.len);
        defer allocator.free(used);
        @memset(used, false);
        for (open_m, assignment) |member, target| {
            used[target] = true;
            try self.equate(member, closed_m[target]);
        }
        if (open_r.len != 1) return open_r.len == 0;
        var leftover: std.ArrayListUnmanaged(ExprId) = .empty;
        defer leftover.deinit(allocator);
        for (closed_m, used) |member, taken| if (!taken) try leftover.append(allocator, member);
        try self.appendUnits(combiner, closed_units, &leftover);
        const value = (try combiner.build(self.inputs.theorem, leftover.items)) orelse return false;
        try self.equate(open_r[0], value);
        return true;
    }

    /// Set law: when one side has no rest, each member of the other side is
    /// one of its members; commit those with a single candidate. A side
    /// that is a single rest takes the other, when that has no rest.
    fn bagSet(
        self: *Solver,
        combiner: AcuiBag.Combiner,
        left: *std.ArrayListUnmanaged(ExprId),
        right: *std.ArrayListUnmanaged(ExprId),
        units: [2]usize,
    ) !bool {
        const allocator = self.inputs.allocator;
        dedupe(left);
        dedupe(right);
        var lm: std.ArrayListUnmanaged(ExprId) = .empty;
        defer lm.deinit(allocator);
        var lr: std.ArrayListUnmanaged(ExprId) = .empty;
        defer lr.deinit(allocator);
        var rm: std.ArrayListUnmanaged(ExprId) = .empty;
        defer rm.deinit(allocator);
        var rr: std.ArrayListUnmanaged(ExprId) = .empty;
        defer rr.deinit(allocator);
        try self.partition(left.items, &lm, &lr);
        try self.partition(right.items, &rm, &rr);
        if (rr.items.len == 0) try self.commitUniqueCandidates(lm.items, rm.items);
        if (lr.items.len == 0) try self.commitUniqueCandidates(rm.items, lm.items);
        if (lm.items.len == 0 and lr.items.len == 1 and rr.items.len == 0) {
            try self.appendUnits(combiner, @min(units[1], 1), &rm);
            try self.equate(lr.items[0], (try combiner.build(self.inputs.theorem, rm.items)) orelse return false);
            return true;
        }
        if (rm.items.len == 0 and rr.items.len == 1 and lr.items.len == 0) {
            try self.appendUnits(combiner, @min(units[0], 1), &lm);
            try self.equate(rr.items[0], (try combiner.build(self.inputs.theorem, lm.items)) orelse return false);
            return true;
        }
        return lr.items.len == 0 and rr.items.len == 0;
    }

    /// Append `count` units to `members`: a rest's value keeps the units
    /// the closed side writes, so it is spelled as the source spells it.
    fn appendUnits(
        self: *Solver,
        combiner: AcuiBag.Combiner,
        count: usize,
        members: *std.ArrayListUnmanaged(ExprId),
    ) !void {
        const unit = combiner.unit orelse return;
        const unit_expr = try self.inputs.theorem.interner.internApp(unit, &.{});
        for (0..count) |_| try members.append(self.inputs.allocator, unit_expr);
    }

    /// Each of `members` equals one of `candidates`: commit those that can
    /// equal only one; a member that can equal none is a clash.
    fn commitUniqueCandidates(self: *Solver, members: []const ExprId, candidates: []const ExprId) !void {
        for (members) |member| {
            var only: ?ExprId = null;
            var count: usize = 0;
            for (candidates) |candidate| {
                if (!try self.compatible(member, candidate)) continue;
                count += 1;
                only = candidate;
            }
            if (count == 0) return error.Clash;
            if (count == 1) try self.equate(member, only.?);
        }
    }

    /// Sequence law: cancel the common ends; then pair positionally when
    /// neither side has a rest, or around a single rest on one side.
    fn bagSequence(
        self: *Solver,
        combiner: AcuiBag.Combiner,
        left_all: []const ExprId,
        right_all: []const ExprId,
    ) !bool {
        var left = left_all;
        var right = right_all;
        while (left.len != 0 and right.len != 0 and left[0] == right[0]) {
            left = left[1..];
            right = right[1..];
        }
        while (left.len != 0 and right.len != 0 and left[left.len - 1] == right[right.len - 1]) {
            left = left[0 .. left.len - 1];
            right = right[0 .. right.len - 1];
        }
        const left_rests = self.countRests(left);
        const right_rests = self.countRests(right);
        if (left_rests == 0 and right_rests == 0) {
            if (left.len != right.len) return error.Clash;
            for (left, right) |l, r| try self.equate(l, r);
            return true;
        }
        if (left_rests != 0 and right_rests != 0) return false;
        const open, const closed = if (left_rests != 0) .{ left, right } else .{ right, left };
        if (self.countRests(open) != 1) return false;
        const at = for (open, 0..) |leaf, i| {
            if (self.isVariable(leaf)) break i;
        } else unreachable;
        const before = open[0..at];
        const after = open[at + 1 ..];
        if (before.len + after.len > closed.len) return error.Clash;
        for (before, closed[0..before.len]) |l, r| try self.equate(l, r);
        for (after, closed[closed.len - after.len ..]) |l, r| try self.equate(l, r);
        const middle = closed[before.len .. closed.len - after.len];
        try self.equate(open[at], (try combiner.build(self.inputs.theorem, middle)) orelse return false);
        return true;
    }

    fn anyUndecidedLeaf(self: *const Solver, leaves: []const ExprId) bool {
        for (leaves) |leaf| switch (self.inputs.theorem.interner.node(leaf).*) {
            .app => |app| if (self.undecided(app.term_id)) return true,
            else => {},
        };
        return false;
    }

    fn countRests(self: *const Solver, leaves: []const ExprId) usize {
        var count: usize = 0;
        for (leaves) |leaf| {
            if (self.isVariable(leaf)) count += 1;
        }
        return count;
    }

    /// The only injective assignment of `members` into `targets` that pairs
    /// only compatible terms, or null when there are several; a clash when
    /// there is none. Caller frees.
    fn uniqueMatching(self: *Solver, members: []const ExprId, targets: []const ExprId) !?[]usize {
        const allocator = self.inputs.allocator;
        const compat = try allocator.alloc(bool, members.len * targets.len);
        defer allocator.free(compat);
        for (members, 0..) |member, i| for (targets, 0..) |target, j| {
            compat[i * targets.len + j] = try self.compatible(member, target);
        };
        var matcher = Matching{
            .compat = compat,
            .members = members.len,
            .targets = targets.len,
            .owner = try allocator.alloc(?usize, targets.len),
            .seen = try allocator.alloc(bool, targets.len),
        };
        defer allocator.free(matcher.owner);
        defer allocator.free(matcher.seen);
        if (!matcher.run(null)) return error.Clash;
        const assignment = try allocator.alloc(usize, members.len);
        errdefer allocator.free(assignment);
        for (matcher.owner, 0..) |owner, j| if (owner) |i| {
            assignment[i] = j;
        };
        // Another matching differs from this one in some member's pair:
        // forbid each pair in turn and look for one.
        for (assignment, 0..) |target, member| {
            if (matcher.run(.{ member, target })) {
                allocator.free(assignment);
                return null;
            }
        }
        return assignment;
    }

    /// Whether `lhs` and `rhs` could be equal: false only when no binding
    /// of the pass's variables makes them so.
    fn compatible(self: *Solver, lhs_id: ExprId, rhs_id: ExprId) !bool {
        const lhs = self.resolve(lhs_id);
        const rhs = self.resolve(rhs_id);
        if (lhs == rhs or self.isVariable(lhs) or self.isVariable(rhs)) return true;
        const theorem = self.inputs.theorem;
        const lhs_node = theorem.interner.node(lhs).*;
        const rhs_node = theorem.interner.node(rhs).*;
        switch (lhs_node) {
            .placeholder => return true,
            .variable => return switch (rhs_node) {
                .app => |app| self.flexibleHead(app.term_id),
                .variable => false,
                .placeholder => true,
            },
            .app => |lhs_app| switch (rhs_node) {
                .placeholder => return true,
                .variable => return self.flexibleHead(lhs_app.term_id),
                .app => |rhs_app| {
                    if (lhs_app.term_id != rhs_app.term_id or lhs_app.args.len != rhs_app.args.len) {
                        return self.flexibleHead(lhs_app.term_id) or self.flexibleHead(rhs_app.term_id);
                    }
                    if (self.flexibleHead(lhs_app.term_id)) return true;
                    for (lhs_app.args, rhs_app.args) |l, r| {
                        if (!try self.compatible(l, r)) return false;
                    }
                    return true;
                },
            },
        }
    }

    /// Heads whose applications may equal a term with another head.
    fn flexibleHead(self: *const Solver, term_id: u32) bool {
        const theory = self.inputs.theory;
        return self.undecided(term_id) or
            AcuiBag.Combiner.of(&theory.registry, &theory.env, term_id) != null;
    }

    fn bind(self: *Solver, variable: ExprId, value: ExprId) !void {
        if (try self.occurs(variable, value)) return error.Clash;
        const env = &self.inputs.theory.env;
        const theorem = self.inputs.theorem;
        const want = try SurfaceExpr.exprIdSortName(theorem, env, variable);
        const have = try SurfaceExpr.exprIdSortName(theorem, env, value);
        if (!std.mem.eql(u8, want, have)) return error.Clash;
        self.variables.getPtr(variable).?.* = value;
        self.progress += 1;
    }

    fn occurs(self: *Solver, variable: ExprId, expr: ExprId) !bool {
        const resolved = self.resolve(expr);
        if (resolved == variable) return true;
        return switch (self.inputs.theorem.interner.node(resolved).*) {
            .app => |app| for (app.args) |arg| {
                if (try self.occurs(variable, arg)) break true;
            } else false,
            else => false,
        };
    }

    fn resolveFully(self: *Solver, expr: ExprId) !ExprId {
        const theorem = self.inputs.theorem;
        const resolved = self.resolve(expr);
        const app = switch (theorem.interner.node(resolved).*) {
            .app => |app| app,
            else => return resolved,
        };
        const args = try theorem.allocator.alloc(ExprId, app.args.len);
        defer theorem.allocator.free(args);
        var changed = false;
        for (app.args, args) |arg, *out| {
            out.* = try self.resolveFully(arg);
            if (out.* != arg) changed = true;
        }
        if (!changed) return resolved;
        return try theorem.interner.internApp(app.term_id, args);
    }

    fn mentionsVariable(self: *const Solver, expr: ExprId) bool {
        if (self.isVariable(expr)) return true;
        return switch (self.inputs.theorem.interner.node(expr).*) {
            .app => |app| for (app.args) |arg| {
                if (self.mentionsVariable(arg)) break true;
            } else false,
            else => false,
        };
    }
};

/// Kuhn's augmenting-path matching of members into targets over a
/// compatibility matrix, optionally with one pair forbidden.
const Matching = struct {
    compat: []const bool,
    members: usize,
    targets: usize,
    owner: []?usize,
    seen: []bool,
    banned: ?[2]usize = null,

    /// Whether every member can be matched.
    fn run(self: *Matching, banned: ?[2]usize) bool {
        self.banned = banned;
        @memset(self.owner, null);
        for (0..self.members) |member| {
            @memset(self.seen, false);
            if (!self.augment(member)) return false;
        }
        return true;
    }

    fn edge(self: *const Matching, member: usize, target: usize) bool {
        if (self.banned) |pair| if (pair[0] == member and pair[1] == target) return false;
        return self.compat[member * self.targets + target];
    }

    fn augment(self: *Matching, member: usize) bool {
        for (0..self.targets) |target| {
            if (self.seen[target] or !self.edge(member, target)) continue;
            self.seen[target] = true;
            if (self.owner[target] == null or self.augment(self.owner[target].?)) {
                self.owner[target] = member;
                return true;
            }
        }
        return false;
    }
};

/// Remove members the two sides share, one copy at a time.
fn cancelIdentical(left: *std.ArrayListUnmanaged(ExprId), right: *std.ArrayListUnmanaged(ExprId)) void {
    var i: usize = 0;
    outer: while (i < left.items.len) {
        for (right.items, 0..) |item, j| {
            if (item != left.items[i]) continue;
            _ = left.orderedRemove(i);
            _ = right.orderedRemove(j);
            continue :outer;
        }
        i += 1;
    }
}

/// Drop repeated leaves (set law).
fn dedupe(list: *std.ArrayListUnmanaged(ExprId)) void {
    var len: usize = 0;
    for (list.items) |item| {
        if (std.mem.indexOfScalar(ExprId, list.items[0..len], item) != null) continue;
        list.items[len] = item;
        len += 1;
    }
    list.shrinkRetainingCapacity(len);
}

/// Whether any line could hold a named unknown: some line's statement holds
/// an `@unknown` prefix. A cheap text test, so blocks without names (and
/// theories without `@unknown`) pay nothing.
fn mayNameUnknowns(parser: *const MM0Parser, lines: []const ProofLine) bool {
    const prefixes = &parser.core.unknown_prefixes;
    if (prefixes.count() == 0) return false;
    for (lines) |line| {
        var it = prefixes.keyIterator();
        while (it.next()) |prefix| {
            if (std.mem.indexOf(u8, line.assertion.text, prefix.*) != null) return true;
        }
    }
    return false;
}

fn isOrdinaryRuleName(name: []const u8) bool {
    return !ProofScript.isOpenGoalRuleName(name) and
        !ProofScript.isSorryRuleName(name) and
        !ProofScript.isSearchPlaceholderRuleName(name);
}
