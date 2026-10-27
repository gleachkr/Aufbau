//! The search core's prover (`docs/design_notes/shared_witness.md` D1, D4):
//! one agenda of open goals, solved most recent first in
//! continuation-passing style, and one proof record.
//!
//! A goal is tried with the pool facts that state it and the closers, then
//! (with depth left) the safe rules, and only when no safe rule applies,
//! the unsafe rules one depth lower. A rule's premises go on the agenda
//! ahead of the goal's close marker; when the run reaches the marker the
//! goal is proved, and the run goes on with the rest of the agenda.
//!
//! Stage C0's goals are ground, so a proved goal never helps its
//! continuation by being proved another way: when the continuation fails,
//! the goal's other alternatives are cut (the W5 prune, in the form it takes
//! without witness variables). For the same reason a goal that runs out of
//! alternatives without reaching its marker has no proof at its depth, and
//! a proved goal has one at every depth at least its own; both are
//! memoized for the whole run.

const std = @import("std");
const ExprId = @import("../../../expr.zig").ExprId;
const ProofScript = @import("../../../proof_script.zig");
const TemplateExpr = @import("../../../rules.zig").TemplateExpr;
const Context = @import("../types.zig").Context;
const GlobalBudget = @import("../types.zig").GlobalBudget;
const catalog_mod = @import("./catalog.zig");
const Catalog = catalog_mod.Catalog;
const terms_mod = @import("./terms.zig");
const Terms = terms_mod.Terms;

pub const Error = terms_mod.Error || error{
    SearchBudgetExhausted,
    SearchStackExhausted,
};

/// One applied step of the proof record.
pub const Node = struct {
    step: Step,
    /// One slot per premise, filled as the premise is proved.
    children: []?*const Node,
};

pub const Step = union(enum) {
    rule: struct { rule_id: u32, bindings: []const ExprId },
    /// A pool fact that states the goal.
    ref: ProofScript.Ref,
};

/// A pool fact and the canonical expression it states.
pub const Fact = struct {
    expr: ExprId,
    ref: ProofScript.Ref,
};

/// Called once the agenda is empty, with the root of the finished proof
/// record; true when the checker accepts the proof.
pub const CloseOut = struct {
    ctx: *anyopaque,
    tryFn: *const fn (ctx: *anyopaque, root: *const Node) Error!bool,
};

pub const Stats = struct {
    /// Goals expanded (memo hits and path repeats excluded).
    nodes: usize = 0,
    /// Finished proofs the checker rejected at close-out.
    rejects: usize = 0,
};

const Goal = struct {
    expr: ExprId,
    depth: usize,
    slot: *?*const Node,
    /// The goals this one was reached through.
    path: ?*const PathCell,
};

const PathCell = struct {
    expr: ExprId,
    next: ?*const PathCell,
};

/// A goal being solved. `reached` is set once the run passes its marker.
const Frame = struct {
    id: u32,
    goal: Goal,
    reached: bool = false,
};

const Agenda = struct {
    item: union(enum) {
        goal: Goal,
        close: *Frame,
    },
    next: ?*const Agenda,
};

/// How a run ended: the whole proof was accepted, this branch failed, or
/// the continuation of the goal of frame `cut` failed after the goal was
/// proved, so the goal's remaining alternatives are skipped.
const Outcome = union(enum) {
    proved,
    failed,
    cut: u32,
};

const Proved = struct {
    depth: usize,
    node: *const Node,
};

pub const Prover = struct {
    allocator: std.mem.Allocator,
    /// Owns the proof record; lives for the run.
    arena: std.mem.Allocator,
    context: *const Context,
    terms: *Terms,
    catalog: *const Catalog,
    facts: []const Fact,
    budget: ?*GlobalBudget,
    close_out: CloseOut,
    stack_base: usize,
    stack_guard_bytes: usize,
    /// Per goal: the greatest depth at which it has no proof.
    failed: std.AutoHashMapUnmanaged(ExprId, usize) = .empty,
    /// Per goal: a proof, and the depth it was found at.
    proved: std.AutoHashMapUnmanaged(ExprId, Proved) = .empty,
    next_frame: u32 = 0,
    /// The root goal's slot during `solve`.
    root: ?*const ?*const Node = null,
    /// Path repeats pruned so far. A failure below a prune depends on the
    /// path, so it is not memoized.
    prunes: usize = 0,
    stats: Stats = .{},

    pub fn deinit(self: *Prover) void {
        self.failed.deinit(self.allocator);
        self.proved.deinit(self.allocator);
        self.* = undefined;
    }

    /// Search for a proof of the canonical `goal` within `depth` unsafe
    /// steps per branch; true once the close-out accepted one.
    pub fn solve(self: *Prover, goal: ExprId, depth: usize) Error!bool {
        var root: ?*const Node = null;
        self.root = &root;
        defer self.root = null;
        const outcome = try self.prove(.{ .expr = goal, .depth = depth, .slot = &root, .path = null }, null);
        return outcome == .proved;
    }

    fn charge(self: *Prover) Error!void {
        if (self.budget) |budget| try budget.check();
        if (self.stack_base -| @frameAddress() > self.stack_guard_bytes) return error.SearchStackExhausted;
    }

    fn run(self: *Prover, agenda: ?*const Agenda) Error!Outcome {
        const cell = agenda orelse return self.finish();
        switch (cell.item) {
            .goal => |goal| return self.prove(goal, cell.next),
            .close => |frame| {
                frame.reached = true;
                const node = frame.goal.slot.*.?;
                const gop = try self.proved.getOrPut(self.allocator, frame.goal.expr);
                if (!gop.found_existing or gop.value_ptr.depth > frame.goal.depth) {
                    gop.value_ptr.* = .{ .depth = frame.goal.depth, .node = node };
                }
                return switch (try self.run(cell.next)) {
                    .failed => .{ .cut = frame.id },
                    else => |outcome| outcome,
                };
            },
        }
    }

    /// The agenda is empty: every goal is proved.
    fn finish(self: *Prover) Error!Outcome {
        if (try self.close_out.tryFn(self.close_out.ctx, self.root.?.*.?)) return .proved;
        self.stats.rejects += 1;
        return .failed;
    }

    fn prove(self: *Prover, goal: Goal, next: ?*const Agenda) Error!Outcome {
        try self.charge();
        if (self.failed.get(goal.expr)) |failed_at| {
            if (failed_at >= goal.depth) return .failed;
        }
        if (self.proved.get(goal.expr)) |known| {
            if (known.depth <= goal.depth) {
                goal.slot.* = known.node;
                return self.run(next);
            }
        }
        var on_path = goal.path;
        while (on_path) |cell| : (on_path = cell.next) {
            if (cell.expr == goal.expr) {
                self.prunes += 1;
                return .failed;
            }
        }
        self.stats.nodes += 1;

        var frame = Frame{ .id = self.next_frame, .goal = goal };
        self.next_frame += 1;
        const close = Agenda{ .item = .{ .close = &frame }, .next = next };
        const path = PathCell{ .expr = goal.expr, .next = goal.path };
        const prunes_at_entry = self.prunes;
        switch (try self.expand(&frame, &close, &path)) {
            .proved => return .proved,
            .failed => {},
            .cut => |id| if (id != frame.id) return .{ .cut = id },
        }
        if (!frame.reached and self.prunes == prunes_at_entry) {
            const gop = try self.failed.getOrPut(self.allocator, goal.expr);
            if (!gop.found_existing or gop.value_ptr.* < goal.depth) gop.value_ptr.* = goal.depth;
        }
        return .failed;
    }

    /// Try every alternative for `frame`'s goal until one leads to a proof
    /// or a cut.
    fn expand(self: *Prover, frame: *Frame, close: *const Agenda, path: *const PathCell) Error!Outcome {
        const goal = frame.goal;
        for (self.facts) |fact| {
            if (fact.expr != goal.expr) continue;
            const outcome = try self.apply(frame, .{ .ref = fact.ref }, &.{}, &.{}, 0, close, path);
            if (outcome != .failed) return outcome;
        }
        const head = switch (self.terms.theorem.interner.node(goal.expr).*) {
            .app => |app| app.term_id,
            else => return .failed,
        };
        var any_safe = false;
        for (self.catalog.forHead(head)) |entry| {
            switch (entry.role) {
                .closer => {},
                .safe => if (goal.depth == 0) break,
                .unsafe => if (goal.depth == 0 or any_safe) break,
            }
            const premise_depth = if (entry.role == .unsafe) goal.depth - 1 else goal.depth;
            const options = try self.matches(entry.rule_id, goal.expr);
            for (options) |bindings| {
                if (entry.role == .safe) any_safe = true;
                const rule = &self.context.env.rules.items[entry.rule_id];
                const outcome = try self.apply(
                    frame,
                    .{ .rule = .{ .rule_id = entry.rule_id, .bindings = bindings } },
                    rule.hyps,
                    bindings,
                    premise_depth,
                    close,
                    path,
                );
                if (outcome != .failed) return outcome;
            }
        }
        return .failed;
    }

    /// Every way `rule_id`'s conclusion fits `goal`, as binder values.
    fn matches(self: *Prover, rule_id: u32, goal: ExprId) Error![]const []const ExprId {
        const Collector = struct {
            arena: std.mem.Allocator,
            out: std.ArrayListUnmanaged([]const ExprId) = .empty,

            pub const Error = error{OutOfMemory};

            pub fn match(collector: *@This(), bindings: []const ExprId) error{OutOfMemory}!bool {
                try collector.out.append(collector.arena, try collector.arena.dupe(ExprId, bindings));
                return false;
            }
        };
        var collector = Collector{ .arena = self.arena };
        const rule = &self.context.env.rules.items[rule_id];
        _ = try self.terms.matchConclusion(rule, goal, Collector, &collector);
        return collector.out.items;
    }

    /// Record `step` as the proof of `frame`'s goal and run its premises,
    /// then the rest of the agenda.
    fn apply(
        self: *Prover,
        frame: *Frame,
        step: Step,
        premises: []const TemplateExpr,
        bindings: []const ExprId,
        premise_depth: usize,
        close: *const Agenda,
        path: *const PathCell,
    ) Error!Outcome {
        const children = try self.arena.alloc(?*const Node, premises.len);
        @memset(children, null);
        const node = try self.arena.create(Node);
        node.* = .{ .step = step, .children = children };
        frame.goal.slot.* = node;

        var cells: [catalog_mod.max_premises]Agenda = undefined;
        var head: *const Agenda = close;
        var idx = premises.len;
        while (idx > 0) {
            idx -= 1;
            const expr = self.terms.instantiate(premises[idx], bindings) catch |err| switch (err) {
                error.Unsupported => return .failed,
                else => |e| return e,
            };
            cells[idx] = .{
                .item = .{ .goal = .{
                    .expr = expr,
                    .depth = premise_depth,
                    .slot = &children[idx],
                    .path = path,
                } },
                .next = head,
            };
            head = &cells[idx];
        }
        return self.run(head);
    }
};
