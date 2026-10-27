//! The search core's prover (`docs/design_notes/shared_witness.md` D1, D4):
//! one agenda of open goals, solved most recent first in
//! continuation-passing style, and one proof record.
//!
//! A goal is tried with the pool facts that state it and the closers, then
//! (with depth left) the safe rules, and only when no safe rule applies,
//! the unsafe rules one depth lower. A rule's premises go on the agenda
//! ahead of the goal's close marker; when the run reaches the marker the
//! goal is proved, and the run goes on with the rest of the agenda. Each
//! way of closing a goal is tried with its witness bindings in force, so a
//! later goal sees what an earlier one bound.
//!
//! When the continuation of a proved goal fails, and proving the goal bound
//! or narrowed no witness variable that existed when it was entered, the
//! goal's other alternatives are cut (the W5 prune): they could only bind
//! more. A ground goal that runs out of alternatives without reaching its
//! marker has no proof at its depth, and one proved without binding or
//! introducing anything has a proof at every depth at least its own; both
//! are memoized for the whole run. Goals holding witness variables are not
//! memoized: that needs keys up to renaming of the variables (stage C2).

const std = @import("std");
const ExprId = @import("../../../expr.zig").ExprId;
const ProofScript = @import("../../../proof_script.zig");
const TemplateExpr = @import("../../../rules.zig").TemplateExpr;
const ViewDecl = @import("../../../views.zig").ViewDecl;
const PoolVars = @import("../../vars.zig").PoolVars;
const types = @import("../types.zig");
const Context = types.Context;
const GlobalBudget = types.GlobalBudget;
const NameExprMap = types.NameExprMap;
const catalog_mod = @import("./catalog.zig");
const Catalog = catalog_mod.Catalog;
const terms_mod = @import("./terms.zig");
const Terms = terms_mod.Terms;
const WVars = @import("./wvars.zig").WVars;

pub const Error = terms_mod.Error || error{
    SearchBudgetExhausted,
    SearchStackExhausted,
};
const ProveError = Error;

/// One applied step of the proof record.
pub const Node = struct {
    step: Step,
    /// One slot per premise, filled as the premise is proved.
    children: []?*const Node,
};

pub const Step = union(enum) {
    /// The rule's binder values; witnesses may still be wvars.
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
    /// The goal holds no wvar.
    ground: bool,
    /// The wvar log length, wvar count and step count at entry.
    mark: usize,
    wvars: u32,
    steps: usize,
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
    wvars: *WVars,
    /// Names the `@vars` pools, for eigenvariables.
    theorem_vars: *const NameExprMap,
    catalog: *const Catalog,
    facts: []const Fact,
    budget: ?*GlobalBudget,
    close_out: CloseOut,
    stack_base: usize,
    stack_guard_bytes: usize,
    /// Per ground goal: the greatest depth at which it has no proof.
    failed: std.AutoHashMapUnmanaged(ExprId, usize) = .empty,
    /// Per ground goal: a proof, and the depth it was found at.
    proved: std.AutoHashMapUnmanaged(ExprId, Proved) = .empty,
    /// Each sort's `@vars` pool variables, in pool order.
    pools: std.StringHashMapUnmanaged([]const ExprId) = .empty,
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
        self.pools.deinit(self.allocator);
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
                if (frame.ground and self.wvars.steps == frame.steps) {
                    const gop = try self.proved.getOrPut(self.allocator, frame.goal.expr);
                    if (!gop.found_existing or gop.value_ptr.depth > frame.goal.depth) {
                        gop.value_ptr.* = .{ .depth = frame.goal.depth, .node = frame.goal.slot.*.? };
                    }
                }
                return switch (try self.run(cell.next)) {
                    .failed => if (self.wvars.constrainedOlderSince(frame.mark, frame.wvars))
                        .failed
                    else
                        .{ .cut = frame.id },
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

    fn prove(self: *Prover, raw: Goal, next: ?*const Agenda) Error!Outcome {
        try self.charge();
        var goal = raw;
        goal.expr = try self.terms.resolveGoal(raw.expr);
        const ground = !try self.wvars.holdsWVar(goal.expr);
        if (ground) {
            if (self.failed.get(goal.expr)) |failed_at| {
                if (failed_at >= goal.depth) return .failed;
            }
            if (self.proved.get(goal.expr)) |known| {
                if (known.depth <= goal.depth) {
                    goal.slot.* = known.node;
                    return self.run(next);
                }
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

        var frame = Frame{
            .id = self.next_frame,
            .goal = goal,
            .ground = ground,
            .mark = self.wvars.mark(),
            .wvars = self.wvars.count(),
            .steps = self.wvars.steps,
        };
        self.next_frame += 1;
        const close = Agenda{ .item = .{ .close = &frame }, .next = next };
        const path = PathCell{ .expr = goal.expr, .next = goal.path };
        const prunes_at_entry = self.prunes;
        switch (try self.expand(&frame, &close, &path)) {
            .proved => return .proved,
            .failed => {},
            .cut => |id| if (id != frame.id) return .{ .cut = id },
        }
        if (ground and !frame.reached and self.prunes == prunes_at_entry) {
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
            var applier = Applier{ .prover = self, .frame = frame, .how = .{ .ref = fact.ref }, .close = close, .path = path };
            if (try self.terms.unify(fact.expr, goal.expr, Applier, &applier)) return applier.outcome;
        }
        const head = switch (self.terms.theorem.interner.node(goal.expr).*) {
            .app => |app| app.term_id,
            else => return .failed,
        };
        var any_safe = false;
        for (self.catalog.forHead(head)) |*entry| {
            switch (entry.role) {
                .closer => {},
                .safe => if (goal.depth == 0) break,
                .unsafe => if (goal.depth == 0 or any_safe) break,
            }
            var applier = Applier{
                .prover = self,
                .frame = frame,
                .how = .{ .rule = entry },
                .premise_depth = if (entry.role == .unsafe) goal.depth - 1 else goal.depth,
                .close = close,
                .path = path,
            };
            const rule = &self.context.env.rules.items[entry.rule_id];
            const stopped = try self.terms.matchConclusion(rule, goal.expr, Applier, &applier);
            if (applier.matched and entry.role == .safe) any_safe = true;
            if (stopped) return applier.outcome;
        }
        return .failed;
    }

    /// The matcher's sink: applies each way of closing a goal while its
    /// witness bindings hold, and stops at the first that does not fail.
    const Applier = struct {
        prover: *Prover,
        frame: *Frame,
        how: union(enum) { rule: *const catalog_mod.Rule, ref: ProofScript.Ref },
        premise_depth: usize = 0,
        close: *const Agenda,
        path: *const PathCell,
        /// Some match applied: its witnesses could be filled.
        matched: bool = false,
        outcome: Outcome = .failed,

        pub const Error = ProveError;

        pub fn match(self: *Applier, bindings: []const ?ExprId) ProveError!bool {
            const outcome = try self.prover.apply(self, bindings);
            if (outcome == .failed) return false;
            self.outcome = outcome;
            return true;
        }
    };

    /// Record the applier's step as the proof of its goal, with
    /// `bindings` from the match, and run its premises, then the rest of
    /// the agenda.
    fn apply(self: *Prover, applier: *Applier, bindings: []const ?ExprId) Error!Outcome {
        const start = self.wvars.mark();
        defer self.wvars.rollback(start);
        var step: Step = undefined;
        var premises: []const TemplateExpr = &.{};
        var values: []const ExprId = &.{};
        switch (applier.how) {
            .ref => |ref| step = .{ .ref = ref },
            .rule => |entry| {
                const full = try self.arena.alloc(ExprId, bindings.len);
                for (full, bindings) |*value, binding| value.* = binding orelse undefined;
                premises = entry.premises;
                values = full;
                if (entry.view) |view| {
                    values = (try self.witness(entry, view, full, applier.frame.goal.expr)) orelse return .failed;
                }
                step = .{ .rule = .{ .rule_id = entry.rule_id, .bindings = full } };
            },
        }
        applier.matched = true;

        const frame = applier.frame;
        const children = try self.arena.alloc(?*const Node, premises.len);
        @memset(children, null);
        const node = try self.arena.create(Node);
        node.* = .{ .step = step, .children = children };
        frame.goal.slot.* = node;

        // On the heap: the run stays on the stack for the rest of the proof.
        const cells = try self.allocator.alloc(Agenda, premises.len);
        defer self.allocator.free(cells);
        var head: *const Agenda = applier.close;
        var idx = premises.len;
        while (idx > 0) {
            idx -= 1;
            const expr = self.terms.instantiate(premises[idx], values) catch |err| switch (err) {
                error.Unsupported => return .failed,
                else => |e| return e,
            };
            cells[idx] = .{
                .item = .{ .goal = .{
                    .expr = expr,
                    .depth = applier.premise_depth,
                    .slot = &children[idx],
                    .path = applier.path,
                } },
                .next = head,
            };
            head = &cells[idx];
        }
        return self.run(head);
    }

    /// Fill `entry`'s witnesses in `full` (a fresh wvar for each γ, a fresh
    /// eigenvariable for each δ) and return the view's binder values, or
    /// null when no eigenvariable is fresh for `goal`.
    fn witness(
        self: *Prover,
        entry: *const catalog_mod.Rule,
        view: *const ViewDecl,
        full: []ExprId,
        goal: ExprId,
    ) Error!?[]const ExprId {
        const rule = &self.context.env.rules.items[entry.rule_id];
        const patterns = try self.arena.alloc(ExprId, entry.witnesses.len);
        for (entry.witnesses, patterns) |w, *pattern| {
            pattern.* = try self.wvars.deref(full[w.pattern], null);
            const sort_name = rule.args[w.arg].sort_name;
            switch (w.kind) {
                .gamma => {
                    var capture = std.ArrayListUnmanaged(ExprId).empty;
                    try self.terms.boundVariables(self.arena, pattern.*, &capture);
                    full[w.arg] = try self.wvars.mint(sort_name, capture.items);
                },
                .delta => {
                    full[w.arg] = (try self.eigenvariable(sort_name, goal)) orelse return null;
                    try self.wvars.introduce(full[w.arg]);
                },
            }
        }
        const values = try self.arena.alloc(ExprId, view.num_binders);
        for (view.binder_map, values) |mapped, *value| {
            if (mapped) |arg| value.* = full[arg];
        }
        for (entry.witnesses, patterns) |w, pattern| {
            values[w.source] = try self.terms.swap(pattern, full[w.hole], full[w.arg]);
        }
        return values;
    }

    /// A `@vars` variable of `sort_name` that `goal` does not mention,
    /// preferring one no live introduction holds.
    fn eigenvariable(self: *Prover, sort_name: []const u8, goal: ExprId) Error!?ExprId {
        var reused: ?ExprId = null;
        for (try self.pool(sort_name)) |variable| {
            if (self.wvars.mentions(goal, variable)) continue;
            if (!self.wvars.introduced(variable)) return variable;
            if (reused == null) reused = variable;
        }
        return reused;
    }

    pub fn pool(self: *Prover, sort_name: []const u8) Error![]const ExprId {
        if (self.pools.get(sort_name)) |known| return known;
        var vars = try PoolVars.init(
            self.allocator,
            self.context.sort_vars,
            sort_name,
            self.terms.theorem,
            self.theorem_vars,
        );
        defer vars.deinit();
        var out = std.ArrayListUnmanaged(ExprId).empty;
        while (true) {
            const pool_var = vars.next() catch |err| switch (err) {
                error.OutOfMemory => return error.OutOfMemory,
                else => break,
            } orelse break;
            try out.append(self.arena, pool_var.expr);
        }
        try self.pools.put(self.allocator, sort_name, out.items);
        return out.items;
    }
};
