//! The search core's prover (`docs/design_notes/shared_witness.md` D1, D4):
//! one agenda of open goals, solved most recent first in
//! continuation-passing style, and one proof record.
//!
//! A goal is tried with the pool facts that state it and the closers, then
//! the safe rules, and only when no safe rule applies, the unsafe rules one
//! depth lower (with depth left), those with fewer premises no pool fact
//! might close first. A goal with an `@rewrite` normal form is tried in
//! that form too, and one headed by a definition with the rules for each
//! head its unfoldings reach, at no cost: each is a conversion the checker
//! makes. Safe rules cost no depth, so they apply at depth 0 too. A rule's
//! premises go on the agenda ahead of the goal's close marker; when the run
//! reaches the marker the goal is proved, and the run goes on with the rest
//! of the agenda. Each way of closing a goal is tried with its witness
//! bindings in force, so a later goal sees what an earlier one bound.
//!
//! A cut wvar is chosen by the proof, never invented: a goal that holds
//! one unbound is closed by a pool fact or a closer, or by a rule whose
//! conclusion match binds one of its cut wvars, and no other rule works on
//! it. So a rule's premises that a pool fact might close come first, and
//! an unbound wvar premise waits for a sibling that fixes it.
//!
//! When the continuation of a proved goal fails, and proving the goal bound
//! or narrowed no witness variable that existed when it was entered, the
//! goal's other alternatives are cut (the W5 prune): they could only bind
//! more. Likewise a proof that leaves the older witness variables as an
//! earlier proof of the goal did, whose continuation failed, is skipped
//! (W5 dedupe). A failure that includes a rejected close-out does neither.
//!
//! A goal that runs out of alternatives without reaching its marker has no
//! proof at its depth; a goal proved without binding or narrowing a witness
//! variable older than it has that proof at every depth at least its own,
//! whatever its witness variables later become (W9). Both are memoized for
//! the whole run, under the goal itself when it is ground and under its key
//! up to renaming its witness variables (`keys.zig`) when not. A remembered
//! proof is reused with the goal's witness variables in place of the
//! original's and fresh copies of those the proof introduced.

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
const Keys = @import("./keys.zig").Keys;

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
    /// The number of goals above this one.
    level: usize,
    next: ?*const PathCell,
};

/// A goal being solved. `reached` is set once the run passes its marker.
const Frame = struct {
    id: u32,
    goal: Goal,
    /// The goal holds no wvar.
    ground: bool,
    /// The wvar log length, wvar count and eigenvariable count at entry.
    mark: usize,
    wvars: u32,
    eigens: u32,
    /// The cut wvars the goal holds unbound; owned by the caller of
    /// `expand`.
    cuts: []const u32 = &.{},
    reached: bool = false,
    /// Signatures (`WVars.signature`) of the proofs of the goal whose
    /// continuation failed; owned by the prover's allocator.
    seen: std.StringHashMapUnmanaged(void) = .empty,
    /// For a goal holding wvars, its key and its wvars in key order; owned
    /// by the prover's allocator.
    key: []const u8 = &.{},
    order: []const u32 = &.{},
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

/// A remembered proof (W9): `node` with its bindings resolved, holding the
/// wvars of the goal it proved (`positions`, in key order) and those the
/// proof itself minted or introduced (`internals`, oldest first).
const Proved = struct {
    depth: usize,
    node: *const Node,
    positions: []const u32,
    internals: []const Internal,
};

const Internal = struct {
    wvar: u32,
    /// For an eigenvariable, its introduction goal, resolved.
    introduced_at: ?ExprId,
};

const no_prune = std.math.maxInt(usize);

pub const Prover = struct {
    allocator: std.mem.Allocator,
    /// Owns the proof record; lives for the run.
    arena: std.mem.Allocator,
    context: *const Context,
    terms: *Terms,
    wvars: *WVars,
    keys: *Keys,
    /// Names the `@vars` pools, for close-out.
    theorem_vars: *const NameExprMap,
    catalog: *const Catalog,
    facts: []const Fact,
    budget: ?*GlobalBudget,
    close_out: CloseOut,
    stack_base: usize,
    stack_guard_bytes: usize,
    /// Per ground goal: the greatest depth at which it has no proof.
    failed: std.AutoHashMapUnmanaged(ExprId, usize) = .empty,
    /// The same per key of a goal holding wvars.
    failed_open: std.StringHashMapUnmanaged(usize) = .empty,
    /// Per ground goal: a proof, and the depth it was found at.
    proved: std.AutoHashMapUnmanaged(ExprId, Proved) = .empty,
    /// The same per key of a goal holding wvars.
    proved_open: std.StringHashMapUnmanaged(Proved) = .empty,
    /// Each sort's `@vars` pool variables, in pool order.
    pools: std.StringHashMapUnmanaged([]const ExprId) = .empty,
    next_frame: u32 = 0,
    /// The root goal's slot during `solve`.
    root: ?*const ?*const Node = null,
    /// The lowest path level a pruned path repeat has hit in the current
    /// goal's search so far. A goal that repeats itself or a goal below it
    /// is pruned without loss: a proof of a goal that uses the goal again
    /// contains a smaller proof of it. Only a repeat of a goal above makes
    /// a failure depend on the path, and then it is not memoized.
    prune_floor: usize = no_prune,
    stats: Stats = .{},

    pub fn deinit(self: *Prover) void {
        self.failed.deinit(self.allocator);
        self.failed_open.deinit(self.allocator);
        self.proved.deinit(self.allocator);
        self.proved_open.deinit(self.allocator);
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
                const constrained = self.wvars.constrainedOlderSince(frame.mark, frame.wvars);
                if (!constrained) try self.remember(frame);
                // A proof that left the older wvars as an earlier one did,
                // whose continuation failed, fails the same way (W5 dedupe).
                var sig: ?[]u8 = null;
                defer if (sig) |bytes| self.allocator.free(bytes);
                if (constrained) {
                    var bytes = std.ArrayListUnmanaged(u8).empty;
                    errdefer bytes.deinit(self.allocator);
                    try self.wvars.signature(self.allocator, frame.mark, frame.wvars, frame.eigens, &bytes);
                    sig = try bytes.toOwnedSlice(self.allocator);
                    if (frame.seen.contains(sig.?)) return .failed;
                }
                const rejects = self.stats.rejects;
                const outcome = try self.run(cell.next);
                if (outcome != .failed) return outcome;
                // A rejected close-out may hinge on more than bindings (how
                // many eigenvariables need names), so it neither cuts nor
                // counts as seen.
                if (self.stats.rejects != rejects) return .failed;
                if (!constrained) return .{ .cut = frame.id };
                try frame.seen.put(self.allocator, sig.?, {});
                sig = null;
                return .failed;
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
        const outer_floor = self.prune_floor;
        self.prune_floor = no_prune;
        defer self.prune_floor = @min(outer_floor, self.prune_floor);
        var goal = raw;
        goal.expr = try self.terms.resolveGoal(raw.expr);
        const ground = !try self.wvars.holdsWVar(goal.expr);
        var key: []const u8 = &.{};
        var order: []const u32 = &.{};
        defer self.allocator.free(key);
        defer self.allocator.free(order);
        const known = if (ground) blk: {
            if (self.failed.get(goal.expr)) |failed_at| {
                if (failed_at >= goal.depth) return .failed;
            }
            break :blk self.proved.get(goal.expr);
        } else blk: {
            key = try self.allocator.dupe(u8, try self.keys.key(goal.expr));
            order = try self.allocator.dupe(u32, self.keys.order.items);
            if (self.failed_open.get(key)) |failed_at| {
                if (failed_at >= goal.depth) return .failed;
            }
            break :blk self.proved_open.get(key);
        };
        if (known) |proof| if (proof.depth <= goal.depth) {
            const rejects = self.stats.rejects;
            goal.slot.* = try self.reuse(proof, order);
            const outcome = try self.run(next);
            // As for the W5 prune: the proof bound nothing older, so no
            // other proof can help the continuation.
            if (outcome != .failed or self.stats.rejects == rejects) return outcome;
        };
        var on_path = goal.path;
        while (on_path) |cell| : (on_path = cell.next) {
            if (cell.expr == goal.expr) {
                self.prune_floor = @min(self.prune_floor, cell.level);
                return .failed;
            }
        }
        self.stats.nodes += 1;

        var cuts = std.ArrayListUnmanaged(u32).empty;
        defer cuts.deinit(self.allocator);
        if (!ground) {
            try self.wvars.collectUnbound(self.allocator, goal.expr, &cuts);
            var kept: usize = 0;
            for (cuts.items) |idx| {
                if (!self.wvars.vars.items[idx].cut) continue;
                cuts.items[kept] = idx;
                kept += 1;
            }
            cuts.shrinkRetainingCapacity(kept);
        }
        var frame = Frame{
            .id = self.next_frame,
            .goal = goal,
            .ground = ground,
            .mark = self.wvars.mark(),
            .wvars = self.wvars.count(),
            .eigens = self.wvars.eigen_count,
            .cuts = cuts.items,
            .key = key,
            .order = order,
        };
        defer {
            var it = frame.seen.keyIterator();
            while (it.next()) |sig| self.allocator.free(sig.*);
            frame.seen.deinit(self.allocator);
        }
        self.next_frame += 1;
        const close = Agenda{ .item = .{ .close = &frame }, .next = next };
        const level = if (goal.path) |above| above.level + 1 else 0;
        const path = PathCell{ .expr = goal.expr, .level = level, .next = goal.path };
        switch (try self.expand(&frame, &close, &path)) {
            .proved => return .proved,
            .failed => {},
            .cut => |id| if (id != frame.id) return .{ .cut = id },
        }
        if (!frame.reached and self.prune_floor >= level) {
            // Every binding made below is undone, so the key is the
            // entry's again.
            const failed_at = if (ground) blk: {
                const gop = try self.failed.getOrPut(self.allocator, goal.expr);
                if (!gop.found_existing) gop.value_ptr.* = 0;
                break :blk gop.value_ptr;
            } else blk: {
                const gop = try self.failed_open.getOrPut(self.allocator, key);
                if (!gop.found_existing) {
                    gop.key_ptr.* = try self.arena.dupe(u8, gop.key_ptr.*);
                    gop.value_ptr.* = 0;
                }
                break :blk gop.value_ptr;
            };
            failed_at.* = @max(failed_at.*, goal.depth);
        }
        return .failed;
    }

    /// Remember the proof of `frame`'s goal just reached (W9), unless one at
    /// the same or a smaller depth is known.
    fn remember(self: *Prover, frame: *const Frame) Error!void {
        const depth = frame.goal.depth;
        if (frame.ground) {
            if (self.proved.get(frame.goal.expr)) |known| if (known.depth <= depth) return;
        } else if (self.proved_open.get(frame.key)) |known| if (known.depth <= depth) return;

        var leftovers = std.ArrayListUnmanaged(u32).empty;
        defer leftovers.deinit(self.allocator);
        const node = try self.resolveNode(frame.goal.slot.*.?, &leftovers);
        std.mem.sort(u32, leftovers.items, {}, std.sort.asc(u32));
        var internals = std.ArrayListUnmanaged(Internal).empty;
        for (leftovers.items) |idx| {
            if (idx < frame.wvars) {
                // An older wvar the goal does not hold: nothing to map it to.
                if (std.mem.indexOfScalar(u32, frame.order, idx) == null) return;
                continue;
            }
            const at = self.wvars.vars.items[idx].introduced_at;
            try internals.append(self.arena, .{
                .wvar = idx,
                .introduced_at = if (at) |goal| try self.wvars.deref(goal, null) else null,
            });
        }
        const proof = Proved{
            .depth = depth,
            .node = node,
            .positions = try self.arena.dupe(u32, frame.order),
            .internals = internals.items,
        };
        if (frame.ground) {
            try self.proved.put(self.allocator, frame.goal.expr, proof);
        } else {
            const gop = try self.proved_open.getOrPut(self.allocator, frame.key);
            if (!gop.found_existing) gop.key_ptr.* = try self.arena.dupe(u8, frame.key);
            gop.value_ptr.* = proof;
        }
    }

    /// A copy of `node` with every binding resolved; the unbound wvars it
    /// holds go to `leftovers`.
    fn resolveNode(self: *Prover, node: *const Node, leftovers: *std.ArrayListUnmanaged(u32)) Error!*const Node {
        const copy = try self.arena.create(Node);
        const children = try self.arena.alloc(?*const Node, node.children.len);
        for (children, node.children) |*out, child| out.* = try self.resolveNode(child.?, leftovers);
        copy.* = .{ .step = node.step, .children = children };
        switch (node.step) {
            .ref => {},
            .rule => |step| {
                const bindings = try self.arena.alloc(ExprId, step.bindings.len);
                for (bindings, step.bindings) |*out, value| {
                    out.* = try self.wvars.deref(value, null);
                    try self.wvars.collectUnbound(self.allocator, out.*, leftovers);
                }
                copy.step = .{ .rule = .{ .rule_id = step.rule_id, .bindings = bindings } };
            },
        }
        return copy;
    }

    /// `proof` for the goal whose wvars in key order are `order`: its goal's
    /// wvars replaced by those, and its own by fresh ones minted or
    /// introduced now, so each is younger than every wvar the goal holds.
    fn reuse(self: *Prover, proof: Proved, order: []const u32) Error!*const Node {
        if (proof.positions.len == 0 and proof.internals.len == 0) return proof.node;
        var map = std.AutoHashMapUnmanaged(u32, ExprId).empty;
        defer map.deinit(self.allocator);
        for (proof.positions, order) |old, new| try map.put(self.allocator, old, self.wvars.vars.items[new].expr);
        for (proof.internals) |internal| {
            const wvar = self.wvars.vars.items[internal.wvar];
            const fresh = if (internal.introduced_at) |at|
                try self.wvars.introduce(wvar.sort_name, at)
            else
                try self.wvars.mint(wvar.sort_name, wvar.capture, wvar.cut);
            try map.put(self.allocator, internal.wvar, fresh);
        }
        var memo = std.AutoHashMapUnmanaged(ExprId, ExprId).empty;
        defer memo.deinit(self.allocator);
        // An introduction goal may hold eigenvariables introduced after it
        // (an unfolding holds all its dummies), so it is renamed once every
        // copy exists.
        for (proof.internals) |internal| {
            const at = internal.introduced_at orelse continue;
            const copy = self.wvars.of(map.get(internal.wvar).?).?;
            self.wvars.vars.items[copy].introduced_at = try self.rename(at, &map, &memo);
        }
        return self.renameNode(proof.node, &map, &memo);
    }

    fn renameNode(
        self: *Prover,
        node: *const Node,
        map: *const std.AutoHashMapUnmanaged(u32, ExprId),
        memo: *std.AutoHashMapUnmanaged(ExprId, ExprId),
    ) Error!*const Node {
        const copy = try self.arena.create(Node);
        const children = try self.arena.alloc(?*const Node, node.children.len);
        for (children, node.children) |*out, child| out.* = try self.renameNode(child.?, map, memo);
        copy.* = .{ .step = node.step, .children = children };
        switch (node.step) {
            .ref => {},
            .rule => |step| {
                const bindings = try self.arena.alloc(ExprId, step.bindings.len);
                for (bindings, step.bindings) |*out, value| out.* = try self.rename(value, map, memo);
                copy.step = .{ .rule = .{ .rule_id = step.rule_id, .bindings = bindings } };
            },
        }
        return copy;
    }

    /// `expr` with each wvar leaf `map` names replaced.
    fn rename(
        self: *Prover,
        expr: ExprId,
        map: *const std.AutoHashMapUnmanaged(u32, ExprId),
        memo: *std.AutoHashMapUnmanaged(ExprId, ExprId),
    ) Error!ExprId {
        if (!try self.wvars.holdsWVar(expr)) return expr;
        if (memo.get(expr)) |done| return done;
        const interner = &self.terms.theorem.interner;
        const result = switch (interner.node(expr).*) {
            .variable => expr,
            .placeholder => map.get(self.wvars.of(expr).?) orelse expr,
            .app => |app| blk: {
                const args = try self.allocator.alloc(ExprId, app.args.len);
                defer self.allocator.free(args);
                for (app.args, args) |arg, *out| out.* = try self.rename(arg, map, memo);
                break :blk interner.internApp(app.term_id, args) catch |err| switch (err) {
                    error.OutOfMemory => return error.OutOfMemory,
                    else => return error.TooManyTheoremExprs,
                };
            },
        };
        try memo.put(self.allocator, expr, result);
        return result;
    }

    /// Try every alternative for `frame`'s goal until one leads to a proof
    /// or a cut.
    fn expand(self: *Prover, frame: *Frame, close: *const Agenda, path: *const PathCell) Error!Outcome {
        const goal = frame.goal;
        // The goal, its normal form and the unfoldings of the last, each
        // tried with the rules for its head: each is a conversion, which
        // the checker makes. Facts meet the goal and its normal form, and
        // unification unfolds definitions itself.
        var targets = std.ArrayListUnmanaged(ExprId).empty;
        defer targets.deinit(self.allocator);
        try targets.append(self.allocator, goal.expr);
        if (try self.terms.normalForm(goal.expr)) |normal| try targets.append(self.allocator, normal);
        for (targets.items) |target| {
            for (self.facts) |fact| {
                var applier = Applier{
                    .prover = self,
                    .frame = frame,
                    .target = target,
                    .how = .{ .ref = fact.ref },
                    .close = close,
                    .path = path,
                };
                if (try self.terms.unify(fact.expr, target, Applier, &applier)) return applier.outcome;
            }
        }
        while (try self.terms.unfold(targets.getLast())) |unfolded| try targets.append(self.allocator, unfolded);
        const goal_sort = self.wvars.sortOf(goal.expr);
        var any_safe = false;
        // Unsafe alternatives are tried after the closers and safe rules,
        // those whose premises the pool facts might close first.
        var alts = std.ArrayListUnmanaged(Alt).empty;
        defer alts.deinit(self.allocator);
        for (targets.items, 0..) |target, at| {
            const by_head = if (self.terms.headOf(target)) |head| self.catalog.forHead(head) else &.{};
            // A bare-binder conclusion matches the goal as it stands.
            const bare = if (at == 0) self.catalog.forHead(catalog_mod.bare_head) else &.{};
            for ([_][]const catalog_mod.Rule{ by_head, bare }) |rules| {
                for (rules) |*entry| {
                    switch (entry.role) {
                        .closer => {},
                        .safe => {},
                        .unsafe => if (goal.depth == 0 or any_safe) break,
                    }
                    const rule = &self.context.env.rules.items[entry.rule_id];
                    // A bare-binder conclusion matches only goals of its sort.
                    switch (rule.concl) {
                        .app => {},
                        .binder => |idx| if (!std.mem.eql(u8, rule.args[idx].sort_name, goal_sort orelse break)) continue,
                    }
                    if (entry.role == .unsafe) {
                        var scorer = Scorer{ .prover = self, .entry = entry, .target = target, .alts = &alts };
                        _ = try self.terms.matchConclusion(rule, target, Scorer, &scorer);
                        continue;
                    }
                    var applier = Applier{
                        .prover = self,
                        .frame = frame,
                        .target = target,
                        .how = .{ .rule = entry },
                        .premise_depth = goal.depth,
                        .close = close,
                        .path = path,
                    };
                    const stopped = try self.terms.matchConclusion(rule, target, Applier, &applier);
                    if (applier.matched and entry.role == .safe) any_safe = true;
                    if (stopped) return applier.outcome;
                }
            }
        }
        if (any_safe) return .failed;
        std.mem.sort(Alt, alts.items, {}, Alt.lessThan);
        for (alts.items) |alt| {
            var picker = Picker{
                .target = alt.index,
                .applier = .{
                    .prover = self,
                    .frame = frame,
                    .target = alt.target,
                    .how = .{ .rule = alt.entry },
                    .premise_depth = goal.depth - 1,
                    .close = close,
                    .path = path,
                },
            };
            const rule = &self.context.env.rules.items[alt.entry.rule_id];
            if (try self.terms.matchConclusion(rule, alt.target, Picker, &picker)) return picker.applier.outcome;
        }
        return .failed;
    }

    /// One way an unsafe rule's conclusion matches a goal: the `index`th
    /// match and how many of its premises no pool fact might close. The
    /// rule's declaration order breaks ties.
    const Alt = struct {
        entry: *const catalog_mod.Rule,
        /// The goal or unfolding of it the rule matched.
        target: ExprId,
        index: usize,
        open: usize,

        fn lessThan(_: void, lhs: Alt, rhs: Alt) bool {
            if (lhs.open != rhs.open) return lhs.open < rhs.open;
            if (lhs.entry.rule_id != rhs.entry.rule_id) return lhs.entry.rule_id < rhs.entry.rule_id;
            return lhs.index < rhs.index;
        }
    };

    /// The matcher's sink that lists an unsafe rule's matches as `Alt`s.
    const Scorer = struct {
        prover: *Prover,
        entry: *const catalog_mod.Rule,
        target: ExprId,
        alts: *std.ArrayListUnmanaged(Alt),
        index: usize = 0,

        pub const Error = ProveError;

        pub fn match(self: *Scorer, bindings: []const ?ExprId) ProveError!bool {
            const prover = self.prover;
            const rule = &prover.context.env.rules.items[self.entry.rule_id];
            var open: usize = 0;
            for (rule.hyps) |hyp| {
                // A premise the match leaves unfixed takes any fact: a guess.
                if (hyp == .binder and bindings[hyp.binder] == null) {
                    open += 1;
                    continue;
                }
                for (prover.facts) |fact| {
                    if (prover.terms.mightFit(hyp, bindings, fact.expr)) break;
                } else open += 1;
            }
            try self.alts.append(prover.allocator, .{
                .entry = self.entry,
                .target = self.target,
                .index = self.index,
                .open = open,
            });
            self.index += 1;
            return false;
        }
    };

    /// The matcher's sink that applies only the `target`th match.
    const Picker = struct {
        target: usize,
        index: usize = 0,
        applier: Applier,

        pub const Error = ProveError;

        pub fn match(self: *Picker, bindings: []const ?ExprId) ProveError!bool {
            defer self.index += 1;
            if (self.index != self.target) return false;
            return self.applier.match(bindings);
        }
    };

    /// The matcher's sink: applies each way of closing a goal while its
    /// witness bindings hold, and stops at the first that does not fail.
    const Applier = struct {
        prover: *Prover,
        frame: *Frame,
        /// The frame's goal, or the conversion of it the step proves.
        target: ExprId,
        how: union(enum) { rule: *const catalog_mod.Rule, ref: ProofScript.Ref },
        premise_depth: usize = 0,
        close: *const Agenda,
        path: *const PathCell,
        /// Some match applied.
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
                if (entry.role != .closer and !self.bindsCut(applier.frame.cuts)) return .failed;
                const full = try self.arena.alloc(ExprId, bindings.len);
                for (full, bindings) |*value, binding| value.* = binding orelse undefined;
                premises = entry.premises;
                values = full;
                if (entry.view) |view| values = try self.witness(entry, view, full, applier.target);
                if (entry.cuts.len != 0) try self.cut(entry, full, applier.target);
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
        const exprs = try self.allocator.alloc(ExprId, premises.len);
        defer self.allocator.free(exprs);
        for (exprs, premises) |*expr, premise| {
            expr.* = self.terms.instantiate(premise, values) catch |err| switch (err) {
                error.Unsupported => return .failed,
                else => |e| return e,
            };
        }
        const order = try self.allocator.alloc(usize, premises.len);
        defer self.allocator.free(order);
        try self.orderPremises(exprs, order);
        const cells = try self.allocator.alloc(Agenda, premises.len);
        defer self.allocator.free(cells);
        var head: *const Agenda = applier.close;
        var at = premises.len;
        while (at > 0) {
            at -= 1;
            const idx = order[at];
            cells[at] = .{
                .item = .{ .goal = .{
                    .expr = exprs[idx],
                    .depth = applier.premise_depth,
                    .slot = &children[idx],
                    .path = applier.path,
                } },
                .next = head,
            };
            head = &cells[at];
        }
        return self.run(head);
    }

    /// The order to prove the premises `exprs` in, as indices into `order`.
    /// Those a pool fact might close go first: closing them binds the cut
    /// wvars the others share. A premise that is an unbound wvar goes last
    /// when such a sibling holds it, since any fact fits the wvar: closing
    /// it first only guesses what the sibling fixes.
    fn orderPremises(self: *Prover, exprs: []const ExprId, order: []usize) Error!void {
        const ranks = try self.allocator.alloc(u2, exprs.len);
        defer self.allocator.free(ranks);
        for (ranks, exprs) |*rank, expr| {
            rank.* = for (self.facts) |fact| {
                if (self.terms.mightEqual(fact.expr, expr)) break 0;
            } else 1;
        }
        var held = std.ArrayListUnmanaged(u32).empty;
        defer held.deinit(self.allocator);
        for (ranks, exprs, 0..) |*rank, expr, idx| {
            const wvar = self.wvars.of(self.wvars.resolve(expr)) orelse continue;
            for (exprs, ranks, 0..) |sibling, sibling_rank, sibling_idx| {
                if (sibling_idx == idx or sibling_rank != 0) continue;
                if (self.wvars.of(self.wvars.resolve(sibling)) != null) continue;
                held.clearRetainingCapacity();
                try self.wvars.collectUnbound(self.allocator, sibling, &held);
                if (std.mem.indexOfScalar(u32, held.items, wvar) != null) {
                    rank.* = 2;
                    break;
                }
            }
        }
        var placed: usize = 0;
        for (0..3) |pass| for (ranks, 0..) |rank, idx| {
            if (rank != pass) continue;
            order[placed] = idx;
            placed += 1;
        };
    }

    /// Fill `entry`'s witnesses in `full` (a fresh wvar for each γ, an
    /// eigenvariable introduced at `goal` for each δ) and return the view's
    /// binder values.
    fn witness(
        self: *Prover,
        entry: *const catalog_mod.Rule,
        view: *const ViewDecl,
        full: []ExprId,
        goal: ExprId,
    ) Error![]const ExprId {
        const rule = &self.context.env.rules.items[entry.rule_id];
        const patterns = try self.arena.alloc(ExprId, entry.witnesses.len);
        for (entry.witnesses, patterns) |w, *pattern| {
            pattern.* = try self.wvars.deref(full[w.pattern], null);
            const sort_name = rule.args[w.arg].sort_name;
            switch (w.kind) {
                .gamma => {
                    var capture = std.ArrayListUnmanaged(ExprId).empty;
                    try self.terms.boundVariables(self.arena, pattern.*, &capture);
                    full[w.arg] = try self.wvars.mint(sort_name, capture.items, false);
                },
                .delta => full[w.arg] = try self.wvars.introduce(sort_name, goal),
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

    /// Whether a goal whose unbound cut wvars were `cuts` has none, or the
    /// match just made binds one.
    fn bindsCut(self: *const Prover, cuts: []const u32) bool {
        for (cuts) |idx| {
            if (self.wvars.vars.items[idx].value != null) return true;
        }
        return cuts.len == 0;
    }

    /// Fill `entry`'s cuts in `full`: a fresh wvar for each γ, an
    /// eigenvariable introduced at `goal` for each δ. A γ cut that depends
    /// on no δ one is minted before them, so it cannot hold one; nor may it
    /// hold the variable of a bound binder of the conclusion it does not
    /// depend on.
    fn cut(self: *Prover, entry: *const catalog_mod.Rule, full: []ExprId, goal: ExprId) Error!void {
        const args = self.context.env.rules.items[entry.rule_id].args;
        var cut_mask: u64 = 0;
        var delta_deps: u64 = 0;
        for (entry.cuts) |c| {
            cut_mask |= @as(u64, 1) << @intCast(c.arg);
            if (c.kind == .delta) delta_deps |= args[c.arg].deps;
        }
        for (0..3) |pass| for (entry.cuts) |c| {
            const arg = args[c.arg];
            const stage: usize = switch (c.kind) {
                .gamma => if (arg.deps & delta_deps == 0) 0 else 2,
                .delta => 1,
            };
            if (stage != pass) continue;
            full[c.arg] = switch (c.kind) {
                .gamma => blk: {
                    var capture = std.ArrayListUnmanaged(ExprId).empty;
                    for (args, full, 0..) |other, value, idx| {
                        if (!other.bound or (cut_mask >> @intCast(idx)) & 1 != 0) continue;
                        if (arg.deps & other.deps != 0) continue;
                        const variable = try self.wvars.deref(value, null);
                        if (self.terms.theorem.interner.node(variable).* != .variable) continue;
                        try capture.append(self.arena, variable);
                    }
                    break :blk try self.wvars.mint(arg.sort_name, capture.items, true);
                },
                .delta => try self.wvars.introduce(arg.sort_name, goal),
            };
        };
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
