//! The search core's prover (`docs/design_notes/shared_witness.md` D1, D4):
//! one agenda of open goals, solved most recent first in
//! continuation-passing style, and one proof record.
//!
//! A goal is tried with the facts that state it and the closers, then
//! the safe rules, and only when no safe rule applies, the unsafe rules one
//! depth lower (with depth left), those with fewer premises no fact
//! might close first. A goal with an `@rewrite` normal form is tried in
//! that form too, and one headed by a definition with the rules for each
//! head its unfoldings reach, at no cost: each is a conversion the checker
//! makes. Safe rules cost no depth, so they apply at depth 0 too. A rule's
//! premises go on the agenda ahead of the goal's close marker; when the run
//! reaches the marker the goal is proved, and the run goes on with the rest
//! of the agenda. Each way of closing a goal is tried with its witness
//! bindings in force, so a later goal sees what an earlier one bound.
//!
//! A rule whose conclusion bag has several rest binders splits the goal's
//! context between its premises (`Split`): each such binder is a share, a
//! wvar a fact may bind to the part of the context it needs. A goal that
//! still holds a share when its rules come up binds it first, to what the
//! other shares leave of the context or to the whole context, and once the
//! premises are proved the shares must make up the context again, a member
//! holding a wvar counting as any it unifies with. A share a step binds
//! must hold only members of its context from then on.
//!
//! A conclusion node the match postponed with binders it left unbound
//! (`Terms.postponed`) is checked once the premises are proved and have
//! bound those cuts: instantiated, in normal form, it must unify with the
//! goal node it stood against. An instance whose wvars keep it from a
//! normal form (`[x/?t] φ` with `?t` still open) first meets the goal in
//! the normal form with those wvars as stand-ins (`Terms.openNormalForm`),
//! which binds what the goal fixes; then its own normal form must meet the
//! goal, or, where a wvar is still open, the wvar keeps out of the
//! instance's bound variables as its stand-in did.
//!
//! A cut wvar is chosen by the proof: a goal that holds one unbound is
//! closed by a fact or a closer, or by a rule whose conclusion match binds
//! one of its cut wvars or leaves a postponed node over a part of the goal
//! holding one, which the node's check binds. Any other rule without cuts
//! of its own passes the goal's cut wvars on to its premises
//! (`Goal.pass`): each premise holding one is closed by facts only, and
//! none may be the bare wvar, which any fact closes. The step then reads
//! the cut's value off a fact one rule away, as a bridge does; a cut rule
//! never passes one on, which would stack one guess on another. A
//! narrowing that leaves binders of its node unbound gives each a cut
//! wvar of its own (`Terms.invented`) when the rule is unsafe, a premise
//! mentions the binder and the node holds a binder the match bound; the
//! step passes those on too. A narrowing of a hole gives hole wvars
//! instead, which it does not pass on: rules fix them as they fix the hole
//! (`wvars.zig`). So a rule's premises that a fact might close come first, and
//! an unbound wvar premise waits for a sibling that fixes it. When no fact
//! closes that sibling, a lone such premise is still closed by a fact
//! first, which guesses the wvar from the facts; two or more wait, since
//! their guesses would multiply (`mp2`'s `a`, `b` behind `a → b → c`).
//! When the premise that went first fails, another holding its cut wvars
//! goes first in its stead: one a fact might close and holding one of
//! them, or one no fact might close and holding all of them, which a rule
//! may fix where the first only guessed.
//!
//! A bridge's premises are closed by facts only, never by a rule: the
//! step costs no depth, and `weak`'s premise, with a fresh share for the
//! part of the context it keeps, is a new goal each time, so a premise
//! open to rules could take the bridge again without end. A fact that
//! states the bridge's goal itself is skipped, since it closes that goal
//! directly, and a step whose premise no fact might close is not taken.
//! A premise that no fact closes has failed only as a bridge's, so it is
//! not memoized; neither is a premise a passing step left to facts.
//!
//! A step by a rule whose view abstracts a binder (`catalog.Abstraction`)
//! reads that binder off the view's two sides once its premises are
//! proved, before the goal's close marker. The walk's sides and plugs
//! must be fixed by then, so the step fails as soon as one holds a wvar
//! that none of its premises still to come holds.
//!
//! When the continuation of a proved goal fails, and proving the goal bound
//! or narrowed no witness variable that existed when it was entered, the
//! goal's other alternatives are cut (the W5 prune): they could only bind
//! more. Likewise a proof that leaves the older witness variables as an
//! earlier proof of the goal did, whose continuation failed, is skipped
//! (W5 dedupe). A failure that includes a rejected close-out does neither.
//!
//! A step whose bound binder is fixed to an eigenvariable bars it from the
//! step's other arguments that do not depend on the binder
//! (`WVars.bar`), so no later merge, binding or name breaks MM0's condition
//! for that step. A bar does not count as constraining the eigenvariable
//! for the W5 prune or W9: a proof that bars an older one is remembered,
//! and its bars are applied again where it is reused. This leaves a gap:
//! when a continuation fails only because a bar refused something, the
//! W5 prune still skips the goal's other proofs, one of which might not
//! have barred. The corpus shows no case of it; counting bars closes it at
//! a large cost in re-search.
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
const Rules = @import("../../../rules.zig");
const ArgInfo = @import("../../../parse_recovery.zig").ArgInfo;
const TemplateExpr = Rules.TemplateExpr;
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
const term_index = @import("./term_index.zig");
const TermIndex = term_index.TermIndex;
const AcuiBag = @import("../../../acui_bag.zig");
const DerivedBindings = @import("../../../derived_bindings.zig");
const AbstractDecl = DerivedBindings.AbstractDecl;

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
    /// A fact that states the goal.
    ref: ProofScript.Ref,
};

/// A pool ref, or the recipe of a fact forward saturation derived, and
/// the canonical expression it states.
pub const Fact = struct {
    expr: ExprId,
    ref: ProofScript.Ref,
    shape: terms_mod.Shape,
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
    /// For a bridge's premise, the bridge's goal: only a fact closes the
    /// premise, and not one that states that goal, which closes it directly.
    bridged: ?ExprId = null,
    /// For a premise of a step that left the goal's cut wvars `pass`
    /// unbound: while it holds one unbound, only a fact closes it.
    pass: []const u32 = &.{},
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
        /// The premises of the rule that made `split` are proved.
        settle: *const Split,
        check: *const Check,
        abstract: *const Abstract,
        /// Some of an abstraction's premises are proved.
        ready: *const Ready,
        close: *Frame,
    },
    next: ?*const Agenda,
};

/// The shares of one rule application (`catalog.Rule.shares`), which split
/// the members of a goal bag between the premises. A share is a wvar that
/// a fact may bind to a part of the bag; a goal that still holds one when
/// rules come to it binds it first (`expand`).
const Split = struct {
    shares: []const u32,
    bag: terms_mod.SplitBag,
    /// The split whose premises were being proved when this one was made.
    outer: ?*const Split,
};

/// A postponed conclusion node (`terms_mod.Postponed`) to check once a
/// step's premises are proved: `template` with the step's binder values
/// against the goal node `goal`.
const Check = struct {
    template: TemplateExpr,
    values: []const ExprId,
    goal: ExprId,
};

/// A step by an abstraction (`catalog.Abstraction`), whose target is read
/// off once its premises are proved: the view's binder values, the hole an
/// eigenvariable and the target a wvar.
const Abstract = struct {
    abstraction: *const catalog_mod.Abstraction,
    values: []const ExprId,
};

/// The view binders an abstraction's walk reads: its two sides, then its
/// two plugs.
fn abstractInputs(decl: AbstractDecl) [4]usize {
    return .{ decl.left_view_idx, decl.right_view_idx, decl.left_plug.template.binder, decl.right_plug.template.binder };
}

/// An abstraction step whose premises `rest` are still to be proved.
const Ready = struct {
    abstract: *const Abstract,
    rest: []const ExprId,
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
    /// For an eigenvariable, its introduction goal and the arguments it
    /// may not occur in, resolved.
    introduced_at: ?ExprId,
    fresh_in: ?[]const ExprId,
    name: bool,
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
    /// Over `facts`, in order.
    fact_index: *const TermIndex,
    /// For a query of `fact_index` whose loop starts no other query.
    fact_scratch: []u64,
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
    /// The innermost split whose premises are being proved.
    splits: ?*const Split = null,
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
            .settle => |split| return self.settle(split, cell.next),
            .check => |check_cell| return self.check(check_cell, cell.next),
            .abstract => |made| return self.abstractTarget(made, cell.next),
            .ready => |ready| {
                const made = ready.abstract;
                if (!try self.inputsFixed(made.abstraction.decl, made.values, ready.rest)) return .failed;
                return self.run(cell.next);
            },
            .close => |frame| {
                frame.reached = true;
                // Bars do not count: a proof that only barred older
                // eigenvariables is reused with its bars (`reuse`).
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
        var cuts = std.ArrayListUnmanaged(u32).empty;
        defer cuts.deinit(self.allocator);
        // Whether the goal can fail for reasons outside it: the shares it
        // holds take their values from the rest of their split.
        var shared = false;
        if (!ground) {
            try self.wvars.collectUnbound(self.allocator, goal.expr, &cuts);
            var kept: usize = 0;
            for (cuts.items) |idx| {
                if (self.splitOf(idx) != null) shared = true;
                if (!self.wvars.vars.items[idx].cut) continue;
                cuts.items[kept] = idx;
                kept += 1;
            }
            cuts.shrinkRetainingCapacity(kept);
        }
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
            if (!shared) if (self.failed_open.get(key)) |failed_at| {
                if (failed_at >= goal.depth) return .failed;
            };
            break :blk self.proved_open.get(key);
        };
        if (known) |proof| if (proof.depth <= goal.depth) reused: {
            const rejects = self.stats.rejects;
            const mark = self.wvars.mark();
            defer self.wvars.rollback(mark);
            goal.slot.* = (try self.reuse(proof, order)) orelse break :reused;
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
        // A goal only facts may close (a bridge's or a passing step's
        // premise) has not failed as the same goal closed by rules would.
        if (!frame.reached and !shared and goal.bridged == null and goal.pass.len == 0 and self.prune_floor >= level) {
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
            const wvar = self.wvars.vars.items[idx];
            var fresh_in: ?[]const ExprId = null;
            if (wvar.fresh_in) |exprs| {
                const resolved = try self.arena.alloc(ExprId, exprs.len);
                for (resolved, exprs) |*out, expr| out.* = try self.wvars.deref(expr, null);
                fresh_in = resolved;
            }
            try internals.append(self.arena, .{
                .wvar = idx,
                .introduced_at = if (wvar.introduced_at) |goal| try self.wvars.deref(goal, null) else null,
                .fresh_in = fresh_in,
                .name = wvar.name,
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
    /// The goal's eigenvariables are barred as the proof's steps barred the
    /// original's (`freshBound`); null when one now occurs where it is
    /// barred.
    fn reuse(self: *Prover, proof: Proved, order: []const u32) Error!?*const Node {
        if (proof.positions.len == 0 and proof.internals.len == 0) return proof.node;
        var map = std.AutoHashMapUnmanaged(u32, ExprId).empty;
        defer map.deinit(self.allocator);
        for (proof.positions, order) |old, new| try map.put(self.allocator, old, self.wvars.vars.items[new].expr);
        for (proof.internals) |internal| {
            const wvar = self.wvars.vars.items[internal.wvar];
            const fresh = if (internal.name)
                try self.wvars.introduceName(wvar.sort_name)
            else if (internal.introduced_at) |at|
                try self.wvars.introduce(wvar.sort_name, at, null)
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
            const copy = &self.wvars.vars.items[self.wvars.of(map.get(internal.wvar).?).?];
            copy.introduced_at = try self.rename(at, &map, &memo);
            if (internal.fresh_in) |exprs| {
                const renamed = try self.arena.alloc(ExprId, exprs.len);
                for (renamed, exprs) |*out, expr| out.* = try self.rename(expr, &map, &memo);
                copy.fresh_in = renamed;
            }
        }
        const node = try self.renameNode(proof.node, &map, &memo);
        return if (try self.rebar(node, order)) node else null;
    }

    /// Bar each eigenvariable of `order` that a bound binder of a step of
    /// `node`'s proof holds, as `freshBound` did when the step was made.
    fn rebar(self: *Prover, node: *const Node, order: []const u32) Error!bool {
        switch (node.step) {
            .ref => {},
            .rule => |step| {
                const args = self.context.env.rules.items[step.rule_id].args;
                for (args, step.bindings, 0..) |arg, value, idx| {
                    if (!arg.bound) continue;
                    const wvar = self.wvars.of(self.wvars.resolve(value)) orelse continue;
                    if (!self.wvars.isEigen(wvar) or std.mem.indexOfScalar(u32, order, wvar) == null) continue;
                    if (!try self.barFrom(args, step.bindings, idx, wvar)) return false;
                }
            },
        }
        for (node.children) |child| {
            if (!try self.rebar(child.?, order)) return false;
        }
        return true;
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
        // Facts meet the goal and its normal form, and unification unfolds
        // definitions itself.
        var targets = std.ArrayListUnmanaged(ExprId).empty;
        defer targets.deinit(self.allocator);
        try targets.append(self.allocator, goal.expr);
        if (try self.terms.normalForm(goal.expr)) |normal| try targets.append(self.allocator, normal);
        const scratch = try self.allocator.alloc(u64, self.fact_index.scratchLen());
        defer self.allocator.free(scratch);
        for (targets.items) |target| {
            const screen = try self.terms.screen(target);
            var picks = self.fact_index.query(self.terms, target, scratch);
            while (picks.next()) |n| {
                const fact = self.facts[n];
                if (try self.terms.excludes(screen, fact.expr, fact.shape)) continue;
                if (goal.bridged) |bridged| if (try self.states(fact.expr, bridged)) continue;
                var applier = Applier{
                    .prover = self,
                    .frame = frame,
                    .target = target,
                    .how = .{ .ref = fact.ref },
                    .close = close,
                    .path = path,
                };
                if (try self.terms.unifyScreened(fact.expr, target, Applier, &applier)) return applier.outcome;
            }
        }
        if (goal.bridged != null) return .failed;
        // While it holds a cut its step passed on, only a fact closes it.
        if (goal.pass.len != 0) {
            var open = std.ArrayListUnmanaged(u32).empty;
            defer open.deinit(self.allocator);
            try self.wvars.collectUnbound(self.allocator, goal.expr, &open);
            for (open.items) |idx| if (std.mem.indexOfScalar(u32, goal.pass, idx) != null) return .failed;
        }
        var held = std.ArrayListUnmanaged(u32).empty;
        defer held.deinit(self.allocator);
        const split = try self.heldShares(goal.expr, &held) orelse return self.expandRules(frame, goal.expr, close, path);
        // The rules see the goal with its shares bound: to what the other
        // shares leave of the bag, or to the whole bag.
        const rest = try self.remainder(split);
        const whole = try split.bag.combiner.build(self.terms.theorem, split.bag.members);
        for ([_]?ExprId{ rest, if (whole == rest) null else whole }) |candidate| {
            const value = candidate orelse continue;
            const start = self.wvars.mark();
            defer self.wvars.rollback(start);
            for (held.items) |idx| {
                if (!try self.wvars.bind(idx, value)) break;
            } else {
                const outcome = try self.expandRules(frame, try self.terms.resolveGoal(goal.expr), close, path);
                if (outcome != .failed) return outcome;
            }
        }
        return .failed;
    }

    /// A head's rules, or the ones its index picks for a goal, in
    /// catalog order.
    const Picked = struct {
        rules: []const catalog_mod.Rule,
        picks: ?term_index.Picks = null,
        n: usize = 0,

        fn next(self: *Picked) ?*const catalog_mod.Rule {
            if (self.picks) |*picks| return &self.rules[picks.next() orelse return null];
            if (self.n == self.rules.len) return null;
            self.n += 1;
            return &self.rules[self.n - 1];
        }
    };

    /// Whether some fact might equal `expr` (`Terms.mightEqual`).
    fn factMightEqual(self: *Prover, expr: ExprId) Error!bool {
        var picks = self.fact_index.query(self.terms, expr, self.fact_scratch);
        while (picks.next()) |n| {
            if (try self.terms.mightEqual(self.facts[n].expr, expr, .unfolding)) return true;
        }
        return false;
    }

    /// Whether `fact` unifies with `goal`; the bindings are undone.
    fn states(self: *Prover, fact: ExprId, goal: ExprId) Error!bool {
        const mark = self.wvars.mark();
        defer self.wvars.rollback(mark);
        var probe = Probe{};
        return self.terms.unify(fact, goal, Probe, &probe);
    }

    const Probe = struct {
        pub const Error = ProveError;

        pub fn match(_: *Probe, _: []const ?ExprId) ProveError!bool {
            return true;
        }
    };

    /// Try the rules for `expr`, `frame`'s goal or the goal with its shares
    /// bound, until one leads to a proof or a cut. The goal, its normal
    /// form and the unfoldings of the last are each tried with the rules
    /// for its head: each is a conversion, which the checker makes.
    fn expandRules(self: *Prover, frame: *Frame, expr: ExprId, close: *const Agenda, path: *const PathCell) Error!Outcome {
        const goal = frame.goal;
        var targets = std.ArrayListUnmanaged(ExprId).empty;
        defer targets.deinit(self.allocator);
        try targets.append(self.allocator, expr);
        if (try self.terms.normalForm(expr)) |normal| try targets.append(self.allocator, normal);
        while (try self.terms.unfold(targets.getLast())) |unfolded| try targets.append(self.allocator, unfolded);
        const goal_sort = self.wvars.sortOf(expr);
        var any_safe = false;
        // Unsafe alternatives are tried after the closers and safe rules,
        // those whose premises the facts might close first.
        var alts = std.ArrayListUnmanaged(Alt).empty;
        defer {
            for (alts.items) |alt| if (alt.bindings) |bindings| self.allocator.free(bindings);
            alts.deinit(self.allocator);
        }
        for (targets.items, 0..) |target, at| {
            const head = self.terms.headOf(target);
            const index = if (head) |id| self.catalog.indexes.getPtr(id) else null;
            const scratch = try self.allocator.alloc(u64, if (index) |found| found.scratchLen() else 0);
            defer self.allocator.free(scratch);
            const by_head = Picked{
                .rules = if (head) |id| self.catalog.forHead(id) else &.{},
                .picks = if (index) |found| found.query(self.terms, target, scratch) else null,
            };
            // A bare-binder conclusion matches the goal as it stands.
            const bare = Picked{ .rules = if (at == 0) self.catalog.forHead(catalog_mod.bare_head) else &.{} };
            for ([_]Picked{ by_head, bare }) |picked| {
                var rules = picked;
                while (rules.next()) |entry| {
                    switch (entry.role) {
                        .closer, .bridge => {},
                        .safe => {},
                        .unsafe => if (goal.depth == 0 or any_safe) break,
                    }
                    const rule = entry.statement(self.context);
                    // A bare-binder conclusion matches only goals of its sort.
                    switch (rule.concl) {
                        .app => {},
                        .binder => |idx| if (!std.mem.eql(u8, rule.args[idx].sort_name, goal_sort orelse break)) continue,
                    }
                    if (entry.role == .unsafe) {
                        var scorer = Scorer{
                            .prover = self,
                            .entry = entry,
                            .target = target,
                            .alts = &alts,
                            .mark = self.wvars.mark(),
                        };
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
            if (alt.bindings) |bindings| {
                // A kept match postponed nothing; the list in force is
                // the enclosing match's.
                const outer = self.terms.postponed;
                self.terms.postponed = null;
                defer self.terms.postponed = outer;
                var applier = Applier{
                    .prover = self,
                    .frame = frame,
                    .target = alt.target,
                    .how = .{ .rule = alt.entry },
                    .premise_depth = goal.depth - 1,
                    .close = close,
                    .path = path,
                };
                if (try applier.match(bindings)) return applier.outcome;
                continue;
            }
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
            const rule = alt.entry.statement(self.context);
            if (try self.terms.matchConclusion(rule, alt.target, Picker, &picker)) return picker.applier.outcome;
        }
        return .failed;
    }

    /// One way an unsafe rule's conclusion matches a goal: the `index`th
    /// match and how many of its premises no fact might close. The more
    /// specific conclusion (`catalog.Rule.specificity`), then the rule's
    /// declaration order break ties.
    const Alt = struct {
        entry: *const catalog_mod.Rule,
        /// The goal or unfolding of it the rule matched.
        target: ExprId,
        index: usize,
        open: usize,
        /// The match's bindings when making it bound no wvar, so it
        /// needs no redoing; owned by the prover's allocator.
        bindings: ?[]const ?ExprId,

        fn lessThan(_: void, lhs: Alt, rhs: Alt) bool {
            if (lhs.open != rhs.open) return lhs.open < rhs.open;
            if (lhs.entry.specificity != rhs.entry.specificity) return lhs.entry.specificity > rhs.entry.specificity;
            if (lhs.entry.rule_id != rhs.entry.rule_id) return lhs.entry.rule_id < rhs.entry.rule_id;
            return lhs.index < rhs.index;
        }
    };

    /// Whether `entry` may invent `binder`: only an unsafe rule makes a
    /// guess, and only for a binder a premise holds, which a fact closes.
    fn inventable(entry: *const catalog_mod.Rule, binder: usize) bool {
        if (entry.role != .unsafe) return false;
        if (entry.view != null or entry.abstraction != null) return true;
        for (entry.premises) |premise| {
            if (Rules.templateMentionsBinder(premise, binder)) return true;
        }
        return false;
    }

    /// The matcher's sink that lists an unsafe rule's matches as `Alt`s.
    const Scorer = struct {
        prover: *Prover,
        entry: *const catalog_mod.Rule,
        target: ExprId,
        alts: *std.ArrayListUnmanaged(Alt),
        /// The wvar log length before the match.
        mark: usize,
        index: usize = 0,

        pub const Error = ProveError;

        /// Whether the match may invent `binder` (`Terms.invented`).
        pub fn mayInvent(self: *const Scorer, binder: usize) bool {
            return inventable(self.entry, binder);
        }

        pub fn match(self: *Scorer, bindings: []const ?ExprId) ProveError!bool {
            const prover = self.prover;
            const rule = self.entry.statement(prover.context);
            var open: usize = 0;
            for (rule.hyps) |hyp| {
                // A premise the match leaves unfixed takes any fact: a guess.
                if (hyp == .binder and bindings[hyp.binder] == null) {
                    open += 1;
                    continue;
                }
                for (prover.facts) |fact| {
                    if (try prover.terms.mightFit(hyp, bindings, fact.expr)) break;
                } else open += 1;
            }
            // A rule with shares is matched again: the match reports its
            // split only while it runs.
            // So is one with postponed nodes, which it reports only then too.
            const kept = if (prover.wvars.mark() == self.mark and self.entry.shares.len == 0 and
                prover.terms.postponed == null)
                try prover.allocator.dupe(?ExprId, bindings)
            else
                null;
            errdefer if (kept) |slice| prover.allocator.free(slice);
            try self.alts.append(prover.allocator, .{
                .entry = self.entry,
                .target = self.target,
                .index = self.index,
                .open = open,
                .bindings = kept,
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

        /// As `Scorer.mayInvent`, so the picked match is the scored one.
        pub fn mayInvent(self: *const Picker, binder: usize) bool {
            return self.applier.mayInvent(binder);
        }

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
        /// The cut wvars the step leaves open: the goal's, when the match
        /// left them unbound, and the ones it invented.
        pass: []const u32 = &.{},

        pub const Error = ProveError;

        /// Whether the match may invent `binder` (`Terms.invented`).
        pub fn mayInvent(self: *const Applier, binder: usize) bool {
            return switch (self.how) {
                .rule => |entry| inventable(entry, binder),
                .ref => false,
            };
        }

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
        var split: ?Split = null;
        var checks: []const Check = &.{};
        var abstract: ?Abstract = null;
        if (!try self.sharesFit()) return .failed;
        applier.pass = &.{};
        const invented = self.terms.invented;
        switch (applier.how) {
            .ref => |ref| step = .{ .ref = ref },
            .rule => |entry| {
                if (entry.role != .closer and entry.role != .bridge and !try self.bindsCut(applier.frame.cuts)) {
                    // A cut rule passing the goal's cut on would stack one
                    // guess on another.
                    if (entry.cuts.len != 0) return .failed;
                    applier.pass = applier.frame.cuts;
                }
                const full = try self.arena.alloc(ExprId, bindings.len);
                for (full, bindings) |*value, binding| value.* = binding orelse undefined;
                premises = entry.premises;
                values = full;
                const filled = try self.arena.alloc(bool, bindings.len);
                for (filled, bindings) |*known, binding| known.* = binding != null;
                // A share goes before the eigenvariables the step
                // introduces, so none can end up in it, unless it depends
                // on one (`ex_elim`'s `G: ctx x`).
                const eigen_deps = self.eigenDeps(entry);
                var shares = std.ArrayListUnmanaged(u32).empty;
                try self.share(entry, eigen_deps, false, full, filled, &shares);
                if (entry.view) |view| values = try self.witness(entry, view, full, filled, applier.target);
                if (entry.cuts.len != 0) try self.cut(entry, full, filled, applier.target);
                try self.share(entry, eigen_deps, true, full, filled, &shares);
                // An abstraction's hole and target are made once its
                // premises can fix the walk's inputs: the hole after the
                // cuts, so none can hold it, and the target after the hole,
                // which it holds.
                if (entry.abstraction) |*abstraction| {
                    var held = std.ArrayListUnmanaged(ExprId).empty;
                    defer held.deinit(self.allocator);
                    for (full, 0..) |value, idx| {
                        if ((abstraction.premise_binders >> @intCast(idx)) & 1 != 0) try held.append(self.allocator, value);
                    }
                    if (!try self.inputsFixed(abstraction.decl, full, held.items)) return .failed;
                    const args = entry.statement(self.context).args;
                    const hole = abstraction.decl.hole_view_idx;
                    full[hole] = try self.wvars.introduce(args[hole].sort_name, applier.target, null);
                    filled[hole] = true;
                    const target = abstraction.decl.target_view_idx;
                    full[target] = try self.wvars.mint(args[target].sort_name, &.{}, false);
                    filled[target] = true;
                    abstract = .{ .abstraction = abstraction, .values = full };
                }
                if (shares.items.len != 0) split = .{ .shares = shares.items, .bag = self.terms.split.?, .outer = self.splits };
                if (self.terms.postponed) |list| checks = (try self.postponedChecks(list, full, filled)) orelse return .failed;
                if (!try self.freshBound(entry, bindings, full)) return .failed;
                const rule_bindings = if (entry.abstraction != null) try self.ruleBindings(entry, full) else full;
                step = .{ .rule = .{ .rule_id = entry.rule_id, .bindings = rule_bindings } };
            },
        }
        // Only an unsafe rule, which charges depth, invents (`inventable`).
        std.debug.assert(invented == null or (applier.how == .rule and applier.how.rule.role == .unsafe));
        if (invented) |first| {
            var list = std.ArrayListUnmanaged(u32).empty;
            try list.appendSlice(self.arena, applier.pass);
            var cell: ?*const terms_mod.Invented = first;
            while (cell) |c| : (cell = c.next) try list.append(self.arena, c.wvar);
            applier.pass = list.items;
        }
        // The cuts the step leaves open, passed on from the goal or
        // invented, are each held by a premise a fact closes
        // (`Goal.pass`): a rule closing it would guess their values, and
        // so would any fact closing a bare one.
        var instantiated: ?[]const ExprId = null;
        if (applier.pass.len != 0) {
            const exprs = try self.arena.alloc(ExprId, premises.len);
            const held = try self.arena.alloc(bool, applier.pass.len);
            @memset(held, false);
            var open = std.ArrayListUnmanaged(u32).empty;
            defer open.deinit(self.allocator);
            for (exprs, premises) |*expr, premise| {
                expr.* = self.terms.instantiate(premise, values) catch |err| switch (err) {
                    error.Unsupported => return .failed,
                    else => |e| return e,
                };
                if (self.wvars.of(expr.*)) |idx| if (std.mem.indexOfScalar(u32, applier.pass, idx) != null) return .failed;
                open.clearRetainingCapacity();
                try self.wvars.collectUnbound(self.allocator, expr.*, &open);
                var holds = false;
                for (open.items) |idx| if (std.mem.indexOfScalar(u32, applier.pass, idx)) |at| {
                    held[at] = true;
                    holds = true;
                };
                if (!holds) continue;
                if (!try self.factMightEqual(expr.*)) return .failed;
            }
            for (applier.pass, held) |pass_wvar, is_held| {
                if (!is_held and self.wvars.vars.items[pass_wvar].value == null) return .failed;
            }
            instantiated = exprs;
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
        if (instantiated) |made| @memcpy(exprs, made) else for (exprs, premises) |*expr, premise| {
            expr.* = self.terms.instantiate(premise, values) catch |err| switch (err) {
                error.Unsupported => return .failed,
                else => |e| return e,
            };
        }
        // Only a fact closes a bridge's premise.
        if (applier.how == .rule and applier.how.rule.role == .bridge) for (exprs) |expr| {
            if (!try self.factMightEqual(expr)) return .failed;
        };
        const order = try self.allocator.alloc(usize, premises.len);
        defer self.allocator.free(order);
        var firsts = std.ArrayListUnmanaged(usize).empty;
        defer firsts.deinit(self.allocator);
        try self.orderPremises(exprs, order, &firsts);
        var head: *const Agenda = applier.close;
        const check_cells = try self.allocator.alloc(Agenda, checks.len);
        defer self.allocator.free(check_cells);
        for (check_cells, checks) |*check_cell, *made| {
            check_cell.* = .{ .item = .{ .check = made }, .next = head };
            head = check_cell;
        }
        var abstract_cell: Agenda = undefined;
        if (abstract) |*made| {
            abstract_cell = .{ .item = .{ .abstract = made }, .next = head };
            head = &abstract_cell;
        }
        var settle_cell: Agenda = undefined;
        if (split) |*made| {
            settle_cell = .{ .item = .{ .settle = made }, .next = head };
            head = &settle_cell;
            self.splits = made;
        }
        defer if (split) |made| {
            self.splits = made.outer;
        };
        const made_abstract: ?*const Abstract = if (abstract) |*made| made else null;
        const outcome = try self.runPremises(applier, exprs, order, children, head, made_abstract);
        if (outcome != .failed) return outcome;
        // Another premise holding a cut of the first may be the one whose
        // fact fixes it: `le_trans_ax`'s `y` in `suc a ≤ y` and `y ≤ c` is
        // `suc b` when `suc b ≤ c` is a fact and `suc a ≤ b` is the only
        // one for the first. Or whose rule does: `eqmp`'s `P` in `P ⇔ Q`
        // and `P` is `a = a` by `bineq1` when the fact `a = b` that `P`
        // guessed fails.
        const reordered = try self.allocator.alloc(usize, order.len);
        defer self.allocator.free(reordered);
        for (firsts.items) |first| {
            reordered[0] = first;
            var at: usize = 1;
            for (order) |idx| {
                if (idx == first) continue;
                reordered[at] = idx;
                at += 1;
            }
            const retried = try self.runPremises(applier, exprs, reordered, children, head, made_abstract);
            if (retried != .failed) return retried;
        }
        return .failed;
    }

    /// Whether each bound binder of `entry` the match fixed to a variable
    /// keeps it, and the theorem variables that depend on it, out of the
    /// other arguments that do not depend on the binder, as MM0 requires.
    /// A binder fixed to an unbound eigenvariable bars it from those
    /// arguments (`WVars.bar`), so no later binding or name breaks the
    /// condition either. The match's `bindings` say which binders it
    /// fixed; `full` holds every binder's value.
    fn freshBound(self: *Prover, entry: *const catalog_mod.Rule, bindings: []const ?ExprId, full: []const ExprId) Error!bool {
        const args = entry.statement(self.context).args;
        for (args, bindings, 0..) |arg, binding, idx| {
            if (!arg.bound or binding == null) continue;
            const value = self.wvars.resolve(full[idx]);
            switch (self.terms.theorem.interner.node(value).*) {
                .variable => for (args, full, 0..) |other, other_value, other_idx| {
                    if (other_idx == idx or other.deps & arg.deps != 0) continue;
                    if (!self.wvars.mentions(other_value, value)) continue;
                    // `@freshen` renames the variable out of the argument
                    // when the checker applies the step.
                    if (entry.abstraction == null and self.freshens(entry.rule_id, other_idx, idx)) continue;
                    return false;
                },
                .placeholder => {
                    const wvar = self.wvars.of(value) orelse continue;
                    if (!self.wvars.isEigen(wvar)) continue;
                    if (!try self.barFrom(args, full, idx, wvar)) return false;
                },
                .app => {},
            }
        }
        return true;
    }

    /// Whether rule `rule_id` declares `@freshen target blocker`.
    fn freshens(self: *const Prover, rule_id: u32, target: usize, blocker: usize) bool {
        const decls = self.context.freshen_bindings.get(rule_id) orelse return false;
        for (decls) |decl| {
            if (decl.target_arg_idx == target and decl.blocker_arg_idx == blocker) return true;
        }
        return false;
    }

    /// Bar the eigenvariable `wvar` that bound binder `idx` holds from the
    /// step's other arguments that do not depend on the binder; false when
    /// one holds it.
    fn barFrom(self: *Prover, args: []const ArgInfo, values: []const ExprId, idx: usize, wvar: u32) Error!bool {
        var others = std.ArrayListUnmanaged(ExprId).empty;
        defer others.deinit(self.allocator);
        for (args, values, 0..) |other, other_value, other_idx| {
            if (other_idx == idx or other.deps & args[idx].deps != 0) continue;
            try others.append(self.allocator, other_value);
        }
        return self.wvars.bar(wvar, others.items);
    }

    /// The checks of the postponed conclusion nodes `list` with the step's
    /// binder values `full`; null when one holds a binder the step leaves
    /// unfilled (`filled`).
    fn postponedChecks(self: *Prover, list: *const terms_mod.Postponed, full: []const ExprId, filled: []const bool) Error!?[]const Check {
        var count: usize = 0;
        var at: ?*const terms_mod.Postponed = list;
        while (at) |node| : (at = node.next) count += 1;
        const checks = try self.arena.alloc(Check, count);
        at = list;
        for (checks) |*made| {
            const node = at.?;
            at = node.next;
            for (filled, 0..) |known, idx| {
                if (!known and Rules.templateMentionsBinder(node.template, idx)) return null;
            }
            made.* = .{ .template = node.template, .values = full, .goal = node.goal };
        }
        return checks;
    }

    /// The premises of a step are proved: its postponed node `made`,
    /// instantiated and in normal form, must unify with its goal node.
    fn check(self: *Prover, made: *const Check, next: ?*const Agenda) Error!Outcome {
        const instance = self.terms.instantiate(made.template, made.values) catch |err| switch (err) {
            error.Unsupported => return .failed,
            else => |e| return e,
        };
        const resolved = try self.terms.resolveGoal(instance);
        var continuer = Continuer{ .prover = self, .next = next };
        const normal = (try self.terms.normalForm(resolved)) orelse resolved;
        // A substitution of a term still open has no normal form yet; the
        // one taken over stand-ins binds what the goal fixes.
        if (try self.wvars.holdsWVar(normal)) if (try self.terms.openNormalForm(normal)) |open| {
            var verifier = Verifier{ .prover = self, .instance = resolved, .goal = made.goal, .continuer = &continuer };
            _ = try self.terms.unify(open, made.goal, Verifier, &verifier);
            return continuer.outcome;
        };
        _ = try self.terms.unify(normal, made.goal, Continuer, &continuer);
        return continuer.outcome;
    }

    /// The premises of an abstraction's step are proved: the checker's
    /// walk reads the target off the view's two sides as they stand, the
    /// hole's eigenvariable at each site of the plugs. A side or plug
    /// still holding a wvar would make the walk guess, so the step fails
    /// then.
    fn abstractTarget(self: *Prover, made: *const Abstract, next: ?*const Agenda) Error!Outcome {
        const decl = made.abstraction.decl;
        if (!try self.inputsFixed(decl, made.values, &.{})) return .failed;
        const bindings = try self.allocator.alloc(?ExprId, made.abstraction.view.num_binders);
        defer self.allocator.free(bindings);
        @memset(bindings, null);
        for (abstractInputs(decl)) |idx| bindings[idx] = try self.terms.resolveGoal(made.values[idx]);
        bindings[decl.hole_view_idx] = made.values[decl.hole_view_idx];
        const value = (DerivedBindings.abstractAsIs(self.terms.theorem, self.context.env, decl, bindings) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            else => return .failed,
        }) orelse return .failed;
        const start = self.wvars.mark();
        defer self.wvars.rollback(start);
        if (!try self.wvars.bind(self.wvars.of(made.values[decl.target_view_idx]).?, value)) return .failed;
        return self.run(next);
    }

    /// Whether every wvar the inputs of `decl`'s walk hold unbound in the
    /// view binder values `values`, other than an eigenvariable, is one
    /// `rest` holds: the premises still to come, as no other goal is
    /// proved before the walk.
    fn inputsFixed(self: *Prover, decl: AbstractDecl, values: []const ExprId, rest: []const ExprId) Error!bool {
        var pending = std.ArrayListUnmanaged(u32).empty;
        defer pending.deinit(self.allocator);
        for (rest) |expr| try self.wvars.collectUnbound(self.allocator, expr, &pending);
        var held = std.ArrayListUnmanaged(u32).empty;
        defer held.deinit(self.allocator);
        for (abstractInputs(decl)) |idx| {
            held.clearRetainingCapacity();
            try self.wvars.collectUnbound(self.allocator, values[idx], &held);
            for (held.items) |wvar| {
                if (self.wvars.isEigen(wvar)) continue;
                if (std.mem.indexOfScalar(u32, pending.items, wvar) == null) return false;
            }
        }
        return true;
    }

    /// The binder values `full` of a step by `entry`, an abstraction, over
    /// the view's binders, as the rule's.
    fn ruleBindings(self: *Prover, entry: *const catalog_mod.Rule, full: []const ExprId) Error![]const ExprId {
        const out = try self.arena.alloc(ExprId, self.context.env.rules.items[entry.rule_id].args.len);
        for (entry.abstraction.?.view.binder_map, full) |arg, value| {
            if (arg) |idx| out[idx] = value;
        }
        return out;
    }

    /// The unifier's sink for a check taken over stand-ins: with the wvars
    /// the goal bound, the instance's normal form must meet the goal. Where
    /// a wvar is left open, it keeps out of the instance's bound variables,
    /// as its stand-in did, and the normal form over stand-ins stands.
    const Verifier = struct {
        prover: *Prover,
        instance: ExprId,
        goal: ExprId,
        continuer: *Continuer,

        pub const Error = ProveError;

        pub fn match(self: *Verifier, _: []const ?ExprId) ProveError!bool {
            const terms = self.prover.terms;
            const wvars = self.prover.wvars;
            const resolved = try terms.resolveGoal(self.instance);
            const normal = (try terms.normalForm(resolved)) orelse resolved;
            const open = if (try wvars.holdsWVar(normal)) (try terms.openNormalForm(normal)) orelse normal else normal;
            if (open == normal) return terms.unify(normal, self.goal, Continuer, self.continuer);
            const mark = wvars.mark();
            defer wvars.rollback(mark);
            var bound = std.ArrayListUnmanaged(ExprId).empty;
            defer bound.deinit(self.prover.allocator);
            try wvars.collectBound(self.prover.allocator, resolved, &bound);
            var held = std.ArrayListUnmanaged(u32).empty;
            defer held.deinit(self.prover.allocator);
            try wvars.collectUnbound(self.prover.allocator, normal, &held);
            for (held.items) |idx| try wvars.narrowCapture(idx, bound.items);
            return terms.unify(open, self.goal, Continuer, self.continuer);
        }
    };

    /// The unifier's sink that runs the rest of the agenda.
    const Continuer = struct {
        prover: *Prover,
        next: ?*const Agenda,
        outcome: Outcome = .failed,

        pub const Error = ProveError;

        pub fn match(self: *Continuer, _: []const ?ExprId) ProveError!bool {
            self.outcome = try self.prover.run(self.next);
            return self.outcome != .failed;
        }
    };

    /// Run the premises `exprs` in `order`, then `next`.
    fn runPremises(
        self: *Prover,
        applier: *const Applier,
        exprs: []const ExprId,
        order: []const usize,
        children: []?*const Node,
        next: *const Agenda,
        abstract: ?*const Abstract,
    ) Error!Outcome {
        const cells = try self.allocator.alloc(Agenda, exprs.len);
        defer self.allocator.free(cells);
        // An abstraction's inputs are checked after each premise against
        // those still to come.
        const ready_cells = try self.allocator.alloc(Agenda, if (abstract != null) exprs.len else 0);
        defer self.allocator.free(ready_cells);
        const ordered = try self.allocator.alloc(ExprId, ready_cells.len);
        defer self.allocator.free(ordered);
        for (ordered, 0..) |*expr, at| expr.* = exprs[order[at]];
        const readies = try self.allocator.alloc(Ready, ready_cells.len);
        defer self.allocator.free(readies);
        var head = next;
        var at = exprs.len;
        while (at > 0) {
            at -= 1;
            const idx = order[at];
            // After the last premise, the abstraction itself checks them.
            if (abstract) |made| if (at + 1 < exprs.len) {
                readies[at] = .{ .abstract = made, .rest = ordered[at + 1 ..] };
                ready_cells[at] = .{ .item = .{ .ready = &readies[at] }, .next = head };
                head = &ready_cells[at];
            };
            cells[at] = .{
                .item = .{ .goal = .{
                    .expr = exprs[idx],
                    .depth = applier.premise_depth,
                    .slot = &children[idx],
                    .path = applier.path,
                    .bridged = if (applier.how == .rule and applier.how.rule.role == .bridge) applier.target else null,
                    .pass = applier.pass,
                } },
                .next = head,
            };
            head = &cells[at];
        }
        return self.run(head);
    }

    /// The order to prove the premises `exprs` in, as indices into `order`.
    /// Those a fact might close go first: closing them binds the cut
    /// wvars the others share, and the more of those a premise holds, the
    /// earlier it goes (`or_elim`'s major premise fixes what both minor
    /// ones take). A fact that might close a premise only once a
    /// definition unfolds (`cb_branch` for `p ∨ q`) breaks no tie. A
    /// premise that is an unbound wvar goes last when such a sibling holds
    /// it, since any fact fits the wvar: closing it first only guesses what
    /// the sibling fixes. Behind a sibling no fact closes, which may need a
    /// rule that leaves the wvar open, only a lone such premise goes first:
    /// with several, each fact one guesses meets every fact the others do
    /// before the sibling is tried. The other premises a fact might close that hold
    /// an unbound cut wvar of the first go to `firsts`, to go first in its
    /// stead if it fails, and so does one no fact might close that holds
    /// every such wvar of the first: a rule closing it fixes what the first
    /// only guessed from the facts.
    fn orderPremises(self: *Prover, exprs: []const ExprId, order: []usize, firsts: *std.ArrayListUnmanaged(usize)) Error!void {
        const Rank = struct {
            /// 0: a fact might close the premise; 1: none might; 2: an
            /// unbound wvar such a sibling holds, or one of several a
            /// sibling holds that none might close.
            class: u2,
            cuts: usize,
            /// A fact might close it without unfolding.
            strict: bool,

            fn before(ranks: []const @This(), lhs: usize, rhs: usize) bool {
                const a = ranks[lhs];
                const b = ranks[rhs];
                if (a.class != b.class) return a.class < b.class;
                if (a.cuts != b.cuts) return a.cuts > b.cuts;
                if (a.strict != b.strict) return a.strict;
                return lhs < rhs;
            }
        };
        const ranks = try self.allocator.alloc(Rank, exprs.len);
        defer self.allocator.free(ranks);
        var held = std.ArrayListUnmanaged(u32).empty;
        defer held.deinit(self.allocator);
        for (ranks, exprs) |*rank, expr| {
            rank.* = .{ .class = 1, .cuts = 0, .strict = false };
            var picks = self.fact_index.query(self.terms, expr, self.fact_scratch);
            while (picks.next()) |n| {
                const fact = self.facts[n];
                if (try self.terms.mightEqual(fact.expr, expr, .strict)) {
                    rank.* = .{ .class = 0, .cuts = 0, .strict = true };
                    break;
                }
                if (try self.terms.mightEqual(fact.expr, expr, .unfolding)) rank.class = 0;
            }
            if (rank.class != 0) continue;
            held.clearRetainingCapacity();
            try self.wvars.collectUnbound(self.allocator, expr, &held);
            for (held.items) |idx| {
                if (self.wvars.vars.items[idx].cut) rank.cuts += 1;
            }
        }
        for (ranks, exprs, 0..) |*rank, expr, idx| {
            const wvar = self.wvars.of(self.wvars.resolve(expr)) orelse continue;
            for (exprs, ranks, 0..) |sibling, sibling_rank, sibling_idx| {
                if (sibling_idx == idx) continue;
                if (self.wvars.of(self.wvars.resolve(sibling)) != null) continue;
                held.clearRetainingCapacity();
                try self.wvars.collectUnbound(self.allocator, sibling, &held);
                if (std.mem.indexOfScalar(u32, held.items, wvar) == null) continue;
                const waits = sibling_rank.class == 0 or for (exprs, 0..) |other, other_idx| {
                    if (other_idx == idx or other_idx == sibling_idx) continue;
                    const other_wvar = self.wvars.of(self.wvars.resolve(other)) orelse continue;
                    if (std.mem.indexOfScalar(u32, held.items, other_wvar) != null) break true;
                } else false;
                if (!waits) continue;
                rank.class = 2;
                break;
            }
        }
        for (order, 0..) |*slot, idx| slot.* = idx;
        std.mem.sort(usize, order, @as([]const Rank, ranks), Rank.before);

        if (order.len < 2 or ranks[order[0]].cuts == 0) return;
        var first_cuts = std.ArrayListUnmanaged(u32).empty;
        defer first_cuts.deinit(self.allocator);
        try self.wvars.collectUnbound(self.allocator, exprs[order[0]], &first_cuts);
        for (order[1..]) |idx| {
            if (ranks[idx].class == 2) continue;
            held.clearRetainingCapacity();
            try self.wvars.collectUnbound(self.allocator, exprs[idx], &held);
            var holds_one = false;
            var holds_all = true;
            for (first_cuts.items) |wvar| {
                if (!self.wvars.vars.items[wvar].cut) continue;
                if (std.mem.indexOfScalar(u32, held.items, wvar) != null) holds_one = true else holds_all = false;
            }
            if (if (ranks[idx].class == 0) holds_one else holds_all) try firsts.append(self.allocator, idx);
        }
    }

    /// Fill `entry`'s witnesses in `full` (a fresh wvar for each γ, an
    /// eigenvariable introduced at `goal` for each δ) and return the view's
    /// binder values.
    fn witness(
        self: *Prover,
        entry: *const catalog_mod.Rule,
        view: *const ViewDecl,
        full: []ExprId,
        filled: []bool,
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
                .delta => full[w.arg] = try self.wvars.introduce(sort_name, goal, null),
            }
            filled[w.arg] = true;
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
    /// match just made binds one, or postponed a conclusion node against a
    /// part of the goal holding one, which the node's check binds.
    fn bindsCut(self: *Prover, cuts: []const u32) Error!bool {
        if (cuts.len == 0) return true;
        for (cuts) |idx| {
            if (self.wvars.vars.items[idx].value != null) return true;
        }
        var held = std.ArrayListUnmanaged(u32).empty;
        defer held.deinit(self.allocator);
        var node = self.terms.postponed;
        while (node) |cell| : (node = cell.next) {
            held.clearRetainingCapacity();
            try self.wvars.collectUnbound(self.allocator, cell.goal, &held);
            for (held.items) |idx| {
                if (std.mem.indexOfScalar(u32, cuts, idx) != null) return true;
            }
        }
        return false;
    }

    /// The binders of `entry`'s eigenvariables, as a dependency mask.
    fn eigenDeps(self: *const Prover, entry: *const catalog_mod.Rule) u64 {
        const args = entry.statement(self.context).args;
        var deps: u64 = 0;
        for (entry.cuts) |c| {
            if (c.kind == .delta) deps |= args[c.arg].deps;
        }
        for (entry.witnesses) |w| {
            if (w.kind == .delta) deps |= args[w.arg].deps;
        }
        return deps;
    }

    /// Fill the shares of `entry` the match left unbound with fresh wvars:
    /// those that depend on an eigenvariable of the step when `dependent`,
    /// the others otherwise.
    fn share(
        self: *Prover,
        entry: *const catalog_mod.Rule,
        eigen_deps: u64,
        dependent: bool,
        full: []ExprId,
        filled: []bool,
        shares: *std.ArrayListUnmanaged(u32),
    ) Error!void {
        const args = entry.statement(self.context).args;
        for (entry.shares) |arg| {
            if (filled[arg] or (args[arg].deps & eigen_deps != 0) != dependent) continue;
            full[arg] = try self.wvars.mint(args[arg].sort_name, &.{}, false);
            filled[arg] = true;
            try shares.append(self.arena, self.wvars.of(full[arg]).?);
        }
    }

    /// The split wvar `idx` is a share of, if any.
    fn splitOf(self: *const Prover, idx: u32) ?*const Split {
        var at = self.splits;
        while (at) |split| : (at = split.outer) {
            if (std.mem.indexOfScalar(u32, split.shares, idx) != null) return split;
        }
        return null;
    }

    /// The split of the first unbound share `expr` holds, with the unbound
    /// shares of that split it holds in `held`; null when it holds none.
    fn heldShares(self: *Prover, expr: ExprId, held: *std.ArrayListUnmanaged(u32)) Error!?*const Split {
        if (self.splits == null or !try self.wvars.holdsWVar(expr)) return null;
        try self.wvars.collectUnbound(self.allocator, expr, held);
        var found: ?*const Split = null;
        var kept: usize = 0;
        for (held.items) |idx| {
            const split = self.splitOf(idx) orelse continue;
            if (found == null) found = split;
            if (split != found.?) continue;
            held.items[kept] = idx;
            kept += 1;
        }
        held.shrinkRetainingCapacity(kept);
        return found;
    }

    /// The members of `split`'s bag that neither the template's own
    /// members took nor a bound share holds, as one expression; null when
    /// there are none and the bag has no unit.
    fn remainder(self: *Prover, split: *const Split) Error!?ExprId {
        const bag = split.bag;
        var left: AcuiBag.ExprBag = .{};
        for (bag.members, 0..) |member, at| {
            if (bag.taken & (@as(u64, 1) << @intCast(at)) != 0) continue;
            if (try self.shareHolds(split, member)) continue;
            _ = left.append(member);
        }
        return bag.combiner.build(self.terms.theorem, left.slice());
    }

    /// Whether a bound share of `split` holds the bag member `member`.
    fn shareHolds(self: *Prover, split: *const Split, member: ExprId) Error!bool {
        const want = try self.terms.resolveGoal(member);
        for (split.shares) |idx| {
            const value = self.wvars.vars.items[idx].value orelse continue;
            const members = split.bag.combiner.flatten(self.terms.theorem, try self.terms.resolveGoal(value)) orelse
                return error.Unsupported;
            if (std.mem.indexOfScalar(ExprId, members.slice(), want) != null) return true;
        }
        return false;
    }

    /// Whether every bound share holds only members of its bag, as far as
    /// is known: a member that is none must still unify with one (`settle`),
    /// so it may not clash with them all (`Terms.mightEqual`).
    fn sharesFit(self: *Prover) Error!bool {
        var at = self.splits;
        while (at) |split| : (at = split.outer) {
            var members: AcuiBag.ExprBag = .{};
            for (split.bag.members) |member| _ = members.append(try self.terms.resolveGoal(member));
            for (split.shares) |idx| {
                const value = self.wvars.vars.items[idx].value orelse continue;
                const held = split.bag.combiner.flatten(self.terms.theorem, try self.terms.resolveGoal(value)) orelse
                    return error.Unsupported;
                for (held.slice()) |member| {
                    if (std.mem.indexOfScalar(ExprId, members.slice(), member) != null) continue;
                    for (members.slice()) |other| {
                        if (try self.terms.mightEqual(member, other, .unfolding)) break;
                    } else return false;
                }
            }
        }
        return true;
    }

    /// The premises of `split`'s rule are proved: a share still unbound
    /// (one no premise holds) takes what the others leave, and then the
    /// shares must hold only members of the bag and every member the
    /// template's own members did not take. A share's member that is no
    /// bag member as it stands is one once it unifies with one: a fact may
    /// name the variable a step's eigenvariable in the bag becomes
    /// (`dvd_elim`'s `k` in `y = x * k`).
    fn settle(self: *Prover, split: *const Split, next: ?*const Agenda) Error!Outcome {
        const start = self.wvars.mark();
        defer self.wvars.rollback(start);
        for (split.shares) |idx| {
            if (self.wvars.vars.items[idx].value != null) continue;
            const value = (try self.remainder(split)) orelse return .failed;
            if (!try self.wvars.bind(idx, value)) return .failed;
        }
        const bag = split.bag;
        var members: AcuiBag.ExprBag = .{};
        for (bag.members) |member| _ = members.append(try self.terms.resolveGoal(member));
        var strays = std.ArrayListUnmanaged(ExprId).empty;
        defer strays.deinit(self.allocator);
        for (split.shares) |idx| {
            const value = try self.terms.resolveGoal(self.wvars.vars.items[idx].expr);
            const held = bag.combiner.flatten(self.terms.theorem, value) orelse return error.Unsupported;
            for (held.slice()) |member| {
                if (std.mem.indexOfScalar(ExprId, members.slice(), member) == null) try strays.append(self.allocator, member);
            }
        }
        return self.placeStrays(split, strays.items, next);
    }

    /// Unify each share member in `strays` with a member of `split`'s bag,
    /// each way in turn, then check that the shares hold every member the
    /// template's own members did not take and run `next`.
    fn placeStrays(self: *Prover, split: *const Split, strays: []const ExprId, next: ?*const Agenda) Error!Outcome {
        const bag = split.bag;
        if (strays.len == 0) {
            for (bag.members, 0..) |member, at| {
                if (bag.taken & (@as(u64, 1) << @intCast(at)) != 0) continue;
                if (!try self.shareHolds(split, member)) return .failed;
            }
            return self.run(next);
        }
        // An earlier placement may have made it a member already.
        const stray = try self.terms.resolveGoal(strays[0]);
        for (bag.members) |member| {
            if (try self.terms.resolveGoal(member) == stray) return self.placeStrays(split, strays[1..], next);
        }
        const open = try self.wvars.holdsWVar(stray);
        for (bag.members) |raw| {
            const member = try self.terms.resolveGoal(raw);
            // Two distinct ground members never unify.
            if (!open and !try self.wvars.holdsWVar(member)) continue;
            var placer = Placer{ .prover = self, .split = split, .rest = strays[1..], .next = next };
            _ = try self.terms.unify(stray, member, Placer, &placer);
            if (placer.outcome != .failed) return placer.outcome;
        }
        return .failed;
    }

    /// The unifier's sink that places the rest of a split's strays.
    const Placer = struct {
        prover: *Prover,
        split: *const Split,
        rest: []const ExprId,
        next: ?*const Agenda,
        outcome: Outcome = .failed,

        pub const Error = ProveError;

        pub fn match(self: *Placer, _: []const ?ExprId) ProveError!bool {
            self.outcome = try self.prover.placeStrays(self.split, self.rest, self.next);
            return self.outcome != .failed;
        }
    };

    /// Fill `entry`'s cuts in `full`: a fresh wvar for each γ, an
    /// eigenvariable introduced at `goal` for each δ. A γ cut that depends
    /// on no δ one is minted before them, so it cannot hold one; nor may it
    /// hold the variable of a bound binder of the conclusion it does not
    /// depend on. A δ cut may become a variable only the arguments that
    /// depend on it mention (`ex_elim`'s `x`, which `G` may hold but not
    /// `H` or `c`).
    fn cut(self: *Prover, entry: *const catalog_mod.Rule, full: []ExprId, filled: []bool, goal: ExprId) Error!void {
        const args = entry.statement(self.context).args;
        var cut_mask: u64 = 0;
        var delta_deps: u64 = 0;
        for (entry.cuts) |c| {
            if (filled[c.arg]) continue;
            cut_mask |= @as(u64, 1) << @intCast(c.arg);
            if (c.kind == .delta) delta_deps |= args[c.arg].deps;
        }
        for (0..3) |pass| for (entry.cuts) |c| {
            const arg = args[c.arg];
            const stage: usize = switch (c.kind) {
                .gamma => if (arg.deps & delta_deps == 0) 0 else 2,
                .delta => 1,
            };
            // The match binds a cut it holds under a rewritten head when
            // the goal has that head too.
            if (stage != pass or filled[c.arg]) continue;
            full[c.arg] = switch (c.kind) {
                .gamma => blk: {
                    var capture = std.ArrayListUnmanaged(ExprId).empty;
                    for (args, full, filled, 0..) |other, value, known, idx| {
                        if (!other.bound or !known or (cut_mask >> @intCast(idx)) & 1 != 0) continue;
                        if (arg.deps & other.deps != 0) continue;
                        const variable = try self.wvars.deref(value, null);
                        if (self.terms.theorem.interner.node(variable).* != .variable) continue;
                        try capture.append(self.arena, variable);
                    }
                    break :blk try self.wvars.mint(arg.sort_name, capture.items, true);
                },
                .delta => blk: {
                    var fresh_in = std.ArrayListUnmanaged(ExprId).empty;
                    for (args, full, filled, 0..) |other, value, known, idx| {
                        if (!known or idx == c.arg or other.deps & arg.deps != 0) continue;
                        try fresh_in.append(self.arena, value);
                    }
                    break :blk try self.wvars.introduce(arg.sort_name, goal, fresh_in.items);
                },
            };
            filled[c.arg] = true;
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
