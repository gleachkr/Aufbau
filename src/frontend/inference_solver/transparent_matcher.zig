const std = @import("std");

const ExprId = @import("../expr.zig").ExprId;
const TemplateExpr = @import("../rules.zig").TemplateExpr;
const DefOps = @import("../def_ops.zig");
const DebugTrace = @import("../debug.zig");
const NormalizedCompare = @import("../normalized_compare.zig");
const BranchStateOps = @import("./branch_state.zig");
const SemanticCompare = @import("./semantic_compare.zig");
const StructuralIntervals = @import("./intervals.zig");
const SessionSync = @import("./session_sync.zig");
const types = @import("./types.zig");
const BinderSpace = types.BinderSpace;
const BranchState = types.BranchState;

pub fn matchExprTransparent(
    self: anytype,
    template: TemplateExpr,
    actual: ExprId,
    space: BinderSpace,
    state: BranchState,
) anyerror![]BranchState {
    const transparent = try matchTransparentOnly(
        self,
        template,
        actual,
        space,
        state,
    );
    if (transparent.len != 0) return transparent;

    return try matchNormalizedOnly(
        self,
        template,
        actual,
        space,
        state,
    );
}

fn matchTransparentOnly(
    self: anytype,
    template: TemplateExpr,
    actual: ExprId,
    space: BinderSpace,
    state: BranchState,
) anyerror![]BranchState {
    if (BranchStateOps.matchState(&state, space) != null) {
        return try matchSessionTransparentOnly(
            self,
            template,
            actual,
            space,
            state,
        );
    }

    var new_state = try BranchStateOps.cloneState(self, state);
    const bindings = BranchStateOps.getBindings(&new_state, space);
    const old_bindings = BranchStateOps.getBindings(@constCast(&state), space);

    const def_ops = self.defOpsContextPlain();
    var residue = false;
    if (!(def_ops.matchTemplateTransparent(
        template,
        actual,
        bindings,
        &residue,
    ) catch |err| switch (err) {
        error.DependencySlotExhausted => return &.{},
        else => return err,
    })) {
        return &.{};
    }
    if (residue) {
        // The match assigned a binder to a value plain bindings cannot hold:
        // it still refers to a hidden def dummy that only a later constraint
        // can pin (`∃ x p` against a def hiding `x` leaves `p` mentioning
        // `x`). Dropping it would lose both the dummy and the relationship,
        // so redo the match in a session and keep that state on the branch;
        // from here on the branch replays its rule-space matching from it.
        DebugTrace.traceInference(
            self.debug,
            "structural inference: keeping symbolic match state for a hidden binder\n",
            .{},
        );
        return try matchSessionTransparentFresh(
            self,
            template,
            actual,
            space,
            state,
        );
    }
    for (bindings, old_bindings, 0..) |binding, old_binding, idx| {
        const expr_id = binding orelse continue;
        if (old_binding != null) continue;
        if (!try StructuralIntervals.bindingSatisfiesStructural(
            self,
            &new_state,
            space,
            idx,
            expr_id,
        )) {
            return &.{};
        }
    }

    const out = try self.allocator.alloc(BranchState, 1);
    out[0] = new_state;
    return out;
}

/// Replay a match from the branch's exported session state.
fn matchSessionTransparentOnly(
    self: anytype,
    template: TemplateExpr,
    actual: ExprId,
    space: BinderSpace,
    state: BranchState,
) anyerror![]BranchState {
    const seed_state = BranchStateOps.matchState(&state, space) orelse return &.{};

    const def_ops = self.defOpsContext();

    var session = try def_ops.beginRuleMatchFromSeedState(
        self.argInfosForSpace(space),
        seed_state,
    );
    defer session.deinit();

    const matched = session.matchTransparent(template, actual) catch |err| {
        return switch (err) {
            error.DependencySlotExhausted => &.{},
            else => err,
        };
    };
    if (!matched) return &.{};

    return try copySessionToBranch(self, &session, space, state);
}

/// The same match `matchTransparentOnly` just made through plain bindings,
/// redone in a session seeded from those bindings so its state can be kept.
fn matchSessionTransparentFresh(
    self: anytype,
    template: TemplateExpr,
    actual: ExprId,
    space: BinderSpace,
    state: BranchState,
) anyerror![]BranchState {
    const old_bindings = BranchStateOps.getBindings(@constCast(&state), space);
    const seeds = try DefOps.BindingSeed.fromOptionalBindings(
        self.allocator,
        old_bindings,
    );
    defer self.allocator.free(seeds);

    const def_ops = self.defOpsContextPlain();

    var session = try def_ops.beginRuleMatch(
        self.argInfosForSpace(space),
        seeds,
    );
    defer session.deinit();

    const matched = session.matchTransparent(template, actual) catch |err| {
        return switch (err) {
            error.DependencySlotExhausted => &.{},
            else => err,
        };
    };
    if (!matched) return &.{};

    return try copySessionToBranch(self, &session, space, state);
}

fn matchNormalizedOnly(
    self: anytype,
    template: TemplateExpr,
    actual: ExprId,
    space: BinderSpace,
    state: BranchState,
) anyerror![]BranchState {
    if (!self.canUseNormalizedStructuralItemMatch()) return &.{};
    const scratch = self.scratch orelse return &.{};

    const old_bindings = BranchStateOps.getBindings(@constCast(&state), space);
    const seed_state = BranchStateOps.matchState(&state, space);

    const def_ops = self.defOpsContext();
    const args = self.argInfosForSpace(space);

    const seeds = if (seed_state != null)
        null
    else
        try DefOps.BindingSeed.fromOptionalBindings(
            self.allocator,
            old_bindings,
        );
    defer if (seeds) |owned| self.allocator.free(owned);

    var session = if (seed_state) |saved|
        try def_ops.beginRuleMatchFromSeedState(args, saved)
    else
        try def_ops.beginRuleMatch(args, seeds.?);
    defer session.deinit();

    const mark = scratch.mark();
    const matched = NormalizedCompare.matchTemplate(
        // The normalizer/canonicalizer built inside `finish` create def_ops
        // contexts that intern into the mirror theorem, so they must run on the
        // real allocator rather than the per-solve arena.
        self.real_allocator,
        self.env,
        self.registry,
        scratch,
        &session,
        template,
        actual,
    ) catch |err| {
        scratch.discard(mark);
        return switch (err) {
            error.DependencySlotExhausted => &.{},
            error.MissingRepresentative => &.{},
            error.UnresolvedDummyWitness => &.{},
            else => err,
        };
    };
    scratch.discard(mark);
    if (!matched) return &.{};

    if (seed_state != null) {
        return try copySessionToBranch(self, &session, space, state);
    }

    // `materialized`/`represented` are allocated by the session on its own
    // allocator (`self.real_allocator`, which the def_ops context above is
    // pinned to), so they must be freed there — not on the per-solve arena
    // (`self.allocator`), where the free would be a no-op and leak the real
    // allocation.
    const materialized = try session.materializeOptionalBindings();
    defer self.real_allocator.free(materialized);
    const represented = try session.representOptionalBindings(materialized);
    defer self.real_allocator.free(represented);

    return try copySessionBindingsToBranch(
        self,
        &session,
        represented,
        old_bindings,
        space,
        state,
    );
}

fn copySessionToBranch(
    self: anytype,
    session: *DefOps.RuleMatchSession,
    space: BinderSpace,
    state: BranchState,
) anyerror![]BranchState {
    const old_bindings = BranchStateOps.bindingsForSpace(
        @constCast(&state),
        space,
    ) orelse return &.{};

    var new_state = try BranchStateOps.cloneState(self, state);
    try SessionSync.syncFromSession(self.allocator, &new_state, space, session);

    const bindings = BranchStateOps.bindingsForSpace(&new_state, space) orelse {
        return &.{};
    };
    for (bindings, old_bindings, 0..) |binding, old_binding, idx| {
        const expr_id = binding orelse continue;
        if (old_binding) |existing| {
            if (!try SemanticCompare.bindingCompatible(
                self,
                existing,
                expr_id,
            )) {
                return &.{};
            }
            continue;
        }
        if (!try StructuralIntervals.bindingSatisfiesStructural(
            self,
            &new_state,
            space,
            idx,
            expr_id,
        )) {
            return &.{};
        }
    }

    if (!try self.partialStructuralStateCompatible(&new_state, space)) {
        return &.{};
    }

    const out = try self.allocator.alloc(BranchState, 1);
    out[0] = new_state;
    return out;
}

fn copySessionBindingsToBranch(
    self: anytype,
    session: *DefOps.RuleMatchSession,
    session_bindings: []const ?ExprId,
    old_bindings: []const ?ExprId,
    space: BinderSpace,
    state: BranchState,
) anyerror![]BranchState {
    var new_state = try BranchStateOps.cloneState(self, state);
    const bindings = BranchStateOps.getBindings(&new_state, space);

    for (session_bindings, old_bindings, 0..) |
        maybe_expr,
        old_binding,
        idx,
    | {
        if (idx >= bindings.len) return &.{};
        const expr_id = maybe_expr orelse {
            if (old_binding == null and session.state.bindings[idx] != null) {
                // Assigned but not materializable: keep the session state on
                // the branch rather than dropping the assignment.
                return try copySessionToBranch(self, session, space, state);
            }
            continue;
        };
        if (old_binding) |existing| {
            if (!try SemanticCompare.bindingCompatible(
                self,
                existing,
                expr_id,
            )) {
                return &.{};
            }
            continue;
        }
        if (!try StructuralIntervals.bindingSatisfiesStructural(
            self,
            &new_state,
            space,
            idx,
            expr_id,
        )) {
            return &.{};
        }
        bindings[idx] = expr_id;
    }

    if (!try self.partialStructuralStateCompatible(&new_state, space)) {
        return &.{};
    }

    const out = try self.allocator.alloc(BranchState, 1);
    out[0] = new_state;
    return out;
}
