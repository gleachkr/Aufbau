const std = @import("std");

const ArgInfo = @import("../parse_recovery.zig").ArgInfo;
const ExprId = @import("../expr.zig").ExprId;
const TemplateExpr = @import("../rules.zig").TemplateExpr;
const DefOps = @import("../def_ops.zig");
const NormalizedCompare = @import("../compiler/normalized_compare.zig");
const BranchStateOps = @import("./branch_state.zig");
const SemanticCompare = @import("./semantic_compare.zig");
const StructuralIntervals = @import("./intervals.zig");
const ViewState = @import("./view_state.zig");
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
    if (space == .view and state.view_match_state != null) {
        return try matchViewTransparentOnly(
            self,
            template,
            actual,
            state,
        );
    }

    var new_state = try BranchStateOps.cloneState(self, state);
    const bindings = BranchStateOps.getBindings(&new_state, space);
    const old_bindings = switch (space) {
        .rule => state.rule_bindings,
        .view => state.view_bindings.?,
    };

    const def_ops = self.defOpsContextPlain();
    if (!(def_ops.matchTemplateTransparent(
        template,
        actual,
        bindings,
    ) catch |err| switch (err) {
        error.DependencySlotExhausted => return &.{},
        else => return err,
    })) {
        return &.{};
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

fn matchViewTransparentOnly(
    self: anytype,
    template: TemplateExpr,
    actual: ExprId,
    state: BranchState,
) anyerror![]BranchState {
    const seed_state = state.view_match_state orelse return &.{};
    const view = self.view orelse return &.{};

    const def_ops = self.defOpsContext();

    var session = try def_ops.beginRuleMatchFromSeedState(
        view.arg_infos,
        &seed_state,
    );
    defer session.deinit();

    const matched = session.matchTransparent(template, actual) catch |err| {
        return switch (err) {
            error.DependencySlotExhausted => &.{},
            else => err,
        };
    };
    if (!matched) return &.{};

    return try copyViewSessionToBranch(self, &session, state);
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

    const old_bindings = switch (space) {
        .rule => state.rule_bindings,
        .view => state.view_bindings.?,
    };

    const def_ops = self.defOpsContext();

    const seeds = if (space == .view and state.view_match_state != null)
        null
    else
        try DefOps.BindingSeed.fromOptionalBindings(
            self.allocator,
            old_bindings,
        );
    defer if (seeds) |owned| self.allocator.free(owned);

    var session = if (space == .view) blk: {
        if (state.view_match_state) |*seed_state| {
            break :blk try def_ops.beginRuleMatchFromSeedState(
                ruleArgsForSpace(self, space),
                seed_state,
            );
        }
        break :blk try def_ops.beginRuleMatch(
            ruleArgsForSpace(self, space),
            seeds.?,
        );
    } else try def_ops.beginRuleMatch(
        ruleArgsForSpace(self, space),
        seeds.?,
    );
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

    if (space == .view and state.view_match_state != null) {
        return try copyViewSessionToBranch(self, &session, state);
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

fn copyViewSessionToBranch(
    self: anytype,
    session: *DefOps.RuleMatchSession,
    state: BranchState,
) anyerror![]BranchState {
    var new_state = try BranchStateOps.cloneState(self, state);
    try ViewState.syncFromSession(self.allocator, &new_state, session);

    const old_bindings = state.view_bindings orelse return &.{};
    const bindings = new_state.view_bindings orelse return &.{};
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
            .view,
            idx,
            expr_id,
        )) {
            return &.{};
        }
    }

    if (!try self.partialStructuralStateCompatible(&new_state, .view)) {
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
                return &.{};
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

fn ruleArgsForSpace(
    self: anytype,
    space: BinderSpace,
) []const ArgInfo {
    return switch (space) {
        .rule => self.rule.args,
        .view => self.view.?.arg_infos,
    };
}
