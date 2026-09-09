const std = @import("std");
const ExprId = @import("../expr.zig").ExprId;
const DefOps = @import("../def_ops.zig");
const types = @import("./types.zig");
const BinderSpace = types.BinderSpace;
const BranchState = types.BranchState;
const BranchStateOps = @import("./branch_state.zig");

/// Copy a rule-match session's resolvable bindings into the branch and keep
/// the session's exported state on the branch, so later constraints in the
/// same space replay from it.
pub fn syncFromSession(
    allocator: std.mem.Allocator,
    state: *BranchState,
    space: BinderSpace,
    session: *DefOps.RuleMatchSession,
) anyerror!void {
    const bindings = BranchStateOps.bindingsForSpace(state, space) orelse return;
    // The snapshot is allocated on the session's (real) allocator. We keep only
    // a clone of the seed state on `allocator` so the BranchState owns all of
    // its memory from a single allocator (the per-solve arena), then free the
    // whole export back on the session allocator.
    var snapshot = try session.exportOptionalBindingSnapshot();
    defer snapshot.deinit(session.shared.allocator);

    for (snapshot.bindings, 0..) |binding, idx| {
        if (idx >= bindings.len) break;
        if (binding) |expr_id| bindings[idx] = expr_id;
    }

    const cloned = try BranchStateOps.cloneMatchSeedState(
        allocator,
        &snapshot.seed_state,
    );
    BranchStateOps.setMatchState(allocator, state, space, cloned);
}

pub fn syncConcreteBindingsIntoSeedState(
    allocator: std.mem.Allocator,
    state: *BranchState,
    space: BinderSpace,
) void {
    const bindings = BranchStateOps.bindingsForSpace(state, space) orelse return;
    const seed_state = BranchStateOps.matchStateMut(state, space) orelse return;
    for (bindings, 0..) |binding, idx| {
        const expr_id: ExprId = binding orelse continue;
        if (idx >= seed_state.bindings.len) break;
        seed_state.replaceSeed(
            allocator,
            idx,
            .{ .exact = expr_id },
        );
    }
}
