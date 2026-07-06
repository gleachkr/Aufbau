const std = @import("std");
const ExprId = @import("../expr.zig").ExprId;
const DefOps = @import("../def_ops.zig");
const types = @import("./types.zig");
const BranchState = types.BranchState;
const BranchStateOps = @import("./branch_state.zig");

pub fn syncFromSession(
    allocator: std.mem.Allocator,
    state: *BranchState,
    session: *DefOps.RuleMatchSession,
) anyerror!void {
    const view_bindings = state.view_bindings orelse return;
    // The snapshot is allocated on the session's (real) allocator. We keep only
    // a clone of the seed state on `allocator` so the BranchState owns all of
    // its memory from a single allocator (the per-solve arena), then free the
    // whole export back on the session allocator.
    var snapshot = try session.exportOptionalBindingSnapshot();
    defer snapshot.deinit(session.shared.allocator);

    for (snapshot.bindings, 0..) |binding, idx| {
        if (idx >= view_bindings.len) break;
        if (binding) |expr_id| view_bindings[idx] = expr_id;
    }

    const cloned = try BranchStateOps.cloneMatchSeedState(
        allocator,
        &snapshot.seed_state,
    );

    if (state.view_match_state) |*old_state| {
        old_state.deinit(allocator);
    }
    state.view_match_state = cloned;
}

pub fn syncConcreteBindingsIntoSeedState(
    allocator: std.mem.Allocator,
    state: *BranchState,
) void {
    const view_bindings = state.view_bindings orelse return;
    const seed_state = if (state.view_match_state) |*match_state|
        match_state
    else
        return;
    for (view_bindings, 0..) |binding, idx| {
        const expr_id: ExprId = binding orelse continue;
        if (idx >= seed_state.bindings.len) break;
        seed_state.replaceSeed(
            allocator,
            idx,
            .{ .exact = expr_id },
        );
    }
}
