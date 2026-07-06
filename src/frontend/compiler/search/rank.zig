const types = @import("./types.zig");
const Goal = types.Goal;
const ApplyCandidate = types.ApplyCandidate;
const ExactCandidate = types.ExactCandidate;

pub fn exactCandidateLessThan(
    _: void,
    lhs: ExactCandidate,
    rhs: ExactCandidate,
) bool {
    if (lhs.declaration_order != rhs.declaration_order) {
        return lhs.declaration_order < rhs.declaration_order;
    }
    if (lhs.refs.len != rhs.refs.len) return lhs.refs.len < rhs.refs.len;
    return lhs.reference_rank < rhs.reference_rank;
}

pub fn applyCandidateLessThan(
    _: void,
    lhs: ApplyCandidate,
    rhs: ApplyCandidate,
) bool {
    return lhs.declaration_order < rhs.declaration_order;
}

pub fn isBroadWholeLineHole(goal: Goal) bool {
    return switch (goal) {
        .holey => |expr| expr.* == .hole,
        else => false,
    };
}
