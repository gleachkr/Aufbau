const types = @import("./types.zig");
const Goal = types.Goal;
const ApplyCandidate = types.ApplyCandidate;

pub fn applyCandidateLessThan(
    _: void,
    lhs: ApplyCandidate,
    rhs: ApplyCandidate,
) bool {
    return lhs.declaration_order < rhs.declaration_order;
}
