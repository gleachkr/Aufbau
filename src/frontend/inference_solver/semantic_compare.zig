const StructuralCongruence = @import("./congruence.zig");
const ExprId = @import("../expr.zig").ExprId;
const types = @import("./types.zig");
const StructuralProfile = types.StructuralProfile;

pub fn commonStructuralTarget(
    self: anytype,
    lhs: ExprId,
    rhs: ExprId,
) anyerror!?ExprId {
    const common = try self.canonicalizer.buildCommonTarget(lhs, rhs) orelse {
        return null;
    };
    return common.target_expr;
}

pub fn bindingCompatible(
    self: anytype,
    lhs: ExprId,
    rhs: ExprId,
) anyerror!bool {
    if (lhs == rhs) return true;
    try self.checkBudget();
    const lhs_canon = try self.canonicalizer.canonicalize(lhs);
    const rhs_canon = try self.canonicalizer.canonicalize(rhs);
    if (lhs_canon == rhs_canon) return true;
    if (!try meetsOtherForms(self, lhs_canon) and !try meetsOtherForms(self, rhs_canon)) {
        return false;
    }
    if ((try commonStructuralTarget(self, lhs_canon, rhs_canon)) != null) {
        return true;
    }
    return try structuralCongruenceCompatible(self, lhs_canon, rhs_canon);
}

/// Whether a canonical form can be `bindingCompatible` with a different
/// canonical form. Past their normal forms, two exprs meet only through a
/// definition: the ACUI laws and congruence are settled by normalizing,
/// and hash-consing makes distinct ids distinct terms.
pub fn meetsOtherForms(self: anytype, canonical: ExprId) anyerror!bool {
    const support = try self.canonicalizer.support();
    return support.isDefBearing(canonical);
}

fn structuralCongruenceCompatible(
    self: anytype,
    lhs: ExprId,
    rhs: ExprId,
) anyerror!bool {
    const support = try self.canonicalizer.support();
    const combiner = try support.sharedStructuralCombiner(lhs, rhs) orelse {
        return false;
    };
    return try StructuralCongruence.expressionsEqual(
        self,
        lhs,
        rhs,
        StructuralProfile.init(combiner),
    );
}

pub fn sameRuleBindingsCompatible(
    self: anytype,
    lhs: []const ?ExprId,
    rhs: []const ?ExprId,
) anyerror!bool {
    return try sameBindingsCompatible(self, lhs, rhs);
}

pub fn sameBindingsCompatible(
    self: anytype,
    lhs: []const ?ExprId,
    rhs: []const ?ExprId,
) anyerror!bool {
    if (lhs.len != rhs.len) return false;
    for (lhs, rhs) |l, r| {
        if (l == null or r == null) {
            if (l != r) return false;
            continue;
        }
        if (!try bindingCompatible(self, l.?, r.?)) return false;
    }
    return true;
}
