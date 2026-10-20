const AcuiBag = @import("../acui_bag.zig");
const ExprId = @import("../expr.zig").ExprId;
const ResolvedRelation = @import("../rewrite_registry.zig").ResolvedRelation;
const Support = @import("./support.zig");
const Core = @import("./core.zig");
const Acui = @import("./acui.zig");
const Cover = @import("./acui/cover.zig");
const NonAcuiTarget = @import("./non_acui_target.zig");
const ProofEmit = @import("./proof_emit.zig");
const Types = @import("./types.zig");

const CommonTargetResult = Types.CommonTargetResult;

pub fn buildCommonTarget(
    self: anytype,
    lhs: ExprId,
    rhs: ExprId,
) anyerror!?CommonTargetResult {
    return try buildCommonTargetInside(self, null, lhs, rhs);
}

/// A common target of two members of one bag of `head_term_id`:
/// `buildCommonTarget` short of comparing them as bags of that combiner.
/// Members that are bags of another combiner still meet as bags.
pub fn buildMemberCommonTarget(
    self: anytype,
    head_term_id: u32,
    lhs: ExprId,
    rhs: ExprId,
) anyerror!?CommonTargetResult {
    return try buildCommonTargetInside(self, head_term_id, lhs, rhs);
}

fn buildCommonTargetInside(
    self: anytype,
    enclosing_head: ?u32,
    lhs: ExprId,
    rhs: ExprId,
) anyerror!?CommonTargetResult {
    if (lhs == rhs) return sameTarget(lhs);
    if (try buildDefCommonTarget(self, lhs, rhs)) |result| return result;
    if (try Cover.sharedStructuralCombiner(self, lhs, rhs)) |acui| {
        // Members of a bag of this combiner would meet again as one-member
        // bags of it (the combiner falls back to the sort's) and be paired
        // here once more, without end.
        if (acui.head_term_id != enclosing_head) {
            if (try Acui.buildAcuiCommonTarget(self, lhs, rhs)) |result| {
                return result;
            }
            // Two bags of a commutative combiner have just been compared
            // member by member, every member against every other.
            // Descending through the spine pairs the same members in one
            // fixed order, and repeats the bag comparison on every suffix on
            // the way down.
            const spine = AcuiBag.Spine.raw(acui.head_term_id);
            if (acui.comm_id != null and
                spine.isBag(self.theorem, lhs) and
                spine.isBag(self.theorem, rhs))
            {
                return null;
            }
        }
    }
    return try NonAcuiTarget.buildNonAcuiCommonTarget(self, lhs, rhs);
}

fn sameTarget(expr_id: ExprId) CommonTargetResult {
    return .{
        .target_expr = expr_id,
        .lhs_conv_line_idx = null,
        .rhs_conv_line_idx = null,
    };
}

fn buildDefCommonTarget(
    self: anytype,
    lhs: ExprId,
    rhs: ExprId,
) anyerror!?CommonTargetResult {
    // The two def-unfolding steps can only make progress through a
    // concrete def: `compareTransparent` on distinct interned exprs needs
    // a def-headed subterm to get past a structural mismatch, and
    // `instantiateDefTowardExpr` bails unless its expr is def-headed.
    // Hash-consing makes "distinct ids, no def anywhere" a proof that both
    // return null, so skip their per-pair cache probes entirely.
    const support = try self.support();
    if (!support.isDefBearing(lhs) and !support.isDefBearing(rhs)) return null;
    if (try buildDirectTransparentCommonTarget(self, lhs, rhs)) |direct| {
        return direct;
    }
    return try buildSemanticDefCommonTarget(self, lhs, rhs);
}

pub fn buildDirectTransparentCommonTarget(
    self: anytype,
    lhs: ExprId,
    rhs: ExprId,
) anyerror!?CommonTargetResult {
    const relation = Support.relationFor(self, lhs) orelse return null;
    const def_ops = try self.defOps();

    if ((try def_ops.compareTransparent(lhs, rhs)) != null) {
        return .{
            .target_expr = rhs,
            .lhs_conv_line_idx = try ProofEmit.emitTransparentRelationProof(
                self,
                relation,
                lhs,
                rhs,
            ),
            .rhs_conv_line_idx = null,
        };
    }
    if ((try def_ops.compareTransparent(rhs, lhs)) != null) {
        return .{
            .target_expr = lhs,
            .lhs_conv_line_idx = null,
            .rhs_conv_line_idx = try ProofEmit.emitTransparentRelationProof(
                self,
                relation,
                rhs,
                lhs,
            ),
        };
    }
    return null;
}

pub fn buildSemanticDefCommonTarget(
    self: anytype,
    lhs: ExprId,
    rhs: ExprId,
) anyerror!?CommonTargetResult {
    const relation = Support.relationFor(self, lhs) orelse return null;
    if (try buildSemanticCommonTargetFromDef(self, lhs, rhs, relation)) |result| {
        return result;
    }
    if (try buildSemanticCommonTargetFromDef(self, rhs, lhs, relation)) |result| {
        return .{
            .target_expr = result.target_expr,
            .lhs_conv_line_idx = result.rhs_conv_line_idx,
            .rhs_conv_line_idx = result.lhs_conv_line_idx,
        };
    }
    return null;
}

pub fn buildSemanticCommonTargetFromDef(
    self: anytype,
    def_expr: ExprId,
    other_expr: ExprId,
    relation: ResolvedRelation,
) anyerror!?CommonTargetResult {
    const def_ops = try self.defOps();
    const witness = if (self.hidden_witness_provider) |provider|
        try def_ops.instantiateDefTowardExprWithProvider(
            def_expr,
            other_expr,
            provider,
        )
    else
        try def_ops.instantiateDefTowardExpr(
            def_expr,
            other_expr,
        );
    const concrete_witness = witness orelse return null;
    const def_to_witness = try ProofEmit.emitTransparentRelationProof(
        self,
        relation,
        def_expr,
        concrete_witness,
    );
    const norm_witness = try Core.normalize(self, concrete_witness);
    if (norm_witness.result_expr == other_expr) {
        return .{
            .target_expr = other_expr,
            .lhs_conv_line_idx = try ProofEmit.composeTransitivity(
                self,
                relation,
                def_expr,
                concrete_witness,
                other_expr,
                def_to_witness,
                norm_witness.conv_line_idx,
            ),
            .rhs_conv_line_idx = null,
        };
    }

    const common = try buildCommonTarget(
        self,
        norm_witness.result_expr,
        other_expr,
    ) orelse return null;
    const witness_to_common = try ProofEmit.composeTransitivity(
        self,
        relation,
        concrete_witness,
        norm_witness.result_expr,
        common.target_expr,
        norm_witness.conv_line_idx,
        common.lhs_conv_line_idx,
    );
    return .{
        .target_expr = common.target_expr,
        .lhs_conv_line_idx = try ProofEmit.composeTransitivity(
            self,
            relation,
            def_expr,
            concrete_witness,
            common.target_expr,
            def_to_witness,
            witness_to_common,
        ),
        .rhs_conv_line_idx = common.rhs_conv_line_idx,
    };
}
