const std = @import("std");
const ExprId = @import("../../expr.zig").ExprId;
const AcuiSupport = @import("../../acui_support.zig");
const ResolvedRelation = @import("../../rewrite_registry.zig").ResolvedRelation;
const ResolvedStructuralCombiner =
    @import("../../rewrite_registry.zig").ResolvedStructuralCombiner;
const AcuiBag = @import("../../acui_bag.zig");
const ChildNorm = @import("../child_norm.zig");
const ProofEmit = @import("../proof_emit.zig");
const Support = @import("../support.zig");
const Cover = @import("./cover.zig");
const Types = @import("../types.zig");

const NormalizeResult = Types.NormalizeResult;
const AcuiLeaf = Types.AcuiLeaf;

pub fn buildAcuiRewriteConversion(
    self: anytype,
    expr_id: ExprId,
    relation: ResolvedRelation,
    acui: ResolvedStructuralCombiner,
    leaves: []const AcuiLeaf,
) anyerror!NormalizeResult {
    var next_leaf: usize = 0;
    const replaced = try rewriteAcuiLeaves(
        self,
        expr_id,
        relation,
        acui,
        leaves,
        &next_leaf,
    );
    const rewritten = switch (self.theorem.interner.node(replaced.result_expr).*) {
        .app => |rewritten_app| try ChildNorm.normalizeChildren(
            self,
            replaced.result_expr,
            rewritten_app,
        ),
        .variable => NormalizeResult{
            .result_expr = replaced.result_expr,
            .conv_line_idx = null,
        },
        .placeholder => NormalizeResult{
            .result_expr = replaced.result_expr,
            .conv_line_idx = null,
        },
    };
    const exact = try Cover.normalizeStructuralExact(
        self,
        rewritten.result_expr,
        relation,
        acui,
    );
    const replaced_to_rewritten = try ProofEmit.composeTransitivity(
        self,
        relation,
        expr_id,
        replaced.result_expr,
        rewritten.result_expr,
        replaced.conv_line_idx,
        rewritten.conv_line_idx,
    );
    const proof = try ProofEmit.composeTransitivity(
        self,
        relation,
        expr_id,
        rewritten.result_expr,
        exact.result_expr,
        replaced_to_rewritten,
        exact.conv_line_idx,
    );
    return .{
        .result_expr = exact.result_expr,
        .conv_line_idx = proof,
    };
}

pub fn normalizeStructural(
    self: anytype,
    expr_id: ExprId,
    relation: ResolvedRelation,
    acui: ResolvedStructuralCombiner,
) anyerror!NormalizeResult {
    const node = self.theorem.interner.node(expr_id);
    const app = switch (node.*) {
        .app => |value| value,
        else => return .{ .result_expr = expr_id, .conv_line_idx = null },
    };
    if (app.term_id != acui.head_term_id or app.args.len != 2) {
        return .{ .result_expr = expr_id, .conv_line_idx = null };
    }

    var leaves = std.ArrayListUnmanaged(AcuiLeaf).empty;
    defer leaves.deinit(self.allocator);
    try collectAcuiLeaves(self, expr_id, acui.head_term_id, &leaves);

    const unit_expr = try ProofEmit.unitExpr(self, acui);
    try applySameSideAbsorption(self, leaves.items, unit_expr, relation, acui);

    var next_leaf: usize = 0;
    const replaced = try rewriteAcuiLeaves(
        self,
        expr_id,
        relation,
        acui,
        leaves.items,
        &next_leaf,
    );
    const rewritten = switch (self.theorem.interner.node(replaced.result_expr).*) {
        .app => |rewritten_app| try ChildNorm.normalizeChildren(
            self,
            replaced.result_expr,
            rewritten_app,
        ),
        .variable => NormalizeResult{
            .result_expr = replaced.result_expr,
            .conv_line_idx = null,
        },
        .placeholder => NormalizeResult{
            .result_expr = replaced.result_expr,
            .conv_line_idx = null,
        },
    };
    const exact = try Cover.normalizeStructuralExact(
        self,
        rewritten.result_expr,
        relation,
        acui,
    );
    const replaced_to_rewritten = try ProofEmit.composeTransitivity(
        self,
        relation,
        expr_id,
        replaced.result_expr,
        rewritten.result_expr,
        replaced.conv_line_idx,
        rewritten.conv_line_idx,
    );
    const proof = try ProofEmit.composeTransitivity(
        self,
        relation,
        expr_id,
        rewritten.result_expr,
        exact.result_expr,
        replaced_to_rewritten,
        exact.conv_line_idx,
    );
    return .{
        .result_expr = exact.result_expr,
        .conv_line_idx = proof,
    };
}

/// The normal form of a commutative bag, without its proof, when the
/// combiner heads no rewrite rule; null for any other expression. Each
/// member is normalized once, concrete members fold into equal defs, and one
/// sort orders the rest. The proof-producing path normalizes every prefix of
/// the spine and merges member by member, a pass over the bag for each
/// member; with no rule at the combiner the prefixes have no normal form of
/// their own to add, and both paths end at the same bag.
pub fn normalizeCommutativeBag(
    self: anytype,
    expr_id: ExprId,
) anyerror!?NormalizeResult {
    const app = switch (self.theorem.interner.node(expr_id).*) {
        .app => |value| value,
        else => return null,
    };
    if (app.args.len != 2) return null;
    const acui = try self.registry.resolveStructuralCombiner(
        self.env,
        app.term_id,
    ) orelse return null;
    if (acui.comm_id == null) return null;
    if (self.registry.getRewriteRules(acui.head_term_id).len != 0) return null;
    const relation = Support.relationFor(self, expr_id) orelse return null;

    const support = try self.support();
    var raw = std.ArrayListUnmanaged(ExprId).empty;
    defer raw.deinit(self.allocator);
    try support.collectLeaves(expr_id, acui.head_term_id, &raw);
    var members = std.ArrayListUnmanaged(ExprId).empty;
    defer members.deinit(self.allocator);
    for (raw.items) |leaf| {
        const member = (try self.normalize(leaf)).result_expr;
        try support.collectLeaves(member, acui.head_term_id, &members);
    }

    const leaves = try self.allocator.alloc(AcuiLeaf, members.items.len);
    defer self.allocator.free(leaves);
    for (members.items, leaves) |member, *leaf| leaf.* = .{
        .old_expr = member,
        .new_expr = member,
        .is_def = support.isDefBearing(member),
        .conv_line_idx = null,
    };
    const unit_expr = try ProofEmit.unitExpr(self, acui);
    try applySameSideAbsorption(self, leaves, unit_expr, relation, acui);

    members.clearRetainingCapacity();
    for (leaves) |leaf| {
        if (leaf.new_expr == unit_expr and acui.supportsLeftUnit()) continue;
        members.appendAssumeCapacity(leaf.new_expr);
    }
    const bag = try support.buildCanonicalAcuiFromItems(members.items, acui);
    // One member left, or none: its own normal form, not a bag's.
    if (!Cover.isAcuiExpr(self, bag, acui.head_term_id)) {
        return try self.normalize(bag);
    }
    return .{
        .result_expr = bag,
        .conv_line_idx = if (bag == expr_id) null else Support.proof_free_line,
    };
}

pub fn collectAcuiLeaves(
    self: anytype,
    expr_id: ExprId,
    head_term_id: u32,
    out: *std.ArrayListUnmanaged(AcuiLeaf),
) anyerror!void {
    const support = try self.support();
    // Sized once: the normalizer's allocator is the pipeline arena, which
    // keeps every buffer a growing list leaves behind.
    try out.ensureTotalCapacityPrecise(
        self.allocator,
        out.items.len + support.countLeaves(expr_id, head_term_id),
    );
    const Appender = struct {
        support: *AcuiSupport.Context,
        out: *std.ArrayListUnmanaged(AcuiLeaf),
        pub fn leaf(a: @This(), leaf_id: ExprId) void {
            a.out.appendAssumeCapacity(.{
                .old_expr = leaf_id,
                .new_expr = leaf_id,
                .is_def = a.support.isDefBearing(leaf_id),
                .conv_line_idx = null,
            });
        }
    };
    support.visitLeaves(
        expr_id,
        head_term_id,
        Appender{ .support = support, .out = out },
    );
}

/// The canonical bag of `acui` at `expr_id` with its members left as they
/// are: concrete members fold into equal def members, then the bag is
/// flattened, sorted and deduplicated by the combiner's laws.
pub fn canonicalizeBag(
    self: anytype,
    expr_id: ExprId,
    acui: ResolvedStructuralCombiner,
) anyerror!ExprId {
    const relation = Support.relationFor(self, expr_id) orelse return expr_id;
    var leaves = std.ArrayListUnmanaged(AcuiLeaf).empty;
    defer leaves.deinit(self.allocator);
    try collectAcuiLeaves(self, expr_id, acui.head_term_id, &leaves);
    const unit_expr = try ProofEmit.unitExpr(self, acui);
    try applySameSideAbsorption(self, leaves.items, unit_expr, relation, acui);

    const items = try self.allocator.alloc(ExprId, leaves.items.len);
    defer self.allocator.free(items);
    for (leaves.items, items) |leaf, *item| item.* = leaf.new_expr;
    const rebuilt = (try AcuiBag.Combiner.fromResolved(acui).build(
        self.theorem,
        items,
    )).?;
    return try (try self.support()).canonicalizeAcuiExact(rebuilt, acui);
}

/// Fold each concrete leaf into a def leaf of the same bag that equals it,
/// the first such def in leaf order, so equal members meet as one item.
pub fn applySameSideAbsorption(
    self: anytype,
    leaves: []AcuiLeaf,
    unit_expr: ExprId,
    relation: ResolvedRelation,
    acui: ResolvedStructuralCombiner,
) anyerror!void {
    for (leaves) |*leaf| {
        if (leaf.old_expr == unit_expr or leaf.is_def) continue;
        for (leaves) |owner| {
            if (!owner.is_def) continue;
            const proof = try Cover.buildConcreteToDefCoverProof(
                self,
                leaf.old_expr,
                owner.old_expr,
                relation,
                acui,
            ) orelse continue;
            leaf.new_expr = owner.old_expr;
            leaf.conv_line_idx = proof;
            break;
        }
    }
}

pub fn rewriteAcuiLeaves(
    self: anytype,
    expr_id: ExprId,
    relation: ResolvedRelation,
    acui: ResolvedStructuralCombiner,
    leaves: []const AcuiLeaf,
    next_leaf: *usize,
) anyerror!NormalizeResult {
    const node = self.theorem.interner.node(expr_id);
    switch (node.*) {
        .app => |app| {
            if (app.term_id == acui.head_term_id and app.args.len == 2) {
                const left = try rewriteAcuiLeaves(
                    self,
                    app.args[0],
                    relation,
                    acui,
                    leaves,
                    next_leaf,
                );
                const right = try rewriteAcuiLeaves(
                    self,
                    app.args[1],
                    relation,
                    acui,
                    leaves,
                    next_leaf,
                );
                const new_args = [_]ExprId{
                    left.result_expr,
                    right.result_expr,
                };
                const old_args = [_]ExprId{ app.args[0], app.args[1] };
                const new_expr = if (left.result_expr == app.args[0] and
                    right.result_expr == app.args[1])
                    expr_id
                else
                    try self.theorem.interner.internApp(
                        acui.head_term_id,
                        &new_args,
                    );
                return .{
                    .result_expr = new_expr,
                    .conv_line_idx = try ProofEmit.emitCongruenceLine(
                        self,
                        acui.head_term_id,
                        &old_args,
                        &new_args,
                        &[_]?usize{
                            left.conv_line_idx,
                            right.conv_line_idx,
                        },
                    ),
                };
            }
        },
        .variable => {},
        .placeholder => {},
    }

    if (next_leaf.* >= leaves.len) return error.MissingStructuralMetadata;
    const leaf = leaves[next_leaf.*];
    next_leaf.* += 1;
    if (leaf.old_expr != expr_id) return error.MissingStructuralMetadata;
    return .{
        .result_expr = leaf.new_expr,
        .conv_line_idx = if (leaf.conv_line_idx) |idx|
            idx
        else
            try ProofEmit.emitTransparentRelationProof(
                self,
                relation,
                leaf.old_expr,
                leaf.new_expr,
            ),
    };
}
