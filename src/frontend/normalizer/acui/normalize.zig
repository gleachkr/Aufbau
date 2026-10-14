const std = @import("std");
const ExprId = @import("../../expr.zig").ExprId;
const TheoremContext = @import("../../expr.zig").TheoremContext;
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
/// combiner heads no rewrite rule and no member folds into a def; null for
/// any other expression. Each member is normalized once and one sort orders
/// them. The proof-producing path normalizes every prefix of the spine and
/// merges member by member, a pass over the bag for each member; with no
/// rule at the combiner the prefixes have no normal form of their own to
/// add, and both paths end at the same bag. A bag with a fold takes the
/// prefix path: there the fold meets the combiner's laws member by member,
/// as when a def is itself the unit.
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
    const spine = AcuiBag.Spine.raw(acui.head_term_id);
    var raw = std.ArrayListUnmanaged(ExprId).empty;
    defer raw.deinit(self.allocator);
    try spine.collect(self.allocator, self.theorem, expr_id, &raw);
    var members = std.ArrayListUnmanaged(ExprId).empty;
    defer members.deinit(self.allocator);
    for (raw.items) |leaf| {
        const member = (try self.normalize(leaf)).result_expr;
        try spine.collect(self.allocator, self.theorem, member, &members);
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
    for (leaves) |leaf| {
        if (leaf.new_expr != leaf.old_expr) return null;
    }

    const bag = try support.buildCanonicalAcuiFromItems(members.items, acui);
    // One member left, or none: its own normal form, not a bag's.
    if (!spine.isBag(self.theorem, bag)) {
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
    const spine = AcuiBag.Spine.raw(head_term_id);
    // Sized once: the normalizer's allocator is the pipeline arena, which
    // keeps every buffer a growing list leaves behind.
    try out.ensureTotalCapacityPrecise(
        self.allocator,
        out.items.len + spine.count(self.theorem, expr_id),
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
    spine.visit(self.theorem, expr_id, Appender{ .support = support, .out = out });
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

/// Fold each leaf into the least def leaf of the same bag that equals it,
/// so equal members meet as one item whatever their order or grouping: a
/// concrete leaf, and a def leaf with a lesser twin (`i2 a` into `i1 a`).
pub fn applySameSideAbsorption(
    self: anytype,
    leaves: []AcuiLeaf,
    unit_expr: ExprId,
    relation: ResolvedRelation,
    acui: ResolvedStructuralCombiner,
) anyerror!void {
    var owners = std.ArrayListUnmanaged(ExprId).empty;
    defer owners.deinit(self.allocator);
    for (leaves) |leaf| {
        if (!leaf.is_def) continue;
        if (std.mem.indexOfScalar(ExprId, owners.items, leaf.old_expr) != null) continue;
        try owners.append(self.allocator, leaf.old_expr);
    }
    const theorem: *const TheoremContext = self.theorem;
    std.mem.sort(ExprId, owners.items, theorem, AcuiSupport.exprIdLessThan);
    for (leaves) |*leaf| {
        if (leaf.old_expr == unit_expr) continue;
        for (owners.items) |owner| {
            // A def leaf folds only into a lesser def.
            if (owner == leaf.old_expr) break;
            const proof = if (leaf.is_def) blk: {
                // Two defs meet when they unfold alike, which the verifier
                // checks for the one transport line.
                if (try (try self.defOps()).compareTransparent(leaf.old_expr, owner) == null) continue;
                break :blk try ProofEmit.emitTransparentRelationProof(
                    self,
                    relation,
                    leaf.old_expr,
                    owner,
                );
            } else try Cover.buildConcreteToDefCoverProof(
                self,
                leaf.old_expr,
                owner,
                relation,
                acui,
            ) orelse continue;
            leaf.new_expr = owner;
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
    if (AcuiBag.Spine.raw(acui.head_term_id).split(self.theorem, expr_id)) |old_args| {
        const left = try rewriteAcuiLeaves(self, old_args[0], relation, acui, leaves, next_leaf);
        const right = try rewriteAcuiLeaves(self, old_args[1], relation, acui, leaves, next_leaf);
        const new_args = [_]ExprId{ left.result_expr, right.result_expr };
        const new_expr = if (left.result_expr == old_args[0] and
            right.result_expr == old_args[1])
            expr_id
        else
            try self.theorem.interner.internApp(acui.head_term_id, &new_args);
        return .{
            .result_expr = new_expr,
            .conv_line_idx = try ProofEmit.emitCongruenceLine(
                self,
                acui.head_term_id,
                &old_args,
                &new_args,
                &[_]?usize{ left.conv_line_idx, right.conv_line_idx },
            ),
        };
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
