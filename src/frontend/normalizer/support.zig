const std = @import("std");
const ExprId = @import("../expr.zig").ExprId;
const ResolvedRelation = @import("../rewrite_registry.zig").ResolvedRelation;

/// The line index a proof-free normalizer reports for a step it would have
/// emitted. Non-null, so code that needs "some proof" of a step still sees
/// one; never an index into any line list.
pub const proof_free_line: usize = std.math.maxInt(usize);

/// Comptime-known: whether `self` (a normalizer pointer) has a proof sink.
pub inline fn emitsProofs(self: anytype) bool {
    const Engine = @typeInfo(@TypeOf(self)).pointer.child;
    return comptime @FieldType(Engine, "lines") != void;
}

pub fn getExprSort(self: anytype, expr_id: ExprId) ?[]const u8 {
    const node = self.theorem.interner.node(expr_id);
    return switch (node.*) {
        .app => |app| if (app.term_id < self.env.terms.items.len)
            self.env.terms.items[app.term_id].ret_sort_name
        else
            null,
        .variable, .placeholder => self.theorem.currentLeafSortName(expr_id),
    };
}

pub fn resolveRelationForExpr(
    self: anytype,
    expr_id: ExprId,
) ?ResolvedRelation {
    const sort = getExprSort(self, expr_id) orelse return null;
    return self.registry.resolveRelation(self.env, sort);
}

/// The relation the engine's steps on `expr_id` are stated in. A proof-free
/// normalizer states nothing, so it does not need one: it gets a stand-in
/// that no proof-free step reads, and normalizes sorts the proof-producing
/// normalizer has to leave alone.
pub fn relationFor(self: anytype, expr_id: ExprId) ?ResolvedRelation {
    if (resolveRelationForExpr(self, expr_id)) |relation| return relation;
    if (emitsProofs(self)) return null;
    return .{
        .sort_name = getExprSort(self, expr_id) orelse "",
        .rel_term_id = undefined,
        .refl_id = undefined,
        .trans_id = undefined,
        .symm_id = undefined,
        .transport_id = null,
    };
}
