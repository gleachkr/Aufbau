//! The search's handle on `acui_bag.zig`: the same bag reading, with the
//! combiner looked up from the search context by its head.

const types = @import("../types.zig");
const AcuiBag = @import("../../../acui_bag.zig");
const ExprId = @import("../../../expr.zig").ExprId;
const TheoremContext = @import("../../../expr.zig").TheoremContext;
const TemplateExpr = @import("../../../rules.zig").TemplateExpr;
const Context = types.Context;

pub const capacity = AcuiBag.capacity;
pub const Law = AcuiBag.Law;
pub const Combiner = AcuiBag.Combiner;
pub const ExprBag = AcuiBag.ExprBag;
pub const TemplateBag = AcuiBag.TemplateBag;
pub const rightFold = AcuiBag.rightFold;

/// The `@acui` combiner headed by `head_id`, or null when it is not one.
pub fn combinerOf(context: *const Context, head_id: u32) ?Combiner {
    return Combiner.of(context.registry, context.env, head_id);
}

/// The law of combiner `head_id`, or null when it is not an `@acui` head.
pub fn lawOf(context: *const Context, head_id: u32) ?Law {
    return AcuiBag.lawOf(context.registry, head_id);
}

/// Whether combiner `head_id` is commutative (false when it is not `@acui`).
pub fn isCommutative(context: *const Context, head_id: u32) bool {
    const law = lawOf(context, head_id) orelse return false;
    return law.isCommutative();
}

/// The unit term of combiner `head_id`, or null when it is not an `@acui` head
/// or its unit does not resolve.
pub fn unitOf(context: *const Context, head_id: u32) ?u32 {
    const combiner = combinerOf(context, head_id) orelse return null;
    return combiner.unit;
}

/// Whether `expr` is the unit of combiner `head_id`.
pub fn isUnitOf(
    context: *const Context,
    theorem: *const TheoremContext,
    head_id: u32,
    expr: ExprId,
) bool {
    const combiner = combinerOf(context, head_id) orelse return false;
    return combiner.isUnit(theorem, expr);
}

/// `Combiner.flatten` for head `head_id`. A head that is not an `@acui`
/// combiner still splices its own applications, with no unit.
pub fn flatten(
    context: *const Context,
    theorem: *const TheoremContext,
    head_id: u32,
    expr: ExprId,
) ?ExprBag {
    return anyCombiner(context, head_id).flatten(theorem, expr);
}

/// `Combiner.flattenTemplate` for head `head_id`.
pub fn flattenTemplate(
    context: *const Context,
    head_id: u32,
    template: TemplateExpr,
) ?TemplateBag {
    return anyCombiner(context, head_id).flattenTemplate(template);
}

/// `Combiner.build` for head `head_id`.
pub fn build(
    context: *const Context,
    theorem: *TheoremContext,
    head_id: u32,
    members: []const ExprId,
) error{ OutOfMemory, TooManyTheoremExprs }!?ExprId {
    return anyCombiner(context, head_id).build(theorem, members);
}

fn anyCombiner(context: *const Context, head_id: u32) Combiner {
    return combinerOf(context, head_id) orelse
        .{ .head = head_id, .unit = null, .law = .sequence };
}
