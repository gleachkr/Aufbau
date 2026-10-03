const types = @import("../types.zig");
const ExprId = @import("../../../expr.zig").ExprId;
const TheoremContext = @import("../../../expr.zig").TheoremContext;
const TemplateExpr = @import("../../../rules.zig").TemplateExpr;
const Context = types.Context;
const head_class = @import("../../../head_class.zig");
pub const HeadClass = head_class.HeadClass;

/// How conversion can treat `head` (see `head_class.HeadClass`).
pub fn headClass(context: *const Context, head: u32) HeadClass {
    return head_class.classify(context.env, context.registry, head);
}

/// No conversion changes `head`: a primitive term or a bodiless def. Any other
/// head may unfold, rearrange, or reduce, so a template carrying it cannot be
/// matched syntactically (`r : [y/x][q/refl A x] C` against the reduced
/// `refl A x : Id A x x`); such a pair is left to the validator's normalizing
/// matcher.
pub fn isRigidHead(context: *const Context, head: u32) bool {
    return headClass(context, head) == .rigid;
}

/// Does `h(a) ≡ h(b)` force the args at `arg_idx` equal? A lockstep walk may
/// compare, pin, or descend into only such args. See
/// `head_class.argDetermined`.
pub fn argDetermined(context: *const Context, head: u32, arg_idx: usize) bool {
    return head_class.argDetermined(context.env, context.registry, head, arg_idx);
}

pub fn templateNeedsSemantic(
    context: *const Context,
    template: TemplateExpr,
) bool {
    return switch (template) {
        .binder => false,
        .app => |app| blk: {
            if (!isRigidHead(context, app.term_id)) break :blk true;
            for (app.args) |arg| {
                if (templateNeedsSemantic(context, arg)) break :blk true;
            }
            break :blk false;
        },
    };
}

pub fn exprNeedsSemantic(
    context: *const Context,
    theorem: *const TheoremContext,
    expr_id: ExprId,
) bool {
    const node = theorem.interner.node(expr_id);
    return switch (node.*) {
        .variable, .placeholder => false,
        .app => |app| blk: {
            if (!isRigidHead(context, app.term_id)) break :blk true;
            for (app.args) |arg| {
                if (exprNeedsSemantic(context, theorem, arg)) break :blk true;
            }
            break :blk false;
        },
    };
}

/// Strict `matchTemplate` decides `expr` exactly: no head a conversion can
/// change, and no placeholder. A meta may still become, and a def-unfold
/// dummy may still be renamed to, a different value.
pub fn exprStrictlyComparable(
    context: *const Context,
    theorem: *const TheoremContext,
    expr_id: ExprId,
) bool {
    if (exprNeedsSemantic(context, theorem, expr_id)) return false;
    if (theorem.theorem_placeholders.items.len == 0) return true;
    return !theorem.containsPlaceholder(expr_id);
}

/// Strict `matchTemplate` of `template` under `bindings` decides exactly: the
/// template needs no semantics and every bound value it mentions is
/// `exprStrictlyComparable`.
pub fn templateStrictlyComparable(
    context: *const Context,
    theorem: *const TheoremContext,
    template: TemplateExpr,
    bindings: []const ?ExprId,
) bool {
    return switch (template) {
        .binder => |idx| blk: {
            if (idx >= bindings.len) break :blk true;
            const bound = bindings[idx] orelse break :blk true;
            break :blk exprStrictlyComparable(context, theorem, bound);
        },
        .app => |app| blk: {
            if (!isRigidHead(context, app.term_id)) break :blk false;
            for (app.args) |arg| {
                if (!templateStrictlyComparable(context, theorem, arg, bindings)) break :blk false;
            }
            break :blk true;
        },
    };
}

pub fn bindingsNeedSemantic(
    context: *const Context,
    theorem: *const TheoremContext,
    bindings: []const ?ExprId,
) bool {
    for (bindings) |maybe_expr| {
        const expr_id = maybe_expr orelse continue;
        if (exprNeedsSemantic(context, theorem, expr_id)) return true;
    }
    return false;
}
