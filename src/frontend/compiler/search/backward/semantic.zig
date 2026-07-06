const types = @import("../types.zig");
const ExprId = @import("../../../expr.zig").ExprId;
const TheoremContext = @import("../../../expr.zig").TheoremContext;
const TemplateExpr = @import("../../../rules.zig").TemplateExpr;
const Context = types.Context;

pub fn termNeedsSemantic(context: *const Context, term_id: u32) bool {
    if (!context.env.hasAvailableTerm(term_id)) return true;
    if (context.registry.acui_by_head.contains(term_id)) return true;
    // A `@rewrite` LHS head (e.g. `sb_ty`/`sb_tm` substitution) can reduce to a
    // different head, so a template carrying it cannot be matched syntactically
    // against a ref written in reduced form (`r : [y/x][q/refl A x] C` vs the
    // concrete `refl A x : Id A x x`). Treat it as "needs semantic" so the hyp
    // matcher classifies the pair `.unknown` rather than `.mismatch` and defers
    // to `tryCandidate`'s real normalized matcher. Symmetric to shape.zig's
    // reducible-head widening: a head conversion can change is not decisive.
    if (context.registry.rewrites_by_head.contains(term_id)) return true;
    const term = context.env.terms.items[term_id];
    return term.available and term.is_def and term.body != null;
}

pub fn templateNeedsSemantic(
    context: *const Context,
    template: TemplateExpr,
) bool {
    return switch (template) {
        .binder => false,
        .app => |app| blk: {
            if (termNeedsSemantic(context, app.term_id)) break :blk true;
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
            if (termNeedsSemantic(context, app.term_id)) break :blk true;
            for (app.args) |arg| {
                if (exprNeedsSemantic(context, theorem, arg)) break :blk true;
            }
            break :blk false;
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
