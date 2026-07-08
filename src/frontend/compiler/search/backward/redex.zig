//! Substitution/rewrite redex reduction for generated emit targets. Split out
//! of `backtrack.zig`: both the concrete (`emitGeneratedSlot`) and open
//! (`emitOpenTarget`) emit paths reduce a rule-instantiated target's rewrite
//! redexes to their computed form while leaving the surrounding ACUI context
//! structure byte-identical to the pool refs. These are pure functions over
//! `context`/`theorem`/`Canonicalizer` — they hold no search state.

const std = @import("std");
const types = @import("../types.zig");
const ExprId = @import("../../../expr.zig").ExprId;
const TheoremContext = @import("../../../expr.zig").TheoremContext;
const Canonicalizer = @import("../../../canonicalizer.zig").Canonicalizer;
const Context = types.Context;

/// Reduce only the substitution/rewrite redexes in `expr_id`, leaving the ACUI
/// context structure byte-identical to the pool refs.
///
/// A generation target built by instantiating a rule whose conclusion type is a
/// substitution redex (`[k/n] C` = `sb_ty …`, a `registry.rewrites_by_head`
/// head) must be reduced to its computed form (`Id Nat …`) for the emitted line:
/// the upstream ref/rule concludes the reduced form, not the redex, so without
/// this the generated slot is neither identity-equal to nor matchable against the
/// pool. A *full* `Canonicalizer.canonicalize` would also ACUI-re-associate the
/// context `join` (`@acui eq_raw_ctx_assoc _ emp _`, left-assoc parse) away from
/// the raw pool refs and break the positional `solveCorrespondence` readback. So
/// we recurse the structure (`nd`/`has_ty`/`join`/…) and invoke the canonicalizer
/// *only* on a subtree whose head is a rewrite head — reducing the redex without
/// disturbing the surrounding ACUI association.
///
/// The `containsRewriteRedex` pre-walk short-circuits the common case (no redex
/// present — e.g. the rewrite-free generation targets that dominate euclid)
/// before allocating a `Canonicalizer`, so this is a single cheap walk on every
/// non-substitution target and the canonicalizer cost is paid only when a redex
/// is actually present.
pub fn reduceRedexOnly(
    context: *const Context,
    theorem: *TheoremContext,
    expr_id: ExprId,
) anyerror!ExprId {
    // Whole-theory short-circuit: a theory with no `@rewrite` rules can never
    // hold a redex, so skip the structural walk entirely (O(1) for euclid etc.).
    if (context.registry.rewrites_by_head.count() == 0) return expr_id;
    if (!containsRewriteRedex(context, theorem, expr_id)) return expr_id;
    var canon = Canonicalizer.init(
        theorem.allocator,
        theorem,
        context.registry,
        context.env,
    );
    defer canon.cache.deinit();
    return reduceRedexOnlyInner(context, theorem, &canon, expr_id);
}

fn containsRewriteRedex(
    context: *const Context,
    theorem: *const TheoremContext,
    expr_id: ExprId,
) bool {
    return theorem.exprAny(expr_id, context, rewriteRedexHeadPred);
}

fn rewriteRedexHeadPred(
    context: *const Context,
    theorem: *const TheoremContext,
    expr_id: ExprId,
) bool {
    return switch (theorem.interner.node(expr_id).*) {
        .app => |app| context.registry.rewrites_by_head.contains(app.term_id),
        else => false,
    };
}

fn reduceRedexOnlyInner(
    context: *const Context,
    theorem: *TheoremContext,
    canon: *Canonicalizer,
    expr_id: ExprId,
) anyerror!ExprId {
    var term_id: u32 = undefined;
    var arg_count: usize = 0;
    switch (theorem.interner.node(expr_id).*) {
        .app => |a| {
            term_id = a.term_id;
            arg_count = a.args.len;
        },
        else => return expr_id,
    }
    // A rewrite-rooted subtree (e.g. `sb_ty …`) is the redex: reduce it to its
    // computed form. The canonicalizer reduces to fixpoint within this subtree
    // only; the surrounding context structure is left untouched.
    //
    // INVARIANT: a rewrite-rooted subtree must not itself contain an ACUI
    // structural combiner (`join`), or `canon.canonicalize` would re-associate it
    // and defeat the byte-identical-to-pool-refs contract this function exists to
    // protect. This holds by sort discipline in the current theories — the
    // rewrite heads are the substitution terms `sb_ty`/`sb_tm` (sorts `ty`/`tm`)
    // and the only ACUI combiner `join` is sort `ctx`; the `ty`/`tm` sub-grammar
    // takes no `ctx` argument, so no `join` can nest inside an `sb_*` redex. A
    // future commutative `@acui` operator over `ty`/`tm` appearing as an `sb_*`
    // argument would break this and must reduce structurally instead.
    if (context.registry.rewrites_by_head.contains(term_id)) {
        return canon.canonicalize(expr_id);
    }
    if (arg_count == 0) return expr_id;
    const args = try theorem.allocator.alloc(ExprId, arg_count);
    defer theorem.allocator.free(args);
    @memcpy(args, theorem.interner.node(expr_id).app.args);
    var changed = false;
    for (args) |*a| {
        const reduced = try reduceRedexOnlyInner(context, theorem, canon, a.*);
        if (reduced != a.*) changed = true;
        a.* = reduced;
    }
    if (!changed) return expr_id;
    return theorem.interner.internApp(term_id, args);
}
