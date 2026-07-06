const types = @import("../types.zig");
const ExprId = @import("../../../expr.zig").ExprId;
const ExprNode = @import("../../../expr.zig").ExprNode;
const TheoremContext = @import("../../../expr.zig").TheoremContext;
const TemplateExpr = @import("../../../rules.zig").TemplateExpr;
const ArgInfo = @import("../../../parse_recovery.zig").ArgInfo;
const Context = types.Context;

const acui = @import("./acui.zig");
const semantic = @import("./semantic.zig");

const termNeedsSemantic = semantic.termNeedsSemantic;
pub const templateNeedsSemantic = semantic.templateNeedsSemantic;
pub const exprNeedsSemantic = semantic.exprNeedsSemantic;
pub const bindingsNeedSemantic = semantic.bindingsNeedSemantic;
// Decide whether `source` provably cannot be `pattern` with the `@recover`
// hole replaced by a single witness term — accounting for the reconciliation
// the full validator is still allowed to perform.
//
// The validator's recover only unfolds transparent defs and canonicalizes
// ACUI terms before re-running the structural comparison. Neither operation
// can change a *rigid* head (an available, non-def, non-ACUI term) into a
// different one. So the only divergence we may treat as a hard mismatch is
// two app nodes at corresponding positions whose heads differ and are *both*
// rigid (e.g. `∧` vs `=`). Any other shape — a def/ACUI head that could
// unfold, a variable/placeholder that could be a wrapper or identity witness,
// or a position sitting at the hole — is left to the validator (return
// false). This keeps the guard sound: it never drops a ref the validator
// would accept, only ones whose rigid logical skeleton already clashes.
pub fn recoverDefiniteMismatch(
    context: *const Context,
    theorem: *const TheoremContext,
    source: ExprId,
    pattern: ExprId,
    hole: ExprId,
) bool {
    if (pattern == hole) return false;
    if (source == pattern) return false;
    const pattern_node = theorem.interner.node(pattern);
    const source_node = theorem.interner.node(source);
    const pattern_app = switch (pattern_node.*) {
        .placeholder => return false,
        // A non-hole pattern variable is a fixed ground leaf: the recover law
        // never instantiates it (only the hole becomes the witness), so the
        // source must equal it verbatim at this position. When the source is a
        // *distinct* variable leaf it is a hard mismatch. `source != pattern`
        // (checked above) is ExprId inequality, and within one interner a
        // variable id is a unique allocation — `theorem_var` ids are stable,
        // `dummy_var` ids come from the monotonic `next_dummy_id` counter, and
        // the two kinds are disjoint — so distinct ids are distinct variables
        // and no def-unfold/ACUI step can reconcile two ground leaves. (Source
        // apps/placeholders could still reduce/instantiate — no opinion.)
        .variable => return switch (source_node.*) {
            .variable => true,
            else => false,
        },
        .app => |app| app,
    };
    const source_app = switch (source_node.*) {
        // A placeholder is a genuinely unfilled position; later matching may
        // instantiate it to an app that agrees with the pattern, so we hold no
        // opinion here (unlike the validator, which only sees it post-fill).
        .placeholder => return false,
        // A bound variable is a ground, irreducible leaf — both `theorem_var`
        // and `dummy_var` key the search index as nullary atoms, and the
        // validator's recover never unfolds a leaf into an app. So when the
        // pattern's head resolves to a rigid root (no def-unfold/ACUI step can
        // collapse that app to a bare leaf), the ref provably can't be the
        // pattern. This mirrors `recoverBindingCandidate`, which returns
        // `RecoverStructureMismatch` for exactly this pattern-app/source-var
        // shape (derived_bindings.zig:625).
        .variable => return resolveRigidHead(context, pattern_app.term_id) != null,
        .app => |app| app,
    };
    if (source_app.term_id != pattern_app.term_id) {
        // Heads differ. Resolve each through any transparent-def head chain (the
        // validator's recover unfolds defs before comparing) to its rigid root.
        // If both resolve to *distinct* rigid roots, no unfolding/canonicalization
        // can reconcile them, so the ref provably can't be the pattern — e.g. a
        // ref `has_preimage(…)` unfolds to `∃ …` (head `ex`, rigid) which clashes
        // with a pattern `∧`. When either side resolves through an ACUI combiner
        // or a binder-rooted body, or to the *same* root, we hold no opinion.
        const source_head = resolveRigidHead(context, source_app.term_id) orelse
            return false;
        const pattern_head = resolveRigidHead(context, pattern_app.term_id) orelse
            return false;
        return source_head != pattern_head;
    }
    if (source_app.args.len != pattern_app.args.len) return false;
    for (source_app.args, pattern_app.args) |source_arg, pattern_arg| {
        if (recoverDefiniteMismatch(
            context,
            theorem,
            source_arg,
            pattern_arg,
            hole,
        )) return true;
    }
    return false;
}

// A term whose head the validator's recover reconciliation can never rewrite
// away: available, not a transparent def, not an ACUI combiner. This is the
// negation of `termNeedsSemantic`, named for the role it plays here.
fn isRigidTerm(context: *const Context, term_id: u32) bool {
    return !termNeedsSemantic(context, term_id);
}

// True when the node is an application whose head term can be rewritten away
// by a `@rewrite` rule (so its head is not a reliable rigid key). Used to
// withhold a definite-mismatch verdict, mirroring the reducible-head guards in
// shape.zig and `termNeedsSemantic`.
fn headIsReducibleNode(context: *const Context, node: *const ExprNode) bool {
    return switch (node.*) {
        .app => |app| context.registry.rewrites_by_head.contains(app.term_id),
        else => false,
    };
}

// Resolve the outermost RIGID head a term presents after the validator's
// def-unfolding alignment: follow transparent-def heads through their body
// templates until reaching a non-def app head (the rigid root). Head-only, so it
// neither interns nor inspects dummy-bearing arguments — a head term's identity
// is independent of the def's dummies, so unfolding binder-defs here is sound
// (unlike the deep arg comparison `transparentDefBody` must gate against).
// Returns null when the chain hits an ACUI combiner (canonicalization could
// rewrite it), a `@rewrite` LHS head (could rewrite to a different head), an
// unavailable term, or a body rooted at a binder rather than an app — i.e. cases
// where we hold no opinion.
pub fn rigidHeadMismatch(
    context: *const Context,
    a_term_id: u32,
    b_term_id: u32,
) bool {
    const a_head = resolveRigidHead(context, a_term_id) orelse return false;
    const b_head = resolveRigidHead(context, b_term_id) orelse return false;
    return a_head != b_head;
}

/// Public view of `resolveRigidHead`: the outermost RIGID head `term_id` presents
/// after transparent-def head-chain unfolding, or null when the chain bottoms out
/// on an ACUI / `@rewrite` / unavailable / binder-rooted-body head (no stable
/// rigid root). Read-only and head-only — it never interns, mints placeholders,
/// or inspects dummy-bearing arguments. The key invariant for callers reasoning
/// about the validator's preprocessing: that preprocessing (transparent-def
/// unfold + ACUI/`@rewrite` canonicalize) preserves this head whenever it is
/// non-null, because resolveRigidHead returns null on exactly the heads
/// canonicalization could rewrite.
pub fn rigidHeadOf(context: *const Context, term_id: u32) ?u32 {
    return resolveRigidHead(context, term_id);
}

fn resolveRigidHead(context: *const Context, term_id: u32) ?u32 {
    var current = term_id;
    var depth: usize = 0;
    while (depth < max_def_unfold_depth) : (depth += 1) {
        if (context.registry.acui_by_head.contains(current)) return null;
        // A `@rewrite` LHS head can rewrite to a *different* head, so it is not a
        // reliable rigid root — even though it may be an ordinary (non-def,
        // available) term. Treat it as non-rigid so a head clash against it is
        // never decisive. (Callers that hit the immediate head guard this too;
        // doing it here also covers a def whose body unfolds onto a rewrite head.)
        if (context.registry.rewrites_by_head.contains(current)) return null;
        if (!context.env.hasAvailableTerm(current)) return null;
        const term = context.env.terms.items[current];
        if (!term.available) return null;
        if (!term.is_def) return current;
        const body = term.body orelse return null;
        switch (body) {
            .app => |app| current = app.term_id,
            .binder => return null,
        }
    }
    return null;
}

// True when `term_id` heads a structural combiner registered with `@acui` AND
// that declaration includes commutativity. Multiset/bag reasoning over the
// combiner's arguments is only sound when this holds.
fn acuiIsCommutative(context: *const Context, term_id: u32) bool {
    const combiner = context.registry.acui_by_head.get(term_id) orelse return false;
    // `comm_name` is the declaration-time signal (null iff `_` was given for the
    // commutativity slot); `comm_id` is resolved lazily and may still be null.
    return combiner.comm_name != null;
}

// Decide whether `template` (under `bindings`) provably cannot match `ref`,
// looking only at *rigid* structure the validator can never bridge.
//
// `matchTemplate` is all-or-nothing: when it fails it tells us nothing about
// *why*. The coarse classification around the call site then gives up
// (`.unknown`) the moment any ACUI/def/unavailable term appears anywhere in the
// template, ref, or current bindings — even when the actual disagreement is in a
// fully rigid region. That is the church-`inst` blowup: hypothesis `G ⊩ t : A`
// has `t`, `A` already pinned, so the rigid `… : …` payload determines the
// match, yet every ref survives the filter merely because its *context* is an
// ACUI `join`. Here we walk template against ref and report a mismatch only when
// they diverge at a point both sides hold rigid — exactly the divergences def
// unfolding and ACUI rearrangement cannot reconcile. ACUI/def regions (and
// unbound binders, placeholders, opaque atoms paired with non-rigid terms) are
// treated as "no opinion" so we never prune a ref the validator would accept.
pub fn templateDefiniteMismatch(
    context: *const Context,
    theorem: *const TheoremContext,
    template: TemplateExpr,
    ref: ExprId,
    bindings: []const ?ExprId,
) bool {
    switch (template) {
        .binder => |idx| {
            const value = if (idx < bindings.len) bindings[idx] else null;
            // Unbound binder: matches anything. Bound binder: its value must
            // equal the ref subterm, judged by rigid divergence.
            if (value) |bound| return rigidExprMismatch(context, theorem, bound, ref);
            return false;
        },
        .app => |app| {
            // A `@rewrite` LHS head can reduce to a *different* head, so a
            // rigid-head clash here is never definite — defer to the semantic
            // matcher. (e.g. `[y/x][q/refl A x] C` vs `Id A x x`: the `sb_ty`
            // head rewrites away.) Mirrors shape.zig's reducible-head widening
            // and `termNeedsSemantic`; without this the rigid-head comparison
            // below short-circuits the whole pair to `.mismatch`.
            if (context.registry.rewrites_by_head.contains(app.term_id)) return false;
            const node = theorem.interner.node(ref);
            // Transparent def with a body: when the ref is the SAME def at the
            // same arity, compare *through* the body. A payload like `≃[A] a = b`
            // (`eqc`) unfolds to `eq · A · a · b`, so its bound args sit at rigid
            // positions and can prune — even though the `eqc` head itself is not
            // rigid. We never assume a def is injective: only arguments the body
            // actually places at a rigid position are compared (see
            // `defBodyTemplateMismatch`); ignored args (the `const` trap) and
            // dummies are silently skipped. Bounded to one unfold layer.
            if (transparentDefBody(context, app.term_id)) |info| {
                switch (node.*) {
                    .app => |concrete| {
                        if (concrete.term_id == app.term_id and
                            concrete.args.len == app.args.len and
                            app.args.len == info.nargs)
                        {
                            return defBodyTemplateMismatch(
                                context,
                                theorem,
                                info.body,
                                app.args,
                                concrete.args,
                                info.nargs,
                                bindings,
                            );
                        }
                    },
                    .variable => {
                        return resolveRigidHead(context, app.term_id) != null;
                    },
                    .placeholder => return false,
                }
                // Different def heads can still be impossible: if both expose
                // distinct rigid roots after transparent-def unfolding, no
                // unification or ACUI canonicalization can reconcile them.
                switch (node.*) {
                    .app => |concrete| {
                        return rigidHeadMismatch(
                            context,
                            app.term_id,
                            concrete.term_id,
                        );
                    },
                    else => return false,
                }
            }
            // A non-rigid template head (ACUI / unavailable / binder-def) could
            // rearrange or unfold to match.  Still, if head-only def unfolding
            // reveals distinct rigid roots on both sides, we can reject.
            if (!isRigidTerm(context, app.term_id)) {
                switch (node.*) {
                    .app => |concrete| return rigidHeadMismatch(
                        context,
                        app.term_id,
                        concrete.term_id,
                    ),
                    .variable => return resolveRigidHead(context, app.term_id) !=
                        null,
                    .placeholder => return false,
                }
            }
            switch (node.*) {
                .app => |concrete| {
                    if (concrete.term_id != app.term_id) {
                        return rigidHeadMismatch(
                            context,
                            app.term_id,
                            concrete.term_id,
                        );
                    }
                    if (concrete.args.len != app.args.len) return false;
                    for (app.args, concrete.args) |tmpl_arg, ref_arg| {
                        if (templateDefiniteMismatch(
                            context,
                            theorem,
                            tmpl_arg,
                            ref_arg,
                            bindings,
                        )) return true;
                    }
                    return false;
                },
                // A rigid compound can't equal a bare atom; a placeholder may
                // still stand for anything, so withhold judgment there.
                .variable => return true,
                .placeholder => return false,
            }
        },
    }
}

// Rigid-divergence comparison of two committed expressions (the bound-binder
// counterpart of `templateDefiniteMismatch`). Two distinct rigid atoms, a rigid
// atom against a rigid compound, or two rigid compounds with differing heads are
// all unbridgeable. Anything touching an ACUI/def/unavailable head or a
// placeholder is inconclusive.
pub fn rigidExprMismatch(
    context: *const Context,
    theorem: *const TheoremContext,
    a: ExprId,
    b: ExprId,
) bool {
    if (a == b) return false;
    const na = theorem.interner.node(a);
    const nb = theorem.interner.node(b);
    // A `@rewrite`-reducible head on either side can rewrite to a different
    // head, so a rigid clash is never definite — e.g. a bound motive value
    // `const_ty k A` (reducible to `A` via `const_ty_eval`) compared against a
    // ref's `A`. Mirrors `templateDefiniteMismatch`'s `.app` reducible guard;
    // without it, primitive-but-reducible heads are treated as rigid and the
    // pair is wrongly rejected before the normalizer runs.
    if (headIsReducibleNode(context, na) or headIsReducibleNode(context, nb)) {
        return false;
    }
    switch (na.*) {
        .placeholder => return false,
        .variable => switch (nb.*) {
            // Distinct interned atoms are genuinely different and nothing
            // reconciles them.
            .variable => return true,
            .app => |bb| return resolveRigidHead(context, bb.term_id) != null,
            .placeholder => return false,
        },
        .app => |aa| {
            // Same transparent-def head on both sides: compare through the body
            // (e.g. a bound value `and(p,q)` vs ref `and(p',q')`), mirroring
            // `templateDefiniteMismatch`. Only args the body places at a rigid
            // position are compared, so this stays sound (no injectivity
            // assumption) and bounded.
            if (transparentDefBody(context, aa.term_id)) |info| {
                switch (nb.*) {
                    .app => |bb| {
                        if (bb.term_id == aa.term_id and
                            bb.args.len == aa.args.len and
                            aa.args.len == info.nargs)
                        {
                            return defBodyExprMismatch(
                                context,
                                theorem,
                                info.body,
                                aa.args,
                                bb.args,
                                info.nargs,
                            );
                        }
                    },
                    else => {},
                }
                switch (nb.*) {
                    .app => |bb| return rigidHeadMismatch(
                        context,
                        aa.term_id,
                        bb.term_id,
                    ),
                    .variable => return resolveRigidHead(context, aa.term_id) !=
                        null,
                    .placeholder => return false,
                }
            }
            if (!isRigidTerm(context, aa.term_id)) {
                switch (nb.*) {
                    .app => |bb| return rigidHeadMismatch(
                        context,
                        aa.term_id,
                        bb.term_id,
                    ),
                    .variable => return resolveRigidHead(context, aa.term_id) !=
                        null,
                    .placeholder => return false,
                }
            }
            switch (nb.*) {
                .variable => return true,
                .placeholder => return false,
                .app => |bb| {
                    if (aa.term_id != bb.term_id) {
                        return rigidHeadMismatch(
                            context,
                            aa.term_id,
                            bb.term_id,
                        );
                    }
                    if (aa.args.len != bb.args.len) return false;
                    for (aa.args, bb.args) |x, y| {
                        if (rigidExprMismatch(context, theorem, x, y)) return true;
                    }
                    return false;
                },
            }
        },
    }
}

const DefBodyInfo = struct {
    body: TemplateExpr,
    nargs: usize,
};

// If `term_id` heads an available transparent def we can SAFELY unfold for a
// structural comparison, return its body and argument count; otherwise null.
//
// "Safely" means first-order: the body introduces no binders of its own. We
// detect this by `dummy_args.len == 0` — a def's inner λ-bound variables are
// exactly its dummy args. The comparison walks the body substituting each side's
// arguments and compares them at rigid positions as if independent closed terms;
// that reasoning is only valid when no enclosing binder can capture an argument's
// free variables. So binder-introducing defs (`∀`, `∃`, substitution, `and`/`or`
// built from λ, …) are deliberately excluded — unfolding those here was unsound
// and over-pruned. ACUI combiners are excluded too (flagged by
// `termNeedsSemantic` but not defs).
fn transparentDefBody(context: *const Context, term_id: u32) ?DefBodyInfo {
    if (!context.env.hasAvailableTerm(term_id)) return null;
    if (context.registry.acui_by_head.contains(term_id)) return null;
    const term = context.env.terms.items[term_id];
    if (!(term.available and term.is_def)) return null;
    if (term.dummy_args.len != 0) return null;
    const body = term.body orelse return null;
    return .{ .body = body, .nargs = term.args.len };
}

pub const UnfoldDefInfo = struct {
    body: TemplateExpr,
    nargs: usize,
    dummies: []const ArgInfo,
};

// Like `transparentDefBody`, but optionally accepts binder-introducing defs
// (those with dummy args). Binder defs are only safe to unfold in SEED contexts
// that materialize each dummy as a fresh placeholder (see `unfoldDefBody`): a
// placeholder only loosens downstream matching, so it can never cause a false
// prune or a captured-variable comparison. The matcher's mismatch logic must
// NOT use this — it compares dummies as concrete terms, which is
// capture-unsound — and stays on first-order `transparentDefBody`.
pub fn defBodyForUnfold(
    context: *const Context,
    term_id: u32,
    allow_binder_defs: bool,
) ?UnfoldDefInfo {
    if (!context.env.hasAvailableTerm(term_id)) return null;
    if (context.registry.acui_by_head.contains(term_id)) return null;
    const term = context.env.terms.items[term_id];
    if (!(term.available and term.is_def)) return null;
    if (term.dummy_args.len != 0 and !allow_binder_defs) return null;
    const body = term.body orelse return null;
    return .{ .body = body, .nargs = term.args.len, .dummies = term.dummy_args };
}

// Unfold one layer of a transparent def application into its body, supplying the
// application's `args` for the real parameters and a fresh placeholder for each
// dummy binder. Interns into `theorem`. `args.len` must equal `info.nargs`.
pub fn unfoldDefBody(
    theorem: *TheoremContext,
    info: UnfoldDefInfo,
    args: []const ExprId,
) !ExprId {
    if (info.dummies.len == 0) {
        return try theorem.instantiateTemplate(info.body, args);
    }
    const binders = try theorem.allocator.alloc(
        ExprId,
        info.nargs + info.dummies.len,
    );
    defer theorem.allocator.free(binders);
    @memcpy(binders[0..info.nargs], args[0..info.nargs]);
    for (info.dummies, 0..) |dummy, i| {
        binders[info.nargs + i] = try theorem.addPlaceholderResolved(
            dummy.sort_name,
        );
    }
    return try theorem.instantiateTemplate(info.body, binders);
}

// Compare `def(t_args)` against `def(r_args)` by walking the def's body. Both
// unfoldings share the entire (recursively unfolded) body skeleton and differ
// ONLY at occurrences of the outermost def's parameters, so a mismatch can only
// arise where a root parameter sits at an all-rigid path. We walk the body, and:
//   * a root-parameter binder reached via rigid heads → compare its two argument
//     trees (`templateDefiniteMismatch`);
//   * a nested transparent-def head → unfold it, pushing a scope whose params map
//     to that application's argument templates (interpreted in the parent scope),
//     so deeper levels (e.g. `⇔`/`bic` → `≃`/`eqc` → `eq`) keep narrowing;
//   * a non-rigid, non-def head (ACUI / unavailable) → stop (no opinion);
//   * a dummy binder (idx ≥ nargs) → fresh on both sides, no opinion.
// Sound without assuming injectivity: arguments the unfolded body never places at
// a rigid position are never compared (handles the `const`-def trap). Terminating:
// def bodies reference only earlier-declared terms, so the unfold chain is acyclic;
// `max_def_unfold_depth` is a defensive cap against pathologically deep stacks.
const max_def_unfold_depth = 64;

// A def-unfold scope. The root carries the two sides' argument trees being
// compared (either rule-template-vs-ref-expr or expr-vs-expr); each nested level
// carries the unfolding application's argument templates plus a pointer to the
// enclosing scope they are interpreted in.
const DefScope = struct {
    nargs: usize,
    kind: union(enum) {
        // Outermost def reached from `templateDefiniteMismatch`.
        template_root: struct {
            t_args: []const TemplateExpr,
            r_args: []const ExprId,
        },
        // Outermost def reached from `rigidExprMismatch`.
        expr_root: struct {
            a_args: []const ExprId,
            b_args: []const ExprId,
        },
        nested: struct {
            args: []const TemplateExpr,
            parent: *const DefScope,
        },
    },
};

fn defBodyTemplateMismatch(
    context: *const Context,
    theorem: *const TheoremContext,
    body: TemplateExpr,
    t_args: []const TemplateExpr,
    r_args: []const ExprId,
    nargs: usize,
    bindings: []const ?ExprId,
) bool {
    const root = DefScope{
        .nargs = nargs,
        .kind = .{ .template_root = .{ .t_args = t_args, .r_args = r_args } },
    };
    return scopedBodyMismatch(context, theorem, body, &root, bindings, 0);
}

// Expr-vs-expr counterpart: compare `def(a_args)` against `def(b_args)` through
// the shared body. Same machinery as `defBodyTemplateMismatch`, differing only in
// the root leaf comparison (`rigidExprMismatch`).
fn defBodyExprMismatch(
    context: *const Context,
    theorem: *const TheoremContext,
    body: TemplateExpr,
    a_args: []const ExprId,
    b_args: []const ExprId,
    nargs: usize,
) bool {
    const root = DefScope{
        .nargs = nargs,
        .kind = .{ .expr_root = .{ .a_args = a_args, .b_args = b_args } },
    };
    return scopedBodyMismatch(context, theorem, body, &root, &.{}, 0);
}

// Resolve `template` (a node of some def body) against `scope`, reporting a rigid
// divergence between the two sides it stands for. See `defBodyTemplateMismatch`.
fn scopedBodyMismatch(
    context: *const Context,
    theorem: *const TheoremContext,
    template: TemplateExpr,
    scope: *const DefScope,
    bindings: []const ?ExprId,
    depth: usize,
) bool {
    if (depth >= max_def_unfold_depth) return false;
    switch (template) {
        .binder => |idx| {
            if (idx >= scope.nargs) return false; // dummy of this def
            switch (scope.kind) {
                // Outermost def parameter: this is where the two sides actually
                // differ — compare their argument trees.
                .template_root => |r| return templateDefiniteMismatch(
                    context,
                    theorem,
                    r.t_args[idx],
                    r.r_args[idx],
                    bindings,
                ),
                .expr_root => |r| return rigidExprMismatch(
                    context,
                    theorem,
                    r.a_args[idx],
                    r.b_args[idx],
                ),
                // Nested def parameter: continue with the argument template that
                // was substituted for it, interpreted one scope out.
                .nested => |n| return scopedBodyMismatch(
                    context,
                    theorem,
                    n.args[idx],
                    n.parent,
                    bindings,
                    depth + 1,
                ),
            }
        },
        .app => |app| {
            if (transparentDefBody(context, app.term_id)) |info| {
                // Unfold one more transparent-def layer.
                if (app.args.len != info.nargs) return false;
                const child = DefScope{
                    .nargs = info.nargs,
                    .kind = .{ .nested = .{ .args = app.args, .parent = scope } },
                };
                return scopedBodyMismatch(
                    context,
                    theorem,
                    info.body,
                    &child,
                    bindings,
                    depth + 1,
                );
            }
            // Non-rigid, non-def head (ACUI / unavailable): can't judge.
            if (!isRigidTerm(context, app.term_id)) return false;
            for (app.args) |child| {
                if (scopedBodyMismatch(
                    context,
                    theorem,
                    child,
                    scope,
                    bindings,
                    depth + 1,
                )) return true;
            }
            return false;
        },
    }
}

pub fn projectViewBindingsIntoRule(
    view: types.ViewDecl,
    view_bindings: []const ?ExprId,
    rule_bindings: []?ExprId,
) void {
    for (view.binder_map, 0..) |maybe_rule_idx, vi| {
        const rule_idx = maybe_rule_idx orelse continue;
        if (rule_idx >= rule_bindings.len) continue;
        if (rule_bindings[rule_idx] != null) continue;
        if (view_bindings[vi]) |expr| rule_bindings[rule_idx] = expr;
    }
}

// Walk template against ref filling in any binder slots that the ref's
// structure pins down, without ever overriding a binding that was already
// set. Called on the `.unknown` path so that even when `matchTemplate`
// failed structurally, partial information about the rule's binders can
// reach the next hyp's lookup. Soundness: bindings written here are
// values matchTemplate would itself have committed if it had walked past
// the failure point; the only way they could be "wrong" is if the
// candidate is ultimately rejected by the full validator, in which case
// the worst outcome is some wasted exploration of refs that wouldn't have
// matched. Existing bindings (from goal seed or earlier hyps) are
// trusted: this walk never overwrites them.
pub fn extractHypPartialBindings(
    context: *const Context,
    theorem: *TheoremContext,
    template: TemplateExpr,
    expr_id: ExprId,
    bindings: []?ExprId,
) void {
    switch (template) {
        .binder => |idx| {
            if (idx >= bindings.len) return;
            if (bindings[idx] != null) return;
            bindings[idx] = expr_id;
        },
        .app => |app| {
            const node = theorem.interner.node(expr_id);
            switch (node.*) {
                .variable, .placeholder => {},
                .app => |concrete| {
                    if (concrete.term_id == app.term_id and
                        concrete.args.len == app.args.len)
                    {
                        // Positional walk: when the ref happens to be written
                        // with the same association as the template, this pins
                        // binders directly (and matches the ordered reading an
                        // associative-but-not-commutative combiner requires).
                        //
                        // Skip it under a *commutative* ACUI head: there the
                        // positional correspondence is meaningless — the ref's
                        // members can be in any order/association — so pinning a
                        // bare binder leaf (e.g. `ex_elim`'s context `H` in
                        // `H , p`) to the ref's first arg is a wrong guess at the
                        // split. It would also swallow members that belong to a
                        // sibling leaf (the eigenvariable hyp `p`), leaving that
                        // leaf unpinnable and the binder carrying a free
                        // eigenvariable into the conclusion (pruned by
                        // `finalConclusionPlausible`). The `extractAcuiMemberBindings`
                        // pass below is the correct, order-insensitive extractor
                        // for this case; it never pins a bare binder, leaving the
                        // split open for the validator's ACUI weakening.
                        if (!acuiIsCommutative(context, app.term_id)) {
                            for (app.args, concrete.args) |tmpl_arg, conc_arg| {
                                extractHypPartialBindings(
                                    context,
                                    theorem,
                                    tmpl_arg,
                                    conc_arg,
                                    bindings,
                                );
                            }
                        }
                    } else if (transparentDefBody(context, app.term_id)) |info| {
                        // Head mismatch but the template head is a transparent
                        // first-order def whose unfolding may line up with the
                        // ref. The ref is commonly stored in the def's *unfolded*
                        // form (e.g. hyp `P ⇔ Q` = `bic(P,Q)` against a ref proven
                        // as `≃[𝔹] a = b` = `eqc(𝔹,a,b)`), so the plain positional
                        // walk bails at `bic`≠`eqc` and the binders under the def
                        // never get pinned. Unfold the template body and continue
                        // extraction against the same ref. Mirrors the matcher's
                        // `scopedBodyMismatch`; sound for the same reason (the def
                        // is transparent and first-order, so the binder values are
                        // forced by the ref).
                        if (app.args.len == info.nargs) {
                            const root = ExtractScope{
                                .nargs = info.nargs,
                                .kind = .{ .template_root = .{ .t_args = app.args } },
                            };
                            extractScopedBindings(
                                context,
                                theorem,
                                info.body,
                                &root,
                                expr_id,
                                bindings,
                                0,
                            );
                        }
                    } else if (defBodyForUnfold(
                        context,
                        concrete.term_id,
                        true,
                    )) |info| {
                        // Symmetric case: the *ref* head is a binder-introducing
                        // def folded over the template's existential — e.g. the
                        // view hyp `G ⊢ ∃ x p` (`nd(G, ex(λx.p))`) against a ref
                        // proven as `has_preimage f X y` (= `∃ x (x∈X ∧ maps f x y)`)
                        // or euclid's `a < b` (= `∃ k …`). The positional walk bails
                        // at `ex` ≠ `has_preimage`, so the existential body binder
                        // `p` never pins and the `@recover` containment injection
                        // for the paired hypothesis stays inert. Unfold the ref one
                        // layer — each dummy materialized as a fresh placeholder by
                        // `unfoldDefBody` — and re-extract against the same template,
                        // exposing the `∃` so `p` binds.
                        //
                        // Sound for the same reason as `partialMatchTemplate`'s
                        // concrete-side unfold (which this mirrors): a placeholder
                        // only ever loosens later matching, and bindings written on
                        // this extraction path merely seed downstream hyp lookups
                        // and the recover guard — they never themselves reject a
                        // candidate. Reserved for extraction; the strict matcher
                        // stays first-order (see `defBodyForUnfold`). `concrete` is
                        // a value copy whose `args` slice is a stable heap
                        // allocation, so interning here cannot invalidate it.
                        if (concrete.args.len == info.nargs) {
                            const unfolded = unfoldDefBody(
                                theorem,
                                info,
                                concrete.args,
                            ) catch return;
                            extractHypPartialBindings(
                                context,
                                theorem,
                                template,
                                unfolded,
                                bindings,
                            );
                        }
                    }
                },
            }
            // For an ACUI combiner the positional walk above usually bails at
            // the head (the ref writes the same multiset in a different shape),
            // leaving leaf binders unbound. Recover those from the ref's
            // members, but only where a leaf has a single shape-compatible
            // member so the value is forced (see `extractAcuiMemberBindings`).
            //
            // Gated on commutativity: the member extractor treats the combiner's
            // arguments as an unordered bag, which is only valid when `@acui`
            // declared C. Under a non-commutative subset (e.g. AU) the args are
            // an ordered list — the positional walk above already handles those
            // correctly, and order-aware strategies are a separate problem.
            if (acuiIsCommutative(context, app.term_id)) {
                acui.extractAcuiMemberBindings(
                    context,
                    theorem,
                    app.term_id,
                    template,
                    expr_id,
                    bindings,
                    extractHypPartialBindings,
                );
            }
        },
    }
}

// Scope for extraction through transparent-def unfoldings, the extraction-side
// analogue of `DefScope`. A `template_root` carries the rule template's argument
// trees (binders index into `bindings`); each `nested` level carries a def
// application's argument templates plus the enclosing scope they are read in.
const ExtractScope = struct {
    nargs: usize,
    kind: union(enum) {
        template_root: struct { t_args: []const TemplateExpr },
        nested: struct { args: []const TemplateExpr, parent: *const ExtractScope },
    },
};

// Walk a def `body` (interpreted through `scope`) against `expr_id` in lockstep,
// pinning forced binder values into `bindings`. Unfolds transparent first-order
// defs *lazily* — only when the current head fails to align with the ref's head —
// so a ref written at any folding level (`bic` ↔ `eqc` ↔ `eq · _ · _`) is matched
// without over-unfolding past the ref's own representation. Soundness mirrors
// `extractHypPartialBindings`: only binders forced by the ref's structure are set.
fn extractScopedBindings(
    context: *const Context,
    theorem: *TheoremContext,
    body: TemplateExpr,
    scope: *const ExtractScope,
    expr_id: ExprId,
    bindings: []?ExprId,
    depth: usize,
) void {
    if (depth >= max_def_unfold_depth) return;
    switch (body) {
        .binder => |idx| {
            if (idx >= scope.nargs) return; // dummy of this def: no opinion
            switch (scope.kind) {
                // Outermost def parameter: resolve to the rule template argument
                // and hand back to the binder-aware extractor.
                .template_root => |r| extractHypPartialBindings(
                    context,
                    theorem,
                    r.t_args[idx],
                    expr_id,
                    bindings,
                ),
                // Nested def parameter: continue with the substituted argument,
                // interpreted one scope out.
                .nested => |n| extractScopedBindings(
                    context,
                    theorem,
                    n.args[idx],
                    n.parent,
                    expr_id,
                    bindings,
                    depth + 1,
                ),
            }
        },
        .app => |app| {
            const node = theorem.interner.node(expr_id);
            if (node.* == .app and
                node.app.term_id == app.term_id and
                node.app.args.len == app.args.len)
            {
                // Heads aligned at this folding level: descend positionally.
                for (app.args, node.app.args) |barg, rarg| {
                    extractScopedBindings(
                        context,
                        theorem,
                        barg,
                        scope,
                        rarg,
                        bindings,
                        depth + 1,
                    );
                }
                return;
            }
            // Heads differ: unfold one more transparent-def layer on the template
            // side and retry against the same ref.
            if (transparentDefBody(context, app.term_id)) |info| {
                if (app.args.len != info.nargs) return;
                const child = ExtractScope{
                    .nargs = info.nargs,
                    .kind = .{ .nested = .{ .args = app.args, .parent = scope } },
                };
                extractScopedBindings(
                    context,
                    theorem,
                    info.body,
                    &child,
                    expr_id,
                    bindings,
                    depth + 1,
                );
                return;
            }
            // Symmetric: the ref may be folded *tighter* than the current
            // body level (ref `bic X Y` against body head `eq ·`-spine, where
            // bic ↦ eqc ↦ eq · _ · _). Template-side unfolding can never
            // align those — the productive move is unfolding the ref one
            // layer and retrying this same body level. Sound for the same
            // reason as the ref-side unfold in `extractHypPartialBindings`:
            // only binders forced by the (unfolded) ref's structure are set,
            // and the full validator still confirms every assembly. `concrete`
            // is a value copy whose `args` slice is stable, so interning the
            // unfolded body cannot invalidate it.
            if (node.* == .app) {
                const concrete = node.app;
                if (defBodyForUnfold(context, concrete.term_id, true)) |rinfo| {
                    if (concrete.args.len == rinfo.nargs) {
                        const unfolded = unfoldDefBody(
                            theorem,
                            rinfo,
                            concrete.args,
                        ) catch return;
                        extractScopedBindings(
                            context,
                            theorem,
                            body,
                            scope,
                            unfolded,
                            bindings,
                            depth + 1,
                        );
                    }
                }
            }
        },
    }
}

// Extract binder values from the members of an ACUI multiset (Proposal B).
//
// The structural walk in `extractHypPartialBindings` can't cross an ACUI head:
// e.g. the template context `G , ≃[A] x = t` (`join(G, hyp(eqc(A,x,t)))`)
// almost never matches the ref's context shape, so `A`, `x`, `t` stay unbound
// and the next hypothesis (`G ⊩ t : A`) is left searching its full ref pool.
// Here we treat the template's leaves under this combiner as a multiset and try
// to pin the binders of an unbound leaf from a forced ref member.
//
// The key step is *subtracting the bound siblings*. A leaf like the bound `G`
// (a binder already pinned to the goal context) expands to a known multiset of
// ref members; in any valid alignment those members are claimed by `G`. We mark
// them consumed first, so the unbound leaf only competes against what's left.
// Without this, `G ⊩ … , ≃[A] x = t` against a goal whose context already holds
// other equations would see several `hyp(eqc …)` members and give up. After
// removing `G`'s members, the lone remaining equation is forced.
//
// Why this is completeness-safe: in any valid ACUI alignment each bound leaf
// maps to ref members equal to its own (hash-consed ⇒ identity equality), and
// the unbound leaf maps to one of the rest. If, after removing the bound-leaf
// members, exactly one remaining member is shape-compatible with the unbound
// leaf, every valid alignment maps the leaf to it — so the binder values it
// yields are forced (the same the full validator would derive). With zero or
// several candidates we commit nothing. These are only search-guidance bindings
// (the proof is re-derived by `tryCandidate`), so an over-eager commit could
// only cost completeness, which the uniqueness gate prevents.
//
// NOTE: treating the args as an unordered multiset assumes commutativity. Under
// a non-commutative `@acui` subset (e.g. pure AU) this is a heuristic — still
// sound as guidance, but not a completeness guarantee. See `docs/rewrite_system.md`.
