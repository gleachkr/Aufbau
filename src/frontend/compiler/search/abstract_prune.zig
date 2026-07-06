//! Necessary-condition prefilter for `@abstract` (Leibniz one-hole-context)
//! view rules during candidate-ref enumeration.
//!
//! The motivating case is the Leibniz substitution family (`eq_replace` and
//! friends): the rule's target hypothesis is a bare binder, so the ref-index
//! shapes that slot to a covering wildcard and the enumerator pairs it with the
//! entire ref pool. That is an O(pool^2) flood of `tryCandidate` calls, almost
//! all rejected, because nothing constrains the broad slot. The standard
//! conclusion-plausibility prune (`finalConclusionPlausible`) now refutes view
//! rules against their *view* conclusion, but for a bare-binder target that
//! template is a covering wildcard, so it offers little protection here — this
//! `@abstract`-specific check does.
//!
//! `@abstract target left right hole left_plug right_plug` declares that the two
//! solved view expressions `left` and `right` are structurally identical except
//! at occurrences of the plug pair `(left_plug, right_plug)`. That is a sound
//! *necessary* condition: if, for the resolved plug pair, `left` and `right`
//! diverge at a position that is provably NOT the hole and that no head
//! conversion could reconcile, no one-hole context can explain them and the rule
//! cannot apply for this ref tuple.
//!
//! Completeness discipline: this only ever *removes* tuples whose `(left, right)`
//! have a **definite divergence** at a node that is provably not the hole. The
//! walk first resolves transparent-def head chains to rigid roots; distinct
//! rigid roots are a definite mismatch because no unfolding or canonicalization
//! can align them. When a transparent def body is available, it may also walk the
//! body template read-only, substituting actual arguments through a scope stack.
//! Dummy binders, ambiguous arguments, ACUI heads, `@rewrite` heads, unavailable
//! terms, and depth exhaustion all mean "no opinion".
//!
//! Crucially it does NOT use plug absence as evidence for a prune: a hole-free /
//! constant motive candidate shows up here as `left ≡ right` (possibly only after
//! a head/body conversion), on which we abstain and leave the real `@abstract`
//! validator to enforce the plug-occurrence requirement.
//!
//! Head resolution sees through transparent defs including binder-introducing
//! ones — `le a b`≡`∃ k (a+k=b)`, `dvd a b`≡`∃ k (b=a*k)`, `lt`→`le`→`∃` — because
//! a def's *head* term never depends on its dummy binders, so a `dvd`-vs-`eq` or
//! `or`-vs-`le` tuple prunes even though one surface head is `termNeedsSemantic`.
//! Body walking is deliberately non-materializing: it never interns the expanded
//! body and never mints placeholders for dummy binders, so it stays read-only and
//! cannot consume the bounded per-context dependency-mask slots.
//!
//! A *reducible plug* (`D a` that unfolds/rewrites to `F a`) appears in left/right
//! only in its preprocessed form, so the raw-ExprId hole test would miss it. We do
//! NOT bail the whole decl: instead the divergence walk switches to a head-aware
//! hole guard (`plugCouldOccurAt`) — the same head-resolution machinery, applied
//! to the plug. A node is treated as a possible hole unless its rigid root and the
//! plug's are both resolved and distinct, so the head clash still prunes on the
//! residual while a genuine (preprocessed) hole is never misjudged. The plug/side
//! bindings are extracted by a purely structural (no
//! normalization) template match, and we abstain whenever any required view
//! binder cannot be pinned cleanly — so a binding the real, normalization-aware
//! view match would only discover after unfolding is never the basis for a prune.

const std = @import("std");
const ExprId = @import("../../expr.zig").ExprId;
const TheoremContext = @import("../../expr.zig").TheoremContext;
const TemplateExpr = @import("../../rules.zig").TemplateExpr;
const DerivedBindings = @import("../derived_bindings.zig");
const ViewDecl = @import("../views.zig").ViewDecl;
const AbstractDecl = DerivedBindings.AbstractDecl;
const types = @import("./types.zig");
const Context = types.Context;
const def_match = @import("./backward/def_match.zig");
const semantic = @import("./backward/semantic.zig");

/// One resolved hypothesis slot: the rule/view hypothesis index and the concrete
/// ref expression filling it. The view hypotheses are parallel to the rule
/// hypotheses, so `hyp_index` doubles as the view-hyp index.
pub const Fill = struct {
    hyp_index: usize,
    ref_expr: ExprId,
};

/// True when, for some `@abstract` declaration on `view`, the one-hole-context
/// derivation is *provably infeasible* given `goal_expr` (the proof line) and
/// the resolved hypothesis `fills`. A true result means the candidate ref tuple
/// can be skipped before `tryCandidate`. Conservative: returns false whenever a
/// required binder cannot be syntactically pinned, on any ambiguity, or when the
/// divergence touches anything a normalizer could reconcile.
///
/// `theorem` must be the candidate's own context: `goal_expr`/`fills` exprs must
/// live in its id-space, and the divergence walk reads its interner.
pub fn abstractInfeasible(
    theorem: *const TheoremContext,
    context: *const Context,
    view: ViewDecl,
    goal_expr: ?ExprId,
    fills: []const Fill,
) bool {
    if (view.derived_bindings.len == 0) return false;

    var bindings_buf: [64]?ExprId = undefined;
    var conflict_buf: [64]bool = undefined;
    if (view.num_binders > bindings_buf.len) return false;
    const bindings = bindings_buf[0..view.num_binders];
    const conflicted = conflict_buf[0..view.num_binders];
    @memset(bindings, null);
    @memset(conflicted, false);

    // Solve view binders structurally from everything currently known: the goal
    // pins binders in the view conclusion, each resolved ref pins binders in its
    // view hypothesis. Best-effort: partial matches still record the binders at
    // positions reached before any structural divergence.
    if (goal_expr) |g| {
        matchTemplateStructural(context, theorem, view.concl, g, bindings, conflicted);
    }
    for (fills) |fill| {
        if (fill.hyp_index >= view.hyps.len) continue;
        matchTemplateStructural(
            context,
            theorem,
            view.hyps[fill.hyp_index],
            fill.ref_expr,
            bindings,
            conflicted,
        );
    }

    for (view.derived_bindings) |db| {
        const abstract = switch (db) {
            .abstract => |a| a,
            .recover => continue,
        };
        if (declInfeasible(theorem, context, abstract, bindings, conflicted)) {
            return true;
        }
    }
    return false;
}

fn declInfeasible(
    theorem: *const TheoremContext,
    context: *const Context,
    abstract: AbstractDecl,
    bindings: []const ?ExprId,
    conflicted: []const bool,
) bool {
    const left = pinned(bindings, conflicted, abstract.left_view_idx) orelse return false;
    const right = pinned(bindings, conflicted, abstract.right_view_idx) orelse return false;
    const left_plug = pinned(bindings, conflicted, abstract.left_plug_view_idx) orelse return false;
    const right_plug = pinned(bindings, conflicted, abstract.right_plug_view_idx) orelse return false;
    // The hole is detected by raw-ExprId equality with the plug pair, which is
    // exact only when the plugs are rigid. The real `@abstract` derivation
    // (`applyAbstractBinding`) preprocesses BOTH plugs alongside left/right before
    // its raw-equality hole-finding pass, so a reducible plug (`D a` that
    // unfolds/rewrites to `F a`) occurs in left/right only in its preprocessed
    // form — which raw equality would miss, then descend through `F` and report a
    // spurious `a` vs `b` mismatch. When a plug is reducible we therefore switch
    // the divergence walk to a sound *head-aware* hole test (`plugs_semantic`):
    // preprocessing preserves a term's rigid head whenever `rigidHeadOf` resolves,
    // so a node whose rigid root differs from the plug's is provably not a hole and
    // a head clash there is still decisive. Any later body walk remains
    // non-materializing: no placeholders are minted, so the bounded per-context
    // dependency-mask budget is untouched.
    const plugs_semantic = semantic.exprNeedsSemantic(context, theorem, left_plug) or
        semantic.exprNeedsSemantic(context, theorem, right_plug);
    return abstractDefiniteMismatch(
        context,
        theorem,
        left,
        right,
        left_plug,
        right_plug,
        plugs_semantic,
    );
}

fn pinned(bindings: []const ?ExprId, conflicted: []const bool, idx: usize) ?ExprId {
    if (idx >= bindings.len) return null;
    if (conflicted[idx]) return null;
    return bindings[idx];
}

/// True iff `left` and `right` have a **definite divergence** for the plug pair
/// `(left_plug, right_plug)` — i.e. a one-hole context provably cannot explain
/// them, possibly only after unfolding transparent defs. Sound (only prunes the
/// impossible):
///   * the plug pair `(left_plug, right_plug)` is the hole — never a mismatch;
///   * when `plugs_semantic`, a reducible plug occurs in left/right only in its
///     preprocessed form, so raw equality can miss the hole. We then also abstain
///     wherever the node *could* be a hole under the validator's preprocessing —
///     i.e. both sides' rigid roots could still match the plugs' (`plugCouldOccurAt`).
///     A head clash is only declared past that guard, so a genuine hole is never
///     pruned;
///   * `left == right` (identical, incl. hole-free candidates) — abstain;
///   * the two heads resolve through their transparent-def head chains to
///     *distinct* rigid roots (`dvd`→`ex` vs `eq`, `or` vs `le`→`ex`) — a
///     definite mismatch, since no unfolding/canonicalization aligns them;
///   * an ACUI / `@rewrite` / unavailable head, or a same-rigid-root pair whose
///     surface heads differ (`dvd` vs `le`, both `∃`-rooted) — a conversion could
///     reconcile it, so no opinion;
///   * same rigid head — descend positionally, still honoring nested holes;
///   * otherwise defer to the rigid-divergence verdict (`rigidExprMismatch`),
///     which itself abstains on anything reducible and never recurses past a
///     differing head (so no nested hole can be misjudged there). With reducible
///     plugs we skip this deeper fallback (its no-hole-below justification relies
///     on raw==preprocessed structure) and rely on the head clash alone.
fn abstractDefiniteMismatch(
    context: *const Context,
    theorem: *const TheoremContext,
    left: ExprId,
    right: ExprId,
    left_plug: ExprId,
    right_plug: ExprId,
    plugs_semantic: bool,
) bool {
    if (left == left_plug and right == right_plug) return false;
    // Head-aware hole guard for reducible plugs: if THIS node could be a hole
    // occurrence once the validator preprocesses node and plug into a common form,
    // hold no opinion. Sound by `plugCouldOccurAt`'s over-approximation — it only
    // returns false (definitely-not-a-hole) when a rigid-root clash rules the node
    // out, so the head clash and descent below can never misjudge a real hole.
    if (plugs_semantic and
        plugCouldOccurAt(context, theorem, left, left_plug) and
        plugCouldOccurAt(context, theorem, right, right_plug)) return false;
    if (left == right) return false;

    const ln = theorem.interner.node(left);
    const rn = theorem.interner.node(right);

    // Resolve both heads through their transparent-def head chains (`le`/`dvd`
    // → `ex`, `lt` → `le` → `ex`, …) to a rigid root. `resolveRigidHead` is
    // sound across binder-introducing defs because a def's *head* term never
    // depends on its dummy binders. When the two roots are distinct rigid terms,
    // no unfolding or ACUI canonicalization can reconcile them. This is a
    // definite mismatch even though one or both surface heads is a
    // `termNeedsSemantic` def: the divergence is at THIS node, and a node can be
    // the hole only when it is the plug pair (excluded above) — a hole below
    // would force the two sides to share this head (hence the same rigid root).
    // `resolveRigidHead` returns null for ACUI / `@rewrite` / unavailable /
    // binder-rooted-body heads, so those still fall through to the abstain below.
    // If either surface head has an available transparent body, the body walker
    // below can refine same-root or cross def/raw pairs without materializing the
    // expansion. It threads body binders through scopes, treats dummy binders as
    // no-opinion, and never mints placeholders, preserving the shared dependency
    // budget.
    if (ln.* == .app and rn.* == .app) {
        if (def_match.rigidHeadMismatch(context, ln.app.term_id, rn.app.term_id)) {
            return true;
        }
        if (bodyCompareUseful(context, ln.app.term_id, rn.app.term_id)) {
            if (bodyExpandedMismatch(
                context,
                theorem,
                .{ .expr = left },
                .{ .expr = right },
                left_plug,
                right_plug,
                plugs_semantic,
                0,
            )) return true;
        }
    }

    if (headNeedsSemantic(context, ln) or headNeedsSemantic(context, rn)) return false;

    switch (ln.*) {
        .app => |la| switch (rn.*) {
            .app => |ra| {
                if (la.term_id == ra.term_id and la.args.len == ra.args.len) {
                    for (la.args, ra.args) |x, y| {
                        if (abstractDefiniteMismatch(
                            context,
                            theorem,
                            x,
                            y,
                            left_plug,
                            right_plug,
                            plugs_semantic,
                        )) {
                            return true;
                        }
                    }
                    return false;
                }
            },
            else => {},
        },
        else => {},
    }

    // The deeper rigid-divergence fallback is justified only when this node has no
    // hole below it, an argument that leans on raw==preprocessed structure. With a
    // reducible plug that can fail, so abstain and rely on the head clash above.
    if (plugs_semantic) return false;
    return def_match.rigidExprMismatch(context, theorem, left, right);
}

const BodyInfo = struct { body: TemplateExpr, nargs: usize };

const max_body_compare_depth = 64;

const BodyScope = struct {
    nargs: usize,
    kind: union(enum) {
        root: []const ExprId,
        nested: struct {
            args: []const TemplateExpr,
            parent: *const BodyScope,
        },
    },
};

const BodySide = union(enum) {
    unknown,
    expr: ExprId,
    tmpl: struct {
        template: TemplateExpr,
        scope: *const BodyScope,
    },
};

fn defBody(context: *const Context, term_id: u32) ?BodyInfo {
    if (!context.env.hasAvailableTerm(term_id)) return null;
    if (context.registry.acui_by_head.contains(term_id)) return null;
    if (context.registry.rewrites_by_head.contains(term_id)) return null;
    const term = context.env.terms.items[term_id];
    if (!(term.available and term.is_def)) return null;
    const body = term.body orelse return null;
    return .{ .body = body, .nargs = term.args.len };
}

fn bodyCompareUseful(
    context: *const Context,
    left_term_id: u32,
    right_term_id: u32,
) bool {
    return defBody(context, left_term_id) != null or
        defBody(context, right_term_id) != null;
}

fn scopedArg(side: BodySide) BodySide {
    const t = switch (side) {
        .tmpl => |value| value,
        else => return .unknown,
    };
    const idx = switch (t.template) {
        .binder => |value| value,
        .app => return side,
    };
    if (idx >= t.scope.nargs) return .unknown;
    switch (t.scope.kind) {
        .root => |args| {
            if (idx >= args.len) return .unknown;
            return .{ .expr = args[idx] };
        },
        .nested => |nested| {
            if (idx >= nested.args.len) return .unknown;
            return .{ .tmpl = .{
                .template = nested.args[idx],
                .scope = nested.parent,
            } };
        },
    }
}

fn bodyExpandedMismatch(
    context: *const Context,
    theorem: *const TheoremContext,
    left: BodySide,
    right: BodySide,
    left_plug: ExprId,
    right_plug: ExprId,
    plugs_semantic: bool,
    depth: usize,
) bool {
    if (depth >= max_body_compare_depth) return false;
    if (bodySidesCouldBeHole(
        context,
        theorem,
        left,
        right,
        left_plug,
        right_plug,
        plugs_semantic,
    )) return false;

    switch (left) {
        .unknown => return false,
        .tmpl => |t| switch (t.template) {
            .binder => return bodyExpandedMismatch(
                context,
                theorem,
                scopedArg(left),
                right,
                left_plug,
                right_plug,
                plugs_semantic,
                depth + 1,
            ),
            .app => |app| {
                if (defBody(context, app.term_id)) |info| {
                    if (app.args.len != info.nargs) return false;
                    const child = BodyScope{
                        .nargs = info.nargs,
                        .kind = .{ .nested = .{
                            .args = app.args,
                            .parent = t.scope,
                        } },
                    };
                    return bodyExpandedMismatch(
                        context,
                        theorem,
                        .{ .tmpl = .{
                            .template = info.body,
                            .scope = &child,
                        } },
                        right,
                        left_plug,
                        right_plug,
                        plugs_semantic,
                        depth + 1,
                    );
                }
            },
        },
        .expr => |expr| {
            const node = theorem.interner.node(expr);
            switch (node.*) {
                .app => |app| {
                    if (defBody(context, app.term_id)) |info| {
                        if (app.args.len != info.nargs) return false;
                        const child = BodyScope{
                            .nargs = info.nargs,
                            .kind = .{ .root = app.args },
                        };
                        return bodyExpandedMismatch(
                            context,
                            theorem,
                            .{ .tmpl = .{
                                .template = info.body,
                                .scope = &child,
                            } },
                            right,
                            left_plug,
                            right_plug,
                            plugs_semantic,
                            depth + 1,
                        );
                    }
                },
                .variable, .placeholder => {},
            }
        },
    }
    switch (right) {
        .unknown => return false,
        .tmpl => |t| switch (t.template) {
            .binder => return bodyExpandedMismatch(
                context,
                theorem,
                left,
                scopedArg(right),
                left_plug,
                right_plug,
                plugs_semantic,
                depth + 1,
            ),
            .app => |app| {
                if (defBody(context, app.term_id)) |info| {
                    if (app.args.len != info.nargs) return false;
                    const child = BodyScope{
                        .nargs = info.nargs,
                        .kind = .{ .nested = .{
                            .args = app.args,
                            .parent = t.scope,
                        } },
                    };
                    return bodyExpandedMismatch(
                        context,
                        theorem,
                        left,
                        .{ .tmpl = .{
                            .template = info.body,
                            .scope = &child,
                        } },
                        left_plug,
                        right_plug,
                        plugs_semantic,
                        depth + 1,
                    );
                }
            },
        },
        .expr => |expr| {
            const node = theorem.interner.node(expr);
            switch (node.*) {
                .app => |app| {
                    if (defBody(context, app.term_id)) |info| {
                        if (app.args.len != info.nargs) return false;
                        const child = BodyScope{
                            .nargs = info.nargs,
                            .kind = .{ .root = app.args },
                        };
                        return bodyExpandedMismatch(
                            context,
                            theorem,
                            left,
                            .{ .tmpl = .{
                                .template = info.body,
                                .scope = &child,
                            } },
                            left_plug,
                            right_plug,
                            plugs_semantic,
                            depth + 1,
                        );
                    }
                },
                .variable, .placeholder => {},
            }
        },
    }

    return compareReducedBodySides(
        context,
        theorem,
        left,
        right,
        left_plug,
        right_plug,
        plugs_semantic,
        depth,
    );
}

fn bodySidesCouldBeHole(
    context: *const Context,
    theorem: *const TheoremContext,
    left: BodySide,
    right: BodySide,
    left_plug: ExprId,
    right_plug: ExprId,
    plugs_semantic: bool,
) bool {
    if (plugs_semantic) {
        return bodySideCouldOccurAt(context, theorem, left, left_plug) and
            bodySideCouldOccurAt(context, theorem, right, right_plug);
    }
    return bodySideExprEquals(left, left_plug) and
        bodySideExprEquals(right, right_plug);
}

fn bodySideExprEquals(side: BodySide, plug: ExprId) bool {
    return switch (side) {
        .expr => |expr| expr == plug,
        .unknown, .tmpl => false,
    };
}

fn bodySideCouldOccurAt(
    context: *const Context,
    theorem: *const TheoremContext,
    side: BodySide,
    plug: ExprId,
) bool {
    switch (side) {
        .unknown => return true,
        .expr => |expr| return plugCouldOccurAt(context, theorem, expr, plug),
        .tmpl => |t| switch (t.template) {
            .binder => return bodySideCouldOccurAt(
                context,
                theorem,
                scopedArg(side),
                plug,
            ),
            .app => |app| return appCouldOccurAt(
                context,
                theorem,
                app.term_id,
                plug,
            ),
        },
    }
}

fn appCouldOccurAt(
    context: *const Context,
    theorem: *const TheoremContext,
    term_id: u32,
    plug: ExprId,
) bool {
    const pn = theorem.interner.node(plug);
    switch (pn.*) {
        .placeholder => return true,
        .variable => return def_match.rigidHeadOf(context, term_id) == null,
        .app => |pa| {
            const ph = def_match.rigidHeadOf(context, pa.term_id) orelse
                return true;
            const nh = def_match.rigidHeadOf(context, term_id) orelse
                return true;
            return nh == ph;
        },
    }
}

fn compareReducedBodySides(
    context: *const Context,
    theorem: *const TheoremContext,
    left: BodySide,
    right: BodySide,
    left_plug: ExprId,
    right_plug: ExprId,
    plugs_semantic: bool,
    depth: usize,
) bool {
    switch (left) {
        .unknown => return false,
        .expr => |left_expr| switch (right) {
            .unknown => return false,
            .expr => |right_expr| return abstractDefiniteMismatch(
                context,
                theorem,
                left_expr,
                right_expr,
                left_plug,
                right_plug,
                plugs_semantic,
            ),
            .tmpl => return exprTemplateMismatch(
                context,
                theorem,
                left_expr,
                right,
                left_plug,
                right_plug,
                plugs_semantic,
                depth,
            ),
        },
        .tmpl => switch (right) {
            .unknown => return false,
            .expr => |right_expr| return exprTemplateMismatch(
                context,
                theorem,
                right_expr,
                left,
                right_plug,
                left_plug,
                plugs_semantic,
                depth,
            ),
            .tmpl => return templateTemplateMismatch(
                context,
                theorem,
                left,
                right,
                left_plug,
                right_plug,
                plugs_semantic,
                depth,
            ),
        },
    }
}

fn exprTemplateMismatch(
    context: *const Context,
    theorem: *const TheoremContext,
    expr: ExprId,
    template_side: BodySide,
    expr_plug: ExprId,
    template_plug: ExprId,
    plugs_semantic: bool,
    depth: usize,
) bool {
    const expr_node = theorem.interner.node(expr);
    const template = switch (template_side) {
        .tmpl => |value| value,
        else => return false,
    };
    const template_app = switch (template.template) {
        .app => |app| app,
        .binder => return bodyExpandedMismatch(
            context,
            theorem,
            .{ .expr = expr },
            scopedArg(template_side),
            expr_plug,
            template_plug,
            plugs_semantic,
            depth + 1,
        ),
    };
    switch (expr_node.*) {
        .placeholder => return false,
        .variable => return def_match.rigidHeadOf(
            context,
            template_app.term_id,
        ) != null,
        .app => |expr_app| return appAppMismatch(
            context,
            theorem,
            .{ .expr = expr },
            expr_app.term_id,
            expr_app.args.len,
            template_side,
            template_app.term_id,
            template_app.args.len,
            expr_plug,
            template_plug,
            plugs_semantic,
            depth,
        ),
    }
}

fn templateTemplateMismatch(
    context: *const Context,
    theorem: *const TheoremContext,
    left: BodySide,
    right: BodySide,
    left_plug: ExprId,
    right_plug: ExprId,
    plugs_semantic: bool,
    depth: usize,
) bool {
    const left_template = switch (left) {
        .tmpl => |value| value,
        else => return false,
    };
    const right_template = switch (right) {
        .tmpl => |value| value,
        else => return false,
    };
    const left_app = switch (left_template.template) {
        .app => |app| app,
        .binder => return bodyExpandedMismatch(
            context,
            theorem,
            scopedArg(left),
            right,
            left_plug,
            right_plug,
            plugs_semantic,
            depth + 1,
        ),
    };
    const right_app = switch (right_template.template) {
        .app => |app| app,
        .binder => return bodyExpandedMismatch(
            context,
            theorem,
            left,
            scopedArg(right),
            left_plug,
            right_plug,
            plugs_semantic,
            depth + 1,
        ),
    };
    return appAppMismatch(
        context,
        theorem,
        left,
        left_app.term_id,
        left_app.args.len,
        right,
        right_app.term_id,
        right_app.args.len,
        left_plug,
        right_plug,
        plugs_semantic,
        depth,
    );
}

fn appAppMismatch(
    context: *const Context,
    theorem: *const TheoremContext,
    left: BodySide,
    left_term_id: u32,
    left_arg_count: usize,
    right: BodySide,
    right_term_id: u32,
    right_arg_count: usize,
    left_plug: ExprId,
    right_plug: ExprId,
    plugs_semantic: bool,
    depth: usize,
) bool {
    if (def_match.rigidHeadMismatch(
        context,
        left_term_id,
        right_term_id,
    )) return true;
    if (left_term_id != right_term_id) return false;
    if (left_arg_count != right_arg_count) return false;
    if (semantic.termNeedsSemantic(context, left_term_id)) return false;
    for (0..left_arg_count) |idx| {
        if (bodyExpandedMismatch(
            context,
            theorem,
            appArgSide(theorem, left, idx),
            appArgSide(theorem, right, idx),
            left_plug,
            right_plug,
            plugs_semantic,
            depth + 1,
        )) return true;
    }
    return false;
}

fn appArgSide(
    theorem: *const TheoremContext,
    side: BodySide,
    idx: usize,
) BodySide {
    switch (side) {
        .unknown => return .unknown,
        .expr => |expr| {
            const node = theorem.interner.node(expr);
            return switch (node.*) {
                .app => |app| blk: {
                    if (idx >= app.args.len) break :blk .unknown;
                    break :blk .{ .expr = app.args[idx] };
                },
                .variable, .placeholder => .unknown,
            };
        },
        .tmpl => |t| switch (t.template) {
            .binder => return .unknown,
            .app => |app| {
                if (idx >= app.args.len) return .unknown;
                return .{ .tmpl = .{
                    .template = app.args[idx],
                    .scope = t.scope,
                } };
            },
        },
    }
}

/// Sound over-approximation of "`node` could be a hole occurrence of `plug`" used
/// only when `plug` is reducible, so the raw-ExprId hole test (`node == plug`) is
/// unreliable — the plug appears in left/right only in its preprocessed form. The
/// validator preprocesses node and plug identically (transparent-def unfold +
/// ACUI/`@rewrite` canonicalize) before its raw-equality hole test, and that
/// preprocessing preserves a term's rigid head whenever `rigidHeadOf` resolves
/// (it returns null on exactly the ACUI/`@rewrite`/unavailable heads
/// canonicalization could rewrite). So at a genuine hole, node and plug share a
/// rigid root; we may declare "definitely not the hole" (return false) only when
/// both sides expose DISTINCT non-null rigid roots. Anything we cannot bound — a
/// null root on either side, a placeholder, the matching-root case — stays a
/// possible hole. Head-only and read-only (no unfold/intern/placeholder).
fn plugCouldOccurAt(
    context: *const Context,
    theorem: *const TheoremContext,
    node: ExprId,
    plug: ExprId,
) bool {
    if (node == plug) return true;
    const pn = theorem.interner.node(plug);
    const nn = theorem.interner.node(node);
    switch (pn.*) {
        // A placeholder plug could stand for anything once filled.
        .placeholder => return true,
        // A bare-variable plug is irreducible: preprocessing leaves it unchanged,
        // so the only node that becomes it is one that reduces to a leaf (a
        // reducible head) or the variable itself (handled by `node == plug`).
        .variable => return switch (nn.*) {
            .variable => false, // distinct irreducible leaves never reconcile
            .placeholder => true,
            .app => |na| def_match.rigidHeadOf(context, na.term_id) == null,
        },
        .app => |pa| {
            const ph = def_match.rigidHeadOf(context, pa.term_id) orelse return true;
            return switch (nn.*) {
                .placeholder => true,
                // The plug preprocesses to an app (rigid head `ph`); an
                // irreducible leaf can never equal it.
                .variable => false,
                .app => |na| {
                    const nh = def_match.rigidHeadOf(context, na.term_id) orelse return true;
                    return nh == ph;
                },
            };
        },
    }
}

fn headNeedsSemantic(context: *const Context, node: anytype) bool {
    return switch (node.*) {
        .app => |a| semantic.termNeedsSemantic(context, a.term_id),
        else => false,
    };
}

/// Purely structural template match (no normalization). Records each view binder
/// the first time its position is reached; flags a binder as conflicted if a
/// later position would bind it to a different expression. Best-effort: on a
/// structural divergence it simply stops descending that subtree, leaving the
/// already-recorded (and positionally correct) bindings intact.
///
/// It does NOT descend a `termNeedsSemantic` head (ACUI / transparent def /
/// `@rewrite` / unavailable): such a head has no canonical positional structure
/// that the normalization-aware view match would commit to, so a binder pinned
/// under it would be evidence the real matcher never forces — and could drive an
/// unsound prune. Leaving those binders unresolved makes the decl abstain, which
/// is safe (same discipline as the comparison phase).
fn matchTemplateStructural(
    context: *const Context,
    theorem: *const TheoremContext,
    template: TemplateExpr,
    expr_id: ExprId,
    bindings: []?ExprId,
    conflicted: []bool,
) void {
    switch (template) {
        .binder => |vi| {
            if (vi >= bindings.len) return;
            if (bindings[vi]) |existing| {
                if (existing != expr_id) conflicted[vi] = true;
            } else {
                bindings[vi] = expr_id;
            }
        },
        .app => |app| {
            if (semantic.termNeedsSemantic(context, app.term_id)) return;
            const node = theorem.interner.node(expr_id);
            switch (node.*) {
                .app => |concrete| {
                    if (concrete.term_id != app.term_id) return;
                    if (concrete.args.len != app.args.len) return;
                    for (app.args, concrete.args) |t_arg, c_arg| {
                        matchTemplateStructural(context, theorem, t_arg, c_arg, bindings, conflicted);
                    }
                },
                .variable, .placeholder => {},
            }
        },
    }
}
