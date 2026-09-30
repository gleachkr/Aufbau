const types = @import("../types.zig");
const ExprId = @import("../../../expr.zig").ExprId;
const ExprNode = @import("../../../expr.zig").ExprNode;
const TheoremContext = @import("../../../expr.zig").TheoremContext;
const TemplateExpr = @import("../../../rules.zig").TemplateExpr;
const ArgInfo = @import("../../../parse_recovery.zig").ArgInfo;
const Context = types.Context;

const acui = @import("./acui.zig");
const semantic = @import("./semantic.zig");
const lockstep = @import("./lockstep.zig");
const bag = @import("./bag.zig");

const isRigidHead = semantic.isRigidHead;
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
    // A coercion chain around the hole is itself a recovery site: the
    // validator re-sorts the source subtree through the coercion graph
    // (cross-sort `@recover`, #215), so the chain's heads are not a rigid
    // skeleton to clash on — `F (v2t x)` against `F (n2t b)` recovers `b`.
    if (coercedHole(context, theorem, pattern, hole)) return false;
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
    // Same head: only the args it forces must agree. A def arg the body drops
    // (`K x y ≡ K x z` for `K a b := a`) or a `@rewrite` head's arg can differ
    // in a source the validator still accepts.
    var args = lockstep.exprArgs(context, theorem, source, pattern) orelse return false;
    while (args.next()) |pair| {
        if (recoverDefiniteMismatch(context, theorem, pair.a, pair.b, hole)) return true;
    }
    return false;
}

// Whether `expr` is the hole wrapped in nothing but declared coercions.
fn coercedHole(
    context: *const Context,
    theorem: *const TheoremContext,
    expr: ExprId,
    hole: ExprId,
) bool {
    var current = expr;
    while (current != hole) {
        const app = switch (theorem.interner.node(current).*) {
            .app => |app| app,
            else => return false,
        };
        if (app.args.len != 1 or !context.env.isCoercionTerm(app.term_id)) {
            return false;
        }
        current = app.args[0];
    }
    return true;
}

// True when the node is an application whose head term can be rewritten away
// by a `@rewrite` rule (so its head is not a reliable rigid key). Used to
// withhold a definite-mismatch verdict, mirroring the reducible-head guards in
// shape.zig and `semantic.isRigidHead`.
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
// is independent of the def's dummies. Returns null when the chain hits an ACUI combiner (canonicalization could
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
        switch (semantic.headClass(context, current)) {
            .rigid => return current,
            // Follow a def to the head its body presents.
            .def => switch (context.env.terms.items[current].body.?) {
                .app => |app| current = app.term_id,
                .binder => return null,
            },
            // Canonicalization can rewrite an ACUI or `@rewrite` head, even a
            // `@rewrite` head that is an ordinary term, so it is no stable root.
            .acui, .rewrite, .unavailable => return null,
        }
    }
    return null;
}

// True when `term_id` heads a structural combiner declared with neither
// commutativity nor idempotence, so its members form a sequence: two spines
// are equal exactly when their flattened, unit-free member lists are.
fn acuiIsOrdered(context: *const Context, term_id: u32) bool {
    const combiner = context.registry.acui_by_head.get(term_id) orelse return false;
    return combiner.comm_name == null and combiner.idem_name == null;
}

// Whether a sequence entry is exactly one member: an application whose head
// no conversion can turn into a combiner spine or the unit. A binder, a
// variable, a placeholder, or a def or `@rewrite` head may stand for any
// number of members.
fn templateIsSingleMember(context: *const Context, template: TemplateExpr) bool {
    return switch (template) {
        .binder => false,
        .app => |app| isRigidHead(context, app.term_id),
    };
}

fn exprIsSingleMember(
    context: *const Context,
    theorem: *const TheoremContext,
    expr_id: ExprId,
) bool {
    return switch (theorem.interner.node(expr_id).*) {
        .variable, .placeholder => false,
        .app => |app| isRigidHead(context, app.term_id),
    };
}

// Order-aware extraction under an ordered combiner (`acuiIsOrdered`). Both
// sides are flattened to their member sequences. Single-member template leaves
// before the first multi-member leaf align with the ref's leading members, and
// those after the last one with its trailing members; any other alignment
// would reorder the sequence. So when every aligned ref member is itself a
// single member, those pairs are forced and extracted. With no multi-member
// leaf the lengths must agree and every pair is forced. With exactly one, an
// unbound bare binder, it is forced to the members in between (the unit when
// there are none). E.g. martin_lof's `var` concludes `g , x : A ⊢ x : A`;
// against `g , k : Nat , ih : Nat` in any association this pins
// `x : A := ih : Nat` and `g := g , k : Nat`, where a positional walk of the
// right-nested spine `g , (k : Nat , ih : Nat)` would bind `g := g`.
fn extractOrderedSpineBindings(
    context: *const Context,
    theorem: *TheoremContext,
    head_id: u32,
    template: TemplateExpr,
    expr_id: ExprId,
    bindings: []?ExprId,
) void {
    const leaf_bag = bag.flattenTemplate(context, head_id, template) orelse return;
    const leaves = leaf_bag.slice();
    const leaf_len = leaves.len;
    const member_bag = bag.flatten(context, theorem, head_id, expr_id) orelse return;
    const members = member_bag.slice();
    const member_len = members.len;

    var first_multi: ?usize = null;
    var last_multi: usize = 0;
    var multi_count: usize = 0;
    for (leaves, 0..) |leaf, i| {
        if (templateIsSingleMember(context, leaf)) continue;
        if (first_multi == null) first_multi = i;
        last_multi = i;
        multi_count += 1;
    }
    const prefix_len = first_multi orelse leaf_len;
    const suffix_len = if (first_multi == null) 0 else leaf_len - last_multi - 1;
    if (first_multi == null) {
        if (leaf_len != member_len) return;
    } else if (prefix_len + suffix_len > member_len) return;

    // Every aligned ref entry must be exactly one member, or the alignment is
    // not forced and nothing is extracted.
    for (members[0..prefix_len]) |member| {
        if (!exprIsSingleMember(context, theorem, member)) return;
    }
    for (members[member_len - suffix_len .. member_len]) |member| {
        if (!exprIsSingleMember(context, theorem, member)) return;
    }
    for (leaves[0..prefix_len], members[0..prefix_len]) |leaf, member| {
        extractHypPartialBindings(context, theorem, leaf, member, bindings);
    }
    for (
        leaves[leaf_len - suffix_len .. leaf_len],
        members[member_len - suffix_len .. member_len],
    ) |leaf, member| {
        extractHypPartialBindings(context, theorem, leaf, member, bindings);
    }

    if (multi_count != 1) return;
    const idx = switch (leaves[first_multi.?]) {
        .binder => |b| b,
        .app => return,
    };
    if (idx >= bindings.len or bindings[idx] != null) return;
    const middle = members[prefix_len .. member_len - suffix_len];
    bindings[idx] = (bag.build(context, theorem, head_id, middle) catch return) orelse return;
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
            // A `@rewrite` head can reduce to a *different* head, so no clash
            // with it is definite (`[y/x][q/refl A x] C` vs `Id A x x`: the
            // `sb_ty` head rewrites away).
            if (semantic.headClass(context, app.term_id) == .rewrite) return false;
            switch (theorem.interner.node(ref).*) {
                // A placeholder may still stand for anything.
                .placeholder => return false,
                // A compound with a rigid root can't equal a bare atom.
                .variable => return resolveRigidHead(context, app.term_id) != null,
                .app => |concrete| {
                    // Same head: compare the args it forces. No def is assumed
                    // injective: an arg its body drops (the `const` trap) or
                    // places only under an ACUI or `@rewrite` head is skipped.
                    if (lockstep.templateArgs(context, theorem, app, ref)) |aligned| {
                        var args = aligned;
                        while (args.next()) |pair| {
                            if (templateDefiniteMismatch(
                                context,
                                theorem,
                                pair.template,
                                pair.expr,
                                bindings,
                            )) return true;
                        }
                        return false;
                    }
                    // Different heads are definite only when def unfolding
                    // exposes distinct rigid roots on both sides.
                    return rigidHeadMismatch(context, app.term_id, concrete.term_id);
                },
            }
        },
    }
}

// Rigid-divergence comparison of two committed expressions (the bound-binder
// counterpart of `templateDefiniteMismatch`). Two distinct rigid atoms, a rigid
// atom against a compound with a rigid root, compounds with distinct rigid
// roots, or a divergence in an argument their shared head forces are all
// unbridgeable. Anything else touching an ACUI/`@rewrite`/unavailable head or a
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
    // ref's `A`.
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
        .app => |aa| switch (nb.*) {
            .placeholder => return false,
            .variable => return resolveRigidHead(context, aa.term_id) != null,
            .app => |bb| {
                if (lockstep.exprArgs(context, theorem, a, b)) |aligned| {
                    var args = aligned;
                    while (args.next()) |pair| {
                        if (rigidExprMismatch(context, theorem, pair.a, pair.b)) return true;
                    }
                    return false;
                }
                return rigidHeadMismatch(context, aa.term_id, bb.term_id);
            },
        },
    }
}

pub const UnfoldDefInfo = struct {
    body: TemplateExpr,
    nargs: usize,
    dummies: []const ArgInfo,
};

// The body of `term_id` when it is an available transparent def, for unfolding
// one layer. A binder-introducing def (one with dummy args) is returned only
// when `allow_binder_defs`: its unfolding materializes each dummy as a fresh
// placeholder (see `unfoldDefBody`), which only loosens later matching, so
// only a caller that tolerates placeholders may ask for it.
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

// Bound on nested def unfolding. Def bodies reference only earlier-declared
// terms, so the chain is acyclic; this caps pathologically deep stacks.
pub const max_def_unfold_depth = 64;

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
            // An ordered (non-commutative, non-idempotent) combiner: align the
            // flattened member sequences, never the binary spines, whose
            // association is arbitrary. A ref folded behind a def presents no
            // sequence to align, so unfold it first.
            if (acuiIsOrdered(context, app.term_id)) {
                if (unfoldForeignRefDef(context, theorem, app.term_id, expr_id)) |unfolded| {
                    extractHypPartialBindings(context, theorem, template, unfolded, bindings);
                    return;
                }
                extractOrderedSpineBindings(
                    context,
                    theorem,
                    app.term_id,
                    template,
                    expr_id,
                    bindings,
                );
                return;
            }
            const node = theorem.interner.node(expr_id);
            if (lockstep.templateArgs(context, theorem, app, expr_id)) |aligned| {
                // Positional walk over the args the head forces (see
                // `lockstep`). That skips an ACUI spine, where pinning a bare
                // binder leaf (e.g. `ex_elim`'s context `H` in `H , p`) to the
                // ref's first arg would guess at the split and swallow members
                // of a sibling leaf; the member pass below handles commutative
                // combiners instead. It also skips a `@rewrite` head's args and
                // a def arg its body drops, where the value would be a guess.
                var args = aligned;
                while (args.next()) |pair| {
                    extractHypPartialBindings(
                        context,
                        theorem,
                        pair.template,
                        pair.expr,
                        bindings,
                    );
                }
            } else if (node.* == .app) {
                if (defBodyForUnfold(context, app.term_id, false)) |info| {
                    // Head mismatch but the template head is a transparent
                    // first-order def whose unfolding may line up with the
                    // ref. The ref is commonly stored in the def's *unfolded*
                    // form (e.g. hyp `P ⇔ Q` = `bic(P,Q)` against a ref proven
                    // as `≃[𝔹] a = b` = `eqc(𝔹,a,b)`), so the plain positional
                    // walk bails at `bic`≠`eqc` and the binders under the def
                    // never get pinned. Unfold the template body and continue
                    // extraction against the same ref; the def is transparent
                    // and first-order, so the binder values are forced by the
                    // ref.
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
                } else if (unfoldForeignRefDef(context, theorem, app.term_id, expr_id)) |unfolded| {
                    // Symmetric case: the *ref* head is a def folded over the
                    // template's structure — e.g. the view hyp `G ⊢ ∃ x p`
                    // (`nd(G, ex(λx.p))`) against a ref proven as
                    // `has_preimage f X y` (= `∃ x (x∈X ∧ maps f x y)`) or
                    // euclid's `a < b` (= `∃ k …`). The positional walk bails
                    // at `ex` ≠ `has_preimage`, so the existential body binder
                    // `p` never pins and the `@recover` containment injection
                    // for the paired hypothesis stays inert. Unfold the ref one
                    // layer and re-extract against the same template, exposing
                    // the `∃` so `p` binds.
                    extractHypPartialBindings(
                        context,
                        theorem,
                        template,
                        unfolded,
                        bindings,
                    );
                }
            }
            // For an ACUI combiner the positional walk above usually bails at
            // the head (the ref writes the same multiset in a different shape),
            // leaving leaf binders unbound. Recover those from the ref's
            // members, but only where a leaf has a single shape-compatible
            // member so the value is forced (see `extractAcuiMemberBindings`).
            //
            // Gated on commutativity: the member extractor treats the combiner's
            // arguments as a multiset, which is only valid when `@acui` declared
            // C. An ordered combiner (neither C nor I) returned above through
            // `extractOrderedSpineBindings`; an idempotent non-commutative one
            // keeps only the positional walk.
            if (acui.isCommutative(context, app.term_id)) {
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

// `expr_id` unfolded one layer when it is an application of a def other than
// `head` (binder-introducing defs included), else null. Each dummy of the def
// becomes a fresh placeholder (`unfoldDefBody`); that only loosens later
// matching, and the bindings extraction writes merely seed downstream lookups
// and the recover guard, so it is sound for extraction. The strict matcher
// stays first-order (see `defBodyForUnfold`).
fn unfoldForeignRefDef(
    context: *const Context,
    theorem: *TheoremContext,
    head: u32,
    expr_id: ExprId,
) ?ExprId {
    const concrete = switch (theorem.interner.node(expr_id).*) {
        .app => |concrete| concrete,
        else => return null,
    };
    if (concrete.term_id == head) return null;
    const info = defBodyForUnfold(context, concrete.term_id, true) orelse return null;
    if (concrete.args.len != info.nargs) return null;
    return unfoldDefBody(theorem, info, concrete.args) catch null;
}

// Scope for extraction through transparent-def unfoldings. A `template_root` carries the rule template's argument
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
            if (lockstep.templateArgs(context, theorem, app, expr_id)) |aligned| {
                // Heads aligned at this folding level: descend into the args
                // the head forces.
                var args = aligned;
                while (args.next()) |pair| {
                    extractScopedBindings(
                        context,
                        theorem,
                        pair.template,
                        scope,
                        pair.expr,
                        bindings,
                        depth + 1,
                    );
                }
                return;
            }
            // Heads differ: unfold one more transparent-def layer on the template
            // side and retry against the same ref.
            if (defBodyForUnfold(context, app.term_id, false)) |info| {
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
