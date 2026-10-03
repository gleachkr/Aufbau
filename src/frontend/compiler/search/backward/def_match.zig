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

/// Whether `source` provably cannot be `pattern` with the `@recover` `hole`
/// replaced by a single witness term. The validator's recover unfolds
/// transparent defs and canonicalizes ACUI terms before comparing, and neither
/// changes a rigid head, so this is `rigidExprMismatch` with every position at
/// the hole, or at a coercion chain around it, left open: the validator
/// re-sorts that subtree through the coercion graph (cross-sort `@recover`,
/// #215), so `F (v2t x)` against `F (n2t b)` recovers `b`.
pub fn recoverDefiniteMismatch(
    context: *const Context,
    theorem: *const TheoremContext,
    source: ExprId,
    pattern: ExprId,
    hole: ExprId,
) bool {
    return rigidMismatch(context, theorem, source, pattern, hole);
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

// Whether two heads resolve to distinct rigid roots (see `rigidHeadOf`), which
// no def unfolding or canonicalization can reconcile.
pub fn rigidHeadMismatch(
    context: *const Context,
    a_term_id: u32,
    b_term_id: u32,
) bool {
    const a_head = rigidHeadOf(context, a_term_id) orelse return false;
    const b_head = rigidHeadOf(context, b_term_id) orelse return false;
    return a_head != b_head;
}

/// The outermost RIGID head `term_id` presents after transparent-def head-chain
/// unfolding, or null when the chain bottoms out on an ACUI / `@rewrite` /
/// unavailable / binder-rooted-body head (no stable rigid root). Read-only and
/// head-only — it never interns, mints placeholders, or inspects dummy-bearing
/// arguments. The key invariant for callers reasoning about the validator's
/// preprocessing: that preprocessing (transparent-def unfold + ACUI/`@rewrite`
/// canonicalize) preserves this head whenever it is non-null, because it is null
/// on exactly the heads canonicalization could rewrite.
pub fn rigidHeadOf(context: *const Context, term_id: u32) ?u32 {
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
    return bag.lawOf(context, term_id) == .sequence;
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
        extractPartial(context, theorem, leaf, member, bindings);
    }
    for (
        leaves[leaf_len - suffix_len .. leaf_len],
        members[member_len - suffix_len .. member_len],
    ) |leaf, member| {
        extractPartial(context, theorem, leaf, member, bindings);
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
                .variable => return rigidHeadOf(context, app.term_id) != null,
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
    return rigidMismatch(context, theorem, a, b, null);
}

// `rigidExprMismatch`, holding no opinion at `hole` in `b` or at a coercion
// chain around it.
fn rigidMismatch(
    context: *const Context,
    theorem: *const TheoremContext,
    a: ExprId,
    b: ExprId,
    hole: ?ExprId,
) bool {
    if (a == b) return false;
    if (hole) |h| {
        if (b == h or coercedHole(context, theorem, b, h)) return false;
    }
    const na = theorem.interner.node(a);
    const nb = theorem.interner.node(b);
    // A `@rewrite`-reducible head on either side can rewrite to a different
    // head, so a rigid clash is never definite — e.g. a bound motive value
    // `const_ty k A` (reducible to `A` via `const_ty_eval`) compared against a
    // ref's `A`.
    for ([_]*const ExprNode{ na, nb }) |n| switch (n.*) {
        .app => |app| if (semantic.headClass(context, app.term_id) == .rewrite) return false,
        else => {},
    };
    switch (na.*) {
        .placeholder => return false,
        .variable => switch (nb.*) {
            // Distinct interned atoms are genuinely different and nothing
            // reconciles them: a `theorem_var` id is stable and a `dummy_var`
            // id comes from a monotonic counter, so distinct ids are distinct
            // variables.
            .variable => return true,
            .app => |bb| return rigidHeadOf(context, bb.term_id) != null,
            .placeholder => return false,
        },
        .app => |aa| switch (nb.*) {
            .placeholder => return false,
            .variable => return rigidHeadOf(context, aa.term_id) != null,
            .app => |bb| {
                if (lockstep.exprArgs(context, theorem, a, b)) |aligned| {
                    var args = aligned;
                    while (args.next()) |pair| {
                        if (rigidMismatch(context, theorem, pair.a, pair.b, hole)) return true;
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

// `expr` unfolded one layer when it is an application of an available
// transparent def at its full arity, else null. `allow_binder_defs` is as for
// `defBodyForUnfold`.
pub fn unfoldAppOnce(
    context: *const Context,
    theorem: *TheoremContext,
    expr: ExprId,
    allow_binder_defs: bool,
) !?ExprId {
    // A copy of the node payload: its `args` slice is a stable heap
    // allocation, so interning the unfolded body cannot invalidate it.
    const app = switch (theorem.interner.node(expr).*) {
        .app => |app| app,
        else => return null,
    };
    const info = defBodyForUnfold(context, app.term_id, allow_binder_defs) orelse return null;
    if (app.args.len != info.nargs) return null;
    return try unfoldDefBody(theorem, info, app.args);
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
//
// Unfolding a binder-introducing def on the ref side mints a placeholder per
// hidden variable, each taking a dependency slot. Only `bindings` can hold
// one afterwards, so every other slot the walk took is given back.
pub fn extractHypPartialBindings(
    context: *const Context,
    theorem: *TheoremContext,
    template: TemplateExpr,
    expr_id: ExprId,
    bindings: []?ExprId,
) void {
    const mark = theorem.depSlotMark();
    extractPartial(context, theorem, template, expr_id, bindings);
    theorem.releaseUnheldDepSlots(mark, &.{bindings});
}

fn extractPartial(
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
                    extractPartial(context, theorem, template, unfolded, bindings);
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
                    extractPartial(
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
                        const root = DefScope{ .nargs = info.nargs, .args = app.args, .parent = null };
                        walkDefBody(
                            ExtractRoot{ .context = context, .theorem = theorem, .bindings = bindings },
                            context,
                            theorem,
                            info.body,
                            &root,
                            expr_id,
                            true,
                            0,
                        ) catch {};
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
                    extractPartial(
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
            if (bag.isCommutative(context, app.term_id)) {
                acui.extractAcuiMemberBindings(
                    context,
                    theorem,
                    app.term_id,
                    template,
                    expr_id,
                    bindings,
                    extractPartial,
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
    switch (theorem.interner.node(expr_id).*) {
        .app => |concrete| if (concrete.term_id == head) return null,
        else => return null,
    }
    return unfoldAppOnce(context, theorem, expr_id, true) catch null;
}

/// One level of transparent-def unfolding on the template side of a walk: the
/// def application's argument templates, read in `parent`, or at rule-binder
/// level when `parent` is null. A body binder `idx < nargs` resolves to
/// `args[idx]`; a higher one is a hidden variable of the def and carries no
/// opinion.
pub const DefScope = struct {
    nargs: usize,
    args: []const TemplateExpr,
    parent: ?*const DefScope,
};

/// Walk a def `body`, read through `scope`, against `expr_id` in lockstep,
/// handing each body binder that resolves to a rule-level template to
/// `walker.root(template, expr)`. Transparent defs unfold lazily, only where
/// heads fail to align: first the body's own first-order def head (pushing a
/// scope), else the expression's head (`allow_ref_binder_defs` as for
/// `defBodyForUnfold`), so an expression written at any folding level
/// (`bic` ↔ `eqc` ↔ `eq · _ · _`) lines up without over-unfolding. A combiner
/// node, a variable, or a placeholder holds no opinion: a combiner's binders
/// are def parameters here, not rule binders, so no member pass applies.
pub fn walkDefBody(
    walker: anytype,
    context: *const Context,
    theorem: *TheoremContext,
    body: TemplateExpr,
    scope: *const DefScope,
    expr_id: ExprId,
    allow_ref_binder_defs: bool,
    depth: usize,
) error{OutOfMemory}!void {
    if (depth >= max_def_unfold_depth) return;
    switch (body) {
        .binder => |idx| {
            if (idx >= scope.nargs) return;
            const arg = scope.args[idx];
            const parent = scope.parent orelse return walker.root(arg, expr_id);
            return walkDefBody(walker, context, theorem, arg, parent, expr_id, allow_ref_binder_defs, depth + 1);
        },
        .app => |app| {
            if (context.registry.hasStructuralCombiner(app.term_id)) return;
            if (theorem.interner.node(expr_id).* != .app) return;
            if (lockstep.templateArgs(context, theorem, app, expr_id)) |aligned| {
                var args = aligned;
                while (args.next()) |pair| {
                    try walkDefBody(walker, context, theorem, pair.template, scope, pair.expr, allow_ref_binder_defs, depth + 1);
                }
                return;
            }
            if (defBodyForUnfold(context, app.term_id, false)) |info| {
                if (app.args.len != info.nargs) return;
                const child = DefScope{ .nargs = info.nargs, .args = app.args, .parent = scope };
                return walkDefBody(walker, context, theorem, info.body, &child, expr_id, allow_ref_binder_defs, depth + 1);
            }
            // The expression may be folded tighter than this body level (`bic X
            // Y` against an `eq ·`-spine, where bic ↦ eqc ↦ eq · _ · _), which no
            // template-side unfolding can align. A dependency slot running out
            // merely means the walk learns nothing more here.
            const unfolded = unfoldAppOnce(context, theorem, expr_id, allow_ref_binder_defs) catch |err| switch (err) {
                error.OutOfMemory => return error.OutOfMemory,
                else => return,
            } orelse return;
            return walkDefBody(walker, context, theorem, body, scope, unfolded, allow_ref_binder_defs, depth + 1);
        },
    }
}

/// `walkDefBody`'s root callback for hyp-side extraction.
const ExtractRoot = struct {
    context: *const Context,
    theorem: *TheoremContext,
    bindings: []?ExprId,

    pub fn root(self: ExtractRoot, template: TemplateExpr, expr_id: ExprId) error{OutOfMemory}!void {
        extractPartial(self.context, self.theorem, template, expr_id, self.bindings);
    }
};
