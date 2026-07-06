const std = @import("std");
const types = @import("../types.zig");
const ExprId = @import("../../../expr.zig").ExprId;
const TheoremContext = @import("../../../expr.zig").TheoremContext;
const TemplateExpr = @import("../../../rules.zig").TemplateExpr;
const ArgInfo = @import("../../../parse_recovery.zig").ArgInfo;
const StructuralCombiner = @import("../../../rewrite_registry.zig").StructuralCombiner;
const Context = types.Context;
const semantic = @import("./semantic.zig");
const exprNeedsSemantic = semantic.exprNeedsSemantic;
const templateNeedsSemantic = semantic.templateNeedsSemantic;
const termNeedsSemantic = semantic.termNeedsSemantic;
const OpenTerms = @import("../../inference/open_terms.zig");
const DeepVerdictCache = types.DeepVerdictCache;

const DeepExprMismatchFn = fn (*const Context, *TheoremContext, ExprId, ExprId, usize) bool;

const max_acui_members = 64;

const AcuiMember = struct {
    expr: ExprId,
    consumed: bool = false,
};

pub fn extractAcuiMemberBindings(
    context: *const Context,
    theorem: *TheoremContext,
    head_id: u32,
    template: TemplateExpr,
    container: ExprId,
    bindings: []?ExprId,
    comptime extract_fn: fn (
        *const Context,
        *TheoremContext,
        TemplateExpr,
        ExprId,
        []?ExprId,
    ) void,
) void {
    var members: [max_acui_members]AcuiMember = undefined;
    var count: usize = 0;
    // Bail (extract nothing) on an unusually large context rather than risk
    // truncating the multiset, which could make a member look spuriously unique.
    if (!collectAcuiMembers(theorem, container, head_id, &members, &count)) return;
    const pool = members[0..count];

    // Pass 1: consume ref members claimed by the bound sibling leaves.
    consumeBoundLeafMembers(theorem, head_id, template, bindings, pool);
    // Pass 2: pin each unbound leaf from a unique remaining member.
    extractUnboundLeafMembers(
        context,
        theorem,
        head_id,
        template,
        bindings,
        pool,
        extract_fn,
    );
}

// Flatten the ACUI multiset rooted at `container` into `buf`. A node headed by
// `head_id` is a nested combiner (recurse); anything else is one member.
// Returns false if the multiset would exceed `buf` (caller then bails).
fn collectAcuiMembers(
    theorem: *const TheoremContext,
    container: ExprId,
    head_id: u32,
    buf: []AcuiMember,
    count: *usize,
) bool {
    const node = theorem.interner.node(container);
    switch (node.*) {
        .app => |app| {
            if (app.term_id == head_id) {
                for (app.args) |arg| {
                    if (!collectAcuiMembers(theorem, arg, head_id, buf, count)) {
                        return false;
                    }
                }
                return true;
            }
        },
        else => {},
    }
    if (count.* >= buf.len) return false;
    buf[count.*] = .{ .expr = container };
    count.* += 1;
    return true;
}

// Mark consumed the pool members claimed by template leaves that have no
// unbound binder: a bound binder (e.g. `G`) expands to its own multiset; any
// other fully-bound leaf matches a single member directly.
fn consumeBoundLeafMembers(
    theorem: *const TheoremContext,
    head_id: u32,
    template: TemplateExpr,
    bindings: []const ?ExprId,
    pool: []AcuiMember,
) void {
    switch (template) {
        .binder => |idx| {
            if (idx >= bindings.len) return;
            const value = bindings[idx] orelse return;
            var sub: [max_acui_members]AcuiMember = undefined;
            var sub_n: usize = 0;
            if (!collectAcuiMembers(theorem, value, head_id, &sub, &sub_n)) return;
            for (sub[0..sub_n]) |member| consumePoolMemberById(pool, member.expr);
        },
        .app => |app| {
            if (app.term_id == head_id) {
                for (app.args) |arg| {
                    consumeBoundLeafMembers(theorem, head_id, arg, bindings, pool);
                }
                return;
            }
            if (templateHasUnboundBinder(template, bindings)) return;
            for (pool) |*slot| {
                if (slot.consumed) continue;
                if (templateMatchesExprReadOnly(theorem, template, slot.expr, bindings)) {
                    slot.consumed = true;
                    return;
                }
            }
        },
    }
}

fn consumePoolMemberById(pool: []AcuiMember, expr: ExprId) void {
    for (pool) |*slot| {
        if (!slot.consumed and slot.expr == expr) {
            slot.consumed = true;
            return;
        }
    }
}

// For each template leaf with an unbound binder, if exactly one unconsumed pool
// member is shape-compatible, pin the leaf's binders from it and consume it.
fn extractUnboundLeafMembers(
    context: *const Context,
    theorem: *TheoremContext,
    head_id: u32,
    template: TemplateExpr,
    bindings: []?ExprId,
    pool: []AcuiMember,
    comptime extract_fn: fn (
        *const Context,
        *TheoremContext,
        TemplateExpr,
        ExprId,
        []?ExprId,
    ) void,
) void {
    switch (template) {
        // A bare binder captures "everything else"; can't pin to one member.
        .binder => return,
        .app => |app| {
            if (app.term_id == head_id) {
                for (app.args) |arg| {
                    extractUnboundLeafMembers(
                        context,
                        theorem,
                        head_id,
                        arg,
                        bindings,
                        pool,
                        extract_fn,
                    );
                }
                return;
            }
            if (!templateHasUnboundBinder(template, bindings)) return;
            var found: ?usize = null;
            var matches: usize = 0;
            for (pool, 0..) |slot, i| {
                if (slot.consumed) continue;
                if (templateMatchesExprReadOnly(theorem, template, slot.expr, bindings)) {
                    matches += 1;
                    found = i;
                }
            }
            if (matches == 1) {
                const idx = found.?;
                extract_fn(context, theorem, template, pool[idx].expr, bindings);
                pool[idx].consumed = true;
            }
        },
    }
}

fn templateHasUnboundBinder(
    template: TemplateExpr,
    bindings: []const ?ExprId,
) bool {
    switch (template) {
        .binder => |idx| return idx < bindings.len and bindings[idx] == null,
        .app => |app| {
            for (app.args) |arg| {
                if (templateHasUnboundBinder(arg, bindings)) return true;
            }
            return false;
        },
    }
}

// The ambiguous-principal companion to `extractUnboundLeafMembers`. The seed
// pins a backward branching rule's principal-formula binders (e.g. `lor`'s a,b
// in `g , (a ∨ b) ⊢ d`) from the goal's antecedent ONLY when exactly one goal
// member is shape-compatible — when several are (multiple `∨`/`→` members), it
// abstains, leaving a,b open so the backtracker pins them from *loose* pool
// matches (the near-universal premise `g , a ⊢ d`), which is where the
// generation search spends ~98% of its `tryCandidate` calls on doomed tuples.
//
// This routine instead REPORTS that ambiguity: it returns the first unbound
// principal leaf together with every shape-compatible goal member, so the caller
// can fan out one tightly-seeded candidate per member (standard sequent-search
// principal-formula selection). Sound/complete: the conclusion must ACUI-equal
// the goal, so the principal is a *required* member of the goal multiset — the
// enumerated members are exactly the legal principal choices, no more.
//
// Returns null when no unbound leaf is ambiguous (every one has 0 or 1 matches,
// i.e. the existing single-candidate behaviour). `members` is owned by the
// caller. Commutativity-gated for the same reason as `extractAcuiMemberBindings`
// (the member multiset is only order-insensitive under a `@acui`-declared C).
pub const PrincipalFanout = struct {
    /// The principal leaf template whose binders the variants pin (e.g.
    /// `hyp(or(a,b))`). The same leaf `extractHypPartialBindings` consumes.
    leaf: TemplateExpr,
    /// Every goal member shape-compatible with `leaf`; one variant per member.
    members: []ExprId,
};

pub fn findAmbiguousPrincipal(
    allocator: std.mem.Allocator,
    context: *const Context,
    theorem: *TheoremContext,
    head_id: u32,
    template: TemplateExpr,
    container: ExprId,
    bindings: []const ?ExprId,
) !?PrincipalFanout {
    if (!isCommutative(context, head_id)) return null;
    var members: [max_acui_members]AcuiMember = undefined;
    var count: usize = 0;
    if (!collectAcuiMembers(theorem, container, head_id, &members, &count)) return null;
    const pool = members[0..count];
    // Soundness gate for REPLACING the loose candidate with the fan-out. The
    // member match below (`templateMatchesExprReadOnly`) is purely structural —
    // it never unfolds a transparent def — so it equals the validator's true
    // matchable set only when every member is fully rigid. If any member could
    // unfold to the principal's shape (a `lt`/`le`/`∈`-style def, as in
    // euclid/zermelo), read-only enumeration may under-count and dropping the
    // loose candidate would lose a proof; bail and keep the existing behaviour.
    // Additive connective contexts (all `hyp(im/or/an/…)`) are fully rigid, so
    // this fires exactly where it is complete and stays inert elsewhere.
    for (pool) |member| {
        if (!exprFullyRigid(context, theorem, member.expr)) return null;
    }
    // Pass 1 (as in `extractAcuiMemberBindings`): consume members claimed by
    // already-bound sibling leaves, so they don't inflate a principal's count.
    consumeBoundLeafMembers(theorem, head_id, template, bindings, pool);
    return findAmbiguousLeaf(allocator, theorem, head_id, template, bindings, pool);
}

// A member is fan-out-safe only if the strict read-only matcher sees its true
// shape — i.e. it embeds no transparent-def or semantic head the validator's
// def-aware matcher could unfold past. Bound atoms are rigid; an open
// placeholder (meta) could match anything, so it is treated as non-rigid.
fn exprFullyRigid(
    context: *const Context,
    theorem: *const TheoremContext,
    expr_id: ExprId,
) bool {
    switch (theorem.interner.node(expr_id).*) {
        .variable => return true,
        .placeholder => return false,
        .app => |app| {
            if (termNeedsSemantic(context, app.term_id)) return false;
            if (headIsTransparentDef(context, app.term_id)) return false;
            for (app.args) |arg| {
                if (!exprFullyRigid(context, theorem, arg)) return false;
            }
            return true;
        },
    }
}

// True when `term_id` heads a transparent (unfoldable) definition. Inlined from
// `defBodyForUnfold`'s essential test to avoid importing `prune` (which
// imports this module). ACUI combiner heads are structural, not defs.
fn headIsTransparentDef(context: *const Context, term_id: u32) bool {
    if (!context.env.hasAvailableTerm(term_id)) return false;
    if (context.registry.acui_by_head.contains(term_id)) return false;
    const term = context.env.terms.items[term_id];
    return term.available and term.is_def and term.body != null;
}

fn findAmbiguousLeaf(
    allocator: std.mem.Allocator,
    theorem: *TheoremContext,
    head_id: u32,
    template: TemplateExpr,
    bindings: []const ?ExprId,
    pool: []AcuiMember,
) !?PrincipalFanout {
    switch (template) {
        // A bare binder captures "everything else"; never a principal.
        .binder => return null,
        .app => |app| {
            if (app.term_id == head_id) {
                for (app.args) |arg| {
                    if (try findAmbiguousLeaf(
                        allocator,
                        theorem,
                        head_id,
                        arg,
                        bindings,
                        pool,
                    )) |fan| return fan;
                }
                return null;
            }
            if (!templateHasUnboundBinder(template, bindings)) return null;
            var matches = std.ArrayListUnmanaged(ExprId){};
            errdefer matches.deinit(allocator);
            for (pool) |slot| {
                if (slot.consumed) continue;
                if (!templateMatchesExprReadOnly(theorem, template, slot.expr, bindings)) continue;
                // Dedup idempotent-ACUI duplicates: the same interned member can
                // appear twice in the flattened multiset (e.g. `g , a , a`), and
                // each would pin the principal identically — a byte-identical
                // variant that only wastes node budget. Skip the repeat.
                var seen = false;
                for (matches.items) |m| {
                    if (m == slot.expr) {
                        seen = true;
                        break;
                    }
                }
                if (!seen) try matches.append(allocator, slot.expr);
            }
            // matches == 1 is the seed's existing single-candidate case (left to
            // `extractUnboundLeafMembers`); only >1 needs fan-out.
            if (matches.items.len > 1) {
                return PrincipalFanout{
                    .leaf = template,
                    .members = try matches.toOwnedSlice(allocator),
                };
            }
            matches.deinit(allocator);
            return null;
        },
    }
}

pub fn isCommutative(context: *const Context, term_id: u32) bool {
    const combiner = context.registry.acui_by_head.get(term_id) orelse return false;
    return combiner.comm_name != null;
}

/// True when ANY registered structural combiner declares commutativity — the
/// precondition for the member-wise ACUI read-back pass to be able to do
/// anything at all. Cached per generation driver so theories without
/// commutative combiners skip that pass entirely.
pub fn hasCommutativeCombiner(context: *const Context) bool {
    var it = context.registry.acui_by_head.iterator();
    while (it.next()) |entry| {
        if (entry.value_ptr.comm_name != null) return true;
    }
    return false;
}

// When the template uses an associative combiner (one registered as @acui),
// the structural `matchTemplate` walker can fail purely because the ref
// happens to write the same multiset of elements in a different shape — e.g.
// rule template `g, a ⊢ c` against ref `prime m ⊢ …`, where the ref's ctx
// is a singleton (`hyp(prime m)`) and the template demands a binary `join`.
// Even though structural alignment fails, an ACUI matcher could rearrange
// the ref's elements unless one of the required elements is provably absent.
//
// This precheck looks only at template subterms underneath an ACUI-rooted
// node where the binders happen to be already bound. For each such required
// subterm, we walk the corresponding ref subtree and ask "is there any leaf
// element that the (read-only) bound subterm matches?" If not, the rule
// candidate cannot satisfy this hypothesis under any ACUI rearrangement.
//
// The check requires only associativity. Without it, `f(f(a,b),c)` and
// `f(a,f(b,c))` are distinct expressions, not two shapes of one multiset,
// and "is X a member?" is ill-defined. Commutativity, idempotency, and the
// unit element are irrelevant: if a unit appears as a leaf, it just fails
// equality with the target, same outcome as if it weren't there. So this
// works equally for A, AU, AC, ACU, and full ACUI combiners; we never need
// to consult the registry beyond "is this term_id flagged as ACUI?".
//
// The plausibility path is conservative around semantic heads: when a
// transparent def or ACUI combiner could reconcile the required member with a
// ref member, it returns "present" and leaves the expensive verdict to the
// validator. The extraction path below keeps its stricter structural matcher,
// because pinning from a merely plausible member could consume the wrong slot.
pub fn acuiBoundMembersPlausible(
    context: *const Context,
    theorem: *const TheoremContext,
    template: TemplateExpr,
    expr_id: ExprId,
    bindings: []const ?ExprId,
) bool {
    return acuiPrecheckWalk(
        context,
        theorem,
        template,
        expr_id,
        bindings,
    );
}

fn acuiPrecheckWalk(
    context: *const Context,
    theorem: *const TheoremContext,
    template: TemplateExpr,
    expr_id: ExprId,
    bindings: []const ?ExprId,
) bool {
    switch (template) {
        .binder => return true,
        .app => |app| {
            if (context.registry.acui_by_head.contains(app.term_id)) {
                return acuiCheckRequiredElements(
                    context,
                    theorem,
                    template,
                    expr_id,
                    app.term_id,
                    bindings,
                );
            }
            // Non-ACUI head: structurally line up template and ref so that
            // child positions point at corresponding ref subtrees. If they
            // don't line up at the rigid head, `matchTemplate` already
            // failed for an unrelated reason and we have no opinion.
            const node = theorem.interner.node(expr_id);
            switch (node.*) {
                .variable, .placeholder => return true,
                .app => |concrete| {
                    if (concrete.term_id != app.term_id) return true;
                    if (concrete.args.len != app.args.len) return true;
                    for (app.args, concrete.args) |tmpl_arg, conc_arg| {
                        if (!acuiPrecheckWalk(
                            context,
                            theorem,
                            tmpl_arg,
                            conc_arg,
                            bindings,
                        )) return false;
                    }
                    return true;
                },
            }
        },
    }
}

// Inside an ACUI-rooted template subtree, each "leaf" (a sub-template that
// isn't another nested application of the same combiner) is a required
// element of the ref's ACUI multiset. For each such leaf, search the ref's
// subtree for a member that the leaf (with current bindings) could match
// against. Returns false if any required leaf has no compatible member.
fn acuiCheckRequiredElements(
    context: *const Context,
    theorem: *const TheoremContext,
    template: TemplateExpr,
    container: ExprId,
    head_id: u32,
    bindings: []const ?ExprId,
) bool {
    switch (template) {
        .binder => |idx| {
            // A binder at the multiset level (e.g. `$h` in `join($h, …)`)
            // captures "everything else". With or without a value, we can't
            // soundly insist on its presence at a single slot, so skip.
            _ = idx;
            return true;
        },
        .app => |app| {
            if (app.term_id == head_id) {
                for (app.args) |arg| {
                    if (!acuiCheckRequiredElements(
                        context,
                        theorem,
                        arg,
                        container,
                        head_id,
                        bindings,
                    )) return false;
                }
                return true;
            }
            // Non-combiner leaf: a single required element. Either it's
            // entirely concrete (or has only bound binders) and we can be
            // strict about membership, or it has unbound binders and we
            // treat them as wildcards while walking the container.
            return acuiContainerHasTemplateMember(
                context,
                theorem,
                container,
                template,
                head_id,
                bindings,
            );
        },
    }
}

fn acuiContainerHasTemplateMember(
    context: *const Context,
    theorem: *const TheoremContext,
    container: ExprId,
    leaf_template: TemplateExpr,
    head_id: u32,
    bindings: []const ?ExprId,
) bool {
    const node = theorem.interner.node(container);
    switch (node.*) {
        .app => |app| {
            if (app.term_id == head_id) {
                for (app.args) |arg| {
                    if (acuiContainerHasTemplateMember(
                        context,
                        theorem,
                        arg,
                        leaf_template,
                        head_id,
                        bindings,
                    )) return true;
                }
                return false;
            }
        },
        else => {},
    }
    return templateMatchesExprPlausible(
        context,
        theorem,
        leaf_template,
        container,
        bindings,
    );
}

// ===========================================================================
// Deep-unfold ACUI member check (Lever E).
//
// `acuiBoundMembersPlausible` abstains the moment a transparent-def head differs
// between a required member leaf and a container member (`templateMatchesExprPlausible`
// → `exprNeedsSemantic`). For def-dense theories (church) every leaf/member pair
// involves a def, so the check never rejects — the eqmp/ax reject-flood. This
// variant instead instantiates each FULLY-BOUND required leaf concretely and
// requires SOME container member to survive a COMPLETE (to-fixpoint) def-unfold
// comparison (`deepExprMismatch` = `unfoldedExprMismatch`). It returns true when
// some required leaf has no deep-compatible member — i.e. the candidate would be
// pruned. `deepExprMismatch` is injected to avoid an plausible↔acui
// cycle.
//
// `cache` (optional) memoizes the per-(leaf, member) verdict ACROSS candidates:
// the goal members are fixed for a search, so the same def-unfold comparisons
// recur on every candidate. The verdict is a pure function of the two exprs'
// content + the fixed env, so it is keyed by a content hash (`hashExprContent`).
// See that function for why the key is sound across the COW-cloned candidate
// interners even when a leaf carries a candidate-local variable id.
pub fn acuiBoundMembersDeepMismatch(
    context: *const Context,
    theorem: *TheoremContext,
    template: TemplateExpr,
    expr_id: ExprId,
    bindings: []const ?ExprId,
    comptime deepExprMismatch: DeepExprMismatchFn,
    cache: ?*DeepVerdictCache,
) bool {
    switch (template) {
        .binder => return false,
        .app => |app| {
            if (context.registry.acui_by_head.contains(app.term_id)) {
                return deepCheckRequiredElements(
                    context,
                    theorem,
                    template,
                    expr_id,
                    app.term_id,
                    bindings,
                    deepExprMismatch,
                    cache,
                );
            }
            // Non-ACUI head: line up positionally so child positions point at
            // the corresponding goal subtrees, recursing for any nested ACUI
            // context. A head/arity mismatch means the plain check would not
            // have lined up here either — no opinion.
            const node = theorem.interner.node(expr_id);
            switch (node.*) {
                .variable, .placeholder => return false,
                .app => |concrete| {
                    if (concrete.term_id != app.term_id) return false;
                    if (concrete.args.len != app.args.len) return false;
                    for (app.args, concrete.args) |tmpl_arg, conc_arg| {
                        if (acuiBoundMembersDeepMismatch(
                            context,
                            theorem,
                            tmpl_arg,
                            conc_arg,
                            bindings,
                            deepExprMismatch,
                            cache,
                        )) return true;
                    }
                    return false;
                },
            }
        },
    }
}

fn deepCheckRequiredElements(
    context: *const Context,
    theorem: *TheoremContext,
    template: TemplateExpr,
    container: ExprId,
    head_id: u32,
    bindings: []const ?ExprId,
    comptime deepExprMismatch: DeepExprMismatchFn,
    cache: ?*DeepVerdictCache,
) bool {
    switch (template) {
        // A multiset-level binder captures "everything else" — never a single
        // required member.
        .binder => return false,
        .app => |app| {
            if (app.term_id == head_id) {
                for (app.args) |arg| {
                    if (deepCheckRequiredElements(
                        context,
                        theorem,
                        arg,
                        container,
                        head_id,
                        bindings,
                        deepExprMismatch,
                        cache,
                    )) return true;
                }
                return false;
            }
            // A required leaf. Only judge it when FULLY BOUND — instantiate to a
            // concrete expr (null ⇒ an unbound binder remains ⇒ wildcard ⇒ no
            // opinion) and require a deep-compatible container member.
            const leaf = (OpenTerms.instantiateTemplateConcrete(
                theorem,
                template,
                bindings,
            ) catch return false) orelse return false;
            return !deepContainerHasCompatibleMember(
                context,
                theorem,
                container,
                leaf,
                head_id,
                deepExprMismatch,
                cache,
            );
        },
    }
}

fn deepContainerHasCompatibleMember(
    context: *const Context,
    theorem: *TheoremContext,
    container: ExprId,
    leaf: ExprId,
    head_id: u32,
    comptime deepExprMismatch: DeepExprMismatchFn,
    cache: ?*DeepVerdictCache,
) bool {
    const node = theorem.interner.node(container);
    switch (node.*) {
        .app => |app| {
            if (app.term_id == head_id) {
                for (app.args) |arg| {
                    if (deepContainerHasCompatibleMember(
                        context,
                        theorem,
                        arg,
                        leaf,
                        head_id,
                        deepExprMismatch,
                        cache,
                    )) return true;
                }
                return false;
            }
        },
        else => {},
    }
    // A single container member: compatible iff it does NOT definitely diverge
    // from the leaf after complete def-unfolding. Memoize the verdict across
    // candidates by a content key (see `acuiBoundMembersDeepMismatch`).
    return !deepMemberMismatch(context, theorem, leaf, container, deepExprMismatch, cache);
}

fn deepMemberMismatch(
    context: *const Context,
    theorem: *TheoremContext,
    leaf: ExprId,
    member: ExprId,
    comptime deepExprMismatch: DeepExprMismatchFn,
    cache: ?*DeepVerdictCache,
) bool {
    const c = cache orelse
        return deepExprMismatch(context, theorem, leaf, member, 0);
    // Keyed by canonical CONTENT (`types.hashCanonicalContent`), never raw
    // ExprIds, so keys are stable across COW-cloned candidate interners AND
    // `hookSolveOpen` interner-scope discards. Two distinct eigenvariable
    // dummies sharing (index, sort) hash equal, and the cached verdict is
    // still correct: `unfoldedExprMismatch` is variable-identity-agnostic
    // except for the `a == b` id-equality test, and (index, sort) fully
    // determines a dummy's compare behavior (its dep bit advances in lockstep
    // with the index). (Distinct 64-bit keys colliding is the usual hash
    // risk: a false "present" → a MISSED prune, never an unsound accept — the
    // candidate still faces `tryCandidate`.)
    var h = std.hash.Wyhash.init(0xDEE9_4E37_CAC4_E000);
    types.hashCanonicalContent(theorem, leaf, &h);
    h.update("|");
    types.hashCanonicalContent(theorem, member, &h);
    const key = h.final();
    if (c.lookup(key)) |verdict| return verdict;
    const verdict = deepExprMismatch(context, theorem, leaf, member, 0);
    c.store(key, verdict);
    return verdict;
}

// Read-only structural alignment: does `expr` match `template` under the
// current bindings? Bound binders demand exact ExprId equality; unbound
// binders match anything (we make no commitment, since we're only deciding
// whether the candidate could plausibly work).
pub fn templateMatchesExprReadOnly(
    theorem: *const TheoremContext,
    template: TemplateExpr,
    expr_id: ExprId,
    bindings: []const ?ExprId,
) bool {
    return templateMatchesExprImpl(theorem, template, expr_id, bindings, false);
}

// Like `templateMatchesExprReadOnly`, but a bound binder embedding an open
// search meta is allowed to unify-modulo-meta with the member (carry-to-leaf
// witness, e.g. `rim`'s `P ?t` against a concrete `P c`). For meta-free
// bindings the leaf check degenerates to exact equality, so this matches the
// strict matcher — the concrete corpus is unaffected. Used only by the
// read-only ACUI coverage prune (no member is pinned), so the relaxed match
// cannot poison a sibling extractor the way loosening the strict matcher would.
fn templateMatchesExprModuloMeta(
    theorem: *const TheoremContext,
    template: TemplateExpr,
    expr_id: ExprId,
    bindings: []const ?ExprId,
) bool {
    return templateMatchesExprImpl(theorem, template, expr_id, bindings, true);
}

// Shared structural walk for the two read-only plausibility matchers above.
// `meta_wildcard` (comptime) selects the bound-binder leaf semantics: exact
// `ExprId` equality (strict) vs. unify-modulo-meta (carry-to-leaf witness).
fn templateMatchesExprImpl(
    theorem: *const TheoremContext,
    template: TemplateExpr,
    expr_id: ExprId,
    bindings: []const ?ExprId,
    comptime meta_wildcard: bool,
) bool {
    switch (template) {
        .binder => |idx| {
            if (idx >= bindings.len) return true;
            if (bindings[idx]) |bound| {
                if (meta_wildcard) return exprUnifiesModuloMeta(theorem, bound, expr_id);
                return bound == expr_id;
            }
            return true;
        },
        .app => |app| {
            const node = theorem.interner.node(expr_id);
            switch (node.*) {
                .app => |concrete| {
                    if (concrete.term_id != app.term_id) return false;
                    if (concrete.args.len != app.args.len) return false;
                    for (app.args, concrete.args) |tmpl_arg, conc_arg| {
                        if (!templateMatchesExprImpl(
                            theorem,
                            tmpl_arg,
                            conc_arg,
                            bindings,
                            meta_wildcard,
                        )) return false;
                    }
                    return true;
                },
                else => return false,
            }
        },
    }
}

// Membership variant for the conclusion/hyp ACUI *plausibility* prune. Same
// structural walk as `templateMatchesExprReadOnly`, but a bound-binder leaf
// whose value differs from the member is treated as a definite mismatch ONLY
// when both sides are rigid (no transparent def / ACUI). When a def on either
// side could unfold to bridge them — e.g. `ax`'s required member `hyp(a)` with
// `a := suc x ≤ y` (`le …`) against a context member `x < y` (`lt …`), where
// `lt` unfolds to `le (suc …)` — we yield "no opinion" (plausible) and leave
// the verdict to the validator's def-aware matcher. Extraction callers keep the
// strict `templateMatchesExprReadOnly`, since over-eager def matching there
// would consume/pin the wrong member.
fn templateMatchesExprPlausible(
    context: *const Context,
    theorem: *const TheoremContext,
    template: TemplateExpr,
    expr_id: ExprId,
    bindings: []const ?ExprId,
) bool {
    switch (template) {
        .binder => |idx| {
            if (idx >= bindings.len) return true;
            if (bindings[idx]) |bound| {
                if (bound == expr_id) return true;
                // Carry-to-leaf witness: a bound value embedding an open
                // search meta (e.g. `rim`'s antecedent binder seeded to
                // `P ?t` from an open-backward `rex` premise) can still unify
                // with a concrete member (`P c`) — the meta absorbs the
                // difference, pinning the witness. Treat as plausible when the
                // rigid skeleton agrees and defer the actual unification to
                // full validation, rather than hard-pruning the ref.
                if (exprUnifiesModuloMeta(theorem, bound, expr_id)) return true;
                return exprNeedsSemantic(context, theorem, bound) or
                    exprNeedsSemantic(context, theorem, expr_id);
            }
            return true;
        },
        .app => |app| {
            const node = theorem.interner.node(expr_id);
            switch (node.*) {
                .app => |concrete| {
                    // Heads differ but a transparent def on either side could
                    // unfold to align them — no opinion rather than a hard
                    // mismatch (mirrors the binder case above).
                    if (concrete.term_id != app.term_id) {
                        return exprNeedsSemantic(context, theorem, expr_id) or
                            templateNeedsSemantic(context, .{ .app = app });
                    }
                    // Same semantic head: transparent defs are not injective,
                    // and an ACUI-headed member may match after canonicalizing.
                    // Do not judge this by positional argument equality.
                    if (termNeedsSemantic(context, app.term_id)) return true;
                    if (concrete.args.len != app.args.len) return false;
                    for (app.args, concrete.args) |tmpl_arg, conc_arg| {
                        if (!templateMatchesExprPlausible(
                            context,
                            theorem,
                            tmpl_arg,
                            conc_arg,
                            bindings,
                        )) return false;
                    }
                    return true;
                },
                .variable, .placeholder => {
                    return templateNeedsSemantic(context, .{ .app = app });
                },
            }
        },
    }
}

/// Structural unifiability of two interned expressions treating any
/// search-meta leaf (on either side) as a wildcard. Used by the ACUI
/// membership prune to keep a carry-to-leaf witness binding (e.g. `P ?t`)
/// plausible against a concrete member (`P c`) without committing the meta —
/// the verdict is deferred to full validation. For meta-free expressions this
/// is exact structural equality, so a differing rigid skeleton (head/arity/var
/// clash) still prunes.
pub fn exprUnifiesModuloMeta(
    theorem: *const TheoremContext,
    a: ExprId,
    b: ExprId,
) bool {
    if (a == b) return true;
    const na = theorem.interner.node(a).*;
    const nb = theorem.interner.node(b).*;
    if (na == .placeholder and theorem.placeholderClass(na.placeholder) == .meta)
        return true;
    if (nb == .placeholder and theorem.placeholderClass(nb.placeholder) == .meta)
        return true;
    switch (na) {
        .app => |aa| switch (nb) {
            .app => |bb| {
                if (aa.term_id != bb.term_id) return false;
                if (aa.args.len != bb.args.len) return false;
                for (aa.args, bb.args) |x, y| {
                    if (!exprUnifiesModuloMeta(theorem, x, y)) return false;
                }
                return true;
            },
            else => return false,
        },
        // Distinct non-meta leaves (variables / non-meta placeholders) already
        // failed the `a == b` identity check above, so they do not unify.
        else => return false,
    }
}

// The unit (identity) term id of the ACUI combiner headed by `head_id`, or
// null if `head_id` is not a registered combiner / has no resolvable unit.
pub fn acuiUnitIdForHead(context: *const Context, head_id: u32) ?u32 {
    const combiner = context.registry.acui_by_head.get(head_id) orelse return null;
    return context.env.term_names.get(combiner.unit_term_name);
}

// Is `expr_id` the unit element of some registered ACUI combiner (e.g. `emp`)?
// A unit is a nullary application of the combiner's declared unit term.
pub fn isAcuiUnitExpr(
    context: *const Context,
    theorem: *const TheoremContext,
    expr_id: ExprId,
) bool {
    const node = theorem.interner.node(expr_id);
    const app = switch (node.*) {
        .app => |a| a,
        else => return false,
    };
    if (app.args.len != 0) return false;
    var it = context.registry.acui_by_head.iterator();
    while (it.next()) |entry| {
        const unit_id = context.env.term_names.get(entry.value_ptr.unit_term_name) orelse continue;
        if (unit_id == app.term_id) return true;
    }
    return false;
}

// Canonicalize ACUI units away: under any registered combiner head (e.g. `join`
// / `,`), drop unit operands (`emp`) and flatten nested same-head combiners, so
// `combine(emp, X) ≡ X` structurally. Non-combiner apps are rebuilt with
// normalized children; leaves are returned unchanged. Returns the original id
// when nothing changed.
//
// Why: a generated context target carries a redundant `emp` — an `imp_intro`
// over an `emp ⊢ …` goal binds the rule's context binder to `emp`, so its
// hypothesis instantiates to `emp, p, …`. Search's strict `matchTemplate` then
// cannot equate that with a unit-free pool ref (e.g. `l3 : a=b, a∈a ⊢ …`), even
// though the validator absorbs the unit via the unit law. Normalizing the
// generation target before the recursive solve closes that gap soundly (the
// real `tryCandidate` still has final say).
pub fn normalizeAcuiUnits(
    context: *const Context,
    theorem: *TheoremContext,
    expr_id: ExprId,
) error{ OutOfMemory, TooManyTheoremExprs }!ExprId {
    var term_id: u32 = undefined;
    var arg_count: usize = 0;
    switch (theorem.interner.node(expr_id).*) {
        .app => |a| {
            term_id = a.term_id;
            arg_count = a.args.len;
        },
        else => return expr_id,
    }
    if (arg_count == 0) return expr_id;

    if (context.registry.acui_by_head.get(term_id) != null) {
        return normalizeAcuiCombiner(context, theorem, term_id, expr_id);
    }

    // Non-combiner application: normalize children, rebuild only if one changed.
    const args = try theorem.allocator.alloc(ExprId, arg_count);
    defer theorem.allocator.free(args);
    @memcpy(args, theorem.interner.node(expr_id).app.args);
    var changed = false;
    for (args) |*a| {
        const normalized = try normalizeAcuiUnits(context, theorem, a.*);
        if (normalized != a.*) changed = true;
        a.* = normalized;
    }
    if (!changed) return expr_id;
    return theorem.interner.internApp(term_id, args);
}

fn normalizeAcuiCombiner(
    context: *const Context,
    theorem: *TheoremContext,
    head_id: u32,
    expr_id: ExprId,
) error{ OutOfMemory, TooManyTheoremExprs }!ExprId {
    var raw: [max_acui_members]AcuiMember = undefined;
    var raw_n: usize = 0;
    // Bail unchanged on an oversized multiset rather than truncate it.
    if (!collectAcuiMembers(theorem, expr_id, head_id, &raw, &raw_n)) return expr_id;

    var kept: [max_acui_members]ExprId = undefined;
    var kept_n: usize = 0;
    for (raw[0..raw_n]) |member| {
        const normalized = try normalizeAcuiUnits(context, theorem, member.expr);
        if (isAcuiUnitExpr(context, theorem, normalized)) continue;
        kept[kept_n] = normalized;
        kept_n += 1;
    }

    if (kept_n == 0) {
        // Every member was a unit ⇒ the whole region is the unit element.
        const unit_term = acuiUnitIdForHead(context, head_id) orelse return expr_id;
        return theorem.interner.internApp(unit_term, &.{});
    }
    return internRightFold(theorem, head_id, kept[0..kept_n]);
}

/// Right-fold `members` back into binary `head_id` combiner applications,
/// preserving left-to-right order: `[a, b, c]` → `head(a, head(b, c))`. A
/// single member is returned as itself. The empty region is the combiner's
/// unit, whose resolution can fail — callers handle that case themselves.
pub fn internRightFold(
    theorem: *TheoremContext,
    head_id: u32,
    members: []const ExprId,
) error{ OutOfMemory, TooManyTheoremExprs }!ExprId {
    std.debug.assert(members.len > 0);
    var result = members[members.len - 1];
    var i = members.len - 1;
    while (i > 0) {
        i -= 1;
        result = try theorem.interner.internApp(head_id, &.{ members[i], result });
    }
    return result;
}

/// Canonical `ExprId` for ACUI-equality memo keying. Like `normalizeAcuiUnits`
/// (flatten association, drop units) but additionally *sorts* the members of a
/// commutative combiner and *dedups* the members of an idempotent one, so two
/// ACUI-equal expressions map to the same id and a sub-proof of one can be
/// reused for the other (the proof compiler bridges the reordering when the
/// cached application is spliced — see `generate.zig` `concrete_ok`).
///
/// Conservative: it only collapses differences the *registered subset* actually
/// licenses — reordering only when `comm_name != null`, duplicates only when
/// `idem_name != null` (and only after a sort, so duplicates are adjacent). It
/// therefore never maps two genuinely-unequal expressions to the same id; the
/// worst case is under-collision (a missed reuse), never a false one.
///
/// The result is used *only* as a hash key, never as a proof term, so its own
/// identity is irrelevant beyond equality — the replayed proof is relabeled to
/// the caller's exact target, not to this canonical form.
pub fn canonicalizeAcui(
    context: *const Context,
    theorem: *TheoremContext,
    expr_id: ExprId,
) error{ OutOfMemory, TooManyTheoremExprs }!ExprId {
    var term_id: u32 = undefined;
    var arg_count: usize = 0;
    switch (theorem.interner.node(expr_id).*) {
        .app => |a| {
            term_id = a.term_id;
            arg_count = a.args.len;
        },
        else => return expr_id,
    }
    if (arg_count == 0) return expr_id;

    if (context.registry.acui_by_head.get(term_id)) |combiner| {
        return canonicalizeAcuiCombiner(context, theorem, term_id, combiner, expr_id);
    }

    // Non-combiner application: canonicalize children, rebuild only if changed.
    const args = try theorem.allocator.alloc(ExprId, arg_count);
    defer theorem.allocator.free(args);
    @memcpy(args, theorem.interner.node(expr_id).app.args);
    var changed = false;
    for (args) |*a| {
        const canonical = try canonicalizeAcui(context, theorem, a.*);
        if (canonical != a.*) changed = true;
        a.* = canonical;
    }
    if (!changed) return expr_id;
    return theorem.interner.internApp(term_id, args);
}

fn canonicalizeAcuiCombiner(
    context: *const Context,
    theorem: *TheoremContext,
    head_id: u32,
    combiner: StructuralCombiner,
    expr_id: ExprId,
) error{ OutOfMemory, TooManyTheoremExprs }!ExprId {
    var raw: [max_acui_members]AcuiMember = undefined;
    var raw_n: usize = 0;
    if (!collectAcuiMembers(theorem, expr_id, head_id, &raw, &raw_n)) return expr_id;

    // Each canonicalization step is gated on the law the *registered subset*
    // actually declares, so this never equates two genuinely-unequal expressions
    // (worst case: a missed reuse). The minimum subset is AU — the DSL makes the
    // associativity rule and unit term mandatory while `comm`/`idem` are optional
    // — so flattening (above, A) and unit removal (here, U) are always licensed;
    // ordering and multiplicity are only collapsed under C and I respectively.

    // U (always): drop unit members. `isAcuiUnitExpr` is false for everything if
    // the unit term is unresolvable, so a malformed unit-less declaration is inert
    // here rather than wrong.
    var kept: [max_acui_members]ExprId = undefined;
    var kept_n: usize = 0;
    for (raw[0..raw_n]) |member| {
        const canonical = try canonicalizeAcui(context, theorem, member.expr);
        if (isAcuiUnitExpr(context, theorem, canonical)) continue;
        kept[kept_n] = canonical;
        kept_n += 1;
    }

    // C (only when commutative): order is immaterial, so sort to collide
    // order-variant regions. Under a non-commutative subset (AU/AUI) order is
    // significant and must be preserved — we leave the members as written.
    if (combiner.comm_name != null) {
        std.mem.sort(ExprId, kept[0..kept_n], {}, std.sort.asc(ExprId));
        // I (only when also commutative): collapse duplicates, now adjacent after
        // the sort. We deliberately do NOT dedup an idempotent-but-non-commutative
        // (AUI) combiner: collapsing only *adjacent* duplicates there would be a
        // partial, order-dependent canonicalization, so we conservatively skip it
        // (a missed reuse, never an unsound collision).
        if (combiner.idem_name != null) {
            var w: usize = 0;
            var i: usize = 0;
            while (i < kept_n) : (i += 1) {
                if (w == 0 or kept[w - 1] != kept[i]) {
                    kept[w] = kept[i];
                    w += 1;
                }
            }
            kept_n = w;
        }
    }

    if (kept_n == 0) {
        const unit_term = acuiUnitIdForHead(context, head_id) orelse return expr_id;
        return theorem.interner.internApp(unit_term, &.{});
    }
    return internRightFold(theorem, head_id, kept[0..kept_n]);
}

// Unit law: in an ACUI monoid with a unit, `combine(a, b, …) = unit` forces
// every summand to the unit (no inverses; ∅∪∅ is the only way to ∅). So when a
// combiner-headed template region is matched against the unit element, bind
// every *direct summand* binder leaf to that unit. Only spine binders are
// forced — a non-combiner member (e.g. `hyp(a)`) cannot equal the unit, so its
// internal binders are NOT pinned (the eventual contradiction is left to
// validation / the closed-region check). Sound for any A/AU/AC/ACU/ACUI subset
// that carries a unit. Mirrors the conflict handling of `partialMatchTemplate`.
pub fn bindAcuiSpineToUnit(
    template: TemplateExpr,
    head_id: u32,
    unit_expr: ExprId,
    bindings: []?ExprId,
) void {
    switch (template) {
        .binder => |idx| {
            if (idx >= bindings.len) return;
            if (bindings[idx]) |existing| {
                if (existing != unit_expr) bindings[idx] = null;
            } else {
                bindings[idx] = unit_expr;
            }
        },
        .app => |app| {
            if (app.term_id != head_id) return;
            for (app.args) |arg| {
                bindAcuiSpineToUnit(arg, head_id, unit_expr, bindings);
            }
        },
    }
}

// Necessary condition DUAL to `acuiBoundMembersPlausible`. That checks every
// required template member is present in the ref (template ⊆ ref). This checks
// the other direction where it is sound: once an ACUI region's summand spine is
// *closed* (no free summand binder remains to absorb extra elements), the ref's
// region can hold no member the template lacks (ref ⊆ template). It also
// enforces that a binder bound to the unit forces the ref position to be that
// unit. Both are necessary for ACUI equality under any A/AU/AC/ACU/ACUI subset:
// an unmatched ref member means the regions cannot be equal and there is no free
// binder left to soak it up. Returns false ⇒ a sound `.mismatch`.
//
// The key payoff: a region like `h , q` with `h` pinned to the unit is a single
// occupied slot, so a two-member ref context is impossible *regardless* of
// whether the witness `q` is itself solved yet.
pub fn acuiClosedRegionPlausible(
    context: *const Context,
    theorem: *const TheoremContext,
    template: TemplateExpr,
    expr_id: ExprId,
    bindings: []const ?ExprId,
) bool {
    switch (template) {
        .binder => |idx| {
            if (idx < bindings.len) {
                if (bindings[idx]) |bound| {
                    // A binder pinned to the unit closes its position to the
                    // empty region: the ref here must be that same unit.
                    if (isAcuiUnitExpr(context, theorem, bound)) {
                        return isAcuiUnitExpr(context, theorem, expr_id);
                    }
                }
            }
            return true;
        },
        .app => |app| {
            if (context.registry.hasStructuralCombiner(app.term_id)) {
                if (!acuiSpineClosed(template, app.term_id, bindings)) return true;
                return acuiRegionRefCompatible(
                    context,
                    theorem,
                    template,
                    expr_id,
                    app.term_id,
                    bindings,
                );
            }
            const node = theorem.interner.node(expr_id);
            switch (node.*) {
                .app => |concrete| {
                    if (concrete.term_id != app.term_id) return true;
                    if (concrete.args.len != app.args.len) return true;
                    for (app.args, concrete.args) |tmpl_arg, conc_arg| {
                        if (!acuiClosedRegionPlausible(
                            context,
                            theorem,
                            tmpl_arg,
                            conc_arg,
                            bindings,
                        )) return false;
                    }
                    return true;
                },
                else => return true,
            }
        },
    }
}

// A combiner-headed template region is "closed" when every direct summand
// binder is bound. Members (non-combiner sub-templates) count as occupied slots
// regardless of any free binders *inside* them.
fn acuiSpineClosed(
    template: TemplateExpr,
    head_id: u32,
    bindings: []const ?ExprId,
) bool {
    switch (template) {
        .binder => |idx| return idx < bindings.len and bindings[idx] != null,
        .app => |app| {
            if (app.term_id != head_id) return true;
            for (app.args) |arg| {
                if (!acuiSpineClosed(arg, head_id, bindings)) return false;
            }
            return true;
        },
    }
}

// The ref's ACUI region must be compatible with the closed template region in
// BOTH directions:
//   * cardinality — the ref's distinct (non-unit) members cannot outnumber the
//     template's member slots (a binder pinned to the unit offers 0 slots, any
//     other summand offers 1). This is what catches `h , q` (one slot, `h=emp`)
//     against a two-member ref context even while `q` is still free — counting
//     beats coverage there, since a free `q` would "match" every member.
//   * coverage — every ref member must match some template member slot.
// Bails to "no opinion" (true) on an oversized region or any opaque (bare
// variable/placeholder) ref member, which could expand to anything.
fn acuiRegionRefCompatible(
    context: *const Context,
    theorem: *const TheoremContext,
    template: TemplateExpr,
    container: ExprId,
    head_id: u32,
    bindings: []const ?ExprId,
) bool {
    var buf: [max_acui_members]AcuiMember = undefined;
    var n: usize = 0;
    if (!collectAcuiMembers(theorem, container, head_id, &buf, &n)) return true;

    var members: [max_acui_members]ExprId = undefined;
    var m: usize = 0;
    for (buf[0..n]) |item| {
        if (isAcuiUnitExpr(context, theorem, item.expr)) continue;
        switch (theorem.interner.node(item.expr).*) {
            .variable, .placeholder => return true,
            else => {},
        }
        members[m] = item.expr;
        m += 1;
    }

    var distinct: usize = 0;
    for (members[0..m], 0..) |mem, i| {
        var seen = false;
        for (members[0..i]) |prev| {
            if (prev == mem) {
                seen = true;
                break;
            }
        }
        if (!seen) distinct += 1;
    }
    if (distinct > countTemplateSlots(context, theorem, template, head_id, bindings)) {
        return false;
    }

    for (members[0..m]) |mem| {
        if (!templateRegionHasMemberMatching(
            context,
            theorem,
            template,
            mem,
            head_id,
            bindings,
        )) return false;
    }
    return true;
}

// Maximum number of distinct members the closed template region can contribute:
// a summand binder pinned to the unit gives 0, any other summand (bound binder
// or member sub-template) gives 1.
fn countTemplateSlots(
    context: *const Context,
    theorem: *const TheoremContext,
    template: TemplateExpr,
    head_id: u32,
    bindings: []const ?ExprId,
) usize {
    switch (template) {
        .binder => |idx| {
            if (idx < bindings.len) {
                if (bindings[idx]) |bound| {
                    // A summand binder bound to a multi-member ACUI region of
                    // this combiner contributes ALL of its members, not one
                    // slot. Undercounting it as 1 wrongly fails the cardinality
                    // check whenever the ref's matching members outnumber the
                    // single slot (e.g. a sequent rule's context binder `g`
                    // pinned to a two-formula antecedent against a three-member
                    // ref). A plain (non-region) value flattens to one member,
                    // and a unit to zero.
                    return boundRegionSlots(context, theorem, bound, head_id);
                }
            }
            return 1;
        },
        .app => |app| {
            if (app.term_id != head_id) return 1;
            var total: usize = 0;
            for (app.args) |arg| {
                total += countTemplateSlots(context, theorem, arg, head_id, bindings);
            }
            return total;
        },
    }
}

// Number of non-unit members a bound summand binder contributes to a closed
// ACUI region: the flattened members of `bound` under `head_id`, units dropped.
// Overflowing the member buffer yields a deliberately large count so the
// cardinality check never rejects on an undercount.
fn boundRegionSlots(
    context: *const Context,
    theorem: *const TheoremContext,
    bound: ExprId,
    head_id: u32,
) usize {
    if (isAcuiUnitExpr(context, theorem, bound)) return 0;
    var buf: [max_acui_members]AcuiMember = undefined;
    var n: usize = 0;
    if (!collectAcuiMembers(theorem, bound, head_id, &buf, &n)) {
        return max_acui_members;
    }
    var slots: usize = 0;
    for (buf[0..n]) |item| {
        if (isAcuiUnitExpr(context, theorem, item.expr)) continue;
        slots += 1;
    }
    return slots;
}

// Does the template's ACUI region contain a member that (read-only) could match
// the single ref member `ref_member`? A summand binder bound to the unit offers
// no member; one bound to a non-unit value offers exactly that value (or, when
// that value is itself a multi-member region of this combiner, any of its
// members); an unbound summand binder absorbs anything (cannot occur once the
// region is closed).
fn templateRegionHasMemberMatching(
    context: *const Context,
    theorem: *const TheoremContext,
    template: TemplateExpr,
    ref_member: ExprId,
    head_id: u32,
    bindings: []const ?ExprId,
) bool {
    switch (template) {
        .binder => |idx| {
            if (idx < bindings.len) {
                if (bindings[idx]) |bound| {
                    if (isAcuiUnitExpr(context, theorem, bound)) return false;
                    // Unify-modulo-meta so a binder bound to a carry-to-leaf
                    // witness value (e.g. `P ?t`) stays plausible against a
                    // concrete member (`P c`); degenerates to identity for
                    // meta-free bindings, matching the relaxed `.app` leaf below.
                    if (exprUnifiesModuloMeta(theorem, bound, ref_member)) return true;
                    var buf: [max_acui_members]AcuiMember = undefined;
                    var n: usize = 0;
                    if (!collectAcuiMembers(theorem, bound, head_id, &buf, &n)) {
                        return true; // overflow: no opinion (could match)
                    }
                    // A non-region value flattens to itself; the loop then just
                    // re-checks the unify above (already handled).
                    for (buf[0..n]) |item| {
                        if (exprUnifiesModuloMeta(theorem, item.expr, ref_member)) return true;
                    }
                    return false;
                }
            }
            return true;
        },
        .app => |app| {
            if (app.term_id == head_id) {
                for (app.args) |arg| {
                    if (templateRegionHasMemberMatching(
                        context,
                        theorem,
                        arg,
                        ref_member,
                        head_id,
                        bindings,
                    )) return true;
                }
                return false;
            }
            return templateMatchesExprModuloMeta(theorem, template, ref_member, bindings);
        },
    }
}
