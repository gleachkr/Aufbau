const std = @import("std");
const types = @import("../types.zig");
const ExprId = @import("../../../expr.zig").ExprId;
const TheoremContext = @import("../../../expr.zig").TheoremContext;
const TemplateExpr = @import("../../../rules.zig").TemplateExpr;
const Context = types.Context;
const semantic = @import("./semantic.zig");
const exprNeedsSemantic = semantic.exprNeedsSemantic;
const templateNeedsSemantic = semantic.templateNeedsSemantic;
const isRigidHead = semantic.isRigidHead;
const lockstep = @import("./lockstep.zig");
const bag = @import("./bag.zig");
const def_match = @import("./def_match.zig");
const OpenTerms = @import("../../inference/open_terms.zig");
const DeepVerdictCache = types.DeepVerdictCache;

const DeepExprMismatchFn = fn (*const Context, *TheoremContext, ExprId, ExprId, usize) bool;

const AcuiMember = struct {
    expr: ExprId,
    consumed: bool = false,
};

// Extract binder values from the members of an ACUI multiset (Proposal B).
//
// The structural walk in `def_match.extractHypPartialBindings` can't cross an
// ACUI head: e.g. the template context `G , ≃[A] x = t` (`join(G, hyp(eqc(A,x,t)))`)
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
// Treating the args as a multiset assumes commutativity, so callers gate this
// on it (`bag.isCommutative`). A combiner that is neither commutative
// nor idempotent is a sequence and goes through
// `def_match.extractOrderedSpineBindings` instead.
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
    var members: [bag.capacity]AcuiMember = undefined;
    var count: usize = 0;
    // Bail (extract nothing) on an unusually large context rather than risk
    // truncating the multiset, which could make a member look spuriously unique.
    if (!collectAcuiMembers(context, theorem, container, head_id, &members, &count)) return;
    const pool = members[0..count];
    const consume = consumesClaimed(context, head_id);

    // Pass 1: consume ref members claimed by the bound sibling leaves.
    if (consume) consumeBoundLeafMembers(context, theorem, head_id, template, bindings, pool);
    // Pass 2: pin each unbound leaf from a unique remaining member.
    extractUnboundLeafMembers(
        context,
        theorem,
        head_id,
        template,
        bindings,
        pool,
        consume,
        extract_fn,
    );
}

/// Whether a member one leaf claims is spent for the others. Under
/// idempotence (`g , g = g`) a leaf may repeat a member a sibling holds, so
/// claiming one rules out nothing, and a leaf whose only unclaimed match is
/// unique may still take a claimed one instead.
fn consumesClaimed(context: *const Context, head_id: u32) bool {
    const law = bag.lawOf(context, head_id) orelse return true;
    return !law.isIdempotent();
}

// The members of `container` under `head_id` (see `bag.flatten`) as an
// unconsumed pool. Returns false on overflow (caller then bails).
fn collectAcuiMembers(
    context: *const Context,
    theorem: *const TheoremContext,
    container: ExprId,
    head_id: u32,
    buf: *[bag.capacity]AcuiMember,
    count: *usize,
) bool {
    const members = bag.flatten(context, theorem, head_id, container) orelse return false;
    for (members.slice(), buf[0..members.len]) |expr, *slot| slot.* = .{ .expr = expr };
    count.* = members.len;
    return true;
}

// Mark consumed the pool members claimed by template leaves that have no
// unbound binder: a bound binder (e.g. `G`) expands to its own multiset; any
// other fully-bound leaf matches a single member directly.
fn consumeBoundLeafMembers(
    context: *const Context,
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
            const sub = bag.flatten(context, theorem, head_id, value) orelse return;
            for (sub.slice()) |member| consumePoolMemberById(pool, member);
        },
        .app => |app| {
            if (app.term_id == head_id) {
                for (app.args) |arg| {
                    consumeBoundLeafMembers(context, theorem, head_id, arg, bindings, pool);
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
    consume: bool,
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
                        consume,
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
                pool[idx].consumed = consume;
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
    if (!bag.isCommutative(context, head_id)) return null;
    var members: [bag.capacity]AcuiMember = undefined;
    var count: usize = 0;
    if (!collectAcuiMembers(context, theorem, container, head_id, &members, &count)) return null;
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
    if (consumesClaimed(context, head_id)) {
        consumeBoundLeafMembers(context, theorem, head_id, template, bindings, pool);
    }
    return findAmbiguousLeaf(allocator, theorem, head_id, template, bindings, pool);
}

/// The distinct `members` the principal leaf `leaf` could match under
/// `bindings` (read-only): the legal principal choices. An idempotent bag may
/// list one member twice, and both copies would pin the principal alike, so
/// each is offered once.
pub fn principalChoices(
    theorem: *const TheoremContext,
    leaf: TemplateExpr,
    members: []const ExprId,
    bindings: []const ?ExprId,
) bag.ExprBag {
    var choices = bag.ExprBag{};
    for (members) |member| {
        if (templateMatchesExprReadOnly(theorem, leaf, member, bindings)) {
            _ = choices.appendDistinct(member);
        }
    }
    return choices;
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
            if (!isRigidHead(context, app.term_id)) return false;
            for (app.args) |arg| {
                if (!exprFullyRigid(context, theorem, arg)) return false;
            }
            return true;
        },
    }
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
            var open = bag.ExprBag{};
            for (pool) |slot| {
                if (!slot.consumed) _ = open.append(slot.expr);
            }
            // One choice is the seed's existing single-candidate case (left to
            // `extractUnboundLeafMembers`); only more needs fan-out.
            const choices = principalChoices(theorem, template, open.slice(), bindings);
            if (choices.len < 2) return null;
            return PrincipalFanout{
                .leaf = template,
                .members = try allocator.dupe(ExprId, choices.slice()),
            };
        },
    }
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
// and "is X a member?" is ill-defined. Commutativity and idempotency are
// irrelevant to presence, and the unit is dropped on both sides (`bag.flatten`),
// so presence works equally for A, AU, AC, ACU, and full ACUI combiners.
// Multiplicity does consult the combiner: without idempotence each required
// leaf needs a member of its own (`acuiRequiredMembersPlausible`).
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
                return acuiRequiredMembersPlausible(
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
            var args = lockstep.templateArgs(context, theorem, app, expr_id) orelse return true;
            while (args.next()) |pair| {
                if (!acuiPrecheckWalk(
                    context,
                    theorem,
                    pair.template,
                    pair.expr,
                    bindings,
                )) return false;
            }
            return true;
        },
    }
}

// Inside an ACUI-rooted template subtree, each non-binder summand is a
// required member of the ref's bag and needs a ref member it could match (with
// current bindings; unbound binders act as wildcards). A binder summand (`$h` in
// `join($h, …)`) captures "everything else", so it requires nothing. Returns
// false if some required leaf cannot be placed.
//
// Under idempotence a member can serve any number of leaves, so presence is
// enough. Without it each leaf needs a member of its OWN: `weaken2`'s
// `g , x : T1 , y : T2` against `g , k : Nat` finds a `hyp` member for both
// leaves, but only one exists. That is a bipartite matching (leaf -> distinct
// compatible member), found by augmenting paths.
//
// The matching is sound only when the ref's bag is fixed: a placeholder member,
// or one headed by a def or `@rewrite` term, might expand into several members
// (or none), so any such member falls back to presence. A leaf whose head
// needs semantics might vanish (unfold to the unit), so it is never required.
// A variable member (an opaque context such as `g`) can only be
// absorbed by a binder summand, which never counts.
fn acuiRequiredMembersPlausible(
    context: *const Context,
    theorem: *const TheoremContext,
    template: TemplateExpr,
    container: ExprId,
    head_id: u32,
    bindings: []const ?ExprId,
) bool {
    const law = bag.lawOf(context, head_id) orelse return true;
    const leaf_bag = bag.flattenTemplate(context, head_id, template) orelse return true;
    const member_bag = bag.flatten(context, theorem, head_id, container) orelse return true;
    const leaves = leaf_bag.slice();
    const members = member_bag.slice();
    const distinct = !law.isIdempotent() and bagIsFixed(context, theorem, members);

    // owner[m] = leaf currently matched to member m.
    var owner: [bag.capacity]?usize = @splat(null);
    for (leaves, 0..) |leaf, leaf_idx| {
        if (leaf == .binder) continue;
        // A def or `@rewrite` leaf may unfold to the unit, needing no member.
        if (!isRigidHead(context, leaf.app.term_id)) continue;
        if (distinct) {
            var visited: [bag.capacity]bool = @splat(false);
            if (!augmentLeaf(context, theorem, leaves, members, bindings, leaf_idx, &owner, &visited))
                return false;
        } else {
            for (members) |member| {
                if (!def_match.templateDefiniteMismatch(context, theorem, leaf, member, bindings)) break;
            } else return false;
        }
    }
    return true;
}

// Whether no member of the bag could stand for a different number of members
// after conversion.
fn bagIsFixed(
    context: *const Context,
    theorem: *const TheoremContext,
    members: []const ExprId,
) bool {
    for (members) |member| {
        if (!memberIsFixed(context, theorem, member)) return false;
    }
    return true;
}

/// Whether `member` stays exactly one member after conversion: not a meta, and
/// not headed by a def or `@rewrite` term that may unfold to several or none.
pub fn memberIsFixed(
    context: *const Context,
    theorem: *const TheoremContext,
    member: ExprId,
) bool {
    return switch (theorem.interner.node(member).*) {
        .placeholder => false,
        .variable => true,
        .app => |app| isRigidHead(context, app.term_id),
    };
}

/// Whether `member` could equal some member of `list`. A member that is not
/// fixed (`memberIsFixed`) may convert to the unit (a `wk_nil`-style def of the
/// empty context), so it needs no partner.
pub fn memberPossiblyIn(
    context: *const Context,
    theorem: *const TheoremContext,
    member: ExprId,
    list: []const ExprId,
) bool {
    if (!memberIsFixed(context, theorem, member)) return true;
    for (list) |candidate| {
        if (!def_match.rigidExprMismatch(context, theorem, member, candidate)) return true;
    }
    return false;
}

fn augmentLeaf(
    context: *const Context,
    theorem: *const TheoremContext,
    leaves: []const TemplateExpr,
    members: []const ExprId,
    bindings: []const ?ExprId,
    leaf_idx: usize,
    owner: *[bag.capacity]?usize,
    visited: *[bag.capacity]bool,
) bool {
    for (members, 0..) |member, m| {
        if (visited[m]) continue;
        if (def_match.templateDefiniteMismatch(context, theorem, leaves[leaf_idx], member, bindings))
            continue;
        visited[m] = true;
        if (owner[m]) |other| {
            if (!augmentLeaf(context, theorem, leaves, members, bindings, other, owner, visited))
                continue;
        }
        owner[m] = leaf_idx;
        return true;
    }
    return false;
}

// ===========================================================================
// Deep-unfold ACUI member check (Lever E).
//
// `acuiBoundMembersPlausible` abstains the moment a transparent-def head differs
// between a required member leaf and a container member (`templateDefiniteMismatch`
// finds no rigid clash through a def). For def-dense theories (church) every leaf/member pair
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
            var args = lockstep.templateArgs(context, theorem, app, expr_id) orelse return false;
            while (args.next()) |pair| {
                if (acuiBoundMembersDeepMismatch(
                    context,
                    theorem,
                    pair.template,
                    pair.expr,
                    bindings,
                    deepExprMismatch,
                    cache,
                )) return true;
            }
            return false;
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
    const leaves = bag.flattenTemplate(context, head_id, template) orelse return false;
    const members = bag.flatten(context, theorem, head_id, container) orelse return false;
    for (leaves.slice()) |leaf_template| {
        // A bag-level binder captures "everything else" — never a single
        // required member.
        if (leaf_template == .binder) continue;
        // A required leaf. Only judge it when FULLY BOUND — instantiate to a
        // concrete expr (null ⇒ an unbound binder remains ⇒ wildcard ⇒ no
        // opinion) and require a deep-compatible container member. A member is
        // compatible iff it does NOT definitely diverge from the leaf after
        // complete def-unfolding. The unit is implicitly always a member: a
        // leaf that unfolds to it needs no member of its own.
        const leaf = (OpenTerms.instantiateTemplateConcrete(
            theorem,
            leaf_template,
            bindings,
        ) catch continue) orelse continue;
        for (members.slice()) |member| {
            if (!deepMemberMismatch(context, theorem, leaf, member, deepExprMismatch, cache)) break;
        } else {
            const unit = bag.unitOf(context, head_id) orelse continue;
            const unit_expr = theorem.interner.internApp(unit, &.{}) catch continue;
            if (deepMemberMismatch(context, theorem, leaf, unit_expr, deepExprMismatch, cache))
                return true;
        }
    }
    return false;
}

// Memoizes the verdict across candidates by a content key (see
// `acuiBoundMembersDeepMismatch`).
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
    return rebuildAcui(context, theorem, expr_id, .unit_free);
}

/// Canonical `ExprId` for ACUI-equality memo keying. Like `normalizeAcuiUnits`
/// (flatten association, drop units) but additionally *sorts* the members of a
/// commutative combiner and *dedups* the members of an idempotent one, so two
/// ACUI-equal expressions map to the same id and a sub-proof of one can be
/// reused for the other (the proof compiler bridges the reordering when the
/// cached application is spliced — see `generate.zig` `concrete_ok`).
///
/// Conservative: it only collapses differences the *registered subset* actually
/// licenses — reordering only under C, duplicates only under C and I (after the
/// sort, so duplicates are adjacent). It therefore never maps two
/// genuinely-unequal expressions to the same id; the worst case is
/// under-collision (a missed reuse), never a false one.
///
/// The result is used *only* as a hash key, never as a proof term, so its own
/// identity is irrelevant beyond equality — the replayed proof is relabeled to
/// the caller's exact target, not to this canonical form.
pub fn canonicalizeAcui(
    context: *const Context,
    theorem: *TheoremContext,
    expr_id: ExprId,
) error{ OutOfMemory, TooManyTheoremExprs }!ExprId {
    return rebuildAcui(context, theorem, expr_id, .memo_key);
}

const AcuiForm = enum {
    /// Association flattened and this combiner's units dropped.
    unit_free,
    /// `unit_free`, with members sorted under C and deduped under C and I.
    memo_key,
};

fn rebuildAcui(
    context: *const Context,
    theorem: *TheoremContext,
    expr_id: ExprId,
    comptime form: AcuiForm,
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

    if (bag.combinerOf(context, term_id)) |combiner| {
        return rebuildAcuiCombiner(context, theorem, combiner, expr_id, form);
    }

    // Non-combiner application: rebuild children, rebuild only if one changed.
    const args = try theorem.allocator.alloc(ExprId, arg_count);
    defer theorem.allocator.free(args);
    @memcpy(args, theorem.interner.node(expr_id).app.args);
    var changed = false;
    for (args) |*a| {
        const rebuilt = try rebuildAcui(context, theorem, a.*, form);
        if (rebuilt != a.*) changed = true;
        a.* = rebuilt;
    }
    if (!changed) return expr_id;
    return theorem.interner.internApp(term_id, args);
}

fn rebuildAcuiCombiner(
    context: *const Context,
    theorem: *TheoremContext,
    combiner: bag.Combiner,
    expr_id: ExprId,
    comptime form: AcuiForm,
) error{ OutOfMemory, TooManyTheoremExprs }!ExprId {
    // Bail unchanged on an oversized bag rather than truncate it.
    const raw = combiner.flatten(theorem, expr_id) orelse return expr_id;

    // Each step is gated on the law the *registered subset* actually declares,
    // so this never equates two genuinely-unequal expressions (worst case: a
    // missed reuse). The minimum subset is AU — the DSL makes the associativity
    // rule and unit term mandatory while `comm`/`idem` are optional — so
    // flattening (A) and unit removal (U) are always licensed; ordering and
    // multiplicity are only collapsed under C and I respectively.

    // U (always): drop this combiner's unit members, including a member that
    // rebuilds to it (a member that is another combiner's unit stays). Nothing
    // is a unit if the unit term is unresolvable, so a malformed unit-less
    // declaration is inert here rather than wrong.
    var kept: [bag.capacity]ExprId = undefined;
    var kept_n: usize = 0;
    for (raw.slice()) |member| {
        const rebuilt = try rebuildAcui(context, theorem, member, form);
        if (combiner.isUnit(theorem, rebuilt)) continue;
        kept[kept_n] = rebuilt;
        kept_n += 1;
    }

    // C (only when commutative): order is immaterial, so sort to collide
    // order-variant regions. Under a non-commutative subset (AU/AUI) order is
    // significant and must be preserved — we leave the members as written.
    if (form == .memo_key and combiner.law.isCommutative()) {
        std.mem.sort(ExprId, kept[0..kept_n], {}, std.sort.asc(ExprId));
        // I (only when also commutative): collapse duplicates, now adjacent after
        // the sort. We deliberately do NOT dedup an idempotent-but-non-commutative
        // (AUI) combiner: collapsing only *adjacent* duplicates there would be a
        // partial, order-dependent canonicalization, so we conservatively skip it
        // (a missed reuse, never an unsound collision).
        if (combiner.law.isIdempotent()) {
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

    // Every member was a unit ⇒ the whole region is the unit element.
    return (try combiner.build(theorem, kept[0..kept_n])) orelse expr_id;
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
                    // A binder pinned to a combiner's unit closes its
                    // position to the empty region: the ref here must hold no
                    // members of that combiner.
                    if (unitRefPlausible(context, theorem, bound, expr_id)) |plausible| {
                        return plausible;
                    }
                    // A bound binder is a closed one-summand region: when
                    // either side is a combiner region, the ref must hold
                    // exactly the bound value's members.
                    const head_id = combinerHeadOf(context, theorem, bound) orelse
                        combinerHeadOf(context, theorem, expr_id) orelse
                        return true;
                    return boundRegionRefEqualPlausible(
                        context,
                        theorem,
                        bound,
                        expr_id,
                        head_id,
                    );
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
            var args = lockstep.templateArgs(context, theorem, app, expr_id) orelse return true;
            while (args.next()) |pair| {
                if (!acuiClosedRegionPlausible(
                    context,
                    theorem,
                    pair.template,
                    pair.expr,
                    bindings,
                )) return false;
            }
            return true;
        },
    }
}

// When `bound` is the unit of some combiner: whether `ref` can equal it,
// i.e. flattens to no members under that combiner (`emp , emp` does). A meta
// member may stand for nothing, so it abstains. Null when `bound` is no unit.
fn unitRefPlausible(
    context: *const Context,
    theorem: *const TheoremContext,
    bound: ExprId,
    ref: ExprId,
) ?bool {
    var is_unit = false;
    var it = context.registry.acui_by_head.keyIterator();
    while (it.next()) |head_id| {
        if (!bag.isUnitOf(context, theorem, head_id.*, bound)) continue;
        is_unit = true;
        const members = bag.flatten(context, theorem, head_id.*, ref) orelse return true;
        for (members.slice()) |member| {
            if (theorem.interner.node(member).* != .placeholder) break;
        } else return true;
    }
    return if (is_unit) false else null;
}

fn combinerHeadOf(
    context: *const Context,
    theorem: *const TheoremContext,
    expr_id: ExprId,
) ?u32 {
    return switch (theorem.interner.node(expr_id).*) {
        .app => |app| if (context.registry.hasStructuralCombiner(app.term_id))
            app.term_id
        else
            null,
        else => null,
    };
}

// ACUI equality of a bound binder's value with the ref at its position, as
// member-set coverage in both directions. Bails to "no opinion" (true) on
// overflow, on a bare variable/placeholder ref member (it could expand to
// anything), and on any member conversion could change (a `@rewrite` head or
// a transparent def), where syntactic member identity is not decisive.
fn boundRegionRefEqualPlausible(
    context: *const Context,
    theorem: *const TheoremContext,
    bound: ExprId,
    container: ExprId,
    head_id: u32,
) bool {
    const bound_members = bag.flatten(context, theorem, head_id, bound) orelse return true;
    const ref_members = bag.flatten(context, theorem, head_id, container) orelse return true;
    for (ref_members.slice()) |item| {
        switch (theorem.interner.node(item).*) {
            .variable, .placeholder => return true,
            else => {},
        }
        if (exprNeedsSemantic(context, theorem, item)) return true;
    }
    for (bound_members.slice()) |item| {
        if (exprNeedsSemantic(context, theorem, item)) return true;
    }
    return regionCovers(theorem, bound_members.slice(), ref_members.slice()) and
        regionCovers(theorem, ref_members.slice(), bound_members.slice());
}

// Every member of `wants` matches (modulo metas) some member of `haves`. Both
// come from `bag.flatten`, so neither holds the unit. A bare meta may stand for
// no members at all, so it needs none.
fn regionCovers(
    theorem: *const TheoremContext,
    wants: []const ExprId,
    haves: []const ExprId,
) bool {
    outer: for (wants) |want| {
        if (theorem.interner.node(want).* == .placeholder) continue;
        for (haves) |have| {
            if (exprUnifiesModuloMeta(theorem, want, have)) continue :outer;
        }
        return false;
    }
    return true;
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
    const flat = bag.flatten(context, theorem, head_id, container) orelse return true;
    var members = bag.ExprBag{};
    for (flat.slice()) |item| {
        switch (theorem.interner.node(item).*) {
            .variable, .placeholder => return true,
            else => {},
        }
        _ = members.appendDistinct(item);
    }
    if (members.len > countTemplateSlots(context, theorem, template, head_id, bindings)) {
        return false;
    }

    for (members.slice()) |mem| {
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
    const members = bag.flatten(context, theorem, head_id, bound) orelse return bag.capacity;
    return members.len;
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
                    if (bag.isUnitOf(context, theorem, head_id, bound)) return false;
                    // Unify-modulo-meta so a binder bound to a carry-to-leaf
                    // witness value (e.g. `P ?t`) stays plausible against a
                    // concrete member (`P c`); degenerates to identity for
                    // meta-free bindings, matching the relaxed `.app` leaf below.
                    if (exprUnifiesModuloMeta(theorem, bound, ref_member)) return true;
                    // Overflow: no opinion (could match).
                    const members = bag.flatten(context, theorem, head_id, bound) orelse
                        return true;
                    // A non-region value flattens to itself; the loop then just
                    // re-checks the unify above (already handled).
                    for (members.slice()) |item| {
                        if (exprUnifiesModuloMeta(theorem, item, ref_member)) return true;
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
