//! Necessary-condition plausibility prunes for backward search. Two related
//! concerns: (1) split-member reasoning — collect the ACUI members a
//! multiplicative context split would require and check they could be present;
//! (2) the final conclusion prune — reject a completed assembly whose
//! conclusion provably cannot ACUI-match the goal (via def-unfold / member-list
//! comparison) before it reaches `tryCandidate`. Split out of `backtrack.zig`;
//! these are necessary-condition filters the backtracker and validator call —
//! they never commit search bindings, though the conclusion prune may intern
//! scratch nodes while unfolding defs to test the goal.

const types = @import("../types.zig");
const prune = @import("./prune.zig");
const acui = @import("./acui.zig");
const match = @import("./match.zig");
const split = @import("./split.zig");
const OpenTerms = @import("../../inference/open_terms.zig");
const ExprId = @import("../../../expr.zig").ExprId;
const TheoremContext = @import("../../../expr.zig").TheoremContext;
const TemplateExpr = @import("../../../rules.zig").TemplateExpr;
const RuleDecl = @import("../../../env.zig").RuleDecl;
const ViewDecl = @import("../../views.zig").ViewDecl;
const Context = types.Context;
const Goal = types.Goal;
const ApplyCandidate = types.ApplyCandidate;
const SearchCounters = types.SearchCounters;
const acuiBoundMembersPlausible = prune.acuiBoundMembersPlausible;
const acuiUnitIdForHead = prune.acuiUnitIdForHead;
const defBodyForUnfold = prune.defBodyForUnfold;
const templateDefiniteMismatch = prune.templateDefiniteMismatch;
const unfoldDefBody = prune.unfoldDefBody;

const max_split_guard_members: usize = 64;

pub const SplitMemberList = struct {
    items: [max_split_guard_members]ExprId = undefined,
    len: usize = 0,

    fn appendDistinct(self: *SplitMemberList, expr: ExprId) bool {
        for (self.items[0..self.len]) |existing| {
            if (existing == expr) return true;
        }
        if (self.len >= self.items.len) return false;
        self.items[self.len] = expr;
        self.len += 1;
        return true;
    }
};

pub fn splitSiteBindingsPlausible(
    context: *const Context,
    theorem: *const TheoremContext,
    site: split.SplitSite,
    bindings: []const ?ExprId,
) bool {
    const goal_members = collectSplitMembers(
        context,
        theorem,
        site.container,
        site.head_id,
    ) orelse return true;

    var bound_members = SplitMemberList{};
    var all_bound = true;
    var any_bound = false;
    for (site.spine[0..site.spine_len]) |binder_idx| {
        if (binder_idx >= bindings.len or bindings[binder_idx] == null) {
            all_bound = false;
            continue;
        }
        any_bound = true;
        const value_members = collectSplitMembers(
            context,
            theorem,
            bindings[binder_idx].?,
            site.head_id,
        ) orelse return true;
        for (value_members.items[0..value_members.len]) |member| {
            if (!bound_members.appendDistinct(member)) return true;
        }
    }
    // Structured principal summands (e.g. rim's `a→b` alongside the open rest `d`)
    // cover their goal member too — without counting them, a goal member claimed
    // by a fixed principal looks uncovered and the otherwise-valid split (`d` to
    // the leftover, here `emp`) is wrongly rejected.
    for (site.fixed[0..site.fixed_len]) |ftmpl| {
        if (!split.templateFullyBound(ftmpl, bindings)) {
            all_bound = false;
            continue;
        }
        any_bound = true;
        for (goal_members.items[0..goal_members.len]) |gm| {
            if (acui.templateMatchesExprReadOnly(theorem, ftmpl, gm, bindings)) {
                if (!bound_members.appendDistinct(gm)) return true;
            }
        }
    }
    if (!any_bound) return true;
    if (!all_bound) return true;

    for (bound_members.items[0..bound_members.len]) |member| {
        if (!memberPossiblyInList(context, theorem, member, goal_members)) {
            return false;
        }
    }
    for (goal_members.items[0..goal_members.len]) |member| {
        if (!memberPossiblyInList(context, theorem, member, bound_members)) {
            return false;
        }
    }
    return true;
}

pub fn collectSplitMembers(
    context: *const Context,
    theorem: *const TheoremContext,
    expr: ExprId,
    head_id: u32,
) ?SplitMemberList {
    var out = SplitMemberList{};
    if (!collectSplitMembersInto(context, theorem, expr, head_id, &out)) {
        return null;
    }
    return out;
}

fn collectSplitMembersInto(
    context: *const Context,
    theorem: *const TheoremContext,
    expr: ExprId,
    head_id: u32,
    out: *SplitMemberList,
) bool {
    const node = theorem.interner.node(expr);
    switch (node.*) {
        .placeholder => return false,
        .variable => return out.appendDistinct(expr),
        .app => |app| {
            if (app.term_id == head_id) {
                for (app.args) |arg| {
                    if (!collectSplitMembersInto(
                        context,
                        theorem,
                        arg,
                        head_id,
                        out,
                    )) return false;
                }
                return true;
            }
            if (isAcuiUnitForHead(context, theorem, expr, head_id)) return true;
            return out.appendDistinct(expr);
        },
    }
}

fn isAcuiUnitForHead(
    context: *const Context,
    theorem: *const TheoremContext,
    expr: ExprId,
    head_id: u32,
) bool {
    const unit_id = acuiUnitIdForHead(context, head_id) orelse return false;
    const node = theorem.interner.node(expr);
    const app = switch (node.*) {
        .app => |a| a,
        else => return false,
    };
    return app.term_id == unit_id and app.args.len == 0;
}

fn memberPossiblyInList(
    context: *const Context,
    theorem: *const TheoremContext,
    member: ExprId,
    list: SplitMemberList,
) bool {
    for (list.items[0..list.len]) |candidate| {
        if (!prune.rigidExprMismatch(
            context,
            theorem,
            member,
            candidate,
        )) return true;
    }
    return false;
}

pub fn finalConclusionPlausible(
    context: *const Context,
    candidate: *ApplyCandidate,
    goal: Goal,
    bindings: []const ?ExprId,
    counters: ?*SearchCounters,
) bool {
    const goal_expr = switch (goal) {
        .concrete => |expr| expr,
        .implicit_whole_conclusion => |maybe_expr| maybe_expr orelse return true,
        .holey => return true,
    };
    // View rules match their VIEW conclusion, not `rule.concl`, so refuting
    // against the raw conclusion would falsely reject (e.g. `ax_inst`'s raw
    // `A.x p -> sb t x p` vs a line matching the view `A.x p -> q`). Run the base
    // (trap-free) refuter against the view conclusion instead, remapping bindings
    // into view-binder space via `binder_map`. `view.concl` is an
    // over-approximation (phantom / unbound view binders are unconstrained), so
    // this stays a sound one-sided necessary-condition filter. Deliberately does
    // NOT apply the Lever B/E strengthenings below: those call `pinRigidBinders`,
    // which has the non-injective-def const-trap edge, whereas the base refuter is
    // trap-free.
    if (context.views.get(candidate.rule_id)) |view| {
        return viewConclusionPlausible(
            context,
            &candidate.theorem,
            view,
            goal_expr,
            bindings,
        );
    }
    const rule = &context.env.rules.items[candidate.rule_id];
    if (!conclusionTemplatePlausible(
        context,
        &candidate.theorem,
        rule.concl,
        goal_expr,
        bindings,
    )) return false;
    // Lever B: strengthen the necessary check by re-pinning conclusion binders
    // the goal forces at rigid (non-ACUI) positions, then re-running it. A binder
    // pinned at a rigid succedent (e.g. `ax`'s `P` in `… ⊩ P`) may also appear as
    // an ACUI context member (`hyp(P)`); with `P` re-pinned to the goal's wff the
    // member check can require `hyp(W)`'s presence in the goal context and reject
    // `W ∉ Γ` before the expensive `tryCandidate`. Sound: the re-pins are
    // goal-forced for any provable candidate, so this never rejects a winnable
    // one.
    //
    // The prune fires under `repin_prune_enabled` (behavior); `would_prune`/
    // `prunes` are diagnostics gated by `collect`. `repinConclusionPlausible`
    // itself skips the expensive re-check when re-pinning adds nothing, so it is
    // cheap for candidates the strengthening can't affect.
    if (counters) |c| {
        if ((c.repin_prune_enabled or c.collect) and !repinConclusionPlausible(
            context,
            &candidate.theorem,
            rule.concl,
            goal_expr,
            bindings,
        )) {
            if (c.collect) c.repin_would_prune += 1;
            if (c.repin_prune_enabled) {
                if (c.collect) c.repin_prunes += 1;
                return false;
            }
        }
    }
    // Lever E: does a COMPLETE def-unfold ACUI member check reject this
    // otherwise-plausible candidate? Cracks the church `ax`/membership
    // reject-flood the one-layer member check cannot. `would_prune`/`prunes`
    // are diagnostics gated by `collect`; the reject fires under
    // `deep_member_prune_enabled`.
    if (counters) |c| {
        if (c.collect) c.deep_member_calls += 1;
        if ((c.deep_member_prune_enabled or c.collect) and deepMemberWouldPrune(
            context,
            &candidate.theorem,
            rule.concl,
            goal_expr,
            bindings,
            c.deep_verdict_cache,
        )) {
            if (c.collect) c.deep_member_would_prune += 1;
            if (c.deep_member_prune_enabled) {
                if (c.collect) c.deep_member_prunes += 1;
                return false;
            }
        }
    }
    return true;
}

/// Largest view handled inline; views with more binders abstain (return true =
/// no prune, which is sound for a one-sided filter).
const max_view_binders: usize = 32;

/// View-aware conclusion refuter: run the base `conclusionTemplatePlausible`
/// against a view rule's `view.concl` (the true matching template) with `bindings`
/// (rule-arg indexed) remapped into view-binder space via `binder_map`. Phantom
/// view binders (`binder_map[vi] == null`) and unbound / out-of-range mapped
/// binders become `null` ("matches anything") — the over-approximation that keeps
/// this a sound necessary condition. Only the trap-free base refuter is used (no
/// `pinRigidBinders` strengthening).
fn viewConclusionPlausible(
    context: *const Context,
    theorem: *TheoremContext,
    view: ViewDecl,
    goal_expr: ExprId,
    bindings: []const ?ExprId,
) bool {
    if (view.num_binders > max_view_binders) return true;
    var buf: [max_view_binders]?ExprId = undefined;
    const view_bindings = buf[0..view.num_binders];
    match.seedViewBindingsFromRule(view, bindings, view_bindings);
    return conclusionTemplatePlausible(
        context,
        theorem,
        view.concl,
        goal_expr,
        view_bindings,
    );
}

/// Re-pin goal-forced conclusion binders, then ask whether a COMPLETE
/// def-unfold ACUI member check would reject the candidate.
/// `acui.acuiBoundMembersDeepMismatch` is given the deep expr-vs-expr
/// refuter `unfoldedExprMismatch` (passed in to break the import cycle), which
/// unfolds both sides to a fixpoint before comparing.
///
/// The re-pin is REQUIRED: most doomed church `ax` candidates leave the
/// required-member binder (the succedent `P` in `Γ ⊢ P`, mirrored as `hyp(P)`
/// in the context) unbound at this stage, so without it `instantiateTemplateConcrete`
/// returns null and the deep check abstains (church flood uncracked). To avoid
/// amplifying `pinRigidBinders`' const-trap (the deep refuter actively seeks
/// divergence, unlike Lever B's def-abstaining check), this re-pin runs with
/// `descend_defs = false`: it pins only through injective rigid heads, never
/// baking a non-injective-def mis-pin into the concrete leaf.
fn deepMemberWouldPrune(
    context: *const Context,
    theorem: *TheoremContext,
    concl: TemplateExpr,
    goal_expr: ExprId,
    bindings: []const ?ExprId,
    cache: ?*types.DeepVerdictCache,
) bool {
    const enriched = context.allocator.dupe(?ExprId, bindings) catch return false;
    defer context.allocator.free(enriched);
    _ = pinRigidBinders(context, theorem, concl, goal_expr, enriched, false);
    return acui.acuiBoundMembersDeepMismatch(
        context,
        theorem,
        concl,
        goal_expr,
        enriched,
        unfoldedExprMismatch,
        cache,
    );
}

/// Copy `bindings`, re-pin conclusion binders the goal forces at rigid
/// (non-ACUI) positions, and re-run the plausibility check with those extra
/// pins. Returns false only when the enriched check finds a definite mismatch.
fn repinConclusionPlausible(
    context: *const Context,
    theorem: *TheoremContext,
    concl: TemplateExpr,
    goal_expr: ExprId,
    bindings: []const ?ExprId,
) bool {
    const enriched = context.allocator.dupe(?ExprId, bindings) catch return true;
    defer context.allocator.free(enriched);
    // If re-pinning adds no new binding, the enriched check is identical to the
    // plain one (already run by the caller) — skip the second full check.
    if (!pinRigidBinders(context, theorem, concl, goal_expr, enriched, true)) return true;
    return conclusionTemplatePlausible(context, theorem, concl, goal_expr, enriched);
}

/// Fill unbound binders from the goal subterms at rigid, head/arity-aligned
/// template positions. ACUI-combiner subtrees are skipped (members aren't
/// positionally ordered — the member check handles them); a head/arity mismatch
/// stops the descent (a def could bridge it, so forming no opinion is the
/// conservative choice). Only fills `null` slots, so it never overwrites a seed.
///
/// Mirrors the established seed descent (`seed.partialMatchTemplate`), and
/// is corpus-validated sound (breadth byte-identical, depth TOTAL=325) — the
/// `top1`/depth oracle would catch any false prune from a mis-pin. ⚠ Known
/// latent edge: descending a *non-injective* transparent def head (the const
/// trap, where `f(X) == f(t)` with `X ≠ t`) can pin `X := t` wrongly, and if `X`
/// also occurs at another rigid position the strengthened check could falsely
/// reject. Not exercised by the current corpus; restricting descent to
/// `termNeedsSemantic`-rigid heads fixes it soundly but also drops the
/// def-headed descents that carry the zermelo_hilbert benefit, so the precise
/// fix needs per-arg injectivity analysis (tracked follow-up). The member check
/// downstream (`templateDefiniteMismatch`) is def-aware but does NOT backstop a
/// concrete mis-pin, so this is a real (if narrow) risk, kept deliberately.
fn pinRigidBinders(
    context: *const Context,
    theorem: *const TheoremContext,
    template: TemplateExpr,
    expr_id: ExprId,
    bindings: []?ExprId,
    comptime descend_defs: bool,
) bool {
    switch (template) {
        .binder => |idx| {
            if (idx < bindings.len and bindings[idx] == null) {
                bindings[idx] = expr_id;
                return true;
            }
            return false;
        },
        .app => |app| {
            if (context.registry.hasStructuralCombiner(app.term_id)) return false;
            // The const-trap (`f(X) == f(t)` with `X ≠ t` for a non-injective
            // transparent def) only arises when descending INTO a def head's
            // args. Callers that feed the pinned values to a divergence-seeking
            // deep refuter (Lever E) pass `descend_defs = false` to stay on
            // injective rigid heads and avoid baking a mis-pin into a concrete
            // leaf. Lever B's one-layer/def-abstaining check is robust to it, so
            // it keeps `true` (carrying the zermelo_hilbert def-descent benefit).
            if (!descend_defs and isTransparentDefHead(context, app.term_id)) {
                return false;
            }
            const node = theorem.interner.node(expr_id);
            switch (node.*) {
                .app => |concrete| {
                    if (concrete.term_id != app.term_id) return false;
                    if (concrete.args.len != app.args.len) return false;
                    var added = false;
                    for (app.args, concrete.args) |targ, earg| {
                        if (pinRigidBinders(
                            context,
                            theorem,
                            targ,
                            earg,
                            bindings,
                            descend_defs,
                        )) {
                            added = true;
                        }
                    }
                    return added;
                },
                else => return false,
            }
        },
    }
}

fn isTransparentDefHead(context: *const Context, term_id: u32) bool {
    if (!context.env.hasAvailableTerm(term_id)) return false;
    const term = context.env.terms.items[term_id];
    return term.available and term.is_def;
}

fn conclusionTemplatePlausible(
    context: *const Context,
    theorem: *TheoremContext,
    concl: TemplateExpr,
    goal_expr: ExprId,
    bindings: []const ?ExprId,
) bool {
    if (templateDefiniteMismatch(
        context,
        theorem,
        concl,
        goal_expr,
        bindings,
    )) return false;
    if (!acuiBoundMembersPlausible(
        context,
        theorem,
        concl,
        goal_expr,
        bindings,
    )) return false;
    if (closedAcuiTemplateMismatch(
        context,
        theorem,
        concl,
        goal_expr,
        bindings,
    )) return false;
    return !foldedGoalBodyMismatch(
        context,
        theorem,
        concl,
        goal_expr,
        bindings,
        0,
    );
}

fn closedAcuiTemplateMismatch(
    context: *const Context,
    theorem: *TheoremContext,
    template: TemplateExpr,
    goal_expr: ExprId,
    bindings: []const ?ExprId,
) bool {
    switch (template) {
        .binder => return false,
        .app => |app| {
            if (context.registry.acui_by_head.contains(app.term_id)) {
                const concrete = (OpenTerms.instantiateTemplateConcrete(
                    theorem,
                    template,
                    bindings,
                ) catch return false) orelse
                    // The region could not be concretized — a binder is unbound.
                    // The fully-bound member-list compare below can't run, but the
                    // unbound-repeated-binder case (e.g. `ax`'s `a` in `⊢ a,¬a,d`,
                    // present in two ACUI members with no rigid anchor for Lever B)
                    // is still refutable by enumerating that binder over the goal
                    // members.
                    return repeatedBinderMemberMismatch(
                        context,
                        theorem,
                        app,
                        goal_expr,
                        bindings,
                    );
                return acuiMemberListsMismatch(
                    context,
                    theorem,
                    app.term_id,
                    concrete,
                    goal_expr,
                );
            }
            const node = theorem.interner.node(goal_expr);
            const goal_app = switch (node.*) {
                .app => |concrete| concrete,
                else => return false,
            };
            if (goal_app.term_id != app.term_id) return false;
            if (goal_app.args.len != app.args.len) return false;
            for (app.args, goal_app.args) |arg, goal_arg| {
                if (closedAcuiTemplateMismatch(
                    context,
                    theorem,
                    arg,
                    goal_arg,
                    bindings,
                )) return true;
            }
            return false;
        },
    }
}

fn acuiMemberListsMismatch(
    context: *const Context,
    theorem: *TheoremContext,
    head_id: u32,
    candidate_expr: ExprId,
    goal_expr: ExprId,
) bool {
    const candidate_members = collectSplitMembers(
        context,
        theorem,
        candidate_expr,
        head_id,
    ) orelse return false;
    const goal_members = collectSplitMembers(
        context,
        theorem,
        goal_expr,
        head_id,
    ) orelse return false;
    for (candidate_members.items[0..candidate_members.len]) |member| {
        if (!memberPossiblyInList(context, theorem, member, goal_members)) {
            return true;
        }
    }
    for (goal_members.items[0..goal_members.len]) |member| {
        if (!memberPossiblyInList(context, theorem, member, candidate_members)) {
            return true;
        }
    }
    return false;
}

const max_repeated_binder_binders = 128;

/// Unbound-repeated-binder branch of the ACUI member-list check, reached from
/// `closedAcuiTemplateMismatch` when an ACUI conclusion region cannot be
/// concretized because a binder is unbound. If some binder appears in ≥2 members
/// of the region and no value drawn from the goal's members makes *every*
/// occurrence a present goal member, the candidate can never ACUI-match the goal
/// — a definite mismatch. This is the case the fully-bound compare above and
/// Lever B's rigid re-pin both miss: `ax`'s `a` in `⊢ a, (¬ a), d` sits in two
/// ACUI members (`hyp a`, `hyp (¬ a)`) with no rigid position, so nothing binds
/// it before validation and every non-complementary member pair burns a full
/// `tryCandidate`. Necessary-condition only: any *other* unbound binder (e.g. the
/// rest `d`) acts as a per-member wildcard via `matchTemplate` and absorbs, so a
/// consistent assignment is never wrongly reported absent — it never rejects a
/// winnable candidate.
fn repeatedBinderMemberMismatch(
    context: *const Context,
    theorem: *TheoremContext,
    region: TemplateExpr.App,
    goal_expr: ExprId,
    bindings: []const ?ExprId,
) bool {
    if (bindings.len == 0 or bindings.len > max_repeated_binder_binders) return false;
    var members: [max_split_guard_members]TemplateExpr = undefined;
    var member_len: usize = 0;
    collectAcuiMemberTemplates(region, region.term_id, &members, &member_len);
    if (member_len < 2) return false;

    // The unbound binder shared by ≥2 members (the repeated-binder schema).
    var repeated: ?usize = null;
    for (bindings, 0..) |binding, bi| {
        if (binding != null) continue;
        var count: usize = 0;
        for (members[0..member_len]) |m| {
            if (templateMentionsBinder(m, bi)) count += 1;
        }
        if (count >= 2) {
            repeated = bi;
            break;
        }
    }
    const b = repeated orelse return false;

    const goal_members = collectSplitMembers(
        context,
        theorem,
        goal_expr,
        region.term_id,
    ) orelse return false;
    if (goal_members.len == 0) return false;

    // A member mentioning `b`, used to enumerate `b`'s candidate values off the
    // goal (matchTemplate reads through the `hyp(...)` coercion structurally).
    var seed: ?TemplateExpr = null;
    for (members[0..member_len]) |m| {
        if (templateMentionsBinder(m, b)) {
            seed = m;
            break;
        }
    }
    const seed_member = seed orelse return false;

    for (goal_members.items[0..goal_members.len]) |g0| {
        var s0: [max_repeated_binder_binders]?ExprId = undefined;
        @memcpy(s0[0..bindings.len], bindings);
        if (!theorem.matchTemplate(seed_member, g0, s0[0..bindings.len])) continue;
        const bval = s0[b] orelse continue;

        var all_present = true;
        for (members[0..member_len]) |m| {
            if (!templateMentionsBinder(m, b)) continue;
            var found = false;
            for (goal_members.items[0..goal_members.len]) |gm| {
                var sm: [max_repeated_binder_binders]?ExprId = undefined;
                @memcpy(sm[0..bindings.len], bindings);
                sm[b] = bval;
                if (theorem.matchTemplate(m, gm, sm[0..bindings.len])) {
                    found = true;
                    break;
                }
            }
            if (!found) {
                all_present = false;
                break;
            }
        }
        if (all_present) return false; // a consistent assignment exists → plausible
    }
    return true; // no goal value of `b` covers every occurrence → definite mismatch
}

// ============================================================
// Hyp-vs-ref ACUI member consistency.
//
// A loose backward candidate whose principal binders sit inside an ACUI
// conclusion region arrives at validation with those binders UNBOUND (the
// seed never descends ACUI spines), so its premise slots are wildcard
// sequents and the plan pairs them with every pool line — each doomed
// (candidate, refs) tuple then burns a full `tryCandidate`. This check
// refutes such tuples cheaply: enumerate the (bounded) ways the conclusion
// template's unbound compound members can match the concrete goal's region
// members, and for each assignment require every pool-ref conclusion to be
// ACUI-member-consistent with its instantiated hypothesis:
//   (1) every determined hyp member must possibly appear in the ref;
//   (2) every ref member must be a determined member or a goal member
//       reachable through a rest binder;
//   (3) every goal member NOT consumed by a conclusion member must appear
//       in any ref whose hypothesis carries that region's full rest.
// Necessary condition only — every uncertainty abstains (transparent-def
// heads, placeholders, hyp-only binders, nested ACUI heads inside a member
// template, cap overflows), so a winnable tuple is never pruned.
// ============================================================

const max_hypref_regions: usize = 4;
const max_hypref_items: usize = 4;
const max_hypref_consumed: usize = 8;
const max_hypref_leaves: usize = 32;

const RegionPair = struct { app: TemplateExpr.App, expr: ExprId };
const HypRefItem = struct { member: TemplateExpr, region: usize };
const HypRefOutcome = enum { found, exhausted, abstain };
const HypEval = enum { pass, fail, abstain };

const HypRefState = struct {
    context: *const Context,
    theorem: *TheoremContext,
    rule: *const RuleDecl,
    regions: []const RegionPair,
    goal_members: [max_hypref_regions]SplitMemberList,
    // Per-binder: the conclusion region in which it is a bare (rest) member.
    rest_region: [max_repeated_binder_binders]?usize,
    // Per-region: how many distinct rest binders it holds.
    rest_count: [max_hypref_regions]usize,
    // Per-region: the non-rest ("consumed") member templates.
    consumed: [max_hypref_regions][max_hypref_consumed]TemplateExpr,
    consumed_len: [max_hypref_regions]usize,
    ref_concls: []const ?ExprId,
    leaves: usize,
};

pub fn hypRefMembersPlausible(
    context: *const Context,
    theorem: *TheoremContext,
    rule_id: u32,
    goal: Goal,
    bindings: []const ?ExprId,
    ref_concls: []const ?ExprId,
) bool {
    if (context.views.contains(rule_id)) return true;
    const goal_expr = switch (goal) {
        .concrete => |e| e,
        else => return true,
    };
    if (bindings.len == 0 or bindings.len > max_repeated_binder_binders) return true;
    var any_ref = false;
    for (ref_concls) |rc| {
        if (rc != null) any_ref = true;
    }
    if (!any_ref) return true;
    const rule = &context.env.rules.items[@intCast(rule_id)];
    if (rule.hyps.len != ref_concls.len) return true;

    var regions: [max_hypref_regions]RegionPair = undefined;
    var region_len: usize = 0;
    if (!collectLockstepRegions(
        context,
        theorem,
        rule.concl,
        goal_expr,
        &regions,
        &region_len,
    )) return true;
    if (region_len == 0) return true;

    var state = HypRefState{
        .context = context,
        .theorem = theorem,
        .rule = rule,
        .regions = regions[0..region_len],
        .goal_members = undefined,
        .rest_region = [_]?usize{null} ** max_repeated_binder_binders,
        .rest_count = [_]usize{0} ** max_hypref_regions,
        .consumed = undefined,
        .consumed_len = [_]usize{0} ** max_hypref_regions,
        .ref_concls = ref_concls,
        .leaves = max_hypref_leaves,
    };

    for (regions[0..region_len], 0..) |r, i| {
        state.goal_members[i] = collectSplitMembers(
            context,
            theorem,
            r.expr,
            r.app.term_id,
        ) orelse return true;
        // The strict `matchTemplate` enumeration below cannot see through a
        // transparent def, so a foldable goal member could hide the true
        // assignment — abstain.
        for (state.goal_members[i].items[0..state.goal_members[i].len]) |gm| {
            const node = theorem.interner.node(gm);
            if (node.* == .app and isTransparentDefHead(context, node.app.term_id)) {
                return true;
            }
        }
    }

    var items: [max_hypref_items]HypRefItem = undefined;
    var item_len: usize = 0;
    for (regions[0..region_len], 0..) |r, ridx| {
        var mts: [max_split_guard_members]TemplateExpr = undefined;
        var mts_len: usize = 0;
        collectAcuiMemberTemplates(r.app, r.app.term_id, &mts, &mts_len);
        for (mts[0..mts_len]) |m| {
            switch (m) {
                .binder => |bi| {
                    if (bi >= bindings.len) return true;
                    if (bindings[bi] != null) {
                        if (state.consumed_len[ridx] == max_hypref_consumed) return true;
                        state.consumed[ridx][state.consumed_len[ridx]] = m;
                        state.consumed_len[ridx] += 1;
                        continue;
                    }
                    // Bare unbound member in two regions: which region's
                    // members feed it is ambiguous — abstain.
                    if (state.rest_region[bi] != null) return true;
                    state.rest_region[bi] = ridx;
                    state.rest_count[ridx] += 1;
                },
                .app => {
                    if (state.consumed_len[ridx] == max_hypref_consumed) return true;
                    state.consumed[ridx][state.consumed_len[ridx]] = m;
                    state.consumed_len[ridx] += 1;
                    if (split.templateFullyBound(m, bindings)) continue;
                    // A member template that itself embeds an ACUI head (or a
                    // transparent def head) can match goal members in ways the
                    // strict matcher misses — abstain.
                    if (templateMentionsSpecialHead(context, m)) return true;
                    if (item_len == max_hypref_items) return true;
                    items[item_len] = .{ .member = m, .region = ridx };
                    item_len += 1;
                },
            }
        }
    }

    var merged: [max_repeated_binder_binders]?ExprId = undefined;
    @memcpy(merged[0..bindings.len], bindings);
    const outcome = hypRefDfs(&state, items[0..item_len], 0, merged[0..bindings.len]);
    return outcome != .exhausted;
}

fn templateMentionsSpecialHead(context: *const Context, t: TemplateExpr) bool {
    switch (t) {
        .binder => return false,
        .app => |app| {
            if (context.registry.acui_by_head.contains(app.term_id)) return true;
            if (isTransparentDefHead(context, app.term_id)) return true;
            for (app.args) |arg| {
                if (templateMentionsSpecialHead(context, arg)) return true;
            }
            return false;
        },
    }
}

fn collectLockstepRegions(
    context: *const Context,
    theorem: *const TheoremContext,
    template: TemplateExpr,
    expr_id: ExprId,
    out: *[max_hypref_regions]RegionPair,
    len: *usize,
) bool {
    switch (template) {
        // A binder in a rigid position imposes no member constraint here.
        .binder => return true,
        .app => |app| {
            if (context.registry.acui_by_head.contains(app.term_id)) {
                if (len.* == max_hypref_regions) return false;
                out[len.*] = .{ .app = app, .expr = expr_id };
                len.* += 1;
                return true;
            }
            const node = theorem.interner.node(expr_id);
            switch (node.*) {
                .app => |g| {
                    // Head/arity mismatch: a def could bridge — abstain by
                    // reporting a structural surprise to the caller.
                    if (g.term_id != app.term_id) return false;
                    if (g.args.len != app.args.len) return false;
                    for (app.args, g.args) |ta, ga| {
                        if (!collectLockstepRegions(
                            context,
                            theorem,
                            ta,
                            ga,
                            out,
                            len,
                        )) return false;
                    }
                    return true;
                },
                else => return false,
            }
        },
    }
}

fn hypRefDfs(
    state: *HypRefState,
    items: []const HypRefItem,
    idx: usize,
    merged: []?ExprId,
) HypRefOutcome {
    if (idx == items.len) {
        if (state.leaves == 0) return .abstain;
        state.leaves -= 1;
        return switch (evalHypsForAssignment(state, merged)) {
            .pass => .found,
            .fail => .exhausted,
            .abstain => .abstain,
        };
    }
    const item = items[idx];
    const gms = &state.goal_members[item.region];
    var scratch: [max_repeated_binder_binders]?ExprId = undefined;
    for (gms.items[0..gms.len]) |gm| {
        if (state.leaves == 0) return .abstain;
        @memcpy(scratch[0..merged.len], merged);
        if (!state.theorem.matchTemplate(item.member, gm, scratch[0..merged.len])) continue;
        switch (hypRefDfs(state, items, idx + 1, scratch[0..merged.len])) {
            .found => return .found,
            .abstain => return .abstain,
            .exhausted => {},
        }
    }
    return .exhausted;
}

fn evalHypsForAssignment(state: *HypRefState, merged: []const ?ExprId) HypEval {
    const context = state.context;
    const theorem = state.theorem;

    // Instantiate each region's consumed (non-rest) conclusion members under
    // this assignment, for the direction-3 remainder check below.
    var consumed_vals: [max_hypref_regions]SplitMemberList = undefined;
    for (state.regions, 0..) |r, ridx| {
        consumed_vals[ridx] = SplitMemberList{};
        for (state.consumed[ridx][0..state.consumed_len[ridx]]) |ct| {
            if (!split.templateFullyBound(ct, merged)) return .abstain;
            const v = (OpenTerms.instantiateTemplateConcrete(
                theorem,
                ct,
                merged,
            ) catch return .abstain) orelse return .abstain;
            const vm = collectSplitMembers(
                context,
                theorem,
                v,
                r.app.term_id,
            ) orelse return .abstain;
            for (vm.items[0..vm.len]) |vmm| {
                if (!consumed_vals[ridx].appendDistinct(vmm)) return .abstain;
            }
        }
    }

    for (state.rule.hyps, 0..) |hyp_tmpl, hi| {
        const rc = state.ref_concls[hi] orelse continue;
        var hregions: [max_hypref_regions]RegionPair = undefined;
        var hlen: usize = 0;
        if (!collectLockstepRegions(
            context,
            theorem,
            hyp_tmpl,
            rc,
            &hregions,
            &hlen,
        )) return .abstain;
        for (hregions[0..hlen]) |hr| {
            const ref_members = collectSplitMembers(
                context,
                theorem,
                hr.expr,
                hr.app.term_id,
            ) orelse return .abstain;
            var mts: [max_split_guard_members]TemplateExpr = undefined;
            var mts_len: usize = 0;
            collectAcuiMemberTemplates(hr.app, hr.app.term_id, &mts, &mts_len);
            var inst = SplitMemberList{};
            var rest_mask = [_]bool{false} ** max_hypref_regions;
            var hyp_rest_count = [_]usize{0} ** max_hypref_regions;
            var has_rest = false;
            for (mts[0..mts_len]) |m| {
                switch (m) {
                    .binder => |bi| {
                        if (bi >= merged.len) return .abstain;
                        if (merged[bi]) |v| {
                            // The bound value may itself be a combiner spine
                            // (or a unit): flatten it the same way the goal
                            // side is flattened.
                            const vm = collectSplitMembers(
                                context,
                                theorem,
                                v,
                                hr.app.term_id,
                            ) orelse return .abstain;
                            for (vm.items[0..vm.len]) |vmm| {
                                if (!inst.appendDistinct(vmm)) return .abstain;
                            }
                        } else if (state.rest_region[bi]) |ridx| {
                            // A rest binder shared with the conclusion region:
                            // its members are necessarily goal members of that
                            // region (same combiner head required).
                            if (state.regions[ridx].app.term_id != hr.app.term_id) {
                                return .abstain;
                            }
                            rest_mask[ridx] = true;
                            hyp_rest_count[ridx] += 1;
                            has_rest = true;
                        } else {
                            // Hyp-only unbound binder (e.g. a witness) — no
                            // way to bound its members.
                            return .abstain;
                        }
                    },
                    .app => {
                        if (!split.templateFullyBound(m, merged)) {
                            return .abstain;
                        }
                        const v = (OpenTerms.instantiateTemplateConcrete(
                            theorem,
                            m,
                            merged,
                        ) catch return .abstain) orelse return .abstain;
                        const vm = collectSplitMembers(
                            context,
                            theorem,
                            v,
                            hr.app.term_id,
                        ) orelse return .abstain;
                        for (vm.items[0..vm.len]) |vmm| {
                            if (!inst.appendDistinct(vmm)) return .abstain;
                        }
                    },
                }
            }
            // Direction 1: every determined hypothesis member must possibly
            // appear in the ref's conclusion.
            for (inst.items[0..inst.len]) |v| {
                if (!memberPossiblyInList(context, theorem, v, ref_members)) {
                    return .fail;
                }
            }
            // Direction 2: every ref member must be accounted for by a
            // determined member or by a rest binder's goal-member pool.
            for (ref_members.items[0..ref_members.len]) |r| {
                var ok = memberPossiblyInList(context, theorem, r, inst);
                if (!ok and has_rest) {
                    for (rest_mask, 0..) |used, ridx| {
                        if (!used) continue;
                        if (memberPossiblyInList(
                            context,
                            theorem,
                            r,
                            state.goal_members[ridx],
                        )) {
                            ok = true;
                            break;
                        }
                    }
                }
                if (!ok) return .fail;
            }
            // Direction 3: every goal member the conclusion's non-rest members
            // do NOT consume belongs to the rest — so it must appear in a ref
            // whose hypothesis carries that region's FULL rest (with a partial
            // rest the member might live in the other rest binder — skip).
            for (rest_mask, 0..) |used, ridx| {
                if (!used) continue;
                if (hyp_rest_count[ridx] != state.rest_count[ridx]) continue;
                const gms = &state.goal_members[ridx];
                for (gms.items[0..gms.len]) |gm| {
                    if (memberPossiblyInList(
                        context,
                        theorem,
                        gm,
                        consumed_vals[ridx],
                    )) continue;
                    if (!memberPossiblyInList(context, theorem, gm, ref_members)) {
                        return .fail;
                    }
                }
            }
        }
    }
    return .pass;
}

fn templateMentionsBinder(t: TemplateExpr, b: usize) bool {
    return switch (t) {
        .binder => |idx| idx == b,
        .app => |app| {
            for (app.args) |arg| {
                if (templateMentionsBinder(arg, b)) return true;
            }
            return false;
        },
    };
}

/// Flatten an ACUI region template into its member templates (descending nested
/// combiner apps of the same head, mirroring `collectSplitMembers` on the
/// concrete side).
fn collectAcuiMemberTemplates(
    region: TemplateExpr.App,
    head_id: u32,
    out: *[max_split_guard_members]TemplateExpr,
    len: *usize,
) void {
    for (region.args) |arg| {
        switch (arg) {
            .app => |inner| {
                if (inner.term_id == head_id) {
                    collectAcuiMemberTemplates(inner, head_id, out, len);
                    continue;
                }
            },
            else => {},
        }
        if (len.* < out.len) {
            out[len.*] = arg;
            len.* += 1;
        }
    }
}

const max_folded_body_probe_depth: usize = 64;

fn foldedGoalBodyMismatch(
    context: *const Context,
    theorem: *TheoremContext,
    template: TemplateExpr,
    goal_expr: ExprId,
    bindings: []const ?ExprId,
    depth: usize,
) bool {
    if (depth >= max_folded_body_probe_depth) return false;
    switch (template) {
        .binder => |idx| {
            if (idx >= bindings.len) return false;
            const bound = bindings[idx] orelse return false;
            return unfoldedExprMismatch(
                context,
                theorem,
                bound,
                goal_expr,
                depth + 1,
            );
        },
        .app => |app| {
            const goal_node = theorem.interner.node(goal_expr);
            const goal_app = switch (goal_node.*) {
                .app => |concrete| concrete,
                else => return false,
            };
            if (goal_app.term_id == app.term_id) {
                if (goal_app.args.len != app.args.len) return false;
                if (context.registry.acui_by_head.contains(app.term_id)) {
                    return false;
                }
                const goal_args = theorem.allocator.dupe(
                    ExprId,
                    goal_app.args,
                ) catch return false;
                defer theorem.allocator.free(goal_args);
                for (app.args, goal_args) |arg, goal_arg| {
                    if (foldedGoalBodyMismatch(
                        context,
                        theorem,
                        arg,
                        goal_arg,
                        bindings,
                        depth + 1,
                    )) return true;
                }
                return false;
            }
            const unfolded_goal = unfoldExprOnce(
                context,
                theorem,
                goal_expr,
            ) catch return false;
            if (unfolded_goal == goal_expr) return false;
            const unfolded_node = theorem.interner.node(unfolded_goal);
            const unfolded_app = switch (unfolded_node.*) {
                .app => |concrete| concrete,
                else => return false,
            };
            if (unfolded_app.term_id != app.term_id) return false;
            if (unfolded_app.args.len != app.args.len) return false;
            if (context.registry.acui_by_head.contains(app.term_id)) return false;
            const goal_args = theorem.allocator.dupe(
                ExprId,
                unfolded_app.args,
            ) catch return false;
            defer theorem.allocator.free(goal_args);
            for (app.args, goal_args) |arg, goal_arg| {
                if (templateArgMismatchAfterGoalUnfold(
                    context,
                    theorem,
                    arg,
                    goal_arg,
                    bindings,
                    depth + 1,
                )) return true;
            }
            return false;
        },
    }
}

fn templateArgMismatchAfterGoalUnfold(
    context: *const Context,
    theorem: *TheoremContext,
    template: TemplateExpr,
    goal_arg: ExprId,
    bindings: []const ?ExprId,
    depth: usize,
) bool {
    const instantiated = (OpenTerms.instantiateTemplateConcrete(
        theorem,
        template,
        bindings,
    ) catch null) orelse {
        return templateDefiniteMismatch(
            context,
            theorem,
            template,
            goal_arg,
            bindings,
        );
    };
    return unfoldedExprMismatch(
        context,
        theorem,
        instantiated,
        goal_arg,
        depth + 1,
    );
}

fn unfoldedExprMismatch(
    context: *const Context,
    theorem: *TheoremContext,
    a: ExprId,
    b: ExprId,
    depth: usize,
) bool {
    if (a == b) return false;
    if (depth >= max_folded_body_probe_depth) return false;
    const na = theorem.interner.node(a);
    const nb = theorem.interner.node(b);
    switch (na.*) {
        .placeholder => return false,
        .variable => switch (nb.*) {
            .placeholder => return false,
            .variable => return true,
            .app => {},
        },
        .app => |aa| if (context.registry.acui_by_head.contains(aa.term_id)) {
            return false;
        },
    }
    switch (nb.*) {
        .placeholder => return false,
        .variable => {},
        .app => |bb| if (context.registry.acui_by_head.contains(bb.term_id)) {
            return false;
        },
    }
    if (prune.rigidExprMismatch(context, theorem, a, b)) return true;
    const ua = unfoldExprOnce(context, theorem, a) catch return false;
    const ub = unfoldExprOnce(context, theorem, b) catch return false;
    if (ua != a or ub != b) {
        return unfoldedExprMismatch(context, theorem, ua, ub, depth + 1);
    }
    const nua = theorem.interner.node(a);
    const nub = theorem.interner.node(b);
    switch (nua.*) {
        .placeholder => return false,
        .variable => switch (nub.*) {
            .placeholder => return false,
            .variable => return true,
            .app => return prune.rigidExprMismatch(context, theorem, a, b),
        },
        .app => |aa| switch (nub.*) {
            .placeholder => return false,
            .variable => return prune.rigidExprMismatch(context, theorem, a, b),
            .app => |bb| {
                if (aa.term_id != bb.term_id) {
                    if (plainRigidTerm(context, aa.term_id) and
                        plainRigidTerm(context, bb.term_id))
                    {
                        return true;
                    }
                    return prune.rigidExprMismatch(context, theorem, a, b);
                }
                if (aa.args.len != bb.args.len) return false;
                const a_args = theorem.allocator.dupe(
                    ExprId,
                    aa.args,
                ) catch return false;
                defer theorem.allocator.free(a_args);
                const b_args = theorem.allocator.dupe(
                    ExprId,
                    bb.args,
                ) catch return false;
                defer theorem.allocator.free(b_args);
                for (a_args, b_args) |a_arg, b_arg| {
                    if (unfoldedExprMismatch(
                        context,
                        theorem,
                        a_arg,
                        b_arg,
                        depth + 1,
                    )) return true;
                }
                return false;
            },
        },
    }
}

fn plainRigidTerm(context: *const Context, term_id: u32) bool {
    if (context.registry.acui_by_head.contains(term_id)) return false;
    // A `@rewrite`-reducible head can rewrite to a different head, so a clash
    // between two such heads is never definite. Mirror `rigidExprMismatch`'s
    // `headIsReducibleNode` guard: without this the fast-path at
    // `unfoldedExprMismatch`'s `aa.term_id != bb.term_id` branch reports a
    // mismatch before `rigidExprMismatch` (which abstains on reducible heads)
    // is reached, wrongly pruning a candidate a rewrite step could reconcile.
    if (context.registry.rewrites_by_head.contains(term_id)) return false;
    if (!context.env.hasAvailableTerm(term_id)) return false;
    const term = context.env.terms.items[term_id];
    return term.available and !term.is_def;
}

fn unfoldExprOnce(
    context: *const Context,
    theorem: *TheoremContext,
    expr: ExprId,
) !ExprId {
    const node = theorem.interner.node(expr);
    const app = switch (node.*) {
        .app => |concrete| concrete,
        else => return expr,
    };
    const info = defBodyForUnfold(context, app.term_id, true) orelse return expr;
    if (app.args.len != info.nargs) return expr;
    return try unfoldDefBody(theorem, info, app.args);
}
