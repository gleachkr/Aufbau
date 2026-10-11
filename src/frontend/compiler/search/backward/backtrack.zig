const std = @import("std");
const types = @import("../types.zig");
const refs_mod = @import("../refs.zig");
const ref_index_mod = @import("../ref_index.zig");
const rank = @import("../rank.zig");
const def_match = @import("./def_match.zig");
const abstract_prune = @import("../abstract_prune.zig");
const context_prune = @import("../context_prune.zig");
const seed = @import("./seed.zig");
const split = @import("./split.zig");
const lockstep = @import("./lockstep.zig");
const acui = @import("./acui.zig");
const Witness = @import("./witness.zig");
const match = @import("./match.zig");
const plausible = @import("./plausible.zig");
const lookup_mod = @import("./lookup.zig");
const plan = @import("./plan.zig");
const validate = @import("./validate.zig");
const forward = @import("../forward.zig");
const session_mod = @import("../session.zig");
const ExprId = @import("../../../expr.zig").ExprId;
const TheoremContext = @import("../../../expr.zig").TheoremContext;
const RuleDecl = @import("../../../env.zig").RuleDecl;
const TemplateExpr = @import("../../../rules.zig").TemplateExpr;
const ProofScript = @import("../../../proof_script.zig");
const RuleApplication = ProofScript.RuleApplication;
const CompilerContext = @import("../../context.zig").CompilerContext;
const OpenTerms = @import("../../inference/open_terms.zig");
const Redex = @import("./redex.zig");
const Goal = types.Goal;
const Context = types.Context;
const ApplyCandidate = types.ApplyCandidate;
const ExactCandidate = types.ExactCandidate;
const ExactOptions = types.ExactOptions;
const ExactResults = types.ExactResults;
const SearchCounters = types.SearchCounters;
const SearchRuntime = types.SearchRuntime;
const NameExprMap = types.NameExprMap;
const GenerationHook = types.GenerationHook;
const DerivedPool = types.DerivedPool;
const Fuel = types.Fuel;
const exactCandidateLessThan = rank.exactCandidateLessThan;
const isBroadWholeLineHole = rank.isBroadWholeLineHole;
const normalizeAcuiUnits = acui.normalizeAcuiUnits;
const unfoldDefBody = def_match.unfoldDefBody;

const matchOneHypWithSnapshot = match.matchOneHypWithSnapshot;
const seedViewBindingsForMatch = match.seedViewBindingsForMatch;
const rollbackOneHypMatch = match.rollbackOneHypMatch;
const finalConclusionPlausible = plausible.finalConclusionPlausible;
const splitSiteBindingsPlausible = plausible.splitSiteBindingsPlausible;
const collectSplitMembers = plausible.collectSplitMembers;
const lookupHypReferences = lookup_mod.lookupHypReferences;
const HypPlan = plan.HypPlan;
const buildHypPlans = plan.buildHypPlans;
const templateBinderMask = plan.templateBinderMask;
const hasPremiseOnlyBinder =
    @import("../../../rules.zig").hasPremiseOnlyBinder;
const conclusionBinderMaskOrNone = plan.conclusionBinderMaskOrNone;
const validateSelectedRefs = validate.validateSelectedRefs;
const appendDerivedDirectCandidates = validate.appendDerivedDirectCandidates;
const open_slot = @import("./open_slot.zig");
const tryOpenGenerateSlot = open_slot.tryOpenGenerateSlot;
const rebindHiddenVars = open_slot.rebindHiddenVars;
const heldElsewhere = open_slot.heldElsewhere;
const isHiddenVarLeaf = open_slot.isHiddenVarLeaf;
const bindingsDepHit = open_slot.bindingsDepHit;
const ruleMayRechooseBound = open_slot.ruleMayRechooseBound;
const emitOpenTarget = open_slot.emitOpenTarget;
const ExplicitFlag = open_slot.ExplicitFlag;
const handSplitChoice = open_slot.handSplitChoice;

pub fn exact(
    compiler: *CompilerContext,
    context: *const Context,
    goal: Goal,
    theorem: *const TheoremContext,
    theorem_vars: *const NameExprMap,
    options: ExactOptions,
) !ExactResults {
    var session = session_mod.SearchSession.init(context, .{
        .counters = options.counters,
    });
    defer session.deinit();
    return exactWithSession(
        compiler,
        &session,
        goal,
        theorem,
        theorem_vars,
        options,
    );
}

pub fn exactWithSession(
    compiler: *CompilerContext,
    session: *session_mod.SearchSession,
    goal: Goal,
    theorem: *const TheoremContext,
    theorem_vars: *const NameExprMap,
    options: ExactOptions,
) !ExactResults {
    const context = session.context;
    const allocator = context.allocator;
    const counters = session.effectiveCounters(options.counters);
    const runtime = options.runtime;
    const pool = try session.getReferencePool(theorem, counters);

    var candidates = std.ArrayListUnmanaged(ExactCandidate).empty;
    errdefer {
        for (candidates.items) |*candidate| {
            candidate.deinit();
        }
        candidates.deinit(allocator);
    }

    const broad_whole_hole = isBroadWholeLineHole(goal);
    if (broad_whole_hole and pool.len == 0) {
        return .{
            .allocator = allocator,
            .candidates = try candidates.toOwnedSlice(allocator),
        };
    }

    const apply_candidates = try exactRuleCandidates(
        session,
        goal,
        theorem,
        // `auto?` has no machinery to guide `@abstract` motive inference, so
        // on the generation path an abstract-view rule (e.g. Leibniz
        // `eq_replace`, whose bare-binder view hypothesis matches every ref)
        // only floods validation with doomed assemblies — skip such rules
        // before even seeding their candidates. This is the settled
        // `@auto`-generation discipline, not a transitional gap: direct
        // `exact?`/`apply?` (generator == null) still offer them.
        options.generator != null,
        counters,
    );
    defer deinitApplyCandidates(allocator, apply_candidates);

    // When generating, try non-splitting (additive) rules before split-capable
    // (multiplicative) ones, so a goal solvable without a speculative context
    // split claims the bounded generation budget first. Within a band, the rule
    // whose conclusion matches more of the goal goes first (`matchSpecificity`).
    // Stable, and only on the generation path — plain `exact?` ordering is
    // untouched. The order is a permutation of indices: a candidate carries
    // its theorem by value, too large to move.
    const order = try allocator.alloc(u32, apply_candidates.len);
    defer allocator.free(order);
    for (order, 0..) |*slot, idx| slot.* = @intCast(idx);
    if (options.generator != null) {
        for (apply_candidates) |*apply_candidate| {
            apply_candidate.concl_is_split = split.conclusionIsSplit(
                context,
                context.env.rules.items[apply_candidate.rule_id].concl,
            );
            apply_candidate.order_class = generationOrderClass(context, apply_candidate.rule_id);
        }
        if (goal.concreteOrHint()) |goal_expr| {
            for (apply_candidates) |*apply_candidate| {
                apply_candidate.match_specificity = matchSpecificity(
                    context,
                    &apply_candidate.theorem,
                    context.env.rules.items[apply_candidate.rule_id].concl,
                    goal_expr,
                );
            }
        }
        std.sort.insertion(u32, order, apply_candidates, nonSplitCandidateFirst);
    }

    const ref_index = try session.getRefIndex(theorem, counters);
    // A direct search (no `fuel`) spends its candidates from the call's
    // budget, and stops where it runs out with what it has validated.
    var direct_fuel = Fuel{ .remaining = std.math.maxInt(usize), .global = options.budget };
    const fuel: ?*Fuel = options.fuel orelse
        if (options.budget != null) &direct_fuel else null;
    // `@auto eager` set-commit cut (generation path only, mirroring the sort
    // gate above — plain `exact?` never has an eager band). Once an eager
    // candidate has actually *applied* — reached a child solve or produced a
    // validated result — the remaining non-eager candidates are skipped: the
    // user declared the decomposition invertible, so if it fails, the goal
    // fails. All eager candidates (other bag members, other eager rules) are
    // still tried. The eager band is not contiguous: split-ness sorts first,
    // so a split eager rule comes after every non-split rule, and the cut
    // skips the non-eager candidates rather than ending the enumeration. A
    // mis-annotated (non-invertible) eager rule can therefore lose proofs;
    // the annotation is trusted. The eager *depth exemption* rides on
    // `emitGeneratedSlot`'s hook call, not on this cut. See
    // docs/design_notes/eager_rule_scheduling.md.
    const eager_cut = options.generator != null and
        context.registry.autoEagerRuleCount() > 0;
    var eager_armed = false;
    for (order) |candidate_idx| {
        const apply_candidate = &apply_candidates[candidate_idx];
        apply_candidate.internal_child = options.internal_open_child;
        const is_eager = eager_cut and
            context.registry.eagerPriority(apply_candidate.rule_id) != null;
        if (eager_armed and !is_eager) continue;
        const hyp_count = apply_candidate.unresolved_hyps.len;
        // An empty pool can't fill any hyp — unless a generator can synthesize
        // sub-proofs for them, or a derived ref can fill a slot.
        if (hyp_count > 0 and pool.len == 0 and
            options.generator == null and options.derived == null) continue;
        if (broad_whole_hole and hyp_count == 0) continue;
        if (!seed.conclusionMembersPlausible(
            context,
            apply_candidate,
            goal,
        )) {
            if (counters) |c| c.conclusion_member_prunes += 1;
            continue;
        }
        // A conclusion binding that rigidly mentions a bound binder its
        // dependency list omits dooms the application: no conversion removes
        // the occurrence, and without a view, `@fresh` or `@freshen` nothing
        // re-chooses the bound binder, so every assembly fails the checker's
        // DepViolation. (e.g. `weaken`'s `g , x : T ⊢ J` against
        // `g , k : Nat ⊢ suc k : Nat` binds `J := suc k : Nat`.)
        const dep_hit = bindingsDepHit(
            context,
            &apply_candidate.theorem,
            &context.env.rules.items[apply_candidate.rule_id],
            apply_candidate.bindings,
        );
        if (dep_hit == .rigid and !ruleMayRechooseBound(context, apply_candidate.rule_id)) {
            if (counters) |c| c.dep_violation_prunes += 1;
            continue;
        }

        const results_before = candidates.items.len;
        enumerateCandidateRefs(
            compiler,
            context,
            ref_index,
            pool,
            apply_candidate,
            goal,
            theorem,
            theorem_vars,
            options.generator,
            options.derived,
            runtime,
            counters,
            fuel,
            &candidates,
        ) catch |err| switch (err) {
            error.SearchBudgetExhausted => if (options.fuel == null) break else return err,
            else => return err,
        };
        // An eager candidate whose conclusion bindings may break the rule's
        // eigenvariable condition does not arm the cut: the step may not be
        // applicable as matched (e.g. `all_intro` over a context that
        // mentions `y` free), so it says nothing about the goal's other
        // rules. The rigid, view-less case was pruned above; the rest is
        // tried, since a conversion, view or `@freshen` may still repair it.
        if (is_eager and
            (apply_candidate.reached_child_solve or
                candidates.items.len > results_before) and
            dep_hit == .none)
        {
            eager_armed = true;
        }
        // Internal generation children stop enumerating once as many results
        // exist as the caller will keep (see `ExactOptions.internal_open_child`).
        if (options.internal_open_child) {
            if (options.max_results) |max| {
                if (candidates.items.len >= max) break;
            }
        }
    }

    // A derived forward ref whose shape directly matches the goal is
    // itself a complete proof — materialize the recipe and validate it.
    if (options.derived) |dpool| {
        try appendDerivedDirectCandidates(
            compiler,
            allocator,
            context,
            dpool,
            goal,
            theorem,
            theorem_vars,
            runtime,
            counters,
            options.fuel,
            &candidates,
        );
    }

    std.mem.sort(
        ExactCandidate,
        candidates.items,
        {},
        exactCandidateLessThan,
    );
    if (options.max_results) |max| {
        if (max < candidates.items.len) {
            for (candidates.items[max..]) |*candidate| {
                candidate.deinit();
            }
            candidates.shrinkRetainingCapacity(max);
        }
    }
    return .{
        .allocator = allocator,
        .candidates = try candidates.toOwnedSlice(allocator),
    };
}

/// True when the rule's view declares any `@abstract` derived binding (a
/// motive the validator must invent — search offers no guidance for these).
fn viewHasAbstract(context: *const Context, rule_id: u32) bool {
    const view = context.views.get(rule_id) orelse return false;
    return viewDeclHasAbstract(view);
}

fn viewDeclHasAbstract(view: types.ViewDecl) bool {
    for (view.derived_bindings) |derived| {
        switch (derived) {
            .abstract => return true,
            .recover => {},
        }
    }
    return false;
}

/// Loop-invariant candidate-ref pruning setup for one rule. Every field is a
/// pure function of `(context, rule_id)`, so each candidate computes it once
/// (`SlotCtx.prune_setup`) rather than at every DFS node (a single hoisted
/// `views.get` plus the static `analyzeView` flatten).
const PruneSetup = struct {
    /// The view when it carries an `@abstract` decl (else null): gates the
    /// Leibniz one-hole-context prefilter (`abstract_prune.zig`).
    abstract_view: ?types.ViewDecl,
    /// The analysed ACUI context-combination info (`context_prune.zig`), or null
    /// when the rule has no context position to reason about.
    context_info: ?context_prune.Info,
    /// True when `context_info` was built in raw rule binder space, so the
    /// current rule bindings can be used for shape-aware discharge pruning.
    context_uses_rule_bindings: bool,
    /// The rule's conclusion has a `@rewrite` head, so `validateSelectedRefs`
    /// runs the redex check.
    concl_has_rewrite_head: bool,
};

fn computePruneSetup(context: *const Context, rule_id: u32) PruneSetup {
    const rule = context.env.rules.items[rule_id];
    const concl_has_rewrite_head = plausible.templateHasRewriteHead(context, rule.concl);
    if (context.views.get(rule_id)) |view| {
        return .{
            .abstract_view = if (viewDeclHasAbstract(view)) view else null,
            .context_info = context_prune.analyzeView(context, view),
            .context_uses_rule_bindings = false,
            .concl_has_rewrite_head = concl_has_rewrite_head,
        };
    }
    return .{
        .abstract_view = null,
        .context_info = context_prune.analyzeRule(context, rule),
        .context_uses_rule_bindings = true,
        .concl_has_rewrite_head = concl_has_rewrite_head,
    };
}

fn nonSplitCandidateFirst(
    candidates: []const ApplyCandidate,
    a_idx: u32,
    b_idx: u32,
) bool {
    const a = &candidates[a_idx];
    const b = &candidates[b_idx];
    if (a.concl_is_split != b.concl_is_split) {
        return @intFromBool(a.concl_is_split) < @intFromBool(b.concl_is_split);
    }
    // Among same split-ness, order by witness class: non-`@auto` rules first
    // (closing/structural rules like `ax` and the eigenvariable rules
    // `lex`/`rall`, deliberately un-enrolled), then `@auto` rules whose binders
    // are all conclusion-determined (the invertible-style De Morgan/intro
    // steps), and LAST the `@auto` rules that carry a premise-only witness
    // binder (`rex`/`lall`). A witness becomes an existential meta that must be
    // pinned by a later leaf; firing the eigenvariable/invertible rules first
    // brings the eigenvariable into the sequent context so the forced
    // member-witness unification (`tryAcuiMemberWitnesses`) can read the
    // witness off an in-scope member instead of the search drowning in
    // fallbacks.
    if (a.order_class != b.order_class) return a.order_class < b.order_class;
    // Within a band, the rule whose conclusion matches more of the goal first:
    // `t_lam` (`g ⊢ λ x : A. t : A ⇒ B`) before an elimination whose
    // conclusion `g ⊢ b` fits every goal. Under a holey root the elimination's
    // cut carries to full depth, so trying it first spends the node budget.
    return a.match_specificity > b.match_specificity;
}

/// Rigid application nodes of `template` that met the same head in `expr`,
/// counted through the arguments each head determines. A binder, an ACUI
/// combiner, a meta or a head mismatch contributes nothing.
fn matchSpecificity(
    context: *const Context,
    theorem: *const TheoremContext,
    template: TemplateExpr,
    expr: ExprId,
) u16 {
    const app = switch (template) {
        .binder => return 0,
        .app => |app| app,
    };
    if (context.registry.hasStructuralCombiner(app.term_id)) return 0;
    var args = lockstep.templateArgs(context, theorem, app, expr) orelse return 0;
    var count: u16 = 1;
    while (args.next()) |pair| {
        count +|= matchSpecificity(context, theorem, pair.template, pair.expr);
    }
    return count;
}

/// Generation-order band of a rule within equal split-ness: witness class 0
/// (non-enrolled closing/structural rules) first, then the `@auto eager` band
/// ordered by declared priority (1..255), then enrolled conclusion-determined
/// rules (class 1), then witness-deferring rules (class 2). An eager rule is
/// validated to be class-1-shaped, so without the explicit band it would sort
/// with its unannotated class-1 peers; the band puts the user-declared
/// invertible ladder ahead of them, in the user's priority order.
pub fn generationOrderClass(context: *const Context, rule_id: u32) u16 {
    if (context.registry.eagerPriority(rule_id)) |priority| {
        return priority; // 1..255: after class 0 (0), before class 1 (256).
    }
    return switch (witnessClass(context, rule_id)) {
        0 => 0,
        1 => 256,
        else => 257,
    };
}

/// Generation-order class of a rule: 0 = not enrolled in `@auto backward`
/// (unchanged front class -- the pre-existing annotation-trust ordering),
/// 1 = enrolled with every hypothesis binder conclusion-determined,
/// 2 = enrolled with a premise-only binder (a witness the backward
/// application must defer as an existential meta -- `rex`/`lall`'s `t`).
/// Splitting class 1 from class 2 is what lets a one-sided calculus (where
/// EVERY rule is enrolled, so the annotation alone orders nothing) try its
/// invertible De Morgan ladder before the self-feeding witness contraction
/// (`rex`) floods the open-child searches. Overflowed binder masks (>=64
/// binders) conservatively stay in class 1.
pub fn witnessClass(context: *const Context, rule_id: u32) u8 {
    // Scheduling reads enrollment directly by design: ordering and open-path
    // capability are separate axes (see `OpenMode`; uniform structural
    // ordering is task #88's question, not this one's).
    if (!context.registry.isAutoBackwardRule(rule_id)) return 0;
    const rule = context.env.rules.items[rule_id];
    return if (hasPremiseOnlyBinder(rule.concl, rule.hyps)) 2 else 1;
}

/// Open-generation policy for one candidate slot, computed once at each
/// open-path seam instead of re-deriving `isAutoBackwardRule` at every layer.
///
/// `.witness` — exactly `@auto backward` enrollment: the rule may defer a
/// premise-only binder as an existential meta, with the full witness
/// machinery (ancestor-meta carrying, force-first member pass, coupled leaf
/// solving, and — only under `allow_invent_witness` — `@vars` pool
/// invention).
///
/// `.constrained` — a structured open target is built, but the child proof
/// must determine every meta by read-back; no meta propagates into nested
/// open slots (except under a holey root, `hook.open_root`) and nothing is
/// invented. Un-enrolled rules get it in phase 5
/// (constrained backward modus ponens, `hook.allow_constrained_mp`), and
/// `@abstract` motive inference rides that branch too. A premise that only
/// opens a hidden bound variable gets it in every phase
/// (`tryFreshBoundGenerate`).
///
/// `.none` — no open generation for this candidate.
pub const OpenMode = enum { none, constrained, witness };

pub fn openMode(
    context: *const Context,
    rule_id: u32,
    allow_constrained_mp: bool,
) OpenMode {
    if (context.registry.isAutoBackwardRule(rule_id)) return .witness;
    if (allow_constrained_mp) return .constrained;
    return .none;
}

/// Generate a premise whose only open binders are bound variables nothing
/// outside the premise sees, in every phase. Two kinds qualify:
/// - a variable a def hid. Unfolding `A → B` to `Π x : A. B`, on the goal
///   (`pi_form`) or on a ref (`app_elim`'s `f : A → B`), leaves `x` null (the
///   seed scrubs it) or a bare placeholder. When the seed kept a term over
///   the variable (`nat_ind_elim`'s step term `s` over `ih`, `reflt`'s
///   `t := λ x. x` under `T`), the variable is a seed meta instead, and
///   `rebindHiddenVars` opens it in place, whichever binder holds it;
/// - an eigenvariable of an intro-shaped premise (`subset_intro`'s `x` in
///   `G , x ∈ A ⊢ x ∈ B`): the goal fixes every other binder of the premise
///   (`otherHypBindersInConclusion`, a cost gate), and no fixed binding may mention the
///   variable (`noFixedBindingMayMention`; `inst`'s `a : term x` may).
/// The binders open as metas (`fresh_bound` open slot), so a proof below can
/// still name the variable, however deep its ref (`g , y : A ⊢ Ty B` under
/// `list_form`). Only if none does is each given a `@vars` variable occurring
/// in no binding (`tryPoolWitnesses`). Such a variable must avoid every
/// variable of the instance, so any fresh one gives the same instance up to
/// renaming. `@auto backward` rules take this route too: their witness
/// ladder has no fresh-variable rung. A holey goal may still carry the
/// variable as a meta. Reports whether the premise opened this way and
/// whether that produced a candidate; either way the other fallbacks run,
/// but an opened premise is not opened again.
pub fn tryFreshBoundGenerate(
    ctx: *const SlotCtx,
    hook: *const GenerationHook,
    at: Slot,
) anyerror!FreshBound {
    const context = ctx.context;
    const candidate = ctx.candidate;
    const rule = ctx.rule;
    const bindings = ctx.bindings;
    if (ctx.goal != .concrete) return .skipped;
    const cand_theorem = &candidate.theorem;
    const mask = plan.templateBinderMask(rule.hyps[at.hyp_index]);
    if (mask.overflow) return .skipped;
    // A null conclusion binder of a non-view rule met a def's dummy in the
    // concrete goal (the seed scrubs it). A view rule's raw conclusion is not
    // what matched the goal, so there only the placeholder case applies.
    const concl_mask: u64 = if (context.views.contains(candidate.rule_id))
        0
    else
        plan.conclusionBinderMaskOrNone(rule.concl);
    var open: u64 = 0;
    var hosts: u64 = 0;
    var rest = mask.mask;
    while (rest != 0) {
        const idx: u6 = @intCast(@ctz(rest));
        rest &= rest - 1;
        if (idx >= bindings.len) return .skipped;
        const bit = @as(u64, 1) << idx;
        if (bindings[idx]) |value| {
            // Still standing in for a def's hidden variable: the unfolded
            // dummy (`unfoldDefBody`), or a seed meta a ref match would have
            // replaced (`seed.partitionSeedBindings`).
            const kind = cand_theorem.leafPlaceholderKind(value) orelse {
                // A term over a def's hidden variable (`reflt`'s
                // `t := λ x. x` under `T`): the variable opens in place, as
                // no ref matched this premise to name it.
                if (cand_theorem.exprAny(value, {}, isHiddenVarLeaf)) hosts |= bit;
                continue;
            };
            if (kind != .dummy and kind != .seed_meta) continue;
        } else if (concl_mask & bit == 0 and
            !(noFixedBindingMayMention(rule, bindings, idx) and
                otherHypBindersInConclusion(rule, mask.mask, idx))) return .skipped;
        if (!rule.args[idx].bound) return .skipped;
        open |= bit;
    }
    if (open == 0 and hosts == 0) return .skipped;

    if (hook.solveOpenFn == null) return .skipped;
    // Open the def-unfold placeholders too, so the child search can fix them.
    // A seed meta stays put: other kept bindings mention it (`s` under `ih`),
    // and `tryOpenGenerateSlot` rebinds it everywhere at once. So does a
    // dummy another binding also holds (`B` over `x` in `Π x : A. B`), or its
    // copies would open as two variables.
    var saved: [64]?ExprId = undefined;
    var nulled: u64 = 0;
    rest = open;
    while (rest != 0) {
        const idx: u6 = @intCast(@ctz(rest));
        rest &= rest - 1;
        if (bindings[idx]) |value| {
            if (cand_theorem.leafPlaceholderKind(value) == .seed_meta or
                heldElsewhere(cand_theorem, bindings, idx, value)) continue;
        }
        saved[idx] = bindings[idx];
        bindings[idx] = null;
        nulled |= @as(u64, 1) << idx;
    }
    defer {
        rest = nulled;
        while (rest != 0) {
            const idx: u6 = @intCast(@ctz(rest));
            rest &= rest - 1;
            bindings[idx] = saved[idx];
        }
    }

    const before = ctx.candidates.items.len;
    try tryOpenGenerateSlot(ctx, hook, at, .{ .binders = open, .hosts = hosts });
    return if (ctx.candidates.items.len != before) .found else .opened;
}

/// What `tryFreshBoundGenerate` did with a premise.
const FreshBound = enum { skipped, opened, found };

/// True when every non-bound binder of the premise other than `idx` occurs in
/// the rule's conclusion, so the goal alone fixes the premise (intro-shaped,
/// `subset_intro`). A cost gate, not a soundness condition: an elim-shaped
/// premise takes its other binders from a sibling ref (`dvd_elim`'s `a`, `b`),
/// and opening its eigenvariable, though sound, was mostly a doomed search
/// (euclid).
fn otherHypBindersInConclusion(
    rule: *const RuleDecl,
    hyp_mask: u64,
    idx: usize,
) bool {
    const concl = plan.conclusionBinderMaskOrNone(rule.concl);
    var rest = hyp_mask & ~(@as(u64, 1) << @intCast(idx));
    while (rest != 0) {
        const other: u6 = @intCast(@ctz(rest));
        rest &= rest - 1;
        if (rule.args[other].bound) continue;
        if (concl & (@as(u64, 1) << other) == 0) return false;
    }
    return true;
}

/// True when no bound-to-a-value binder of `rule` is declared to depend on
/// bound binder `idx`. Each fixed value must then avoid the variable, so every
/// legal choice is distinct from all of them and any fresh one is equal up to
/// renaming (`subset_intro`'s `x` in `G , x ∈ A ⊢ x ∈ B`). A fixed dependent
/// (`inst`'s `a : term x`) may already mention the right variable.
fn noFixedBindingMayMention(
    rule: *const RuleDecl,
    bindings: []const ?ExprId,
    idx: usize,
) bool {
    const bit = rule.args[idx].deps;
    for (rule.args, 0..) |arg, other| {
        if (other == idx or arg.bound) continue;
        if (arg.deps & bit == 0) continue;
        if (bindings[other] != null) return false;
    }
    return true;
}

/// True when a generated slot's otherwise concrete target still carries a
/// witness meta threaded in from an enclosing open slot (e.g. `imp_intro`'s
/// premise `Γ , P ?t ⊢ ∀y P y` inside the child search for `ex_intro`'s
/// `Γ ⊢ P ?t → ∀y P y`). The concrete route cannot solve it — `hook.solve`
/// lifts only placeholder-free targets — so such a slot takes the open path,
/// where the meta can be bound at a leaf and read back to the slot that
/// minted it. Witness-mode rules only: the same ones that mint those metas.
fn carriesAncestorWitness(
    context: *const Context,
    candidate: *const ApplyCandidate,
    hook: *const GenerationHook,
    target: ExprId,
) bool {
    if (hook.solveOpenFn == null) return false;
    if (openMode(context, candidate.rule_id, hook.allow_constrained_mp) != .witness) return false;
    return candidate.theorem.containsMetaLeaf(target);
}

fn exactRuleCandidates(
    session: *session_mod.SearchSession,
    goal: Goal,
    theorem: *const TheoremContext,
    skip_abstract: bool,
    counters: ?*SearchCounters,
) ![]ApplyCandidate {
    const context = session.context;
    const allocator = context.allocator;
    const rule_ids = try session.candidateRuleIds(goal, theorem, true, counters);
    defer allocator.free(rule_ids);

    var list = std.ArrayListUnmanaged(ApplyCandidate).empty;
    errdefer {
        deinitApplyCandidateItems(list.items);
        list.deinit(allocator);
    }

    for (rule_ids) |rule_id| {
        if (skip_abstract and viewHasAbstract(context, rule_id)) continue;
        // Relation-transport rules (e.g. `mpbi`) match every goal backward but are
        // never a backward proof step. Unlike the `@abstract` screen above (which
        // is generation-only, via `skip_abstract`), this screen is unconditional —
        // a transport is useless backward on the direct `exact?` path too. See
        // `RewriteRegistry.isRelationTransport`.
        if (context.registry.isRelationTransport(context.env, rule_id)) continue;
        try seed.appendRuleCandidates(
            &list,
            allocator,
            context,
            goal,
            theorem,
            rule_id,
        );
    }
    if (counters) |actual| {
        actual.candidate_rules_before_conclusion_validation += list.items.len;
    }
    return try list.toOwnedSlice(allocator);
}

fn deinitApplyCandidates(
    allocator: std.mem.Allocator,
    candidates: []ApplyCandidate,
) void {
    deinitApplyCandidateItems(candidates);
    allocator.free(candidates);
}

fn deinitApplyCandidateItems(candidates: []ApplyCandidate) void {
    for (candidates) |*candidate| candidate.deinit();
}

/// One candidate's backtracking search: what `backtrackRefs` and the slot
/// generators share for the lifetime of one `enumerateCandidateRefs` call.
/// The slices are the search's mutable state (the rule bindings, a bindings
/// snapshot per depth, and the pool ref or generated sub-application chosen
/// for each slot); everything else is fixed for the candidate.
const AcceptedConclusion = struct {
    bindings: []?ExprId,
    valid: bool = false,
};

pub const SlotCtx = struct {
    compiler: *CompilerContext,
    context: *const Context,
    ref_index: *const ref_index_mod.Index,
    pool: []const refs_mod.RefPoolEntry,
    candidate: *ApplyCandidate,
    rule: *const RuleDecl,
    goal: Goal,
    theorem: *const TheoremContext,
    theorem_vars: *const NameExprMap,
    plans: []const HypPlan,
    bindings: []?ExprId,
    snapshots: []?ExprId,
    selected: []?usize,
    /// Parallel to `selected`: a generated inline sub-application chosen for
    /// a slot instead of a pool ref. Always `null` without a `generator`, so
    /// the pool-only `exact?` path is unaffected.
    generated: []?RuleApplication,
    generator: ?*const GenerationHook,
    derived: ?*DerivedPool,
    runtime: SearchRuntime,
    counters: ?*SearchCounters,
    fuel: ?*Fuel,
    candidates: *std.ArrayListUnmanaged(ExactCandidate),
    prune_setup: PruneSetup,
    /// The bindings `finalConclusionPlausible` last accepted. It reads
    /// nothing else that changes during this search, so the same bindings
    /// pass again without rerunning it.
    accepted_conclusion: *AcceptedConclusion,

    /// The bindings snapshot of search depth `depth`.
    pub fn snapshotAt(self: *const SlotCtx, depth: usize) []?ExprId {
        return self.snapshots[depth * self.bindings.len ..][0..self.bindings.len];
    }

    /// `finalConclusionPlausible` for the current bindings.
    pub fn conclusionPlausible(self: *const SlotCtx) bool {
        const accepted = self.accepted_conclusion;
        if (accepted.valid and std.mem.eql(?ExprId, accepted.bindings, self.bindings)) return true;
        if (!finalConclusionPlausible(
            self.context,
            self.candidate,
            self.goal,
            self.bindings,
            self.runtime,
            self.counters,
        )) return false;
        @memcpy(accepted.bindings, self.bindings);
        accepted.valid = true;
        return true;
    }

    /// Validate the fills chosen for every slot as one complete application.
    fn validate(self: *const SlotCtx) !void {
        if (!self.conclusionPlausible()) {
            if (self.counters) |actual| actual.final_conclusion_prunes += 1;
            return;
        }
        try validateSelectedRefs(
            self.compiler,
            self.context.allocator,
            self.context,
            self.pool,
            self.candidate,
            self.goal,
            self.theorem,
            self.theorem_vars,
            self.bindings,
            self.selected,
            self.generated,
            self.prune_setup.concl_has_rewrite_head,
            self.runtime,
            self.counters,
            self.fuel,
            self.candidates,
        );
    }

    /// Descend to the next slot with slot `position` filled by `application`.
    pub fn descendGenerated(
        self: *const SlotCtx,
        depth: usize,
        position: usize,
        application: RuleApplication,
    ) anyerror!void {
        self.generated[position] = application;
        defer self.generated[position] = null;
        try backtrackRefs(self, depth + 1);
    }
};

/// The hypothesis slot a generator fills: its search depth, its index into
/// `candidate.unresolved_hyps`, and the rule hypothesis it instantiates.
pub const Slot = struct {
    depth: usize,
    position: usize,
    hyp_index: usize,
};

fn enumerateCandidateRefs(
    compiler: *CompilerContext,
    context: *const Context,
    ref_index: *const ref_index_mod.Index,
    pool: []const refs_mod.RefPoolEntry,
    candidate: *ApplyCandidate,
    goal: Goal,
    theorem: *const TheoremContext,
    theorem_vars: *const NameExprMap,
    generator: ?*const GenerationHook,
    derived: ?*DerivedPool,
    runtime: SearchRuntime,
    counters: ?*SearchCounters,
    fuel: ?*Fuel,
    candidates: *std.ArrayListUnmanaged(ExactCandidate),
) !void {
    const allocator = context.allocator;
    const rule = &context.env.rules.items[candidate.rule_id];
    const hyp_count = candidate.unresolved_hyps.len;
    // A single slot needs no order, and the search's own lookup for it would
    // repeat the one planning does, so it is not planned.
    const single_plan = [1]HypPlan{.{
        .position = 0,
        .initial_len = 0,
        .seeded_len = 0,
        .strength = 0,
        .defer_generate = false,
        .defer_wildcard = false,
    }};
    const plans: []const HypPlan = switch (hyp_count) {
        0 => &.{},
        1 => &single_plan,
        else => try buildHypPlans(
            allocator,
            context,
            ref_index,
            candidate,
            generator != null,
            generator != null and generator.?.allow_constrained_mp,
            derived,
            counters,
        ),
    };
    defer if (hyp_count > 1) allocator.free(plans);
    // A hyp with no pool refs makes the candidate impossible for pool-only
    // search. With a generator (or a derived-ref pool) the slot may
    // instead be filled by a synthesized sub-proof, so don't prune then. A
    // single slot's own lookup makes the same check.
    if (hyp_count > 1 and generator == null and derived == null) {
        for (plans) |hyp_plan| {
            if (hyp_plan.initial_len == 0) return;
        }
    }

    const bindings = try allocator.dupe(?ExprId, candidate.bindings);
    defer allocator.free(bindings);
    const snapshots = try allocator.alloc(?ExprId, bindings.len * hyp_count);
    defer allocator.free(snapshots);
    const selected = try allocator.alloc(?usize, hyp_count);
    defer allocator.free(selected);
    @memset(selected, null);
    const generated = try allocator.alloc(?RuleApplication, hyp_count);
    defer allocator.free(generated);
    @memset(generated, null);
    var accepted_conclusion = AcceptedConclusion{
        .bindings = try allocator.alloc(?ExprId, bindings.len),
    };
    defer allocator.free(accepted_conclusion.bindings);

    const ctx = SlotCtx{
        .compiler = compiler,
        .context = context,
        .ref_index = ref_index,
        .pool = pool,
        .candidate = candidate,
        .rule = rule,
        .goal = goal,
        .theorem = theorem,
        .theorem_vars = theorem_vars,
        .plans = plans,
        .bindings = bindings,
        .snapshots = snapshots,
        .selected = selected,
        .generated = generated,
        .generator = generator,
        .derived = derived,
        .runtime = runtime,
        .counters = counters,
        .fuel = fuel,
        .candidates = candidates,
        .prune_setup = computePruneSetup(context, candidate.rule_id),
        .accepted_conclusion = &accepted_conclusion,
    };
    try backtrackRefs(&ctx, 0);
}

fn backtrackRefs(ctx: *const SlotCtx, depth: usize) anyerror!void {
    // Poll the call's budget at every node, not only where a candidate is
    // spent: the cheap prunes can reject every tuple of a large subtree.
    if (ctx.fuel) |fuel| if (fuel.global) |budget| try budget.check();
    if (depth == ctx.plans.len) {
        try ctx.validate();
        return;
    }

    const context = ctx.context;
    const candidate = ctx.candidate;
    const bindings = ctx.bindings;
    const counters = ctx.counters;
    const position = ctx.plans[depth].position;
    const hyp = candidate.unresolved_hyps[position];
    // Derived-pool participation for this slot. The cached unbound lookup
    // (`derivedSlotCandidates`) can prove no derived shape will ever fill
    // this (rule, hyp) slot — then the slot pays nothing further for the
    // derived pool for the lifetime of the search. Otherwise the slot's
    // shape query below runs against the pool index and the derived index
    // in one build (the dual lookup).
    var derived_index: ?*const ref_index_mod.Index = null;
    var derived_dead = false;
    if (ctx.derived) |dpool| {
        if (dpool.index != null) {
            if (try derivedSlotCandidates(
                context,
                dpool,
                candidate,
                hyp.index,
                counters,
            )) |cached| {
                if (cached.len == 0) derived_dead = true;
            }
            if (!derived_dead) derived_index = &dpool.index.?;
        }
    }
    var lookup = try lookupHypReferences(
        context,
        ctx.ref_index,
        derived_index,
        candidate,
        bindings,
        position,
        .dynamic,
        depth,
        true,
        counters,
    );
    defer lookup.deinit();
    // No pool ref fits this slot. With no generator and no derived refs that's
    // a dead branch (unchanged `exact?` behaviour); otherwise we still fall
    // through to try a derived ref or a synthesized sub-proof below.
    if (lookup.pool.indices.len == 0 and ctx.generator == null and ctx.derived == null) {
        return;
    }

    // Candidate-ref pruning setup, loop-invariant for this rule:
    //   * `@abstract` (Leibniz one-hole-context) prefilter — only views carrying
    //     an @abstract decl participate; fires on *all* search paths to cut the
    //     broad-slot ref flood, e.g. `eq_replace`'s bare-binder target hyp, whose
    //     view conclusion is a covering wildcard `finalConclusionPlausible` can't
    //     refute.
    //   * ACUI context-combination prefilter — any view with an ACUI context
    //     position participates, catching broad hypothesis-context floods the
    //     conclusion-side view refuter does not reach.
    const setup = ctx.prune_setup;
    const abstract_view = setup.abstract_view;
    const context_prune_info = setup.context_info;

    const snapshot = ctx.snapshotAt(depth);
    for (lookup.pool.indices) |pool_index| {
        switch (try matchOneHypWithSnapshot(
            ctx.context.allocator,
            context,
            &candidate.theorem,
            candidate.rule_id,
            hyp.index,
            ctx.ref_index.entries[pool_index].expr,
            bindings,
            snapshot,
            candidate.view_concl_seed,
            counters,
        )) {
            .matched => if (counters) |actual| {
                actual.hyp_match_syntactic += 1;
            },
            .mismatch => {
                if (counters) |actual| {
                    actual.hyp_match_definite_mismatch += 1;
                }
                continue;
            },
            .unknown => if (counters) |actual| {
                actual.hyp_match_unknown += 1;
            },
        }
        // On the `auto?` path (generator or derived pool present), check the
        // conclusion-vs-goal correspondence as soon as this fill pins its
        // binders: a contradiction dooms every tuple under it, and the
        // subtrees here are far bushier than under plain `exact?` (derived
        // fills, generation). The check is the same one
        // `validateSelectedRefs` applies at the end, so results are
        // unchanged; plain `exact?` keeps its existing flow untouched.
        if ((ctx.generator != null or ctx.derived != null) and !ctx.conclusionPlausible()) {
            if (counters) |actual| actual.final_conclusion_prunes += 1;
            rollbackOneHypMatch(bindings, snapshot);
            continue;
        }
        // `@abstract` necessary-condition prefilter: with this fill pinned, if no
        // one-hole context can explain the rule's declared (left, right) view
        // pair for the resolved plug pair, the tuple is doomed. Abstains unless
        // all four plug/side binders are syntactically determined, so it only
        // removes tuples the real derivation could never accept.
        if (abstract_view != null or context_prune_info != null) {
            var fill_buf: [32]abstract_prune.Fill = undefined;
            var fill_len: usize = 0;
            for (ctx.plans[0..depth]) |earlier| {
                const sel = ctx.selected[earlier.position] orelse continue;
                if (fill_len >= fill_buf.len) break;
                fill_buf[fill_len] = .{
                    .hyp_index = candidate.unresolved_hyps[earlier.position].index,
                    .ref_expr = ctx.ref_index.entries[sel].expr,
                };
                fill_len += 1;
            }
            if (fill_len < fill_buf.len) {
                fill_buf[fill_len] = .{
                    .hyp_index = hyp.index,
                    .ref_expr = ctx.ref_index.entries[pool_index].expr,
                };
                fill_len += 1;
            }
            const fills = fill_buf[0..fill_len];
            const goal_expr: ?ExprId = ctx.goal.concreteOrHint();
            if (abstract_view) |view| {
                if (abstract_prune.abstractInfeasible(
                    &candidate.theorem,
                    context,
                    view,
                    goal_expr,
                    fills,
                )) {
                    if (counters) |actual| actual.abstract_prunes += 1;
                    rollbackOneHypMatch(bindings, snapshot);
                    continue;
                }
            }
            if (context_prune_info) |info| {
                const context_bindings: ?[]const ?ExprId =
                    if (setup.context_uses_rule_bindings) bindings else null;
                if (context_prune.contextInfeasible(
                    &candidate.theorem,
                    context,
                    info,
                    goal_expr,
                    fills,
                    context_bindings,
                )) {
                    if (counters) |actual| actual.context_prunes += 1;
                    rollbackOneHypMatch(bindings, snapshot);
                    continue;
                }
            }
        }
        ctx.selected[position] = pool_index;
        try backtrackRefs(ctx, depth + 1);
        ctx.selected[position] = null;
        rollbackOneHypMatch(bindings, snapshot);
    }

    // Forward refs: after pool refs, try filling the slot with a
    // derived ref's materialized recipe (cheaper than recursive generation,
    // and the only way an open slot can absorb a deferred instantiation).
    if (ctx.derived) |dpool| {
        if (!derived_dead) try tryDerivedSlots(
            ctx,
            dpool,
            if (lookup.derived) |*dlookup| dlookup else null,
            .{ .depth = depth, .position = position, .hyp_index = hyp.index },
        );
    }

    // After pool refs, let the generation hook try to synthesize a
    // sub-proof for this slot. Only fires when a hook is present and the
    // hypothesis is already concrete given the current bindings (its binders
    // pinned by the conclusion or by sibling refs chosen above).
    if (ctx.generator) |hook| {
        try tryGenerateSlot(ctx, hook, .{
            .depth = depth,
            .position = position,
            .hyp_index = hyp.index,
        });
    }
}

/// Try each derived forward ref as a fill for hypothesis slot
/// `position`. The structural slot match binds the candidate rule's binders
/// against the derived ref's shape (universal metas riding along inside the
/// bound values); the candidate rule's own `@recover` laws then solve those
/// metas from their concrete sources (the use-time `@recover` solve). On
/// success the recipe is materialized with explicit bindings and spliced in
/// as a generated inline application; the meta assignments are rolled back
/// immediately, so the same derived ref can be selected again at a different
/// witness deeper in the assembly.
fn tryDerivedSlots(
    ctx: *const SlotCtx,
    dpool: *DerivedPool,
    derived_lookup: ?*const ref_index_mod.LookupResult,
    slot: Slot,
) anyerror!void {
    const context = ctx.context;
    const candidate = ctx.candidate;
    const bindings = ctx.bindings;
    const snapshot = ctx.snapshotAt(slot.depth);
    const goal_expr: ?ExprId = ctx.goal.concreteOrHint();
    // `derived_lookup` is the derived-index half of the slot's dual shape
    // lookup (binding-pinned, so it narrows as siblings pin binders); the
    // caller already skipped this call entirely when the cached unbound
    // lookup proved the slot can never take a derived fill. Without an index
    // (tests, failed build) every derived ref is attempted, as before.
    const slot_count = if (derived_lookup) |l| l.indices.len else dpool.refs.len;
    for (0..slot_count) |slot_idx| {
        const dref_idx = if (derived_lookup) |l| l.indices[slot_idx] else slot_idx;
        const dref = &dpool.refs[dref_idx];
        const mark = dpool.store.mark();
        const was_open = dpool.store.universal_use_open;
        dpool.store.openUniversalUse();
        defer dpool.store.universal_use_open = was_open;

        var ok = switch (try matchOneHypWithSnapshot(
            ctx.context.allocator,
            context,
            &candidate.theorem,
            candidate.rule_id,
            slot.hyp_index,
            dref.shape,
            bindings,
            snapshot,
            candidate.view_concl_seed,
            ctx.counters,
        )) {
            .matched, .unknown => true,
            .mismatch => false,
        };

        // Solve the derived ref's universal metas via the candidate rule's
        // `@recover` laws: the law's concrete source (goal-seeded or pinned by
        // an earlier sibling) shows the witness at every meta position of the
        // matched pattern.
        if (ok and dref.has_universal_meta) {
            if (context.views.get(candidate.rule_id)) |cview| {
                const view_bindings = try ctx.context.allocator.alloc(
                    ?ExprId,
                    cview.num_binders,
                );
                defer ctx.context.allocator.free(view_bindings);
                seedViewBindingsForMatch(
                    cview,
                    bindings,
                    candidate.view_concl_seed,
                    view_bindings,
                );
                for (cview.derived_bindings) |derived_binding| {
                    const rec = switch (derived_binding) {
                        .recover => |r| r,
                        .abstract => continue,
                    };
                    if (rec.source_view_idx >= view_bindings.len) continue;
                    if (rec.pattern_view_idx >= view_bindings.len) continue;
                    if (rec.hole_view_idx >= view_bindings.len) continue;
                    const source = view_bindings[rec.source_view_idx] orelse
                        continue;
                    const pattern = view_bindings[rec.pattern_view_idx] orelse
                        continue;
                    const hole = view_bindings[rec.hole_view_idx] orelse
                        continue;
                    if (forward.solveCorrespondence(
                        &dpool.store,
                        &candidate.theorem,
                        source,
                        pattern,
                        hole,
                    ) == .conflict) {
                        ok = false;
                        break;
                    }
                }
            }
        }

        var application: ?RuleApplication = null;
        if (ok) {
            // The matched rule bindings may hold meta-bearing shape fragments;
            // resolve them now so siblings and validation only ever see
            // concrete values (the matching-site invariant). Any binding left
            // with a live meta fails the branch.
            for (bindings) |*binding| {
                const value = binding.* orelse continue;
                const resolved = try dpool.store.deref(
                    &candidate.theorem,
                    value,
                );
                if (!dpool.store.isFullySolved(
                    &candidate.theorem,
                    resolved,
                )) {
                    ok = false;
                    break;
                }
                binding.* = resolved;
            }
            if (ok) {
                application = try forward.materializeApplication(
                    dpool,
                    context,
                    &candidate.theorem,
                    ctx.theorem_vars,
                    goal_expr,
                    dref,
                    bindings,
                );
            }
        }
        // Use-time discipline: assignments are transient; each use gets an
        // independent instantiation.
        dpool.store.rollbackTo(mark);

        if (application) |app| {
            // Same incremental prune as the pool-ref loop: a fill whose
            // pinned binders already contradict the conclusion-vs-goal
            // correspondence dooms every tuple under it.
            if (ctx.conclusionPlausible()) {
                try ctx.descendGenerated(slot.depth, slot.position, app);
            } else if (ctx.counters) |actual| {
                actual.final_conclusion_prunes += 1;
            }
        }
        rollbackOneHypMatch(bindings, snapshot);
    }
}

const derivedSlotCandidates = plan.derivedSlotCandidates;

/// Try to fill hypothesis slot `position` with a generated sub-application
/// rather than a pool ref. Computes the hypothesis's concrete expression from
/// the current bindings; if fully concrete, asks the hook to prove it, and on
/// success recurses with that slot generated.
pub fn tryGenerateSlot(
    ctx: *const SlotCtx,
    hook: *const GenerationHook,
    slot: Slot,
) anyerror!void {
    const context = ctx.context;
    const candidate = ctx.candidate;
    // A premise whose only open binders are bound variables (a def's hidden
    // binder, `pi_form`'s `x` under `A → B`) takes fresh ones. Once opened
    // that way it is not opened again below: the open path already ran the
    // child search on it.
    const fresh = try tryFreshBoundGenerate(ctx, hook, slot);
    if (fresh == .found) return;
    const opened = fresh == .opened;

    if (try OpenTerms.instantiateTemplateConcrete(
        &candidate.theorem,
        ctx.rule.hyps[slot.hyp_index],
        ctx.bindings,
    )) |raw_target| {
        if (carriesAncestorWitness(context, candidate, hook, raw_target)) {
            if (!opened) try tryOpenGenerateSlot(ctx, hook, slot, .{});
            return;
        }
        try emitGeneratedSlot(ctx, hook, slot, raw_target);
        return;
    }

    // The hypothesis context binder is still open. This is the multiplicative
    // case: a conclusion combining contexts under an ACUI combiner leaves a
    // split-half (`Γ`/`Δ`/`Σ`) unpinned because its subproof must be generated.
    // Speculatively distribute the goal context across the open binder and recurse
    // per candidate; the validator confirms each assembly.
    const candidates_before_split = ctx.candidates.items.len;
    const split_step = try trySplitGenerate(ctx, hook, slot);

    // Structured open backward generation. Strictly the
    // LAST fallback (concrete and ACUI split-generate both failed for this
    // slot). For an `@auto backward` rule this opens existential witnesses
    // (with the force-first / invention machinery). For any other rule it is
    // the *constrained backward modus ponens* path: a binder the goal does not
    // pin (e.g. `ax_mp`'s cut `a`) is opened as a meta, and the child search
    // closes that hypothesis with a rule whose conclusion *pins* the meta — no
    // existential is propagated or invented (the non-`@auto` branch of
    // `emitOpenTarget` is child-search-first with no var-pool fallback). If no
    // child conclusion determines the binder, the slot simply fails.
    //
    // Constrained MP skips a slot whose open binders the conclusion already
    // fixes up to an ACUI choice: the split and principal steps own those
    // choices. Opened here instead, such a binder leaves the child a bare
    // meta context or principal that every rule matches, and each of those
    // rules opens its own again. The skip holds only where those steps
    // enumerate: when either abstains (a cap, a placeholder member, several
    // unbound principals), the slot still opens, after them.
    if (ctx.candidates.items.len != candidates_before_split) return;
    const open_mode = openMode(context, candidate.rule_id, hook.allow_constrained_mp);
    const may_open = !opened and hook.solveOpenFn != null and open_mode != .none;
    const acui_owned = may_open and open_mode == .constrained and allOpenAcuiOwned(ctx, slot);
    if (may_open and !acui_owned) {
        try tryOpenGenerateSlot(ctx, hook, slot, .{});
        if (ctx.candidates.items.len != candidates_before_split) return;
    }

    // Final fallback: ACUI principal enumeration for the order-sensitive
    // principal-selection gap (e.g. `de_morgan`). Reached only when split and
    // open generation both produced nothing for this slot, so it is additive.
    const principal = try tryPrincipalEnumerate(ctx, hook, slot);
    if (acui_owned and ctx.candidates.items.len == candidates_before_split and
        (split_step == .abstained or principal == .abstained))
    {
        try tryOpenGenerateSlot(ctx, hook, slot, .{});
    }
}

/// What an ACUI step did with a slot: no site applied, it abstained on one,
/// or it enumerated the choices.
const AcuiStep = enum { none, abstained, enumerated };

/// Every open binder of the slot's premise is fixed by the conclusion up to
/// an ACUI choice: a spine binder of a conclusion split site, or a binder
/// inside one of its fixed summands. A rule with a `@view` opens the view's
/// premise, not the rule's, so it never qualifies.
fn allOpenAcuiOwned(ctx: *const SlotCtx, slot: Slot) bool {
    if (ctx.context.views.contains(ctx.candidate.rule_id)) return false;
    const goal_expr = ctx.goal.concreteOrHint() orelse return false;
    return premiseOpenAcuiOwned(
        ctx.context,
        &ctx.candidate.theorem,
        ctx.rule,
        slot.hyp_index,
        goal_expr,
        ctx.bindings,
    );
}

/// `allOpenAcuiOwned` for premise `hyp_index` of a rule without a view.
pub fn premiseOpenAcuiOwned(
    context: *const Context,
    theorem: *const TheoremContext,
    rule: *const RuleDecl,
    hyp_index: usize,
    goal_expr: ExprId,
    bindings: []const ?ExprId,
) bool {
    const hyp = templateBinderMask(rule.hyps[hyp_index]);
    const all = templateBinderMask(rule.concl);
    if (hyp.overflow or all.overflow) return false;
    var owned: u64 = 0;
    var m = all.mask;
    while (m != 0) {
        const idx: u6 = @intCast(@ctz(m));
        m &= m - 1;
        const site = split.findSplitSite(context, theorem, rule.concl, goal_expr, idx) orelse continue;
        for (site.spine[0..site.spine_len]) |sb| {
            if (sb < 64) owned |= @as(u64, 1) << @intCast(sb);
        }
        for (site.fixed[0..site.fixed_len]) |f| {
            const fm = templateBinderMask(f);
            if (!fm.overflow) owned |= fm.mask;
        }
    }
    var open: u64 = 0;
    m = hyp.mask;
    while (m != 0) {
        const idx: u6 = @intCast(@ctz(m));
        m &= m - 1;
        if (idx < bindings.len and bindings[idx] != null) continue;
        open |= @as(u64, 1) << idx;
    }
    return open != 0 and open & ~owned == 0;
}

/// Emit a single generated slot: canonicalize ACUI units out of the (now
/// concrete) sub-target, ask the hook to prove it, and recurse with the slot
/// filled. Canonicalizing the unit (`emp`) lets the sub-target match unit-free
/// pool refs — an `imp_intro` over an `emp ⊢ …` goal binds the context binder to
/// `emp`, leaving a redundant unit the strict `matchTemplate` would otherwise
/// reject (the validator absorbs it anyway).
pub fn emitGeneratedSlot(
    ctx: *const SlotCtx,
    hook: *const GenerationHook,
    slot: Slot,
    raw_target: ExprId,
) anyerror!void {
    const candidate = ctx.candidate;
    const reduced = try Redex.reduceRedexOnly(ctx.context, &candidate.theorem, raw_target);
    const target = try normalizeAcuiUnits(ctx.context, &candidate.theorem, reduced);
    // The application matched the goal and is launching a subgoal solve —
    // the signal that arms the `@auto eager` set-commit cut (consulted only
    // for eager candidates). An eager application is also exempt from the
    // depth budget: `eager_step` tells the driver to solve the child at the
    // parent's remaining depth.
    candidate.reached_child_solve = true;
    const eager_step = ctx.context.registry.eagerPriority(candidate.rule_id) != null;
    const proof = (try hook.solve(target, &candidate.theorem, eager_step)) orelse {
        return;
    };
    if (proof.conclusion != target) {
        return;
    }
    try ctx.descendGenerated(slot.depth, slot.position, proof.application);
}

/// Speculative ACUI split for a generate-only slot whose context binder is open.
/// Finds the first open binder of this hypothesis that the conclusion combines
/// under an ACUI head, enumerates concrete candidate contexts for it (distributing
/// the goal's members, minimal-first), and for each makes the slot concrete and
/// emits it. The binding is set only for the duration of each candidate's
/// recursion (so it pins the conclusion + later slots), then rolled back. Other
/// open binders are resolved as their own slots are reached.
fn trySplitGenerate(
    ctx: *const SlotCtx,
    hook: *const GenerationHook,
    slot: Slot,
) anyerror!AcuiStep {
    if (!hook.allow_split) return .none; // first (non-splitting) generation pass
    const context = ctx.context;
    const candidate = ctx.candidate;
    const bindings = ctx.bindings;
    const goal_expr = ctx.goal.concreteOrHint() orelse return .none;
    const hyp_template = ctx.rule.hyps[slot.hyp_index];
    const binders = templateBinderMask(hyp_template);
    if (binders.overflow) return .abstained;
    var step: AcuiStep = .none;

    var bits = binders.mask;
    while (bits != 0) {
        const b: usize = @ctz(bits);
        bits &= bits - 1;
        if (b < bindings.len and bindings[b] != null) continue; // already pinned
        const site = split.findSplitSite(
            context,
            &candidate.theorem,
            ctx.rule.concl,
            goal_expr,
            b,
        ) orelse continue;

        var enumerator = split.buildEnumerator(
            context,
            &candidate.theorem,
            site,
            bindings,
            b,
            // An eager rule never keeps its principal: the user declared it
            // invertible, so its premises without the principal are provable
            // whenever the goal is. Nor does a rule whose premise restates
            // the principal (`rex`): keeping it would only repeat it.
            hook.allow_retain_principal and
                context.registry.eagerPriority(candidate.rule_id) == null and
                !split.hypRestatesPrincipals(context, site, hyp_template, b),
        ) orelse {
            step = .abstained;
            continue;
        };

        var i: usize = 0;
        while (i < enumerator.count()) : (i += 1) {
            const cand = (try enumerator.candidate(
                context,
                &candidate.theorem,
                i,
            )) orelse continue;
            const saved = bindings[b];
            bindings[b] = cand;
            const handed = try handSplitChoice(candidate, b, cand);
            defer if (handed) |h| h.restore(candidate);
            if (!splitSiteBindingsPlausible(
                context,
                &candidate.theorem,
                site,
                bindings,
            )) {
                if (ctx.counters) |actual| {
                    actual.split_context_guard_rejects += 1;
                }
                bindings[b] = saved;
                continue;
            }
            const concrete_target = try OpenTerms.instantiateTemplateConcrete(
                &candidate.theorem,
                hyp_template,
                bindings,
            );
            if (concrete_target != null and
                !carriesAncestorWitness(context, candidate, hook, concrete_target.?))
            {
                try emitGeneratedSlot(ctx, hook, slot, concrete_target.?);
            } else if (hook.solveOpenFn != null and
                openMode(
                    context,
                    candidate.rule_id,
                    hook.allow_constrained_mp,
                ) == .witness)
            {
                // The split pinned this context binder, but
                // the hypothesis still has an open witness binder (e.g.
                // `union_intro`'s `G ⊢ x ∈ y` with `y` hypothesis-only), or
                // carries an enclosing slot's witness meta. Run the open path
                // under the split binding so the witness can be solved from
                // the now-concrete context's ACUI members.
                try tryOpenGenerateSlot(ctx, hook, slot, .{});
            }
            bindings[b] = saved;
        }
        // One open binder enumerated; sibling open binders are split at their own
        // slots, with this binder's choice now pinning their intervals.
        return .enumerated;
    }
    return step;
}

/// Final-fallback ACUI *principal* enumeration for a generate-only slot.
///
/// `trySplitGenerate` distributes a rule's open context-rest binder (`d`), but
/// can only remove a structured principal summand (`(¬a)` in `rnot`'s succedent
/// `(¬a), d`) from that distribution when the summand is already fully bound.
/// When the conclusion seed left the principal's binder unpinned — because two
/// or more goal members could equally be the principal and ACUI-aware seeding
/// refuses to commit to one positionally — neither the split nor the open path
/// pins it, so the premise never becomes concrete. This is the order-sensitive
/// principal-selection gap: e.g. `de_morgan`'s `¬(P c ∧ P d) ⊢ ¬P c, ¬P d`,
/// where either `¬P c` or `¬P d` may be the `rnot` principal, and only the
/// favoured position is ever tried.
///
/// Here we enumerate the choice: for each distinct goal member the unbound
/// principal summand structurally matches (binding the principal's binders),
/// pin it and re-enter `trySplitGenerate`, so the now-bound principal claims
/// that member and the open rest distributes the remainder. Reached only after
/// both the split and the open path produced nothing for this slot, and only
/// when 2+ members genuinely compete (a forced principal is left to the
/// positional path), so it is purely additive — theories that already generate
/// a candidate here are byte-identical.
fn tryPrincipalEnumerate(
    ctx: *const SlotCtx,
    hook: *const GenerationHook,
    slot: Slot,
) anyerror!AcuiStep {
    if (!hook.allow_split) return .none;
    const context = ctx.context;
    const candidate = ctx.candidate;
    const bindings = ctx.bindings;
    // Structural gate only, no enrollment requirement: everything below
    // enumerates concrete goal members for one unresolved structured
    // principal (no metas minted, ≥2 genuinely competing members), mirroring
    // seed-time `detectPrincipalFanout`, which is likewise
    // annotation-independent. The seed-time/generation-time pair differ by
    // *phase*, not by author permission.
    const goal_expr = ctx.goal.concreteOrHint() orelse return .none;
    const hyp_template = ctx.rule.hyps[slot.hyp_index];
    const hyp_binders = templateBinderMask(hyp_template);
    if (hyp_binders.overflow) return .abstained;

    // Locate the conclusion's ACUI split site that carries an *unbound*
    // structured principal summand (the additive rule's principal formula whose
    // binder the seed left open). A site whose principals are all already bound
    // is skipped so a rule combining several contexts doesn't mask a later site
    // that holds the real gap. Exactly one unbound principal is enumerated (the
    // common case); already-bound principals keep their value and their members
    // are claimed by the re-entered split. Several unbound principals are left
    // to a future extension rather than enumerated as a cross-product here.
    var ftmpl: ?TemplateExpr = null;
    var found_site: ?split.SplitSite = null;
    var skipped = false;
    var bits = hyp_binders.mask;
    site_search: while (bits != 0) {
        const b: usize = @ctz(bits);
        bits &= bits - 1;
        const s = split.findSplitSite(
            context,
            &candidate.theorem,
            ctx.rule.concl,
            goal_expr,
            b,
        ) orelse continue;
        var only_unbound: ?TemplateExpr = null;
        var f: usize = 0;
        while (f < s.fixed_len) : (f += 1) {
            if (split.templateFullyBound(s.fixed[f], bindings)) continue;
            if (only_unbound != null) {
                skipped = true; // >1 unbound: skip
                continue :site_search;
            }
            only_unbound = s.fixed[f];
        }
        if (only_unbound) |p| {
            ftmpl = p;
            found_site = s;
            break;
        }
    }
    const site = found_site orelse return if (skipped) .abstained else .none;
    const principal_template = ftmpl.?;

    const members = collectSplitMembers(
        context,
        &candidate.theorem,
        site.container,
        site.head_id,
    ) orelse return .abstained;

    const pmask = templateBinderMask(principal_template);
    if (pmask.overflow) return .abstained;

    // Only enumerate when 2+ distinct members genuinely compete for the
    // principal; a single match is forced and already handled positionally.
    const choices = acui.principalChoices(
        &candidate.theorem,
        principal_template,
        members.slice(),
        bindings,
    );
    // A single match is the forced case.
    if (choices.len < 2) return .none;

    for (choices.slice()) |member| {
        // Snapshot the principal's binder slots so a failed (or completed)
        // match rolls back cleanly before the next member is tried.
        var saved: [64]?ExprId = undefined;
        var pm = pmask.mask;
        while (pm != 0) {
            const idx: u6 = @intCast(@ctz(pm));
            pm &= pm - 1;
            if (idx < bindings.len) saved[idx] = bindings[idx];
        }
        const matched = OpenTerms.matchTemplateToTarget(
            &candidate.theorem,
            principal_template,
            member,
            bindings,
            .{},
        );
        if (matched) {
            // The binders this member just bound are the search's choice of
            // principal, as much as the split of the rest is.
            var handed: [64]?ExplicitFlag = @splat(null);
            defer for (handed) |maybe| if (maybe) |h| h.restore(candidate);
            pm = pmask.mask;
            while (pm != 0) {
                const idx: u6 = @intCast(@ctz(pm));
                pm &= pm - 1;
                if (idx < bindings.len and saved[idx] == null)
                    handed[idx] = try handSplitChoice(candidate, idx, bindings[idx]);
            }
            _ = try trySplitGenerate(ctx, hook, slot);
        }
        pm = pmask.mask;
        while (pm != 0) {
            const idx: u6 = @intCast(@ctz(pm));
            pm &= pm - 1;
            if (idx < bindings.len) bindings[idx] = saved[idx];
        }
    }
    return .enumerated;
}
