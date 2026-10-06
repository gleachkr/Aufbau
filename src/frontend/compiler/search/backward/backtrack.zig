const std = @import("std");
const types = @import("../types.zig");
const refs_mod = @import("../refs.zig");
const ref_index_mod = @import("../ref_index.zig");
const rank = @import("../rank.zig");
const def_match = @import("./def_match.zig");
const semantic = @import("./semantic.zig");
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
const PlaceholderId = @import("../../../expr.zig").PlaceholderId;
const TheoremContext = @import("../../../expr.zig").TheoremContext;
const RuleDecl = @import("../../../env.zig").RuleDecl;
const TemplateExpr = @import("../../../rules.zig").TemplateExpr;
const ArgInfo = @import("../../../parse_recovery.zig").ArgInfo;
const ProofScript = @import("../../../proof_script.zig");
const RuleApplication = ProofScript.RuleApplication;
const CompilerContext = @import("../../context.zig").CompilerContext;
const OpenTerms = @import("../../inference/open_terms.zig");
const Redex = @import("./redex.zig");
const MetaStoreMod = @import("../../inference/meta_store.zig");
const MetaStore = MetaStoreMod.MetaStore;
const BindingValidation = @import("../../../binding_validation.zig");
const PoolVars = @import("../../vars.zig").PoolVars;
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

    var candidates = std.ArrayListUnmanaged(ExactCandidate){};
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
    // untouched.
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
        std.sort.insertion(
            ApplyCandidate,
            apply_candidates,
            {},
            nonSplitCandidateFirst,
        );
    }

    const ref_index = try session.getRefIndex(theorem, counters);
    // `@auto eager` set-commit cut (generation path only, mirroring the sort
    // gate above — plain `exact?` never has an eager band). Once an eager
    // candidate has actually *applied* — reached a child solve or produced a
    // validated result — the remaining non-eager candidates are skipped: the
    // user declared the decomposition invertible, so if it fails, the goal
    // fails. All eager candidates (other bag members, other eager rules) are
    // still tried; the sort placed the band contiguously after class 0, so
    // the first non-eager candidate after arming ends the enumeration. A
    // mis-annotated (non-invertible) eager rule can therefore lose proofs;
    // the annotation is trusted. The eager *depth exemption* rides on
    // `emitGeneratedSlot`'s hook call, not on this cut. See
    // docs/design_notes/eager_rule_scheduling.md.
    const eager_cut = options.generator != null and
        context.registry.autoEagerRuleCount() > 0;
    var eager_armed = false;
    for (apply_candidates) |*apply_candidate| {
        apply_candidate.internal_child = options.internal_open_child;
        const is_eager = eager_cut and
            context.registry.eagerPriority(apply_candidate.rule_id) != null;
        if (eager_armed and !is_eager) break;
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
        try enumerateCandidateRefs(
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
            options.fuel,
            &candidates,
        );
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
    _: void,
    a: ApplyCandidate,
    b: ApplyCandidate,
) bool {
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
fn tryFreshBoundGenerate(
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

    var list = std.ArrayListUnmanaged(ApplyCandidate){};
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
const SlotCtx = struct {
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

    /// The bindings snapshot of search depth `depth`.
    fn snapshotAt(self: *const SlotCtx, depth: usize) []?ExprId {
        return self.snapshots[depth * self.bindings.len ..][0..self.bindings.len];
    }

    /// Validate the fills chosen for every slot as one complete application.
    fn validate(self: *const SlotCtx) !void {
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
    fn descendGenerated(
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
const Slot = struct {
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
    const plans: []const HypPlan = if (hyp_count == 0) &.{} else try buildHypPlans(
        allocator,
        context,
        ref_index,
        candidate,
        generator != null,
        generator != null and generator.?.allow_constrained_mp,
        derived,
        counters,
    );
    defer if (hyp_count != 0) allocator.free(plans);
    // A hyp with no pool refs makes the candidate impossible for pool-only
    // search. With a generator (or a derived-ref pool) the slot may
    // instead be filled by a synthesized sub-proof, so don't prune then.
    if (generator == null and derived == null) {
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
    };
    try backtrackRefs(&ctx, 0);
}

fn backtrackRefs(ctx: *const SlotCtx, depth: usize) anyerror!void {
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
        if ((ctx.generator != null or ctx.derived != null) and
            !finalConclusionPlausible(context, candidate, ctx.goal, bindings, ctx.runtime, counters))
        {
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
            if (finalConclusionPlausible(context, candidate, ctx.goal, bindings, ctx.runtime, ctx.counters)) {
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
fn tryGenerateSlot(
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
fn emitGeneratedSlot(
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
                !split.hypRestatesPrincipals(context, site, hyp_template),
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

/// State for one open-slot attempt, on top of the candidate's `SlotCtx`. The
/// open path recurses over bound-witness choices and recover/meta
/// construction layers, which all share it.
const OpenSlot = struct {
    ctx: *const SlotCtx,
    hook: *const GenerationHook,
    at: Slot,
    /// Branch-local existential store for this slot attempt. Mint marks are
    /// taken before each construction layer and rolled back beside the
    /// bindings snapshot (the meta-store rollback invariant).
    store: *MetaStore,
    /// Open policy for this candidate, computed once at slot entry.
    /// `.witness` gates the existential machinery (bound-binder meta
    /// deferral, ancestor-meta registration, the force-first ladder);
    /// `.constrained` keeps the child-search-first read-back discipline.
    mode: OpenMode,
    /// The slot's open binders are bound variables nothing outside the premise
    /// sees (`tryFreshBoundGenerate`): when the child search leaves one
    /// unsolved, it takes a fresh `@vars` variable (`tryPoolWitnesses`).
    fresh_bound: bool = false,
    /// Binders whose values hold metas `rebindHiddenVars` minted for this slot;
    /// a solved fill materializes them too.
    rebound: u64 = 0,

    /// The candidate is `@auto eager`: its open subgoal keeps the parent's
    /// remaining depth, as a concrete one does (`tryGenerateSlot`).
    fn eagerStep(self: *const OpenSlot) bool {
        return self.ctx.context.registry.eagerPriority(self.ctx.candidate.rule_id) != null;
    }
};

/// Structured open backward generation for one hypothesis
/// slot of an `@auto backward` rule. Builds an open target whose unsolved
/// leaves are existential metas — preferring the `@recover`-shaped surface
/// over raw template deferral — asks the hook to solve it with a generated
/// child proof, matches the child's concrete conclusion back against the
/// target to pin the parent's binders, and continues to the next sibling.
fn tryOpenGenerateSlot(
    ctx: *const SlotCtx,
    hook: *const GenerationHook,
    at: Slot,
    /// What opens as fresh bound variables (`tryFreshBoundGenerate`);
    /// empty for an ordinary open slot.
    fresh: FreshOpen,
) anyerror!void {
    const context = ctx.context;
    const candidate = ctx.candidate;
    const bindings = ctx.bindings;
    const fresh_bound = fresh.binders != 0 or fresh.hosts != 0;
    // Each `.bound_choice` meta the open path mints takes a dependency slot.
    // Candidates leave as proof text and the bindings roll back below, so
    // nothing holds those slots once the slot attempt is over: give them back
    // (this defer runs after the rollback).
    const slot_mark = candidate.theorem.depSlotMark();
    defer candidate.theorem.releaseUnheldDepSlots(slot_mark, &.{bindings});
    var store = MetaStore.init(ctx.context.allocator, context.env);
    // Share the driver's global meta-id counter so witness metas keep a stable
    // identity across the open-target recursion's interner clones.
    store.meta_id_counter = hook.meta_id_counter;
    store.dep_bans = hook.meta_dep_bans;
    // The pool-ref loop at this depth is done with its snapshot slice;
    // reuse it as the open path's bindings rollback point.
    const snapshot = ctx.snapshotAt(at.depth);
    @memcpy(snapshot, bindings);
    defer rollbackOneHypMatch(bindings, snapshot);
    const rebound = try rebindHiddenVars(&store, &candidate.theorem, bindings, fresh.binders | fresh.hosts);
    // Narrow the carried-meta dependency bans for this slot's lifetime: the
    // candidate's bindings are fixed for everything opened beneath it.
    const ban_mark = if (hook.meta_dep_bans) |bans| blk: {
        const mark = bans.mark();
        try banCarriedMetaDeps(ctx.rule, &candidate.theorem, bindings, bans);
        break :blk mark;
    } else 0;
    defer if (hook.meta_dep_bans) |bans| bans.rollback(ban_mark);
    defer {
        // Mirror this branch's meta activity into the bench counters
        // (META.md performance gates).
        if (ctx.counters) |c| {
            c.existential_metas_created += store.stats.existential_created;
            c.bound_choice_metas_created += store.stats.bound_choice_created;
            c.meta_assignments += store.stats.assignments;
            c.meta_rollbacks += store.stats.rollbacks;
        }
        store.deinit();
    }

    var slot = OpenSlot{
        .ctx = ctx,
        .hook = hook,
        .at = at,
        .store = &store,
        .mode = if (fresh_bound) .constrained else openMode(
            context,
            candidate.rule_id,
            hook.allow_constrained_mp,
        ),
        .fresh_bound = fresh_bound,
        .rebound = rebound,
    };
    if (context.views.get(candidate.rule_id)) |view| {
        try openSlotViaView(&slot, view);
    } else {
        try openSlotRaw(&slot);
    }
}

/// The parts of a premise `tryFreshBoundGenerate` opens as fresh bound
/// variables.
const FreshOpen = struct {
    /// Bound binders that open as metas.
    binders: u64 = 0,
    /// Binders whose values are terms over a def's hidden variable.
    hosts: u64 = 0,
};

/// Replace each hidden-variable leaf in the values of `hosts` with a
/// `.bound_choice` meta of `store`, in every binding that mentions it, so the
/// child search can name the variable and `tryPoolWitnesses` can fill it.
/// Two leaves stand for a def's hidden variable: an unfolded dummy, and a
/// seed meta (`ih` on an open binder, unmatched by any ref, or inside a kept
/// term such as `reflt`'s `t := λ x. x` under `T`). A hidden variable only
/// another premise's binders mention stays put: this slot's solve could not
/// fill it. Returns the binders whose values changed.
fn rebindHiddenVars(
    store: *MetaStore,
    theorem: *TheoremContext,
    bindings: []?ExprId,
    hosts: u64,
) !u64 {
    var changed: u64 = 0;
    var rest = hosts;
    while (rest != 0) {
        const idx: u6 = @intCast(@ctz(rest));
        rest &= rest - 1;
        while (bindings[idx]) |value| {
            const leaf = firstHiddenVarLeaf(theorem, value) orelse break;
            const pid = theorem.interner.node(leaf).placeholder;
            const info = theorem.placeholderInfo(pid) orelse break;
            const meta = try store.mintBoundVar(theorem, info.sort_name, info.deps, std.math.maxInt(u55));
            for (bindings, 0..) |*binding, other| {
                const other_value = binding.* orelse continue;
                const swapped = try forward.leafSwap(theorem, other_value, leaf, meta);
                if (swapped == other_value) continue;
                binding.* = swapped;
                if (other < 64) changed |= @as(u64, 1) << @intCast(other);
            }
        }
    }
    return changed;
}

/// True when a binding other than `bindings[idx]` mentions `leaf`.
fn heldElsewhere(theorem: *const TheoremContext, bindings: []const ?ExprId, idx: usize, leaf: ExprId) bool {
    for (bindings, 0..) |maybe, other| {
        if (other == idx) continue;
        const value = maybe orelse continue;
        if (theorem.exprAny(value, leaf, isExpr)) return true;
    }
    return false;
}

fn isExpr(target: ExprId, _: *const TheoremContext, expr: ExprId) bool {
    return expr == target;
}

fn isHiddenVarLeaf(_: void, theorem: *const TheoremContext, expr: ExprId) bool {
    const kind = theorem.leafPlaceholderKind(expr) orelse return false;
    return kind == .dummy or kind == .seed_meta;
}

fn firstHiddenVarLeaf(theorem: *const TheoremContext, expr: ExprId) ?ExprId {
    return switch (theorem.interner.node(expr).*) {
        .variable => null,
        .placeholder => if (isHiddenVarLeaf({}, theorem, expr)) expr else null,
        .app => |app| for (app.args) |arg| {
            if (firstHiddenVarLeaf(theorem, arg)) |leaf| break leaf;
        } else null,
    };
}

/// The eigenvariable condition, read off the rule's own dependency data: a
/// non-bound binder whose `ArgInfo.deps` omits bound arg `x` must not depend
/// on `x`'s value, so no meta inside it may be filled with anything
/// mentioning that value. Bans the value's dep bits on every such meta (by
/// stable `meta_id`, so the ban survives the child search's interner
/// clones); `MetaStore.registerAncestorMeta` turns the ban into the meta's
/// `allowed_deps`.
fn banCarriedMetaDeps(
    rule: *const RuleDecl,
    theorem: *const TheoremContext,
    bindings: []const ?ExprId,
    bans: *MetaStoreMod.MetaDepBans,
) !void {
    for (rule.args, 0..) |arg, idx| {
        if (arg.bound) continue;
        const value = bindings[idx] orelse continue;
        if (!theorem.containsMetaLeaf(value)) continue;
        const banned = bannedDeps(theorem, rule, bindings, idx);
        if (banned != 0) try banMetasIn(theorem, value, banned, bans);
    }
}

/// The dependency bits non-bound binder `idx` of `rule` must avoid, as the
/// checker's dependency condition reads them: those of the values of the bound
/// binders `idx`'s `ArgInfo.deps` omits.
fn bannedDeps(
    theorem: *const TheoremContext,
    rule: *const RuleDecl,
    bindings: []const ?ExprId,
    idx: usize,
) u55 {
    const deps = rule.args[idx].deps;
    var banned: u55 = 0;
    for (rule.args, 0..) |bound_arg, bound_idx| {
        if (!bound_arg.bound or deps & bound_arg.deps != 0) continue;
        const bound_value = bindings[bound_idx] orelse continue;
        banned |= (theorem.exprDeps(bound_value, .{}) catch 0);
    }
    return banned;
}

/// How a matched non-bound binder's value mentions the value of a bound arg
/// its `ArgInfo.deps` omits. Occurrences under a term with alpha rules don't
/// count (`@freshen` renames only through those). A meta leaf counts as no hit,
/// even a seed meta carrying a dep bit: an open meta may still be assigned
/// something that avoids the bound variable, so a partially open binding is
/// judged on its concrete part.
const DepHit = enum {
    none,
    /// Reached only through a head conversion can rewrite away: a def
    /// argument its body may drop, a `@rewrite` head, or an unavailable term.
    soft,
    /// Reached along heads no conversion removes (`argSurvivesConversion`).
    /// ACUI combiners count: rearrangement never drops a member (idempotence
    /// keeps a copy, and the unit mentions nothing).
    rigid,
};

/// The strongest `DepHit` over the rule's non-bound binders, as matched.
fn bindingsDepHit(
    context: *const Context,
    theorem: *const TheoremContext,
    rule: *const RuleDecl,
    bindings: []const ?ExprId,
) DepHit {
    var result: DepHit = .none;
    for (rule.args, 0..) |arg, idx| {
        if (arg.bound) continue;
        const value = bindings[idx] orelse continue;
        const banned = bannedDeps(theorem, rule, bindings, idx);
        if (banned == 0) continue;
        const hit = exprDepHit(context, theorem, value, banned);
        if (@intFromEnum(hit) > @intFromEnum(result)) result = hit;
        if (result == .rigid) break;
    }
    return result;
}

fn exprDepHit(
    context: *const Context,
    theorem: *const TheoremContext,
    expr: ExprId,
    banned: u55,
) DepHit {
    return switch (theorem.interner.node(expr).*) {
        .placeholder => .none,
        .variable => blk: {
            const info = (theorem.currentLeafInfo(expr) catch null) orelse break :blk .none;
            break :blk if (info.deps & banned != 0) .rigid else .none;
        },
        .app => |app| blk: {
            if (context.registry.getAlphaRules(app.term_id).len != 0) break :blk .none;
            var result: DepHit = .none;
            for (app.args, 0..) |arg, i| {
                var hit = exprDepHit(context, theorem, arg, banned);
                if (hit == .rigid and !argSurvivesConversion(context, app.term_id, i)) hit = .soft;
                if (@intFromEnum(hit) > @intFromEnum(result)) result = hit;
                if (result == .rigid) break;
            }
            break :blk result;
        },
    };
}

/// No checker conversion can remove argument `arg_idx` of a `term_id` app: the
/// head is rigid, an ACUI combiner (rearrangement never drops a member), or a
/// def whose body keeps the argument along determining heads
/// (`semantic.argDetermined`). Alpha-rule heads are screened by the caller.
fn argSurvivesConversion(context: *const Context, term_id: u32, arg_idx: usize) bool {
    return switch (semantic.headClass(context, term_id)) {
        .rigid, .acui => true,
        .def => semantic.argDetermined(context, term_id, arg_idx),
        .rewrite, .unavailable => false,
    };
}

/// A view, `@fresh`, or `@freshen` can re-choose a bound binder after the
/// conclusion match, so a dependency hit as matched is not decisive.
fn ruleMayRechooseBound(context: *const Context, rule_id: u32) bool {
    return context.views.contains(rule_id) or
        context.fresh_bindings.contains(rule_id) or
        context.freshen_bindings.contains(rule_id);
}

fn banMetasIn(
    theorem: *const TheoremContext,
    expr: ExprId,
    banned: u55,
    bans: *MetaStoreMod.MetaDepBans,
) !void {
    switch (theorem.interner.node(expr).*) {
        .variable => {},
        .placeholder => |pid| {
            const info = theorem.placeholderInfo(pid) orelse return;
            if (info.meta_id) |meta_id| try bans.ban(meta_id, banned);
        },
        .app => |app| for (app.args) |arg| try banMetasIn(theorem, arg, banned, bans),
    }
}

/// Open path for a rule without a `@view`: enumerate witnesses for open
/// bound-class binders, defer the remaining open binders as existential
/// metas, and emit the structured target.
fn openSlotRaw(slot: *OpenSlot) anyerror!void {
    const template = slot.ctx.rule.hyps[slot.at.hyp_index];
    // See `openSlotView`: open bound binders defer to the existential-meta path
    // (carry-to-leaf) rather than enumerating a concrete witness pool.
    const unknowns = try slot.ctx.context.allocator.alloc(?ExprId, slot.ctx.bindings.len);
    defer slot.ctx.context.allocator.free(unknowns);
    @memset(unknowns, null);
    var options = OpenTerms.OpenInstantiateOptions{
        .factory = .{
            .context = slot.store,
            .kind = .existential,
            .makeFn = mintStoreMeta,
        },
        .logical_unknowns = unknowns,
        .excluded = null,
        .conclusion_binders = conclusionBinderMaskOrNone(slot.ctx.rule.concl),
        .open_bound_in_combiner = slot.mode != .witness,
        .arg_infos = slot.ctx.rule.args,
    };
    const mark = slot.store.mark();
    defer slot.store.rollbackTo(mark);
    // A bound binder opens as a variable with its own dependency bit; with
    // the theorem's bits spent, the slot cannot open.
    const target = (OpenTerms.instantiateTemplateOpen(
        &slot.ctx.candidate.theorem,
        slot.ctx.context.env,
        slot.ctx.context.registry,
        template,
        slot.ctx.bindings,
        &options,
    ) catch |err| switch (err) {
        error.DependencySlotExhausted => return,
        else => return err,
    }) orelse return;
    try emitOpenTarget(slot, target, unknowns, null, null);
}

/// Open path for a rule with a `@view`: the open target is the *view*
/// hypothesis surface. `@recover` laws whose pattern/hole are pinned defer
/// their witness as one existential meta and build the source surface by the
/// leaf swap (`φ[x ↦ ?t]` instead of the raw `sb`-headed template);
/// a law that cannot fire owns its binders exclusively (no bare-meta
/// fallback for them).
fn openSlotViaView(slot: *OpenSlot, view: types.ViewDecl) anyerror!void {
    if (slot.at.hyp_index >= view.hyps.len) return;
    const theorem = &slot.ctx.candidate.theorem;
    const view_bindings = try slot.ctx.context.allocator.alloc(?ExprId, view.num_binders);
    defer slot.ctx.context.allocator.free(view_bindings);
    seedViewBindingsForMatch(
        view,
        slot.ctx.bindings,
        slot.ctx.candidate.view_concl_seed,
        view_bindings,
    );

    const excluded = try slot.ctx.context.allocator.alloc(bool, view.num_binders);
    defer slot.ctx.context.allocator.free(excluded);
    @memset(excluded, false);

    const mark = slot.store.mark();
    defer slot.store.rollbackTo(mark);

    for (view.derived_bindings) |derived_binding| {
        const rec = switch (derived_binding) {
            .recover => |r| r,
            .abstract => continue,
        };
        if (rec.target_view_idx >= view_bindings.len) continue;
        if (rec.source_view_idx >= view_bindings.len) continue;
        if (rec.pattern_view_idx >= view_bindings.len) continue;
        if (rec.hole_view_idx >= view_bindings.len) continue;
        if (view_bindings[rec.target_view_idx] != null) continue;
        if (view_bindings[rec.source_view_idx] != null) continue;
        const fired = blk: {
            const pattern = view_bindings[rec.pattern_view_idx] orelse
                break :blk false;
            const hole = view_bindings[rec.hole_view_idx] orelse
                break :blk false;
            if (view.arg_infos[rec.target_view_idx].bound) break :blk false;
            const meta = try slot.store.mint(
                theorem,
                view.arg_infos[rec.target_view_idx].sort_name,
                std.math.maxInt(u55),
                .existential,
            );
            view_bindings[rec.target_view_idx] = meta;
            view_bindings[rec.source_view_idx] = try forward.leafSwap(
                theorem,
                pattern,
                hole,
                meta,
            );
            break :blk true;
        };
        if (!fired) {
            // Recover-owned exclusion: the rule derives nothing for these
            // binders in this branch — never fall back to bare-meta deferral.
            excluded[rec.target_view_idx] = true;
            excluded[rec.source_view_idx] = true;
        }
    }

    // All open binders — including the principal quantifier's bound variable —
    // defer to the existential-meta path and are pinned to a concrete variable
    // at the leaf (carry-to-leaf). Earlier code enumerated bound binders over a
    // `@vars` witness pool here; that proved to be dead weight (the meta path
    // subsumes it: corpus byte-identical with the enumeration removed) and a
    // smell (it fired `rex`/`lall` even on purely propositional goals).
    try instantiateAndEmitView(slot, view, view_bindings, excluded);
}

/// Defer the remaining open view binders of the slot's hypothesis as
/// existential metas, instantiate the view surface, and emit it.
fn instantiateAndEmitView(
    slot: *OpenSlot,
    view: types.ViewDecl,
    view_bindings: []?ExprId,
    excluded: []const bool,
) anyerror!void {
    const unknowns = try slot.ctx.context.allocator.alloc(?ExprId, view.num_binders);
    defer slot.ctx.context.allocator.free(unknowns);
    @memset(unknowns, null);
    var options = OpenTerms.OpenInstantiateOptions{
        .factory = .{
            .context = slot.store,
            .kind = .existential,
            .makeFn = mintStoreMeta,
        },
        .logical_unknowns = unknowns,
        .excluded = excluded,
        .conclusion_binders = conclusionBinderMaskOrNone(view.concl),
        .open_bound_in_combiner = slot.mode != .witness,
        .arg_infos = view.arg_infos,
    };
    const mark = slot.store.mark();
    defer slot.store.rollbackTo(mark);
    // A bound binder opens as a variable with its own dependency bit; with
    // the theorem's bits spent, the slot cannot open.
    const target = (OpenTerms.instantiateTemplateOpen(
        &slot.ctx.candidate.theorem,
        slot.ctx.context.env,
        slot.ctx.context.registry,
        view.hyps[slot.at.hyp_index],
        view_bindings,
        &options,
    ) catch |err| switch (err) {
        error.DependencySlotExhausted => return,
        else => return err,
    }) orelse return;

    // Overlay the freshly minted per-binder metas into a local copy of the
    // view bindings so the match-back materialization covers them.
    const effective = try slot.ctx.context.allocator.dupe(?ExprId, view_bindings);
    defer slot.ctx.context.allocator.free(effective);
    for (unknowns, 0..) |maybe_meta, vi| {
        if (maybe_meta) |meta| {
            if (effective[vi] == null) effective[vi] = meta;
        }
    }
    try emitOpenTarget(slot, target, unknowns, view, effective);
}

/// Emit one structured open target: route fully concrete targets through the
/// ordinary concrete generated-slot path; otherwise enforce the rigid-root
/// (absorber) guard, let the hook solve the target, pin the parent's binders
/// from the solved metas, and continue the backtrack at the next sibling.
fn emitOpenTarget(
    slot: *OpenSlot,
    raw_target_in: ExprId,
    unknowns: []const ?ExprId,
    view: ?types.ViewDecl,
    view_bindings: ?[]?ExprId,
) anyerror!void {
    const theorem = &slot.ctx.candidate.theorem;
    // Canonicalize ACUI units away before the recursive solve and readback.
    // An open target can carry a redundant `emp` (e.g. a witness rule whose
    // context binder `g` is the unit, so its hypothesis instantiates to
    // `emp , (∀ x p) , [x/t]p ⊢ d`). The child's accepted conclusion comes
    // back unit-free, so without this the readback `solveCorrespondence` cannot
    // align the ACUI members to bind the carried ancestor witness. Meta leaves
    // survive normalization unchanged, so the open binders stay intact. The
    // concrete generated path already normalizes (see `tryGenerateSlot`).
    const reduced_target = try Redex.reduceRedexOnly(slot.ctx.context, theorem, raw_target_in);
    const raw_target = try normalizeAcuiUnits(slot.ctx.context, theorem, reduced_target);
    // Register the witness metas threaded in from enclosing open slots before
    // anything reads the store: an unregistered ancestor leaf counts as
    // solved, which would send a target carrying one down the concrete route
    // below, where `hook.solve` cannot lift a placeholder and drops it. Also
    // before the rollback mark, so the registration survives the per-pass
    // rollbacks: every pass (concrete-member, child `solveOpen`, coupled)
    // needs the ancestor leaves bindable, and `solveOpen`'s hint reintern
    // bails outright on an unregistered meta. Registration is trailed and
    // unwound by `tryOpenGenerateSlot`'s outer mark, so it does not leak past
    // this slot. Only `.witness` open slots carry witness metas, except under
    // an open root (`hook.open_root`): there a constrained slot carries its
    // ancestors' metas too, the root's hole metas and those minted between.
    if (slot.mode == .witness or (slot.mode == .constrained and slot.hook.open_root)) {
        try registerAncestorMetas(slot.store, theorem, raw_target);
    }
    if (slot.store.isFullySolved(theorem, raw_target)) {
        // A meta the bindings still hold but the target no longer mentions
        // dangles: a fresh variable the premise substitutes away
        // (`nat_ind_elim`'s base case `g ⊢ z : [k/zero] C` still holds `k`
        // in `C`), or an erased witness (`PoolPick.dangling`). No proof of
        // the premise can determine it, so the concrete route below could
        // only send the branch to validation with it undeterminable. It takes
        // a `@vars` name now instead, and the solved-target pinning path
        // renders the explicit binding the validator requires.
        if (slot.fresh_bound and
            try tryPoolWitnesses(slot, raw_target, unknowns, view, view_bindings, .fresh)) return;
        if (slot.mode == .witness and slot.hook.allow_invent_witness and
            try tryPoolWitnesses(slot, raw_target, unknowns, view, view_bindings, .dangling)) return;
        // Bound-witness enumeration closed every open binder: this is an
        // ordinary concrete generated slot (for view rules, a concrete
        // view-surface target the validator reconciles through the view
        // machinery).
        try emitGeneratedSlot(slot.ctx, slot.hook, slot.at, raw_target);
        return;
    }
    // Steps 4–5: reject bare-meta targets and targets with no rigid root (the
    // forward absorber check, reused as the "no useful concrete shape"
    // first line). Erring on the forced side: a target this open would make
    // child search guessing, not deduction.
    switch (theorem.interner.node(raw_target).*) {
        .app => {},
        .variable, .placeholder => return,
    }

    const candidates_before = slot.ctx.candidates.items.len;
    const mark = slot.store.mark();

    // Force-first is a *witness-rule* optimization: only a `.witness` open
    // slot defers a witness that a leaf must force. Gate on that so
    // witness-free `.constrained` open generation (notably `@abstract` motive
    // inference, which has no `@auto` rule but still mints open metas) keeps
    // its original child-search-first ordering untouched.
    if (slot.mode == .witness) {
        // Witness migration: FORCE the carried witness by the cheap,
        // deterministic concrete-member pass first (e.g. an `ax` leaf whose
        // `[x/t]p` instance must equal a concrete succedent member uniquely
        // determines `t`). Pinning the witness from a member identity here —
        // rather than enumerating candidate witnesses in the child search and
        // reading one back — collapses the per-level `open_child_max_results`
        // fan that otherwise compounds through nested open targets. The
        // expensive O(n²) coupled pass is left last (`try_coupled = false`).
        // Every emitted fill is still revalidated by `tryCandidate`.
        try tryAcuiMemberWitnesses(slot, raw_target, unknowns, view, view_bindings, false);
        if (slot.ctx.candidates.items.len != candidates_before) return;
        slot.store.rollbackTo(mark);
        try solveOpenTargetByChild(slot, raw_target, unknowns, view, view_bindings);
        if (slot.ctx.candidates.items.len != candidates_before) return;
        slot.store.rollbackTo(mark);
        try tryCoupledWitnesses(slot, raw_target, unknowns, view, view_bindings);
        if (slot.ctx.candidates.items.len != candidates_before) return;
        // Last resort: the witness is genuinely free — invent it from the
        // `@vars` pool. The flag is set whenever the theory has a pool; the
        // forced passes above stay the default because they run first and
        // this rung is reached only when they leave metas unsolved.
        if (slot.hook.allow_invent_witness) {
            slot.store.rollbackTo(mark);
            _ = try tryPoolWitnesses(slot, raw_target, unknowns, view, view_bindings, .shared);
        }
        return;
    }

    // Witness-free open target (e.g. `@abstract` motive inference): keep the
    // original child-search-first ordering, with member/coupled witness
    // enumeration as the fallback.
    try solveOpenTargetByChild(slot, raw_target, unknowns, view, view_bindings);
    if (slot.ctx.candidates.items.len != candidates_before) return;
    slot.store.rollbackTo(mark);
    try tryAcuiMemberWitnesses(slot, raw_target, unknowns, view, view_bindings, true);
    if (slot.ctx.candidates.items.len != candidates_before) return;
    // No proof below fixed the variable (`weaken` only echoes it back), so
    // any fresh one will do.
    if (slot.fresh_bound) {
        slot.store.rollbackTo(mark);
        _ = try tryPoolWitnesses(slot, raw_target, unknowns, view, view_bindings, .fresh);
    }
}

/// Solve an open target by child search (`GenerationHook.solveOpen`),
/// continuing the slot from each child proof in turn until one continuation
/// emits a candidate.
fn solveOpenTargetByChild(
    slot: *OpenSlot,
    raw_target: ExprId,
    unknowns: []const ?ExprId,
    view: ?types.ViewDecl,
    view_bindings: ?[]const ?ExprId,
) anyerror!void {
    const Continuation = struct {
        slot: *OpenSlot,
        raw_target: ExprId,
        unknowns: []const ?ExprId,
        view: ?types.ViewDecl,
        view_bindings: ?[]const ?ExprId,
        candidates_before: usize,

        fn accept(ctx: *anyopaque, proof: types.GeneratedProof) anyerror!bool {
            const self: *@This() = @ptrCast(@alignCast(ctx));
            try continueOpenTargetSolved(
                self.slot,
                self.raw_target,
                self.unknowns,
                self.view,
                self.view_bindings,
                proof,
            );
            return self.slot.ctx.candidates.items.len != self.candidates_before;
        }
    };
    var continuation = Continuation{
        .slot = slot,
        .raw_target = raw_target,
        .unknowns = unknowns,
        .view = view,
        .view_bindings = view_bindings,
        .candidates_before = slot.ctx.candidates.items.len,
    };
    try slot.hook.solveOpen(
        raw_target,
        &slot.ctx.candidate.theorem,
        slot.store,
        slot.eagerStep(),
        .{ .ctx = &continuation, .acceptFn = Continuation.accept },
    );
}

/// Continue a structured open slot whose metas are all solved in the store:
/// pin the parent's binders from the solved metas, prune, flag the binders
/// for explicit-binding rendering, and resume the backtrack. With `proof`
/// set this is the open-hook success path (the child's accepted conclusion
/// must equal the materialized target); with `proof == null` (the
/// member-witness path) the now-concrete target is routed through the
/// ordinary concrete generation pipeline instead.
fn continueOpenTargetSolved(
    slot: *OpenSlot,
    raw_target: ExprId,
    unknowns: []const ?ExprId,
    view: ?types.ViewDecl,
    view_bindings: ?[]const ?ExprId,
    proof: ?types.GeneratedProof,
) anyerror!void {
    const theorem = &slot.ctx.candidate.theorem;
    // The metas the target mentions must all be solved; the materialized
    // target is the concrete hypothesis this branch commits to.
    const concrete_target = slot.store.materialize(theorem, raw_target) catch {
        return;
    };
    if (proof) |p| {
        if (concrete_target != p.conclusion) return;
    }

    // Pin parent binders from the solved metas, remembering exactly which
    // binders this fill set (and their prior value) so they roll back with the
    // branch and render as explicit bindings on the final application.
    const Flag = struct { idx: usize, orig: ?ExprId };
    var flagged = std.ArrayListUnmanaged(Flag){};
    defer flagged.deinit(slot.ctx.context.allocator);
    var solve_failed = false;
    if (view) |v| {
        const vb = try slot.ctx.context.allocator.dupe(?ExprId, view_bindings.?);
        defer slot.ctx.context.allocator.free(vb);
        for (vb) |*entry| {
            const value = entry.* orelse continue;
            // A view binder whose meta is still unsolved is left unpinned (the
            // binder_map loop skips null and `tryCandidate` infers it from the
            // goal). On the member/coupled witness paths every binding is
            // already solved, so this is inert there; only the invented-witness
            // path reaches here with an open context binder (e.g. `g`/`d`) that
            // never appeared in the now-concrete `raw_target`.
            entry.* = slot.store.materialize(theorem, value) catch null;
        }
        for (v.binder_map, 0..) |maybe_rule_idx, vi| {
            const rule_idx = maybe_rule_idx orelse continue;
            if (rule_idx >= slot.ctx.bindings.len) continue;
            if (slot.ctx.bindings[rule_idx] != null) continue;
            const value = vb[vi] orelse continue;
            slot.ctx.bindings[rule_idx] = value;
            try flagged.append(slot.ctx.context.allocator, .{ .idx = rule_idx, .orig = null });
        }
    } else {
        for (unknowns, 0..) |maybe_meta, idx| {
            const meta = maybe_meta orelse continue;
            const value = slot.store.materialize(theorem, meta) catch {
                solve_failed = true;
                break;
            };
            if (slot.ctx.bindings[idx] == null) {
                slot.ctx.bindings[idx] = value;
                try flagged.append(slot.ctx.context.allocator, .{ .idx = idx, .orig = null });
            }
        }
    }
    // Carry-to-leaf: a binder whose value mentions an ancestor witness meta
    // that just got solved at this leaf must be re-materialized and rendered
    // explicitly, so its now-concrete value reaches the slot that minted the
    // meta (via the conclusion of the assembled child proof). Inert unless an
    // ancestor meta is present (only the cross-boundary generation path).
    var coupled = false;
    if (!solve_failed) {
        for (slot.ctx.bindings, 0..) |maybe_val, idx| {
            const val = maybe_val orelse continue;
            var already = false;
            for (flagged.items) |f| {
                if (f.idx == idx) {
                    already = true;
                    break;
                }
            }
            if (already) continue;
            const rebound = idx < 64 and slot.rebound & (@as(u64, 1) << @intCast(idx)) != 0;
            if (!rebound and !slot.store.exprMentionsAncestor(theorem, val)) continue;
            // A value still holding an unsolved meta is not this leaf's to
            // fill (another slot's witness): it stays unrendered, for the
            // checker to infer.
            const concrete = slot.store.materialize(theorem, val) catch continue;
            if (concrete == val) continue;
            slot.ctx.bindings[idx] = concrete;
            try flagged.append(slot.ctx.context.allocator, .{ .idx = idx, .orig = val });
            coupled = true;
        }
    }
    // Carry-to-leaf only: this slot is being validated against a holey
    // (implicit-whole-conclusion) goal — the open-generation child has no
    // concrete conclusion to infer the rule's conclusion-pinned binders from,
    // so `tryCandidate`'s binder inference leaves them null
    // (`MissingBinderAssignment`). Because the coupled solve has already pinned
    // *every* binder in the search, render them all as explicit bindings so the
    // holey-goal validation needs no inference. Gated on `coupled` (an ancestor
    // witness flowed back here) so the single-witness path — used by the
    // byte-identical broad corpus — is untouched.
    if (coupled) {
        for (slot.ctx.bindings, 0..) |maybe_val, idx| {
            const val = maybe_val orelse continue;
            var already = false;
            for (flagged.items) |f| {
                if (f.idx == idx) {
                    already = true;
                    break;
                }
            }
            if (already) continue;
            try flagged.append(slot.ctx.context.allocator, .{ .idx = idx, .orig = val });
        }
    }
    defer for (flagged.items) |f| {
        slot.ctx.bindings[f.idx] = f.orig;
    };
    if (solve_failed) return;

    // Same incremental prune as the pool-ref loop: a fill whose pinned
    // binders contradict the conclusion-vs-goal correspondence dooms every
    // tuple under it.
    if (!finalConclusionPlausible(slot.ctx.context, slot.ctx.candidate, slot.ctx.goal, slot.ctx.bindings, slot.ctx.runtime, slot.ctx.counters)) {
        if (slot.ctx.counters) |c| c.final_conclusion_prunes += 1;
        return;
    }

    const explicit = try slot.ctx.context.allocator.alloc(ExplicitFlag, flagged.items.len);
    defer slot.ctx.context.allocator.free(explicit);
    for (flagged.items, explicit) |f, *e| e.* = try setExplicitFlag(slot.ctx.candidate, f.idx);
    defer for (explicit) |e| e.restore(slot.ctx.candidate);

    if (proof) |p| {
        try slot.ctx.descendGenerated(slot.at.depth, slot.at.position, p.application);
        return;
    }
    try emitGeneratedSlot(slot.ctx, slot.hook, slot.at, concrete_target);
}

/// Cap on member-witness fills attempted per open slot. The domain is the
/// target's own concrete ACUI members, so this is small in practice; the cap
/// is a hard brake on pathological member × fragment products.
const max_member_witness_attempts: usize = 8;

/// ACUI finite-domain witness enumeration. The open
/// target's own ACUI regions hold concrete members (`A ∈ A ⊢ ?t ∈ A` —
/// the context member shows the witness `?t := A`); matching each
/// meta-bearing fragment of the target against each member proposes
/// assignments by the same structural correspondence the open hook uses.
/// Only fills that solve the target completely are pursued (the concrete
/// target then runs the ordinary generation pipeline, and `tryCandidate`
/// still validates the whole assembly); partial fills are rolled back.
/// Concrete members come first by construction — metas never enter the
/// domain — and each distinct fill is attempted once.
fn tryAcuiMemberWitnesses(
    slot: *OpenSlot,
    raw_target: ExprId,
    unknowns: []const ?ExprId,
    view: ?types.ViewDecl,
    view_bindings: ?[]const ?ExprId,
    try_coupled: bool,
) anyerror!void {
    const theorem = &slot.ctx.candidate.theorem;

    // Collect meta fragments first and bail before the (more expensive) domain
    // member walk when the target has none — the common case for open targets
    // that carry no witness meta (e.g. `@abstract` motive slots), so they pay
    // almost nothing for this now-first pass.
    var fragments: [Witness.max_fragments]ExprId = undefined;
    const fragment_count = Witness.collectMetaFragments(
        theorem,
        slot.store,
        raw_target,
        &fragments,
    );
    if (fragment_count == 0) return;
    var members: [Witness.max_domain_members]ExprId = undefined;
    const member_count = Witness.collectDomainMembers(
        slot.ctx.context,
        theorem,
        raw_target,
        &members,
    );

    // Distinct materialized targets already attempted: two members often
    // propose the same fill (shared subterms), and one child solve per
    // distinct fill is enough.
    var seen: [max_member_witness_attempts]ExprId = undefined;
    var attempts: usize = 0;
    const before_concrete = slot.ctx.candidates.items.len;
    for (members[0..member_count]) |member| {
        for (fragments[0..fragment_count]) |fragment| {
            if (attempts >= max_member_witness_attempts) break;
            const mark = slot.store.mark();
            if (!Witness.matchFragmentToMember(
                slot.ctx.context,
                slot.store,
                theorem,
                fragment,
                member,
            )) continue;
            try pursueSolvedWitnessFill(
                slot,
                raw_target,
                unknowns,
                view,
                view_bindings,
                &seen,
                &attempts,
            );
            slot.store.rollbackTo(mark);
        }
    }

    // Coupled-witness fallback (carry-to-leaf): when the concrete pass found
    // nothing, two metas may be jointly forced by an `ax`-style member
    // identity — an antecedent member must unify with a succedent member,
    // binding metas on both sides (e.g. `R ?t ey` = `R ez ?w` → `?t:=ez`,
    // `?w:=ey`). One of those metas is typically an ancestor witness; solving
    // it here concretizes the conclusion that carries it back up.
    if (try_coupled and slot.ctx.candidates.items.len == before_concrete) {
        try tryCoupledWitnesses(slot, raw_target, unknowns, view, view_bindings);
    }
}

/// Shared tail of every witness-enumeration loop (member, equal-coupled,
/// complementary-coupled): if the store's current assignments fully solve
/// `raw_target`, materialize it, dedupe against `seen`, and pursue the fill
/// through `continueOpenTargetSolved`. Abstains (returns early) otherwise;
/// the caller owns the mark/rollback bracket around each attempt.
fn pursueSolvedWitnessFill(
    slot: *OpenSlot,
    raw_target: ExprId,
    unknowns: []const ?ExprId,
    view: ?types.ViewDecl,
    view_bindings: ?[]const ?ExprId,
    seen: *[max_member_witness_attempts]ExprId,
    attempts: *usize,
) anyerror!void {
    const theorem = &slot.ctx.candidate.theorem;
    if (!slot.store.isFullySolved(theorem, raw_target)) return;
    const concrete = slot.store.materialize(theorem, raw_target) catch return;
    for (seen[0..attempts.*]) |prior| {
        if (prior == concrete) return;
    }
    seen[attempts.*] = concrete;
    attempts.* += 1;
    if (slot.ctx.counters) |c| c.acui_witness_attempts += 1;
    try continueOpenTargetSolved(
        slot,
        raw_target,
        unknowns,
        view,
        view_bindings,
        null,
    );
}

/// Walk `expr` and register every ancestor-witness meta leaf (stable
/// `meta_id`, not yet locally registered) in `store`, so the leaf unification
/// can bind it. See `MetaStore.registerAncestorMeta`.
fn registerAncestorMetas(
    store: *MetaStore,
    theorem: *const TheoremContext,
    expr: ExprId,
) anyerror!void {
    switch (theorem.interner.node(expr).*) {
        .variable => {},
        .placeholder => try store.registerAncestorMeta(theorem, expr),
        .app => |app| {
            for (app.args) |arg| {
                try registerAncestorMetas(store, theorem, arg);
            }
        },
    }
}

/// Meta-meta unification fallback: unify each pair of distinct meta-bearing
/// region members; a success that fully solves the target is pursued through
/// the ordinary concrete generation pipeline (and `tryCandidate` revalidates).
fn tryCoupledWitnesses(
    slot: *OpenSlot,
    raw_target: ExprId,
    unknowns: []const ?ExprId,
    view: ?types.ViewDecl,
    view_bindings: ?[]const ?ExprId,
) anyerror!void {
    const theorem = &slot.ctx.candidate.theorem;

    // The ancestor witness metas this pass may bind were registered by
    // `emitOpenTarget`, under its open-root gate.
    var members: [Witness.max_domain_members]ExprId = undefined;
    const member_count = Witness.collectMetaMembers(
        slot.ctx.context,
        slot.store,
        theorem,
        raw_target,
        &members,
    );
    if (member_count == 0) return;
    const before_coupled = slot.ctx.candidates.items.len;
    var seen: [max_member_witness_attempts]ExprId = undefined;
    var attempts: usize = 0;
    if (member_count >= 2) try tryPairedMembers(
        slot,
        raw_target,
        unknowns,
        view,
        view_bindings,
        members[0..member_count],
        &seen,
        &attempts,
    );
    if (attempts >= max_member_witness_attempts) return;

    // Anchored closure: nothing paired inside a region, but a
    // hypothesis-free rule may identify a region member with a position
    // outside every region — `ax`'s `g , a ⊢ a` pairs a context member with
    // the succedent. A meta-bearing member (`R ?t y`, an `all_left`
    // instance) and the formula at that position (`R z ?w`, an `ex_intro`
    // premise) are co-solved through the shape, which needs only ONE
    // meta-bearing member. Same guard as the complementary pass: runs only
    // when the region sweeps emitted nothing.
    if (slot.ctx.candidates.items.len != before_coupled) return;
    var anchors: [Witness.max_anchor_shapes]Witness.AnchorShape = undefined;
    const anchor_count = Witness.collectAnchorShapes(slot.ctx.context, &anchors);
    for (anchors[0..anchor_count]) |shape| {
        const anchor = Witness.anchorSubterm(theorem, shape, raw_target) orelse continue;
        for (members[0..member_count]) |member| {
            if (attempts >= max_member_witness_attempts) return;
            const mark = slot.store.mark();
            if (Witness.unifyMemberWithAnchor(
                slot.store,
                theorem,
                shape,
                member,
                anchor,
            )) {
                try pursueSolvedWitnessFill(
                    slot,
                    raw_target,
                    unknowns,
                    view,
                    view_bindings,
                    &seen,
                    &attempts,
                );
            }
            slot.store.rollbackTo(mark);
        }
    }
}

/// The region-pair sweeps of `tryCoupledWitnesses`: equal unification of two
/// meta-bearing members, then (if that emitted nothing) the complementary
/// closure through a rule's repeated-binder member pair.
fn tryPairedMembers(
    slot: *OpenSlot,
    raw_target: ExprId,
    unknowns: []const ?ExprId,
    view: ?types.ViewDecl,
    view_bindings: ?[]const ?ExprId,
    members: []const ExprId,
    seen: *[max_member_witness_attempts]ExprId,
    attempts: *usize,
) anyerror!void {
    const theorem = &slot.ctx.candidate.theorem;
    const before_coupled = slot.ctx.candidates.items.len;
    for (members, 0..) |a, i| {
        for (members, 0..) |b, j| {
            if (i >= j) continue;
            if (attempts.* >= max_member_witness_attempts) return;
            const mark = slot.store.mark();
            if (Witness.unifyMembers(slot.store, theorem, a, b)) {
                try pursueSolvedWitnessFill(
                    slot,
                    raw_target,
                    unknowns,
                    view,
                    view_bindings,
                    seen,
                    attempts,
                );
            }
            slot.store.rollbackTo(mark);
        }
    }

    // Complementary closure: no pair unifies EQUAL, but a hypothesis-free
    // rule may declare a complementation — `ax`'s `⊢ a , (¬ a) , d` repeats
    // binder `a` across two members — so two meta-bearing goal members
    // related by the repeated binder (`¬ R ?x y` vs `R z ?w`, both `rex`
    // witness outputs with no rigid anchor) are co-solved through the
    // template pair. The shapes come from the visible rule templates alone;
    // the engine never knows the wrapper means negation. Runs only when the
    // equal-unify sweep emitted nothing, so existing outcomes are untouched,
    // and every fill is revalidated by the child search plus `tryCandidate`.
    if (slot.ctx.candidates.items.len != before_coupled) return;
    var shapes: [Witness.max_complement_shapes]Witness.ComplementShape = undefined;
    const shape_count = Witness.collectComplementShapes(slot.ctx.context, &shapes);
    if (shape_count == 0) return;
    for (members, 0..) |member_a, i| {
        for (members, 0..) |member_b, j| {
            if (i == j) continue;
            for (shapes[0..shape_count]) |shape| {
                if (attempts.* >= max_member_witness_attempts) return;
                const mark = slot.store.mark();
                if (Witness.unifyMembersThroughShape(
                    slot.store,
                    theorem,
                    shape,
                    member_a,
                    member_b,
                )) {
                    try pursueSolvedWitnessFill(
                        slot,
                        raw_target,
                        unknowns,
                        view,
                        view_bindings,
                        seen,
                        attempts,
                    );
                }
                slot.store.rollbackTo(mark);
            }
        }
    }
}

/// Which `@vars` variables `tryPoolWitnesses` gives the unsolved metas.
const PoolPick = enum {
    /// The invented witness, the ladder's last rung (`allow_invent_witness`,
    /// set whenever the theory has a `@vars` pool): an open target still
    /// carrying unsolved existential metas after the concrete-member and
    /// coupled passes has a *genuinely free* witness — e.g. the `y` in
    /// `(∀x P x) → (∃y P y)`, which any domain element satisfies. The calculus
    /// is sound only over a non-empty domain, so completeness here requires
    /// *picking* a witness rather than forcing one. Every meta takes the first
    /// pool dummy of its sort, in sorted token order, that `assign` accepts
    /// (its dep-mask check is the theory-agnostic guard against a witness that
    /// would capture an in-scope bound variable). This is the "diagonal"
    /// assignment: the coupled slots of one chain pick the SAME witness, so an
    /// equality the proof implies between the metas holds (the `lall`
    /// instantiation and `rex` witness in `all_ex_inst` must coincide).
    shared,
    /// `fresh_bound`, after the child search left the slot's opened bound
    /// metas unsolved: each takes a variable occurring in no binding of the
    /// rule, distinct from every variable of the instance and from the other
    /// fills. Names the refs use in the same place come first
    /// (`assignRefNames`), then the first free `@vars` names
    /// (`fillFromPool`). Any other meta (a view binder) must come from
    /// the child search.
    fresh,
    /// A witness meta *erased* from a fully solved target, the invention
    /// rung's last resort: a vacuous `@recover` body makes the leaf swap
    /// `p[x ↦ ?t]` a no-op, and redex reduction can collapse `[x/?t]p` to `p`
    /// when `x` is not free in `p`. The meta then dangles in the bindings, so
    /// the concrete route sends the branch to validation with the witness
    /// binder undeterminable. Such a witness is genuinely unconstrained; each
    /// one the bindings or the view's still hold is filled like `shared`.
    dangling,
};

/// Ground every unsolved meta of `raw_target` to a `@vars`-pool dummy per
/// `pick`, then continue like the member- and coupled-witness passes:
/// `continueOpenTargetSolved` pins the parent's binders from the solved
/// metas, flags them for explicit-binding rendering (a witness is not
/// inferable from a freshly generated premise, and a bare generated
/// `lall`/`rex` leaves it unassigned → `MissingBinderAssignment`), and resumes
/// the backtrack. Nothing is minted: the dummies are pre-materialized pool
/// tokens (generate.zig), reinterned by `internParsedExpr`, so no dependency
/// bit is consumed however many slots request one. A meta whose sort has no
/// acceptable pool token fails the branch. `tryCandidate` revalidates every
/// fill. Returns whether any meta needed a fill.
fn tryPoolWitnesses(
    slot: *OpenSlot,
    raw_target: ExprId,
    unknowns: []const ?ExprId,
    view: ?types.ViewDecl,
    view_bindings: ?[]const ?ExprId,
    pick: PoolPick,
) anyerror!bool {
    const theorem = &slot.ctx.candidate.theorem;
    var unsolved = std.ArrayListUnmanaged(PlaceholderId){};
    defer unsolved.deinit(slot.ctx.context.allocator);
    try slot.store.collectUnsolved(theorem, raw_target, &unsolved);
    switch (pick) {
        .shared => {},
        .fresh => try collectSlotUnsolved(slot, unknowns, &unsolved),
        .dangling => {
            if (view_bindings) |vb| {
                for (vb) |maybe| if (maybe) |b| try slot.store.collectUnsolved(theorem, b, &unsolved);
            }
            for (unknowns) |maybe| if (maybe) |b| try slot.store.collectUnsolved(theorem, b, &unsolved);
        },
    }
    if (unsolved.items.len == 0) return false;

    const mark = slot.store.mark();
    defer slot.store.rollbackTo(mark);
    switch (pick) {
        .shared, .dangling => {
            var taken = bindingDeps(slot, theorem);
            if (!try fillFromPool(slot, theorem, unsolved.items, &taken, false)) return true;
        },
        .fresh => {
            var taken = bindingDeps(slot, theorem);
            const ref_names = try slot.ctx.context.allocator.alloc(ExprId, unsolved.items.len);
            defer slot.ctx.context.allocator.free(ref_names);
            if (try assignRefNames(slot, theorem, raw_target, unknowns, unsolved.items)) {
                for (unsolved.items, ref_names) |meta_id, *name| name.* = slot.store.lookup(meta_id).?;
                const before = slot.ctx.candidates.items.len;
                if (slot.store.isFullySolved(theorem, raw_target)) {
                    try continueOpenTargetSolved(slot, raw_target, unknowns, view, view_bindings, null);
                }
                if (slot.ctx.candidates.items.len != before) return true;
                slot.store.rollbackTo(mark);
                if (!try fillFromPool(slot, theorem, unsolved.items, &taken, true)) return true;
                // The blind pick repeats the ref-named attempt.
                for (unsolved.items, ref_names) |meta_id, name| {
                    if (slot.store.lookup(meta_id).? != name) break;
                } else return true;
            } else {
                // A false return can leave some names assigned; the blind
                // pick names every variable afresh.
                slot.store.rollbackTo(mark);
                if (!try fillFromPool(slot, theorem, unsolved.items, &taken, true)) return true;
            }
        },
    }
    if (!slot.store.isFullySolved(theorem, raw_target)) return true;
    try continueOpenTargetSolved(slot, raw_target, unknowns, view, view_bindings, null);
    return true;
}

/// Append the unsolved `.bound_choice` metas the slot's bindings and opened
/// binders still hold to `out`, skipping those already listed. Other metas
/// there (an open root's carried ones) are not this slot's to name.
fn collectSlotUnsolved(
    slot: *const OpenSlot,
    unknowns: []const ?ExprId,
    out: *std.ArrayListUnmanaged(PlaceholderId),
) !void {
    const theorem = &slot.ctx.candidate.theorem;
    var found = std.ArrayListUnmanaged(PlaceholderId){};
    defer found.deinit(slot.store.allocator);
    for (slot.ctx.bindings) |maybe| if (maybe) |value| try slot.store.collectUnsolved(theorem, value, &found);
    for (unknowns) |maybe| if (maybe) |value| try slot.store.collectUnsolved(theorem, value, &found);
    for (found.items) |meta_id| {
        if (slot.store.info(meta_id).?.kind != .bound_choice) continue;
        if (std.mem.indexOfScalar(PlaceholderId, out.items, meta_id) != null) continue;
        try out.append(slot.store.allocator, meta_id);
    }
}

/// The dependency bits of every variable the rule's bindings mention: what a
/// fresh variable must avoid.
fn bindingDeps(slot: *const OpenSlot, theorem: *const TheoremContext) u55 {
    var taken: u55 = 0;
    for (slot.ctx.bindings) |maybe| {
        const value = maybe orelse continue;
        taken |= (theorem.exprDeps(value, .{}) catch 0);
    }
    return taken;
}

/// Name the slot's fresh variables after the refs. MM0 has no
/// alpha-equivalence, so the name decides which refs a proof of the premise
/// can use. The first free `@vars` names in sorted order give
/// `nat_ind_elim`'s step premise `g , k : Nat , ih : C ⊢ …` the names
/// `ih` for `k` and `k` for `ih`, and no add_comm line `g , k : Nat ⊢ …`
/// fits it any more. So every part of the target or the bindings that
/// mentions an unsolved variable (the bindings still hold one the target
/// substituted away) is matched against every same-headed subterm of the refs
/// (`g , ?k : Nat` against `g , k : Nat`), and each variable takes the bound
/// variable those matches put in its place most often, ties going to the
/// first seen. A name must still occur in no binding and differ from the
/// other fills; a variable no ref names takes the first free `@vars` name
/// (`fillFromPool`). Returns false when no ref names any variable, one of
/// them is not a `.bound_choice` meta, or one cannot be filled; the caller's
/// rollback undoes any fills made before that.
fn assignRefNames(
    slot: *OpenSlot,
    theorem: *TheoremContext,
    raw_target: ExprId,
    unknowns: []const ?ExprId,
    unsolved: []const PlaceholderId,
) !bool {
    const allocator = slot.ctx.context.allocator;
    for (unsolved) |meta_id| {
        const meta = slot.store.info(meta_id) orelse return false;
        if (meta.kind != .bound_choice) return false;
    }
    var tally = RefNameTally{
        .slot = slot,
        .theorem = theorem,
        .unsolved = unsolved,
    };
    defer tally.deinit(allocator);
    try tally.collectParts(raw_target);
    for (slot.ctx.bindings) |maybe| if (maybe) |value| try tally.collectParts(value);
    for (unknowns) |maybe| if (maybe) |value| try tally.collectParts(value);
    if (tally.parts.items.len == 0) return false;
    for (slot.ctx.ref_index.entries) |entry| {
        try theorem.exprForEach(entry.expr, &tally, RefNameTally.visit);
    }
    if (tally.votes.count() == 0) return false;

    var taken = bindingDeps(slot, theorem);
    var named = false;
    for (unsolved) |meta_id| {
        // Most votes first; `votes` keeps first-seen order for ties.
        var best: ?ExprId = null;
        var best_deps: u55 = 0;
        var best_count: u32 = 0;
        var it = tally.votes.iterator();
        while (it.next()) |vote| {
            if (vote.key_ptr.meta != meta_id or vote.value_ptr.* <= best_count) continue;
            const info = (theorem.currentLeafInfo(vote.key_ptr.name) catch null) orelse continue;
            if (info.deps & taken != 0) continue;
            best = vote.key_ptr.name;
            best_deps = info.deps;
            best_count = vote.value_ptr.*;
        }
        const name = best orelse continue;
        slot.store.assign(theorem, meta_id, name) catch continue;
        taken |= best_deps;
        named = true;
    }
    if (!named) return false;
    return fillFromPool(slot, theorem, unsolved, &taken, true);
}

/// `assignRefNames`'s tally: which bound variable each ref subterm puts in
/// place of each unsolved variable, matched against the target's parts.
const RefNameTally = struct {
    slot: *OpenSlot,
    theorem: *TheoremContext,
    unsolved: []const PlaceholderId,
    /// App subterms of the target and bindings that mention an unsolved
    /// variable.
    parts: std.ArrayListUnmanaged(ExprId) = .{},
    /// Ref subterms already matched (refs share subterms).
    seen: std.AutoHashMapUnmanaged(ExprId, void) = .{},
    votes: std.AutoArrayHashMapUnmanaged(Vote, u32) = .{},

    const Vote = struct { meta: PlaceholderId, name: ExprId };

    fn deinit(self: *RefNameTally, allocator: std.mem.Allocator) void {
        self.parts.deinit(allocator);
        self.seen.deinit(allocator);
        self.votes.deinit(allocator);
    }

    fn collectParts(self: *RefNameTally, expr: ExprId) !void {
        const app = switch (self.theorem.interner.node(expr).*) {
            .app => |app| app,
            .variable, .placeholder => return,
        };
        if (!self.mentionsUnsolved(expr)) return;
        for (self.parts.items) |part| {
            if (part == expr) return;
        }
        try self.parts.append(self.slot.ctx.context.allocator, expr);
        for (app.args) |arg| try self.collectParts(arg);
    }

    fn mentionsUnsolved(self: *const RefNameTally, expr: ExprId) bool {
        return switch (self.theorem.interner.node(expr).*) {
            .variable => false,
            .placeholder => |pid| std.mem.indexOfScalar(PlaceholderId, self.unsolved, pid) != null,
            .app => |app| for (app.args) |arg| {
                if (self.mentionsUnsolved(arg)) break true;
            } else false,
        };
    }

    fn visit(self: *RefNameTally, theorem: *const TheoremContext, sub: ExprId) anyerror!void {
        const sub_app = switch (theorem.interner.node(sub).*) {
            .app => |app| app,
            .variable, .placeholder => return,
        };
        const allocator = self.slot.ctx.context.allocator;
        if ((try self.seen.getOrPut(allocator, sub)).found_existing) return;
        const store = self.slot.store;
        for (self.parts.items) |part| {
            if (theorem.interner.node(part).app.term_id != sub_app.term_id) continue;
            const mark = store.mark();
            defer store.rollbackTo(mark);
            if (forward.solveCorrespondence(store, self.theorem, sub, part, null) != .ok) continue;
            for (self.unsolved) |meta_id| {
                const name = store.lookup(meta_id) orelse continue;
                const info = (theorem.currentLeafInfo(name) catch null) orelse continue;
                if (!info.bound) continue;
                const gop = try self.votes.getOrPut(allocator, .{ .meta = meta_id, .name = name });
                gop.value_ptr.* = if (gop.found_existing) gop.value_ptr.* + 1 else 1;
            }
        }
    }
};

/// Fill each still unassigned meta of `metas` from the `@vars` pool, a
/// `.bound_choice` one with a variable outside `taken` that then joins it
/// (`boundAvoid`). With `require_bound`, every meta must be a `.bound_choice`
/// one. False when one cannot be filled; the caller's rollback undoes the
/// fills made before it.
fn fillFromPool(
    slot: *OpenSlot,
    theorem: *TheoremContext,
    metas: []const PlaceholderId,
    taken: *u55,
    require_bound: bool,
) !bool {
    for (metas) |meta_id| {
        if (slot.store.lookup(meta_id) != null) continue;
        const meta = slot.store.info(meta_id) orelse return false;
        if (require_bound and meta.kind != .bound_choice) return false;
        if (!try assignPoolWitness(slot, theorem, meta_id, meta.sort_name, boundAvoid(meta.kind, taken))) return false;
    }
    return true;
}

/// The avoid set for a pool fill of a meta of `kind`: a `.bound_choice` meta
/// is a bound variable, so it must be none of the instance's variables and
/// none of the other fills; a witness may be any of them.
fn boundAvoid(kind: OpenTerms.MetaKind, taken: *u55) ?*u55 {
    return if (kind == .bound_choice) taken else null;
}

/// Assign `meta_id` a `@vars`-pool dummy of `sort_name`, trying tokens in sorted
/// order and committing the first that `store.assign` accepts (its dep-mask /
/// sort / occurs checks reject a witness that would capture an in-scope bound
/// variable). With `avoid`, a dummy must also be a variable none of whose
/// dependency bits are in `avoid.*`, and its bits join the set. Returns true
/// on success. The dummies were pre-materialized into the work theorem
/// (generate.zig) and registered in `theorem_vars`; reinterning the parser var
/// here is dependency-free. A successful `assign` records a trail entry; a
/// rejected one records nothing, so the caller's single mark/rollback covers
/// the whole loop.
fn assignPoolWitness(
    slot: *OpenSlot,
    theorem: *TheoremContext,
    meta_id: PlaceholderId,
    sort_name: []const u8,
    avoid: ?*u55,
) !bool {
    var pool = try PoolVars.init(
        slot.ctx.context.allocator,
        slot.ctx.context.sort_vars,
        sort_name,
        theorem,
        slot.ctx.theorem_vars,
    );
    defer pool.deinit();
    while (try pool.nextAvoiding(if (avoid) |taken| taken.* else null)) |pool_var| {
        slot.store.assign(theorem, meta_id, pool_var.expr) catch continue;
        if (avoid) |taken| taken.* |= pool_var.deps;
        return true;
    }
    return false;
}

/// `PlaceholderFactory.makeFn` minting branch-local existential metas.
fn mintStoreMeta(
    ctx: ?*anyopaque,
    theorem: *TheoremContext,
    sort_name: []const u8,
    kind: OpenTerms.MetaKind,
) anyerror!ExprId {
    const store: *MetaStore = @ptrCast(@alignCast(ctx.?));
    return store.mint(theorem, sort_name, std.math.maxInt(u55), kind);
}

/// A rule binder's explicit-rendering flag as `setExplicitFlag` set it, with
/// what `restore` puts back.
const ExplicitFlag = struct {
    idx: usize,
    /// The previous value; null when the flag array did not exist before, so
    /// restoring just clears the bit.
    prev: ?bool,

    fn restore(self: ExplicitFlag, candidate: *ApplyCandidate) void {
        const flags = candidate.explicit orelse return;
        if (self.idx >= flags.len) return;
        flags[self.idx] = self.prev orelse false;
    }
};

/// Set the candidate's explicit flag for rule binder `idx`.
fn setExplicitFlag(candidate: *ApplyCandidate, idx: usize) !ExplicitFlag {
    const flags = blk: {
        if (candidate.explicit) |flags| break :blk flags;
        const flags = try candidate.allocator.alloc(bool, candidate.bindings.len);
        @memset(flags, false);
        candidate.explicit = flags;
        break :blk flags;
    };
    if (idx >= flags.len) return .{ .idx = idx, .prev = null };
    defer flags[idx] = true;
    return .{ .idx = idx, .prev = flags[idx] };
}

/// Mark binder `idx`, just bound to `value` by an ACUI split or principal
/// choice, for explicit rendering. The checker re-derives such a binder by
/// its own positional reading of the bag, which need not agree with the
/// search's choice, least of all inside a nested inline application.
/// A value holding a goal meta is not a choice the checker can take, so it
/// stays unmarked (null).
fn handSplitChoice(candidate: *ApplyCandidate, idx: usize, value: ?ExprId) !?ExplicitFlag {
    const expr = value orelse return null;
    if (candidate.theorem.containsPlaceholder(expr)) return null;
    return try setExplicitFlag(candidate, idx);
}
