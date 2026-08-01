const std = @import("std");
const types = @import("../types.zig");
const refs_mod = @import("../refs.zig");
const ref_index_mod = @import("../ref_index.zig");
const clipper = @import("../clipper.zig");
const rank = @import("../rank.zig");
const prune = @import("./prune.zig");
const abstract_prune = @import("../abstract_prune.zig");
const context_prune = @import("../context_prune.zig");
const seed = @import("./seed.zig");
const split = @import("./split.zig");
const acui = @import("./acui.zig");
const Witness = @import("./witness.zig");
const match = @import("./match.zig");
const plausible = @import("./plausible.zig");
const lookup_mod = @import("./lookup.zig");
const plan = @import("./plan.zig");
const validate = @import("./validate.zig");
const forward = @import("../forward.zig");
const candidate_mod = @import("../candidate.zig");
const session_mod = @import("../session.zig");
const ExprId = @import("../../../expr.zig").ExprId;
const PlaceholderId = @import("../../../expr.zig").PlaceholderId;
const TheoremContext = @import("../../../expr.zig").TheoremContext;
const GlobalEnv = @import("../../../env.zig").GlobalEnv;
const TemplateExpr = @import("../../../rules.zig").TemplateExpr;
const ArgInfo = @import("../../../parse_recovery.zig").ArgInfo;
const ProofScript = @import("../../../proof_script.zig");
const RuleApplication = ProofScript.RuleApplication;
const CompilerContext = @import("../../context.zig").CompilerContext;
const Check = @import("../../check.zig");
const OpenTerms = @import("../../inference/open_terms.zig");
const Redex = @import("./redex.zig");
const MetaStoreMod = @import("../../inference/meta_store.zig");
const MetaStore = MetaStoreMod.MetaStore;
const Goal = types.Goal;
const Context = types.Context;
const ApplyCandidate = types.ApplyCandidate;
const ExactCandidate = types.ExactCandidate;
const ExactOptions = types.ExactOptions;
const ExactResults = types.ExactResults;
const SearchCounters = types.SearchCounters;
const NameExprMap = types.NameExprMap;
const GenerationHook = types.GenerationHook;
const DerivedPool = types.DerivedPool;
const Fuel = types.Fuel;
const tryCandidate = candidate_mod.tryCandidate;
const rankReferenceIndices = refs_mod.rankReferenceIndices;
const exactCandidateLessThan = rank.exactCandidateLessThan;
const isBroadWholeLineHole = rank.isBroadWholeLineHole;
const recoverDefiniteMismatch = prune.recoverDefiniteMismatch;
const templateDefiniteMismatch = prune.templateDefiniteMismatch;
const projectViewBindingsIntoRule = prune.projectViewBindingsIntoRule;
const extractHypPartialBindings = prune.extractHypPartialBindings;
const acuiBoundMembersPlausible = prune.acuiBoundMembersPlausible;
const acuiClosedRegionPlausible = prune.acuiClosedRegionPlausible;
const normalizeAcuiUnits = prune.normalizeAcuiUnits;
const acuiUnitIdForHead = prune.acuiUnitIdForHead;
const defBodyForUnfold = prune.defBodyForUnfold;
const unfoldDefBody = prune.unfoldDefBody;
const templateNeedsSemantic = prune.templateNeedsSemantic;
const exprNeedsSemantic = prune.exprNeedsSemantic;
const bindingsNeedSemantic = prune.bindingsNeedSemantic;

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
    // split claims the bounded generation budget first. Stable, and only on the
    // generation path — plain `exact?` ordering is untouched.
    if (options.generator != null) {
        std.sort.insertion(
            ApplyCandidate,
            apply_candidates,
            SplitOrderCtx{ .context = context },
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
    // final clean-miss retry with `honor_eager_cut` off is the completeness
    // valve for a mis-annotation (see `generate.zig`'s ladder) — and the
    // eager *depth exemption* rides on `emitGeneratedSlot`'s hook call, not
    // on this cut. See docs/design_notes/eager_rule_scheduling.md.
    const honor_eager_cut = if (options.generator) |hook|
        hook.honor_eager_cut and context.registry.autoEagerRuleCount() > 0
    else
        false;
    var eager_armed = false;
    for (apply_candidates) |*apply_candidate| {
        apply_candidate.internal_child = options.internal_open_child;
        const is_eager = honor_eager_cut and
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

        const results_before = candidates.items.len;
        try enumerateCandidateRefs(
            compiler,
            allocator,
            context,
            ref_index,
            pool,
            apply_candidate,
            goal,
            theorem,
            theorem_vars,
            options.generator,
            options.derived,
            counters,
            options.fuel,
            &candidates,
        );
        if (is_eager and
            (apply_candidate.reached_child_solve or
                candidates.items.len > results_before))
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

/// Loop-invariant candidate-ref pruning setup for one rule. Both members are a
/// pure function of `(context, rule_id)`, so `backtrackRefs` computes this once
/// per candidate and threads it down the recursive ref enumeration rather than
/// re-deriving it at every DFS node (a single hoisted `views.get` plus the
/// static `analyzeView` flatten).
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
};

fn computePruneSetup(context: *const Context, rule_id: u32) PruneSetup {
    if (context.views.get(rule_id)) |view| {
        return .{
            .abstract_view = if (viewDeclHasAbstract(view)) view else null,
            .context_info = context_prune.analyzeView(context, view),
            .context_uses_rule_bindings = false,
        };
    }
    const rule = context.env.rules.items[rule_id];
    return .{
        .abstract_view = null,
        .context_info = context_prune.analyzeRule(context, rule),
        .context_uses_rule_bindings = true,
    };
}

const SplitOrderCtx = struct { context: *const Context };

fn nonSplitCandidateFirst(
    ctx: SplitOrderCtx,
    a: ApplyCandidate,
    b: ApplyCandidate,
) bool {
    const a_split = split.conclusionIsSplit(
        ctx.context,
        ctx.context.env.rules.items[a.rule_id].concl,
    );
    const b_split = split.conclusionIsSplit(
        ctx.context,
        ctx.context.env.rules.items[b.rule_id].concl,
    );
    if (a_split != b_split) return @intFromBool(a_split) < @intFromBool(b_split);
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
    const a_ord = generationOrderClass(ctx.context, a.rule_id);
    const b_ord = generationOrderClass(ctx.context, b.rule_id);
    return a_ord < b_ord;
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
/// `.constrained` — the phase-5 constrained-backward-MP concession for
/// un-enrolled rules (`hook.allow_constrained_mp`): a structured open target
/// is built, but the child proof must determine every meta by read-back; no
/// meta propagates into nested open slots and nothing is invented.
/// `@abstract` motive inference rides this branch too.
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

fn enumerateCandidateRefs(
    compiler: *CompilerContext,
    allocator: std.mem.Allocator,
    context: *const Context,
    ref_index: *const ref_index_mod.Index,
    pool: []const refs_mod.RefPoolEntry,
    candidate: *ApplyCandidate,
    goal: Goal,
    theorem: *const TheoremContext,
    theorem_vars: *const NameExprMap,
    generator: ?*const GenerationHook,
    derived: ?*DerivedPool,
    counters: ?*SearchCounters,
    fuel: ?*Fuel,
    candidates: *std.ArrayListUnmanaged(ExactCandidate),
) !void {
    const hyp_count = candidate.unresolved_hyps.len;
    if (hyp_count == 0) {
        try validateSelectedRefs(
            compiler,
            allocator,
            context,
            pool,
            candidate,
            goal,
            theorem,
            theorem_vars,
            candidate.bindings,
            &.{},
            &.{},
            counters,
            fuel,
            candidates,
        );
        return;
    }

    const rule = &context.env.rules.items[candidate.rule_id];
    const plans = try buildHypPlans(
        allocator,
        context,
        ref_index,
        candidate,
        generator != null,
        derived,
        counters,
    );
    defer allocator.free(plans);
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
    // Parallel to `selected`: a generated inline sub-application chosen for a
    // slot instead of a pool ref. Always `null` when `generator` is
    // null, so the pool-only `exact?` path is unaffected.
    const generated = try allocator.alloc(?RuleApplication, hyp_count);
    defer allocator.free(generated);
    @memset(generated, null);

    try backtrackRefs(
        compiler,
        allocator,
        context,
        ref_index,
        pool,
        candidate,
        rule,
        goal,
        theorem,
        theorem_vars,
        plans,
        0,
        bindings,
        snapshots,
        selected,
        generated,
        generator,
        derived,
        counters,
        fuel,
        candidates,
        null,
    );
}

fn backtrackRefs(
    compiler: *CompilerContext,
    allocator: std.mem.Allocator,
    context: *const Context,
    ref_index: *const ref_index_mod.Index,
    pool: []const refs_mod.RefPoolEntry,
    candidate: *ApplyCandidate,
    rule: *const @import("../../../env.zig").RuleDecl,
    goal: Goal,
    theorem: *const TheoremContext,
    theorem_vars: *const NameExprMap,
    plans: []const HypPlan,
    depth: usize,
    bindings: []?ExprId,
    snapshots: []?ExprId,
    selected: []?usize,
    generated: []?RuleApplication,
    generator: ?*const GenerationHook,
    derived: ?*DerivedPool,
    counters: ?*SearchCounters,
    fuel: ?*Fuel,
    candidates: *std.ArrayListUnmanaged(ExactCandidate),
    // Loop-invariant pruning setup for `candidate.rule_id`. `null` on the
    // outermost entry (computed once here); the recursive descent threads the
    // computed value so it is not re-derived at every DFS node.
    prune_setup: ?PruneSetup,
) anyerror!void {
    if (depth == plans.len) {
        try validateSelectedRefs(
            compiler,
            allocator,
            context,
            pool,
            candidate,
            goal,
            theorem,
            theorem_vars,
            bindings,
            selected,
            generated,
            counters,
            fuel,
            candidates,
        );
        return;
    }

    const position = plans[depth].position;
    const hyp = candidate.unresolved_hyps[position];
    // Derived-pool participation for this slot. The cached unbound lookup
    // (`derivedSlotCandidates`) can prove no derived shape will ever fill
    // this (rule, hyp) slot — then the slot pays nothing further for the
    // derived pool for the lifetime of the search. Otherwise the slot's
    // shape query below runs against the pool index and the derived index
    // in one build (the dual lookup).
    var derived_index: ?*const ref_index_mod.Index = null;
    var derived_dead = false;
    if (derived) |dpool| {
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
        ref_index,
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
    if (lookup.pool.indices.len == 0 and generator == null and derived == null) {
        return;
    }

    // Candidate-ref pruning setup, loop-invariant for this rule. Computed once on
    // the outermost entry and threaded down the recursion (see `prune_setup`).
    //   * `@abstract` (Leibniz one-hole-context) prefilter — only views carrying
    //     an @abstract decl participate; fires on *all* search paths to cut the
    //     broad-slot ref flood, e.g. `eq_replace`'s bare-binder target hyp, whose
    //     view conclusion is a covering wildcard `finalConclusionPlausible` can't
    //     refute.
    //   * ACUI context-combination prefilter — any view with an ACUI context
    //     position participates, catching broad hypothesis-context floods the
    //     conclusion-side view refuter does not reach.
    const setup = prune_setup orelse computePruneSetup(context, candidate.rule_id);
    const abstract_view = setup.abstract_view;
    const context_prune_info = setup.context_info;

    const snapshot = snapshots[depth * bindings.len ..][0..bindings.len];
    for (lookup.pool.indices) |pool_index| {
        switch (try matchOneHypWithSnapshot(
            allocator,
            context,
            &candidate.theorem,
            candidate.rule_id,
            hyp.index,
            ref_index.entries[pool_index].expr,
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
        if ((generator != null or derived != null) and
            !finalConclusionPlausible(context, candidate, goal, bindings, counters))
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
            for (plans[0..depth]) |earlier| {
                const sel = selected[earlier.position] orelse continue;
                if (fill_len >= fill_buf.len) break;
                fill_buf[fill_len] = .{
                    .hyp_index = candidate.unresolved_hyps[earlier.position].index,
                    .ref_expr = ref_index.entries[sel].expr,
                };
                fill_len += 1;
            }
            if (fill_len < fill_buf.len) {
                fill_buf[fill_len] = .{
                    .hyp_index = hyp.index,
                    .ref_expr = ref_index.entries[pool_index].expr,
                };
                fill_len += 1;
            }
            const fills = fill_buf[0..fill_len];
            const goal_expr: ?ExprId = goal.concreteOrHint();
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
        selected[position] = pool_index;
        try backtrackRefs(
            compiler,
            allocator,
            context,
            ref_index,
            pool,
            candidate,
            rule,
            goal,
            theorem,
            theorem_vars,
            plans,
            depth + 1,
            bindings,
            snapshots,
            selected,
            generated,
            generator,
            derived,
            counters,
            fuel,
            candidates,
            setup,
        );
        selected[position] = null;
        rollbackOneHypMatch(bindings, snapshot);
    }

    // Forward refs: after pool refs, try filling the slot with a
    // derived ref's materialized recipe (cheaper than recursive generation,
    // and the only way an open slot can absorb a deferred instantiation).
    if (derived) |dpool| {
        if (!derived_dead) try tryDerivedSlots(
            compiler,
            allocator,
            context,
            ref_index,
            pool,
            dpool,
            if (lookup.derived) |*dlookup| dlookup else null,
            candidate,
            rule,
            goal,
            theorem,
            theorem_vars,
            plans,
            depth,
            position,
            hyp.index,
            bindings,
            snapshot,
            snapshots,
            selected,
            generated,
            generator,
            counters,
            fuel,
            candidates,
        );
    }

    // After pool refs, let the generation hook try to synthesize a
    // sub-proof for this slot. Only fires when a hook is present and the
    // hypothesis is already concrete given the current bindings (its binders
    // pinned by the conclusion or by sibling refs chosen above).
    if (generator) |hook| {
        try tryGenerateSlot(
            compiler,
            allocator,
            context,
            ref_index,
            pool,
            candidate,
            rule,
            goal,
            theorem,
            theorem_vars,
            plans,
            depth,
            position,
            hyp.index,
            bindings,
            snapshots,
            selected,
            generated,
            hook,
            derived,
            counters,
            fuel,
            candidates,
        );
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
    compiler: *CompilerContext,
    allocator: std.mem.Allocator,
    context: *const Context,
    ref_index: *const ref_index_mod.Index,
    pool: []const refs_mod.RefPoolEntry,
    dpool: *DerivedPool,
    derived_lookup: ?*const ref_index_mod.LookupResult,
    candidate: *ApplyCandidate,
    rule: *const @import("../../../env.zig").RuleDecl,
    goal: Goal,
    theorem: *const TheoremContext,
    theorem_vars: *const NameExprMap,
    plans: []const HypPlan,
    depth: usize,
    position: usize,
    hyp_index: usize,
    bindings: []?ExprId,
    snapshot: []?ExprId,
    snapshots: []?ExprId,
    selected: []?usize,
    generated: []?RuleApplication,
    generator: ?*const GenerationHook,
    counters: ?*SearchCounters,
    fuel: ?*Fuel,
    candidates: *std.ArrayListUnmanaged(ExactCandidate),
) anyerror!void {
    const goal_expr: ?ExprId = goal.concreteOrHint();
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
            allocator,
            context,
            &candidate.theorem,
            candidate.rule_id,
            hyp_index,
            dref.shape,
            bindings,
            snapshot,
            candidate.view_concl_seed,
            counters,
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
                const view_bindings = try allocator.alloc(
                    ?ExprId,
                    cview.num_binders,
                );
                defer allocator.free(view_bindings);
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
                    theorem_vars,
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
            if (finalConclusionPlausible(context, candidate, goal, bindings, counters)) {
                generated[position] = app;
                try backtrackRefs(
                    compiler,
                    allocator,
                    context,
                    ref_index,
                    pool,
                    candidate,
                    rule,
                    goal,
                    theorem,
                    theorem_vars,
                    plans,
                    depth + 1,
                    bindings,
                    snapshots,
                    selected,
                    generated,
                    generator,
                    dpool,
                    counters,
                    fuel,
                    candidates,
                    null,
                );
                generated[position] = null;
            } else if (counters) |actual| {
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
    compiler: *CompilerContext,
    allocator: std.mem.Allocator,
    context: *const Context,
    ref_index: *const ref_index_mod.Index,
    pool: []const refs_mod.RefPoolEntry,
    candidate: *ApplyCandidate,
    rule: *const @import("../../../env.zig").RuleDecl,
    goal: Goal,
    theorem: *const TheoremContext,
    theorem_vars: *const NameExprMap,
    plans: []const HypPlan,
    depth: usize,
    position: usize,
    hyp_index: usize,
    bindings: []?ExprId,
    snapshots: []?ExprId,
    selected: []?usize,
    generated: []?RuleApplication,
    hook: *const GenerationHook,
    derived: ?*DerivedPool,
    counters: ?*SearchCounters,
    fuel: ?*Fuel,
    candidates: *std.ArrayListUnmanaged(ExactCandidate),
) anyerror!void {
    if (try OpenTerms.instantiateTemplateConcrete(
        &candidate.theorem,
        rule.hyps[hyp_index],
        bindings,
    )) |raw_target| {
        try emitGeneratedSlot(
            compiler,
            allocator,
            context,
            ref_index,
            pool,
            candidate,
            rule,
            goal,
            theorem,
            theorem_vars,
            plans,
            depth,
            position,
            bindings,
            snapshots,
            selected,
            generated,
            hook,
            derived,
            counters,
            fuel,
            candidates,
            raw_target,
        );
        return;
    }

    // The hypothesis context binder is still open. This is the multiplicative
    // case: a conclusion combining contexts under an ACUI combiner leaves a
    // split-half (`Γ`/`Δ`/`Σ`) unpinned because its subproof must be generated.
    // Speculatively distribute the goal context across the open binder and recurse
    // per candidate; the validator confirms each assembly.
    const candidates_before_split = candidates.items.len;
    try trySplitGenerate(
        compiler,
        allocator,
        context,
        ref_index,
        pool,
        candidate,
        rule,
        goal,
        theorem,
        theorem_vars,
        plans,
        depth,
        position,
        hyp_index,
        bindings,
        snapshots,
        selected,
        generated,
        hook,
        derived,
        counters,
        fuel,
        candidates,
    );

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
    if (candidates.items.len != candidates_before_split) return;
    if (hook.solveOpenFn != null and
        openMode(context, candidate.rule_id, hook.allow_constrained_mp) != .none)
    {
        try tryOpenGenerateSlot(
            compiler,
            allocator,
            context,
            ref_index,
            pool,
            candidate,
            rule,
            goal,
            theorem,
            theorem_vars,
            plans,
            depth,
            position,
            hyp_index,
            bindings,
            snapshots,
            selected,
            generated,
            hook,
            derived,
            counters,
            fuel,
            candidates,
        );
        if (candidates.items.len != candidates_before_split) return;
    }

    // Final fallback: ACUI principal enumeration for the order-sensitive
    // principal-selection gap (e.g. `de_morgan`). Reached only when split and
    // open generation both produced nothing for this slot, so it is additive.
    try tryPrincipalEnumerate(
        compiler,
        allocator,
        context,
        ref_index,
        pool,
        candidate,
        rule,
        goal,
        theorem,
        theorem_vars,
        plans,
        depth,
        position,
        hyp_index,
        bindings,
        snapshots,
        selected,
        generated,
        hook,
        derived,
        counters,
        fuel,
        candidates,
    );
}

/// Emit a single generated slot: canonicalize ACUI units out of the (now
/// concrete) sub-target, ask the hook to prove it, and recurse with the slot
/// filled. Canonicalizing the unit (`emp`) lets the sub-target match unit-free
/// pool refs — an `imp_intro` over an `emp ⊢ …` goal binds the context binder to
/// `emp`, leaving a redundant unit the strict `matchTemplate` would otherwise
/// reject (the validator absorbs it anyway).
fn emitGeneratedSlot(
    compiler: *CompilerContext,
    allocator: std.mem.Allocator,
    context: *const Context,
    ref_index: *const ref_index_mod.Index,
    pool: []const refs_mod.RefPoolEntry,
    candidate: *ApplyCandidate,
    rule: *const @import("../../../env.zig").RuleDecl,
    goal: Goal,
    theorem: *const TheoremContext,
    theorem_vars: *const NameExprMap,
    plans: []const HypPlan,
    depth: usize,
    position: usize,
    bindings: []?ExprId,
    snapshots: []?ExprId,
    selected: []?usize,
    generated: []?RuleApplication,
    hook: *const GenerationHook,
    derived: ?*DerivedPool,
    counters: ?*SearchCounters,
    fuel: ?*Fuel,
    candidates: *std.ArrayListUnmanaged(ExactCandidate),
    raw_target: ExprId,
) anyerror!void {
    const reduced = try Redex.reduceRedexOnly(context, &candidate.theorem, raw_target);
    const target = try normalizeAcuiUnits(context, &candidate.theorem, reduced);
    // The application matched the goal and is launching a subgoal solve —
    // the signal that arms the `@auto eager` set-commit cut (consulted only
    // for eager candidates). An eager application is also exempt from the
    // depth budget: `eager_step` tells the driver to solve the child at the
    // parent's remaining depth (independent of `honor_eager_cut`).
    candidate.reached_child_solve = true;
    const eager_step = context.registry.eagerPriority(candidate.rule_id) != null;
    const proof = (try hook.solve(target, &candidate.theorem, eager_step)) orelse {
        return;
    };
    if (proof.conclusion != target) {
        return;
    }
    generated[position] = proof.application;
    defer generated[position] = null;
    try backtrackRefs(
        compiler,
        allocator,
        context,
        ref_index,
        pool,
        candidate,
        rule,
        goal,
        theorem,
        theorem_vars,
        plans,
        depth + 1,
        bindings,
        snapshots,
        selected,
        generated,
        hook,
        derived,
        counters,
        fuel,
        candidates,
        null,
    );
}

/// Speculative ACUI split for a generate-only slot whose context binder is open.
/// Finds the first open binder of this hypothesis that the conclusion combines
/// under an ACUI head, enumerates concrete candidate contexts for it (distributing
/// the goal's members, minimal-first), and for each makes the slot concrete and
/// emits it. The binding is set only for the duration of each candidate's
/// recursion (so it pins the conclusion + later slots), then rolled back. Other
/// open binders are resolved as their own slots are reached.
fn trySplitGenerate(
    compiler: *CompilerContext,
    allocator: std.mem.Allocator,
    context: *const Context,
    ref_index: *const ref_index_mod.Index,
    pool: []const refs_mod.RefPoolEntry,
    candidate: *ApplyCandidate,
    rule: *const @import("../../../env.zig").RuleDecl,
    goal: Goal,
    theorem: *const TheoremContext,
    theorem_vars: *const NameExprMap,
    plans: []const HypPlan,
    depth: usize,
    position: usize,
    hyp_index: usize,
    bindings: []?ExprId,
    snapshots: []?ExprId,
    selected: []?usize,
    generated: []?RuleApplication,
    hook: *const GenerationHook,
    derived: ?*DerivedPool,
    counters: ?*SearchCounters,
    fuel: ?*Fuel,
    candidates: *std.ArrayListUnmanaged(ExactCandidate),
) anyerror!void {
    if (!hook.allow_split) return; // first (non-splitting) generation pass
    const goal_expr = goal.concreteOrHint() orelse return;
    const hyp_template = rule.hyps[hyp_index];
    const binders = templateBinderMask(hyp_template);
    if (binders.overflow) return;

    var bits = binders.mask;
    while (bits != 0) {
        const b: usize = @ctz(bits);
        bits &= bits - 1;
        if (b < bindings.len and bindings[b] != null) continue; // already pinned
        const site = split.findSplitSite(
            context,
            &candidate.theorem,
            rule.concl,
            goal_expr,
            b,
        ) orelse continue;

        var enumerator = split.buildEnumerator(
            context,
            &candidate.theorem,
            site,
            bindings,
            b,
            hook.allow_retain_principal,
        ) orelse continue;

        var i: usize = 0;
        while (i < enumerator.count()) : (i += 1) {
            const cand = (try enumerator.candidate(
                context,
                &candidate.theorem,
                i,
            )) orelse continue;
            const saved = bindings[b];
            bindings[b] = cand;
            if (!splitSiteBindingsPlausible(
                context,
                &candidate.theorem,
                site,
                bindings,
            )) {
                if (counters) |actual| {
                    actual.split_context_guard_rejects += 1;
                }
                bindings[b] = saved;
                continue;
            }
            if (try OpenTerms.instantiateTemplateConcrete(
                &candidate.theorem,
                hyp_template,
                bindings,
            )) |raw_target| {
                try emitGeneratedSlot(
                    compiler,
                    allocator,
                    context,
                    ref_index,
                    pool,
                    candidate,
                    rule,
                    goal,
                    theorem,
                    theorem_vars,
                    plans,
                    depth,
                    position,
                    bindings,
                    snapshots,
                    selected,
                    generated,
                    hook,
                    derived,
                    counters,
                    fuel,
                    candidates,
                    raw_target,
                );
            } else if (hook.solveOpenFn != null and
                openMode(
                    context,
                    candidate.rule_id,
                    hook.allow_constrained_mp,
                ) == .witness)
            {
                // The split pinned this context binder, but
                // the hypothesis still has an open witness binder (e.g.
                // `union_intro`'s `G ⊢ x ∈ y` with `y` hypothesis-only). Run
                // the open path under the split binding so the witness can be
                // solved from the now-concrete context's ACUI members.
                try tryOpenGenerateSlot(
                    compiler,
                    allocator,
                    context,
                    ref_index,
                    pool,
                    candidate,
                    rule,
                    goal,
                    theorem,
                    theorem_vars,
                    plans,
                    depth,
                    position,
                    hyp_index,
                    bindings,
                    snapshots,
                    selected,
                    generated,
                    hook,
                    derived,
                    counters,
                    fuel,
                    candidates,
                );
            }
            bindings[b] = saved;
        }
        // One open binder enumerated; sibling open binders are split at their own
        // slots, with this binder's choice now pinning their intervals.
        return;
    }
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
    compiler: *CompilerContext,
    allocator: std.mem.Allocator,
    context: *const Context,
    ref_index: *const ref_index_mod.Index,
    pool: []const refs_mod.RefPoolEntry,
    candidate: *ApplyCandidate,
    rule: *const @import("../../../env.zig").RuleDecl,
    goal: Goal,
    theorem: *const TheoremContext,
    theorem_vars: *const NameExprMap,
    plans: []const HypPlan,
    depth: usize,
    position: usize,
    hyp_index: usize,
    bindings: []?ExprId,
    snapshots: []?ExprId,
    selected: []?usize,
    generated: []?RuleApplication,
    hook: *const GenerationHook,
    derived: ?*DerivedPool,
    counters: ?*SearchCounters,
    fuel: ?*Fuel,
    candidates: *std.ArrayListUnmanaged(ExactCandidate),
) anyerror!void {
    if (!hook.allow_split) return;
    // Structural gate only, no enrollment requirement: everything below
    // enumerates concrete goal members for one unresolved structured
    // principal (no metas minted, ≥2 genuinely competing members), mirroring
    // seed-time `detectPrincipalFanout`, which is likewise
    // annotation-independent. The seed-time/generation-time pair differ by
    // *phase*, not by author permission.
    const goal_expr = goal.concreteOrHint() orelse return;
    const hyp_template = rule.hyps[hyp_index];
    const hyp_binders = templateBinderMask(hyp_template);
    if (hyp_binders.overflow) return;

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
    var bits = hyp_binders.mask;
    site_search: while (bits != 0) {
        const b: usize = @ctz(bits);
        bits &= bits - 1;
        const s = split.findSplitSite(
            context,
            &candidate.theorem,
            rule.concl,
            goal_expr,
            b,
        ) orelse continue;
        var only_unbound: ?TemplateExpr = null;
        var f: usize = 0;
        while (f < s.fixed_len) : (f += 1) {
            if (split.templateFullyBound(s.fixed[f], bindings)) continue;
            if (only_unbound != null) continue :site_search; // >1 unbound: skip
            only_unbound = s.fixed[f];
        }
        if (only_unbound) |p| {
            ftmpl = p;
            found_site = s;
            break;
        }
    }
    const site = found_site orelse return;
    const principal_template = ftmpl orelse return;

    const members = collectSplitMembers(
        context,
        &candidate.theorem,
        site.container,
        site.head_id,
    ) orelse return;

    const pmask = templateBinderMask(principal_template);
    if (pmask.overflow) return;

    // Only enumerate when 2+ distinct members genuinely compete for the
    // principal; a single match is forced and already handled positionally.
    var match_count: usize = 0;
    var ci: usize = 0;
    while (ci < members.len) : (ci += 1) {
        if (acui.templateMatchesExprReadOnly(
            &candidate.theorem,
            principal_template,
            members.items[ci],
            bindings,
        )) match_count += 1;
    }
    if (match_count < 2) return;

    var mi: usize = 0;
    while (mi < members.len) : (mi += 1) {
        const member = members.items[mi];
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
            try trySplitGenerate(
                compiler,
                allocator,
                context,
                ref_index,
                pool,
                candidate,
                rule,
                goal,
                theorem,
                theorem_vars,
                plans,
                depth,
                position,
                hyp_index,
                bindings,
                snapshots,
                selected,
                generated,
                hook,
                derived,
                counters,
                fuel,
                candidates,
            );
        }
        pm = pmask.mask;
        while (pm != 0) {
            const idx: u6 = @intCast(@ctz(pm));
            pm &= pm - 1;
            if (idx < bindings.len) bindings[idx] = saved[idx];
        }
    }
}

/// Shared state for one open-slot attempt. Bundled (unlike the rest
/// of this file's explicit parameter style) because the open path recurses
/// over bound-witness choices and recover/meta construction layers, and
/// would otherwise thread two dozen parameters through every level.
const OpenSlot = struct {
    compiler: *CompilerContext,
    allocator: std.mem.Allocator,
    context: *const Context,
    ref_index: *const ref_index_mod.Index,
    pool: []const refs_mod.RefPoolEntry,
    candidate: *ApplyCandidate,
    rule: *const @import("../../../env.zig").RuleDecl,
    goal: Goal,
    theorem: *const TheoremContext,
    theorem_vars: *const NameExprMap,
    plans: []const HypPlan,
    depth: usize,
    position: usize,
    hyp_index: usize,
    bindings: []?ExprId,
    snapshots: []?ExprId,
    selected: []?usize,
    generated: []?RuleApplication,
    hook: *const GenerationHook,
    derived: ?*DerivedPool,
    counters: ?*SearchCounters,
    fuel: ?*Fuel,
    candidates: *std.ArrayListUnmanaged(ExactCandidate),
    /// Branch-local existential store for this slot attempt. Mint marks are
    /// taken before each construction layer and rolled back beside the
    /// bindings snapshot (the meta-store rollback invariant).
    store: *MetaStore,
    /// Open policy for this candidate, computed once at slot entry.
    /// `.witness` gates the existential machinery (bound-binder meta
    /// deferral, ancestor-meta registration, the force-first ladder);
    /// `.constrained` keeps the child-search-first read-back discipline.
    mode: OpenMode,
};

/// Structured open backward generation for one hypothesis
/// slot of an `@auto backward` rule. Builds an open target whose unsolved
/// leaves are existential metas — preferring the `@recover`-shaped surface
/// over raw template deferral — asks the hook to solve it with a generated
/// child proof, matches the child's concrete conclusion back against the
/// target to pin the parent's binders, and continues to the next sibling.
fn tryOpenGenerateSlot(
    compiler: *CompilerContext,
    allocator: std.mem.Allocator,
    context: *const Context,
    ref_index: *const ref_index_mod.Index,
    pool: []const refs_mod.RefPoolEntry,
    candidate: *ApplyCandidate,
    rule: *const @import("../../../env.zig").RuleDecl,
    goal: Goal,
    theorem: *const TheoremContext,
    theorem_vars: *const NameExprMap,
    plans: []const HypPlan,
    depth: usize,
    position: usize,
    hyp_index: usize,
    bindings: []?ExprId,
    snapshots: []?ExprId,
    selected: []?usize,
    generated: []?RuleApplication,
    hook: *const GenerationHook,
    derived: ?*DerivedPool,
    counters: ?*SearchCounters,
    fuel: ?*Fuel,
    candidates: *std.ArrayListUnmanaged(ExactCandidate),
) anyerror!void {
    var store = MetaStore.init(allocator, context.env);
    // Share the driver's global meta-id counter so witness metas keep a stable
    // identity across the open-target recursion's interner clones.
    store.meta_id_counter = hook.meta_id_counter;
    defer {
        // Mirror this branch's meta activity into the bench counters
        // (META.md performance gates).
        if (counters) |c| {
            c.existential_metas_created += store.stats.existential_created;
            c.bound_choice_metas_created += store.stats.bound_choice_created;
            c.meta_assignments += store.stats.assignments;
            c.meta_rollbacks += store.stats.rollbacks;
        }
        store.deinit();
    }
    // The pool-ref loop at this depth is done with its snapshot slice;
    // reuse it as the open path's bindings rollback point.
    const snapshot = snapshots[depth * bindings.len ..][0..bindings.len];
    @memcpy(snapshot, bindings);
    defer rollbackOneHypMatch(bindings, snapshot);

    var slot = OpenSlot{
        .compiler = compiler,
        .allocator = allocator,
        .context = context,
        .ref_index = ref_index,
        .pool = pool,
        .candidate = candidate,
        .rule = rule,
        .goal = goal,
        .theorem = theorem,
        .theorem_vars = theorem_vars,
        .plans = plans,
        .depth = depth,
        .position = position,
        .hyp_index = hyp_index,
        .bindings = bindings,
        .snapshots = snapshots,
        .selected = selected,
        .generated = generated,
        .hook = hook,
        .derived = derived,
        .counters = counters,
        .fuel = fuel,
        .candidates = candidates,
        .store = &store,
        .mode = openMode(
            context,
            candidate.rule_id,
            hook.allow_constrained_mp,
        ),
    };
    if (context.views.get(candidate.rule_id)) |view| {
        try openSlotViaView(&slot, view);
    } else {
        try openSlotRaw(&slot);
    }
}

/// Open path for a rule without a `@view`: enumerate witnesses for open
/// bound-class binders, defer the remaining open binders as existential
/// metas, and emit the structured target.
fn openSlotRaw(slot: *OpenSlot) anyerror!void {
    const template = slot.rule.hyps[slot.hyp_index];
    // See `openSlotView`: open bound binders defer to the existential-meta path
    // (carry-to-leaf) rather than enumerating a concrete witness pool.
    const unknowns = try slot.allocator.alloc(?ExprId, slot.bindings.len);
    defer slot.allocator.free(unknowns);
    @memset(unknowns, null);
    var options = OpenTerms.OpenInstantiateOptions{
        .factory = .{
            .context = slot.store,
            .kind = .existential,
            .makeFn = mintStoreMeta,
        },
        .logical_unknowns = unknowns,
        .excluded = null,
        .conclusion_binders = conclusionBinderMaskOrNone(slot.rule.concl),
        .open_bound_in_combiner = slot.mode != .witness,
        .arg_infos = slot.rule.args,
    };
    const mark = slot.store.mark();
    defer slot.store.rollbackTo(mark);
    const target = (try OpenTerms.instantiateTemplateOpen(
        &slot.candidate.theorem,
        slot.context.env,
        slot.context.registry,
        template,
        slot.bindings,
        &options,
    )) orelse return;
    try emitOpenTarget(slot, target, unknowns, null, null);
}

/// Open path for a rule with a `@view`: the open target is the *view*
/// hypothesis surface. `@recover` laws whose pattern/hole are pinned defer
/// their witness as one existential meta and build the source surface by the
/// leaf swap (`φ[x ↦ ?t]` instead of the raw `sb`-headed template);
/// a law that cannot fire owns its binders exclusively (no bare-meta
/// fallback for them).
fn openSlotViaView(slot: *OpenSlot, view: types.ViewDecl) anyerror!void {
    if (slot.hyp_index >= view.hyps.len) return;
    const theorem = &slot.candidate.theorem;
    const view_bindings = try slot.allocator.alloc(?ExprId, view.num_binders);
    defer slot.allocator.free(view_bindings);
    seedViewBindingsForMatch(
        view,
        slot.bindings,
        slot.candidate.view_concl_seed,
        view_bindings,
    );

    const excluded = try slot.allocator.alloc(bool, view.num_binders);
    defer slot.allocator.free(excluded);
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
    const unknowns = try slot.allocator.alloc(?ExprId, view.num_binders);
    defer slot.allocator.free(unknowns);
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
    const target = (try OpenTerms.instantiateTemplateOpen(
        &slot.candidate.theorem,
        slot.context.env,
        slot.context.registry,
        view.hyps[slot.hyp_index],
        view_bindings,
        &options,
    )) orelse return;

    // Overlay the freshly minted per-binder metas into a local copy of the
    // view bindings so the match-back materialization covers them.
    const effective = try slot.allocator.dupe(?ExprId, view_bindings);
    defer slot.allocator.free(effective);
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
    const theorem = &slot.candidate.theorem;
    // Canonicalize ACUI units away before the recursive solve and readback.
    // An open target can carry a redundant `emp` (e.g. a witness rule whose
    // context binder `g` is the unit, so its hypothesis instantiates to
    // `emp , (∀ x p) , [x/t]p ⊢ d`). The child's accepted conclusion comes
    // back unit-free, so without this the readback `solveCorrespondence` cannot
    // align the ACUI members to bind the carried ancestor witness. Meta leaves
    // survive normalization unchanged, so the open binders stay intact. The
    // concrete generated path already normalizes (see `tryGenerateSlot`).
    const reduced_target = try Redex.reduceRedexOnly(slot.context, theorem, raw_target_in);
    const raw_target = try normalizeAcuiUnits(slot.context, theorem, reduced_target);
    if (slot.store.isFullySolved(theorem, raw_target)) {
        // Bound-witness enumeration closed every open binder: this is an
        // ordinary concrete generated slot (for view rules, a concrete
        // view-surface target the validator reconciles through the view
        // machinery).
        try emitGeneratedSlot(
            slot.compiler,
            slot.allocator,
            slot.context,
            slot.ref_index,
            slot.pool,
            slot.candidate,
            slot.rule,
            slot.goal,
            slot.theorem,
            slot.theorem_vars,
            slot.plans,
            slot.depth,
            slot.position,
            slot.bindings,
            slot.snapshots,
            slot.selected,
            slot.generated,
            slot.hook,
            slot.derived,
            slot.counters,
            slot.fuel,
            slot.candidates,
            raw_target,
        );
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

    const candidates_before = slot.candidates.items.len;

    // Register the witness metas threaded in from enclosing open slots BEFORE
    // taking the rollback mark, so the registration survives the per-pass
    // rollbacks below: every pass (concrete-member, child `solveOpen`, coupled)
    // needs the ancestor leaves bindable, and `solveOpen`'s hint reintern bails
    // outright on an unregistered meta. Registration is trailed and unwound by
    // `tryOpenGenerateSlot`'s outer mark, so it does not leak past this slot.
    // Only `.witness` open slots carry witness metas.
    if (slot.mode == .witness) {
        try registerAncestorMetas(slot.store, theorem, raw_target);
    }

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
        if (slot.candidates.items.len != candidates_before) return;
        slot.store.rollbackTo(mark);
        if (try slot.hook.solveOpen(raw_target, theorem, slot.store)) |proof| {
            try continueOpenTargetSolved(slot, raw_target, unknowns, view, view_bindings, proof);
            if (slot.candidates.items.len != candidates_before) return;
        }
        slot.store.rollbackTo(mark);
        try tryCoupledWitnesses(slot, raw_target, unknowns, view, view_bindings);
        if (slot.candidates.items.len != candidates_before) return;
        // Last resort: the witness is genuinely free — invent it from the
        // `@vars` pool. The flag is set whenever the theory has a pool; the
        // forced passes above stay the default because they run first and
        // this rung is reached only when they leave metas unsolved.
        if (slot.hook.allow_invent_witness) {
            slot.store.rollbackTo(mark);
            try tryVarPoolWitnesses(slot, raw_target, unknowns, view, view_bindings);
        }
        return;
    }

    // Witness-free open target (e.g. `@abstract` motive inference): keep the
    // original child-search-first ordering, with member/coupled witness
    // enumeration as the fallback.
    if (try slot.hook.solveOpen(raw_target, theorem, slot.store)) |proof| {
        try continueOpenTargetSolved(slot, raw_target, unknowns, view, view_bindings, proof);
        if (slot.candidates.items.len != candidates_before) return;
    }
    slot.store.rollbackTo(mark);
    try tryAcuiMemberWitnesses(slot, raw_target, unknowns, view, view_bindings, true);
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
    const theorem = &slot.candidate.theorem;
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
    defer flagged.deinit(slot.allocator);
    var solve_failed = false;
    if (view) |v| {
        const vb = try slot.allocator.dupe(?ExprId, view_bindings.?);
        defer slot.allocator.free(vb);
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
        if (!solve_failed) {
            for (v.binder_map, 0..) |maybe_rule_idx, vi| {
                const rule_idx = maybe_rule_idx orelse continue;
                if (rule_idx >= slot.bindings.len) continue;
                if (slot.bindings[rule_idx] != null) continue;
                const value = vb[vi] orelse continue;
                slot.bindings[rule_idx] = value;
                try flagged.append(slot.allocator, .{ .idx = rule_idx, .orig = null });
            }
        }
    } else {
        for (unknowns, 0..) |maybe_meta, idx| {
            const meta = maybe_meta orelse continue;
            const value = slot.store.materialize(theorem, meta) catch {
                solve_failed = true;
                break;
            };
            if (slot.bindings[idx] == null) {
                slot.bindings[idx] = value;
                try flagged.append(slot.allocator, .{ .idx = idx, .orig = null });
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
        for (slot.bindings, 0..) |maybe_val, idx| {
            const val = maybe_val orelse continue;
            var already = false;
            for (flagged.items) |f| {
                if (f.idx == idx) {
                    already = true;
                    break;
                }
            }
            if (already) continue;
            if (!slot.store.exprMentionsAncestor(theorem, val)) continue;
            const concrete = slot.store.materialize(theorem, val) catch continue;
            if (concrete == val) continue;
            slot.bindings[idx] = concrete;
            try flagged.append(slot.allocator, .{ .idx = idx, .orig = val });
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
        for (slot.bindings, 0..) |maybe_val, idx| {
            const val = maybe_val orelse continue;
            var already = false;
            for (flagged.items) |f| {
                if (f.idx == idx) {
                    already = true;
                    break;
                }
            }
            if (already) continue;
            try flagged.append(slot.allocator, .{ .idx = idx, .orig = val });
        }
    }
    defer for (flagged.items) |f| {
        slot.bindings[f.idx] = f.orig;
    };
    if (solve_failed) return;

    // Same incremental prune as the pool-ref loop: a fill whose pinned
    // binders contradict the conclusion-vs-goal correspondence dooms every
    // tuple under it.
    if (!finalConclusionPlausible(slot.context, slot.candidate, slot.goal, slot.bindings, slot.counters)) {
        if (slot.counters) |c| c.final_conclusion_prunes += 1;
        return;
    }

    const flag_restores = try slot.allocator.alloc(?bool, flagged.items.len);
    defer slot.allocator.free(flag_restores);
    for (flagged.items, 0..) |f, i| {
        flag_restores[i] = try setMetaSolvedFlag(slot.candidate, f.idx);
    }
    defer for (flagged.items, 0..) |f, i| {
        restoreMetaSolvedFlag(slot.candidate, f.idx, flag_restores[i]);
    };

    if (proof) |p| {
        slot.generated[slot.position] = p.application;
        defer slot.generated[slot.position] = null;
        try backtrackRefs(
            slot.compiler,
            slot.allocator,
            slot.context,
            slot.ref_index,
            slot.pool,
            slot.candidate,
            slot.rule,
            slot.goal,
            slot.theorem,
            slot.theorem_vars,
            slot.plans,
            slot.depth + 1,
            slot.bindings,
            slot.snapshots,
            slot.selected,
            slot.generated,
            slot.hook,
            slot.derived,
            slot.counters,
            slot.fuel,
            slot.candidates,
            null,
        );
        return;
    }
    try emitGeneratedSlot(
        slot.compiler,
        slot.allocator,
        slot.context,
        slot.ref_index,
        slot.pool,
        slot.candidate,
        slot.rule,
        slot.goal,
        slot.theorem,
        slot.theorem_vars,
        slot.plans,
        slot.depth,
        slot.position,
        slot.bindings,
        slot.snapshots,
        slot.selected,
        slot.generated,
        slot.hook,
        slot.derived,
        slot.counters,
        slot.fuel,
        slot.candidates,
        concrete_target,
    );
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
    const theorem = &slot.candidate.theorem;

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
        slot.context,
        theorem,
        raw_target,
        &members,
    );

    // Distinct materialized targets already attempted: two members often
    // propose the same fill (shared subterms), and one child solve per
    // distinct fill is enough.
    var seen: [max_member_witness_attempts]ExprId = undefined;
    var attempts: usize = 0;
    const before_concrete = slot.candidates.items.len;
    for (members[0..member_count]) |member| {
        for (fragments[0..fragment_count]) |fragment| {
            if (attempts >= max_member_witness_attempts) break;
            const mark = slot.store.mark();
            if (!Witness.matchFragmentToMember(
                slot.context,
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
    if (try_coupled and slot.candidates.items.len == before_concrete) {
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
    const theorem = &slot.candidate.theorem;
    if (!slot.store.isFullySolved(theorem, raw_target)) return;
    const concrete = slot.store.materialize(theorem, raw_target) catch return;
    for (seen[0..attempts.*]) |prior| {
        if (prior == concrete) return;
    }
    seen[attempts.*] = concrete;
    attempts.* += 1;
    if (slot.counters) |c| c.acui_witness_attempts += 1;
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
    const theorem = &slot.candidate.theorem;

    // Carry-to-leaf: register any ancestor witness metas (stable-`meta_id`
    // leaves threaded in from an enclosing open slot) so the unification can
    // bind them here. Done only on this fallback so the concrete member pass
    // above stays byte-identical. No-op unless the shared `meta_id` counter is
    // active (the generation recursion).
    try registerAncestorMetas(slot.store, theorem, raw_target);

    var members: [Witness.max_domain_members]ExprId = undefined;
    const member_count = Witness.collectMetaMembers(
        slot.context,
        slot.store,
        theorem,
        raw_target,
        &members,
    );
    if (member_count < 2) return;
    const before_coupled = slot.candidates.items.len;
    var seen: [max_member_witness_attempts]ExprId = undefined;
    var attempts: usize = 0;
    for (members[0..member_count], 0..) |a, i| {
        for (members[0..member_count], 0..) |b, j| {
            if (i >= j) continue;
            if (attempts >= max_member_witness_attempts) return;
            const mark = slot.store.mark();
            if (Witness.unifyMembers(slot.store, theorem, a, b)) {
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

    // Complementary closure: no pair unifies EQUAL, but a hypothesis-free
    // rule may declare a complementation — `ax`'s `⊢ a , (¬ a) , d` repeats
    // binder `a` across two members — so two meta-bearing goal members
    // related by the repeated binder (`¬ R ?x y` vs `R z ?w`, both `rex`
    // witness outputs with no rigid anchor) are co-solved through the
    // template pair. The shapes come from the visible rule templates alone;
    // the engine never knows the wrapper means negation. Runs only when the
    // equal-unify sweep emitted nothing, so existing outcomes are untouched,
    // and every fill is revalidated by the child search plus `tryCandidate`.
    if (slot.candidates.items.len != before_coupled) return;
    var shapes: [Witness.max_complement_shapes]Witness.ComplementShape = undefined;
    const shape_count = Witness.collectComplementShapes(slot.context, &shapes);
    if (shape_count == 0) return;
    for (members[0..member_count], 0..) |member_a, i| {
        for (members[0..member_count], 0..) |member_b, j| {
            if (i == j) continue;
            for (shapes[0..shape_count]) |shape| {
                if (attempts >= max_member_witness_attempts) return;
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
                        &seen,
                        &attempts,
                    );
                }
                slot.store.rollbackTo(mark);
            }
        }
    }
}

/// Invented-witness fallback (the ladder's last rung, `allow_invent_witness`,
/// set whenever the theory has a `@vars` pool): an open
/// target still carrying unsolved existential metas after the concrete-member
/// and coupled passes has a *genuinely free* witness — e.g. the `y` in
/// `(∀x P x) → (∃y P y)`, which any domain element satisfies. The calculus is
/// sound only over a non-empty domain, so completeness here requires *picking*
/// a witness rather than forcing one. We ground every unsolved meta to a reused
/// `@vars`-pool DUMMY of its sort — the "diagonal" assignment, which also
/// realizes any equality the proof implies between the metas (the lall
/// instantiation and rex witness in `all_ex_inst` must coincide). Nothing is
/// minted: the dummy is a pre-materialized pool token (generate.zig), reinterned
/// by `internParsedExpr`, so no dependency bit is consumed however many slots
/// request a witness. One witness per sort is committed (the first pool dummy
/// the dep-mask check accepts); pool dummies are otherwise interchangeable.
/// `tryCandidate` revalidates every fill.
fn tryVarPoolWitnesses(
    slot: *OpenSlot,
    raw_target: ExprId,
    unknowns: []const ?ExprId,
    view: ?types.ViewDecl,
    view_bindings: ?[]const ?ExprId,
) anyerror!void {
    const theorem = &slot.candidate.theorem;

    var unsolved = std.ArrayListUnmanaged(PlaceholderId){};
    defer unsolved.deinit(slot.allocator);
    try slot.store.collectUnsolved(theorem, raw_target, &unsolved);
    if (unsolved.items.len == 0) return;

    const mark = slot.store.mark();
    // Assign each unsolved meta a `@vars`-pool dummy of its sort. Try the pool
    // (in deterministic, sorted token order) and take the first dummy that
    // `assign` accepts: its dependency-mask check is the theory-agnostic guard
    // against picking a witness that would capture an in-scope bound variable
    // (a dummy whose deps exceed the meta's `allowed_deps` is rejected). Trying
    // in a fixed order from the *target* makes the coupled slots of one chain
    // pick the SAME witness, so the implied equality between the metas (e.g.
    // `all_ex_inst`'s lall and rex witnesses) holds. A meta whose sort has no
    // acceptable pool token cannot be invented — bail (the branch just fails).
    for (unsolved.items) |meta_id| {
        const meta = slot.store.info(meta_id) orelse {
            slot.store.rollbackTo(mark);
            return;
        };
        if (!assignPoolWitness(slot, theorem, meta_id, meta.sort_name)) {
            slot.store.rollbackTo(mark);
            return;
        }
    }
    if (!slot.store.isFullySolved(theorem, raw_target)) {
        slot.store.rollbackTo(mark);
        return;
    }
    // The witness metas are now solved. Continue exactly like the member- and
    // coupled-witness passes: `continueOpenTargetSolved` pins the parent's
    // witness binder from the solved meta, flags it for explicit-binding
    // rendering (so the inline witness rule states `(t := …)` — the witness is
    // not inferable from a freshly generated premise, only from a pooled one),
    // and resumes the backtrack. Unlike `emitGeneratedSlot`, this renders the
    // binding, which the validator requires (a bare generated `lall`/`rex`
    // leaves the witness unassigned → `MissingBinderAssignment`).
    if (slot.counters) |c| c.var_pool_witness_attempts += 1;
    try continueOpenTargetSolved(
        slot,
        raw_target,
        unknowns,
        view,
        view_bindings,
        null,
    );
    slot.store.rollbackTo(mark);
}

/// Assign `meta_id` a `@vars`-pool dummy of `sort_name`, trying tokens in sorted
/// order and committing the first that `store.assign` accepts (its dep-mask /
/// sort / occurs checks reject a witness that would capture an in-scope bound
/// variable). Returns true on success. The dummies were pre-materialized into
/// the work theorem (generate.zig) and registered in `theorem_vars`; reinterning
/// the parser var here is dependency-free. A successful `assign` records a trail
/// entry; a rejected one records nothing, so the caller's single mark/rollback
/// covers the whole loop.
fn assignPoolWitness(
    slot: *OpenSlot,
    theorem: *TheoremContext,
    meta_id: PlaceholderId,
    sort_name: []const u8,
) bool {
    // Gather matching tokens, then try in sorted order (the HashMap iteration
    // order is unspecified; the pool is small).
    var tokens: [32][]const u8 = undefined;
    var count: usize = 0;
    var it = slot.context.sort_vars.tokens.iterator();
    while (it.next()) |entry| {
        if (!std.mem.eql(u8, entry.value_ptr.sort_name, sort_name)) continue;
        if (count >= tokens.len) break;
        tokens[count] = entry.key_ptr.*;
        count += 1;
    }
    std.mem.sort([]const u8, tokens[0..count], {}, struct {
        fn lt(_: void, a: []const u8, b: []const u8) bool {
            return std.mem.order(u8, a, b) == .lt;
        }
    }.lt);
    for (tokens[0..count]) |token| {
        const parser_var = slot.theorem_vars.get(token) orelse continue;
        const dummy = theorem.internParsedExpr(parser_var) catch continue;
        slot.store.assign(theorem, meta_id, dummy) catch continue;
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

/// Set the candidate's meta-solved flag for one rule binder, returning the
/// previous value for restoration (null when the flag array did not exist
/// before — restoration then just clears the bit).
fn setMetaSolvedFlag(candidate: *ApplyCandidate, idx: usize) !?bool {
    const flags = blk: {
        if (candidate.meta_solved) |flags| break :blk flags;
        const flags = try candidate.allocator.alloc(bool, candidate.bindings.len);
        @memset(flags, false);
        candidate.meta_solved = flags;
        break :blk flags;
    };
    if (idx >= flags.len) return null;
    const prev = flags[idx];
    flags[idx] = true;
    return prev;
}

fn restoreMetaSolvedFlag(
    candidate: *ApplyCandidate,
    idx: usize,
    prev: ?bool,
) void {
    const flags = candidate.meta_solved orelse return;
    if (idx >= flags.len) return;
    flags[idx] = prev orelse false;
}
