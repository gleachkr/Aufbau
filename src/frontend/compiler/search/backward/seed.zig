const std = @import("std");
const types = @import("../types.zig");
const def_match = @import("./def_match.zig");
const lockstep = @import("./lockstep.zig");
const acui = @import("./acui.zig");
const ExprId = @import("../../../expr.zig").ExprId;
const PlaceholderId = @import("../../../expr.zig").PlaceholderId;
const TheoremContext = @import("../../../expr.zig").TheoremContext;
const TemplateExpr = @import("../../../rules.zig").TemplateExpr;
const templateBinderMask = @import("./plan.zig").templateBinderMask;
const TemplateBinderMask = @import("./plan.zig").TemplateBinderMask;

const Goal = types.Goal;
const Context = types.Context;
const ApplyCandidate = types.ApplyCandidate;
const defBodyForUnfold = def_match.defBodyForUnfold;
const rigidExprMismatch = def_match.rigidExprMismatch;
const acuiBoundMembersPlausible = acui.acuiBoundMembersPlausible;
const bag = @import("./bag.zig");
const bindAcuiSpineToUnit = acui.bindAcuiSpineToUnit;

pub fn makeExactRuleCandidate(
    allocator: std.mem.Allocator,
    context: *const Context,
    goal: Goal,
    theorem: *const TheoremContext,
    rule_id: u32,
) !ApplyCandidate {
    const rule_idx: usize = @intCast(rule_id);
    const rule = context.env.rules.items[rule_idx];
    const bindings = try allocator.alloc(?ExprId, rule.args.len);
    errdefer allocator.free(bindings);
    @memset(bindings, null);
    // Clone before seeding. `seedBindingsFromGoal` may unfold a transparent-def
    // goal head (`partialMatchTemplate`), which interns the unfolded body, so it
    // needs a mutable interner whose ids remain valid for the candidate's later
    // ref/shape lookups. Clone preserves every existing id, so the goal and the
    // extracted bindings stay valid against this same interner.
    var candidate_theorem = try theorem.clone();
    errdefer candidate_theorem.deinit();
    const slot_mark = candidate_theorem.depSlotMark();
    try seedBindingsFromGoal(context, &candidate_theorem, goal, rule_id, bindings);
    // Scrub seeded rule bindings that cannot serve as a rigid constraint:
    //
    //   * The rule-binding seed unfolds binder-introducing goal defs (so a
    //     folded subject like `add_suc_right_p m n` exposes its body and pins
    //     the rule's binders). The unfold materializes the def's bound vars as
    //     fresh STANDARD placeholders; a binder pinned to a placeholder-laden
    //     subterm (e.g. the step term `s`, mentioning the def's bound `ih`)
    //     must not reach validation/emission as a raw placeholder.
    //     `partitionSeedBindings` keeps such terms (and shared dummies) as
    //     reconciliation metas and scrubs the other bare dummies.
    //
    //   * A goal hint from open backward generation carries
    //     meta-class wildcard leaves (lifted open targets). A binder pinned to
    //     a *bare* meta leaf constrains nothing — scrub it.
    //
    // A binder pinned to a rigid app whose only placeholders are meta-class is
    // KEPT (carry-to-leaf): its rigid structure constrains the match, and the
    // embedded ancestor-witness metas ride forward to the open leaf where they
    // are solved (e.g. `rex`'s context `g := … , R ?t v` carries the `lall`
    // witness so the coupled `ax` member identity can force it). Concrete goals
    // never contain meta-class leaves, so for the whole non-meta corpus only
    // the unfolded-dummy partition above applies.
    try partitionSeedBindings(
        allocator,
        &candidate_theorem,
        rule.hyps,
        bindings,
    );
    const unresolved = try allocator.alloc(
        types.UnresolvedHypothesis,
        rule.hyps.len,
    );
    errdefer allocator.free(unresolved);
    for (unresolved, 0..) |*hyp, idx| {
        hyp.* = .{ .index = idx, .expected = null };
    }
    const view_concl_seed = try makeViewConclSeed(
        allocator,
        context,
        &candidate_theorem,
        goal,
        rule_id,
    );
    errdefer if (view_concl_seed) |seed| allocator.free(seed);
    // Seeding mints a placeholder for each hidden variable of a def it
    // unfolds, and the partition scrubs most of them. Keep only the slots the
    // candidate still holds.
    candidate_theorem.releaseUnheldDepSlots(
        slot_mark,
        &.{ bindings, view_concl_seed orelse &.{} },
    );
    return .{
        .allocator = allocator,
        .rule_id = rule_id,
        .rule_name = rule.name,
        .declaration_order = rule_idx,
        .theorem = candidate_theorem,
        .bindings = bindings,
        .conclusion = 0,
        .unresolved_hyps = unresolved,
        .view_concl_seed = view_concl_seed,
    };
}

// Upper bound on principal fan-out: beyond this we keep the single loose
// candidate (still complete, just slow) rather than emit a large candidate set.
// Real sequents have a handful of same-headed members; the cap only guards
// against a pathological context.
const max_principal_fanout: usize = 8;

// Candidate creation for `exactRuleCandidates`, with principal-formula fan-out.
//
// The plain seed leaves a branching rule's principal binders (`lor`'s a,b,
// `lim`'s a,b, …) UNBOUND when the goal's antecedent holds several members of
// the principal's connective head, because a single bindings array cannot
// represent "the principal is EITHER of these members". The backtracker then
// pins them from loose pool matches and burns ~98% of its budget on doomed
// two-premise tuples (seen in the additive_fol stress battery). Here we detect
// that ambiguity and emit one tightly-seeded candidate per legal principal
// member instead — turning an O(pool^premises) loose search into bounded
// principal selection.
//
// Result-neutral where it fires: `exactWithSession` collects every accepted
// candidate and sorts, so the fan-out reaches exactly the same accepted proofs
// (the principal must be one of the enumerated members) without the doomed
// tuples — the post-sort top-k is unchanged. It fires only on the previously
// abstaining `matches > 1` case AND under three gates (`detectPrincipalFanout`
// + `findAmbiguousPrincipal`): the rule is multi-premise, the ambiguous
// principal sits in a commutative-ACUI context, and every member is fully rigid
// (so the read-only enumeration is exhaustive). Otherwise the single loose
// candidate is kept verbatim — the whole def-heavy corpus is byte-identical.
pub fn appendRuleCandidates(
    list: *std.ArrayListUnmanaged(ApplyCandidate),
    allocator: std.mem.Allocator,
    context: *const Context,
    goal: Goal,
    theorem: *const TheoremContext,
    rule_id: u32,
) !void {
    var base = try makeExactRuleCandidate(allocator, context, goal, theorem, rule_id);
    var base_consumed = false;
    errdefer if (!base_consumed) base.deinit();

    if (try detectPrincipalFanout(allocator, context, &base, goal, rule_id)) |plan| {
        defer allocator.free(plan.members);
        if (plan.members.len >= 2 and plan.members.len <= max_principal_fanout) {
            for (plan.members) |member| {
                var variant = try cloneCandidateWithPrincipalPin(
                    allocator,
                    context,
                    &base,
                    plan.leaf,
                    member,
                );
                list.append(allocator, variant) catch |err| {
                    variant.deinit();
                    return err;
                };
            }
            base.deinit();
            base_consumed = true;
            return;
        }
    }

    try list.append(allocator, base);
    base_consumed = true;
}

// Scan the rule conclusion for an ambiguous principal ACUI member (the
// `matches > 1` case the member seed abstains on). Walks the conclusion template
// against the concrete goal in lockstep through plain `app` nodes (e.g. the
// `seq` of `g , (a ∨ b) ⊢ d`); at a commutative ACUI combiner (the
// antecedent/succedent `join`) it enumerates the goal's shape-compatible members
// for the first unbound principal leaf. No annotation coupling — completeness is
// guarded structurally by `findAmbiguousPrincipal`'s rigid-member gate.
fn detectPrincipalFanout(
    allocator: std.mem.Allocator,
    context: *const Context,
    base: *ApplyCandidate,
    goal: Goal,
    rule_id: u32,
) !?acui.PrincipalFanout {
    // Exclude view rules: their goal was matched against the *view* conclusion,
    // so the raw `rule.concl` need not line up positionally with the goal for
    // this lockstep walk (mirrors `conclusionMembersPlausible`).
    if (context.views.contains(rule_id)) return null;
    const rule = &context.env.rules.items[@intCast(rule_id)];
    // Only multi-premise rules explode: an unbound principal makes each loose
    // premise match the pool ~freely, so the doomed-tuple cost is O(pool^hyps)
    // — super-linear only for hyps ≥ 2 (`lim`/`lor`'s two near-universal
    // premises). A one-premise rule's loose backtrack is already linear, so
    // fanning it just multiplies candidates (and node-budget pressure) with no
    // search-space win — exactly the spurious overhead that tips the
    // budget-edge `drinker` case. Restrict to where the explosion lives.
    if (rule.hyps.len < 2) return null;
    const goal_expr = goal.concreteOrHint() orelse return null;
    return walkForFanout(
        allocator,
        context,
        &base.theorem,
        rule.concl,
        goal_expr,
        base.bindings,
    );
}

fn walkForFanout(
    allocator: std.mem.Allocator,
    context: *const Context,
    theorem: *TheoremContext,
    template: TemplateExpr,
    expr_id: ExprId,
    bindings: []const ?ExprId,
) anyerror!?acui.PrincipalFanout {
    // Enumerate the ambiguous principal at the first commutative ACUI combiner
    // (the sequent's antecedent/succedent `join`) that has one, descending
    // plain terms (`seq`, `hyp`, …) through the args the goal forces.
    const Fanout = struct {
        allocator: std.mem.Allocator,
        context: *const Context,
        theorem: *TheoremContext,
        bindings: []const ?ExprId,
        fan: ?acui.PrincipalFanout = null,
        err: ?anyerror = null,

        pub fn binder(_: *@This(), _: usize, _: ExprId) bool {
            return false;
        }

        pub fn combiner(self: *@This(), app: TemplateExpr.App, expr: ExprId) bool {
            self.fan = acui.findAmbiguousPrincipal(
                self.allocator,
                self.context,
                self.theorem,
                app.term_id,
                .{ .app = app },
                expr,
                self.bindings,
            ) catch |err| {
                self.err = err;
                return true;
            };
            return self.fan != null;
        }
    };
    var fanout = Fanout{
        .allocator = allocator,
        .context = context,
        .theorem = theorem,
        .bindings = bindings,
    };
    _ = lockstep.walk(context, theorem, template, expr_id, &fanout);
    if (fanout.err) |err| return err;
    return fanout.fan;
}

// Clone `base` and additionally pin the principal `leaf`'s binders from one
// enumerated `member`, yielding a fan-out variant. The clone's interner shares
// `base`'s ids (copy-on-write), so `member` and the subterms
// `extractHypPartialBindings` reads off it stay valid. No seed scrub is needed:
// `findAmbiguousPrincipal`'s rigid-member gate (`exprFullyRigid`) admits only a
// placeholder-free `member` whose every head is rigid. Extraction mints
// placeholders only by unfolding a ref-side def (`defBodyForUnfold`), which
// needs a def with a body, and no rigid head is one. So every pin is a concrete
// subterm of `member`. Re-running `partitionSeedBindings` would do harm: it
// would scrub the bare reconciliation metas the base seed's partition kept.
// View rules are excluded upstream (`detectPrincipalFanout`), so
// `base.view_concl_seed` is null on this path.
fn cloneCandidateWithPrincipalPin(
    allocator: std.mem.Allocator,
    context: *const Context,
    base: *const ApplyCandidate,
    leaf: TemplateExpr,
    member: ExprId,
) !ApplyCandidate {
    var candidate_theorem = try base.theorem.clone();
    errdefer candidate_theorem.deinit();
    const bindings = try allocator.dupe(?ExprId, base.bindings);
    errdefer allocator.free(bindings);
    const slot_mark = candidate_theorem.depSlotMark();
    def_match.extractHypPartialBindings(
        context,
        &candidate_theorem,
        leaf,
        member,
        bindings,
    );
    // Extraction unfolded no def inside the rigid `member`.
    std.debug.assert(candidate_theorem.depSlotMark() == slot_mark);
    // The variant's COW clone borrows `base.theorem` as its immutable base, but
    // `appendRuleCandidates` deinits `base` as soon as the variants are built —
    // the variants outlive it. Materialize a standalone interner so the variant
    // owns its full id-space and never dangles into the freed `base`.
    try candidate_theorem.flatten();
    const unresolved = try allocator.dupe(
        types.UnresolvedHypothesis,
        base.unresolved_hyps,
    );
    errdefer allocator.free(unresolved);
    // The reconciliation-meta flag travels with each leaf through the COW clone,
    // and the duped bindings carry the same leaves, so the variant reconciles
    // them too with no extra bookkeeping.
    return .{
        .allocator = allocator,
        .rule_id = base.rule_id,
        .rule_name = base.rule_name,
        .declaration_order = base.declaration_order,
        .theorem = candidate_theorem,
        .bindings = bindings,
        .conclusion = 0,
        .unresolved_hyps = unresolved,
        .view_concl_seed = null,
    };
}

// Solve the view's binders by matching its conclusion against the goal. The
// result is indexed in view-binder space and retains phantom binders (those
// with no corresponding rule binder), which the `@recover` pruning guard
// needs. Returns null when the rule has no view or the goal is not concrete.
fn makeViewConclSeed(
    allocator: std.mem.Allocator,
    context: *const Context,
    theorem: *TheoremContext,
    goal: Goal,
    rule_id: u32,
) !?[]const ?ExprId {
    const view = context.views.get(rule_id) orelse return null;
    const goal_expr = goal.concreteOrHint() orelse return null;
    const seed = try allocator.alloc(?ExprId, view.num_binders);
    errdefer allocator.free(seed);
    @memset(seed, null);
    // Extract whatever view binders line up structurally against the goal,
    // unfolding a transparent-def goal head (binder-introducing defs included)
    // when it hides the view's conclusion shape. For `ex_intro`, the goal
    // `has_preimage f A y` unfolds to `∃ x (x∈A ∧ maps f x y)`, pinning the
    // view's existential-body binder `p`. That `p` is exactly the `pattern` the
    // `@recover` guard needs to reject hypotheses whose wff cannot be the body,
    // turning the otherwise-loose `$ G ⊢ q $` view hyp back into a
    // discriminating one. Interns into `theorem` (the candidate's clone), so the
    // seed's placeholder/unfolded ids stay valid for the later hyp-match guard.
    try partialMatchTemplate(context, theorem, view.concl, goal_expr, seed, true, false);
    // A view binder pinned to a *bare* meta-class wildcard from an open goal
    // hint constrains nothing and must not reach the recover guard or
    // hypothesis matching as a rigid value — scrub it. A binder pinned to a
    // rigid context that merely embeds an ancestor-witness meta (carry-to-leaf)
    // is kept: its structure still discriminates, and the meta rides forward.
    // The view seed deliberately keeps STANDARD placeholders (def-unfold
    // dummies the recover guard needs), so only bare meta leaves are dropped.
    for (seed) |*entry| {
        const value = entry.* orelse continue;
        if (isBareMetaLeaf(theorem, value)) entry.* = null;
    }
    return seed;
}

/// The expression is itself a single meta-class placeholder leaf (an open
/// backward-generation hole). Such a binding constrains nothing.
fn isBareMetaLeaf(theorem: *const TheoremContext, expr_id: ExprId) bool {
    return switch (theorem.interner.node(expr_id).*) {
        .placeholder => |pid| theorem.placeholderClass(pid) == .meta,
        else => false,
    };
}

/// True when `expr_id` mentions a STANDARD (non-meta) placeholder anywhere —
/// a def-unfold dummy that must not survive as a rigid rule binding.
fn exprContainsStandardPlaceholder(
    theorem: *const TheoremContext,
    expr_id: ExprId,
) bool {
    return theorem.exprAny(expr_id, {}, standardPlaceholderPred);
}

/// A seed value that holds a meta leaf or a def-unfold dummy, and so could
/// still equal a different concrete value.
fn seedValueIsLoose(theorem: *const TheoremContext, expr_id: ExprId) bool {
    return theorem.containsMetaLeaf(expr_id) or
        exprContainsStandardPlaceholder(theorem, expr_id);
}

fn standardPlaceholderPred(_: void, theorem: *const TheoremContext, expr_id: ExprId) bool {
    return switch (theorem.interner.node(expr_id).*) {
        .placeholder => |pid| theorem.placeholderClass(pid) != .meta,
        else => false,
    };
}

/// Whether `partitionSeedBindings` must decide a seeded rule binding: a bare
/// placeholder leaf (meta hole or def-unfold dummy), or a value embedding a
/// standard def-unfold placeholder, which must not reach validation/emission
/// as it stands. It either keeps such a value, with its dummies turned into
/// shared metas, or scrubs it to null. Concrete values and rigid apps whose
/// only placeholders are meta-class pass through untouched (carry-to-leaf).
fn needsSeedPartition(theorem: *const TheoremContext, expr_id: ExprId) bool {
    return switch (theorem.interner.node(expr_id).*) {
        .variable => false,
        .placeholder => true,
        .app => exprContainsStandardPlaceholder(theorem, expr_id),
    };
}

/// Resolve the def-unfold dummies in the seeded rule bindings (the keystone of
/// eliminator metavar reconciliation).
///
/// The seed pins a rule's binders by matching its conclusion against a
/// transparent-def-unfolded goal; the unfold materializes the def's bound
/// variables as fresh STANDARD placeholders (`add_comm_p`'s `{.k .ih}`), so the
/// binders land on dummy-laden values. The legacy behaviour scrubbed every such
/// binding to null. Instead we partition them:
///
///   * a binder holding a **term** that mentions dummies (a motive, the step
///     term `s` under `k` and `ih`) keeps it: the term fixes its premises'
///     subjects. Every occurrence of one dummy, in any kept binding, becomes
///     ONE shared meta leaf, so a meta-aware ref-match on any hypothesis
///     (`match.tryMetaAwareHypMatch`) pins it for all the others. A dummy no
///     ref pins by the time its premise is generated opens there as a bound
///     variable (`backtrack.tryFreshBoundGenerate`). One no binder holds (the
///     `λ` variable inside `id_trans`'s unfolded `J` term) can only be pinned
///     by a ref; keeping such terms measured neutral against scrubbing them,
///     so they get no special case;
///   * a binder holding a **bare dummy** keeps it when the binder occurs in
///     more than one hypothesis (an induction variable threaded across them)
///     or a kept term mentions the dummy (`ih` under `s`), so the meta stays
///     shared;
///   * any other bare dummy is local to its one hypothesis (its
///     witness/output); scrub it to null so it reconciles at its own generated
///     slot via the open path.
///
/// Concrete (meta-free) goals never expose dummies, so for the whole non-eliminator
/// corpus the `needsSeedPartition` gate skips every binding and this is a no-op.
/// The kept metas are flagged `reconciliation_meta` on their interner leaf, so the
/// meta-aware match (`match.tryMetaAwareHypMatch`) targets exactly these and
/// never disturbs carry-to-leaf metas — no candidate-side bookkeeping needed.
pub fn partitionSeedBindings(
    allocator: std.mem.Allocator,
    theorem: *TheoremContext,
    hyps: []const TemplateExpr,
    bindings: []?ExprId,
) !void {
    const multi = multiHypBinderMask(hyps);
    // Shared per-dummy meta map: one meta leaf per distinct def-unfold dummy id,
    // so repeated occurrences of a dummy (in its own slot and inside other kept
    // bindings) all become the SAME meta and resolve together.
    var dummy_metas = std.AutoHashMapUnmanaged(PlaceholderId, ExprId){};
    defer dummy_metas.deinit(allocator);
    // Dummies some kept term mentions.
    var term_dummies = DummySet{ .allocator = allocator };
    defer term_dummies.set.deinit(allocator);
    for (bindings) |binding| {
        const value = binding orelse continue;
        if (theorem.interner.node(value).* != .app) continue;
        try theorem.exprForEach(value, &term_dummies, DummySet.visit);
    }
    for (bindings, 0..) |*binding, idx| {
        const value = binding.* orelse continue;
        if (!needsSeedPartition(theorem, value)) continue; // concrete / meta-only
        // A bare meta leaf constrains nothing — scrub it (baseline behavior),
        // regardless of the multi-hyp keep below. `rewriteDummiesToSharedMetas`
        // would otherwise return it unchanged (it only converts STANDARD
        // dummies), keeping an unresolved, non-reconciliation pin the meta-aware
        // match never touches.
        if (isBareMetaLeaf(theorem, value)) {
            binding.* = null;
            continue;
        }
        const keep = !multi.overflow and switch (theorem.interner.node(value).*) {
            .app => true,
            .placeholder => |pid| term_dummies.set.contains(pid) or
                (idx < 64 and multi.mask & (@as(u64, 1) << @intCast(idx)) != 0),
            .variable => unreachable, // `needsSeedPartition` passes no variable
        };
        if (keep) {
            binding.* = try rewriteDummiesToSharedMetas(
                allocator,
                theorem,
                value,
                &dummy_metas,
            );
        } else {
            binding.* = null;
        }
    }
}

/// The standard placeholders (def-unfold dummies) an `exprForEach` walk meets.
const DummySet = struct {
    allocator: std.mem.Allocator,
    set: std.AutoHashMapUnmanaged(PlaceholderId, void) = .{},

    fn visit(self: *DummySet, theorem: *const TheoremContext, expr_id: ExprId) !void {
        switch (theorem.interner.node(expr_id).*) {
            .placeholder => |pid| if (theorem.placeholderClass(pid) != .meta) {
                try self.set.put(self.allocator, pid, {});
            },
            else => {},
        }
    }
};

/// Bits set for binder indices occurring in more than one hypothesis. Overflow
/// (a binder index ≥ 64) disables the keep entirely — the caller then scrubs as
/// before — rather than risk a wrong mask decision.
pub fn multiHypBinderMask(hyps: []const TemplateExpr) TemplateBinderMask {
    var seen_once: u64 = 0;
    var seen_twice: u64 = 0;
    for (hyps) |hyp| {
        const m = templateBinderMask(hyp);
        if (m.overflow) return .{ .mask = 0, .overflow = true };
        seen_twice |= seen_once & m.mask;
        seen_once |= m.mask;
    }
    return .{ .mask = seen_twice, .overflow = false };
}

/// Rewrite every STANDARD (def-unfold dummy) placeholder in `expr_id` to a
/// shared `.meta`-class leaf, looked up/minted in `dummy_metas` by the dummy's
/// placeholder id so all occurrences of one dummy map to one meta. Meta-class
/// leaves and variables pass through unchanged.
fn rewriteDummiesToSharedMetas(
    allocator: std.mem.Allocator,
    theorem: *TheoremContext,
    expr_id: ExprId,
    dummy_metas: *std.AutoHashMapUnmanaged(PlaceholderId, ExprId),
) !ExprId {
    switch (theorem.interner.node(expr_id).*) {
        .variable => return expr_id,
        .placeholder => |pid| {
            if (theorem.placeholderClass(pid) == .meta) return expr_id;
            // Look up the sort BEFORE `getOrPut` so a null result can bail
            // without leaving an uninitialized map entry that a later
            // occurrence of `pid` would read back as garbage.
            const ph = theorem.placeholderInfo(pid) orelse return expr_id;
            const gop = try dummy_metas.getOrPut(allocator, pid);
            if (!gop.found_existing) {
                gop.value_ptr.* =
                    try theorem.addReconciliationMetaPlaceholderResolved(
                        ph.sort_name,
                        ph.deps,
                    );
            }
            return gop.value_ptr.*;
        },
        .app => |app| {
            const term_id = app.term_id;
            const args = try allocator.alloc(ExprId, app.args.len);
            defer allocator.free(args);
            @memcpy(args, theorem.interner.node(expr_id).app.args);
            var changed = false;
            for (args) |*a| {
                const r = try rewriteDummiesToSharedMetas(
                    allocator,
                    theorem,
                    a.*,
                    dummy_metas,
                );
                if (r != a.*) changed = true;
                a.* = r;
            }
            if (!changed) return expr_id;
            return theorem.interner.internApp(term_id, args);
        },
    }
}

fn seedBindingsFromGoal(
    context: *const Context,
    theorem: *TheoremContext,
    goal: Goal,
    rule_id: u32,
    bindings: []?ExprId,
) !void {
    const rule = &context.env.rules.items[rule_id];
    try seedBindingsFromTemplateGoal(
        context.allocator,
        context,
        theorem,
        rule.concl,
        goal,
        bindings,
    );
    if (context.views.get(rule_id)) |view| {
        try seedBindingsFromViewGoal(
            context.allocator,
            context,
            theorem,
            view,
            goal,
            bindings,
        );
    }
    // ACUI-sorted bindings that survive `partialMatchTemplate` are now only
    // whole-argument positional binds (it no longer descends into ACUI
    // combiner spines), so they are exact and sound to propagate. The ref
    // index consumes them as containment fingerprints (rearrangement-robust),
    // which is exactly what lets, e.g., `bot_elim`'s `g ⊢ ⊥` hypothesis reject
    // refs whose context can't match the goal's context.
}

// Conclusion-side counterpart of the per-hyp `acuiBoundMembersPlausible`
// precheck. A rule's conclusion must ACUI-equal the goal, so every concrete
// (or fully-bound) ACUI member of the conclusion template is a *necessary*
// element of the goal's corresponding multiset — regardless of any open
// context binder that absorbs the rest. For `ax` (`g, a ⊢ a`, i.e.
// `nd(join(g, hyp(a)), a)`, a 0-hyp rule) the seed pins `a` from the
// turnstile's RHS but leaves `g` open; if the goal context holds no `hyp(a)`
// member, the rule cannot apply, yet with no hypotheses to look up the
// candidate would otherwise run all the way to a doomed conclusion-side
// inference. Catching it here is the conclusion analogue of injecting the
// pinned member into the ref index. Sound: a missing required member can never
// be supplied by the open binder, so this only ever prunes truly inapplicable
// candidates; an open-binder leaf (e.g. `g`) is skipped, never demanded.
//
// View rules are excluded: there the goal was matched against the *view*
// conclusion (a different advertised surface form), so the raw `rule.concl`
// need not line up positionally with the goal, and the hyp-side `@recover`
// member injection already covers their pruning.
pub fn conclusionMembersPlausible(
    context: *const Context,
    candidate: *const ApplyCandidate,
    goal: Goal,
) bool {
    if (context.views.contains(candidate.rule_id)) return true;
    const goal_expr = goal.concreteOrHint() orelse return true;
    const rule = &context.env.rules.items[@intCast(candidate.rule_id)];
    if (conclusionRepeatedBinderConflict(
        context,
        &candidate.theorem,
        rule.concl,
        goal_expr,
        candidate.bindings.len,
    )) return false;
    return acuiBoundMembersPlausible(
        context,
        &candidate.theorem,
        rule.concl,
        goal_expr,
        candidate.bindings,
    );
}

// A rule conclusion that binds the same template variable at two positions —
// e.g. reflt's `G ⊩ ≃[A] t = t` (repeats `t`) or eq_refl's `a = a` — forces the
// corresponding ground goal subterms to coincide. Those positions are pinned
// entirely by the goal; no hypothesis can influence them. So if the goal's two
// subterms are rigidly divergent, the conclusion can't be matched no matter
// which refs the hyps draw — prune now, before enumerating refs or cloning the
// theorem. (Without this, e.g. church beta runs a full `tryCandidate` for each
// of reflt's four typing-judgment refs, all identically doomed.)
//
// Soundness: we prune only on `rigidExprMismatch`, which reports a conflict
// solely for genuine rigid-head clashes and stays silent whenever a def, ACUI
// rearrangement, or placeholder could still reconcile the two sides via
// conversion, and we descend only into arguments the head determines
// (`argDetermined`), so a `@rewrite` head or a def arg the body drops never
// forces two occurrences together. So this never rejects a candidate the
// matcher/normalizer could otherwise close. ACUI-combiner-headed and
// head-mismatched template nodes are treated as "no opinion" for the same reason. Allocation failure simply yields
// no opinion (we keep the candidate).
fn conclusionRepeatedBinderConflict(
    context: *const Context,
    theorem: *const TheoremContext,
    concl: TemplateExpr,
    goal_expr: ExprId,
    num_binders: usize,
) bool {
    const scratch = context.allocator.alloc(?ExprId, num_binders) catch return false;
    defer context.allocator.free(scratch);
    @memset(scratch, null);
    return repeatedBinderConflictWalk(context, theorem, concl, goal_expr, scratch);
}

fn repeatedBinderConflictWalk(
    context: *const Context,
    theorem: *const TheoremContext,
    template: TemplateExpr,
    expr_id: ExprId,
    bindings: []?ExprId,
) bool {
    // Only args the head determines are forced to coincide: not an ACUI
    // spine's (its association and order are arbitrary), a `@rewrite` head's,
    // or a def arg its body drops. A head/arity mismatch could be bridged by
    // unfolding, so it forms no opinion.
    const Conflict = struct {
        context: *const Context,
        theorem: *const TheoremContext,
        bindings: []?ExprId,

        pub fn binder(self: *@This(), idx: usize, expr: ExprId) bool {
            if (idx >= self.bindings.len) return false;
            if (self.bindings[idx]) |existing| {
                // Second occurrence of this template var: the goal subterms it
                // pins must coincide, or the conclusion is unsatisfiable.
                return rigidExprMismatch(self.context, self.theorem, existing, expr);
            }
            self.bindings[idx] = expr;
            return false;
        }

        pub fn combiner(_: *@This(), _: TemplateExpr.App, _: ExprId) bool {
            return false;
        }
    };
    var conflict = Conflict{ .context = context, .theorem = theorem, .bindings = bindings };
    return lockstep.walk(context, theorem, template, expr_id, &conflict) == .stopped;
}

fn seedBindingsFromTemplateGoal(
    allocator: std.mem.Allocator,
    context: *const Context,
    theorem: *TheoremContext,
    template: TemplateExpr,
    goal: Goal,
    bindings: []?ExprId,
) !void {
    const goal_expr = goal.concreteOrHint() orelse return;
    const scratch = try allocator.dupe(?ExprId, bindings);
    defer allocator.free(scratch);
    // Walk template against goal extracting whatever bindings line up
    // structurally. On head mismatch at an ACUI-rooted template node, skip
    // that subtree rather than aborting: ACUI rearrangements (e.g., the
    // rule's `g, h ⊢ c` against a goal whose context is `emp`) prevent the
    // structural matcher from succeeding even though the non-ACUI siblings
    // (the conclusion wff `c`) still align cleanly. Those siblings carry
    // most of the constraint that helps the ref index narrow later hyp
    // lookups, so it's important to extract them.
    // Unfold binder-introducing goal defs too (a folded subject like
    // `add_suc_right_p m n` exposes its `nat_ind k ih C z s n` body so the
    // rule's binders can pin). This seed feeds the *rule* bindings that drive
    // validation and emission, so the placeholders such an unfold materializes
    // must not survive as raw binds — `makeExactRuleCandidate` partitions them
    // (`partitionSeedBindings`): placeholder-laden terms and shared dummies
    // are kept as reconciliation metas, and other bare dummies are scrubbed.
    try partialMatchTemplate(context, theorem, template, goal_expr, scratch, true, true);
    _ = mergeOptionalBindings(bindings, scratch);
}

fn partialMatchTemplate(
    context: *const Context,
    theorem: *TheoremContext,
    template: TemplateExpr,
    expr_id: ExprId,
    bindings: []?ExprId,
    allow_binder_defs: bool,
    // When set, an ACUI-combiner template node (otherwise opaque to this seed)
    // also recovers binders from *forced* structured members of the goal's
    // multiset — a template member with a rigid head that lines up with exactly
    // one goal member must match it, so its internal binders are pinned. This is
    // the conclusion-seed analogue of the hyp-side `extractHypPartialBindings`
    // ACUI member pass (which this delegates to). Under a commutative combiner
    // it never pins a bare context rest-binder, so it does not commit the ACUI
    // context *split* the view seed must leave open (the documented eq_replace
    // hazard) — hence it is enabled only for the rule-conclusion seed, not the
    // view seeds. Under an ordered combiner (neither C nor I) the split is
    // unique, so the one rest-binder it may pin is forced.
    extract_members: bool,
) error{OutOfMemory}!void {
    switch (template) {
        .binder => |idx| {
            if (idx >= bindings.len) return;
            // A goal hint from open backward generation can carry meta-class
            // wildcard leaves (lifted open targets). We still bind a
            // binder to a meta-bearing goal subterm — its rigid structure is a
            // real constraint and the embedded ancestor-witness meta must ride
            // forward (carry-to-leaf, e.g. `rex`'s context `g := … , R ?t v`).
            // The repeated-binder hazard (eq_intro's `a = a` against the hint
            // `?t = 0`, where the first occurrence is meta-bearing and a later
            // one is concrete) is handled by *refinement*: a concrete
            // occurrence overrides a meta-bearing bind, never the reverse, so
            // the concrete seed validation needs survives.
            //
            // A def-unfold dummy (a standard placeholder) is loose the same
            // way: the unfolding may instantiate it to any suitable bound
            // variable. `lam_intro`'s `(λ x : A. t) : (Π x : A. B)` against
            // `(λ x : A. t) : (A → B)` meets `x` twice, once from the λ and
            // once as the arrow's hidden binder; the λ's `x` must win, not
            // null the pin as a conflict between two concretes.
            const incoming_loose = seedValueIsLoose(theorem, expr_id);
            if (bindings[idx]) |existing| {
                if (existing == expr_id) return;
                const existing_loose = seedValueIsLoose(theorem, existing);
                if (existing_loose and !incoming_loose) {
                    bindings[idx] = expr_id; // concrete refines a loose bind
                } else if (existing_loose or incoming_loose) {
                    return; // keep the standing bind; loose values are not comparable
                } else {
                    bindings[idx] = null; // two distinct concretes: real conflict
                }
                return;
            }
            bindings[idx] = expr_id;
        },
        .app => |app| {
            // An ACUI combiner's (e.g. `join`) binary spine encodes an
            // association, and under C an order, that carries no meaning,
            // so positionally descending `join(g, hyp(a))` into a goal's join
            // spine would bind `g` to whichever member happens to land first —
            // an unsound bind. Treat ACUI-combiner-headed template nodes as
            // opaque here. A *whole-argument* ACUI binder (e.g. bot_elim's
            // `g` at `nd(g, a)`, where `g` is the entire context arg, not a
            // sub-position of a join) is still bound by the `.binder` arm and
            // is exact; the ref index uses it as a containment fingerprint.
            //
            // EXCEPTION — the unit law: if the goal subterm is the combiner's
            // unit (e.g. an empty context `emp`), then `combine(g, h, …) = emp`
            // forces every summand to `emp`. Binding each spine binder to the
            // unit is sound and exact (no member can be elsewhere), and it lets
            // the closed-region check reject any ref whose context carries
            // members — e.g. `ex_elim_sub`'s `g , h ⊢ c` against `emp ⊢ c` pins
            // `g = h = emp`, so a major ref with a non-empty context, or a minor
            // ref whose context holds more than the single witness, is doomed.
            if (context.registry.hasStructuralCombiner(app.term_id)) {
                if (bag.isUnitOf(context, theorem, app.term_id, expr_id)) {
                    bindAcuiSpineToUnit(template, app.term_id, expr_id, bindings);
                }
                // Forced structured-member recovery (conclusion seed only).
                // Under C, `extractHypPartialBindings` treats the combiner's
                // args as a multiset and pins a structured leaf's binders only
                // when exactly one goal member is shape-compatible, leaving the
                // bare context rest-binder open. Under an ordered combiner it
                // aligns the member sequences instead. For rim's succedent
                // `(a→b), d` against goal `P c → P c` this pins `a = b = P c`
                // while `d` stays open for generation.
                if (extract_members) {
                    def_match.extractHypPartialBindings(
                        context,
                        theorem,
                        template,
                        expr_id,
                        bindings,
                    );
                }
                return;
            }
            const node = theorem.interner.node(expr_id);
            switch (node.*) {
                .variable, .placeholder => return,
                .app => {
                    if (lockstep.templateArgs(context, theorem, app, expr_id)) |aligned| {
                        // Same head: seed from the args it forces. A `@rewrite`
                        // head's arg or one a def drops need not match the
                        // goal's, so its value would be a guess.
                        var args = aligned;
                        while (args.next()) |pair| {
                            try partialMatchTemplate(
                                context,
                                theorem,
                                pair.template,
                                pair.expr,
                                bindings,
                                allow_binder_defs,
                                extract_members,
                            );
                        }
                        return;
                    }
                    // Head mismatch, template side. If the TEMPLATE head is a
                    // transparent first-order def whose head differs from the
                    // goal's (e.g. `bic`/`⇔` over goal `eqc`/`≃[𝔹]`), unfold the
                    // template one layer and walk its body against the same goal
                    // (`def_match.walkDefBody`), whose parameter binders resolve
                    // back to the rule-binder argument templates. Without this, a rule
                    // whose conclusion folds tighter than the goal (`ded`'s
                    // `P ⇔ Q` against a `≃[𝔹] a = b` goal) pins only the context,
                    // leaving the payload binders `P,Q` open and the per-hyp
                    // lookups broad. First-order only (`allow_binder_defs = false`
                    // here): def dummies cannot be represented as rule-binder
                    // templates, so the body walk drops them as no-opinion. The
                    // hyp-side extraction walks def bodies the same way.
                    if (defBodyForUnfold(context, app.term_id, false)) |tinfo| {
                        if (app.args.len == tinfo.nargs) {
                            const root = def_match.DefScope{
                                .nargs = tinfo.nargs,
                                .args = app.args,
                                .parent = null,
                            };
                            try def_match.walkDefBody(
                                SeedRoot{
                                    .context = context,
                                    .theorem = theorem,
                                    .bindings = bindings,
                                    .allow_binder_defs = allow_binder_defs,
                                    .extract_members = extract_members,
                                },
                                context,
                                theorem,
                                tinfo.body,
                                &root,
                                expr_id,
                                allow_binder_defs,
                                0,
                            );
                        }
                        return;
                    }
                    // Head mismatch. If the GOAL head is a transparent
                    // first-order def, its unfolding may expose the template's
                    // head — e.g. the goal `function f A B`
                    // (= `functional f ∧ (domain_on f A ∧ range_sub f B)`)
                    // against `and_intro`'s `p ∧ q`. Unfold the goal one layer
                    // and retry against the same template. The unfolded body is
                    // fully concrete (first-order def ⇒ no dummy binders to
                    // capture), so any binders the template pins are forced by
                    // the goal — sound, and the resulting concrete bindings let
                    // the ref index reject rules whose unfolded conclusion can't
                    // be assembled from the available refs (and_intro hyp `H ⊢ q`
                    // with `q = domain_on f A ∧ range_sub f B` matches no ref).
                    // Terminates because the def-dependency graph is acyclic.
                    //
                    // With `allow_binder_defs`, this also unfolds
                    // binder-introducing defs (each dummy materialized as a fresh
                    // placeholder by `unfoldDefBody`) — used by the view-conclusion
                    // seed so a folded goal like `has_preimage f A y` exposes
                    // `∃ x (x∈A ∧ maps f x y)` and pins the existential body for
                    // the `@recover` guard. Sound only because placeholders loosen
                    // matching; the matcher's mismatch logic must stay first-order.
                    //
                    // Placeholder dep slots are a finite resource (u55, shared
                    // with dummies); running out merely means this seed walk
                    // learns nothing more from the unfolding — a no-opinion,
                    // never a reason to abort the whole search.
                    const unfolded = def_match.unfoldAppOnce(
                        context,
                        theorem,
                        expr_id,
                        allow_binder_defs,
                    ) catch |err| switch (err) {
                        error.OutOfMemory => return error.OutOfMemory,
                        else => return,
                    } orelse return;
                    try partialMatchTemplate(
                        context,
                        theorem,
                        template,
                        unfolded,
                        bindings,
                        allow_binder_defs,
                        extract_members,
                    );
                    return;
                },
            }
        },
    }
}

/// `walkDefBody`'s root callback for the goal seed.
const SeedRoot = struct {
    context: *const Context,
    theorem: *TheoremContext,
    bindings: []?ExprId,
    allow_binder_defs: bool,
    extract_members: bool,

    pub fn root(self: SeedRoot, template: TemplateExpr, expr_id: ExprId) error{OutOfMemory}!void {
        try partialMatchTemplate(
            self.context,
            self.theorem,
            template,
            expr_id,
            self.bindings,
            self.allow_binder_defs,
            self.extract_members,
        );
    }
};

fn seedBindingsFromViewGoal(
    allocator: std.mem.Allocator,
    context: *const Context,
    theorem: *TheoremContext,
    view: types.ViewDecl,
    goal: Goal,
    bindings: []?ExprId,
) !void {
    const goal_expr = goal.concreteOrHint() orelse return;
    const view_bindings = try allocator.alloc(?ExprId, view.num_binders);
    defer allocator.free(view_bindings);
    @memset(view_bindings, null);
    // Extract whatever VIEW binders line up structurally against the goal, but
    // ACUI-opaquely: a context binder sitting as one summand of an ACUI combiner
    // (e.g. eq_replace's `g , h ⊢ r` = `nd(join(g,h), r)`) must NOT be pinned to
    // a positional half of the goal's context. The earlier raw `matchTemplate`
    // committed exactly such a split — for `eq_replace` it pinned `g`/`h` to one
    // goal-context member each, which then filters the per-hyp ref lookups and
    // forecloses the *other* valid decompositions (e.g. `g = emp`, `h` = the
    // whole context, the split a Leibniz rewrite over a compound replaced term
    // needs). The structural matcher in `matchOneHyp` plus the ACUI-weakening the
    // validator performs explore the splits soundly; the seed must not pre-commit
    // one. `partialMatchTemplate` skips ACUI-combiner descent, so it still pins
    // bare conclusion binders (the witness `q`/`r`) but leaves ambiguous context
    // binders open. First-order unfolding only: the projected bindings become
    // rule bindings, so binder-def unfolding remains reserved for the separate
    // view-conclusion seed used by recover guards.
    partialMatchTemplate(
        context,
        theorem,
        view.concl,
        goal_expr,
        view_bindings,
        false,
        false,
    ) catch |err| switch (err) {
        error.OutOfMemory => return err,
        else => return,
    };

    const projected = try allocator.alloc(?ExprId, bindings.len);
    defer allocator.free(projected);
    @memset(projected, null);
    if (!projectViewBindings(view, view_bindings, projected)) return;
    _ = mergeOptionalBindings(bindings, projected);
}

fn projectViewBindings(
    view: types.ViewDecl,
    view_bindings: []const ?ExprId,
    projected: []?ExprId,
) bool {
    for (view.binder_map, 0..) |maybe_rule_idx, view_idx| {
        const rule_idx = maybe_rule_idx orelse continue;
        if (rule_idx >= projected.len) return false;
        const expr = view_bindings[view_idx] orelse continue;
        if (projected[rule_idx]) |existing| {
            if (existing != expr) return false;
        } else {
            projected[rule_idx] = expr;
        }
    }
    return true;
}

fn mergeOptionalBindings(dst: []?ExprId, src: []const ?ExprId) bool {
    std.debug.assert(dst.len == src.len);
    for (src, 0..) |maybe_expr, idx| {
        const expr = maybe_expr orelse continue;
        if (dst[idx]) |existing| {
            if (existing != expr) return false;
        }
    }
    for (src, 0..) |maybe_expr, idx| {
        if (dst[idx] == null) dst[idx] = maybe_expr;
    }
    return true;
}
