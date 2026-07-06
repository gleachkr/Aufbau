//! Per-reference hypothesis matching for backward search: classify a candidate
//! ref against a rule hypothesis (matched / mismatch / unknown), extract the
//! bindings it forces, and drive the `@view` / `@recover` machinery used during
//! that match. Split out of `backtrack.zig`; the backtracker calls these helpers as
//! its per-slot matching step.

const std = @import("std");
const types = @import("../types.zig");
const prune = @import("./prune.zig");
const seed = @import("./seed.zig");
const forward = @import("../forward.zig");
const OpenTerms = @import("../../inference/open_terms.zig");
const ExprMod = @import("../../../expr.zig");
const ExprId = @import("../../../expr.zig").ExprId;
const PlaceholderId = @import("../../../expr.zig").PlaceholderId;
const TheoremContext = @import("../../../expr.zig").TheoremContext;
const RuleDecl = @import("../../../env.zig").RuleDecl;
const MetaStore = @import("../../inference/meta_store.zig").MetaStore;
const TemplateExpr = @import("../../../rules.zig").TemplateExpr;
const Context = types.Context;
const SearchCounters = types.SearchCounters;
const recoverDefiniteMismatch = prune.recoverDefiniteMismatch;
const templateDefiniteMismatch = prune.templateDefiniteMismatch;
const projectViewBindingsIntoRule = prune.projectViewBindingsIntoRule;
const extractHypPartialBindings = prune.extractHypPartialBindings;
const acuiBoundMembersPlausible = prune.acuiBoundMembersPlausible;
const acuiClosedRegionPlausible = prune.acuiClosedRegionPlausible;
const templateNeedsSemantic = prune.templateNeedsSemantic;
const exprNeedsSemantic = prune.exprNeedsSemantic;
const bindingsNeedSemantic = prune.bindingsNeedSemantic;

pub const HypMatchResult = enum {
    matched,
    mismatch,
    unknown,
};

// A successful positional match through an ACUI combiner is not a canonical
// decomposition if it assigned any binder inside that combiner.  For example,
// matching `Δ , p` against `p , F , p` may bind `Δ := p , F`, while the global
// validation can instead consume one `p` explicitly and use `Δ := F`.  Roll such
// matches back to `.unknown`; only a whole-region bare binder (`Δ`) is safe to
// assign structurally.
fn structuralMatchAssignsUnderAcui(
    context: *const Context,
    theorem: *const TheoremContext,
    template: TemplateExpr,
    expr_id: ExprId,
    before: []const ?ExprId,
    after: []const ?ExprId,
) bool {
    switch (template) {
        .binder => return false,
        .app => |app| {
            const node = theorem.interner.node(expr_id);
            const concrete = switch (node.*) {
                .app => |concrete_app| concrete_app,
                else => return false,
            };
            if (concrete.term_id != app.term_id) return false;
            if (concrete.args.len != app.args.len) return false;
            if (context.registry.acui_by_head.contains(app.term_id)) {
                return templateHasNewBinding(template, before, after);
            }
            for (app.args, concrete.args) |tmpl_arg, conc_arg| {
                if (structuralMatchAssignsUnderAcui(
                    context,
                    theorem,
                    tmpl_arg,
                    conc_arg,
                    before,
                    after,
                )) return true;
            }
            return false;
        },
    }
}

fn templateHasNewBinding(
    template: TemplateExpr,
    before: []const ?ExprId,
    after: []const ?ExprId,
) bool {
    switch (template) {
        .binder => |idx| {
            if (idx >= before.len or idx >= after.len) return false;
            return before[idx] == null and after[idx] != null;
        },
        .app => |app| {
            for (app.args) |arg| {
                if (templateHasNewBinding(arg, before, after)) return true;
            }
            return false;
        },
    }
}

/// True when any binding embeds a search-meta-class placeholder leaf — i.e. an
/// open carry-to-leaf witness rides inside a (possibly rigid) bound value.
/// O(1) short-circuit when the theorem has no metas at all.
fn snapshotEmbedsMeta(theorem: *const TheoremContext, snapshot: []const ?ExprId) bool {
    if (!theorem.hasMetaPlaceholders()) return false;
    for (snapshot) |maybe| {
        const v = maybe orelse continue;
        if (seed.exprContainsMetaLeafWalk(theorem, v)) return true;
    }
    return false;
}

/// Mint a dep-free `.meta`-class placeholder for an open binder of a holey
/// instantiation. Used instead of the default (standard, dep-consuming) factory
/// so the meta-aware hypothesis match — which re-instantiates per ref attempt —
/// cannot exhaust the scarce u55 dependency-bit space (`DependencySlotExhausted`).
/// Unregistered in any store, so `solveCorrespondence` treats it as a wildcard.
fn mintMetaPlaceholder(
    _: ?*anyopaque,
    theorem: *TheoremContext,
    sort_name: []const u8,
    _: OpenTerms.MetaKind,
) anyerror!ExprId {
    return theorem.addMetaPlaceholderResolved(sort_name);
}

/// True when `pid` is a `reconciliation_meta` leaf (an eliminator seed meta —
/// see `PlaceholderInfo.reconciliation_meta`).
fn isReconciliationMeta(theorem: *const TheoremContext, pid: PlaceholderId) bool {
    const info = theorem.placeholderInfo(pid) orelse return false;
    return info.reconciliation_meta;
}

/// True when `expr_id` mentions a reconciliation seed meta.
fn exprMentionsReconciliationMeta(
    theorem: *const TheoremContext,
    expr_id: ExprId,
) bool {
    return theorem.exprAny(expr_id, {}, reconciliationMetaPred);
}

fn reconciliationMetaPred(_: void, theorem: *const TheoremContext, expr_id: ExprId) bool {
    return switch (theorem.interner.node(expr_id).*) {
        .placeholder => |pid| isReconciliationMeta(theorem, pid),
        else => false,
    };
}

/// Register the reconciliation-meta leaves reachable from `expr_id` in `store`
/// so `solveCorrespondence` will unify them. Restricted to reconciliation metas
/// so upstream carry-to-leaf/witness metas are left untouched (deferred to leaf
/// forcing).
fn registerReconciliationMetaLeaves(
    store: *MetaStore,
    theorem: *const TheoremContext,
    expr_id: ExprId,
) !void {
    try theorem.exprForEach(expr_id, store, registerReconciliationMetaVisit);
}

fn registerReconciliationMetaVisit(
    store: *MetaStore,
    theorem: *const TheoremContext,
    expr_id: ExprId,
) anyerror!void {
    switch (theorem.interner.node(expr_id).*) {
        .placeholder => |pid| if (isReconciliationMeta(theorem, pid)) {
            try store.registerLocalMeta(theorem, expr_id);
        },
        else => {},
    }
}

/// Reconcile a hypothesis carrying seed metas against a concrete ref. Returns
/// true (with the solved metas dereferenced back into `bindings`) on a clean
/// unification, false otherwise — bindings are left UNCHANGED on every false
/// path (only the final deref mutates), so the caller falls straight through to
/// the identity-based `matchTemplate` with no restore. See the call site.
fn tryMetaAwareHypMatch(
    context: *const Context,
    theorem: *TheoremContext,
    rule: *const RuleDecl,
    template: TemplateExpr,
    ref_expr: ExprId,
    bindings: []?ExprId,
) !bool {
    // Only meaningful when a binding actually carries a (still-unresolved)
    // reconciliation seed meta; carry-to-leaf and other metas are excluded by
    // the flag check, so this is a no-op for every non-eliminator candidate.
    var has_meta = false;
    for (bindings) |b| {
        if (b) |v| {
            if (exprMentionsReconciliationMeta(theorem, v)) {
                has_meta = true;
                break;
            }
        }
    }
    if (!has_meta) return false;

    // Instantiate the hypothesis with the current (meta-laden) bindings; open
    // binders render as dep-free, store-unregistered meta placeholders so they
    // match the ref freely (`solveCorrespondence` has no opinion on a placeholder
    // absent from the store) without consuming dependency slots.
    const pattern = (try OpenTerms.instantiateTemplateHoley(
        theorem,
        context.env,
        context.registry,
        rule,
        template,
        bindings,
        .{ .placeholder_factory = .{ .makeFn = mintMetaPlaceholder } },
    )) orelse return false;

    // NOTE on ACUI soundness: `solveCorrespondence` matches a commutative-ACUI
    // combiner positionally, so in principle a reconciliation meta under a
    // combiner whose members are genuinely reorderable could be pinned to the
    // wrong member. We deliberately do NOT pre-guard that here: the normal path's
    // `structuralMatchAssignsUnderAcui` rollback cannot be reused (it would
    // discard the reconciliation), and a blanket "bail if a meta sits under any
    // ACUI head" is wrong — the eliminator motive's context `join(g, k:Nat)` has
    // a concrete `g` that anchors the position, so `?k` is unambiguous there and
    // also cross-checked against the subject `Ty C`. A genuinely-ambiguous
    // mis-assignment yields a wrong binding that fails `tryCandidate`
    // revalidation (search is a proposer) — a wasted candidate, never an unsound
    // emitted proof.
    var store = MetaStore.init(theorem.allocator, context.env);
    defer store.deinit();
    for (bindings) |b| {
        if (b) |v| try registerReconciliationMetaLeaves(&store, theorem, v);
    }
    if (store.metas.count() == 0) return false;
    if (forward.solveCorrespondence(&store, theorem, ref_expr, pattern, null) !=
        .ok)
    {
        return false;
    }
    // Deref the solved metas back into the bindings.
    var any_changed = false;
    for (bindings) |*b| {
        const v = b.* orelse continue;
        const d = try store.deref(theorem, v);
        if (d != v) {
            b.* = d;
            any_changed = true;
        }
    }
    return any_changed;
}

pub fn matchOneHypWithSnapshot(
    allocator: std.mem.Allocator,
    context: *const Context,
    theorem: *TheoremContext,
    rule_id: u32,
    hyp_index: usize,
    ref_expr: ExprId,
    bindings: []?ExprId,
    snapshot: []?ExprId,
    view_concl_seed: ?[]const ?ExprId,
    counters: ?*SearchCounters,
) !HypMatchResult {
    @memcpy(snapshot, bindings);
    // When the rule has a `@view`, match and extract bindings against the
    // view's hypothesis template rather than the raw template. The view shape
    // is what the rule author advertised as the recognizable surface form, so
    // refs that match it carry the binder information `exact?` needs even
    // when the raw shape would only become applicable after normalization.
    // Without this, e.g. `ex_intro`'s raw hypothesis `[x/t] p` blocks any ref
    // whose head isn't the substitution term, even though the view's `q`
    // would accept it.
    if (context.views.get(rule_id)) |view| {
        return try matchOneHypViaView(
            allocator,
            context,
            theorem,
            view,
            hyp_index,
            ref_expr,
            bindings,
            view_concl_seed,
            counters,
        );
    }
    const rule = &context.env.rules.items[rule_id];
    const template = rule.hyps[hyp_index];
    // Eliminator seed reconciliation: when the current bindings embed a seed
    // meta (a def-unfold dummy kept as a shared meta by `makeExactRuleCandidate`),
    // the identity-based `matchTemplate` cannot align that meta against this
    // concrete ref. Unify the instantiated hypothesis against the ref through an
    // ephemeral store, then deref the solved metas back into `bindings` so the
    // now-concrete binder rides into the sibling-slot lookups. Falls through to
    // `matchTemplate` on no live meta or any conflict; meta-free matching (the
    // whole non-eliminator corpus) is byte-identical.
    if (theorem.hasReconciliationMetas()) {
        if (try tryMetaAwareHypMatch(
            context,
            theorem,
            rule,
            template,
            ref_expr,
            bindings,
        )) {
            return .matched;
        }
        // No restore needed: `tryMetaAwareHypMatch` leaves `bindings` untouched
        // unless it returns true.
    }
    if (theorem.matchTemplate(template, ref_expr, bindings)) {
        if (structuralMatchAssignsUnderAcui(
            context,
            theorem,
            template,
            ref_expr,
            snapshot,
            bindings,
        )) {
            rollbackOneHypMatch(bindings, snapshot);
            return .unknown;
        }
        return .matched;
    }
    // matchTemplate is all-or-nothing: it commits binder assignments in
    // place as it walks, then returns false on the first inconsistency.
    // Any binders set before the failure point are structurally determined
    // by the ref and consistent with prior bindings. Classify the failure
    // using the original (pre-walk) snapshot so partial commits can't fool
    // the precheck; then on .unknown, do a full partial-extract walk so we
    // recover ALL extractable binders — including any past where
    // matchTemplate's short-circuit stopped — and let them propagate into
    // downstream hyp lookups.
    const classification: HypMatchResult = blk: {
        if (templateDefiniteMismatch(
            context,
            theorem,
            template,
            ref_expr,
            snapshot,
        )) break :blk .mismatch;
        if (!acuiBoundMembersPlausible(
            context,
            theorem,
            template,
            ref_expr,
            snapshot,
        )) break :blk .mismatch;
        if (!acuiClosedRegionPlausible(
            context,
            theorem,
            template,
            ref_expr,
            snapshot,
        )) break :blk .mismatch;
        if (templateNeedsSemantic(context, template)) break :blk .unknown;
        if (exprNeedsSemantic(context, theorem, ref_expr)) break :blk .unknown;
        if (bindingsNeedSemantic(context, theorem, snapshot)) break :blk .unknown;
        // Carry-to-leaf witness: a binding embedding an open search meta (e.g.
        // `rim`'s antecedent seeded to `P ?t` from an open-backward `rex`
        // premise) survived the definite-mismatch and ACUI plausibility gates,
        // so the meta could still unify with this ref's concrete member and
        // pin the witness. Defer to full validation rather than hard-pruning;
        // `exprNeedsSemantic` ignores placeholders, so this is the only escape
        // for the pure-meta (no transparent-def) case. Inert for concrete
        // searches (`hasMetaPlaceholders` is O(1) false).
        if (snapshotEmbedsMeta(theorem, snapshot)) break :blk .unknown;
        break :blk .mismatch;
    };
    rollbackOneHypMatch(bindings, snapshot);
    if (classification == .unknown) {
        extractHypPartialBindings(context, theorem, template, ref_expr, bindings);
    }
    return classification;
}

fn matchOneHypViaView(
    allocator: std.mem.Allocator,
    context: *const Context,
    theorem: *TheoremContext,
    view: types.ViewDecl,
    hyp_index: usize,
    ref_expr: ExprId,
    bindings: []?ExprId,
    view_concl_seed: ?[]const ?ExprId,
    counters: ?*SearchCounters,
) !HypMatchResult {
    const view_bindings = try allocator.alloc(?ExprId, view.num_binders);
    defer allocator.free(view_bindings);
    seedViewBindingsForMatch(view, bindings, view_concl_seed, view_bindings);
    const pre_bindings = try allocator.dupe(?ExprId, view_bindings);
    defer allocator.free(pre_bindings);

    // Closed-ACUI necessary condition against the view hypothesis. When the
    // goal context is the unit, `seedBindingsFromGoal` pins the rule's split
    // context binders (e.g. `ex_elim_sub`'s `g`, `h`) to `emp`, which projects
    // into these view binders; a ref whose context then carries an unmatchable
    // member can be rejected before the full match/extract. Leaves rule
    // `bindings` untouched (only the local `view_bindings` were seeded), so the
    // caller's snapshot is preserved as on the other `.mismatch` paths.
    if (!acuiClosedRegionPlausible(
        context,
        theorem,
        view.hyps[hyp_index],
        ref_expr,
        view_bindings,
    )) {
        return .mismatch;
    }

    if (theorem.matchTemplate(view.hyps[hyp_index], ref_expr, view_bindings) and
        !structuralMatchAssignsUnderAcui(
            context,
            theorem,
            view.hyps[hyp_index],
            ref_expr,
            pre_bindings,
            view_bindings,
        ))
    {
        // A clean structural match (no binder pinned positionally under a
        // commutative ACUI region). The matched view binders now include this
        // hypothesis's bindings on top of the goal-derived conclusion seed. If
        // a `@recover` law over those binders provably fails, this ref cannot
        // satisfy the rule, so prune it before it reaches full validation. The
        // rule `bindings` were never written on this path, so returning
        // `.mismatch` leaves them untouched for the caller's snapshot rollback.
        if (recoverGuardRejects(context, theorem, view, pre_bindings, view_bindings)) {
            if (counters) |actual| actual.recover_guard_match_rejects += 1;
            return .mismatch;
        }
        try solveCarriedViewMetas(context, theorem, view, view_bindings, bindings);
        projectViewBindingsIntoRule(view, view_bindings, bindings);
        return .matched;
    }
    // matchTemplate failed, or it succeeded only by guessing an ACUI split:
    // a binder was pinned positionally under a commutative ACUI region, where
    // the ref's members can be in any order/association so the positional
    // correspondence is arbitrary (e.g. `ex_elim`'s body hypothesis
    // `h , p ⊢ c` against `l41`, whose three-member context lets the structural
    // match pin `p` to whichever member the ref's join happens to end with).
    // Committing that guess would poison the sibling hypothesis's index
    // pre-filter and drop the otherwise-valid ref. Either way, reset (keeping
    // the goal-derived conclusion seed) and re-derive through the same
    // ACUI-aware partial extractor the raw-template path in
    // `matchOneHypWithSnapshot` uses on its `.unknown` branch: it pins only
    // forced members. (Unlike that path, we keep those forced bindings rather
    // than rolling back to the snapshot — they are sound hints for the sibling
    // lookups, and the `.unknown` result still defers the real decision to
    // full validation.)
    seedViewBindingsForMatch(view, bindings, view_concl_seed, view_bindings);
    extractHypPartialBindings(
        context,
        theorem,
        view.hyps[hyp_index],
        ref_expr,
        view_bindings,
    );
    // Run the recover guard here too. A structural matchTemplate failure is
    // common and benign for view hyps — e.g. the context binder `g` is pinned
    // to the goal context while a ref proves a sub-context, which the
    // validator reconciles via ACUI weakening. The witness binder (`q`) is
    // still extracted above, so the `@recover` law can be checked against it
    // and prune refs whose wff cannot be `pattern` with `hole` substituted.
    if (recoverGuardRejects(context, theorem, view, pre_bindings, view_bindings)) {
        if (counters) |actual| actual.recover_guard_extract_rejects += 1;
        return .mismatch;
    }
    try solveCarriedViewMetas(context, theorem, view, view_bindings, bindings);
    projectViewBindingsIntoRule(view, view_bindings, bindings);
    return .unknown;
}

/// Register every meta-class wildcard leaf (a carried ancestor witness, marked
/// by a stable `meta_id`) reachable in `expr`. Returns true if any was found,
/// so the caller can skip the solve when nothing is carried.
fn registerMetasInExpr(
    store: *MetaStore,
    theorem: *const TheoremContext,
    expr: ExprId,
) !bool {
    ExprMod.work_ticks_walk +%= 1;
    return switch (theorem.interner.node(expr).*) {
        .variable => false,
        .placeholder => |pid| blk: {
            if (theorem.placeholderMetaId(pid) == null) break :blk false;
            try store.registerAncestorMeta(theorem, expr);
            break :blk true;
        },
        .app => |app| blk: {
            var found = false;
            for (app.args) |arg| {
                if (try registerMetasInExpr(store, theorem, arg)) found = true;
            }
            break :blk found;
        },
    };
}

/// Solve a carried ancestor witness meta that landed inside a view rule's matrix
/// (the matrix is seeded from the open goal hint, so an enclosing open slot's
/// witness `W` rides along in it). The rule's own `@recover` only solves its
/// witness `t`; the carried `W` would otherwise stay in the matrix, where the
/// verifier treats it rigidly and rejects an otherwise-valid pool-ref fill (the
/// nested-`ex_intro` case: matrix `R W v` vs the concrete hyp `R c d`). But each
/// `@recover` law is itself a forced correspondence `[hole↦t]pattern == source`,
/// so any meta the concrete `source` pins at a non-hole position is *determined*,
/// not guessed. Solve those carried metas from each law's (source, pattern, hole)
/// and rewrite both the view bindings and the projected rule bindings to the
/// resolved values, so validation sees a concrete matrix. No-op for theories
/// with no live metas or no carried meta in this match. Sound: only forced metas
/// are pinned and `tryCandidate` revalidates the whole assembly.
pub fn solveCarriedViewMetas(
    context: *const Context,
    theorem: *TheoremContext,
    view: types.ViewDecl,
    view_bindings: []?ExprId,
    rule_bindings: []?ExprId,
) !void {
    if (theorem.meta_placeholder_count == 0) return;
    var store = MetaStore.init(theorem.allocator, context.env);
    defer store.deinit();
    var any = false;
    for (view_bindings) |maybe| {
        const b = maybe orelse continue;
        if (try registerMetasInExpr(&store, theorem, b)) any = true;
    }
    if (!any) return;

    var solved = false;
    for (view.derived_bindings) |derived| {
        const rec = switch (derived) {
            .recover => |r| r,
            .abstract => continue,
        };
        if (rec.source_view_idx >= view_bindings.len) continue;
        if (rec.pattern_view_idx >= view_bindings.len) continue;
        if (rec.hole_view_idx >= view_bindings.len) continue;
        const source = view_bindings[rec.source_view_idx] orelse continue;
        const pattern = view_bindings[rec.pattern_view_idx] orelse continue;
        const hole = view_bindings[rec.hole_view_idx] orelse continue;
        const mark = store.mark();
        if (forward.solveCorrespondence(&store, theorem, source, pattern, hole) == .ok) {
            solved = true;
        } else {
            store.rollbackTo(mark);
        }
    }
    if (!solved) return;

    for (view_bindings, 0..) |maybe, vi| {
        const b = maybe orelse continue;
        const d = try store.deref(theorem, b);
        if (d == b) continue;
        view_bindings[vi] = d;
        // Propagate the now-forced value into the rule bindings, overwriting the
        // carried-meta version the conclusion seed already projected.
        if (vi < view.binder_map.len) {
            if (view.binder_map[vi]) |rule_idx| {
                if (rule_idx < rule_bindings.len) rule_bindings[rule_idx] = d;
            }
        }
    }
}

pub fn seedViewBindingsFromRule(
    view: types.ViewDecl,
    rule_bindings: []const ?ExprId,
    view_bindings: []?ExprId,
) void {
    @memset(view_bindings, null);
    for (view.binder_map, 0..) |maybe_rule_idx, vi| {
        const rule_idx = maybe_rule_idx orelse continue;
        if (rule_idx >= rule_bindings.len) continue;
        view_bindings[vi] = rule_bindings[rule_idx];
    }
}

// Seed view binders for a hypothesis match. Like `seedViewBindingsFromRule`
// but first lays down the goal-derived conclusion seed (which carries phantom
// binders the recover guard needs), then overlays the current rule bindings
// so any binder already pinned by an earlier hypothesis takes precedence.
pub fn seedViewBindingsForMatch(
    view: types.ViewDecl,
    rule_bindings: []const ?ExprId,
    view_concl_seed: ?[]const ?ExprId,
    view_bindings: []?ExprId,
) void {
    @memset(view_bindings, null);
    if (view_concl_seed) |concl_seed| {
        for (concl_seed, 0..) |maybe_expr, vi| {
            if (vi >= view_bindings.len) break;
            view_bindings[vi] = maybe_expr;
        }
    }
    for (view.binder_map, 0..) |maybe_rule_idx, vi| {
        const rule_idx = maybe_rule_idx orelse continue;
        if (rule_idx >= rule_bindings.len) continue;
        if (rule_bindings[rule_idx]) |expr| view_bindings[vi] = expr;
    }
}

// Returns true when some `@recover` law on this view, evaluated over the
// currently resolved view binders, provably fails — meaning the matched ref
// cannot satisfy the rule and should be pruned before full validation. A law
// is only checked once its `source`, `pattern`, and `hole` binders are all
// resolved; the actual soundness reasoning lives in `recoverDefiniteMismatch`.
fn recoverGuardRejects(
    context: *const Context,
    theorem: *const TheoremContext,
    view: types.ViewDecl,
    pre_bindings: []const ?ExprId,
    view_bindings: []const ?ExprId,
) bool {
    for (view.derived_bindings) |derived| {
        const rec = switch (derived) {
            .recover => |rec| rec,
            .abstract => continue,
        };
        if (rec.target_view_idx >= view_bindings.len) continue;
        if (rec.source_view_idx >= view_bindings.len) continue;
        if (rec.pattern_view_idx >= view_bindings.len) continue;
        if (rec.hole_view_idx >= view_bindings.len) continue;
        // A `@recover` law only determines its target; when the target was
        // already resolved before matching this hypothesis (e.g. pinned directly
        // from the conclusion match), `applyRecover` skips the law entirely
        // (`.no_progress`) and validation never requires it to succeed. Using it
        // as a prune in that state is unsound: a perfectly valid ref whose
        // `source` is not a normalized `[hole]pattern` form (e.g.
        // `sep_intro_imp2`'s shared antecedent `q`, which is not the substituted
        // motive) would be wrongly rejected. But if this hypothesis match is what
        // resolved the target, the law is still a sound necessary condition.
        if (pre_bindings[rec.target_view_idx] != null) continue;
        const source = view_bindings[rec.source_view_idx] orelse continue;
        const pattern = view_bindings[rec.pattern_view_idx] orelse continue;
        const hole = view_bindings[rec.hole_view_idx] orelse continue;
        if (recoverDefiniteMismatch(context, theorem, source, pattern, hole)) {
            return true;
        }
    }
    return false;
}

// Where a `@recover` source binder lives inside a view hypothesis: the sequent
// (turnstile) head, which argument is its context side, the ACUI combiner that
// flattens that context, and the wrapper (e.g. `hyp(·)`) that injects a single
// wff as a context member.
pub const RecoverSourceLocation = struct {
    hyp_index: usize,
    turnstile_term_id: u32,
    ctx_arg_index: usize,
    acui_head: ?u32,
    wrapper_term_id: u32,
    wrapper_arg_pos: usize,
};

pub fn templateReferencesBinder(template: TemplateExpr, idx: usize) bool {
    switch (template) {
        .binder => |i| return i == idx,
        .app => |app| {
            for (app.args) |arg| {
                if (templateReferencesBinder(arg, idx)) return true;
            }
            return false;
        },
    }
}

// Find the app that *directly* wraps binder `idx` (the `hyp(q)` injector around
// a recover source), returning its head term and the argument position holding
// the binder.
fn findBinderWrapper(
    template: TemplateExpr,
    idx: usize,
) ?struct { term_id: u32, arg_pos: usize } {
    switch (template) {
        .binder => return null,
        .app => |app| {
            for (app.args, 0..) |arg, pos| {
                switch (arg) {
                    .binder => |i| if (i == idx) return .{
                        .term_id = app.term_id,
                        .arg_pos = pos,
                    },
                    else => {},
                }
            }
            for (app.args) |arg| {
                if (findBinderWrapper(arg, idx)) |wrapper| return wrapper;
            }
            return null;
        },
    }
}

// Locate the recover source binder within the view's hypothesis templates. The
// view hypotheses are 1:1 with the rule's, so the returned `hyp_index` also
// names the rule hypothesis (and thus the selected ref) to inspect.
pub fn findRecoverSourceLocation(
    context: *const Context,
    view: types.ViewDecl,
    source_view_idx: usize,
) ?RecoverSourceLocation {
    for (view.hyps, 0..) |hyp_template, k| {
        const top = switch (hyp_template) {
            .app => |app| app,
            .binder => continue,
        };
        var ctx_arg_index: ?usize = null;
        for (top.args, 0..) |arg, ai| {
            if (templateReferencesBinder(arg, source_view_idx)) {
                ctx_arg_index = ai;
                break;
            }
        }
        const cai = ctx_arg_index orelse continue;
        const ctx_template = top.args[cai];
        const wrapper = findBinderWrapper(ctx_template, source_view_idx) orelse
            continue;
        const acui_head: ?u32 = switch (ctx_template) {
            .app => |app| if (context.registry.acui_by_head.contains(app.term_id))
                app.term_id
            else
                null,
            .binder => null,
        };
        return .{
            .hyp_index = k,
            .turnstile_term_id = top.term_id,
            .ctx_arg_index = cai,
            .acui_head = acui_head,
            .wrapper_term_id = wrapper.term_id,
            .wrapper_arg_pos = wrapper.arg_pos,
        };
    }
    return null;
}

pub fn rollbackOneHypMatch(bindings: []?ExprId, snapshot: []const ?ExprId) void {
    @memcpy(bindings, snapshot);
}
