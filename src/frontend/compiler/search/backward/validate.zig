//! Candidate validation and result construction for backward search. Takes a
//! completed ref selection (or a goal-direct derived recipe), re-checks it
//! through the ordinary `tryCandidate` pipeline, renders the explicit bindings
//! the suggestion needs, and ranks/appends the accepted candidate. This is the
//! final stage the backtracker reaches once a slot assignment is complete.
//! Split out of `backtrack.zig`.

const std = @import("std");
const types = @import("../types.zig");
const refs_mod = @import("../refs.zig");
const ref_index_mod = @import("../ref_index.zig");
const forward = @import("../forward.zig");
const candidate_mod = @import("../candidate.zig");
const plausible = @import("./plausible.zig");
const ExprId = @import("../../../expr.zig").ExprId;
const TheoremContext = @import("../../../expr.zig").TheoremContext;
const ProofScript = @import("../../../proof_script.zig");
const RuleApplication = ProofScript.RuleApplication;
const CompilerContext = @import("../../context.zig").CompilerContext;
const Check = @import("../../check.zig");
const Context = types.Context;
const Goal = types.Goal;
const ApplyCandidate = types.ApplyCandidate;
const ExactCandidate = types.ExactCandidate;
const DerivedPool = types.DerivedPool;
const NameExprMap = types.NameExprMap;
const SearchCounters = types.SearchCounters;
const Fuel = types.Fuel;
const rankReferenceIndices = refs_mod.rankReferenceIndices;
const tryCandidate = candidate_mod.tryCandidate;
const tryCandidateProbe = candidate_mod.tryCandidateProbe;
const finalConclusionPlausible = plausible.finalConclusionPlausible;

/// Goal-direct use of derived refs: when a derived shape structurally
/// matches the concrete goal (the holes solved positionally by the match),
/// the materialized recipe is itself a candidate proof, validated through the
/// ordinary `tryCandidate` pipeline like everything else.
pub fn appendDerivedDirectCandidates(
    compiler: *CompilerContext,
    allocator: std.mem.Allocator,
    context: *const Context,
    dpool: *DerivedPool,
    goal: Goal,
    theorem: *const TheoremContext,
    theorem_vars: *const NameExprMap,
    counters: ?*SearchCounters,
    fuel: ?*Fuel,
    candidates: *std.ArrayListUnmanaged(ExactCandidate),
) !void {
    const goal_expr = switch (goal) {
        .concrete => |expr| expr,
        .implicit_whole_conclusion => |hint| hint orelse return,
        .holey => return,
    };
    // Same pre-filter as `tryDerivedSlots`: only derived shapes the index
    // says could match the goal get the full correspondence solve. A failed
    // goal lookup (not OOM) falls back to scanning everything.
    var lookup: ?ref_index_mod.LookupResult = null;
    defer if (lookup) |*l| l.deinit();
    if (dpool.index) |*dref_index| {
        lookup = blk: {
            break :blk dref_index.lookupExpected(
                theorem,
                goal_expr,
                counters,
            ) catch |err| switch (err) {
                error.OutOfMemory => return error.OutOfMemory,
                else => break :blk null,
            };
        };
    }
    const direct_count = if (lookup) |l| l.indices.len else dpool.refs.len;
    for (0..direct_count) |direct_idx| {
        const dref_idx = if (lookup) |l| l.indices[direct_idx] else direct_idx;
        const dref = &dpool.refs[dref_idx];
        // Materialization interns scratch nodes (deref / name substitution);
        // run it in a throwaway COW clone so the caller's theorem stays
        // untouched.
        var scratch = try theorem.clone();
        defer scratch.deinit();

        const mark = dpool.store.mark();
        const was_open = dpool.store.universal_use_open;
        dpool.store.openUniversalUse();
        defer dpool.store.universal_use_open = was_open;

        var application: ?RuleApplication = null;
        if (forward.solveCorrespondence(
            &dpool.store,
            &scratch,
            goal_expr,
            dref.shape,
            null,
        ) == .ok) {
            application = try forward.materializeApplication(
                dpool,
                context,
                &scratch,
                theorem_vars,
                goal_expr,
                dref,
            );
        }
        dpool.store.rollbackTo(mark);
        const app = application orelse continue;

        if (fuel) |f| try f.spend();
        if (counters) |actual| {
            actual.ref_tuple_count_after_filtering += 1;
            actual.full_try_candidate_calls += 1;
        }
        var attempt = tryCandidateProbe(
            compiler,
            context,
            app,
            goal,
            theorem,
            theorem_vars,
            .{
                .counters = counters,
                .result_ownership = .borrowed,
            },
        ) catch |err| {
            if (err == error.OutOfMemory) return err;
            // A memoized skip is already tallied as a skip; don't also count it
            // as a fresh validation rejection (it ran no validation).
            if (err == error.MemoizedReject) continue;
            if (counters) |actual| {
                actual.rejected_candidates_after_validation += 1;
                actual.recordRuleAttempt(dref.rule_name, false);
            }
            continue;
        };
        attempt.deinit();
        if (counters) |actual| {
            actual.accepted_candidates += 1;
            actual.recordRuleAttempt(dref.rule_name, true);
        }
        const owned_refs = try allocator.dupe(ProofScript.Ref, app.refs);
        errdefer allocator.free(owned_refs);
        var owned_application = app;
        owned_application.refs = owned_refs;
        try candidates.append(allocator, .{
            .allocator = allocator,
            .rule_id = dref.rule_id,
            .rule_name = dref.rule_name,
            .declaration_order = dref.declaration_order,
            .refs = owned_refs,
            .application = owned_application,
            // Derived recipes rank after any assembly over real pool refs.
            .reference_rank = std.math.maxInt(usize),
        });
    }
}

/// Build a synthetic `RuleApplication` for in-search validation (all spans
/// zeroed; these candidates have no source location). `refs_span` is null for
/// an empty ref list, matching how the parser would leave it.
fn buildRuleApplication(
    rule_name: []const u8,
    refs: []const ProofScript.Ref,
    arg_bindings: []const ProofScript.ArgBinding,
) RuleApplication {
    const zero_span = ProofScript.Span{ .start = 0, .end = 0 };
    return .{
        .rule_name = rule_name,
        .rule_span = zero_span,
        .binding_list_span = null,
        .arg_bindings = arg_bindings,
        .refs_span = if (refs.len == 0) null else zero_span,
        .refs = refs,
        .span = zero_span,
    };
}

fn recordValidationRejection(counters: ?*SearchCounters, rule_name: []const u8) void {
    if (counters) |actual| {
        actual.rejected_candidates_after_validation += 1;
        actual.recordRuleAttempt(rule_name, false);
    }
}

pub fn validateSelectedRefs(
    compiler: *CompilerContext,
    allocator: std.mem.Allocator,
    context: *const Context,
    pool: []const refs_mod.RefPoolEntry,
    candidate: *ApplyCandidate,
    goal: Goal,
    theorem: *const TheoremContext,
    theorem_vars: *const NameExprMap,
    bindings: []const ?ExprId,
    selected: []const ?usize,
    generated: []const ?RuleApplication,
    counters: ?*SearchCounters,
    fuel: ?*Fuel,
    candidates: *std.ArrayListUnmanaged(ExactCandidate),
) !void {
    if (!finalConclusionPlausible(context, candidate, goal, bindings, counters)) {
        if (counters) |actual| actual.final_conclusion_prunes += 1;
        return;
    }

    // Hyp-vs-ref ACUI member consistency: refute (candidate, refs) tuples
    // whose pool-ref conclusions cannot ACUI-match the instantiated
    // hypotheses under any conclusion-vs-goal binder assignment. This is
    // what stops a loose candidate (principal binders unbound inside an
    // ACUI conclusion region, so its premise slots are wildcard sequents)
    // from sweeping the whole pool through full `tryCandidate` — the
    // dominant doomed-reject flood in one-sided sequent theories, where
    // the entire conclusion is one ACUI region and seeding pins nothing.
    hypref: {
        var ref_concls_buf: [16]?ExprId = undefined;
        if (selected.len > ref_concls_buf.len) break :hypref;
        const ref_concls = ref_concls_buf[0..selected.len];
        var any_pool_ref = false;
        for (selected, 0..) |maybe_pool_index, idx| {
            ref_concls[idx] = null;
            if (idx < generated.len and generated[idx] != null) continue;
            const pool_index = maybe_pool_index orelse continue;
            ref_concls[idx] = refs_mod.sourceRefExpr(
                context,
                &candidate.theorem,
                pool[pool_index].ref,
            ) catch null;
            if (ref_concls[idx] != null) any_pool_ref = true;
        }
        if (!any_pool_ref) break :hypref;
        if (!plausible.hypRefMembersPlausible(
            context,
            &candidate.theorem,
            candidate.rule_id,
            goal,
            bindings,
            ref_concls,
        )) {
            if (counters) |actual| actual.hyp_ref_prunes += 1;
            return;
        }
    }

    // Spend global fuel on the expensive op (the `tryCandidate` cascade) before
    // running it. `error.SearchBudgetExhausted` unwinds the whole recursion to
    // the iterative-deepening loop, which reports it distinctly from a miss.
    if (fuel) |f| try f.spend();
    if (counters) |actual| {
        actual.ref_tuple_count_after_filtering += 1;
        actual.full_try_candidate_calls += 1;
    }
    const refs = try refsFromSelected(allocator, pool, selected, generated);
    defer allocator.free(refs);
    const reference_rank = rankSelectedReferenceIndices(
        pool.len,
        selected,
        generated,
    );
    // Binders solved through existential metas (or enumerated bound
    // witnesses) are rendered as explicit bindings, so the suggestion checks
    // robustly without re-deriving the witness. Validation below runs WITH
    // the bindings, exercising the same parse path the final source will.
    var arg_bindings: []ProofScript.ArgBinding = &.{};
    var bindings_transferred = false;
    if (candidate.meta_solved) |flags| {
        arg_bindings = try renderMetaSolvedBindings(
            allocator,
            context,
            candidate,
            theorem_vars,
            bindings,
            flags,
        );
    }
    defer if (!bindings_transferred) freeRenderedBindings(allocator, arg_bindings);
    const application = buildRuleApplication(candidate.rule_name, refs, arg_bindings);

    // Scope of the UnifyMismatch retry arm, computed ONCE and shared with the
    // verdict memo (via `AttemptOptions`) so the memo's retry-eligibility
    // predicate mirrors this gate by construction — a bare-assembly reject the
    // retry below can rescue must never be memoized as terminal.
    const unify_retry_scope = (goal == .implicit_whole_conclusion and
        context.views.contains(candidate.rule_id) and
        candidate.theorem.hasMetaPlaceholders()) or
        // `@auto eager` candidates: the search fully resolves an eager rule's
        // binders (class-1 shape + forced split complement), but the eager
        // ladder freely reorders ACUI members, so the ACUI-blind strict
        // replay routinely fails to recover the context binder from the
        // reassociated inline premise (`UnifyMismatch`). Rendering the
        // resolved bindings explicitly lets the checker accept the exact
        // assembly the search built, instead of the reject-hunt wandering
        // into the retention/constrained-MP tails for an order that happens
        // to survive strict replay. Population-bounded by the annotation, so
        // the martin_lof bulk-reject concern behind the narrow view-rule
        // scope does not apply.
        context.registry.eagerPriority(candidate.rule_id) != null;

    var attempt = tryCandidateProbe(
        compiler,
        context,
        application,
        goal,
        theorem,
        theorem_vars,
        .{
            .counters = counters,
            .result_ownership = .borrowed,
            .unify_retry_eligible = unify_retry_scope,
        },
    ) catch |err| blk: {
        if (err == error.OutOfMemory) return err;
        // A memoized skip is a known terminal reject already tallied as a skip
        // (and the retry guard below only triggers on real checker errors, never
        // on this one); return without re-counting it as a validation rejection.
        if (err == error.MemoizedReject) return;
        // Fallback: the ACUI-blind strict-replay checker couldn't infer a
        // search-resolved binder (a branching rule's context `g`/principal whose
        // value the search pinned by ACUI distribution but replay can't recover
        // from the reassociated premise refs). Retry once, handing the checker
        // every resolved binding explicitly. Only on an already-failing candidate
        // that carried no explicit bindings, so passing suggestions are untouched.
        //
        // `HypothesisMismatch` on a holey (open-generation) goal is the
        // carried-witness case: a nested `@auto backward` view rule whose matrix
        // the search resolved from a carried ancestor meta (`solveCarriedViewMetas`)
        // but whose conclusion the holey goal re-infers WITH the meta still rigid,
        // so the reconstructed hypothesis mismatches the concrete ref. Rendering
        // the resolved matrix explicitly lets the checker use the concrete form
        // (e.g. inner `ex_intro` of `∃u∃v(R u v)`: matrix `R c v`, hyp `R c d`).
        // `UnifyMismatch` on a holey goal is the same condition one stage
        // earlier: when the carried meta's solved value is a COMPOUND term
        // (`W := f c`), the inference solver's placeholder model cannot absorb
        // a whole subtree at the wildcard, so inference itself dies before the
        // hypothesis comparison. Either way the search already resolved the
        // binder; hand the checker the values. The UnifyMismatch arm is scoped
        // to meta-bearing VIEW-rule candidates — the only population
        // `solveCarriedViewMetas` rewrites — because eliminator-seed-meta
        // candidates (martin_lof `nat_ind_elim`) reject with UnifyMismatch in
        // bulk and a blanket retry re-runs the checker on every one of them
        // (+27% ticks on `add_suc_right`, erasing the global-budget margin)
        // without ever succeeding. Gated to holey goals so the concrete-goal
        // corpus pays no second `tryCandidate` on its ordinary mismatches.
        const unify_retry = err == error.UnifyMismatch and unify_retry_scope;
        if (((err == error.MissingBinderAssignment) or
            (err == error.HypothesisMismatch and goal == .implicit_whole_conclusion) or
            unify_retry) and
            arg_bindings.len == 0) blk_retry: {
            const retry_bindings = renderAllResolvedBindings(
                allocator,
                context,
                candidate,
                theorem_vars,
                bindings,
            ) catch |rerr| {
                if (rerr == error.OutOfMemory) return rerr;
                break :blk_retry;
            };
            if (retry_bindings.len == 0) break :blk_retry;
            arg_bindings = retry_bindings;

            // The failed first attempt worked entirely in `tryCandidate`'s own
            // internal clones (a non-commit attempt never writes back through
            // the base pointers), so the retry probes against the same
            // untouched base.
            break :blk tryCandidateProbe(
                compiler,
                context,
                buildRuleApplication(candidate.rule_name, refs, arg_bindings),
                goal,
                theorem,
                theorem_vars,
                .{
                    .counters = counters,
                    .result_ownership = .borrowed,
                    .unify_retry_eligible = unify_retry_scope,
                },
            ) catch |err2| {
                if (err2 == error.OutOfMemory) return err2;
                recordValidationRejection(counters, candidate.rule_name);
                return;
            };
        }
        recordValidationRejection(counters, candidate.rule_name);
        return;
    };
    defer attempt.deinit();
    if (counters) |actual| {
        actual.accepted_candidates += 1;
        actual.recordRuleAttempt(candidate.rule_name, true);
    }
    // Nested-inline binder handoff: an accepted `@auto eager` candidate inside
    // an internal generation child becomes a NESTED node of a parent assembly,
    // where the checker's bottom-up re-inference would have to re-derive its
    // binders from an ACUI-reassociated hint (the pre-existing nested-inline
    // extraction gap — genuinely ambiguous bags cannot be decomposed from the
    // hint alone). The search already resolved the binders; render them on the
    // application so every level of the spliced tree carries its own values.
    // Suggestions surfaced to the user (non-internal candidates) are untouched,
    // as is every theory without eager annotations. Best-effort: a render
    // failure just leaves the bare application (status quo).
    if (candidate.internal_child and
        arg_bindings.len == 0 and
        context.registry.eagerPriority(candidate.rule_id) != null)
    {
        const rendered: []ProofScript.ArgBinding = renderAllResolvedBindings(
            allocator,
            context,
            candidate,
            theorem_vars,
            bindings,
        ) catch |rerr| blk: {
            if (rerr == error.OutOfMemory) return rerr;
            break :blk &.{};
        };
        if (rendered.len != 0) arg_bindings = rendered;
    }
    const owned_refs = try allocator.dupe(ProofScript.Ref, refs);
    errdefer allocator.free(owned_refs);
    const owned_application = buildRuleApplication(candidate.rule_name, owned_refs, arg_bindings);
    try candidates.append(allocator, .{
        .allocator = allocator,
        .rule_id = candidate.rule_id,
        .rule_name = candidate.rule_name,
        .declaration_order = candidate.declaration_order,
        .refs = owned_refs,
        .application = owned_application,
        .reference_rank = reference_rank,
        .owns_arg_bindings = arg_bindings.len != 0,
    });
    bindings_transferred = true;
}

/// Render the meta-solved binder values of `candidate` as explicit
/// `(name := $ … $)` bindings, in ascending binder order. Unrenderable
/// values (unnamed binder, unnamed variable, leftover placeholder) are
/// skipped rather than failing the candidate — the bindings are a
/// robustness aid; validation still arbitrates.
fn renderMetaSolvedBindings(
    allocator: std.mem.Allocator,
    context: *const Context,
    candidate: *ApplyCandidate,
    theorem_vars: *const NameExprMap,
    bindings: []const ?ExprId,
    flags: []const bool,
) ![]ProofScript.ArgBinding {
    var any = false;
    for (flags) |flag| {
        if (flag) any = true;
    }
    if (!any) return &.{};

    const rule = &context.env.rules.items[candidate.rule_id];
    // Binders to render: the meta-solved ones, PLUS the `@recover` pattern
    // binder (`p`, the `wff x` principal) of any witness rule whose witness is
    // here meta-solved. When such a witness rule is assembled INLINE (a deep
    // generated sub-proof, no stated conclusion), the checker re-validates it
    // bottom-up; the witness `t` alone is insufficient — the principal `∃ x p`
    // can't be reconstructed from the premise without `p`, so the hypothesis
    // match fails. Rendering `p` alongside `t` makes the nested assembly check,
    // exactly like a hand-written `rex (p := …, t := …) [premise]`. Empirically
    // `{p,t}` is the needed set; adding the context binders `g`/`d` instead
    // OVER-constrains and breaks inference, so we add only the pattern binder.
    var render = try allocator.alloc(bool, rule.args.len);
    defer allocator.free(render);
    for (render, 0..) |*r, idx| r.* = idx < flags.len and flags[idx];
    if (context.views.get(candidate.rule_id)) |view| {
        for (view.derived_bindings) |db| {
            const rec = switch (db) {
                .recover => |r| r,
                .abstract => continue,
            };
            // Only when this rule's witness (the recover target) is itself
            // meta-solved here — i.e. this is a witness-enumerated candidate.
            const target_arg = if (rec.target_view_idx < view.binder_map.len)
                view.binder_map[rec.target_view_idx]
            else
                null;
            const tgt = target_arg orelse continue;
            if (tgt >= flags.len or !flags[tgt]) continue;
            if (rec.pattern_view_idx >= view.binder_map.len) continue;
            const pat_arg = view.binder_map[rec.pattern_view_idx] orelse continue;
            if (pat_arg < render.len) render[pat_arg] = true;
        }
    }

    return renderBindings(allocator, context, candidate, theorem_vars, bindings, render);
}

/// Shared binding renderer: emit `(name := $ … $)` for the rule binders selected
/// by `mask` (or every search-resolved binder when `mask` is null), rendering
/// each non-null `bindings[idx]` value via the theorem namer in ascending binder
/// order. Unrenderable entries (out of range, unnamed binder/variable, leftover
/// placeholder) are skipped rather than failing — bindings are a robustness aid;
/// validation still arbitrates.
fn renderBindings(
    allocator: std.mem.Allocator,
    context: *const Context,
    candidate: *ApplyCandidate,
    theorem_vars: *const NameExprMap,
    bindings: []const ?ExprId,
    mask: ?[]const bool,
) ![]ProofScript.ArgBinding {
    const zero_span = ProofScript.Span{ .start = 0, .end = 0 };
    const rule = &context.env.rules.items[candidate.rule_id];
    var namer = forward.Namer.init(allocator);
    defer namer.deinit();
    try namer.collectTheoremVars(&candidate.theorem, theorem_vars);

    var out = std.ArrayListUnmanaged(ProofScript.ArgBinding){};
    errdefer {
        for (out.items) |binding| allocator.free(binding.formula.text);
        out.deinit(allocator);
    }
    for (bindings, 0..) |maybe, idx| {
        if (mask) |m| {
            if (idx >= m.len or !m[idx]) continue;
        }
        const value = maybe orelse continue;
        if (idx >= rule.arg_names.len) continue;
        const name = rule.arg_names[idx] orelse continue;
        const text = (try namer.render(
            allocator,
            context,
            &candidate.theorem,
            value,
        )) orelse continue;
        try out.append(allocator, .{
            .name = name,
            .name_span = zero_span,
            .formula = .{ .text = text, .span = zero_span },
            .span = zero_span,
        });
    }
    return try out.toOwnedSlice(allocator);
}

fn freeRenderedBindings(
    allocator: std.mem.Allocator,
    arg_bindings: []ProofScript.ArgBinding,
) void {
    if (arg_bindings.len == 0) return;
    for (arg_bindings) |binding| allocator.free(binding.formula.text);
    allocator.free(arg_bindings);
}

// Render EVERY search-resolved (non-null) rule binder as an explicit binding.
// Used only as a fallback retry when a generated assembly fails validation with
// `MissingBinderAssignment`: the trusted strict-replay checker is ACUI-blind, so
// for a branching rule whose context binder `g` (or principal a,b) the search
// pinned by ACUI distribution, replay cannot re-infer it from the reassociated
// premise refs and gives up. Handing the checker the search's own values makes
// the assembly check the same way a hand-written `lim (g := …, a := …, …)` would.
// Strictly additive: invoked only on an already-failing candidate, so it can
// only turn misses into hits — passing candidates never reach it and stay
// byte-identical.
fn renderAllResolvedBindings(
    allocator: std.mem.Allocator,
    context: *const Context,
    candidate: *ApplyCandidate,
    theorem_vars: *const NameExprMap,
    bindings: []const ?ExprId,
) ![]ProofScript.ArgBinding {
    return renderBindings(allocator, context, candidate, theorem_vars, bindings, null);
}

fn refsFromSelected(
    allocator: std.mem.Allocator,
    pool: []const refs_mod.RefPoolEntry,
    selected: []const ?usize,
    generated: []const ?RuleApplication,
) ![]const ProofScript.Ref {
    const refs = try allocator.alloc(ProofScript.Ref, selected.len);
    for (selected, 0..) |maybe_pool_index, idx| {
        if (idx < generated.len) {
            if (generated[idx]) |application| {
                refs[idx] = .{ .application = application };
                continue;
            }
        }
        const pool_index = maybe_pool_index orelse return error.MissingRef;
        refs[idx] = pool[pool_index].ref;
    }
    return refs;
}

// Rank a selection for ordering. A generated slot sorts after any real pool ref
// (we prefer existing refs to synthesized chains) by ranking it as `pool_len`.
fn rankSelectedReferenceIndices(
    pool_len: usize,
    selected: []const ?usize,
    generated: []const ?RuleApplication,
) usize {
    var pool_indices_buf: [64]usize = undefined;
    if (selected.len <= pool_indices_buf.len) {
        const indices = pool_indices_buf[0..selected.len];
        for (selected, 0..) |maybe_pool_index, idx| {
            indices[idx] = slotRankIndex(maybe_pool_index, generated, idx, pool_len);
        }
        return rankReferenceIndices(pool_len + 1, indices);
    }
    var rank_value: usize = 0;
    for (selected, 0..) |maybe_pool_index, idx| {
        rank_value = std.math.mul(usize, rank_value, pool_len + 1) catch
            std.math.maxInt(usize);
        rank_value = std.math.add(
            usize,
            rank_value,
            slotRankIndex(maybe_pool_index, generated, idx, pool_len),
        ) catch std.math.maxInt(usize);
    }
    return rank_value;
}

fn slotRankIndex(
    maybe_pool_index: ?usize,
    generated: []const ?RuleApplication,
    idx: usize,
    pool_len: usize,
) usize {
    if (idx < generated.len and generated[idx] != null) return pool_len;
    return maybe_pool_index orelse 0;
}
