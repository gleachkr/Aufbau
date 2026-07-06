const std = @import("std");
const types = @import("./types.zig");
const TheoremContext = @import("../../expr.zig").TheoremContext;
const ProofScript = @import("../../proof_script.zig");
const RuleApplication = ProofScript.RuleApplication;
const CompilerContext = @import("../context.zig").CompilerContext;
const Check = @import("../check.zig");
const rank = @import("./rank.zig");
const session_mod = @import("./session.zig");
const Goal = types.Goal;
const Context = types.Context;
const ApplyCandidate = types.ApplyCandidate;
const ApplyOptions = types.ApplyOptions;
const ApplyResults = types.ApplyResults;
const NameExprMap = types.NameExprMap;
const applyCandidateLessThan = rank.applyCandidateLessThan;

pub fn apply(
    compiler: *CompilerContext,
    context: *const Context,
    goal: Goal,
    theorem: *const TheoremContext,
    theorem_vars: *const NameExprMap,
    options: ApplyOptions,
) !ApplyResults {
    var session = session_mod.SearchSession.init(context, .{
        .counters = options.counters,
    });
    defer session.deinit();
    return applyWithSession(
        compiler,
        &session,
        goal,
        theorem,
        theorem_vars,
        options,
    );
}

pub fn applyWithSession(
    compiler: *CompilerContext,
    session: *session_mod.SearchSession,
    goal: Goal,
    theorem: *const TheoremContext,
    theorem_vars: *const NameExprMap,
    options: ApplyOptions,
) !ApplyResults {
    const context = session.context;
    const allocator = context.allocator;
    const counters = session.effectiveCounters(options.counters);
    var candidates = std.ArrayListUnmanaged(ApplyCandidate){};
    errdefer {
        for (candidates.items) |*candidate| {
            candidate.deinit();
        }
        candidates.deinit(allocator);
    }

    const candidate_rule_ids = try session.candidateRuleIds(
        goal,
        theorem,
        options.use_rule_index,
        counters,
    );
    defer allocator.free(candidate_rule_ids);
    if (counters) |actual| {
        actual.candidate_rules_before_conclusion_validation +=
            candidate_rule_ids.len;
    }

    const saved_diag = compiler.getDiagnostic();
    for (candidate_rule_ids) |rule_id| {
        // Relation-transport rules (e.g. `mpbi`) match every goal backward but are
        // never a backward proof step — screen them on all paths, matching the
        // `exact?` candidate loop. See `RewriteRegistry.isRelationTransport`.
        if (context.registry.isRelationTransport(context.env, rule_id)) continue;
        const rule_idx: usize = @intCast(rule_id);
        const rule = context.env.rules.items[rule_idx];
        var attempt_theorem = try theorem.clone();
        var attempt_theorem_owned = true;
        errdefer if (attempt_theorem_owned) attempt_theorem.deinit();
        var attempt_vars = try Check.cloneNameExprMap(
            allocator,
            theorem_vars,
        );
        var attempt_vars_owned = true;
        errdefer if (attempt_vars_owned) attempt_vars.deinit();
        const diag_mark = context.diag_scratch.mark();
        const application = RuleApplication{
            .rule_name = rule.name,
            .rule_span = .{ .start = 0, .end = 0 },
            .span = .{ .start = 0, .end = 0 },
        };
        const line = Check.ApplicationLine{
            .label = "<search>",
            .application = application,
            .assertion_span = .{ .start = 0, .end = 0 },
        };
        const diag_context = Check.ApplicationDiagnosticContext{
            .theorem_name = context.assertion.name,
            .line_label = "<search>",
            .span = null,
        };

        const apply_context = Check.RuleApplyContext{
            .allocator = allocator,
            .parser = context.parser,
            .env = context.env,
            .registry = context.registry,
            .rule_catalog = context.rule_catalog,
            .fresh_bindings = context.fresh_bindings,
            .freshen_bindings = context.freshen_bindings,
            .views = context.views,
            .sort_vars = context.sort_vars,
            .assertion = context.assertion,
            .labels = context.labels,
            .checked = context.checked,
            .diag_scratch = context.diag_scratch,
            .rule_unify_cache = context.rule_unify_cache,
        };
        if (counters) |actual| {
            actual.conclusion_probes += 1;
        }
        var probe = Check.probeRuleConclusion(
            compiler,
            &apply_context,
            application,
            goal.lineAssertion(),
            goal.expectedHint(),
            diag_context,
            line,
            @intCast(rule_idx),
            &attempt_theorem,
            &attempt_vars,
        ) catch |err| {
            if (err == error.OutOfMemory) return err;
            if (counters) |actual| {
                actual.rejected_candidates_after_validation += 1;
            }
            context.diag_scratch.discard(diag_mark);
            compiler.restoreDiagnostic(saved_diag);
            attempt_vars.deinit();
            attempt_vars_owned = false;
            attempt_theorem.deinit();
            attempt_theorem_owned = false;
            continue;
        };
        errdefer probe.deinit();
        context.diag_scratch.discard(diag_mark);
        compiler.restoreDiagnostic(saved_diag);
        attempt_vars.deinit();
        attempt_vars_owned = false;

        if (counters) |actual| {
            actual.accepted_candidates += 1;
        }
        try attempt_theorem.flatten();
        try candidates.append(allocator, .{
            .allocator = allocator,
            .rule_id = probe.rule_id,
            .rule_name = probe.rule_name,
            .declaration_order = rule_idx,
            .theorem = attempt_theorem,
            .bindings = probe.bindings,
            .conclusion = probe.displayed_conclusion,
            .unresolved_hyps = probe.unresolved_hyps,
        });
        attempt_theorem_owned = false;
        probe.bindings = &.{};
        probe.unresolved_hyps = &.{};
        probe.deinit();
    }
    compiler.restoreDiagnostic(saved_diag);
    std.mem.sort(
        ApplyCandidate,
        candidates.items,
        {},
        applyCandidateLessThan,
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
