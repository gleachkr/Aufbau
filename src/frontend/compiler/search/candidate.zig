const std = @import("std");
const types = @import("./types.zig");
const timer = @import("./timer.zig");
const TheoremContext = @import("../../expr.zig").TheoremContext;
const ProofScript = @import("../../proof_script.zig");
const RuleApplication = ProofScript.RuleApplication;
const Span = ProofScript.Span;
const CompilerContext = @import("../context.zig").CompilerContext;
const CheckedIr = @import("../../checked_ir.zig");
const CheckedLine = CheckedIr.CheckedLine;
const Check = @import("../check.zig");
const Goal = types.Goal;
const Context = types.Context;
const AttemptOptions = types.AttemptOptions;
const AttemptResult = types.AttemptResult;
const NameExprMap = types.NameExprMap;

/// Mirror of `validateSelectedRefs`' explicit-binding retry guard: a bare
/// assembly (no rendered bindings) that fails with one of these errors is NOT a
/// terminal reject — the caller retries it with explicit bindings and may
/// succeed. Such rejects must not be memoized (see `tryCandidate`). The
/// UnifyMismatch arm's view/meta scoping lives with the caller and arrives via
/// `AttemptOptions.unify_retry_eligible`, so the two gates cannot drift.
fn retryEligibleReject(
    err: anyerror,
    application: RuleApplication,
    goal: Goal,
    unify_retry_eligible: bool,
) bool {
    if (application.arg_bindings.len != 0) return false;
    return err == error.MissingBinderAssignment or
        (err == error.HypothesisMismatch and goal == .implicit_whole_conclusion) or
        (err == error.UnifyMismatch and unify_retry_eligible);
}

/// Non-committing probe variant of `tryCandidate` for callers holding const
/// theorem state. A non-commit attempt treats the base theorem/vars as
/// read-only: `tryCandidate` clones both up front and only its commit branch
/// ever writes back through the pointers. Probing therefore needs no caller
/// pre-clone — the pre-clone pattern this replaces added one copy-on-write
/// chain level (and a full vars-map copy) under every intern probe of the
/// whole validation, purely to satisfy the mutable signature.
pub fn tryCandidateProbe(
    compiler: *CompilerContext,
    context: *const Context,
    application: RuleApplication,
    goal: Goal,
    theorem: *const TheoremContext,
    theorem_vars: *const NameExprMap,
    options: AttemptOptions,
) !AttemptResult {
    std.debug.assert(!options.commit);
    return tryCandidate(
        compiler,
        context,
        application,
        goal,
        @constCast(theorem),
        @constCast(theorem_vars),
        options,
    );
}

pub fn tryCandidate(
    compiler: *CompilerContext,
    context: *const Context,
    application: RuleApplication,
    goal: Goal,
    theorem: *TheoremContext,
    theorem_vars: *NameExprMap,
    options: AttemptOptions,
) !AttemptResult {
    const allocator = context.allocator;
    const saved_diag = compiler.getDiagnostic();

    // Lever A: cross-phase reject-verdict memo. The verdict is a pure function
    // of (application assembly, goal, fixed base theorem); a rejected assembly
    // rejects identically in every later phase. In measurement mode we only
    // observe (record rejects); when `skip_enabled` we also short-circuit a
    // known-rejecting assembly before the expensive re-derivation.
    //
    // Holey goals are excluded: their signature would key on a raw `*const Expr`
    // address (`applicationSignature`), which is ABA-unstable across phases, so a
    // freed-and-reused holey goal could alias a stale reject. Concrete and
    // implicit-whole-conclusion goals key on scope-stable canonical goal content
    // (`hashCanonicalContent`).
    const verdict_memo: ?*types.VerdictMemo = switch (goal) {
        .holey => null,
        else => if (options.counters) |c| c.verdict_memo else null,
    };
    const verdict_sig: u64 = if (verdict_memo != null)
        types.applicationSignature(theorem, application, goal)
    else
        0;
    if (verdict_memo) |m| {
        if (m.skip_enabled and m.rejectedBefore(verdict_sig)) {
            m.skips += 1;
            return error.MemoizedReject;
        }
    }

    // Timers are diagnostics, gated by `collect` so production (which carries a
    // counters block only for the memo) does not pay clock reads per candidate.
    const collect = if (options.counters) |c| c.collect else false;
    const clone_start = if (collect) timer.nanoTimestamp() else 0;
    var attempt_theorem = try theorem.clone();
    errdefer attempt_theorem.deinit();
    var attempt_theorem_vars = try Check.cloneNameExprMap(
        allocator,
        theorem_vars,
    );
    errdefer attempt_theorem_vars.deinit();

    var scratch_checked = std.ArrayListUnmanaged(CheckedLine){};
    defer scratch_checked.deinit(allocator);
    try scratch_checked.appendSlice(allocator, context.checked.items);
    const checked_mark = scratch_checked.items.len;

    var attempt_context = context.ruleApplyContext(allocator, &scratch_checked);
    const line = Check.ApplicationLine{
        .label = options.line_label,
        .application = application,
        .assertion_span = options.assertion_span,
    };
    const diag_context = Check.ApplicationDiagnosticContext{
        .theorem_name = context.assertion.name,
        .line_label = options.line_label,
        .span = options.diagnostic_span,
    };
    const diag_mark = context.diag_scratch.mark();

    if (collect) {
        if (options.counters) |c| {
            c.tc_clone_ns += @intCast(@max(0, timer.nanoTimestamp() - clone_start));
        }
    }
    const apply_start = if (collect) timer.nanoTimestamp() else 0;

    const attempt = Check.applyRuleApplication(
        compiler,
        &attempt_context,
        application,
        goal.lineAssertion(),
        goal.expectedHint(),
        diag_context,
        line,
        &attempt_theorem,
        &attempt_theorem_vars,
    ) catch |err| {
        if (collect) {
            if (options.counters) |c| {
                c.tc_apply_ns += @intCast(@max(0, timer.nanoTimestamp() - apply_start));
            }
        }
        // A checker rejection is a monotone verdict for THIS assembly — but only
        // a TERMINAL one. A bare assembly (no explicit bindings) that fails with
        // a retry-eligible error is not terminal: `validateSelectedRefs` retries
        // it with explicitly rendered bindings and can SUCCEED, so memoizing the
        // bare reject would make a later re-encounter short-circuit to
        // `error.MemoizedReject` and skip that retry, losing a winnable proof.
        // Mirror the caller's retry guard exactly, and never memoize OOM (a
        // transient resource error, not a verdict).
        if (verdict_memo) |m| {
            if (err != error.OutOfMemory and
                !retryEligibleReject(err, application, goal, options.unify_retry_eligible))
            {
                m.recordReject(verdict_sig);
            }
        }
        CheckedIr.rollbackToMark(allocator, &scratch_checked, checked_mark);
        context.diag_scratch.discard(diag_mark);
        compiler.restoreDiagnostic(saved_diag);
        return err;
    };
    if (collect) {
        if (options.counters) |c| {
            c.tc_apply_ns += @intCast(@max(0, timer.nanoTimestamp() - apply_start));
        }
    }
    context.diag_scratch.discard(diag_mark);
    compiler.restoreDiagnostic(saved_diag);

    errdefer CheckedIr.rollbackToMark(
        allocator,
        &scratch_checked,
        checked_mark,
    );
    const new_lines = try allocator.dupe(
        CheckedLine,
        scratch_checked.items[checked_mark..],
    );
    scratch_checked.shrinkRetainingCapacity(checked_mark);

    if (options.commit) {
        errdefer {
            CheckedIr.deinitLines(allocator, new_lines);
            allocator.free(new_lines);
        }
        // Materialize the COW clone before it replaces (and frees) its base.
        try attempt_theorem.flatten();
        try context.checked.appendSlice(allocator, new_lines);
        var old_theorem = theorem.*;
        theorem.* = attempt_theorem;
        old_theorem.deinit();
        theorem_vars.deinit();
        theorem_vars.* = attempt_theorem_vars;
        return .{
            .allocator = allocator,
            .committed = true,
            .line_idx = attempt.line_idx,
            .checked_start = checked_mark,
            .checked_lines = new_lines,
            .theorem = null,
            .theorem_vars = null,
        };
    }

    if (options.result_ownership == .owned) {
        errdefer {
            CheckedIr.deinitLines(allocator, new_lines);
            allocator.free(new_lines);
        }
        try attempt_theorem.flatten();
    }

    return .{
        .allocator = allocator,
        .committed = false,
        .line_idx = attempt.line_idx,
        .checked_start = checked_mark,
        .checked_lines = new_lines,
        .theorem = attempt_theorem,
        .theorem_vars = attempt_theorem_vars,
    };
}
