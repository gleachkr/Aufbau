const std = @import("std");
const types = @import("./types.zig");
const timer = @import("./timer.zig");
const TheoremContext = @import("../../expr.zig").TheoremContext;
const ProofScript = @import("../../proof_script.zig");
const RuleApplication = ProofScript.RuleApplication;
const CompilerContext = @import("../context.zig").CompilerContext;
const CheckedIr = @import("../../checked_ir.zig");
const CheckedLine = CheckedIr.CheckedLine;
const Check = @import("../check.zig");
const Goal = types.Goal;
const Context = types.Context;
const AttemptOptions = types.AttemptOptions;
const NameExprMap = types.NameExprMap;

/// A successful non-committing attempt. It BORROWS the probed theorem:
/// `theorem` is a copy-on-write clone layered over the caller's theorem, so
/// the probe must be deinitialized before that theorem is mutated, moved, or
/// destroyed. `checked_lines` (the attempt's new lines, indexed from
/// `checked_start`) and `theorem_vars` are owned.
pub const Probe = struct {
    allocator: std.mem.Allocator,
    line_idx: usize,
    checked_start: usize,
    checked_lines: []const CheckedLine,
    theorem: TheoremContext,
    theorem_vars: NameExprMap,

    pub fn deinit(self: *Probe) void {
        CheckedIr.deinitLines(self.allocator, self.checked_lines);
        self.allocator.free(self.checked_lines);
        self.theorem_vars.deinit();
        self.theorem.deinit();
        self.* = undefined;
    }

    /// The checked line the application produced, or null if `line_idx`
    /// falls outside the attempt's new lines.
    pub fn line(self: *const Probe) ?CheckedLine {
        if (self.line_idx < self.checked_start) return null;
        const local_idx = self.line_idx - self.checked_start;
        if (local_idx >= self.checked_lines.len) return null;
        return self.checked_lines[local_idx];
    }
};

/// Check `application` against `goal` without touching the caller's state.
/// Inline-conclusion sink entries recorded by the attempt are dropped, and
/// the caller's diagnostic is restored, whether it succeeds or fails.
pub fn probe(
    compiler: *CompilerContext,
    context: *const Context,
    application: RuleApplication,
    goal: Goal,
    theorem: *const TheoremContext,
    theorem_vars: *const NameExprMap,
    options: AttemptOptions,
) !Probe {
    const sink_mark = if (compiler.inline_conclusion_sink) |sink| sink.mark() else 0;
    defer if (compiler.inline_conclusion_sink) |sink| sink.rollback(sink_mark);
    const result = try tryCandidate(
        compiler,
        context,
        application,
        goal,
        theorem,
        theorem_vars,
        options,
    );
    return .{
        .allocator = context.allocator,
        .line_idx = result.line_idx,
        .checked_start = result.checked_start,
        .checked_lines = result.checked_lines,
        .theorem = result.theorem,
        .theorem_vars = result.theorem_vars,
    };
}

/// Check `application` against `goal` and, on success, append its lines to
/// `context.checked` and replace `theorem`/`theorem_vars` with the attempt's
/// state. Returns the index of the produced line in `context.checked`. On
/// failure the caller's state is untouched.
pub fn commit(
    compiler: *CompilerContext,
    context: *const Context,
    application: RuleApplication,
    goal: Goal,
    theorem: *TheoremContext,
    theorem_vars: *NameExprMap,
    options: AttemptOptions,
) !usize {
    const allocator = context.allocator;
    var result = try tryCandidate(
        compiler,
        context,
        application,
        goal,
        theorem,
        theorem_vars,
        options,
    );
    defer allocator.free(result.checked_lines);
    errdefer {
        CheckedIr.deinitLines(allocator, result.checked_lines);
        result.theorem_vars.deinit();
        result.theorem.deinit();
    }
    try context.checked.ensureUnusedCapacity(allocator, result.checked_lines.len);
    try theorem.promote(&result.theorem);
    context.checked.appendSliceAssumeCapacity(result.checked_lines);
    theorem_vars.deinit();
    theorem_vars.* = result.theorem_vars;
    return result.line_idx;
}

const AttemptOutput = struct {
    line_idx: usize,
    checked_start: usize,
    checked_lines: []const CheckedLine,
    theorem: TheoremContext,
    theorem_vars: NameExprMap,
};

/// Validate one assembly: run the checker on COW clones of the caller's
/// theorem and vars and a scratch copy of the checked IR. The caller's state
/// is only read; `probe` and `commit` decide what happens to the result.
fn tryCandidate(
    compiler: *CompilerContext,
    context: *const Context,
    application: RuleApplication,
    goal: Goal,
    theorem: *const TheoremContext,
    theorem_vars: *const NameExprMap,
    options: AttemptOptions,
) !AttemptOutput {
    const allocator = context.allocator;
    const saved_diag = compiler.getDiagnostic();

    // Timers are diagnostics, gated by `collect` so production (whose counters
    // block exists only for the result's status flags) does not pay clock reads
    // per candidate.
    const collect = if (options.counters) |c| c.collect else false;
    const clone_start = if (collect) timer.nanoTimestamp() else 0;
    var attempt_theorem = try theorem.clone();
    errdefer attempt_theorem.deinit();
    var attempt_theorem_vars = try Check.cloneNameExprMap(
        allocator,
        theorem_vars,
    );
    errdefer attempt_theorem_vars.deinit();

    var scratch_checked = std.ArrayListUnmanaged(CheckedLine).empty;
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

    const line_idx = Check.applyRuleApplication(
        compiler,
        &attempt_context,
        application,
        try goal.lineAssertion(&attempt_theorem, context.env),
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

    return .{
        .line_idx = line_idx,
        .checked_start = checked_mark,
        .checked_lines = new_lines,
        .theorem = attempt_theorem,
        .theorem_vars = attempt_theorem_vars,
    };
}
