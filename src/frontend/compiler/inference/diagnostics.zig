const std = @import("std");
const ExprId = @import("../../expr.zig").ExprId;
const TheoremContext = @import("../../expr.zig").TheoremContext;
const GlobalEnv = @import("../../env.zig").GlobalEnv;
const RuleDecl = @import("../../env.zig").RuleDecl;
const AssertionStmt = @import("../../parse_recovery.zig").AssertionStmt;
const CompilerDiag = @import("../diag.zig");
const ViewTrace = @import("../../view_trace.zig");
const text_util = @import("../../text_util.zig");
const HiddenWitnessFreshContext =
    @import("context.zig").HiddenWitnessFreshContext;
const ReplayMismatch = @import("context.zig").ReplayMismatch;
const DebugConfig = @import("../../debug.zig").DebugConfig;
const DebugTrace = @import("../../debug.zig");

const Diagnostic = CompilerDiag.Diagnostic;
const InferencePath = CompilerDiag.InferencePath;

const BindingSummaryMode = enum {
    explicit,
    inferred,
};

pub fn buildInferenceFailureDiagnostic(
    allocator: std.mem.Allocator,
    env: *const GlobalEnv,
    theorem: *const TheoremContext,
    assertion: AssertionStmt,
    rule: *const RuleDecl,
    line: anytype,
    path: InferencePath,
    err: anyerror,
    explicit_bindings: []const ?ExprId,
    current_bindings: []const ?ExprId,
    fresh_context: ?HiddenWitnessFreshContext,
    mismatch: ?ReplayMismatch,
) !Diagnostic {
    var diag = CompilerDiag.withPhase(.{
        .kind = .inference_failed,
        .err = CompilerDiag.narrowDiagnosticError(err),
        .theorem_name = assertion.name,
        .line_label = line.label,
        .rule_name = line.application.rule_name,
        .span = line.ruleApplicationSpan(),
        .detail = .{ .inference_failure = .{
            .path = path,
            .first_unsolved_binder_name = firstUnsolvedNamedBinder(rule, current_bindings),
        } },
    }, .inference);
    var names = optionalDiagNames(allocator, theorem, fresh_context);
    defer names.deinit(allocator);
    const names_ptr = names.ptr();
    if (mismatch) |site| {
        try addReplayMismatchNotes(
            allocator,
            &diag,
            env,
            theorem,
            rule,
            site,
            names_ptr,
        );
    }
    try addInferenceNotesNamed(
        allocator,
        &diag,
        env,
        theorem,
        rule,
        explicit_bindings,
        current_bindings,
        names_ptr,
    );
    return diag;
}

pub fn buildMissingBinderDiagnostic(
    allocator: std.mem.Allocator,
    env: *const GlobalEnv,
    theorem: *const TheoremContext,
    assertion: AssertionStmt,
    rule: *const RuleDecl,
    line: anytype,
    path: InferencePath,
    explicit_bindings: []const ?ExprId,
    current_bindings: []const ?ExprId,
    missing_idx: usize,
    fresh_context: ?HiddenWitnessFreshContext,
) !Diagnostic {
    const binder_name = rule.arg_names[missing_idx] orelse "_";
    var diag = CompilerDiag.withPhase(.{
        .kind = .missing_binder_assignment,
        .err = error.MissingBinderAssignment,
        .theorem_name = assertion.name,
        .line_label = line.label,
        .rule_name = line.application.rule_name,
        .name = rule.arg_names[missing_idx],
        .span = line.application.binding_list_span orelse line.application.rule_span,
        .detail = .{ .missing_binder_assignment = .{
            .binder_name = binder_name,
            .path = path,
        } },
    }, .inference);
    try addInferenceNotes(
        allocator,
        &diag,
        env,
        theorem,
        rule,
        explicit_bindings,
        current_bindings,
        fresh_context,
    );
    return diag;
}

pub fn addInferenceNotes(
    allocator: std.mem.Allocator,
    diag: *Diagnostic,
    env: *const GlobalEnv,
    theorem: *const TheoremContext,
    rule: *const RuleDecl,
    explicit_bindings: []const ?ExprId,
    current_bindings: []const ?ExprId,
    fresh_context: ?HiddenWitnessFreshContext,
) !void {
    var names = optionalDiagNames(allocator, theorem, fresh_context);
    defer names.deinit(allocator);
    try addInferenceNotesNamed(
        allocator,
        diag,
        env,
        theorem,
        rule,
        explicit_bindings,
        current_bindings,
        names.ptr(),
    );
}

/// Render binding values with declared notation and real binder names when a
/// notation provider + binder map are available; otherwise fall back to the
/// internal prefix/coordinate form inside `buildBindingSummary`.
fn optionalDiagNames(
    allocator: std.mem.Allocator,
    theorem: *const TheoremContext,
    fresh_context: ?HiddenWitnessFreshContext,
) ViewTrace.OptionalDiagNames {
    return ViewTrace.OptionalDiagNames.build(
        allocator,
        theorem,
        if (fresh_context) |fresh| fresh.parser else null,
        if (fresh_context) |fresh| fresh.theorem_vars else null,
    );
}

// The inference path and the first unsolved binder are carried in the
// diagnostic's structured detail; repeating them as notes made every
// renderer print them twice. Notes here only add what the detail
// cannot: the binding summaries (skipped when empty).
fn addInferenceNotesNamed(
    allocator: std.mem.Allocator,
    diag: *Diagnostic,
    env: *const GlobalEnv,
    theorem: *const TheoremContext,
    rule: *const RuleDecl,
    explicit_bindings: []const ?ExprId,
    current_bindings: []const ?ExprId,
    names_ptr: ?*const ViewTrace.DiagNames,
) !void {
    const explicit_summary = try buildBindingSummary(
        allocator,
        theorem,
        env,
        rule,
        explicit_bindings,
        current_bindings,
        .explicit,
        names_ptr,
    );
    if (std.mem.eql(u8, explicit_summary, "none")) {
        allocator.free(explicit_summary);
    } else {
        addInferenceNote(diag, .{ .explicit_bindings = .{
            .summary = explicit_summary,
        } });
    }

    const inferred_summary = try buildBindingSummary(
        allocator,
        theorem,
        env,
        rule,
        explicit_bindings,
        current_bindings,
        .inferred,
        names_ptr,
    );
    if (std.mem.eql(u8, inferred_summary, "none")) {
        allocator.free(inferred_summary);
    } else {
        addInferenceNote(diag, .{ .inferred_bindings_before_failure = .{
            .summary = inferred_summary,
        } });
    }
}

/// Turn the strict-replay clash site into notes that describe the failure at
/// the logical level: which part of the rule application failed to match and
/// which expressions clashed. Deliberately no advice about proof-file syntax:
/// frontends generate proof files from GUIs, so "what went wrong" must stand
/// on its own.
fn addReplayMismatchNotes(
    allocator: std.mem.Allocator,
    diag: *Diagnostic,
    env: *const GlobalEnv,
    theorem: *const TheoremContext,
    rule: *const RuleDecl,
    mismatch: ReplayMismatch,
    names_ptr: ?*const ViewTrace.DiagNames,
) !void {
    switch (mismatch.region) {
        .conclusion => addInferenceNote(diag, .conclusion_replay_mismatch),
        .hypothesis => |idx| addInferenceNote(
            diag,
            .{ .premise_hypothesis_mismatch = .{ .number = idx + 1 } },
        ),
    }
    switch (mismatch.kind) {
        .term_shape => |shape| {
            const term_name = if (shape.expected_term_id < env.terms.items.len)
                env.terms.items[shape.expected_term_id].name
            else
                "?";
            const actual_text = try formatMismatchExpr(
                allocator,
                theorem,
                env,
                names_ptr,
                shape.actual,
            );
            addInferenceNote(diag, .{ .rule_requires_term_at_mismatch = .{
                .term_name = term_name,
                .found_text = truncateMismatchText(actual_text),
            } });
        },
        .repeat_conflict => |conflict| {
            const first_text = try formatMismatchExpr(
                allocator,
                theorem,
                env,
                names_ptr,
                conflict.first,
            );
            const second_text = try formatMismatchExpr(
                allocator,
                theorem,
                env,
                names_ptr,
                conflict.second,
            );
            const binder_name: ?[]const u8 =
                if (conflict.heap_id < rule.arg_names.len)
                    rule.arg_names[conflict.heap_id]
                else
                    null;
            if (binder_name) |name| {
                addInferenceNote(diag, .{ .rule_var_two_values = .{
                    .binder_name = name,
                } });
            } else {
                addInferenceNote(
                    diag,
                    .identical_positions_matched_differently,
                );
            }
            addInferenceNote(diag, .{ .already_matched = .{
                .text = truncateMismatchText(first_text),
            } });
            addInferenceNote(diag, .{ .at_the_mismatch = .{
                .text = truncateMismatchText(second_text),
            } });
        },
        .no_completion => |info| {
            addInferenceNote(diag, .no_rule_var_completion);
            if (mismatch.region == .hypothesis) {
                if (info.actual) |actual| {
                    const actual_text = try formatMismatchExpr(
                        allocator,
                        theorem,
                        env,
                        names_ptr,
                        actual,
                    );
                    addInferenceNote(diag, .{ .cited_premise_proves = .{
                        .text = truncateMismatchText(actual_text),
                    } });
                }
            }
        },
    }
}

fn formatMismatchExpr(
    allocator: std.mem.Allocator,
    theorem: *const TheoremContext,
    env: *const GlobalEnv,
    names_ptr: ?*const ViewTrace.DiagNames,
    expr_id: ExprId,
) ![]const u8 {
    if (names_ptr) |names| {
        return try ViewTrace.formatExprNamed(
            allocator,
            theorem,
            env,
            names,
            expr_id,
        );
    }
    return try ViewTrace.formatExpr(allocator, theorem, env, expr_id);
}

fn truncateMismatchText(text: []const u8) []const u8 {
    return text_util.truncateUtf8(text, 64);
}

pub fn addAmbiguityWarningNotes(
    diag: *Diagnostic,
    report: @import("../../inference_solver.zig").AmbiguityReport,
) void {
    if (report.chosen_bindings) |summary| {
        addInferenceNote(diag, .{ .chosen_bindings = .{
            .summary = summary,
        } });
    }
    if (report.alternative_bindings) |summary| {
        addInferenceNote(diag, .{ .alternative_bindings = .{
            .summary = summary,
        } });
    }
    addInferenceNote(diag, .{ .distinct_solutions_considered = .{
        .count = report.distinct_solution_count,
    } });
}

pub fn addInferenceNote(
    diag: *Diagnostic,
    message: CompilerDiag.NoteMessage,
) void {
    CompilerDiag.addNote(diag, message, .proof, null);
}

pub fn traceInferenceAttempt(
    config: DebugConfig,
    allocator: std.mem.Allocator,
    theorem: *const TheoremContext,
    env: *const GlobalEnv,
    rule: *const RuleDecl,
    path: InferencePath,
    explicit_bindings: []const ?ExprId,
    current_bindings: []const ?ExprId,
) !void {
    if (!config.inference) return;
    DebugTrace.traceInference(
        config,
        "trying {s} for rule {s}",
        .{ CompilerDiag.inferencePathName(path), rule.name },
    );
    try traceInferenceBindingSummaries(
        config,
        allocator,
        theorem,
        env,
        rule,
        explicit_bindings,
        current_bindings,
    );
}

pub fn traceInferenceFailure(
    config: DebugConfig,
    allocator: std.mem.Allocator,
    theorem: *const TheoremContext,
    env: *const GlobalEnv,
    rule: *const RuleDecl,
    path: InferencePath,
    err: anyerror,
    explicit_bindings: []const ?ExprId,
    current_bindings: []const ?ExprId,
) !void {
    if (!config.inference) return;
    DebugTrace.traceInference(
        config,
        "{s} failed for rule {s}: {s}",
        .{
            CompilerDiag.inferencePathName(path),
            rule.name,
            @errorName(err),
        },
    );
    try traceInferenceBindingSummaries(
        config,
        allocator,
        theorem,
        env,
        rule,
        explicit_bindings,
        current_bindings,
    );
}

fn traceInferenceBindingSummaries(
    config: DebugConfig,
    allocator: std.mem.Allocator,
    theorem: *const TheoremContext,
    env: *const GlobalEnv,
    rule: *const RuleDecl,
    explicit_bindings: []const ?ExprId,
    current_bindings: []const ?ExprId,
) !void {
    if (!config.inference) return;

    const explicit_summary = try buildBindingSummary(
        allocator,
        theorem,
        env,
        rule,
        explicit_bindings,
        current_bindings,
        .explicit,
        null,
    );
    defer allocator.free(explicit_summary);
    DebugTrace.traceInference(
        config,
        "  explicit bindings: {s}",
        .{explicit_summary},
    );

    const inferred_summary = try buildBindingSummary(
        allocator,
        theorem,
        env,
        rule,
        explicit_bindings,
        current_bindings,
        .inferred,
        null,
    );
    defer allocator.free(inferred_summary);
    DebugTrace.traceInference(
        config,
        "  inferred bindings: {s}",
        .{inferred_summary},
    );

    if (firstUnsolvedNamedBinder(rule, current_bindings)) |label| {
        DebugTrace.traceInference(
            config,
            "  first unsolved binder: {s}",
            .{label},
        );
    }
}

fn buildBindingSummary(
    allocator: std.mem.Allocator,
    theorem: *const TheoremContext,
    env: *const GlobalEnv,
    rule: *const RuleDecl,
    explicit_bindings: []const ?ExprId,
    current_bindings: []const ?ExprId,
    mode: BindingSummaryMode,
    names: ?*const ViewTrace.DiagNames,
) ![]const u8 {
    var out = std.ArrayListUnmanaged(u8){};
    errdefer out.deinit(allocator);

    var emitted: usize = 0;
    var remaining: usize = 0;
    for (current_bindings, 0..) |binding, idx| {
        const is_explicit = idx < explicit_bindings.len and
            explicit_bindings[idx] != null;
        const include = switch (mode) {
            .explicit => is_explicit,
            .inferred => !is_explicit and binding != null,
        };
        if (!include) continue;

        if (emitted == 3) {
            remaining += 1;
            continue;
        }
        if (emitted != 0) {
            try out.appendSlice(allocator, "; ");
        }
        try appendBindingEntry(
            &out,
            allocator,
            theorem,
            env,
            rule,
            idx,
            binding,
            names,
        );
        emitted += 1;
    }

    if (emitted == 0) {
        try out.appendSlice(allocator, "none");
    } else if (remaining != 0) {
        try out.writer(allocator).print(
            "; +{d} more",
            .{remaining},
        );
    }
    return try out.toOwnedSlice(allocator);
}

fn appendBindingEntry(
    out: *std.ArrayListUnmanaged(u8),
    allocator: std.mem.Allocator,
    theorem: *const TheoremContext,
    env: *const GlobalEnv,
    rule: *const RuleDecl,
    idx: usize,
    binding: ?ExprId,
    names: ?*const ViewTrace.DiagNames,
) !void {
    try out.appendSlice(allocator, binderLabel(rule, idx));
    try out.appendSlice(allocator, " = ");
    if (binding) |expr_id| {
        const text = if (names) |names_ptr|
            try ViewTrace.formatExprNamed(
                allocator,
                theorem,
                env,
                names_ptr,
                expr_id,
            )
        else
            try ViewTrace.formatExpr(allocator, theorem, env, expr_id);
        defer allocator.free(text);
        try appendInferenceTruncatedText(out, allocator, text, 48);
        return;
    }
    try out.appendSlice(allocator, "<unsolved>");
}

fn appendInferenceTruncatedText(
    out: *std.ArrayListUnmanaged(u8),
    allocator: std.mem.Allocator,
    text: []const u8,
    limit: usize,
) !void {
    if (text.len <= limit) {
        try out.appendSlice(allocator, text);
        return;
    }
    if (limit <= 1) {
        try out.appendSlice(allocator, text[0..limit]);
        return;
    }
    try out.appendSlice(allocator, text_util.truncateUtf8(text, limit - 1));
    try out.appendSlice(allocator, "...");
}

pub fn firstUnsolvedNamedBinder(
    rule: *const RuleDecl,
    bindings: []const ?ExprId,
) ?[]const u8 {
    for (bindings, 0..) |binding, idx| {
        if (binding != null) continue;
        if (idx < rule.arg_names.len) {
            if (rule.arg_names[idx]) |name| return name;
        }
        return null;
    }
    return null;
}

fn binderLabel(rule: *const RuleDecl, idx: usize) []const u8 {
    if (idx < rule.arg_names.len) {
        if (rule.arg_names[idx]) |name| return name;
    }
    return "_";
}
