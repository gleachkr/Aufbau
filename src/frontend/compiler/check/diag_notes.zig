const std = @import("std");
const ExprId = @import("../../expr.zig").ExprId;
const TheoremContext = @import("../../expr.zig").TheoremContext;
const GlobalEnv = @import("../../env.zig").GlobalEnv;
const RuleDecl = @import("../../env.zig").RuleDecl;
const AssertionStmt = @import("../../parse_recovery.zig").AssertionStmt;
const ExprModule = @import("../../../trusted/expressions.zig");
const Expr = ExprModule.Expr;
const SourceSpan = ExprModule.SourceSpan;
const Span = @import("../../proof_script.zig").Span;
const RewriteRegistry = @import("../../rewrite_registry.zig").RewriteRegistry;
const CompilerDiag = @import("../diag.zig");
const CompilerContext = @import("../context.zig").CompilerContext;
const AlphaRewrite = @import("../alpha_rewrite.zig");
const Normalize = @import("../normalize.zig");
const Holes = @import("../holes.zig");
const TheoremBoundary = @import("../theorem_boundary.zig");
const ViewTrace = @import("../../view_trace.zig");
const text_util = @import("../../text_util.zig");
const Diagnostic = CompilerDiag.Diagnostic;
const HiddenWitnessFreshContext =
    @import("../inference/context.zig").HiddenWitnessFreshContext;
const MM0Parser = @import("../../parse_recovery.zig").MM0Parser;

const SurfaceExpr = @import("../../surface_expr.zig");
const ArgInfo = @import("../../parse_recovery.zig").ArgInfo;

pub const sort_retry_note_buf_len = 192;

/// A math string that failed sort-directed coercion (rather than parsing)
/// gets a note naming the sort it actually has: re-parse it with no target
/// sort and report the root sort of the result. When even the sort-agnostic
/// parse fails, the mismatch sits inside the expression (a term argument of
/// the wrong sort) and the note says so instead — the trusted parser records
/// no position for argument coercions, so no tighter span is available.
/// `expected` carries the binder's ArgInfo, or null when the target is the
/// provable-sort slot (line assertions). `buf` must stay alive through
/// setProof; the sink stable-copies note strings at set time.
pub fn attachSortRetryNote(
    diag: *Diagnostic,
    buf: []u8,
    parser: *MM0Parser,
    theorem_vars: *const std.StringHashMap(*const Expr),
    expected: ?ArgInfo,
    math_text: []const u8,
) void {
    switch (diag.err) {
        error.SortMismatch,
        error.BoundnessMismatch,
        error.NotProvable,
        => {},
        else => return,
    }
    const expr = parser.parseMathText(math_text, theorem_vars) catch {
        switch (diag.err) {
            error.SortMismatch => addStaticProofNote(
                diag,
                "a subexpression here is used where a different " ++
                    "sort is expected",
            ),
            error.BoundnessMismatch => addStaticProofNote(
                diag,
                "a position inside this expression requires a " ++
                    "single bound variable",
            ),
            else => {},
        }
        return;
    };
    const actual = SurfaceExpr.parserSortName(parser, expr.sort());
    const message: []const u8 = switch (diag.err) {
        error.SortMismatch => blk: {
            const arg = expected orelse return;
            break :blk std.fmt.bufPrint(
                buf,
                "the assignment parses, but as sort '{s}'; this " ++
                    "binder expects sort '{s}'",
                .{ actual, arg.sort_name },
            ) catch return;
        },
        error.NotProvable => std.fmt.bufPrint(
            buf,
            "the statement parses, but as sort '{s}', which is " ++
                "not a provable sort",
            .{actual},
        ) catch return,
        error.BoundnessMismatch => "the assignment parses with the " ++
            "right sort, but this binder requires a single bound variable",
        else => unreachable,
    };
    addStaticProofNote(diag, message);
}

pub fn addFallbackFailureNote(
    diag: *Diagnostic,
    line_assertion: anytype,
    line: anytype,
) void {
    switch (line_assertion) {
        .concrete, .implicit_whole_conclusion => {},
        .holey => |holey| {
            addStaticProofNoteSpan(
                diag,
                "fallback chain exhausted for holey assertion; " ++
                    "showing first candidate failure",
                firstHoleProofSpan(line, holey),
            );
        },
    }
}

pub fn concreteMatchFailureSpan(
    line: anytype,
    report: Holes.ConcreteMatchReport,
) ?Span {
    const failure = report.failure orelse return null;
    return switch (failure) {
        .hole_sort_mismatch => |mismatch| proofSpanForSourceSpan(
            line,
            mismatch.token_span,
        ),
        .visible_structure_mismatch => null,
    };
}

fn firstHoleProofSpan(line: anytype, expr: *const Expr) ?Span {
    return proofSpanForSourceSpan(line, Holes.firstHoleSourceSpan(expr));
}

fn proofSpanForSourceSpan(
    line: anytype,
    maybe_span: ?SourceSpan,
) ?Span {
    const span = maybe_span orelse return null;
    const inner_start = line.assertion_span.start + 1;
    return .{
        .start = inner_start + span.start,
        .end = inner_start + span.end,
    };
}

pub fn setHoleyInferenceDiagnostic(
    self: *CompilerContext,
    allocator: std.mem.Allocator,
    env: *const GlobalEnv,
    theorem: *const TheoremContext,
    assertion: AssertionStmt,
    line: anytype,
    rule: *const RuleDecl,
    holey: *const Expr,
    err: anyerror,
    report: Holes.InferenceReport,
    fresh_context: ?HiddenWitnessFreshContext,
) !void {
    const failure = report.failure;
    const missing = if (failure) |actual| switch (actual) {
        .missing_binder => |info| info,
        else => null,
    } else null;

    const kind: CompilerDiag.DiagnosticKind = if (missing != null)
        .missing_binder_assignment
    else
        .inference_failed;
    const hole_span = firstHoleProofSpan(line, holey);
    const span = if (err == error.HoleyInferenceMismatch)
        hole_span orelse line.assertion_span
    else if (missing != null)
        hole_span orelse line.assertion_span
    else
        line.ruleApplicationSpan();
    const binder_name = if (missing) |info|
        info.name orelse "_"
    else
        null;
    var diag = CompilerDiag.withPhase(.{
        .kind = kind,
        .err = err,
        .theorem_name = assertion.name,
        .line_label = line.label,
        .rule_name = line.application.rule_name,
        .name = binder_name,
        .span = span,
        .detail = if (missing) |info| .{ .missing_binder_assignment = .{
            .binder_name = info.name orelse "_",
            .path = .holey_surface_match,
        } } else .{ .inference_failure = .{
            .path = .holey_surface_match,
            .first_unsolved_binder_name = null,
        } },
    }, .inference);
    try addHoleyInferenceNotes(
        allocator,
        &diag,
        env,
        theorem,
        rule,
        line,
        holey,
        report,
        fresh_context,
    );
    self.setProof(diag);
}

fn addHoleyInferenceNotes(
    allocator: std.mem.Allocator,
    diag: *Diagnostic,
    env: *const GlobalEnv,
    theorem: *const TheoremContext,
    rule: *const RuleDecl,
    line: anytype,
    holey: *const Expr,
    report: Holes.InferenceReport,
    fresh_context: ?HiddenWitnessFreshContext,
) !void {
    // The inference path is carried in the diagnostic's structured detail;
    // no note needed.
    const failure = report.failure orelse return;
    const hole_span = firstHoleProofSpan(line, holey);

    var names: ?ViewTrace.DiagNames = if (fresh_context) |fresh|
        try ViewTrace.DiagNames.build(
            allocator,
            theorem,
            fresh.parser,
            fresh.theorem_vars,
        )
    else
        null;
    defer if (names) |*n| n.deinit(allocator);
    const names_ptr: ?*const ViewTrace.DiagNames =
        if (names) |*n| n else null;

    switch (failure) {
        .hypothesis_mismatch => |info| {
            try addFormattedProofNote(
                allocator,
                diag,
                "cited premise {d} does not match hypothesis {d} of the rule",
                .{ info.index + 1, info.index + 1 },
            );
            const ref_text = try formatNoteExpr(
                allocator,
                theorem,
                env,
                names_ptr,
                info.ref_expr,
            );
            defer allocator.free(ref_text);
            try addFormattedProofNote(
                allocator,
                diag,
                "the cited premise proves: {s}",
                .{truncateSnapshot(ref_text)},
            );
        },
        .visible_structure_mismatch => |detail| {
            addStaticProofNoteSpan(
                diag,
                "the visible parts of the statement do not match " ++
                    "the rule's conclusion",
                hole_span,
            );
            try addVisibleMismatchNotes(
                allocator,
                diag,
                env,
                theorem,
                rule,
                detail,
                names_ptr,
            );
        },
        .missing_binder => |info| {
            const name = info.name orelse "_";
            try addFormattedProofNoteSpan(
                allocator,
                diag,
                "holey assertion left binder {s} unsolved",
                .{name},
                hole_span,
            );
            if (info.index < rule.arg_names.len and rule.arg_names[info.index] == null) {
                try addFormattedProofNote(
                    allocator,
                    diag,
                    "unsolved binder index: {d}",
                    .{info.index + 1},
                );
            }
        },
    }
}

fn addVisibleMismatchNotes(
    allocator: std.mem.Allocator,
    diag: *Diagnostic,
    env: *const GlobalEnv,
    theorem: *const TheoremContext,
    rule: *const RuleDecl,
    detail: Holes.VisibleMismatchDetail,
    names_ptr: ?*const ViewTrace.DiagNames,
) !void {
    switch (detail) {
        .unknown => {},
        .head_clash => |clash| {
            const expected_name = termNameById(env, clash.expected_term_id);
            if (clash.actual_term_id) |actual_id| {
                try addFormattedProofNote(
                    allocator,
                    diag,
                    "the rule's conclusion has '{s}' where the statement " ++
                        "has '{s}'",
                    .{ expected_name, termNameById(env, actual_id) },
                );
            } else {
                try addFormattedProofNote(
                    allocator,
                    diag,
                    "the rule's conclusion has '{s}' where the statement " ++
                        "has a variable",
                    .{expected_name},
                );
            }
        },
        .binder_conflict => |conflict| {
            const binder_name: ?[]const u8 =
                if (conflict.binder_idx < rule.arg_names.len)
                    rule.arg_names[conflict.binder_idx]
                else
                    null;
            if (binder_name) |name| {
                try addFormattedProofNote(
                    allocator,
                    diag,
                    "rule variable {s} would need two different values",
                    .{name},
                );
            } else {
                addStaticProofNote(
                    diag,
                    "one rule variable would need two different values",
                );
            }
            const existing_text = try formatNoteExpr(
                allocator,
                theorem,
                env,
                names_ptr,
                conflict.existing,
            );
            defer allocator.free(existing_text);
            try addFormattedProofNote(
                allocator,
                diag,
                "already matched: {s}",
                .{truncateSnapshot(existing_text)},
            );
            const actual_text = try formatNoteExpr(
                allocator,
                theorem,
                env,
                names_ptr,
                conflict.actual,
            );
            defer allocator.free(actual_text);
            try addFormattedProofNote(
                allocator,
                diag,
                "in the statement: {s}",
                .{truncateSnapshot(actual_text)},
            );
        },
    }
}

fn termNameById(env: *const GlobalEnv, term_id: u32) []const u8 {
    if (term_id < env.terms.items.len) return env.terms.items[term_id].name;
    return "?";
}

fn formatNoteExpr(
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

pub fn addHoleConcreteMatchNotes(
    allocator: std.mem.Allocator,
    diag: *Diagnostic,
    line: anytype,
    report: Holes.ConcreteMatchReport,
) !void {
    const failure = report.failure orelse return;
    switch (failure) {
        .visible_structure_mismatch => addStaticProofNote(
            diag,
            "the visible parts of the statement do not match " ++
                "the rule's conclusion",
        ),
        .hole_sort_mismatch => |mismatch| {
            try addFormattedProofNoteSpan(
                allocator,
                diag,
                "hole {s} expected sort {s} but matched {s}",
                .{
                    mismatch.token,
                    mismatch.expected_sort_name,
                    mismatch.actual_sort_name,
                },
                proofSpanForSourceSpan(line, mismatch.token_span),
            );
        },
    }
}

pub fn addComparisonSnapshotNotes(
    allocator: std.mem.Allocator,
    diag: *Diagnostic,
    theorem: *const TheoremContext,
    env: *const GlobalEnv,
    parser: anytype,
    theorem_vars: *const std.StringHashMap(*const Expr),
    registry: *RewriteRegistry,
    scratch: *CompilerDiag.Scratch,
    expected: ExprId,
    actual: ExprId,
    attempted_normalized: bool,
) !void {
    var names = try ViewTrace.DiagNames.build(
        allocator,
        theorem,
        parser,
        theorem_vars,
    );
    defer names.deinit(allocator);

    const expected_text = try ViewTrace.formatExprNamed(
        allocator,
        theorem,
        env,
        &names,
        expected,
    );
    defer allocator.free(expected_text);
    try addFormattedProofNote(
        allocator,
        diag,
        "expected: {s}",
        .{truncateSnapshot(expected_text)},
    );

    const actual_text = try ViewTrace.formatExprNamed(
        allocator,
        theorem,
        env,
        &names,
        actual,
    );
    defer allocator.free(actual_text);
    try addFormattedProofNote(
        allocator,
        diag,
        "actual: {s}",
        .{truncateSnapshot(actual_text)},
    );

    if (!attempted_normalized) return;

    const snapshot = Normalize.maybeBuildComparisonSnapshotWithDebug(
        allocator,
        @constCast(theorem),
        registry,
        env,
        scratch,
        expected,
        actual,
        .none,
    );
    if (snapshot.normalized_expected == null and
        snapshot.normalized_actual == null)
    {
        return;
    }

    addStaticProofNote(diag, "attempted normalized comparison");
    if (snapshot.normalized_expected) |normalized_expected| {
        const normalized_expected_text = try ViewTrace.formatExprNamed(
            allocator,
            theorem,
            env,
            &names,
            normalized_expected,
        );
        defer allocator.free(normalized_expected_text);
        try addFormattedProofNote(
            allocator,
            diag,
            "normalized expected: {s}",
            .{truncateSnapshot(normalized_expected_text)},
        );
    }
    if (snapshot.normalized_actual) |normalized_actual| {
        const normalized_actual_text = try ViewTrace.formatExprNamed(
            allocator,
            theorem,
            env,
            &names,
            normalized_actual,
        );
        defer allocator.free(normalized_actual_text);
        try addFormattedProofNote(
            allocator,
            diag,
            "normalized actual: {s}",
            .{truncateSnapshot(normalized_actual_text)},
        );
    }
}

fn truncateSnapshot(text: []const u8) []const u8 {
    return text_util.truncateUtf8(text, 64);
}

pub fn addFreshenAttemptNotes(
    allocator: std.mem.Allocator,
    diag: *Diagnostic,
    rule: *const RuleDecl,
    report: AlphaRewrite.FreshenAttemptReport,
) !void {
    if (!report.attempted) return;

    const target_name = rule.arg_names[report.target_arg_idx] orelse "_";
    const blocker_name = rule.arg_names[report.blocker_arg_idx] orelse "_";
    try addFormattedProofNote(
        allocator,
        diag,
        "attempted @freshen for target binder {s}",
        .{target_name},
    );
    try addFormattedProofNote(
        allocator,
        diag,
        "freshen blocker binder: {s}",
        .{blocker_name},
    );
    if (report.replacement_name) |replacement_name| {
        try addFormattedProofNote(
            allocator,
            diag,
            "chosen replacement binder: {s}",
            .{replacement_name},
        );
    }
    if (report.blocker_dependency_remaining) |remaining| {
        if (remaining) {
            try addFormattedProofNote(
                allocator,
                diag,
                "rewritten target still depends on blocker binder {s}",
                .{blocker_name},
            );
        } else {
            try addFormattedProofNote(
                allocator,
                diag,
                "rewritten target no longer depends on blocker binder {s}",
                .{blocker_name},
            );
        }
    }
}

pub fn addBoundaryAttemptNotes(
    allocator: std.mem.Allocator,
    diag: *Diagnostic,
    theorem: *const TheoremContext,
    env: *const GlobalEnv,
    parser: *const MM0Parser,
    theorem_vars: *const std.StringHashMap(*const Expr),
    theorem_concl: ExprId,
    final_line: ExprId,
    report: TheoremBoundary.ReconciliationReport,
) void {
    var names: ?ViewTrace.DiagNames = ViewTrace.DiagNames.build(
        allocator,
        theorem,
        parser,
        theorem_vars,
    ) catch null;
    defer if (names) |*n| n.deinit(allocator);
    const names_ptr: ?*const ViewTrace.DiagNames =
        if (names) |*n| n else null;
    addRenderedExprNote(
        allocator,
        diag,
        "the theorem concludes: {s}",
        theorem,
        env,
        names_ptr,
        theorem_concl,
    );
    addRenderedExprNote(
        allocator,
        diag,
        "the last line proves: {s}",
        theorem,
        env,
        names_ptr,
        final_line,
    );
    if (report.attempted_transparent) {
        addStaticProofNote(
            diag,
            "the two do not match, even with definitions unfolded",
        );
    }
    if (report.attempted_normalized) {
        addStaticProofNote(diag, "nor after normalization");
    }
}

fn addRenderedExprNote(
    allocator: std.mem.Allocator,
    diag: *Diagnostic,
    comptime fmt: []const u8,
    theorem: *const TheoremContext,
    env: *const GlobalEnv,
    names_ptr: ?*const ViewTrace.DiagNames,
    expr_id: ExprId,
) void {
    const text = formatNoteExpr(
        allocator,
        theorem,
        env,
        names_ptr,
        expr_id,
    ) catch return;
    defer allocator.free(text);
    addFormattedProofNote(
        allocator,
        diag,
        fmt,
        .{truncateSnapshot(text)},
    ) catch return;
}

fn addStaticProofNote(diag: *Diagnostic, message: []const u8) void {
    addStaticProofNoteSpan(diag, message, null);
}

fn addStaticProofNoteSpan(
    diag: *Diagnostic,
    message: []const u8,
    span: ?Span,
) void {
    CompilerDiag.addNote(diag, message, .proof, span);
}

fn addFormattedProofNote(
    allocator: std.mem.Allocator,
    diag: *Diagnostic,
    comptime fmt: []const u8,
    args: anytype,
) !void {
    try addFormattedProofNoteSpan(allocator, diag, fmt, args, null);
}

fn addFormattedProofNoteSpan(
    allocator: std.mem.Allocator,
    diag: *Diagnostic,
    comptime fmt: []const u8,
    args: anytype,
    span: ?Span,
) !void {
    const message = try std.fmt.allocPrint(allocator, fmt, args);
    CompilerDiag.addNote(diag, message, .proof, span);
}
