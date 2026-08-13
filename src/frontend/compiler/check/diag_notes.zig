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
const NoteMessage = CompilerDiag.NoteMessage;
const HiddenWitnessFreshContext =
    @import("../inference/context.zig").HiddenWitnessFreshContext;
const MM0Parser = @import("../../parse_recovery.zig").MM0Parser;

const SurfaceExpr = @import("../../surface_expr.zig");
const ArgInfo = @import("../../parse_recovery.zig").ArgInfo;

/// A math string that failed sort-directed coercion (rather than parsing)
/// gets a note naming the sort it actually has: re-parse it with no target
/// sort and report the root sort of the result. When even the sort-agnostic
/// parse fails, the mismatch sits inside the expression (a term argument of
/// the wrong sort) and the note says so instead — the trusted parser records
/// no position for argument coercions, so no tighter span is available.
/// `expected` carries the binder's ArgInfo, or null when the target is the
/// provable-sort slot (line assertions). Sort names are parser/env-owned,
/// so the note payload outlives setProof without a caller buffer.
pub fn attachSortRetryNote(
    diag: *Diagnostic,
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
            error.SortMismatch => addProofNote(
                diag,
                .subexpression_sort_mismatch,
            ),
            error.BoundnessMismatch => addProofNote(
                diag,
                .subexpression_needs_bound_var,
            ),
            else => {},
        }
        return;
    };
    const actual = SurfaceExpr.parserSortName(parser, expr.sort());
    const message: NoteMessage = switch (diag.err) {
        error.SortMismatch => blk: {
            const arg = expected orelse return;
            break :blk .{ .assignment_parses_as_sort = .{
                .actual_sort = actual,
                .expected_sort = arg.sort_name,
            } };
        },
        error.NotProvable => .{ .statement_not_provable_sort = .{
            .actual_sort = actual,
        } },
        error.BoundnessMismatch => .right_sort_but_needs_bound_var,
        else => unreachable,
    };
    addProofNote(diag, message);
}

pub fn addFallbackFailureNote(
    diag: *Diagnostic,
    line_assertion: anytype,
    line: anytype,
) void {
    switch (line_assertion) {
        .concrete, .implicit_whole_conclusion => {},
        .holey => |holey| {
            addProofNoteSpan(
                diag,
                .holey_fallback_exhausted,
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
        .err = CompilerDiag.narrowDiagnosticError(err),
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

    var names = ViewTrace.OptionalDiagNames.build(
        allocator,
        theorem,
        if (fresh_context) |fresh| fresh.parser else null,
        if (fresh_context) |fresh| fresh.theorem_vars else null,
    );
    defer names.deinit(allocator);
    const names_ptr = names.ptr();

    switch (failure) {
        .hypothesis_mismatch => |info| {
            addProofNote(diag, .{ .premise_hypothesis_mismatch = .{
                .number = info.index + 1,
            } });
            const ref_text = try formatNoteExpr(
                allocator,
                theorem,
                env,
                names_ptr,
                info.ref_expr,
            );
            addProofNote(diag, .{ .cited_premise_proves = .{
                .text = truncateSnapshot(ref_text),
            } });
        },
        .visible_structure_mismatch => |detail| {
            addProofNoteSpan(diag, .visible_structure_mismatch, hole_span);
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
            addProofNoteSpan(diag, .{ .holey_unsolved_binder = .{
                .binder_name = name,
            } }, hole_span);
            if (info.index < rule.arg_names.len and rule.arg_names[info.index] == null) {
                addProofNote(diag, .{ .unsolved_binder_index = .{
                    .number = info.index + 1,
                } });
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
                addProofNote(diag, .{ .conclusion_head_clash = .{
                    .expected_term = expected_name,
                    .actual_term = termNameById(env, actual_id),
                } });
            } else {
                addProofNote(diag, .{
                    .conclusion_head_clash_with_variable = .{
                        .expected_term = expected_name,
                    },
                });
            }
        },
        .binder_conflict => |conflict| {
            const binder_name: ?[]const u8 =
                if (conflict.binder_idx < rule.arg_names.len)
                    rule.arg_names[conflict.binder_idx]
                else
                    null;
            if (binder_name) |name| {
                addProofNote(diag, .{ .rule_var_two_values = .{
                    .binder_name = name,
                } });
            } else {
                addProofNote(diag, .unnamed_rule_var_two_values);
            }
            const existing_text = try formatNoteExpr(
                allocator,
                theorem,
                env,
                names_ptr,
                conflict.existing,
            );
            addProofNote(diag, .{ .already_matched = .{
                .text = truncateSnapshot(existing_text),
            } });
            const actual_text = try formatNoteExpr(
                allocator,
                theorem,
                env,
                names_ptr,
                conflict.actual,
            );
            addProofNote(diag, .{ .in_the_statement = .{
                .text = truncateSnapshot(actual_text),
            } });
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
    diag: *Diagnostic,
    line: anytype,
    report: Holes.ConcreteMatchReport,
) void {
    const failure = report.failure orelse return;
    switch (failure) {
        .visible_structure_mismatch => addProofNote(
            diag,
            .visible_structure_mismatch,
        ),
        .hole_sort_mismatch => |mismatch| {
            addProofNoteSpan(diag, .{ .hole_sort_mismatch = .{
                .token = mismatch.token,
                .expected_sort = mismatch.expected_sort_name,
                .actual_sort = mismatch.actual_sort_name,
            } }, proofSpanForSourceSpan(line, mismatch.token_span));
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
    addProofNote(diag, .{ .expected_expr = .{
        .text = truncateSnapshot(expected_text),
    } });

    const actual_text = try ViewTrace.formatExprNamed(
        allocator,
        theorem,
        env,
        &names,
        actual,
    );
    addProofNote(diag, .{ .actual_expr = .{
        .text = truncateSnapshot(actual_text),
    } });

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

    addProofNote(diag, .attempted_normalized_comparison);
    if (snapshot.normalized_expected) |normalized_expected| {
        const normalized_expected_text = try ViewTrace.formatExprNamed(
            allocator,
            theorem,
            env,
            &names,
            normalized_expected,
        );
        addProofNote(diag, .{ .normalized_expected_expr = .{
            .text = truncateSnapshot(normalized_expected_text),
        } });
    }
    if (snapshot.normalized_actual) |normalized_actual| {
        const normalized_actual_text = try ViewTrace.formatExprNamed(
            allocator,
            theorem,
            env,
            &names,
            normalized_actual,
        );
        addProofNote(diag, .{ .normalized_actual_expr = .{
            .text = truncateSnapshot(normalized_actual_text),
        } });
    }
}

fn truncateSnapshot(text: []const u8) []const u8 {
    return text_util.truncateUtf8(text, 64);
}

pub fn addFreshenAttemptNotes(
    diag: *Diagnostic,
    rule: *const RuleDecl,
    report: AlphaRewrite.FreshenAttemptReport,
) void {
    if (!report.attempted) return;

    const target_name = rule.arg_names[report.target_arg_idx] orelse "_";
    const blocker_name = rule.arg_names[report.blocker_arg_idx] orelse "_";
    addProofNote(diag, .{ .freshen_attempted_for_target = .{
        .binder_name = target_name,
    } });
    addProofNote(diag, .{ .freshen_blocker = .{
        .binder_name = blocker_name,
    } });
    if (report.replacement_name) |replacement_name| {
        addProofNote(diag, .{ .freshen_replacement = .{
            .binder_name = replacement_name,
        } });
    }
    if (report.blocker_dependency_remaining) |remaining| {
        if (remaining) {
            addProofNote(diag, .{ .freshen_still_depends_on_blocker = .{
                .binder_name = blocker_name,
            } });
        } else {
            addProofNote(diag, .{
                .freshen_no_longer_depends_on_blocker = .{
                    .binder_name = blocker_name,
                },
            });
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
    var names = ViewTrace.OptionalDiagNames.build(
        allocator,
        theorem,
        parser,
        theorem_vars,
    );
    defer names.deinit(allocator);
    const names_ptr = names.ptr();
    addRenderedExprNote(
        allocator,
        diag,
        .theorem_concludes,
        theorem,
        env,
        names_ptr,
        theorem_concl,
    );
    addRenderedExprNote(
        allocator,
        diag,
        .last_line_proves,
        theorem,
        env,
        names_ptr,
        final_line,
    );
    if (report.attempted_transparent) {
        addProofNote(diag, .boundary_mismatch_despite_unfolding);
    }
    if (report.attempted_normalized) {
        addProofNote(diag, .boundary_mismatch_despite_normalization);
    }
}

fn addRenderedExprNote(
    allocator: std.mem.Allocator,
    diag: *Diagnostic,
    comptime tag: std.meta.Tag(NoteMessage),
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
    addProofNote(diag, @unionInit(NoteMessage, @tagName(tag), .{
        .text = truncateSnapshot(text),
    }));
}

fn addProofNote(diag: *Diagnostic, message: NoteMessage) void {
    addProofNoteSpan(diag, message, null);
}

fn addProofNoteSpan(
    diag: *Diagnostic,
    message: NoteMessage,
    span: ?Span,
) void {
    CompilerDiag.addNote(diag, message, .proof, span);
}
