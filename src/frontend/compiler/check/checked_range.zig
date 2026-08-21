//! Checked-IR range ownership validation: guards against
//! attempt-scoped ExprIds and bindings leaking into committed checked lines.

const std = @import("std");
const ExprId = @import("../../expr.zig").ExprId;
const TheoremContext = @import("../../expr.zig").TheoremContext;
const GlobalEnv = @import("../../env.zig").GlobalEnv;
const RuleDecl = @import("../../env.zig").RuleDecl;
const AssertionStmt = @import("../../parse_recovery.zig").AssertionStmt;
const MM0Parser = @import("../../parse_recovery.zig").MM0Parser;
const ExprModule = @import("../../../trusted/expressions.zig");
const Expr = ExprModule.Expr;
const SourceSpan = ExprModule.SourceSpan;
const ProofScript = @import("../../proof_script.zig");
const ProofLine = ProofScript.ProofLine;
const Ref = ProofScript.Ref;
const RuleApplication = ProofScript.RuleApplication;
const Span = ProofScript.Span;
const TemplateExpr = @import("../../rules.zig").TemplateExpr;
const TheoremBlock = @import("../../proof_script.zig").TheoremBlock;
const RewriteRegistry = @import("../../rewrite_registry.zig").RewriteRegistry;
const CompilerViews = @import("../views.zig");
const FreshSelect = @import("../fresh_select.zig");
const AlphaRewrite = @import("../alpha_rewrite.zig");
const RuleCatalog = @import("../rule_catalog.zig");
const ViewDecl = CompilerViews.ViewDecl;
const FreshDecl = FreshSelect.FreshDecl;
const FreshenDecl = FreshSelect.FreshenDecl;
const CompilerDiag = @import("../../diag.zig");
const CompilerContext = @import("../context.zig").CompilerContext;
const HoleInferenceSink = @import("../context.zig").HoleInferenceSink;
const InlineConclusionSink = @import("../context.zig").InlineConclusionSink;
const DiagnosticSink = @import("../diagnostic_sink.zig").DiagnosticSink;
const Normalize = @import("../normalize.zig");
const ViewTrace = @import("../../view_trace.zig");
const Diagnostic = CompilerDiag.Diagnostic;
const CheckedIr = @import("../../checked_ir.zig");
const CheckedLine = CheckedIr.CheckedLine;
const CheckedRef = CheckedIr.CheckedRef;
const Inference = @import("../inference.zig");
const Matching = @import("./matching.zig");
const DiagNotes = @import("./diag_notes.zig");
const FreshenRetry = @import("./freshen_retry.zig");
const TheoremBoundary = @import("../theorem_boundary.zig");
const CompilerVars = @import("../vars.zig");
const SortVarRegistry = CompilerVars.SortVarRegistry;
const Holes = @import("../holes.zig");
const Idents = @import("../idents.zig");
const OpenTerms = @import("../inference/open_terms.zig");
const addFallbackFailureNote = DiagNotes.addFallbackFailureNote;
const concreteMatchFailureSpan = DiagNotes.concreteMatchFailureSpan;
const setHoleyInferenceDiagnostic = DiagNotes.setHoleyInferenceDiagnostic;
const addHoleConcreteMatchNotes = DiagNotes.addHoleConcreteMatchNotes;
const addComparisonSnapshotNotes = DiagNotes.addComparisonSnapshotNotes;
const addFreshenAttemptNotes = DiagNotes.addFreshenAttemptNotes;
const addBoundaryAttemptNotes = DiagNotes.addBoundaryAttemptNotes;
const applyFreshenedRuleLine = FreshenRetry.applyFreshenedRuleLine;
const findRuleArgIndex = Idents.findRuleArgIndex;

const NameExprMap = @import("./types.zig").NameExprMap;
const getDiagnostic = @import("./types.zig").getDiagnostic;
const restoreDiagnostic = @import("./types.zig").restoreDiagnostic;

pub fn checkedRangeOwnsRefs(
    lines: []const CheckedLine,
    refs: []const CheckedRef,
) bool {
    for (lines) |checked_line| {
        switch (checked_line.data) {
            .rule => |rule| {
                if (rule.refs.ptr == refs.ptr and
                    rule.refs.len == refs.len)
                {
                    return true;
                }
            },
            .transport => {},
        }
    }
    return false;
}

pub fn checkedRangeOwnsBindings(
    lines: []const CheckedLine,
    bindings: []const ExprId,
) bool {
    for (lines) |checked_line| {
        switch (checked_line.data) {
            .rule => |rule| {
                if (rule.bindings.ptr == bindings.ptr and
                    rule.bindings.len == bindings.len)
                {
                    return true;
                }
            },
            .transport => {},
        }
    }
    return false;
}

pub fn ensureConcreteCheckedIrRange(
    self: *CompilerContext,
    env: *const GlobalEnv,
    theorem: *TheoremContext,
    parser: ?*const MM0Parser,
    theorem_vars: ?*const NameExprMap,
    theorem_name: []const u8,
    lines: []const CheckedLine,
    line_label: ?[]const u8,
    span: ?Span,
    phase: CompilerDiag.DiagnosticPhase,
) !void {
    if (lines.len == 0) return;

    CheckedIr.validateLinesCached(theorem, lines) catch |err| {
        self.setProof(CompilerDiag.withPhase(.{
            .kind = .generic,
            .err = err,
            .theorem_name = theorem_name,
            .line_label = line_label,
            .span = span,
        }, phase));
        return err;
    };
    if (try CheckedIr.firstDepViolationCached(env, theorem, lines)) |failure| {
        var detail = failure.detail;
        var text_bufs: Inference.DepViolationTextBufs = .{};
        switch (lines[failure.line_idx].data) {
            .rule => |rule_line| Inference.attachDepViolationBindingTexts(
                &text_bufs,
                env,
                theorem,
                parser,
                theorem_vars,
                &detail,
                rule_line.bindings[detail.first_arg_idx],
                rule_line.bindings[detail.second_arg_idx],
            ),
            .transport => {},
        }
        self.setProof(CompilerDiag.withPhase(.{
            .kind = .generic,
            .err = error.DepViolation,
            .theorem_name = theorem_name,
            .line_label = line_label,
            .rule_name = if (failure.rule_id < env.rules.items.len)
                env.rules.items[failure.rule_id].name
            else
                null,
            .span = span,
            .detail = .{ .dep_violation = detail },
        }, phase));
        return error.DepViolation;
    }
}

// Preserve any new checked-IR validation diagnostic on failure, but restore
// the caller's saved diagnostic on success so speculative attempts remain
// diagnostically transparent.
pub fn validateAttemptCheckedIrRange(
    self: *CompilerContext,
    env: *const GlobalEnv,
    theorem: *TheoremContext,
    parser: ?*const MM0Parser,
    theorem_vars: ?*const NameExprMap,
    theorem_name: []const u8,
    lines: []const CheckedLine,
    line_label: ?[]const u8,
    span: ?Span,
    phase: CompilerDiag.DiagnosticPhase,
    saved_diag: ?Diagnostic,
) !void {
    try ensureConcreteCheckedIrRange(
        self,
        env,
        theorem,
        parser,
        theorem_vars,
        theorem_name,
        lines,
        line_label,
        span,
        phase,
    );
    restoreDiagnostic(self, saved_diag);
}

test "checked ir leak diagnostics replace saved diagnostics" {
    var theorem = TheoremContext.init(std.testing.allocator);
    defer theorem.deinit();
    try theorem.seedBinderCount(1);

    const placeholder = try theorem.addPlaceholderResolved("obj");
    const lines = [_]CheckedLine{.{
        .expr = placeholder,
        .data = .{ .rule = .{
            .rule_id = 0,
            .bindings = &.{theorem.theorem_vars.items[0]},
            .refs = &.{},
        } },
    }};

    var sink = DiagnosticSink.init("", null);
    var context = CompilerContext.init("", null, .none, &sink);
    context.setDiagnostic(CompilerDiag.withPhase(.{
        .kind = .generic,
        .err = error.UnknownRule,
        .theorem_name = "stale",
        .line_label = "old",
    }, .theorem_application));
    const saved_diag = getDiagnostic(&context);
    const span: Span = .{ .start = 3, .end = 11 };
    var env = GlobalEnv.init(std.testing.allocator);
    defer {
        env.sort_names.deinit();
        env.term_names.deinit();
        env.rule_names.deinit();
        env.terms.deinit(std.testing.allocator);
        env.rules.deinit(std.testing.allocator);
    }

    try std.testing.expectError(
        error.PlaceholderLeakage,
        validateAttemptCheckedIrRange(
            &context,
            &env,
            &theorem,
            null,
            null,
            "demo",
            &lines,
            "l2",
            span,
            .theorem_application,
            saved_diag,
        ),
    );

    const diag = sink.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.PlaceholderLeakage, diag.err);
    try std.testing.expectEqualStrings("demo", diag.theorem_name.?);
    try std.testing.expectEqualStrings("l2", diag.line_label.?);
    try std.testing.expectEqual(span.start, diag.span.?.start);
    try std.testing.expectEqual(span.end, diag.span.?.end);
    try std.testing.expectEqual(
        CompilerDiag.DiagnosticPhase.theorem_application,
        diag.phase.?,
    );
    try std.testing.expectEqual(.proof, diag.source);
}
