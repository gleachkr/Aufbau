//! Theorem-block checking facade. The driver (`checkTheoremBlock`) lives
//! here; the application core, binding inference, hint flow, and their
//! supporting types live in the `check/` submodules and are re-exported
//! where they form the public checking API.

const std = @import("std");
const ExprId = @import("../expr.zig").ExprId;
const TheoremContext = @import("../expr.zig").TheoremContext;
const GlobalEnv = @import("../env.zig").GlobalEnv;
const RuleDecl = @import("../env.zig").RuleDecl;
const AssertionStmt = @import("../parse_recovery.zig").AssertionStmt;
const MM0Parser = @import("../parse_recovery.zig").MM0Parser;
const ExprModule = @import("../../trusted/expressions.zig");
const Expr = ExprModule.Expr;
const SourceSpan = ExprModule.SourceSpan;
const ProofScript = @import("../proof_script.zig");
const ProofLine = ProofScript.ProofLine;
const Ref = ProofScript.Ref;
const RuleApplication = ProofScript.RuleApplication;
const Span = ProofScript.Span;
const TemplateExpr = @import("../rules.zig").TemplateExpr;
const TheoremBlock = @import("../proof_script.zig").TheoremBlock;
const RewriteRegistry = @import("../rewrite_registry.zig").RewriteRegistry;
const CompilerViews = @import("./views.zig");
const FreshSelect = @import("./fresh_select.zig");
const AlphaRewrite = @import("./alpha_rewrite.zig");
const RuleCatalog = @import("./rule_catalog.zig");
const ViewDecl = CompilerViews.ViewDecl;
const FreshDecl = FreshSelect.FreshDecl;
const FreshenDecl = FreshSelect.FreshenDecl;
const CompilerDiag = @import("../diag.zig");
const CompilerContext = @import("./context.zig").CompilerContext;
const HoleInferenceSink = @import("./context.zig").HoleInferenceSink;
const InlineConclusionSink = @import("./context.zig").InlineConclusionSink;
const DiagnosticSink = @import("./diagnostic_sink.zig").DiagnosticSink;
const Normalize = @import("./normalize.zig");
const ViewTrace = @import("../view_trace.zig");
const Diagnostic = CompilerDiag.Diagnostic;
const CheckedIr = @import("../checked_ir.zig");
const CheckedLine = CheckedIr.CheckedLine;
const CheckedRef = CheckedIr.CheckedRef;
const Inference = @import("./inference.zig");
const Matching = @import("./check/matching.zig");
const DiagNotes = @import("./check/diag_notes.zig");
const FreshenRetry = @import("./check/freshen_retry.zig");
const TheoremBoundary = @import("./theorem_boundary.zig");
const CompilerVars = @import("./vars.zig");
const SortVarRegistry = CompilerVars.SortVarRegistry;
const Holes = @import("./holes.zig");
const Idents = @import("./idents.zig");
const OpenTerms = @import("./inference/open_terms.zig");
const addFallbackFailureNote = DiagNotes.addFallbackFailureNote;
const concreteMatchFailureSpan = DiagNotes.concreteMatchFailureSpan;
const setHoleyInferenceDiagnostic = DiagNotes.setHoleyInferenceDiagnostic;
const addHoleConcreteMatchNotes = DiagNotes.addHoleConcreteMatchNotes;
const addComparisonSnapshotNotes = DiagNotes.addComparisonSnapshotNotes;
const addFreshenAttemptNotes = DiagNotes.addFreshenAttemptNotes;
const addBoundaryAttemptNotes = DiagNotes.addBoundaryAttemptNotes;
const applyFreshenedRuleLine = FreshenRetry.applyFreshenedRuleLine;
const findRuleArgIndex = Idents.findRuleArgIndex;

pub const NameExprMap = @import("./check/types.zig").NameExprMap;
pub const LabelIndexMap = @import("./check/types.zig").LabelIndexMap;
pub const SuccessfulLineAttempt = @import("./check/types.zig").SuccessfulLineAttempt;
pub const UnresolvedHypothesis = @import("./check/types.zig").UnresolvedHypothesis;
pub const ConclusionProbe = @import("./check/types.zig").ConclusionProbe;
pub const RefExpectationProbe = @import("./check/types.zig").RefExpectationProbe;
pub const LineAssertion = @import("./check/types.zig").LineAssertion;
pub const ApplicationDiagnosticContext = @import("./check/types.zig").ApplicationDiagnosticContext;
pub const ApplicationLine = @import("./check/types.zig").ApplicationLine;
pub const RuleApplyContext = @import("./check/types.zig").RuleApplyContext;
pub const applyRuleApplication = @import("./check/apply.zig").applyRuleApplication;
pub const probeRuleConclusion = @import("./check/apply.zig").probeRuleConclusion;
pub const probeExpectedRefsForApplication = @import("./check/apply.zig").probeExpectedRefsForApplication;
pub const buildTheoremVarMap = @import("./check/types.zig").buildTheoremVarMap;
pub const cloneNameExprMap = @import("./check/types.zig").cloneNameExprMap;

const ensureConcreteCheckedIrRange = @import("./check/checked_range.zig").ensureConcreteCheckedIrRange;
const findSearchPlaceholder = @import("./check/suggest.zig").findSearchPlaceholder;

pub fn checkTheoremBlock(
    self: *CompilerContext,
    allocator: std.mem.Allocator,
    parser: *MM0Parser,
    env: *const GlobalEnv,
    registry: *RewriteRegistry,
    rule_catalog: *const RuleCatalog.Catalog,
    fresh_bindings: *const std.AutoHashMap(u32, []const FreshDecl),
    freshen_bindings: *const std.AutoHashMap(u32, []const FreshenDecl),
    views: *const std.AutoHashMap(u32, ViewDecl),
    sort_vars: *const SortVarRegistry,
    assertion: AssertionStmt,
    block: TheoremBlock,
    theorem: *TheoremContext,
    theorem_concl: ExprId,
) ![]const CheckedLine {
    var theorem_vars = try buildTheoremVarMap(allocator, assertion);
    defer theorem_vars.deinit();

    var labels = LabelIndexMap.init(allocator);
    defer labels.deinit();

    var checked = std.ArrayListUnmanaged(CheckedLine){};
    var rule_unify_cache = Inference.RuleUnifyCache.init(allocator);
    defer rule_unify_cache.deinit();
    var diag_scratch = CompilerDiag.Scratch.init(allocator);
    defer diag_scratch.deinit();
    var last_line: ?ExprId = null;
    var last_line_idx: ?usize = null;
    var last_label: ?[]const u8 = null;
    var last_span: ?Span = null;

    for (block.lines) |line| {
        // A line the lenient parse could not finish. Only the analyze path
        // parses leniently, so this mirrors the placeholder gate below:
        // report the recorded parse failure and keep the lines checked so
        // far, exactly as if the block ended here. The line contributes
        // nothing to the label environment and can never reach emission —
        // the compile path parses strictly and errors out instead.
        if (line.incomplete) {
            const diag = CompilerDiag.incompleteProofLineDiagnostic(
                assertion.name,
                line,
            );
            if (self.allow_search_placeholders) {
                self.addPrimaryDiagnostic(diag);
                return try checked.toOwnedSlice(allocator);
            }
            self.setProof(diag);
            return diag.err;
        }

        if (ProofScript.applicationHasSearchPlaceholder(line.application)) {
            if (self.allow_search_placeholders) {
                return try checked.toOwnedSlice(allocator);
            }
            const placeholder =
                findSearchPlaceholder(line.application) orelse line.application;
            var diag = CompilerDiag.withPhase(.{
                .kind = .unresolved_search_placeholder,
                .err = error.UnknownRule,
                .theorem_name = assertion.name,
                .line_label = line.label,
                .rule_name = placeholder.rule_name,
                .span = placeholder.rule_span,
            }, .theorem_application);
            CompilerDiag.addNote(&diag, .search_placeholder_meaning, .proof, null);
            CompilerDiag.addNote(
                &diag,
                .search_placeholder_unfinished,
                .proof,
                null,
            );
            self.setProof(diag);
            return error.UnknownRule;
        }

        if (labels.contains(line.label)) {
            self.setProof(CompilerDiag.withPhase(.{
                .kind = .duplicate_label,
                .err = error.DuplicateLabel,
                .theorem_name = assertion.name,
                .line_label = line.label,
                .name = line.label,
                .span = line.label_span,
            }, .theorem_application));
            return error.DuplicateLabel;
        }

        const parsed_assertion = try parseProofLineAssertion(
            self,
            parser,
            theorem,
            &theorem_vars,
            sort_vars,
            assertion,
            line,
        );
        const line_assertion = LineAssertion.fromParsed(parsed_assertion);

        const apply_context: RuleApplyContext = .{
            .allocator = allocator,
            .parser = parser,
            .env = env,
            .registry = registry,
            .rule_catalog = rule_catalog,
            .fresh_bindings = fresh_bindings,
            .freshen_bindings = freshen_bindings,
            .views = views,
            .sort_vars = sort_vars,
            .assertion = assertion,
            .labels = &labels,
            .block_lines = block.lines,
            .checked = &checked,
            .diag_scratch = &diag_scratch,
            .rule_unify_cache = &rule_unify_cache,
        };
        const attempt = try applyRuleApplication(
            self,
            &apply_context,
            line.application,
            line_assertion,
            null,
            ApplicationDiagnosticContext.fromLine(assertion, line),
            ApplicationLine.fromLine(line),
            theorem,
            &theorem_vars,
        );

        if (parsed_assertion == .holey) {
            try collectHoleInferences(
                self,
                allocator,
                parser,
                theorem,
                env,
                &theorem_vars,
                line,
                parsed_assertion.holey,
                checked.items[attempt.line_idx].expr,
            );
        }

        try labels.put(line.label, attempt.line_idx);
        last_line = checked.items[attempt.line_idx].expr;
        last_line_idx = attempt.line_idx;
        last_label = line.label;
        last_span = line.span;
    }

    const final_line = last_line orelse {
        self.setProof(CompilerDiag.withPhase(.{
            .kind = .empty_proof_block,
            .err = error.EmptyProofBlock,
            .theorem_name = assertion.name,
            .block_name = block.name,
            .span = block.name_span,
        }, .final_reconciliation));
        return error.EmptyProofBlock;
    };
    if (final_line != theorem_concl) {
        if (last_line_idx) |line_idx| {
            const final_mark = diag_scratch.mark();
            const checked_mark = checked.items.len;
            var final_report: TheoremBoundary.ReconciliationReport = .{};
            if ((TheoremBoundary.tryReconcileFinalConclusion(
                allocator,
                theorem,
                registry,
                env,
                &checked,
                &diag_scratch,
                theorem_concl,
                final_line,
                line_idx,
                self.debug,
                &final_report,
            ) catch |err| {
                if (CompilerDiag.takeScratchDetail(
                    &diag_scratch,
                    final_mark,
                    env,
                    err,
                )) |detail| {
                    var diag = CompilerDiag.withPhase(.{
                        .kind = .generic,
                        .err = CompilerDiag.narrowDiagnosticError(err),
                        .theorem_name = assertion.name,
                        .line_label = last_label,
                        .span = last_span,
                        .detail = detail,
                    }, .final_reconciliation);
                    addBoundaryAttemptNotes(
                        allocator,
                        &diag,
                        theorem,
                        env,
                        parser,
                        &theorem_vars,
                        theorem_concl,
                        final_line,
                        final_report,
                    );
                    self.setProof(diag);
                    return err;
                }
                diag_scratch.discard(final_mark);
                return err;
            })) {
                diag_scratch.discard(final_mark);
                try ensureConcreteCheckedIrRange(
                    self,
                    env,
                    theorem,
                    parser,
                    &theorem_vars,
                    assertion.name,
                    checked.items[checked_mark..],
                    last_label,
                    last_span,
                    .final_reconciliation,
                );
                return try checked.toOwnedSlice(allocator);
            }
            diag_scratch.discard(final_mark);
            var diag = CompilerDiag.withPhase(.{
                .kind = .final_line_mismatch,
                .err = error.FinalLineMismatch,
                .theorem_name = assertion.name,
                .line_label = last_label,
                .span = last_span,
            }, .final_reconciliation);
            addBoundaryAttemptNotes(
                allocator,
                &diag,
                theorem,
                env,
                parser,
                &theorem_vars,
                theorem_concl,
                final_line,
                final_report,
            );
            self.setProof(diag);
            return error.FinalLineMismatch;
        }
        self.setProof(CompilerDiag.withPhase(.{
            .kind = .final_line_mismatch,
            .err = error.FinalLineMismatch,
            .theorem_name = assertion.name,
            .line_label = last_label,
            .span = last_span,
        }, .final_reconciliation));
        return error.FinalLineMismatch;
    }
    return try checked.toOwnedSlice(allocator);
}

fn collectHoleInferences(
    self: *CompilerContext,
    allocator: std.mem.Allocator,
    parser: *MM0Parser,
    theorem: *const TheoremContext,
    env: *const GlobalEnv,
    theorem_vars: *const NameExprMap,
    line: ProofLine,
    surface: *const Expr,
    concrete: ExprId,
) !void {
    const sink = self.hole_inference_sink orelse return;
    var names = try ViewTrace.DiagNames.build(
        allocator,
        theorem,
        parser,
        theorem_vars,
    );
    defer names.deinit(allocator);
    try collectHoleInferencesRecursive(
        sink,
        theorem,
        env,
        &names,
        line.assertion.span.start + 1,
        surface,
        concrete,
    );
}

fn collectHoleInferencesRecursive(
    sink: *HoleInferenceSink,
    theorem: *const TheoremContext,
    env: *const GlobalEnv,
    names: *const ViewTrace.DiagNames,
    math_start: usize,
    surface: *const Expr,
    concrete: ExprId,
) !void {
    switch (surface.*) {
        .hole => |hole| {
            const token_span = hole.token_span orelse return;
            const expression = try ViewTrace.formatExprNamed(
                sink.allocator,
                theorem,
                env,
                names,
                concrete,
            );
            try sink.addOwned(
                .{
                    .start = math_start + token_span.start,
                    .end = math_start + token_span.end,
                },
                expression,
            );
        },
        .variable => {},
        .term => |surface_app| {
            const concrete_app = switch (theorem.interner.node(concrete).*) {
                .app => |app| app,
                else => return,
            };
            if (surface_app.id != concrete_app.term_id or
                surface_app.args.len != concrete_app.args.len)
            {
                return;
            }
            for (surface_app.args, concrete_app.args) |
                surface_arg,
                concrete_arg,
            | {
                if (!Holes.contains(surface_arg)) continue;
                try collectHoleInferencesRecursive(
                    sink,
                    theorem,
                    env,
                    names,
                    math_start,
                    surface_arg,
                    concrete_arg,
                );
            }
        },
    }
}

fn parseProofLineAssertion(
    self: *CompilerContext,
    parser: *MM0Parser,
    theorem: *TheoremContext,
    theorem_vars: *NameExprMap,
    sort_vars: *const SortVarRegistry,
    assertion: AssertionStmt,
    line: ProofLine,
) !Holes.ParsedAssertion {
    return Holes.parseAssertion(
        parser,
        theorem,
        theorem_vars,
        sort_vars,
        line.assertion.text,
    ) catch |err| {
        var diag = CompilerDiag.proofMathParseDiagnostic(
            parser,
            .parse_assertion,
            err,
            assertion.name,
            line.label,
            line.application.rule_name,
            null,
            line.assertion.span,
        );
        DiagNotes.attachSortRetryNote(
            &diag,
            parser,
            theorem_vars,
            null,
            line.assertion.text,
        );
        self.setProof(diag);
        return err;
    };
}
