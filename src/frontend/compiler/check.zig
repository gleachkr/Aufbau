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
const CompilerViews = @import("../views.zig");
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
const Idents = @import("../idents.zig");
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
pub const UnresolvedHypothesis = @import("./check/types.zig").UnresolvedHypothesis;
pub const ConclusionProbe = @import("./check/types.zig").ConclusionProbe;
pub const RefExpectationProbe = @import("./check/types.zig").RefExpectationProbe;
pub const LineAssertion = @import("./check/types.zig").LineAssertion;
pub const HoleyLine = Holes.HoleyLine;
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

/// `checkTheoremBlock` behind the context's check memo, when one is
/// attached (`CompilerContext.check_memo`): a hit replays the recorded
/// outcome and output instead of checking again. A hit yields no checked
/// lines, so paths that emit (the compile path) must call
/// `checkTheoremBlock` directly.
pub fn checkTheoremBlockMemoized(
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
    const memo = self.check_memo orelse return checkTheoremBlock(
        self,
        allocator,
        parser,
        env,
        registry,
        rule_catalog,
        fresh_bindings,
        freshen_bindings,
        views,
        sort_vars,
        assertion,
        block,
        theorem,
        theorem_concl,
    );
    if (!memo.active) {
        return checkTheoremBlock(
            self,
            allocator,
            parser,
            env,
            registry,
            rule_catalog,
            fresh_bindings,
            freshen_bindings,
            views,
            sort_vars,
            assertion,
            block,
            theorem,
            theorem_concl,
        );
    }
    const mm0_pos = parser.core.pos;
    const key = memo.keyForBlock(self.source, mm0_pos, self.proof_source.?, block);
    if (memo.find(key, rule_catalog)) |entry| {
        try entry.replay(self, block.span.start);
        if (entry.outcome) |err| return err;
        return &.{};
    }
    const recording = memo.beginRecording(self);
    const checked = checkTheoremBlock(
        self,
        allocator,
        parser,
        env,
        registry,
        rule_catalog,
        fresh_bindings,
        freshen_bindings,
        views,
        sort_vars,
        assertion,
        block,
        theorem,
        theorem_concl,
    ) catch |err| {
        memo.finishRecording(self, recording, key, err, block.span);
        return err;
    };
    memo.finishRecording(self, recording, key, null, block.span);
    return checked;
}

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
        const line_assertion = try LineAssertion.fromParsed(
            theorem,
            env,
            parsed_assertion,
        );

        if (ProofScript.isSorryRuleName(line.application.rule_name)) {
            const line_idx = try admitSorryLine(
                self,
                allocator,
                &checked,
                assertion,
                line,
                parsed_assertion,
            );
            try labels.put(line.label, line_idx);
            last_line = checked.items[line_idx].expr;
            last_line_idx = line_idx;
            last_label = line.label;
            last_span = line.span;
            continue;
        }

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
        const checked_mark = checked.items.len;
        const line_idx = try applyRuleApplication(
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
                &apply_context,
                checked_mark,
                theorem,
                &theorem_vars,
                line,
                parsed_assertion.holey,
                checked.items[line_idx].expr,
            );
        }

        try labels.put(line.label, line_idx);
        last_line = checked.items[line_idx].expr;
        last_line_idx = line_idx;
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
    apply_context: *const RuleApplyContext,
    checked_mark: usize,
    theorem: *TheoremContext,
    theorem_vars: *const NameExprMap,
    line: ProofLine,
    surface: *const Expr,
    checked_line: ExprId,
) !void {
    const sink = self.hole_inference_sink orelse return;
    const allocator = apply_context.allocator;
    const parser = apply_context.parser;
    const env = apply_context.env;
    // Report the line as written with its holes filled. The checked line can
    // differ in shape: it unfolds a definition the line keeps folded
    // (`_wff -> c e. img f B` checks as `... sep x B (R f x)`). Keep the
    // checked line when the filled one is not the same up to unfolding.
    const fill = Holes.fillThroughDefs(
        parser,
        theorem,
        env,
        surface,
        checked_line,
    ) catch |err| switch (err) {
        error.OutOfMemory => return err,
        // Editor-only display: a failed fill must not fail the check.
        else => null,
    };
    const concrete = fill orelse checked_line;
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
    const filled = try ViewTrace.formatExprSource(
        sink.allocator,
        theorem,
        env,
        &names,
        concrete,
    ) orelse return;
    // Offer the filled line only if it checks as written: a holey line can
    // check where its filled form does not (a rewrite the concrete path
    // needs a congruence for, or a print that does not parse back).
    const checks = filledLineChecks(
        self,
        apply_context,
        checked_mark,
        theorem,
        theorem_vars,
        line,
        filled,
    ) catch |err| {
        sink.allocator.free(filled);
        return err;
    };
    if (!checks) {
        sink.allocator.free(filled);
        return;
    }
    try sink.addAssertionOwned(line.span, line.assertion.span, filled);
}

/// Whether `line` checks with the assertion `text` against the lines checked
/// before it (`apply_context.checked` up to `checked_mark`). Runs on clones
/// and leaves the diagnostics and sinks as they were.
fn filledLineChecks(
    self: *CompilerContext,
    apply_context: *const RuleApplyContext,
    checked_mark: usize,
    theorem: *const TheoremContext,
    theorem_vars: *const NameExprMap,
    line: ProofLine,
    text: []const u8,
) !bool {
    const allocator = apply_context.allocator;
    var probe_theorem = try theorem.clone();
    defer probe_theorem.deinit();
    var probe_vars = try cloneNameExprMap(allocator, theorem_vars);
    defer probe_vars.deinit();

    const saved_diag = self.getDiagnostic();
    defer self.restoreDiagnostic(saved_diag);
    const diag_mark = apply_context.diag_scratch.mark();
    defer apply_context.diag_scratch.discard(diag_mark);
    const inline_mark = if (self.inline_conclusion_sink) |sink| sink.mark() else 0;
    defer if (self.inline_conclusion_sink) |sink| sink.rollback(inline_mark);

    const parsed = Holes.parseAssertion(
        apply_context.parser,
        &probe_theorem,
        &probe_vars,
        apply_context.sort_vars,
        text,
    ) catch |err| switch (err) {
        error.OutOfMemory => return err,
        else => return false,
    };
    if (parsed == .holey) return false;

    var scratch: std.ArrayListUnmanaged(CheckedLine) = .{};
    defer {
        CheckedIr.rollbackToMark(allocator, &scratch, checked_mark);
        scratch.deinit(allocator);
    }
    try scratch.appendSlice(allocator, apply_context.checked.items[0..checked_mark]);
    var probe_context = apply_context.*;
    probe_context.checked = &scratch;
    _ = applyRuleApplication(
        self,
        &probe_context,
        line.application,
        .{ .concrete = parsed.concrete },
        null,
        ApplicationDiagnosticContext.fromLine(apply_context.assertion, line),
        ApplicationLine.fromLine(line),
        &probe_theorem,
        &probe_vars,
    ) catch |err| switch (err) {
        error.OutOfMemory => return err,
        else => return false,
    };
    CheckedIr.validateLinesCached(&probe_theorem, scratch.items[checked_mark..]) catch
        return false;
    return true;
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

/// `by sorry!`: admit the stated goal with no rule. The line joins the
/// checked IR as a `.sorry` line, so later references and the final
/// conclusion check see it like any other, and a warning marks the theorem
/// as not verified. The goal must be concrete and the application bare: a
/// sorry has nothing to infer a hole from and no hypotheses to discharge.
fn admitSorryLine(
    self: *CompilerContext,
    allocator: std.mem.Allocator,
    checked: *std.ArrayListUnmanaged(CheckedLine),
    assertion: AssertionStmt,
    line: ProofLine,
    parsed_assertion: Holes.ParsedAssertion,
) !usize {
    const app = line.application;
    const goal: ?ExprId = switch (parsed_assertion) {
        .concrete => |expr_id| expr_id,
        .holey => null,
    };
    if (goal == null or app.arg_bindings.len != 0 or
        app.search_params.len != 0 or app.refs.len != 0)
    {
        self.setProof(CompilerDiag.withPhase(.{
            .kind = .sorry_line_arguments,
            .err = error.SorryLineArguments,
            .theorem_name = assertion.name,
            .line_label = line.label,
            .rule_name = app.rule_name,
            .span = if (goal == null) line.assertion.span else app.span,
        }, .theorem_application));
        return error.SorryLineArguments;
    }
    const line_idx = try CheckedIr.appendSorryLine(checked, allocator, goal.?);
    self.addWarning(.{
        .kind = .sorry_line,
        .err = error.SorryLine,
        .source = .proof,
        .theorem_name = assertion.name,
        .line_label = line.label,
        .rule_name = app.rule_name,
        .span = app.rule_span,
    });
    return line_idx;
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
