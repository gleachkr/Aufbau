//! Ref elaboration: resolve a line's refs (labels, inline
//! applications, hypothesis names) into checked refs.

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
const CompilerViews = @import("../../views.zig");
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
const Idents = @import("../../idents.zig");
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
const SuccessfulLineAttempt = @import("./types.zig").SuccessfulLineAttempt;
const UnresolvedHypothesis = @import("./types.zig").UnresolvedHypothesis;
const ConclusionProbe = @import("./types.zig").ConclusionProbe;
const RefExpectationProbe = @import("./types.zig").RefExpectationProbe;
const LineAssertion = @import("./types.zig").LineAssertion;
const ApplicationDiagnosticContext = @import("./types.zig").ApplicationDiagnosticContext;
const ApplicationLine = @import("./types.zig").ApplicationLine;
const RuleApplyContext = @import("./types.zig").RuleApplyContext;
const checkedRangeOwnsRefs = @import("./checked_range.zig").checkedRangeOwnsRefs;
const checkedRangeOwnsBindings = @import("./checked_range.zig").checkedRangeOwnsBindings;
const resolveLineAssertionForBindings = @import("./bindings.zig").resolveLineAssertionForBindings;
const inferCandidateOptionalBindings = @import("./bindings.zig").inferCandidateOptionalBindings;
const validateOptionalBindingsForProbe = @import("./bindings.zig").validateOptionalBindingsForProbe;
const inferCandidateBindings = @import("./bindings.zig").inferCandidateBindings;
const elaborateCandidateLine = @import("./bindings.zig").elaborateCandidateLine;
const validateAttemptCheckedIrRange = @import("./checked_range.zig").validateAttemptCheckedIrRange;
const closestKeyName = @import("./suggest.zig").closestKeyName;
const labelAppearsInBlock = @import("./suggest.zig").labelAppearsInBlock;
const lookupRuleApplicationId = @import("./suggest.zig").lookupRuleApplicationId;
const inferExpectedRefsForInlineApplications = @import("./inline_hints.zig").inferExpectedRefsForInlineApplications;
const foldTemplateOrRestore = @import("./inline_hints.zig").foldTemplateOrRestore;
const inferExpectedRefsForInlineApplicationProbe = @import("./inline_hints.zig").inferExpectedRefsForInlineApplicationProbe;
const fillHoleyInlineHints = @import("./inline_hints.zig").fillHoleyInlineHints;
const demoteAcuiSpineBindingsForRule = @import("./inline_hints.zig").demoteAcuiSpineBindingsForRule;
const cloneNameExprMap = @import("./types.zig").cloneNameExprMap;
const getDiagnostic = @import("./types.zig").getDiagnostic;
const restoreDiagnostic = @import("./types.zig").restoreDiagnostic;
const parseBindings = @import("./bindings.zig").parseBindings;
const lineAssertionKnownDeps = @import("./bindings.zig").lineAssertionKnownDeps;
const validateFreshBindingsAgainstLine = @import("./bindings.zig").validateFreshBindingsAgainstLine;
const applyFreshBindings = @import("./bindings.zig").applyFreshBindings;

pub fn applyRuleApplication(
    self: *CompilerContext,
    context: *const RuleApplyContext,
    application: RuleApplication,
    line_assertion: LineAssertion,
    expected_conclusion_hint: ?ExprId,
    diag_context: ApplicationDiagnosticContext,
    line: ApplicationLine,
    theorem: *TheoremContext,
    theorem_vars: *NameExprMap,
) anyerror!SuccessfulLineAttempt {
    const allocator = context.allocator;
    const initial_rule_id = try lookupRuleApplicationId(
        self,
        context.env,
        context.rule_catalog,
        context.labels,
        diag_context,
        application,
    );
    const saved_diag = getDiagnostic(self);

    var first_diag: ?Diagnostic = null;
    var first_err: ?anyerror = null;
    var seen_candidates = std.AutoHashMap(u32, void).init(allocator);
    defer seen_candidates.deinit();
    var candidate_rule_id = initial_rule_id;

    while (true) {
        const seen = try seen_candidates.getOrPut(candidate_rule_id);
        if (seen.found_existing) {
            self.setProof(CompilerDiag.withPhase(.{
                .kind = .generic,
                .err = error.FallbackCycle,
                .theorem_name = diag_context.theorem_name,
                .line_label = diag_context.line_label,
                .rule_name = application.rule_name,
                .span = application.rule_span,
            }, .theorem_application));
            return error.FallbackCycle;
        }

        const next_fallback = context.registry.getFallbackRule(
            candidate_rule_id,
        );
        const speculative = first_err != null or next_fallback != null;
        restoreDiagnostic(self, if (speculative) null else saved_diag);
        const checked_mark = context.checked.items.len;

        if (speculative) {
            var attempt_theorem = try theorem.clone();
            var attempt_theorem_vars = cloneNameExprMap(
                allocator,
                theorem_vars,
            ) catch |err| {
                attempt_theorem.deinit();
                return err;
            };

            var attempt = tryApplyRuleApplicationWithCandidate(
                self,
                context,
                application,
                line_assertion,
                expected_conclusion_hint,
                line,
                candidate_rule_id,
                &attempt_theorem,
                &attempt_theorem_vars,
            ) catch |err| {
                CheckedIr.rollbackToMark(allocator, context.checked, checked_mark);
                attempt_theorem_vars.deinit();
                attempt_theorem.deinit();
                if (first_err == null) {
                    first_err = err;
                    first_diag = getDiagnostic(self);
                }
                candidate_rule_id = next_fallback orelse {
                    var diag = first_diag orelse saved_diag;
                    if (first_diag != null) {
                        if (diag) |*actual_diag| {
                            addFallbackFailureNote(
                                actual_diag,
                                line_assertion,
                                line,
                            );
                        }
                    }
                    restoreDiagnostic(self, diag);
                    return first_err.?;
                };
                continue;
            };

            validateAttemptCheckedIrRange(
                self,
                context.env,
                &attempt.theorem,
                context.parser,
                &attempt.theorem_vars,
                diag_context.theorem_name,
                context.checked.items[checked_mark..],
                diag_context.line_label,
                diag_context.span,
                .theorem_application,
                saved_diag,
            ) catch |err| {
                CheckedIr.rollbackToMark(allocator, context.checked, checked_mark);
                attempt.theorem_vars.deinit();
                attempt.theorem.deinit();
                return err;
            };

            // Materialize the COW clone before it replaces (and frees) its base.
            attempt.theorem.flatten() catch |err| {
                CheckedIr.rollbackToMark(allocator, context.checked, checked_mark);
                attempt.theorem_vars.deinit();
                attempt.theorem.deinit();
                return err;
            };
            var old_theorem = theorem.*;
            theorem.* = attempt.theorem;
            old_theorem.deinit();
            theorem_vars.deinit();
            theorem_vars.* = attempt.theorem_vars;
            restoreDiagnostic(self, saved_diag);
            return attempt;
        }

        const attempt = tryApplyRuleApplicationWithCandidate(
            self,
            context,
            application,
            line_assertion,
            expected_conclusion_hint,
            line,
            candidate_rule_id,
            theorem,
            theorem_vars,
        ) catch |err| {
            return err;
        };

        try validateAttemptCheckedIrRange(
            self,
            context.env,
            theorem,
            context.parser,
            theorem_vars,
            diag_context.theorem_name,
            context.checked.items[checked_mark..],
            diag_context.line_label,
            diag_context.span,
            .theorem_application,
            saved_diag,
        );

        restoreDiagnostic(self, saved_diag);
        return attempt;
    }
}

pub fn probeRuleConclusion(
    self: *CompilerContext,
    context: *const RuleApplyContext,
    application: RuleApplication,
    line_assertion: LineAssertion,
    expected_conclusion_hint: ?ExprId,
    diag_context: ApplicationDiagnosticContext,
    line: ApplicationLine,
    rule_id: u32,
    theorem: *TheoremContext,
    theorem_vars: *NameExprMap,
) anyerror!ConclusionProbe {
    const checked_mark = context.checked.items.len;
    defer CheckedIr.rollbackToMark(
        context.allocator,
        context.checked,
        checked_mark,
    );

    const result = try applyRuleCandidateCore(
        self,
        context,
        application,
        line_assertion,
        expected_conclusion_hint,
        diag_context,
        line,
        rule_id,
        theorem,
        theorem_vars,
        .conclusion_probe,
    );
    return result.conclusion_probe;
}

pub fn probeExpectedRefsForApplication(
    self: *CompilerContext,
    context: *const RuleApplyContext,
    application: RuleApplication,
    line_assertion: LineAssertion,
    expected_conclusion_hint: ?ExprId,
    diag_context: ApplicationDiagnosticContext,
    line: ApplicationLine,
    theorem: *TheoremContext,
    theorem_vars: *NameExprMap,
) anyerror!RefExpectationProbe {
    const allocator = context.allocator;
    const rule_id = try lookupRuleApplicationId(
        self,
        context.env,
        context.rule_catalog,
        context.labels,
        diag_context,
        application,
    );
    const rule = &context.env.rules.items[rule_id];
    const partial_bindings = try parseBindings(
        self,
        allocator,
        context.parser,
        theorem,
        theorem_vars,
        context.sort_vars,
        context.assertion.name,
        rule,
        application,
        line,
    );
    defer allocator.free(partial_bindings);
    const bindings = try allocator.dupe(?ExprId, partial_bindings);
    errdefer allocator.free(bindings);
    const probe = try inferExpectedRefsForInlineApplicationProbe(
        self,
        context,
        application,
        line_assertion,
        expected_conclusion_hint,
        line,
        rule_id,
        rule,
        theorem,
        theorem_vars,
        partial_bindings,
        .strict,
    );
    errdefer allocator.free(probe.contextual_bindings);
    errdefer allocator.free(probe.expected_refs);
    return .{
        .allocator = allocator,
        .rule_id = rule_id,
        .bindings = bindings,
        .contextual_bindings = probe.contextual_bindings,
        .expected_refs = probe.expected_refs,
    };
}

const CandidateApplyKind = enum {
    full_application,
    conclusion_probe,
};

const CandidateApplyResult = union(CandidateApplyKind) {
    full_application: SuccessfulLineAttempt,
    conclusion_probe: ConclusionProbe,
};

fn applyRuleCandidateCore(
    self: *CompilerContext,
    context: *const RuleApplyContext,
    application: RuleApplication,
    line_assertion: LineAssertion,
    expected_conclusion_hint: ?ExprId,
    diag_context: ApplicationDiagnosticContext,
    line: ApplicationLine,
    rule_id: u32,
    theorem: *TheoremContext,
    theorem_vars: *NameExprMap,
    kind: CandidateApplyKind,
) anyerror!CandidateApplyResult {
    const allocator = context.allocator;
    const parser = context.parser;
    const env = context.env;
    const registry = context.registry;
    const assertion = context.assertion;
    const checked = context.checked;
    const diag_scratch = context.diag_scratch;
    const rule = &env.rules.items[rule_id];
    var conclusion_rule = rule.*;
    if (kind == .conclusion_probe) conclusion_rule.hyps = &.{};
    const inference_rule = if (kind == .conclusion_probe)
        &conclusion_rule
    else
        rule;
    const expected_ref_count = switch (kind) {
        .full_application => rule.hyps.len,
        .conclusion_probe => 0,
    };

    if (application.refs.len != expected_ref_count) {
        self.setProof(CompilerDiag.withPhase(.{
            .kind = .ref_count_mismatch,
            .err = error.RefCountMismatch,
            .theorem_name = diag_context.theorem_name,
            .line_label = diag_context.line_label,
            .rule_name = application.rule_name,
            .span = application.refsOrRuleSpan(),
        }, .theorem_application));
        return error.RefCountMismatch;
    }

    const partial_bindings = try parseBindings(
        self,
        allocator,
        parser,
        theorem,
        theorem_vars,
        context.sort_vars,
        assertion.name,
        rule,
        application,
        line,
    );
    defer allocator.free(partial_bindings);

    var expected_refs: []?ExprId = &.{};
    if (kind == .full_application) {
        expected_refs = try inferExpectedRefsForInlineApplications(
            allocator,
            theorem,
            rule,
            line_assertion,
            expected_conclusion_hint,
            partial_bindings,
        );
        try fillHoleyInlineHints(
            self,
            context,
            application,
            line_assertion,
            expected_conclusion_hint,
            line,
            rule_id,
            rule,
            theorem,
            theorem_vars,
            partial_bindings,
            expected_refs,
        );
    }
    defer if (kind == .full_application) allocator.free(expected_refs);

    const refs = try allocator.alloc(CheckedRef, expected_ref_count);
    var refs_owned = true;
    errdefer if (refs_owned) allocator.free(refs);
    const ref_exprs = try allocator.alloc(ExprId, expected_ref_count);
    defer allocator.free(ref_exprs);

    if (kind == .full_application) {
        try elaborateRefs(
            self,
            context,
            line,
            theorem,
            theorem_vars,
            rule,
            partial_bindings,
            line_assertion,
            expected_conclusion_hint,
            application.refs,
            expected_refs,
            refs,
            ref_exprs,
        );
    }

    const explicit_bindings = try allocator.dupe(?ExprId, partial_bindings);
    defer allocator.free(explicit_bindings);

    if (context.fresh_bindings.get(rule_id)) |rule_fresh| {
        try applyFreshBindings(
            self,
            parser,
            env,
            theorem,
            theorem_vars,
            context.sort_vars,
            assertion.name,
            rule,
            line,
            try lineAssertionKnownDeps(
                env,
                theorem,
                rule,
                line_assertion,
                partial_bindings,
            ),
            ref_exprs,
            partial_bindings,
            rule_fresh,
        );
    }

    var maybe_view = context.views.get(rule_id);
    if (kind == .conclusion_probe) {
        if (maybe_view) |*view| view.hyps = &.{};
    }
    const had_omitted = Inference.hasOmittedBindings(partial_bindings);
    const has_omitted_structural = had_omitted and
        try Inference.hasOmittedStructuralBindings(
            env,
            registry,
            inference_rule,
            partial_bindings,
        );
    const prefer_structural_solver = had_omitted and
        try Inference.shouldPreferStructuralSolver(
            env,
            registry,
            inference_rule,
            partial_bindings,
        );
    const rule_has_advanced_inference =
        maybe_view != null or
        has_omitted_structural;
    const use_advanced_inference = had_omitted and
        rule_has_advanced_inference;

    if (maybe_view) |view| {
        if (!use_advanced_inference) {
            switch (line_assertion) {
                .concrete => |line_expr| {
                    CompilerViews.applyViewBindings(
                        allocator,
                        theorem,
                        env,
                        registry,
                        &view,
                        line_expr,
                        ref_exprs,
                        partial_bindings,
                        null,
                        null,
                        self.debug.views,
                    ) catch |err| {
                        self.setProof(CompilerDiag.withPhase(.{
                            .kind = .generic,
                            .err = CompilerDiag.narrowDiagnosticError(err),
                            .theorem_name = assertion.name,
                            .line_label = line.label,
                            .rule_name = line.application.rule_name,
                            .span = line.ruleApplicationSpan(),
                        }, .theorem_application));
                        return err;
                    };
                },
                .holey, .implicit_whole_conclusion => {},
            }
        }
    }

    const fresh_context: Inference.HiddenWitnessFreshContext = .{
        .parser = parser,
        .theorem_vars = theorem_vars,
        .sort_vars = context.sort_vars,
    };
    const inference_context: Inference.RuleInferenceContext = .{
        .allocator = allocator,
        .env = env,
        .registry = registry,
        .scratch = diag_scratch,
        .theorem = theorem,
        .assertion = assertion,
        .rule_id = rule_id,
        .rule = inference_rule,
        .rule_unify_cache = if (kind == .conclusion_probe)
            null
        else
            context.rule_unify_cache,
    };

    if (kind == .conclusion_probe) {
        const optional_bindings = try inferCandidateOptionalBindings(
            self,
            &inference_context,
            line,
            line_assertion,
            partial_bindings,
            ref_exprs,
            expected_conclusion_hint,
            fresh_context,
            maybe_view,
            had_omitted,
            rule_has_advanced_inference,
            use_advanced_inference,
            has_omitted_structural,
            prefer_structural_solver,
        );
        defer allocator.free(optional_bindings);

        try validateOptionalBindingsForProbe(
            self,
            env,
            theorem,
            parser,
            theorem_vars,
            assertion,
            line,
            rule,
            optional_bindings,
        );
        restoreDiagnostic(self, null);

        const filled_bindings = try OpenTerms.fillOptionalBindingsForProbe(
            theorem,
            rule,
            optional_bindings,
        );
        var filled_bindings_owned = true;
        errdefer if (filled_bindings_owned) allocator.free(filled_bindings);

        const candidate = try elaborateCandidateLine(
            self,
            allocator,
            parser,
            theorem,
            env,
            registry,
            diag_scratch,
            assertion,
            line,
            rule,
            line_assertion,
            filled_bindings,
        );

        if (context.fresh_bindings.get(rule_id)) |rule_fresh| {
            try validateFreshBindingsAgainstLine(
                self,
                allocator,
                env,
                theorem,
                assertion.name,
                rule,
                line,
                candidate.displayed_conclusion,
                ref_exprs,
                explicit_bindings,
                filled_bindings,
                rule_fresh,
            );
        }

        const conclusion_mark = checked.items.len;
        // A probe may be abandoned, so it must not allocate theorem-local
        // hidden witnesses. The full application below gets the provider.
        const line_idx = (Matching.tryBuildConclusionLine(
            allocator,
            theorem,
            registry,
            env,
            checked,
            diag_scratch,
            self.debug,
            null,
            candidate.displayed_conclusion,
            candidate.raw_conclusion,
            rule_id,
            filled_bindings,
            refs,
        ) catch |err| {
            if (checkedRangeOwnsRefs(checked.items[conclusion_mark..], refs)) {
                refs_owned = false;
            }
            if (checkedRangeOwnsBindings(
                checked.items[conclusion_mark..],
                filled_bindings,
            )) {
                filled_bindings_owned = false;
            }
            CheckedIr.rollbackToMark(allocator, checked, conclusion_mark);
            return err;
        }) orelse {
            CheckedIr.rollbackToMark(allocator, checked, conclusion_mark);
            return error.ConclusionMismatch;
        };
        _ = line_idx;
        refs_owned = false;
        filled_bindings_owned = false;

        const owned_bindings = try allocator.dupe(?ExprId, optional_bindings);
        errdefer allocator.free(owned_bindings);
        const unresolved = try allocator.alloc(
            UnresolvedHypothesis,
            rule.hyps.len,
        );
        errdefer allocator.free(unresolved);
        for (rule.hyps, 0..) |hyp, idx| {
            unresolved[idx] = .{
                .index = idx,
                .expected = if (OpenTerms.templateHasUnresolvedBinder(
                    hyp,
                    owned_bindings,
                ))
                    null
                else
                    try theorem.instantiateTemplate(hyp, filled_bindings),
            };
        }

        return .{ .conclusion_probe = .{
            .allocator = allocator,
            .rule_id = rule_id,
            .rule_name = rule.name,
            .bindings = owned_bindings,
            .raw_conclusion = candidate.raw_conclusion,
            .displayed_conclusion = candidate.displayed_conclusion,
            .unresolved_hyps = unresolved,
        } };
    }

    const bindings = try inferCandidateBindings(
        self,
        &inference_context,
        line,
        line_assertion,
        partial_bindings,
        ref_exprs,
        expected_conclusion_hint,
        fresh_context,
        maybe_view,
        had_omitted,
        rule_has_advanced_inference,
        use_advanced_inference,
        has_omitted_structural,
        prefer_structural_solver,
    );

    var resolved_bindings = bindings;
    var freshen_steps: std.ArrayListUnmanaged(AlphaRewrite.FreshenResult) = .{};
    defer freshen_steps.deinit(allocator);
    Inference.validateResolvedBindingsWithDebug(
        self,
        self.debug,
        env,
        theorem,
        parser,
        theorem_vars,
        assertion,
        line,
        rule,
        resolved_bindings,
    ) catch |err| {
        if (err != error.DepViolation) return err;
        const rule_freshen = context.freshen_bindings.get(rule_id) orelse
            return err;
        var dep_detail = (try Inference.firstDepViolation(
            env,
            theorem,
            assertion.args,
            rule.args,
            rule.arg_names,
            resolved_bindings,
        )) orelse return err;
        // Repair blocked targets one at a time: each pass alpha-renames the
        // single argument named by the current violation, then re-checks.
        // One application can need several passes — e.g. ex_elim with the
        // eigenvariable bound in both the side context and the conclusion.
        // Each successful pass removes its (target, blocker) violation and
        // never adds one, so the loop is bounded by the declared targets;
        // the cap is a backstop.
        while (true) {
            var dep_text_bufs: Inference.DepViolationTextBufs = .{};
            Inference.attachDepViolationBindingTexts(
                &dep_text_bufs,
                env,
                theorem,
                parser,
                theorem_vars,
                &dep_detail,
                resolved_bindings[dep_detail.first_arg_idx],
                resolved_bindings[dep_detail.second_arg_idx],
            );
            var freshen_report: AlphaRewrite.FreshenAttemptReport = .{};
            const step = AlphaRewrite.tryFreshenBindings(
                allocator,
                parser,
                env,
                registry,
                theorem,
                theorem_vars,
                context.sort_vars,
                rule,
                try resolveLineAssertionForBindings(
                    self,
                    allocator,
                    parser,
                    theorem,
                    env,
                    registry,
                    diag_scratch,
                    assertion,
                    line,
                    rule,
                    line_assertion,
                    resolved_bindings,
                ),
                ref_exprs,
                resolved_bindings,
                rule_freshen,
                dep_detail,
                checked,
                diag_scratch,
                self.debug,
                &freshen_report,
            ) catch |fresh_err| {
                var diag = CompilerDiag.withPhase(.{
                    .kind = .generic,
                    .err = CompilerDiag.narrowDiagnosticError(fresh_err),
                    .theorem_name = assertion.name,
                    .line_label = line.label,
                    .rule_name = application.rule_name,
                    .span = application.ruleApplicationSpan(),
                    .detail = .{ .dep_violation = dep_detail },
                }, .theorem_application);
                addFreshenAttemptNotes(&diag, rule, freshen_report);
                self.setProof(diag);
                return fresh_err;
            } orelse {
                if (freshen_steps.items.len == 0) return err;
                // Earlier passes made progress, but this violation has no
                // matching @freshen declaration to repair it.
                var diag = CompilerDiag.withPhase(.{
                    .kind = .generic,
                    .err = error.AlphaRewriteSearchFailed,
                    .theorem_name = assertion.name,
                    .line_label = line.label,
                    .rule_name = application.rule_name,
                    .span = application.ruleApplicationSpan(),
                    .detail = .{ .dep_violation = dep_detail },
                }, .theorem_application);
                addFreshenAttemptNotes(&diag, rule, freshen_report);
                self.setProof(diag);
                return error.AlphaRewriteSearchFailed;
            };
            try freshen_steps.append(allocator, step);
            resolved_bindings = step.bindings;
            dep_detail = (try Inference.firstDepViolation(
                env,
                theorem,
                assertion.args,
                rule.args,
                rule.arg_names,
                resolved_bindings,
            )) orelse break;
            if (freshen_steps.items.len > rule_freshen.len) {
                var remaining_text_bufs: Inference.DepViolationTextBufs = .{};
                Inference.attachDepViolationBindingTexts(
                    &remaining_text_bufs,
                    env,
                    theorem,
                    parser,
                    theorem_vars,
                    &dep_detail,
                    resolved_bindings[dep_detail.first_arg_idx],
                    resolved_bindings[dep_detail.second_arg_idx],
                );
                var diag = CompilerDiag.withPhase(.{
                    .kind = .generic,
                    .err = error.AlphaRewriteSearchFailed,
                    .theorem_name = assertion.name,
                    .line_label = line.label,
                    .rule_name = application.rule_name,
                    .span = application.ruleApplicationSpan(),
                    .detail = .{ .dep_violation = dep_detail },
                }, .theorem_application);
                addFreshenAttemptNotes(&diag, rule, freshen_report);
                self.setProof(diag);
                return error.AlphaRewriteSearchFailed;
            }
        }
        restoreDiagnostic(self, null);
        try Inference.validateResolvedBindingsWithDebug(
            self,
            self.debug,
            env,
            theorem,
            parser,
            theorem_vars,
            assertion,
            line,
            rule,
            resolved_bindings,
        );
    };
    restoreDiagnostic(self, null);

    if (freshen_steps.items.len != 0) {
        if (context.fresh_bindings.get(rule_id)) |rule_fresh| {
            try validateFreshBindingsAgainstLine(
                self,
                allocator,
                env,
                theorem,
                assertion.name,
                rule,
                line,
                try resolveLineAssertionForBindings(
                    self,
                    allocator,
                    parser,
                    theorem,
                    env,
                    registry,
                    diag_scratch,
                    assertion,
                    line,
                    rule,
                    line_assertion,
                    bindings,
                ),
                ref_exprs,
                explicit_bindings,
                bindings,
                rule_fresh,
            );
        }
        const line_idx = applyFreshenedRuleLine(
            allocator,
            theorem,
            registry,
            env,
            checked,
            diag_scratch,
            try resolveLineAssertionForBindings(
                self,
                allocator,
                parser,
                theorem,
                env,
                registry,
                diag_scratch,
                assertion,
                line,
                rule,
                line_assertion,
                bindings,
            ),
            rule,
            rule_id,
            bindings,
            freshen_steps.items,
            refs,
            ref_exprs,
        ) catch |err| {
            self.setProof(CompilerDiag.withPhase(.{
                .kind = .generic,
                .err = CompilerDiag.narrowDiagnosticError(err),
                .theorem_name = assertion.name,
                .line_label = line.label,
                .rule_name = line.application.rule_name,
                .span = line.ruleApplicationSpan(),
            }, .theorem_application));
            return err;
        };
        allocator.free(refs);
        refs_owned = false;
        return .{ .full_application = .{
            .line_idx = line_idx,
            .theorem = theorem.*,
            .theorem_vars = theorem_vars.*,
        } };
    }

    for (ref_exprs, application.refs, 0..) |actual, ref, idx| {
        const expected = try theorem.instantiateTemplate(
            rule.hyps[idx],
            resolved_bindings,
        );
        const match_mark = diag_scratch.mark();
        if (Matching.tryMatchHypothesis(
            allocator,
            theorem,
            registry,
            env,
            checked,
            diag_scratch,
            self.debug,
            idx,
            refs[idx],
            actual,
            expected,
        ) catch |err| {
            if (self.setProofScratchDiagnosticIfPresent(
                diag_scratch,
                match_mark,
                env,
                .theorem_application,
                .generic,
                err,
                assertion.name,
                line.label,
                application.rule_name,
                refSpan(application.refs[idx]),
            )) {
                return err;
            }
            diag_scratch.discard(match_mark);
            return err;
        }) |matched_ref| {
            diag_scratch.discard(match_mark);
            refs[idx] = matched_ref;
            continue;
        }
        diag_scratch.discard(match_mark);
        const span = switch (ref) {
            .hyp => |hyp| hyp.span,
            .line => |label| label.span,
            .application => |inline_app| inline_app.span,
        };
        var diag = switch (ref) {
            .hyp => |hyp| CompilerDiag.withPhase(Diagnostic{
                .kind = .hypothesis_mismatch,
                .err = error.HypothesisMismatch,
                .theorem_name = assertion.name,
                .line_label = line.label,
                .rule_name = line.application.rule_name,
                .span = span,
                .detail = .{
                    .hypothesis_ref = .{
                        .index = hyp.index,
                        .name = hyp.name,
                    },
                },
            }, .theorem_application),
            .line => |label| CompilerDiag.withPhase(Diagnostic{
                .kind = .hypothesis_mismatch,
                .err = error.HypothesisMismatch,
                .theorem_name = assertion.name,
                .line_label = line.label,
                .rule_name = line.application.rule_name,
                .name = label.label,
                .span = span,
            }, .theorem_application),
            .application => |inline_app| CompilerDiag.withPhase(Diagnostic{
                .kind = .hypothesis_mismatch,
                .err = error.HypothesisMismatch,
                .theorem_name = assertion.name,
                .line_label = line.label,
                .rule_name = line.application.rule_name,
                .name = inline_app.rule_name,
                .span = span,
            }, .theorem_application),
        };
        try addComparisonSnapshotNotes(
            allocator,
            &diag,
            theorem,
            env,
            parser,
            theorem_vars,
            registry,
            diag_scratch,
            expected,
            actual,
            true,
        );
        self.setProof(diag);
        return error.HypothesisMismatch;
    }

    const candidate = try elaborateCandidateLine(
        self,
        allocator,
        parser,
        theorem,
        env,
        registry,
        diag_scratch,
        assertion,
        line,
        rule,
        line_assertion,
        resolved_bindings,
    );

    if (context.fresh_bindings.get(rule_id)) |rule_fresh| {
        try validateFreshBindingsAgainstLine(
            self,
            allocator,
            env,
            theorem,
            assertion.name,
            rule,
            line,
            candidate.displayed_conclusion,
            ref_exprs,
            explicit_bindings,
            candidate.resolved_bindings,
            rule_fresh,
        );
    }

    const concl_checked_mark = checked.items.len;
    const concl_mark = diag_scratch.mark();
    const line_idx = (Matching.tryBuildConclusionLine(
        allocator,
        theorem,
        registry,
        env,
        checked,
        diag_scratch,
        self.debug,
        fresh_context,
        candidate.displayed_conclusion,
        candidate.raw_conclusion,
        rule_id,
        candidate.resolved_bindings,
        refs,
    ) catch |err| {
        if (checkedRangeOwnsRefs(checked.items[concl_checked_mark..], refs)) {
            refs_owned = false;
        }
        if (self.setProofScratchDiagnosticIfPresent(
            diag_scratch,
            concl_mark,
            env,
            .theorem_application,
            .generic,
            err,
            assertion.name,
            line.label,
            line.application.rule_name,
            line.assertion_span,
        )) {
            return err;
        }
        diag_scratch.discard(concl_mark);
        return err;
    }) orelse {
        diag_scratch.discard(concl_mark);
        var diag = CompilerDiag.withPhase(.{
            .kind = .conclusion_mismatch,
            .err = error.ConclusionMismatch,
            .theorem_name = assertion.name,
            .line_label = line.label,
            .rule_name = line.application.rule_name,
            .span = line.assertion_span,
        }, .theorem_application);
        try addComparisonSnapshotNotes(
            allocator,
            &diag,
            theorem,
            env,
            parser,
            theorem_vars,
            registry,
            diag_scratch,
            candidate.raw_conclusion,
            candidate.displayed_conclusion,
            true,
        );
        self.setProof(diag);
        return error.ConclusionMismatch;
    };
    refs_owned = false;
    diag_scratch.discard(concl_mark);

    return .{ .full_application = .{
        .line_idx = line_idx,
        .theorem = theorem.*,
        .theorem_vars = theorem_vars.*,
    } };
}

fn tryApplyRuleApplicationWithCandidate(
    self: *CompilerContext,
    context: *const RuleApplyContext,
    application: RuleApplication,
    line_assertion: LineAssertion,
    expected_conclusion_hint: ?ExprId,
    line: ApplicationLine,
    rule_id: u32,
    theorem: *TheoremContext,
    theorem_vars: *NameExprMap,
) anyerror!SuccessfulLineAttempt {
    const result = try applyRuleCandidateCore(
        self,
        context,
        application,
        line_assertion,
        expected_conclusion_hint,
        .{
            .theorem_name = context.assertion.name,
            .line_label = line.label,
            .span = line.assertion_span,
        },
        line,
        rule_id,
        theorem,
        theorem_vars,
        .full_application,
    );
    return result.full_application;
}

fn elaborateRefs(
    self: *CompilerContext,
    context: *const RuleApplyContext,
    line: ApplicationLine,
    theorem: *TheoremContext,
    theorem_vars: *NameExprMap,
    rule: *const RuleDecl,
    partial_bindings: []const ?ExprId,
    line_assertion: LineAssertion,
    expected_conclusion_hint: ?ExprId,
    source_refs: []const Ref,
    expected_ref_exprs: []const ?ExprId,
    refs: []CheckedRef,
    ref_exprs: []ExprId,
) anyerror!void {
    const assertion = context.assertion;
    for (source_refs, 0..) |ref, idx| {
        ref_exprs[idx] = switch (ref) {
            .hyp => |hyp| blk: {
                const resolved = ProofScript.resolveHypRef(
                    theorem.theorem_hyp_names,
                    theorem.theorem_hyps.items.len,
                    hyp,
                );
                const hyp_idx = switch (resolved) {
                    .index => |value| value,
                    .unknown, .ambiguous => {
                        self.setProof(CompilerDiag.withPhase(.{
                            .kind = if (resolved == .ambiguous)
                                .ambiguous_hypothesis_ref
                            else
                                .unknown_hypothesis_ref,
                            .err = if (resolved == .ambiguous)
                                error.AmbiguousHypothesisRef
                            else
                                error.UnknownHypothesisRef,
                            .theorem_name = assertion.name,
                            .line_label = line.label,
                            .span = hyp.span,
                            .detail = .{
                                .hypothesis_ref = .{
                                    .index = hyp.index,
                                    .name = hyp.name,
                                },
                            },
                        }, .theorem_application));
                        return if (resolved == .ambiguous)
                            error.AmbiguousHypothesisRef
                        else
                            error.UnknownHypothesisRef;
                    },
                };
                refs[idx] = .{ .hyp = hyp_idx };
                break :blk theorem.theorem_hyps.items[hyp_idx];
            },
            .line => |label| blk: {
                const line_idx = context.labels.get(label.label) orelse {
                    var label_diag = CompilerDiag.withPhase(.{
                        .kind = .unknown_label,
                        .err = error.UnknownLabel,
                        .theorem_name = assertion.name,
                        .line_label = line.label,
                        .name = label.label,
                        .span = label.span,
                    }, .theorem_application);
                    if (labelAppearsInBlock(
                        context.block_lines,
                        label.label,
                    )) {
                        CompilerDiag.addNote(
                            &label_diag,
                            .label_belongs_to_later_line,
                            .proof,
                            null,
                        );
                    } else if (closestKeyName(
                        context.labels,
                        label.label,
                    )) |suggestion| {
                        label_diag.detail = .{ .name_suggestion = .{
                            .suggestion = suggestion,
                        } };
                    }
                    self.setProof(label_diag);
                    return error.UnknownLabel;
                };
                refs[idx] = .{ .line = line_idx };
                break :blk context.checked.items[line_idx].expr;
            },
            .application => |inline_app| blk: {
                const hint = try refinedInlineHint(
                    context,
                    theorem,
                    rule,
                    partial_bindings,
                    line_assertion,
                    expected_conclusion_hint,
                    expected_ref_exprs[idx],
                    ref_exprs,
                    idx,
                );
                const attempt = try applyRuleApplication(
                    self,
                    context,
                    inline_app,
                    .implicit_whole_conclusion,
                    hint,
                    .{
                        .theorem_name = assertion.name,
                        .line_label = line.label,
                        .span = inline_app.span,
                    },
                    line.forInline(inline_app),
                    theorem,
                    theorem_vars,
                );
                refs[idx] = .{ .line = attempt.line_idx };
                const conclusion =
                    context.checked.items[attempt.line_idx].expr;
                try recordInlineConclusion(
                    self,
                    context,
                    theorem,
                    theorem_vars,
                    inline_app.span,
                    conclusion,
                );
                break :blk conclusion;
            },
        };
    }
}

/// Record the conclusion an inline application elaborated to, rendered with
/// declared notation and source binder names, for presentation features (the
/// `unpack` code action). Fallback retries re-record the same span; the last
/// entry wins, and entries from candidates that were rolled back are
/// harmless because consumers only read the sink out of documents that
/// analyzed cleanly. No-op (and free) when no sink is configured.
fn recordInlineConclusion(
    self: *CompilerContext,
    context: *const RuleApplyContext,
    theorem: *const TheoremContext,
    theorem_vars: *const NameExprMap,
    span: Span,
    conclusion: ExprId,
) !void {
    const sink = self.inline_conclusion_sink orelse return;
    var names = try ViewTrace.DiagNames.build(
        context.allocator,
        theorem,
        context.parser,
        theorem_vars,
    );
    defer names.deinit(context.allocator);
    const rendered = try ViewTrace.formatExprNamed(
        sink.allocator,
        theorem,
        context.env,
        &names,
        conclusion,
    );
    try sink.addOwned(span, rendered);
}

/// Sharpen an inline minor's expected-conclusion hint using the concrete
/// conclusions of the siblings already elaborated to its left.
///
/// The up-front hint passes (`inferExpectedRefsForInlineApplications` +
/// `fillHoleyInlineHints`) run before any ref is elaborated, so a
/// hypothesis-only binder shared between two hypotheses — `hoare_seq`'s `q` in
/// `⦃p⦄a⟦q⟧ > ⦃q⦄b⟦r⟧ > ⦃p⦄(a⨟b)⟦r⟧` — is left open: no ref expression is known
/// yet. By the time `elaborateRefs` reaches ref `idx`, every earlier sibling has
/// a concrete conclusion (`ref_exprs[0..idx]`). Folding those conclusions back
/// through the rule's hypothesis templates pins `q`, so the minor's hint sharpens
/// from a hole (`⦃‹hole›⦄ skip ⟦p∧¬b⟧`) to the fully concrete
/// `⦃p∧¬b⦄ skip ⟦p∧¬b⟧`. Without it the minor demands an explicit binding
/// (`hoare_skip (p := p∧¬b)`), which strict replay cannot infer because
/// `hoare_skip`'s single binder `p` occupies both a holey pre and a concrete post
/// (bind `p := ‹hole›`, then mismatch on the post).
///
/// Conservative by construction:
///   - only a *null or holey* existing hint is ever replaced — a concrete hint
///     from the strict pre-pass is authoritative and returned unchanged;
///   - the fold accepts only *exact structural* matches (`matchTemplate`, restored
///     on failure), so nothing speculative is committed;
///   - bare ACUI-combiner-spine binders are demoted before instantiation, so a
///     positional context split (`g,h ⊢ …` matched member-wise) declines to
///     refine rather than emit a wrong-but-concrete hint;
///   - instantiation is strict (`instantiateTemplatePartial`): a still-open binder
///     yields null and the original hint is kept.
fn refinedInlineHint(
    context: *const RuleApplyContext,
    theorem: *TheoremContext,
    rule: *const RuleDecl,
    partial_bindings: []const ?ExprId,
    line_assertion: LineAssertion,
    expected_conclusion_hint: ?ExprId,
    existing_hint: ?ExprId,
    ref_exprs: []const ExprId,
    idx: usize,
) !?ExprId {
    if (rule.hyps.len != ref_exprs.len) return existing_hint;
    if (idx >= rule.hyps.len) return existing_hint;

    // A concrete existing hint is authoritative; only null/holey ones are eligible.
    if (existing_hint) |hint| {
        const holey = blk: {
            CheckedIr.validateNoPlaceholderExpr(theorem, hint) catch break :blk true;
            break :blk false;
        };
        if (!holey) return existing_hint;
    }

    const line_expr = expected_conclusion_hint orelse switch (line_assertion) {
        .concrete => |expr| expr,
        .holey, .implicit_whole_conclusion => return existing_hint,
    };

    const allocator = context.allocator;
    const bindings = try allocator.dupe(?ExprId, partial_bindings);
    defer allocator.free(bindings);
    const snap = try allocator.alloc(?ExprId, partial_bindings.len);
    defer allocator.free(snap);

    // Fold the line conclusion, then every already-elaborated sibling's
    // conclusion through its hypothesis template. Each fold is all-or-nothing.
    foldTemplateOrRestore(theorem, rule.concl, line_expr, bindings, snap);
    for (0..idx) |j| {
        foldTemplateOrRestore(theorem, rule.hyps[j], ref_exprs[j], bindings, snap);
    }

    // Drop any positional ACUI-spine commitment so a context split cannot leak a
    // wrong-but-concrete hint (the fold declines rather than guesses a member).
    demoteAcuiSpineBindingsForRule(context.registry, rule, partial_bindings, bindings);

    const refined = try OpenTerms.instantiateTemplatePartial(
        theorem,
        rule.hyps[idx],
        bindings,
    );
    return refined orelse existing_hint;
}

fn refSpan(ref: Ref) Span {
    return switch (ref) {
        .hyp => |hyp| hyp.span,
        .line => |line| line.span,
        .application => |application| application.span,
    };
}
