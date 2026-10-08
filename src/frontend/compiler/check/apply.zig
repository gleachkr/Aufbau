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
const BindingOracle = @import("../context.zig").BindingOracle;
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
const templateMentionsBinder = @import("../../rules.zig").templateMentionsBinder;
const Canonicalizer = @import("../../canonicalizer.zig").Canonicalizer;

const NameExprMap = @import("./types.zig").NameExprMap;
const UnresolvedHypothesis = @import("./types.zig").UnresolvedHypothesis;
const ConclusionProbe = @import("./types.zig").ConclusionProbe;
const RefExpectationProbe = @import("./types.zig").RefExpectationProbe;
const LineAssertion = @import("./types.zig").LineAssertion;
const LineGoal = @import("./types.zig").LineGoal;
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
const ambiguousPrincipalPins = @import("./inline_hints.zig").ambiguousPrincipalPins;
const freePrincipalPins = @import("./inline_hints.zig").freePrincipalPins;
const cloneNameExprMap = @import("./types.zig").cloneNameExprMap;
const getDiagnostic = @import("./types.zig").getDiagnostic;
const restoreDiagnostic = @import("./types.zig").restoreDiagnostic;
const parseBindings = @import("./bindings.zig").parseBindings;
const lineAssertionKnownDeps = @import("./bindings.zig").lineAssertionKnownDeps;
const validateFreshBindingsAgainstLine = @import("./bindings.zig").validateFreshBindingsAgainstLine;
const applyFreshBindings = @import("./bindings.zig").applyFreshBindings;

/// Elaborate one rule application (with `@fallback` candidates and ambiguous
/// ACUI principal retries) and return the index of the checked line it
/// produced. Attempt ownership rules:
/// - a speculative attempt works on COW clones (`SpeculativeAttempt`); a
///   failed one is aborted — its checked lines, inline-conclusion sink
///   entries and clones are discarded — before the next candidate runs;
/// - diagnostics: the first failing candidate's diagnostic is the one
///   reported if every candidate fails; a success restores the entry
///   diagnostic;
/// - on error, sink entries recorded during this call are dropped (the
///   checked IR and, on the non-speculative path, the theorem are left to
///   the caller, which discards the whole line).
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
) anyerror!usize {
    const outermost = self.stack_base == null;
    if (outermost) self.stack_base = @frameAddress();
    defer if (outermost) {
        self.stack_base = null;
    };
    try checkStackGuard(self, application, diag_context);
    const allocator = context.allocator;
    const sink_mark = if (self.inline_conclusion_sink) |sink| sink.mark() else 0;
    errdefer if (self.inline_conclusion_sink) |sink| sink.rollback(sink_mark);
    const oracle_mark = if (self.binding_oracle) |oracle| oracle.mark() else 0;
    errdefer if (self.binding_oracle) |oracle| oracle.rollback(oracle_mark);
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
        // Ambiguous ACUI principal: the plain attempt runs speculatively so a
        // failure can be retried with each competing member pinned (see
        // `ambiguousPrincipalPins`). Only an inline minor can depend on the
        // principal before any concrete ref fixes it, so other applications
        // skip the scan.
        const pins = if (hasInlineRef(application))
            try principalPinsFor(
                allocator,
                context,
                theorem,
                candidate_rule_id,
                line_assertion,
                expected_conclusion_hint,
            )
        else
            &.{};
        defer if (pins.len != 0) freePrincipalPins(allocator, pins);
        const speculative = first_err != null or next_fallback != null or
            pins.len != 0;
        restoreDiagnostic(self, if (speculative) null else saved_diag);
        const checked_mark = context.checked.items.len;

        if (speculative) {
            var attempt = SpeculativeAttempt.run(
                self,
                context,
                application,
                line_assertion,
                expected_conclusion_hint,
                line,
                candidate_rule_id,
                theorem,
                theorem_vars,
                &.{},
            ) catch |err| retry: {
                if (unrecoverable(err)) return err;
                const err_diag = getDiagnostic(self);
                for (pins) |pin| {
                    restoreDiagnostic(self, null);
                    if (SpeculativeAttempt.run(
                        self,
                        context,
                        application,
                        line_assertion,
                        expected_conclusion_hint,
                        line,
                        candidate_rule_id,
                        theorem,
                        theorem_vars,
                        pin,
                    )) |pinned| {
                        break :retry pinned;
                    } else |pin_err| {
                        if (unrecoverable(pin_err)) return pin_err;
                    }
                }
                restoreDiagnostic(self, err_diag);
                if (first_err == null) {
                    first_err = err;
                    first_diag = err_diag;
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
                attempt.abort();
                return err;
            };
            const line_idx = try attempt.promote(theorem, theorem_vars);
            restoreDiagnostic(self, saved_diag);
            return line_idx;
        }

        const line_idx = tryApplyRuleApplicationWithCandidate(
            self,
            context,
            application,
            line_assertion,
            expected_conclusion_hint,
            line,
            candidate_rule_id,
            theorem,
            theorem_vars,
            &.{},
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
        return line_idx;
    }
}

/// Call-stack guard for inline elaboration, which recurses through
/// `applyRuleApplication` once per nested inline application. A level costs
/// tens of KiB of native stack (several times that in Debug), so nesting the
/// parser accepts (`ProofScript.max_inline_depth`) can still overflow the
/// runtime stack; on wasm that silently corrupts linear memory. Sized like
/// the search's guard: below the 8 MiB stack the wasm executables link with,
/// leaving room for one level and the non-recursive work under it.
const check_stack_guard_bytes = 6 * 1024 * 1024;

/// Fail the application once the stack below `CompilerContext.stack_base`
/// passes `check_stack_guard_bytes`. Kept out of line so its diagnostic does
/// not enlarge the recursive frame.
noinline fn checkStackGuard(
    self: *CompilerContext,
    application: RuleApplication,
    diag_context: ApplicationDiagnosticContext,
) error{CheckStackExhausted}!void {
    if (self.stack_base.? -| @frameAddress() <= check_stack_guard_bytes) return;
    self.setProof(CompilerDiag.withPhase(.{
        .kind = .generic,
        .err = error.CheckStackExhausted,
        .theorem_name = diag_context.theorem_name,
        .line_label = diag_context.line_label,
        .rule_name = application.rule_name,
        .span = application.span,
    }, .theorem_application));
    return error.CheckStackExhausted;
}

/// Errors no retry with other pins, fallback rules or bindings can recover
/// from. They propagate at once: retrying would repeat the failed descent at
/// every enclosing inline level.
fn unrecoverable(err: anyerror) bool {
    return err == error.OutOfMemory or err == error.CheckStackExhausted;
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
        &.{},
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
    /// Index of the checked line the application produced.
    full_application: usize,
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
    pins: []const ?ExprId,
) anyerror!CandidateApplyResult {
    const allocator = context.allocator;
    const parser = context.parser;
    const env = context.env;
    const assertion = context.assertion;
    const checked = context.checked;
    const rule = &env.rules.items[rule_id];
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
    // Principal pins from `applyRuleApplication`'s ambiguity retry act as
    // explicit bindings; a binder the user bound explicitly keeps its value.
    for (pins, 0..) |pin, idx| {
        if (idx < partial_bindings.len and partial_bindings[idx] == null) {
            partial_bindings[idx] = pin;
        }
    }

    // A withheld search suggestion (`BindingOracle`): the values the search
    // chose for this application's binders, supplied where the checker
    // cannot do without them.
    const withheld: ?BindingOracle.Withheld = blk: {
        if (kind != .full_application) break :blk null;
        const oracle = self.binding_oracle orelse break :blk null;
        const full = oracle.lookup(application) orelse break :blk null;
        var full_app = application;
        full_app.arg_bindings = full;
        break :blk .{
            .oracle = oracle,
            .rule = rule,
            .full = full,
            .values = try parseBindings(
                self,
                allocator,
                parser,
                theorem,
                theorem_vars,
                context.sort_vars,
                assertion.name,
                rule,
                full_app,
                line,
            ),
        };
    };
    defer if (withheld) |w| allocator.free(w.values);
    if (withheld) |w| try w.supply(null, false, partial_bindings);

    var expected_refs: []?ExprId = &.{};
    defer allocator.free(expected_refs);
    if (kind == .full_application) {
        expected_refs = try inlineHints(
            self,
            context,
            application,
            line_assertion,
            expected_conclusion_hint,
            line,
            rule_id,
            theorem,
            theorem_vars,
            partial_bindings,
        );
    }

    const refs = try allocator.alloc(CheckedRef, expected_ref_count);
    var refs_owned = true;
    errdefer if (refs_owned) allocator.free(refs);
    const ref_exprs = try allocator.alloc(ExprId, expected_ref_count);
    defer allocator.free(ref_exprs);

    if (kind == .full_application) while (true) {
        const checked_mark = checked.items.len;
        const sink_mark = if (self.inline_conclusion_sink) |sink| sink.mark() else 0;
        const oracle_mark = if (self.binding_oracle) |oracle| oracle.mark() else 0;
        var failed_ref: ?usize = null;
        elaborateRefs(
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
            &failed_ref,
        ) catch |err| {
            if (unrecoverable(err)) return err;
            const w = withheld orelse return err;
            const idx = failed_ref orelse return err;
            if (application.refs[idx] != .application) return err;
            const take = try allocator.alloc(bool, w.values.len);
            defer allocator.free(take);
            const widest = (try hintRetryBinders(
                allocator,
                theorem,
                rule,
                line_assertion,
                expected_conclusion_hint,
                partial_bindings,
                w.values,
                ref_exprs[0..idx],
                take,
            )) orelse return err;
            CheckedIr.rollbackToMark(allocator, checked, checked_mark);
            if (self.inline_conclusion_sink) |sink| sink.rollback(sink_mark);
            w.oracle.rollback(oracle_mark);
            try w.supply(take, widest, partial_bindings);
            restoreDiagnostic(self, null);
            allocator.free(expected_refs);
            expected_refs = &.{};
            expected_refs = try inlineHints(
                self,
                context,
                application,
                line_assertion,
                expected_conclusion_hint,
                line,
                rule_id,
                theorem,
                theorem_vars,
                partial_bindings,
            );
            continue;
        };
        break;
    };

    return finishCandidate(
        self,
        context,
        application,
        line_assertion,
        expected_conclusion_hint,
        line,
        rule_id,
        theorem,
        theorem_vars,
        kind,
        partial_bindings,
        withheld,
        refs,
        &refs_owned,
        ref_exprs,
    );
}

/// The rest of `applyRuleCandidateCore` once the refs are elaborated:
/// binding inference, @freshen repair, hypothesis matching and the
/// conclusion line. Kept out of line so its many locals and diagnostics are
/// not part of the frame that stays live while nested inline applications
/// recurse. Clears `refs_owned` when `refs` passes to a checked line.
noinline fn finishCandidate(
    self: *CompilerContext,
    context: *const RuleApplyContext,
    application: RuleApplication,
    line_assertion: LineAssertion,
    expected_conclusion_hint: ?ExprId,
    line: ApplicationLine,
    rule_id: u32,
    theorem: *TheoremContext,
    theorem_vars: *NameExprMap,
    kind: CandidateApplyKind,
    partial_bindings: []?ExprId,
    withheld: ?BindingOracle.Withheld,
    refs: []CheckedRef,
    refs_owned: *bool,
    ref_exprs: []ExprId,
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
    const explicit_bindings = try allocator.dupe(?ExprId, partial_bindings);
    defer allocator.free(explicit_bindings);

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
    const node: NodeInference = .{
        .self = self,
        .context = context,
        .line = line,
        .theorem = theorem,
        .theorem_vars = theorem_vars,
        .rule_id = rule_id,
        .rule = rule,
        .inference_rule = inference_rule,
        .kind = kind,
        .line_assertion = line_assertion,
        .expected_conclusion_hint = expected_conclusion_hint,
        .ref_exprs = ref_exprs,
        .inference_context = &inference_context,
        .fresh_context = fresh_context,
    };

    if (kind == .conclusion_probe) {
        const setup = try node.prepare(partial_bindings);
        const optional_bindings = try inferCandidateOptionalBindings(
            self,
            &inference_context,
            line,
            line_assertion,
            partial_bindings,
            ref_exprs,
            expected_conclusion_hint,
            fresh_context,
            setup.maybe_view,
            setup.had_omitted,
            setup.rule_has_advanced_inference,
            setup.use_advanced_inference,
            setup.has_omitted_structural,
            setup.prefer_structural_solver,
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
                refs_owned.* = false;
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
        refs_owned.* = false;
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

    const bindings = if (withheld) |w| node.inferWithOracle(w, explicit_bindings) catch |err| {
        // With every value supplied there is nothing left to disagree on:
        // an inline sub-proof, checked against the weak hint the withheld
        // binders left it, proved something else.
        if (err != error.OutOfMemory) try w.forceStrayed(application.refs);
        return err;
    } else try node.infer(partial_bindings);

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
        refs_owned.* = false;
        return .{ .full_application = line_idx };
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
        // The sub-proof checked against the weak hint the withheld binders
        // left it, and proved something else.
        if (withheld) |w| if (ref == .application) {
            try w.forcePremise(rule.hyps[idx]);
        };
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
            refs_owned.* = false;
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
        switch (line_assertion) {
            .holey => |holey| try DiagNotes.addAcuiFrameObstacleNote(
                allocator,
                &diag,
                line,
                env,
                registry,
                holey.surface,
            ),
            else => {},
        }
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
    refs_owned.* = false;
    diag_scratch.discard(concl_mark);

    return .{ .full_application = line_idx };
}

/// The binders to supply from a withheld application's `values` (#374)
/// after inline sub-proof `siblings.len` failed on its hint: those its
/// premise mentions that folding the line goal and the earlier `siblings`
/// through `rule` leaves unbound or bound only to a placeholder; if none,
/// every one its premise mentions; if none, every one (the fold that fills
/// the rest of the premise may need them: an ACUI split's other side). The
/// fold is `refinedInlineHint`'s first, without its ACUI-spine demotion, so
/// a binder the child's hint lacked can look bound here; the wider tiers
/// catch that. Fills `take`; null when the oracle has no value to add, else
/// whether the tier taken is the last, which over-approximates (its
/// bindings are forced).
/// Out of line, like the other helpers on the inline recursion path (see
/// `checkStackGuard`), so its frame is not part of every level's.
noinline fn hintRetryBinders(
    allocator: std.mem.Allocator,
    theorem: *TheoremContext,
    rule: *const RuleDecl,
    line_assertion: LineAssertion,
    expected_conclusion_hint: ?ExprId,
    partial_bindings: []const ?ExprId,
    values: []const ?ExprId,
    siblings: []const ExprId,
    take: []bool,
) !?bool {
    const premise = rule.hyps[siblings.len];
    const folded = try allocator.alloc(?ExprId, partial_bindings.len);
    defer allocator.free(folded);
    const snap = try allocator.alloc(?ExprId, partial_bindings.len);
    defer allocator.free(snap);
    try foldGoalAndSiblings(
        theorem,
        rule,
        LineGoal.of(expected_conclusion_hint, line_assertion),
        partial_bindings,
        siblings,
        true,
        folded,
        snap,
    );
    const Tier = enum { open_mentioned, mentioned, any };
    for ([_]Tier{ .open_mentioned, .mentioned, .any }) |tier| {
        var any = false;
        for (values, partial_bindings, folded, take, 0..) |value, given, fold, *slot, idx| {
            const open = if (fold) |expr| theorem.containsPlaceholder(expr) else true;
            slot.* = value != null and given == null and switch (tier) {
                .open_mentioned => open and templateMentionsBinder(premise, idx),
                .mentioned => templateMentionsBinder(premise, idx),
                .any => true,
            };
            any = any or slot.*;
        }
        if (any) return tier == .any;
    }
    return null;
}

/// The expected conclusions of an application's inline sub-proofs, from
/// its line goal and the bindings given so far.
fn inlineHints(
    self: *CompilerContext,
    context: *const RuleApplyContext,
    application: RuleApplication,
    line_assertion: LineAssertion,
    expected_conclusion_hint: ?ExprId,
    line: ApplicationLine,
    rule_id: u32,
    theorem: *TheoremContext,
    theorem_vars: *NameExprMap,
    partial_bindings: []?ExprId,
) ![]?ExprId {
    const rule = &context.env.rules.items[rule_id];
    const expected_refs = try inferExpectedRefsForInlineApplications(
        context.allocator,
        theorem,
        context.registry,
        rule,
        line_assertion,
        expected_conclusion_hint,
        partial_bindings,
    );
    errdefer context.allocator.free(expected_refs);
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
    return expected_refs;
}

/// Binder inference for one application, rerunnable from different given
/// bindings (the oracle trials below).
const NodeInference = struct {
    self: *CompilerContext,
    context: *const RuleApplyContext,
    line: ApplicationLine,
    theorem: *TheoremContext,
    theorem_vars: *NameExprMap,
    rule_id: u32,
    rule: *const RuleDecl,
    inference_rule: *const RuleDecl,
    kind: CandidateApplyKind,
    line_assertion: LineAssertion,
    expected_conclusion_hint: ?ExprId,
    ref_exprs: []const ExprId,
    inference_context: *const Inference.RuleInferenceContext,
    fresh_context: Inference.HiddenWitnessFreshContext,

    const Setup = struct {
        maybe_view: ?ViewDecl,
        had_omitted: bool,
        rule_has_advanced_inference: bool,
        use_advanced_inference: bool,
        has_omitted_structural: bool,
        prefer_structural_solver: bool,
    };

    /// Fill the rule's fresh binders into `given`, then pick the solvers.
    fn prepare(n: NodeInference, given: []?ExprId) !Setup {
        const env = n.context.env;
        const registry = n.context.registry;
        if (n.context.fresh_bindings.get(n.rule_id)) |rule_fresh| {
            try applyFreshBindings(
                n.self,
                n.context.parser,
                n.theorem,
                n.theorem_vars,
                n.context.sort_vars,
                n.context.assertion.name,
                n.rule,
                n.line,
                try lineAssertionKnownDeps(
                    env,
                    n.theorem,
                    n.rule,
                    n.line_assertion,
                    given,
                ),
                n.ref_exprs,
                given,
                rule_fresh,
            );
        }
        var maybe_view = n.context.views.get(n.rule_id);
        if (n.kind == .conclusion_probe) {
            if (maybe_view) |*view| view.hyps = &.{};
        }
        const had_omitted = Inference.hasOmittedBindings(given);
        const has_omitted_structural = had_omitted and
            try Inference.hasOmittedStructuralBindings(
                env,
                registry,
                n.inference_rule,
                given,
            );
        const prefer_structural_solver = had_omitted and
            try Inference.shouldPreferStructuralSolver(
                env,
                registry,
                n.inference_rule,
                given,
            );
        const rule_has_advanced_inference =
            maybe_view != null or
            has_omitted_structural;
        return .{
            .maybe_view = maybe_view,
            .had_omitted = had_omitted,
            .rule_has_advanced_inference = rule_has_advanced_inference,
            // A view only guides inference. With every rule binder given
            // there is nothing to infer, and the rule's own check decides:
            // the view's match can reject a line the rule accepts (`rex`
            // with `d` and `x` given leaves only the member `q` of its
            // premise bag open).
            .use_advanced_inference = had_omitted and
                rule_has_advanced_inference,
            .has_omitted_structural = has_omitted_structural,
            .prefer_structural_solver = prefer_structural_solver,
        };
    }

    /// Every binder of the rule, from `given` and inference.
    fn infer(n: NodeInference, given: []?ExprId) ![]const ExprId {
        const setup = try n.prepare(given);
        return inferCandidateBindings(
            n.self,
            n.inference_context,
            n.line,
            n.line_assertion,
            given,
            n.ref_exprs,
            n.expected_conclusion_hint,
            n.fresh_context,
            setup.maybe_view,
            setup.had_omitted,
            setup.rule_has_advanced_inference,
            setup.use_advanced_inference,
            setup.has_omitted_structural,
            setup.prefer_structural_solver,
        );
    }

    /// `infer` on a withheld application (`BindingOracle`): with nothing
    /// supplied when inference reproduces every value the search chose,
    /// otherwise with every value supplied and then each one taken back,
    /// in list order, that inference still reproduces. The values kept are
    /// marked used and added to `explicit`. Fails only as inference with
    /// every value supplied does.
    fn inferWithOracle(
        n: NodeInference,
        w: BindingOracle.Withheld,
        explicit: []?ExprId,
    ) ![]const ExprId {
        const allocator = n.context.allocator;
        const values = w.values;
        const supplied = try allocator.alloc(bool, values.len);
        defer allocator.free(supplied);
        @memset(supplied, false);

        if (try n.agreeingTrial(explicit, values, supplied)) |bindings| {
            return bindings;
        }
        for (values, explicit, supplied) |value, given, *slot| {
            slot.* = value != null and given == null;
        }
        var bindings = try n.inferSupplied(explicit, values, supplied);
        errdefer allocator.free(bindings);
        for (w.full) |binding| {
            const idx = findRuleArgIndex(n.rule, binding.name) orelse continue;
            if (!supplied[idx]) continue;
            supplied[idx] = false;
            if (try n.agreeingTrial(explicit, values, supplied)) |fewer| {
                allocator.free(bindings);
                bindings = fewer;
            } else {
                supplied[idx] = true;
            }
        }
        try w.supply(supplied, false, explicit);
        return bindings;
    }

    /// `infer` from `explicit` plus the `supplied` values.
    fn inferSupplied(
        n: NodeInference,
        explicit: []const ?ExprId,
        values: []const ?ExprId,
        supplied: []const bool,
    ) ![]const ExprId {
        const given = try n.context.allocator.dupe(?ExprId, explicit);
        defer n.context.allocator.free(given);
        for (given, values, supplied) |*slot, value, use| {
            if (use) slot.* = value;
        }
        return n.infer(given);
    }

    /// `inferSupplied`, or null when it fails or lands anywhere but on the
    /// values the search chose (up to ACUI). What a failed trial interned
    /// stays in the theorem, which only a trimming check runs on and then
    /// discards.
    fn agreeingTrial(
        n: NodeInference,
        explicit: []const ?ExprId,
        values: []const ?ExprId,
        supplied: []const bool,
    ) !?[]const ExprId {
        const allocator = n.context.allocator;
        const saved_diag = getDiagnostic(n.self);
        const scratch_mark = n.context.diag_scratch.mark();
        const bindings = n.inferSupplied(explicit, values, supplied) catch |err| {
            if (err == error.OutOfMemory) return err;
            n.context.diag_scratch.discard(scratch_mark);
            restoreDiagnostic(n.self, saved_diag);
            return null;
        };
        errdefer allocator.free(bindings);
        // Inference may land on an ACUI rearrangement of the search's value,
        // which states the same line.
        var canonicalizer = Canonicalizer.init(
            allocator,
            n.theorem,
            n.context.registry,
            n.context.env,
        );
        defer canonicalizer.cache.deinit();
        for (values, 0..) |value, idx| {
            const expected = value orelse continue;
            if (idx < bindings.len) {
                if (bindings[idx] == expected) continue;
                if (try canonicalizer.canonicalize(bindings[idx]) ==
                    try canonicalizer.canonicalize(expected)) continue;
            }
            allocator.free(bindings);
            return null;
        }
        return bindings;
    }
};

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
    pins: []const ?ExprId,
) anyerror!usize {
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
        pins,
    );
    return result.full_application;
}

/// One speculative attempt, run on COW clones of the caller's theorem and
/// vars. It owns the clones and the marks needed to undo what it appended to
/// the shared checked IR and inline-conclusion sink; the caller's state is
/// untouched until `promote`. Exactly one of `abort`/`promote` must run on a
/// returned attempt (`run` aborts a failed one itself).
const SpeculativeAttempt = struct {
    allocator: std.mem.Allocator,
    checked: *std.ArrayListUnmanaged(CheckedLine),
    checked_mark: usize,
    sink: ?*InlineConclusionSink,
    sink_mark: usize,
    oracle: ?*BindingOracle,
    oracle_mark: usize,
    theorem: TheoremContext,
    theorem_vars: NameExprMap,
    line_idx: usize,

    fn run(
        self: *CompilerContext,
        context: *const RuleApplyContext,
        application: RuleApplication,
        line_assertion: LineAssertion,
        expected_conclusion_hint: ?ExprId,
        line: ApplicationLine,
        rule_id: u32,
        theorem: *const TheoremContext,
        theorem_vars: *const NameExprMap,
        pins: []const ?ExprId,
    ) anyerror!SpeculativeAttempt {
        const allocator = context.allocator;
        var attempt_theorem = try theorem.clone();
        const attempt_theorem_vars = cloneNameExprMap(
            allocator,
            theorem_vars,
        ) catch |err| {
            attempt_theorem.deinit();
            return err;
        };
        var attempt: SpeculativeAttempt = .{
            .allocator = allocator,
            .checked = context.checked,
            .checked_mark = context.checked.items.len,
            .sink = self.inline_conclusion_sink,
            .sink_mark = if (self.inline_conclusion_sink) |sink| sink.mark() else 0,
            .oracle = self.binding_oracle,
            .oracle_mark = if (self.binding_oracle) |oracle| oracle.mark() else 0,
            .theorem = attempt_theorem,
            .theorem_vars = attempt_theorem_vars,
            .line_idx = undefined,
        };
        attempt.line_idx = tryApplyRuleApplicationWithCandidate(
            self,
            context,
            application,
            line_assertion,
            expected_conclusion_hint,
            line,
            rule_id,
            &attempt.theorem,
            &attempt.theorem_vars,
            pins,
        ) catch |err| {
            attempt.abort();
            return err;
        };
        return attempt;
    }

    /// Discard everything the attempt produced.
    fn abort(attempt: *SpeculativeAttempt) void {
        CheckedIr.rollbackToMark(attempt.allocator, attempt.checked, attempt.checked_mark);
        if (attempt.sink) |sink| sink.rollback(attempt.sink_mark);
        if (attempt.oracle) |oracle| oracle.rollback(attempt.oracle_mark);
        attempt.theorem_vars.deinit();
        attempt.theorem.deinit();
        attempt.* = undefined;
    }

    /// Replace the caller's theorem and vars with the attempt's and return
    /// the produced line index. On error the attempt is aborted.
    fn promote(
        attempt: *SpeculativeAttempt,
        theorem: *TheoremContext,
        theorem_vars: *NameExprMap,
    ) !usize {
        // Materialize the COW clone before it replaces (and frees) its base.
        attempt.theorem.flatten() catch |err| {
            attempt.abort();
            return err;
        };
        const line_idx = attempt.line_idx;
        var old_theorem = theorem.*;
        theorem.* = attempt.theorem;
        old_theorem.deinit();
        theorem_vars.deinit();
        theorem_vars.* = attempt.theorem_vars;
        attempt.* = undefined;
        return line_idx;
    }
};

fn hasInlineRef(application: RuleApplication) bool {
    for (application.refs) |ref| {
        if (ref == .application) return true;
    }
    return false;
}

/// Out of line, like the other helpers on the inline recursion path (see
/// `checkStackGuard`), so its frame is not part of every level's.
noinline fn principalPinsFor(
    allocator: std.mem.Allocator,
    context: *const RuleApplyContext,
    theorem: *const TheoremContext,
    rule_id: u32,
    line_assertion: LineAssertion,
    expected_conclusion_hint: ?ExprId,
) ![][]?ExprId {
    const expected = expected_conclusion_hint orelse switch (line_assertion) {
        .concrete => |expr| expr,
        .holey, .implicit_whole_conclusion => return &.{},
    };
    const rule = &context.env.rules.items[rule_id];
    const explicit = try allocator.alloc(?ExprId, rule.args.len);
    defer allocator.free(explicit);
    @memset(explicit, null);
    return ambiguousPrincipalPins(
        allocator,
        theorem,
        context.env,
        context.registry,
        rule,
        expected,
        explicit,
    );
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
    /// Set to the index of the ref that failed, on error.
    failed_ref: *?usize,
) anyerror!void {
    const assertion = context.assertion;
    for (source_refs, 0..) |ref, idx| {
        failed_ref.* = idx;
        ref_exprs[idx] = switch (ref) {
            .hyp => |hyp| blk: {
                const resolved = ProofScript.resolveHypRef(
                    theorem.theorem_hyp_names,
                    theorem.theorem_hyps.items.len,
                    hyp,
                );
                const hyp_idx = switch (resolved) {
                    .index => |value| value,
                    .unknown, .ambiguous => return reportHypRef(
                        self,
                        assertion.name,
                        line.label,
                        hyp,
                        resolved == .ambiguous,
                    ),
                };
                refs[idx] = .{ .hyp = hyp_idx };
                break :blk theorem.theorem_hyps.items[hyp_idx];
            },
            .line => |label| blk: {
                const line_idx = context.labels.get(label.label) orelse
                    return reportUnknownLabel(self, context, line.label, label);
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
                const line_idx = try applyRuleApplication(
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
                refs[idx] = .{ .line = line_idx };
                const conclusion =
                    context.checked.items[line_idx].expr;
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

/// Report a hypothesis ref that names no hypothesis, or several. This and
/// `reportUnknownLabel` are out of line so their diagnostics are not part of
/// the `elaborateRefs` frame that stays live while inline applications
/// recurse.
noinline fn reportHypRef(
    self: *CompilerContext,
    theorem_name: []const u8,
    line_label: []const u8,
    hyp: ProofScript.HypRef,
    ambiguous: bool,
) anyerror {
    const err: CompilerDiag.DiagnosticError = if (ambiguous)
        error.AmbiguousHypothesisRef
    else
        error.UnknownHypothesisRef;
    self.setProof(CompilerDiag.withPhase(.{
        .kind = if (ambiguous)
            .ambiguous_hypothesis_ref
        else
            .unknown_hypothesis_ref,
        .err = err,
        .theorem_name = theorem_name,
        .line_label = line_label,
        .span = hyp.span,
        .detail = .{
            .hypothesis_ref = .{
                .index = hyp.index,
                .name = hyp.name,
            },
        },
    }, .theorem_application));
    return err;
}

noinline fn reportUnknownLabel(
    self: *CompilerContext,
    context: *const RuleApplyContext,
    line_label: []const u8,
    label: ProofScript.LineRef,
) anyerror {
    var label_diag = CompilerDiag.withPhase(.{
        .kind = .unknown_label,
        .err = error.UnknownLabel,
        .theorem_name = context.assertion.name,
        .line_label = line_label,
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
}

/// Record the conclusion an inline application elaborated to, rendered with
/// declared notation and source binder names, for presentation features (the
/// `unpack` code action). Fallback retries re-record the same span; the last
/// entry wins, and entries from candidates that were rolled back are
/// harmless because consumers only read the sink out of documents that
/// analyzed cleanly. No-op (and free) when no sink is configured.
/// Out of line, like the other helpers on the inline recursion path (see
/// `checkStackGuard`), so its frame is not part of every level's.
noinline fn recordInlineConclusion(
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
///     on failure), so nothing speculative is committed; the conclusion is folded
///     first, and only if that leaves the minor open are the siblings folded
///     first instead (a sibling that differs from the conclusion only up to ACUI
///     would otherwise be rolled back whole); a holey line's conclusion fold
///     reads only its hole-free parts, so `$ _wff $ by mp [#1, or_r [..]]`
///     still takes `mp`'s `a` from `#1`;
///   - bare ACUI-combiner-spine binders are demoted before instantiation, so a
///     positional context split (`g,h ⊢ …` matched member-wise) declines to
///     refine rather than emit a wrong-but-concrete hint;
///   - instantiation is strict (`instantiateTemplatePartial`): a still-open binder
///     yields null and the original hint is kept.
/// Out of line, like the other helpers on the inline recursion path (see
/// `checkStackGuard`), so its frame is not part of every level's.
noinline fn refinedInlineHint(
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
        if (!theorem.containsPlaceholder(hint)) return existing_hint;
    }

    const goal = LineGoal.of(expected_conclusion_hint, line_assertion) orelse
        return existing_hint;

    const allocator = context.allocator;
    const bindings = try allocator.alloc(?ExprId, partial_bindings.len);
    defer allocator.free(bindings);
    const snap = try allocator.alloc(?ExprId, partial_bindings.len);
    defer allocator.free(snap);

    // Conclusion first, then siblings. If a sibling disagrees with the
    // conclusion only up to ACUI (`emp , ¬a` vs `¬a` for a shared `g`), its
    // all-or-nothing fold rolls back and drops the binders only it could pin;
    // retry with the siblings first, leaving the conclusion to transport. With
    // no siblings the two orders coincide.
    const orders: []const bool = if (idx == 0) &.{true} else &.{ true, false };
    for (orders) |conclusion_first| {
        try foldGoalAndSiblings(
            theorem,
            rule,
            goal,
            partial_bindings,
            ref_exprs[0..idx],
            conclusion_first,
            bindings,
            snap,
        );

        // Drop any positional ACUI-spine commitment so a context split cannot
        // leak a wrong-but-concrete hint (the fold declines rather than guesses).
        demoteAcuiSpineBindingsForRule(context.registry, rule, partial_bindings, bindings);

        if (try OpenTerms.instantiateTemplatePartial(
            theorem,
            rule.hyps[idx],
            bindings,
        )) |refined| return refined;
    }
    return existing_hint;
}

/// `partial_bindings` plus what folding `goal` through `rule`'s conclusion
/// and each of `siblings` through its premise pins, into `bindings` (`snap`
/// is scratch of the same length).
fn foldGoalAndSiblings(
    theorem: *TheoremContext,
    rule: *const RuleDecl,
    goal: ?LineGoal,
    partial_bindings: []const ?ExprId,
    siblings: []const ExprId,
    conclusion_first: bool,
    bindings: []?ExprId,
    snap: []?ExprId,
) !void {
    @memcpy(bindings, partial_bindings);
    if (conclusion_first) if (goal) |g| try foldLineGoal(theorem, rule, g, bindings, snap);
    for (siblings, 0..) |expr, j| {
        foldTemplateOrRestore(theorem, rule.hyps[j], expr, bindings, snap);
    }
    if (!conclusion_first) if (goal) |g| try foldLineGoal(theorem, rule, g, bindings, snap);
}

/// Fold `goal` through `rule`'s conclusion all-or-nothing. A holey line fixes
/// only the binders its hole-free parts determine.
fn foldLineGoal(
    theorem: *TheoremContext,
    rule: *const RuleDecl,
    goal: LineGoal,
    bindings: []?ExprId,
    snap: []?ExprId,
) !void {
    switch (goal) {
        .expr => |expr| foldTemplateOrRestore(theorem, rule.concl, expr, bindings, snap),
        .holey => |holey| _ = try Holes.foldTemplateToSurface(theorem, rule.concl, holey.surface, bindings, snap),
    }
}

fn refSpan(ref: Ref) Span {
    return switch (ref) {
        .hyp => |hyp| hyp.span,
        .line => |line| line.span,
        .application => |application| application.span,
    };
}
