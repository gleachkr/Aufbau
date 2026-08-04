const std = @import("std");
const Span = @import("../proof_script.zig").Span;
const ProofScriptParser = @import("../proof_script.zig").Parser;
const GlobalEnv = @import("../env.zig").GlobalEnv;
const DiagScratch = @import("../diag_scratch.zig");
const MathParseError = @import("../parse_recovery.zig").MathParseError;
const MathSpan = @import("../parse_recovery.zig").MathSpan;
const MM0Parser = @import("../parse_recovery.zig").MM0Parser;
const MM0Stmt = @import("../parse_recovery.zig").MM0Stmt;

pub const DiagnosticKind = enum {
    generic,
    omitted_diagnostics,
    missing_proof_block,
    extra_proof_block,
    extra_proof_def,
    theorem_name_mismatch,
    missing_public_def_body,
    public_def_body_name_mismatch,
    public_def_body_header,
    unexpected_proof_def,
    unsupported_proof_def_annotation,
    duplicate_rule_name,
    parse_assertion,
    parse_binding,
    parse_fresh,
    inference_failed,
    unknown_rule,
    unresolved_search_placeholder,
    rule_not_yet_available,
    unknown_binder_name,
    duplicate_binder_assignment,
    missing_binder_assignment,
    ref_count_mismatch,
    unknown_hypothesis_ref,
    ambiguous_hypothesis_ref,
    unknown_label,
    hypothesis_mismatch,
    conclusion_mismatch,
    duplicate_label,
    empty_proof_block,
    final_line_mismatch,
    invalid_definition_body,
    unused_theorem_parameter,
    unused_definition_parameter,
};

pub const Scratch = DiagScratch.Scratch;
pub const MissingCongruenceReason = DiagScratch.MissingCongruenceReason;

pub const MissingCongruenceRuleDetail = struct {
    reason: MissingCongruenceReason,
    term_name: ?[]const u8 = null,
    sort_name: ?[]const u8 = null,
    arg_index: ?usize = null,
};

pub const DepViolationDiagnosticDetail = struct {
    first_arg_idx: usize,
    second_arg_idx: usize,
    first_arg_name: ?[]const u8 = null,
    second_arg_name: ?[]const u8 = null,
    first_deps: u55,
    second_deps: u55,
    first_bound: bool,
    second_bound: bool,
    /// Whether the rule declares each argument as a bound binder ({x} vs
    /// (p)). Distinguishes the two violation shapes: a bound binder's
    /// variable occurring where the rule forbids it (exactly one side
    /// bound) vs two bound binders assigned the same variable (both
    /// bound). False/false means the construction path predates this
    /// field; renderers fall back to the generic wording.
    first_rule_bound: bool = false,
    second_rule_bound: bool = false,
    /// Notation-rendered assigned expressions (truncated), for showing the
    /// student what each conflicting argument actually received. Null when
    /// rendering failed or the argument was not yet assigned.
    first_binding_text: ?[]const u8 = null,
    second_binding_text: ?[]const u8 = null,
};

pub const InferencePath = enum {
    strict_replay,
    transparent_fallback,
    normalized_session_fallback,
    structural_solver,
    holey_surface_match,
};

pub const InferenceDiagnosticDetail = struct {
    path: InferencePath,
    first_unsolved_binder_name: ?[]const u8 = null,
};

pub const DefinitionBodyDiagnosticDetail = struct {
    declared_sort_name: []const u8,
    actual_sort_name: []const u8,
    body_deps: u55,
    hidden_binder_count: usize,
};

pub const DiagnosticDetail = union(enum) {
    none,
    omitted_diagnostics: struct {
        count: usize,
    },
    unknown_math_token: struct {
        token: []const u8,
    },
    missing_binder_assignment: struct {
        binder_name: []const u8,
        path: InferencePath = .strict_replay,
    },
    inference_failure: InferenceDiagnosticDetail,
    dep_violation: DepViolationDiagnosticDetail,
    definition_body: DefinitionBodyDiagnosticDetail,
    missing_congruence_rule: MissingCongruenceRuleDetail,
    hypothesis_ref: struct {
        index: usize,
        /// Set when the reference was written by name (`#h`).
        name: ?[]const u8 = null,
    },
    unused_parameter: struct {
        parameter_name: []const u8,
    },
    /// A close-by known name for an unknown rule or line-label reference.
    /// The slice must outlive the diagnostic (rule/label names stored in
    /// the environment or proof script satisfy this).
    name_suggestion: struct {
        suggestion: []const u8,
    },
};

pub const DiagnosticSource = enum {
    mm0,
    proof,
};

pub const DiagnosticSeverity = enum {
    @"error",
    warning,
};

pub const DiagnosticPhase = enum {
    parse,
    inference,
    theorem_application,
    freshen,
    normalization,
    final_reconciliation,
};

pub const max_diagnostic_notes = 8;
pub const max_diagnostic_related = 4;

pub const DiagnosticNote = struct {
    message: []const u8,
    source: DiagnosticSource,
    span: ?Span = null,
};

pub const DiagnosticRelated = struct {
    label: []const u8,
    source: DiagnosticSource,
    span: Span,
};

pub const Diagnostic = struct {
    severity: DiagnosticSeverity = .@"error",
    kind: DiagnosticKind,
    err: anyerror,
    source: DiagnosticSource = .mm0,
    phase: ?DiagnosticPhase = null,
    theorem_name: ?[]const u8 = null,
    block_name: ?[]const u8 = null,
    line_label: ?[]const u8 = null,
    rule_name: ?[]const u8 = null,
    name: ?[]const u8 = null,
    expected_name: ?[]const u8 = null,
    span: ?Span = null,
    detail: DiagnosticDetail = .none,
    note_count: u8 = 0,
    notes: [max_diagnostic_notes]DiagnosticNote = undefined,
    related_count: u8 = 0,
    related: [max_diagnostic_related]DiagnosticRelated = undefined,

    pub fn noteSlice(self: *const Diagnostic) []const DiagnosticNote {
        return self.notes[0..self.note_count];
    }

    pub fn relatedSlice(self: *const Diagnostic) []const DiagnosticRelated {
        return self.related[0..self.related_count];
    }
};

pub fn setPhase(diag: *Diagnostic, phase: DiagnosticPhase) void {
    diag.phase = phase;
}

pub fn withPhase(diag: Diagnostic, phase: DiagnosticPhase) Diagnostic {
    var result = diag;
    result.phase = phase;
    return result;
}

pub fn addNote(
    diag: *Diagnostic,
    message: []const u8,
    source: DiagnosticSource,
    span: ?Span,
) void {
    if (diag.note_count >= max_diagnostic_notes) return;
    diag.notes[diag.note_count] = .{
        .message = message,
        .source = source,
        .span = span,
    };
    diag.note_count += 1;
}

pub fn addRelated(
    diag: *Diagnostic,
    label: []const u8,
    source: DiagnosticSource,
    span: Span,
) void {
    if (diag.related_count >= max_diagnostic_related) return;
    diag.related[diag.related_count] = .{
        .label = label,
        .source = source,
        .span = span,
    };
    diag.related_count += 1;
}

pub fn inferencePathName(path: InferencePath) []const u8 {
    return switch (path) {
        .strict_replay => "exact match",
        .transparent_fallback => "matching with definitions unfolded",
        .normalized_session_fallback => "matching after normalization",
        .structural_solver => "structural matching",
        .holey_surface_match => "holey assertion match",
    };
}

pub fn diagnosticPhaseName(phase: DiagnosticPhase) []const u8 {
    return switch (phase) {
        .parse => "parse",
        .inference => "inference",
        .theorem_application => "theorem application",
        .freshen => "freshen",
        .normalization => "normalization",
        .final_reconciliation => "final reconciliation",
    };
}

pub fn mathSpanToSpan(span: MathSpan) Span {
    return .{ .start = span.start, .end = span.end };
}

pub fn mathSpanToSpanOpt(span: ?MathSpan) ?Span {
    return if (span) |value| mathSpanToSpan(value) else null;
}

pub fn mm0ParserDiagnostic(
    parser: *const MM0Parser,
    err: anyerror,
) Diagnostic {
    const diag = Diagnostic{
        .kind = .generic,
        .err = err,
        .source = .mm0,
        .name = parser.diagnosticName(),
        .span = mathSpanToSpanOpt(parser.diagnosticSpan()),
    };
    return mathErrorDiagnostic(diag, err, parser.mathError());
}

pub fn mm0StatementDiagnostic(
    parser: *const MM0Parser,
    stmt: MM0Stmt,
    err: anyerror,
) Diagnostic {
    return .{
        .kind = .generic,
        .err = err,
        .source = .mm0,
        .name = mm0StmtName(stmt),
        .span = annotationDiagnosticSpan(parser, stmt, err) orelse
            mm0StmtNameSpan(stmt),
    };
}

pub fn proofParserDiagnostic(
    proofs: *const ProofScriptParser,
    fallback_theorem_name: ?[]const u8,
    err: anyerror,
) Diagnostic {
    return .{
        .kind = .generic,
        .err = err,
        .source = .proof,
        .theorem_name = proofs.diagnosticBlockName() orelse
            fallback_theorem_name,
        .block_name = proofs.diagnosticBlockName(),
        .span = proofs.diagnosticSpan(),
    };
}

pub fn extraProofBlockDiagnostic(
    block_name: []const u8,
    span: Span,
) Diagnostic {
    return .{
        .kind = .extra_proof_block,
        .err = error.ExtraProofBlock,
        .source = .proof,
        .block_name = block_name,
        .span = span,
    };
}

pub fn missingProofBlockDiagnostic(
    theorem_name: []const u8,
    span: Span,
) Diagnostic {
    return .{
        .kind = .missing_proof_block,
        .err = error.MissingProofBlock,
        .source = .mm0,
        .theorem_name = theorem_name,
        .span = span,
    };
}

pub fn extraProofDefDiagnostic(
    name: []const u8,
    span: Span,
) Diagnostic {
    return .{
        .kind = .extra_proof_def,
        .err = error.ExtraProofItem,
        .source = .proof,
        .name = name,
        .span = span,
    };
}

pub fn theoremNameMismatchDiagnostic(
    theorem_name: []const u8,
    block_name: []const u8,
    span: Span,
) Diagnostic {
    return .{
        .kind = .theorem_name_mismatch,
        .err = error.TheoremNameMismatch,
        .source = .proof,
        .theorem_name = theorem_name,
        .block_name = block_name,
        .expected_name = theorem_name,
        .span = span,
    };
}

pub fn missingPublicDefBodyDiagnostic(
    name: []const u8,
    span: Span,
) Diagnostic {
    return .{
        .kind = .missing_public_def_body,
        .err = error.MissingPublicDefBody,
        .source = .mm0,
        .name = name,
        .span = span,
    };
}

pub fn publicDefBodyNameMismatchDiagnostic(
    expected_name: []const u8,
    actual_name: []const u8,
    span: Span,
) Diagnostic {
    return .{
        .kind = .public_def_body_name_mismatch,
        .err = error.PublicDefBodyNameMismatch,
        .source = .proof,
        .name = actual_name,
        .expected_name = expected_name,
        .span = span,
    };
}

pub fn publicDefBodyHeaderDiagnostic(
    name: []const u8,
    span: Span,
) Diagnostic {
    return .{
        .kind = .public_def_body_header,
        .err = error.PublicDefBodyMustBeHeaderless,
        .source = .proof,
        .name = name,
        .span = span,
    };
}

pub fn unexpectedProofDefDiagnostic(
    name: []const u8,
    span: Span,
) Diagnostic {
    return .{
        .kind = .unexpected_proof_def,
        .err = error.UnexpectedProofDefItem,
        .source = .proof,
        .name = name,
        .span = span,
    };
}

pub fn unsupportedProofDefAnnotationDiagnostic(
    name: []const u8,
    span: Span,
) Diagnostic {
    return .{
        .kind = .unsupported_proof_def_annotation,
        .err = error.UnsupportedProofDefAnnotation,
        .source = .proof,
        .name = name,
        .span = span,
    };
}

pub fn duplicateRuleNameDiagnostic(
    name: []const u8,
    span: ?Span,
    source: DiagnosticSource,
) Diagnostic {
    return .{
        .kind = .duplicate_rule_name,
        .err = error.DuplicateRuleName,
        .source = source,
        .name = name,
        .span = span,
    };
}

pub fn theoremDiagnostic(
    theorem_name: []const u8,
    span: Span,
    source: DiagnosticSource,
    err: anyerror,
) Diagnostic {
    return .{
        .kind = .generic,
        .err = err,
        .source = source,
        .theorem_name = theorem_name,
        .span = span,
    };
}

pub fn proofBlockDiagnostic(
    block_name: []const u8,
    span: Span,
    err: anyerror,
) Diagnostic {
    return .{
        .kind = .generic,
        .err = err,
        .source = .proof,
        .theorem_name = block_name,
        .block_name = block_name,
        .span = span,
    };
}

pub fn proofMathTokenSpan(math_span: Span, token_span: MathSpan) Span {
    const inner_start = math_span.start + 1;
    return .{
        .start = inner_start + token_span.start,
        .end = inner_start + token_span.end,
    };
}

pub fn proofMathParseDiagnostic(
    parser: *MM0Parser,
    kind: DiagnosticKind,
    err: anyerror,
    theorem_name: []const u8,
    line_label: []const u8,
    rule_name: []const u8,
    name: ?[]const u8,
    math_span: Span,
) Diagnostic {
    var diag = Diagnostic{
        .kind = kind,
        .err = err,
        .source = .proof,
        .theorem_name = theorem_name,
        .line_label = line_label,
        .rule_name = rule_name,
        .name = name,
        .span = math_span,
    };
    setPhase(&diag, .parse);
    const math_err = parser.mathError() orelse return diag;
    return proofMathErrorDiagnostic(diag, math_err, math_span);
}

pub fn proofBindingDiagnosticSpan(
    line: anytype,
    binder_name: ?[]const u8,
) Span {
    return line.application.bindingSpan(binder_name) orelse
        line.application.ruleApplicationSpan();
}

fn proofMathErrorDiagnostic(
    diag: Diagnostic,
    math_err: MathParseError,
    math_span: Span,
) Diagnostic {
    var result = mathErrorDiagnostic(diag, diag.err, math_err);
    switch (math_err) {
        .unknown_token, .unexpected_token => |token| {
            result.span = proofMathTokenSpan(math_span, token.span);
        },
        .unexpected_end => |pos| {
            const start = @min(math_span.start + pos, math_span.end);
            result.span = .{ .start = start, .end = start };
        },
    }
    return result;
}

fn mathErrorDiagnostic(
    diag: Diagnostic,
    err: anyerror,
    math_err: ?MathParseError,
) Diagnostic {
    if (err != error.UnknownMathToken) return diag;
    const actual = math_err orelse return diag;

    var result = diag;
    switch (actual) {
        .unknown_token => |token| {
            result.detail = .{
                .unknown_math_token = .{
                    .token = token.text,
                },
            };
        },
        .unexpected_token,
        .unexpected_end,
        => {},
    }
    return result;
}

fn mm0StmtName(stmt: MM0Stmt) ?[]const u8 {
    return switch (stmt) {
        .sort => |sort_stmt| sort_stmt.name,
        .term => |term_stmt| term_stmt.name,
        .assertion => |assertion| assertion.name,
    };
}

fn mm0StmtNameSpan(stmt: MM0Stmt) Span {
    return switch (stmt) {
        .sort => |sort_stmt| mathSpanToSpan(sort_stmt.name_span),
        .term => |term_stmt| mathSpanToSpan(term_stmt.name_span),
        .assertion => |assertion| mathSpanToSpan(assertion.name_span),
    };
}

fn firstAnnotationSpan(parser: *const MM0Parser) ?Span {
    if (parser.last_annotation_spans.len == 0) return null;
    return mathSpanToSpan(parser.last_annotation_spans[0]);
}

fn annotationDirective(ann: []const u8) ?[]const u8 {
    if (ann.len == 0 or ann[0] != '@') return null;

    var iter = std.mem.tokenizeAny(u8, ann, " \t\r\n");
    return iter.next();
}

fn unknownTermAnnotationSpan(parser: *const MM0Parser) ?Span {
    for (parser.last_annotations, parser.last_annotation_spans) |ann, span| {
        const directive = annotationDirective(ann) orelse continue;
        if (std.mem.eql(u8, directive, "@acui")) continue;
        if (std.mem.eql(u8, directive, "@conversion")) continue;
        return mathSpanToSpan(span);
    }
    return firstAnnotationSpan(parser);
}

fn annotationDiagnosticSpan(
    parser: *const MM0Parser,
    stmt: MM0Stmt,
    err: anyerror,
) ?Span {
    return switch (err) {
        error.UnknownTermAnnotation => switch (stmt) {
            .term => unknownTermAnnotationSpan(parser),
            else => firstAnnotationSpan(parser),
        },
        error.DummyAnnotationRemoved,
        error.InvalidFreshAnnotation,
        error.InvalidFreshenAnnotation,
        error.InvalidAlphaAnnotation,
        error.InvalidCongruenceAnnotation,
        error.CongruenceBinderOrderMismatch,
        error.CongruenceBinderMissingDeps,
        error.RelationBundleBoundBinder,
        error.InvalidConversionAnnotation,
        error.InvalidDefConversionAnnotation,
        error.ConversionTermNotDef,
        error.ConversionDefUnfoldHiddenDummies,
        error.DuplicateConversionAnnotation,
        error.ConversionRuleHasHypotheses,
        error.ConversionConclusionNotRelation,
        error.ConversionMissingRelation,
        error.ConversionBareMatchSide,
        error.ConversionBinderNotCovered,
        error.ConversionCommRuleShape,
        error.ConversionAssocRuleShape,
        error.ConversionRoleBoundBinder,
        error.ConversionRoleRelationHead,
        error.DuplicateConversionRoleForHead,
        error.InvalidComputeAnnotation,
        error.DuplicateComputeAnnotation,
        error.ComputeRuleHasHypotheses,
        error.ComputeConclusionNotRelation,
        error.ComputeMissingRelation,
        error.ComputeBareMatchSide,
        error.ComputeBinderNotCovered,
        error.InvalidFallbackAnnotation,
        error.DuplicateFallbackAnnotation,
        error.UnknownFallbackRule,
        error.InvalidAutoAnnotation,
        error.EagerRuleDefersWitness,
        error.UnknownFreshBinder,
        error.UnknownFreshenBinder,
        error.UnknownAlphaBinder,
        error.DuplicateFreshBinder,
        error.DuplicateFreshenPair,
        error.FreshRequiresBoundBinder,
        error.FreshenTargetMustBeRegularBinder,
        error.FreshenBlockerMustBeBoundBinder,
        error.AlphaRequiresBoundBinders,
        error.AlphaSortMismatch,
        error.AlphaConclusionMustBeBinaryRelation,
        error.AlphaConclusionUnsupported,
        error.AlphaRuleHasHypotheses,
        error.FreshStrictSort,
        error.FreshFreeSort,
        error.FreshNoAvailableVar,
        error.HiddenWitnessNoAvailableVar,
        error.NoAlphaRewriteAvailable,
        error.AlphaRewriteSearchFailed,
        error.FreshenMissingRelation,
        error.FreshenTransportFailed,
        error.DuplicateViewAnnotation,
        error.InvalidViewAnnotation,
        error.ViewHypCountMismatch,
        error.RecoverWithoutView,
        error.InvalidRecoverAnnotation,
        error.UnknownRecoverBinder,
        error.RecoverTargetNotRuleBinder,
        error.RecoverSortMismatch,
        error.AbstractWithoutView,
        error.InvalidAbstractAnnotation,
        error.UnknownAbstractBinder,
        error.AbstractTargetNotRuleBinder,
        error.AbstractPlugSortMismatch,
        error.InvalidVarsAnnotation,
        error.VarsStrictSort,
        error.VarsFreeSort,
        error.DuplicateVarsToken,
        error.VarsTokenCollision,
        error.InvalidHoleAnnotation,
        error.DuplicateHoleAnnotation,
        error.DuplicateHoleToken,
        => firstAnnotationSpan(parser),
        else => null,
    };
}

pub fn diagnosticSummary(diag: Diagnostic) []const u8 {
    return switch (diag.kind) {
        .generic => compilerErrorSummary(diag.err),
        .omitted_diagnostics => "additional diagnostics omitted",
        .missing_proof_block => "missing proof block for theorem",
        .extra_proof_block => "extra proof block with no matching theorem",
        .extra_proof_def => "extra proof-side definition item",
        .theorem_name_mismatch => "proof block name does not match the theorem",
        .missing_public_def_body => "missing proof-side body for public definition",
        .public_def_body_name_mismatch => "proof-side definition body targets a different public definition",
        .public_def_body_header => "public definition body filler must not redeclare the signature (only dummy binders are allowed)",
        .unexpected_proof_def => "unexpected proof-side definition item",
        .unsupported_proof_def_annotation => "proof-side definition annotations are not supported yet",
        .duplicate_rule_name => "duplicate rule name",
        .parse_assertion => "could not parse proof line assertion",
        .parse_binding => "could not parse binder assignment",
        .parse_fresh => compilerErrorSummary(diag.err),
        .inference_failed => compilerErrorSummary(diag.err),
        .unknown_rule => "unknown rule in proof line",
        .unresolved_search_placeholder => "proof line is justified by a search placeholder, not a completed proof",
        .rule_not_yet_available => "rule is declared later and is not yet available here",
        .unknown_binder_name => "unknown binder name in rule application",
        .duplicate_binder_assignment => "duplicate binder assignment in rule application",
        .missing_binder_assignment => "one of the rule's variables could not " ++
            "be determined from the statement and cited premises",
        .ref_count_mismatch => "wrong number of references for rule application",
        .unknown_hypothesis_ref => "unknown theorem hypothesis reference",
        .ambiguous_hypothesis_ref => "hypothesis name matches more than one hypothesis",
        .unknown_label => "unknown proof line label",
        .hypothesis_mismatch => "a cited premise does not match the hypothesis the rule expects there",
        .conclusion_mismatch => if (diag.err == error.HoleConclusionMismatch)
            compilerErrorSummary(diag.err)
        else
            "proof line assertion does not match the rule conclusion",
        .duplicate_label => "duplicate proof line label",
        .empty_proof_block => "proof block is empty",
        .final_line_mismatch => "last proof line does not prove the theorem conclusion",
        .invalid_definition_body => definitionBodySummary(diag.err),
        .unused_theorem_parameter => "theorem parameter is unused; if it is only needed during proofs, use @vars and an explicit theorem-local dummy instead",
        .unused_definition_parameter => "definition parameter is unused; remove it if it is not part of the definition",
    };
}

fn definitionBodySummary(err: anyerror) []const u8 {
    return switch (err) {
        error.DepViolation => "definition body has free variables that the result type does not declare",
        error.SortMismatch => "definition body sort does not match the declared result sort",
        else => "definition body does not satisfy the declared result",
    };
}

fn compilerErrorSummary(err: anyerror) []const u8 {
    return switch (err) {
        error.BoundnessMismatch => "binding does not satisfy the rule's " ++
            "bound-variable constraint",
        error.SortMismatch => "binding does not satisfy the rule's sort constraint",
        error.UnifyMismatch,
        error.UnifyStackNotEmpty,
        => "the statement and cited premises could not be matched " ++
            "against this rule",
        error.TermMismatch,
        error.ExpectedTermApp,
        => "the statement or a cited premise does not have the shape " ++
            "this rule requires",
        error.HypCountMismatch => "the number of cited premises does not " ++
            "match the number of hypotheses this rule has",
        error.HoleTokenNameCollision => "name conflicts with a proof hole token",
        error.BinderTokenCollision => "binder name conflicts with a declared notation token",
        error.ResultDependencyOnDummy => "a result type may only depend on " ++
            "bound variables from the argument list, not hidden binders",
        error.HoleyInferenceMismatch => "the visible parts of the statement " ++
            "do not match what this rule proves",
        error.HoleConclusionMismatch => "the visible parts of the statement " ++
            "do not match the rule's conclusion",
        // Legacy public error name. The repaired structural solver uses
        // this for ambiguity across AU, ACU, AUI, and ACUI matching.
        error.AmbiguousAcuiMatch => "the omitted parts of this rule " ++
            "application can be completed in more than one way",
        error.RuleNotYetAvailable => "rule is declared later and is not yet available here",
        error.UnknownTheoremVariable => "binding refers to a theorem variable that is not in scope",
        error.DuplicateRuleName => "duplicate rule name",
        error.DuplicateViewAnnotation => "multiple @view annotations were attached to one rule",
        error.InvalidViewAnnotation => "could not parse @view annotation",
        error.ViewHypCountMismatch => "@view hypothesis count does not match the rule",
        error.ViewConclusionMismatch => "@view conclusion does not match the proof line assertion",
        error.ViewHypothesisMismatch => "@view hypotheses do not match the cited refs",
        error.ViewBindingConflict => "@view inference conflicts with an explicit binding",
        error.RecoverWithoutView => "@recover requires a preceding @view on the same rule",
        error.InvalidRecoverAnnotation => "@recover expects four binder names: target source " ++
            "pattern hole",
        error.UnknownRecoverBinder => "@recover refers to a binder name not present in the view",
        error.RecoverTargetNotRuleBinder => "@recover target must be a real rule binder",
        error.RecoverSortMismatch => "@recover target and hole binders must have the same sort",
        error.RecoverHoleNotFound => "@recover could not find the hole binder in the pattern expr",
        error.RecoverConflict => "@recover found inconsistent candidates for the target " ++
            "binder",
        error.RecoverStructureMismatch => "@recover source expr does not match the pattern structure",
        error.AbstractWithoutView => "@abstract requires a preceding @view on the same rule",
        error.InvalidAbstractAnnotation => "@abstract expects six binder names: target left " ++
            "right hole left_plug right_plug",
        error.UnknownAbstractBinder => "@abstract refers to a binder name not present in the view",
        error.AbstractTargetNotRuleBinder => "@abstract target must be a real rule binder",
        error.AbstractPlugSortMismatch => "@abstract hole and plug binders must have the same sort",
        error.AbstractNoPlugOccurrence => "@abstract could not find the plug pair in the source exprs",
        error.AbstractConflict => "@abstract found a context that conflicts with the target binder",
        error.AbstractStructureMismatch => "@abstract source exprs do not match outside the plug pair",
        error.UnknownTermAnnotation => "unknown term-level annotation",
        error.DummyAnnotationRemoved => "@dummy was removed; use @fresh instead",
        error.InvalidFreshAnnotation => "@fresh expects exactly one real rule binder name",
        error.InvalidFreshenAnnotation => "@freshen expects two binder names: target blocker",
        error.InvalidAlphaAnnotation => "@alpha expects two bound binder names: old new",
        error.InvalidFallbackAnnotation => "@fallback expects exactly one rule name",
        error.DuplicateFallbackAnnotation => "multiple @fallback annotations were attached to one rule",
        error.UnknownFallbackRule => "@fallback refers to a rule that is not available here",
        error.InvalidAutoAnnotation => "@auto expects one mode: forward, backward, " ++
            "eager [PRIORITY >= 1], or trigger PATTERN",
        error.EagerRuleDefersWitness => "@auto eager rule must not defer a witness: " ++
            "every hypothesis binder must appear in the conclusion",
        error.InvalidTriggerAnnotation => "@auto trigger expects one parenthesized prefix " ++
            "pattern: (term binder-or-_ ...)",
        error.UnknownTriggerTerm => "@auto trigger names a term that is not available here",
        error.UnknownTriggerBinder => "@auto trigger refers to a binder that is not on the rule",
        error.TriggerRuleHasHypotheses => "@auto trigger rule must not have hypotheses",
        error.TriggerBinderNotGround => "@auto trigger must name every rule binder that cannot " ++
            "default to an ACUI unit",
        error.TriggerSortMismatch => "@auto trigger pattern position has the wrong sort",
        error.TriggerBoundPosition => "@auto trigger bound argument positions admit only _",
        error.FallbackCycle => "@fallback chain contains a cycle",
        error.UnknownFreshBinder => "@fresh target must be a real rule binder",
        error.UnknownFreshenBinder => "@freshen refers to a binder that is not on the rule",
        error.UnknownAlphaBinder => "@alpha refers to a binder that is not on the rule",
        error.DuplicateFreshBinder => "multiple @fresh annotations were attached to one rule binder",
        error.DuplicateFreshenPair => "multiple identical @freshen annotations were attached to one rule",
        error.FreshRequiresBoundBinder => "@fresh target must be a bound rule binder",
        error.FreshenTargetMustBeRegularBinder => "@freshen target must be a regular rule binder",
        error.FreshenBlockerMustBeBoundBinder => "@freshen blocker must be a bound rule binder",
        error.AlphaRequiresBoundBinders => "@alpha binders must both be bound rule binders",
        error.AlphaSortMismatch => "@alpha binders must have the same sort",
        error.AlphaConclusionMustBeBinaryRelation => "@alpha rule conclusion must be a binary relation",
        error.AlphaConclusionUnsupported => "@alpha rule left-hand side must be a term application",
        error.AlphaRuleHasHypotheses => "@alpha rule must not have hypotheses",
        error.InvalidCongruenceAnnotation => "@congr rule does not have the expected congruence shape",
        error.CongruenceBinderOrderMismatch => "@congr binders must be ordered old₀ new₀ old₁ new₁ ...",
        error.CongruenceBinderMissingDeps => "@congr old/new binders must declare every dependency " ++
            "the head term's argument permits (e.g. (p q: wff x))",
        error.RelationBundleBoundBinder => "@relation bundle rules (refl/trans/symm/transport) " ++
            "must not have bound binders",
        error.InvalidConversionAnnotation => "@conversion expects one token: " ++
            "ltr, rtl, both, assoc, or comm",
        error.InvalidDefConversionAnnotation => "@conversion on a definition expects one " ++
            "token: unfold, fold, or both",
        error.ConversionTermNotDef => "@conversion on a term requires a definition " ++
            "with a visible definiens",
        error.ConversionDefUnfoldHiddenDummies => "@conversion unfold/both cannot enroll a " ++
            "definition with hidden dummy binders: unfolding would have to " ++
            "invent a dummy witness at every match; only fold is legal here",
        error.DuplicateConversionAnnotation => "multiple @conversion annotations were attached to one rule",
        error.ConversionRuleHasHypotheses => "@conversion rule must not have hypotheses",
        error.ConversionCommRuleShape => "@conversion comm requires the conclusion " ++
            "rel(t(a, b), t(b, a)) over exactly two distinct binders",
        error.ConversionAssocRuleShape => "@conversion assoc requires the conclusion " ++
            "rel(t(t(a, b), c), t(a, t(b, c))) (either orientation) over " ++
            "exactly three distinct binders",
        error.ConversionRoleBoundBinder => "@conversion assoc/comm rules must not have bound binders",
        error.ConversionRoleRelationHead => "@conversion assoc/comm cannot certify a registered " ++
            "@relation term: relation applications must stay plain so local " ++
            "equations can be cited directly",
        error.DuplicateConversionRoleForHead => "another @conversion rule already certifies " ++
            "this law for the same operator",
        error.ConversionConclusionNotRelation => "@conversion rule conclusion must have the shape " ++
            "rel(lhs, rhs)",
        error.ConversionMissingRelation => "@conversion rule conclusion head must be the registered " ++
            "@relation term for its operand sort",
        error.ConversionBareMatchSide => "@conversion match side must be a term application, " ++
            "not a bare binder",
        error.ConversionBinderNotCovered => "@conversion match side must bind every binder " ++
            "the instantiate side uses",
        error.InvalidComputeAnnotation => "@compute expects one token: ltr or rtl",
        error.DuplicateComputeAnnotation => "this rule is already enrolled for conversion? " ++
            "(one @compute/@conversion enrollment per rule)",
        error.ComputeRuleHasHypotheses => "@compute rule must not have hypotheses",
        error.ComputeConclusionNotRelation => "@compute rule conclusion must have the shape " ++
            "rel(lhs, rhs)",
        error.ComputeMissingRelation => "@compute rule conclusion head must be the registered " ++
            "@relation term for its operand sort",
        error.ComputeBareMatchSide => "@compute match side must be a term application, " ++
            "not a bare binder",
        error.ComputeBinderNotCovered => "@compute match side must bind every binder " ++
            "the instantiate side uses",
        error.FreshStrictSort => "@fresh cannot target a binder in a strict sort",
        error.FreshFreeSort => "@fresh cannot target a binder in a free sort",
        error.FreshNoAvailableVar => "@fresh could not find an available @vars token",
        error.HiddenWitnessNoAvailableVar => "hidden def witness needed a fresh @vars token, but none was " ++
            "available",
        error.NoAlphaRewriteAvailable => "no matching @alpha rule was available for this @freshen step",
        error.AlphaRewriteSearchFailed => "the available @alpha rules did not remove the blocker dependency",
        error.DepViolation => "binder assignments violate the rule's dependency constraints",
        error.FreshenMissingRelation => "freshening needs a registered relation on the affected sort",
        error.FreshenTransportFailed => "freshening could not lift the alpha rewrite through the rule formula",
        error.InvalidHoleAnnotation => "@hole expects exactly one raw math token",
        error.DuplicateHoleAnnotation => "multiple @hole annotations were attached to one sort",
        error.DuplicateHoleToken => "duplicate @hole token across sorts",
        error.InvalidVarsAnnotation => "@vars expects one or more raw math tokens",
        error.VarsStrictSort => "@vars cannot be used on a strict sort",
        error.VarsFreeSort => "@vars cannot be used on a free sort",
        error.DuplicateVarsToken => "duplicate @vars token across sorts",
        error.VarsTokenCollision => "@vars token collides with an existing term, notation, " ++
            "or formula marker",
        error.DependencySlotExhausted => "theorem exceeded the 55 tracked bound-variable dependency slots",
        error.UnresolvedDummyWitness => "matched rule through hidden def structure, but omitted " ++
            "binders contain unresolved hidden-dummy witnesses",
        error.MissingCongruenceRule => "missing congruence rule needed for normalization",
        error.ExpectedIdentifier,
        error.ExpectedIdent,
        => "expected identifier",
        error.ExpectedNumber => "expected number",
        error.UnknownMathToken => "unknown token in math string",
        error.ExpectedMathToken => "expected token in math string",
        error.ExpectedCloseParen => "expected closing parenthesis in math string",
        error.TrailingMathTokens => "unexpected trailing tokens in math string",
        error.NotationMismatch => "token sequence does not match declared notation",
        error.AnonymousNotationBinder => "anonymous binders are not permitted in notation declarations",
        error.DummyNotationBinder => "dummy binders are not permitted in notation declarations",
        error.InvalidNotationVariables => "notation must mention each declared argument exactly once",
        error.PrecMismatch => "operator precedence does not allow this parse",
        error.NotProvable => "math string does not have a provable sort",
        error.ExpectedMathString,
        error.ExpectedMathStr,
        => "expected $...$ math string",
        error.MissingPublicDefBody => "missing proof-side body for public definition",
        error.PublicDefBodyNameMismatch => "proof-side definition body targets a different public definition",
        error.PublicDefBodyMustBeHeaderless => "public definition body filler may declare only dummy binders before `=`",
        error.FillerBinderMustBeDummy => "public definition body filler binders must be hidden dummies like (.x: s)",
        error.DuplicateFillerBinderName => "filler dummy name is already bound by the definition",
        error.TooManyBoundVars => "too many bound variables",
        error.UnexpectedProofDefItem => "unexpected proof-side definition item",
        error.UnsupportedProofDefAnnotation => "proof-side definition annotations are not supported yet",
        error.ExtraProofItem => "extra proof item with no matching declaration",
        error.ExpectedBy => "expected 'by' after the proof line's statement",
        error.ExpectedKeyword => "expected keyword",
        error.ExpectedString => "expected quoted string",
        error.UnknownTerm => "unknown term",
        error.UnknownSort => "unknown sort",
        error.UnknownVariable => "unknown variable",
        error.UnexpectedKeyword => "unexpected keyword",
        error.UnexpectedCharacter,
        error.UnexpectedChar,
        => "unexpected character",
        error.ExpectedLineEnd => "expected end of line",
        error.ExpectedBlockUnderline => "expected underline after proof block header",
        error.UnterminatedMathString,
        error.UnterminatedMathStr,
        => "unterminated $...$ math string",
        error.UnterminatedString => "unterminated string",
        else => @errorName(err),
    };
}

pub fn writeMissingCongruenceRuleSummary(
    writer: anytype,
    info: MissingCongruenceRuleDetail,
) !void {
    switch (info.reason) {
        .missing_rule => {
            if (info.term_name) |term_name| {
                try writer.print(
                    "missing @congr for term {s}",
                    .{term_name},
                );
            } else {
                try writer.writeAll("missing @congr rule");
            }
        },
        .changed_bound_arg => {
            if (info.arg_index) |arg_index| {
                if (info.term_name) |term_name| {
                    try writer.print(
                        "bound argument {d} of term {s} changed " ++
                            "during normalization",
                        .{ arg_index + 1, term_name },
                    );
                } else {
                    try writer.print(
                        "bound argument {d} changed during normalization",
                        .{arg_index + 1},
                    );
                }
            } else {
                try writer.writeAll(
                    "bound argument changed during normalization",
                );
            }
        },
        .missing_child_relation => {
            if (info.arg_index) |arg_index| {
                if (info.term_name) |term_name| {
                    try writer.print(
                        "missing relation for argument {d} of term {s}",
                        .{ arg_index + 1, term_name },
                    );
                } else {
                    try writer.print(
                        "missing relation for argument {d}",
                        .{arg_index + 1},
                    );
                }
            } else {
                try writer.writeAll("missing child relation");
            }
        },
        .missing_child_proof => {
            if (info.arg_index) |arg_index| {
                if (info.term_name) |term_name| {
                    try writer.print(
                        "argument {d} of term {s} changed without " ++
                            "a congruence proof",
                        .{ arg_index + 1, term_name },
                    );
                } else {
                    try writer.print(
                        "argument {d} changed without a congruence proof",
                        .{arg_index + 1},
                    );
                }
            } else {
                try writer.writeAll(
                    "argument changed without a congruence proof",
                );
            }
        },
        .missing_parent_relation => {
            if (info.term_name) |term_name| {
                try writer.print(
                    "missing parent relation for term {s}",
                    .{term_name},
                );
            } else {
                try writer.writeAll("missing parent relation");
            }
        },
        .malformed_rule => {
            if (info.term_name) |term_name| {
                try writer.print(
                    "malformed @congr rule for term {s}",
                    .{term_name},
                );
            } else {
                try writer.writeAll("malformed @congr rule");
            }
        },
        .unknown_term => {
            try writer.writeAll("normalization used an unknown term");
        },
    }
}

pub fn writeOmittedDiagnosticsSummary(
    writer: anytype,
    count: usize,
) !void {
    try writer.print("{d} more diagnostics omitted", .{count});
}

pub fn writeDepViolationSummary(
    writer: anytype,
    info: DepViolationDiagnosticDetail,
) !void {
    if (info.first_rule_bound and info.second_rule_bound) {
        try writer.writeAll("bound variables ");
        try writeDepViolationArgLabel(
            writer,
            info.first_arg_name,
            info.first_arg_idx,
        );
        try writer.writeAll(" and ");
        try writeDepViolationArgLabel(
            writer,
            info.second_arg_name,
            info.second_arg_idx,
        );
        try writer.writeAll(" must be assigned distinct variables");
        return;
    }
    if (info.first_rule_bound != info.second_rule_bound) {
        const bound_is_first = info.first_rule_bound;
        try writer.writeAll("the rule does not allow ");
        try writeDepViolationArgLabel(
            writer,
            if (bound_is_first) info.second_arg_name else info.first_arg_name,
            if (bound_is_first) info.second_arg_idx else info.first_arg_idx,
        );
        try writer.writeAll(" to mention the variable assigned to ");
        try writeDepViolationArgLabel(
            writer,
            if (bound_is_first) info.first_arg_name else info.second_arg_name,
            if (bound_is_first) info.first_arg_idx else info.second_arg_idx,
        );
        return;
    }
    try writer.writeAll("conflicting binders ");
    try writeDepViolationArgLabel(
        writer,
        info.first_arg_name,
        info.first_arg_idx,
    );
    try writer.writeAll(" and ");
    try writeDepViolationArgLabel(
        writer,
        info.second_arg_name,
        info.second_arg_idx,
    );
}

/// One "<arg> was assigned: <expr>" line, shared by the LSP and stderr
/// renderers so the wording stays in one place.
pub fn writeDepViolationAssignment(
    writer: anytype,
    name: ?[]const u8,
    idx: usize,
    text: []const u8,
) !void {
    try writeDepViolationArgLabel(writer, name, idx);
    try writer.writeAll(" was assigned: ");
    try writer.writeAll(text);
}

fn writeDepViolationArgLabel(
    writer: anytype,
    name: ?[]const u8,
    idx: usize,
) !void {
    if (name) |actual_name| {
        try writer.writeAll(actual_name);
        return;
    }
    try writer.print("#{d}", .{idx + 1});
}

pub fn buildCapturedDiagnosticDetail(
    env: *const GlobalEnv,
    detail: DiagScratch.CapturedDetail,
) DiagnosticDetail {
    return switch (detail) {
        .missing_congruence_rule => |info| .{
            .missing_congruence_rule = .{
                .reason = info.reason,
                .term_name = if (info.term_id) |term_id|
                    if (term_id < env.terms.items.len)
                        env.terms.items[term_id].name
                    else
                        null
                else
                    null,
                .sort_name = info.sort_name,
                .arg_index = info.arg_index,
            },
        },
    };
}

pub fn takeScratchDetail(
    scratch: *Scratch,
    mark: Scratch.Mark,
    env: *const GlobalEnv,
    err: anyerror,
) ?DiagnosticDetail {
    const detail = scratch.takeSince(mark, err) orelse return null;
    return buildCapturedDiagnosticDetail(env, detail);
}
