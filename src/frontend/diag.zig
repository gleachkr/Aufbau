const std = @import("std");
const Span = @import("./proof_script.zig").Span;
const ProofLine = @import("./proof_script.zig").ProofLine;
const ProofScriptParser = @import("./proof_script.zig").Parser;
const GlobalEnv = @import("./env.zig").GlobalEnv;
const DiagScratch = @import("./diag_scratch.zig");
const MathParseError = @import("./parse_recovery.zig").MathParseError;
const MathSpan = @import("./parse_recovery.zig").MathSpan;
const MM0Parser = @import("./parse_recovery.zig").MM0Parser;
const MM0Stmt = @import("./parse_recovery.zig").MM0Stmt;
const locale_strings = @import("diag_strings.zig");

pub const Lang = locale_strings.Lang;

/// The active diagnostic locale, chosen once at startup/init (CLI flag or
/// env var, wasm `set_locale` export). Every renderer in this file reads
/// it, so all frontends switch together. Not synchronized: set it before
/// compiling, not concurrently with it.
var active_lang: Lang = .en;

pub fn setLang(lang: Lang) void {
    active_lang = lang;
}

pub fn activeLang() Lang {
    return active_lang;
}

/// Parse a locale name ("en", "de"); null when unknown.
pub fn parseLang(name: []const u8) ?Lang {
    return std.meta.stringToEnum(Lang, name);
}

/// Look up a static catalogue string in the active locale. The `inline
/// else` makes each locale's table a comptime constant, so the lookup is
/// a field access, not a hash or scan.
fn t(comptime name: []const u8) []const u8 {
    return switch (active_lang) {
        inline else => |lang| comptime @field(locale_strings.table(lang), name),
    };
}

/// Print a catalogue template with `args` in the active locale. Each
/// locale's template is comptime-known inside its branch, so `std.fmt`
/// checks every translation's placeholders against the call site.
fn printT(writer: anytype, comptime name: []const u8, args: anytype) !void {
    switch (active_lang) {
        inline else => |lang| try writer.print(
            comptime @field(locale_strings.table(lang), name),
            args,
        ),
    }
}

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
    parse_block_header,
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
    /// The character the statement parser wanted when it stopped (e.g.
    /// the ';' a declaration is missing).
    expected_char: struct {
        ch: u8,
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

/// Structured content of a diagnostic note. Like `DiagnosticDetail`, notes
/// store data rather than prose: every message template lives in
/// `renderNoteMessage`, so a note cannot carry free-form English past the
/// catalogue, and adding a variant without a template is a compile error.
/// String payloads follow the same lifetime contract as note messages
/// always have: alive through setProof/setDiagnostic, where the sink
/// stable-copies them.
pub const NoteMessage = union(enum) {
    missing_semicolon_hint,
    unknown_math_token_hint,
    trailing_math_token_hint,
    search_placeholder_meaning,
    search_placeholder_unfinished,
    rule_declared_later,
    name_is_term_not_rule,
    name_is_label_not_rule,
    label_belongs_to_later_line,
    def_body_result_sort,
    def_body_checked_before_unify,
    def_body_free_var_deps,
    subexpression_sort_mismatch,
    subexpression_needs_bound_var,
    right_sort_but_needs_bound_var,
    holey_fallback_exhausted,
    visible_structure_mismatch,
    unnamed_rule_var_two_values,
    attempted_normalized_comparison,
    boundary_mismatch_despite_unfolding,
    boundary_mismatch_despite_normalization,
    conclusion_replay_mismatch,
    identical_positions_matched_differently,
    no_rule_var_completion,
    rule_requires_bound_var_here,
    assignment_parses_as_sort: struct {
        actual_sort: []const u8,
        expected_sort: []const u8,
    },
    statement_not_provable_sort: struct {
        actual_sort: []const u8,
    },
    /// 1-based display number; the premise and hypothesis positions are
    /// always the same number.
    premise_hypothesis_mismatch: struct {
        number: usize,
    },
    cited_premise_proves: struct {
        text: []const u8,
    },
    holey_unsolved_binder: struct {
        binder_name: []const u8,
    },
    /// 1-based display number.
    unsolved_binder_index: struct {
        number: usize,
    },
    conclusion_head_clash: struct {
        expected_term: []const u8,
        actual_term: []const u8,
    },
    conclusion_head_clash_with_variable: struct {
        expected_term: []const u8,
    },
    rule_var_two_values: struct {
        binder_name: []const u8,
    },
    already_matched: struct {
        text: []const u8,
    },
    in_the_statement: struct {
        text: []const u8,
    },
    at_the_mismatch: struct {
        text: []const u8,
    },
    hole_sort_mismatch: struct {
        token: []const u8,
        expected_sort: []const u8,
        actual_sort: []const u8,
    },
    expected_expr: struct {
        text: []const u8,
    },
    actual_expr: struct {
        text: []const u8,
    },
    normalized_expected_expr: struct {
        text: []const u8,
    },
    normalized_actual_expr: struct {
        text: []const u8,
    },
    freshen_attempted_for_target: struct {
        binder_name: []const u8,
    },
    freshen_blocker: struct {
        binder_name: []const u8,
    },
    freshen_replacement: struct {
        binder_name: []const u8,
    },
    freshen_still_depends_on_blocker: struct {
        binder_name: []const u8,
    },
    freshen_no_longer_depends_on_blocker: struct {
        binder_name: []const u8,
    },
    theorem_concludes: struct {
        text: []const u8,
    },
    last_line_proves: struct {
        text: []const u8,
    },
    explicit_bindings: struct {
        summary: []const u8,
    },
    inferred_bindings_before_failure: struct {
        summary: []const u8,
    },
    rule_requires_term_at_mismatch: struct {
        term_name: []const u8,
        found_text: []const u8,
    },
    chosen_bindings: struct {
        summary: []const u8,
    },
    alternative_bindings: struct {
        summary: []const u8,
    },
    distinct_solutions_considered: struct {
        count: usize,
    },
    binder_resolved_to: struct {
        text: []const u8,
    },
    binding_sort_mismatch: struct {
        actual_sort: []const u8,
        expected_sort: []const u8,
    },
    inference_path: struct {
        path: InferencePath,
    },
};

/// Label of a related-location entry, catalogued for the same reason as
/// `NoteMessage`.
pub const RelatedLabel = enum {
    rule_declaration_here,
};

pub const DiagnosticNote = struct {
    message: NoteMessage,
    source: DiagnosticSource,
    span: ?Span = null,
};

pub const DiagnosticRelated = struct {
    label: RelatedLabel,
    source: DiagnosticSource,
    span: Span,
};

/// Every error that may appear in a user-facing diagnostic. `Diagnostic.err`
/// is typed with this set so that routing a new error into a diagnostic is a
/// compile error until it is added here, and `compilerErrorSummary` switches
/// over it exhaustively so that every member must have a rendered message.
pub const DiagnosticError = error{
    AbstractConflict,
    AbstractNoPlugOccurrence,
    AbstractPlugSortMismatch,
    AbstractStructureMismatch,
    AbstractTargetNotRuleBinder,
    AbstractWithoutView,
    AlphaConclusionMustBeBinaryRelation,
    AlphaConclusionUnsupported,
    AlphaRequiresBoundBinders,
    AlphaRewriteSearchFailed,
    AlphaRuleHasHypotheses,
    AlphaSortMismatch,
    AmbiguousAcuiMatch,
    AmbiguousHypothesisRef,
    AnonymousNotationBinder,
    ArgCountMismatch,
    ArgDependencyOnDummy,
    BinderTokenCollision,
    BoundnessMismatch,
    CoercionCycle,
    CoercionDiamond,
    CoercionDiamondToProvable,
    ComputeBareMatchSide,
    ComputeBinderNotCovered,
    ComputeConclusionNotRelation,
    ComputeMissingRelation,
    ComputeRuleHasHypotheses,
    ConclusionMismatch,
    CongruenceBinderMissingDeps,
    CongruenceBinderOrderMismatch,
    ConversionAlphaRuleShape,
    ConversionAssocRuleShape,
    ConversionBareMatchSide,
    ConversionBinderNotCovered,
    ConversionCommRuleShape,
    ConversionConclusionNotRelation,
    ConversionDefUnfoldHiddenDummies,
    ConversionMissingRelation,
    ConversionRoleBoundBinder,
    ConversionRoleRelationHead,
    ConversionRuleHasHypotheses,
    ConversionTermNotDef,
    DepViolation,
    DependencySlotExhausted,
    DiagnosticsOmitted,
    DummyAnnotationRemoved,
    DummyHypothesisBinder,
    DummyNotationBinder,
    DuplicateBinderAssignment,
    DuplicateComputeAnnotation,
    DuplicateConversionAnnotation,
    DuplicateConversionRoleForHead,
    DuplicateFallbackAnnotation,
    DuplicateFillerBinderName,
    DuplicateFreshBinder,
    DuplicateFreshenPair,
    DuplicateHoleAnnotation,
    DuplicateHoleToken,
    DuplicateLabel,
    DuplicateRuleName,
    DuplicateSort,
    DuplicateTermName,
    DuplicateVarsToken,
    DuplicateViewAnnotation,
    EagerRuleDefersWitness,
    EmptyProofBlock,
    ExpectedBinaryOperator,
    ExpectedBlockUnderline,
    ExpectedBy,
    ExpectedCloseParen,
    ExpectedDefEquals,
    ExpectedDefinitionBody,
    ExpectedFormula,
    ExpectedIdent,
    ExpectedIdentifier,
    ExpectedKeyword,
    ExpectedLineEnd,
    ExpectedMathStr,
    ExpectedMathString,
    ExpectedMathToken,
    ExpectedNumber,
    ExpectedProofBlock,
    ExpectedString,
    ExpectedTermApp,
    ExpectedUnaryOperator,
    ExtraProofBlock,
    ExtraProofItem,
    FallbackCycle,
    FillerBinderMustBeDummy,
    FinalLineMismatch,
    FreshFreeSort,
    FreshNoAvailableVar,
    FreshRequiresBoundBinder,
    FreshStrictSort,
    FreshenBlockerMustBeBoundBinder,
    FreshenMissingRelation,
    FreshenTargetMustBeRegularBinder,
    FreshenTransportFailed,
    HiddenWitnessNoAvailableVar,
    HoleConclusionMismatch,
    HoleNotAllowedInTemplate,
    HoleNotConcrete,
    HoleTokenNameCollision,
    HoleyInferenceMismatch,
    HypCountMismatch,
    HypothesisMismatch,
    InfixPrecOutOfRange,
    InvalidAbstractAnnotation,
    InvalidAlphaAnnotation,
    InvalidAutoAnnotation,
    InvalidComputeAnnotation,
    InvalidCongruenceAnnotation,
    InvalidConversionAnnotation,
    InvalidDefConversionAnnotation,
    InvalidExprUseCount,
    InvalidFallbackAnnotation,
    InvalidFreshAnnotation,
    InvalidFreshenAnnotation,
    InvalidHoleAnnotation,
    InvalidNotationToken,
    InvalidNotationVariables,
    InvalidRecoverAnnotation,
    InvalidTriggerAnnotation,
    InvalidVarsAnnotation,
    InvalidViewAnnotation,
    MissingBinderAssignment,
    MissingCongruenceRule,
    MissingProofBlock,
    MissingPublicDefBody,
    MultiCharacterDelimiter,
    NoAlphaRewriteAvailable,
    NotProvable,
    NotationFirstTokenConflict,
    NotationMismatch,
    NumberOutOfRange,
    OutOfMemory,
    Overflow,
    PlaceholderLeakage,
    PrecMismatch,
    PrecedenceAssocMismatch,
    PrecedenceMismatch,
    PublicDefBodyMustBeHeaderless,
    PublicDefBodyNameMismatch,
    RecoverConflict,
    RecoverHoleNotFound,
    RecoverSortMismatch,
    RecoverStructureMismatch,
    RecoverTargetNotRuleBinder,
    RecoverWithoutView,
    RefCountMismatch,
    RelationBundleBoundBinder,
    ResultDependencyOnDummy,
    RuleNotYetAvailable,
    SortMismatch,
    TermMismatch,
    TheoremNameMismatch,
    TooManyBoundVars,
    TooManyCompilerRules,
    TooManyCompilerTerms,
    TooManySorts,
    TooManyTerms,
    TooManyTheoremExprs,
    TooManyTheoremVars,
    TrailingMathTokens,
    TriggerBinderNotGround,
    TriggerBoundPosition,
    TriggerRuleHasHypotheses,
    TriggerSortMismatch,
    UnboundExprVariable,
    UnexpectedChar,
    UnexpectedCharacter,
    UnexpectedEOF,
    UnexpectedHypothesisBinder,
    UnexpectedInternalError,
    UnexpectedKeyword,
    UnexpectedProofDefItem,
    UnexpectedTrailingInput,
    UnifyMismatch,
    UnifyStackNotEmpty,
    UnknownAbstractBinder,
    UnknownAlphaBinder,
    UnknownBinderName,
    UnknownDummyVar,
    UnknownExprUseCount,
    UnknownFallbackRule,
    UnknownFreshBinder,
    UnknownFreshenBinder,
    UnknownHypothesisRef,
    UnknownLabel,
    UnknownMathToken,
    UnknownPlaceholder,
    UnknownRecoverBinder,
    UnknownRule,
    UnknownSort,
    UnknownTemplateVariable,
    UnknownTerm,
    UnknownTermAnnotation,
    UnknownTheoremVariable,
    UnknownTriggerBinder,
    UnknownTriggerTerm,
    UnknownVariable,
    UnnamedRuleBinder,
    UnresolvedDummyWitness,
    UnsolvedMetaLeakage,
    UnsupportedProofDefAnnotation,
    UnterminatedMathStr,
    UnterminatedMathString,
    UnterminatedString,
    UnusedDefinitionParameter,
    UnusedTheoremParameter,
    VarsFreeSort,
    VarsStrictSort,
    VarsTokenCollision,
    ViewBindingConflict,
    ViewConclusionMismatch,
    ViewHypCountMismatch,
    ViewHypothesisMismatch,
};

/// Boundary conversion for code paths whose inferred error sets are erased
/// (functions that break recursion cycles with `anyerror` return types).
/// Catalogued names pass through unchanged; anything else degrades to
/// `UnexpectedInternalError` instead of leaking a raw Zig identifier.
pub fn narrowDiagnosticError(err: anyerror) DiagnosticError {
    const info = @typeInfo(DiagnosticError).error_set.?;
    inline for (info) |e| {
        if (std.mem.eql(u8, e.name, @errorName(err))) {
            return @errorCast(err);
        }
    }
    return error.UnexpectedInternalError;
}

pub const Diagnostic = struct {
    severity: DiagnosticSeverity = .@"error",
    kind: DiagnosticKind,
    err: DiagnosticError,
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
    message: NoteMessage,
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
    label: RelatedLabel,
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
        .strict_replay => t("path_strict_replay"),
        .transparent_fallback => t("path_transparent_fallback"),
        .normalized_session_fallback => t("path_normalized_session_fallback"),
        .structural_solver => t("path_structural_solver"),
        .holey_surface_match => t("path_holey_surface_match"),
    };
}

pub fn diagnosticPhaseName(phase: DiagnosticPhase) []const u8 {
    return switch (phase) {
        .parse => t("phase_parse"),
        .inference => t("phase_inference"),
        .theorem_application => t("phase_theorem_application"),
        .freshen => t("phase_freshen"),
        .normalization => t("phase_normalization"),
        .final_reconciliation => t("phase_final_reconciliation"),
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
    err: DiagnosticError,
) Diagnostic {
    var diag = mathErrorDiagnostic(.{
        .kind = .generic,
        .err = err,
        .source = .mm0,
        .name = parser.diagnosticName(),
        .span = mathSpanToSpanOpt(parser.diagnosticSpan()),
    }, parser.mathError());
    if (err == error.UnexpectedChar) {
        if (parser.expectedChar()) |ch| {
            diag.detail = .{ .expected_char = .{ .ch = ch } };
            if (ch == ';') {
                addNote(&diag, .missing_semicolon_hint, .mm0, null);
            }
        }
    }
    return diag;
}

pub fn mm0StatementDiagnostic(
    parser: *const MM0Parser,
    stmt: MM0Stmt,
    err: DiagnosticError,
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
    err: DiagnosticError,
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

/// A proof line the lenient parse could not finish (`ProofLine.incomplete`).
/// Mirrors `proofParserDiagnostic`'s shape — same error, and the recorded
/// failure span stands in for the parser's — so the analyze path reports
/// what the strict parse would have raised at this spot.
pub fn incompleteProofLineDiagnostic(
    theorem_name: []const u8,
    line: ProofLine,
) Diagnostic {
    return .{
        .kind = .generic,
        .err = line.parse_err orelse error.UnexpectedCharacter,
        .source = .proof,
        .theorem_name = theorem_name,
        .block_name = theorem_name,
        .line_label = line.label,
        .span = line.application.rule_span,
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
    err: DiagnosticError,
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
    err: DiagnosticError,
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

/// For lemma-header parse failures specifically: there is no rule in play,
/// so the `.generic` summaries ("binding does not satisfy the rule's sort
/// constraint") would blame machinery the header never touched.
pub fn lemmaHeaderDiagnostic(
    block_name: []const u8,
    span: Span,
    err: DiagnosticError,
) Diagnostic {
    return .{
        .kind = .parse_block_header,
        .err = err,
        .source = .proof,
        .theorem_name = block_name,
        .block_name = block_name,
        .span = span,
    };
}

/// Remap the error state recorded while parsing the synthetic
/// "theorem NAME<tail>;" buffer back onto the real header: synthetic
/// offsets past the prefix land inside `header_tail`, whose source span
/// the proof script records. Leaves the diagnostic untouched when the
/// failure predates the tail or recorded no span.
pub fn narrowLemmaHeaderDiagnostic(
    diag: *Diagnostic,
    parser: *const MM0Parser,
    syn_prefix_len: usize,
    tail_span: Span,
) void {
    if (parser.diagnosticSpan()) |syn_span| {
        const tail_len = tail_span.end - tail_span.start;
        if (syn_span.start >= syn_prefix_len and
            syn_span.end <= syn_prefix_len + tail_len)
        {
            diag.span = .{
                .start = tail_span.start + (syn_span.start - syn_prefix_len),
                .end = tail_span.start + (syn_span.end - syn_prefix_len),
            };
        }
    }
    const math_err = parser.mathError() orelse return;
    switch (math_err) {
        // Token text slices the synthetic buffer; the sink stable-copies
        // it at set time.
        .unknown_token, .unexpected_token => |token| {
            diag.detail = .{ .unknown_math_token = .{ .token = token.text } };
        },
        .unexpected_end => {},
    }
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
    err: DiagnosticError,
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
    var result = mathErrorDiagnostic(diag, math_err);
    switch (math_err) {
        .unknown_token => |token| {
            result.span = proofMathTokenSpan(math_span, token.span);
            addNote(&result, .unknown_math_token_hint, result.source, null);
        },
        .unexpected_token => |token| {
            result.span = proofMathTokenSpan(math_span, token.span);
            if (diag.err == error.TrailingMathTokens) {
                addNote(
                    &result,
                    .trailing_math_token_hint,
                    result.source,
                    null,
                );
            }
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
    math_err: ?MathParseError,
) Diagnostic {
    const actual = math_err orelse return diag;

    var result = diag;
    switch (actual) {
        // Both variants carry the token the parse stopped at; naming it
        // beats a bare "could not parse" with a whole-string span.
        .unknown_token, .unexpected_token => |token| {
            result.detail = .{
                .unknown_math_token = .{
                    .token = token.text,
                },
            };
        },
        .unexpected_end => {},
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
        error.ConversionAlphaRuleShape,
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
        .omitted_diagnostics => t("kind_omitted_diagnostics"),
        .missing_proof_block => t("kind_missing_proof_block"),
        .extra_proof_block => t("kind_extra_proof_block"),
        .extra_proof_def => t("kind_extra_proof_def"),
        .theorem_name_mismatch => t("kind_theorem_name_mismatch"),
        .missing_public_def_body => t("kind_missing_public_def_body"),
        .public_def_body_name_mismatch => t("kind_public_def_body_name_mismatch"),
        .public_def_body_header => t("kind_public_def_body_header"),
        .unexpected_proof_def => t("kind_unexpected_proof_def"),
        .unsupported_proof_def_annotation => t("kind_unsupported_proof_def_annotation"),
        .duplicate_rule_name => t("kind_duplicate_rule_name"),
        .parse_assertion => switch (diag.err) {
            error.NotProvable => t("kind_statement_not_provable"),
            error.SortMismatch => t("kind_statement_subexpr_sort"),
            else => t("kind_parse_assertion_fallback"),
        },
        .parse_binding => switch (diag.err) {
            error.SortMismatch => t("kind_binding_sort_mismatch"),
            error.BoundnessMismatch => t("kind_binding_boundness_mismatch"),
            else => t("kind_parse_binding_fallback"),
        },
        .parse_block_header => switch (diag.err) {
            error.NotProvable => t("kind_statement_not_provable"),
            error.SortMismatch => t("kind_statement_subexpr_sort"),
            error.BoundnessMismatch => t("kind_block_header_boundness"),
            else => compilerErrorSummary(diag.err),
        },
        .parse_fresh => compilerErrorSummary(diag.err),
        .inference_failed => compilerErrorSummary(diag.err),
        .unknown_rule => t("kind_unknown_rule"),
        .unresolved_search_placeholder => t("kind_unresolved_search_placeholder"),
        .rule_not_yet_available => t("kind_rule_not_yet_available"),
        .unknown_binder_name => t("kind_unknown_binder_name"),
        .duplicate_binder_assignment => t("kind_duplicate_binder_assignment"),
        .missing_binder_assignment => t("kind_missing_binder_assignment"),
        .ref_count_mismatch => t("kind_ref_count_mismatch"),
        .unknown_hypothesis_ref => t("kind_unknown_hypothesis_ref"),
        .ambiguous_hypothesis_ref => t("kind_ambiguous_hypothesis_ref"),
        .unknown_label => t("kind_unknown_label"),
        .hypothesis_mismatch => t("kind_hypothesis_mismatch"),
        .conclusion_mismatch => if (diag.err == error.HoleConclusionMismatch)
            compilerErrorSummary(diag.err)
        else
            t("kind_conclusion_mismatch"),
        .duplicate_label => t("kind_duplicate_label"),
        .empty_proof_block => t("kind_empty_proof_block"),
        .final_line_mismatch => t("kind_final_line_mismatch"),
        .invalid_definition_body => definitionBodySummary(diag.err),
        .unused_theorem_parameter => t("kind_unused_theorem_parameter"),
        .unused_definition_parameter => t("kind_unused_definition_parameter"),
    };
}

fn definitionBodySummary(err: DiagnosticError) []const u8 {
    return switch (err) {
        error.DepViolation => t("defbody_dep_violation"),
        error.SortMismatch => t("defbody_sort_mismatch"),
        else => t("defbody_fallback"),
    };
}

/// Render any error as a user-facing sentence: catalogued errors get their
/// summary, unknown names degrade to the internal-error message. For paths
/// that report an error with no recorded diagnostic.
pub fn errorSummary(err: anyerror) []const u8 {
    return compilerErrorSummary(narrowDiagnosticError(err));
}

fn compilerErrorSummary(err: DiagnosticError) []const u8 {
    return switch (err) {
        error.BoundnessMismatch => t("err_BoundnessMismatch"),
        error.SortMismatch => t("err_SortMismatch"),
        error.UnifyMismatch,
        error.UnifyStackNotEmpty,
        => t("err_UnifyMismatch"),
        error.TermMismatch,
        error.ExpectedTermApp,
        => t("err_TermMismatch"),
        error.HypCountMismatch => t("err_HypCountMismatch"),
        error.HoleTokenNameCollision => t("err_HoleTokenNameCollision"),
        error.BinderTokenCollision => t("err_BinderTokenCollision"),
        error.ResultDependencyOnDummy => t("err_ResultDependencyOnDummy"),
        error.ArgDependencyOnDummy => t("err_ArgDependencyOnDummy"),
        error.HoleyInferenceMismatch => t("err_HoleyInferenceMismatch"),
        error.HoleConclusionMismatch => t("err_HoleConclusionMismatch"),
        error.AmbiguousAcuiMatch => t("err_AmbiguousAcuiMatch"),
        error.RuleNotYetAvailable => t("kind_rule_not_yet_available"),
        error.UnknownTheoremVariable => t("err_UnknownTheoremVariable"),
        error.DuplicateRuleName => t("kind_duplicate_rule_name"),
        error.DuplicateViewAnnotation => t("err_DuplicateViewAnnotation"),
        error.InvalidViewAnnotation => t("err_InvalidViewAnnotation"),
        error.ViewHypCountMismatch => t("err_ViewHypCountMismatch"),
        error.ViewConclusionMismatch => t("err_ViewConclusionMismatch"),
        error.ViewHypothesisMismatch => t("err_ViewHypothesisMismatch"),
        error.ViewBindingConflict => t("err_ViewBindingConflict"),
        error.RecoverWithoutView => t("err_RecoverWithoutView"),
        error.InvalidRecoverAnnotation => t("err_InvalidRecoverAnnotation"),
        error.UnknownRecoverBinder => t("err_UnknownRecoverBinder"),
        error.RecoverTargetNotRuleBinder => t("err_RecoverTargetNotRuleBinder"),
        error.RecoverSortMismatch => t("err_RecoverSortMismatch"),
        error.RecoverHoleNotFound => t("err_RecoverHoleNotFound"),
        error.RecoverConflict => t("err_RecoverConflict"),
        error.RecoverStructureMismatch => t("err_RecoverStructureMismatch"),
        error.AbstractWithoutView => t("err_AbstractWithoutView"),
        error.InvalidAbstractAnnotation => t("err_InvalidAbstractAnnotation"),
        error.UnknownAbstractBinder => t("err_UnknownAbstractBinder"),
        error.AbstractTargetNotRuleBinder => t("err_AbstractTargetNotRuleBinder"),
        error.AbstractPlugSortMismatch => t("err_AbstractPlugSortMismatch"),
        error.AbstractNoPlugOccurrence => t("err_AbstractNoPlugOccurrence"),
        error.AbstractConflict => t("err_AbstractConflict"),
        error.AbstractStructureMismatch => t("err_AbstractStructureMismatch"),
        error.UnknownTermAnnotation => t("err_UnknownTermAnnotation"),
        error.DummyAnnotationRemoved => t("err_DummyAnnotationRemoved"),
        error.InvalidFreshAnnotation => t("err_InvalidFreshAnnotation"),
        error.InvalidFreshenAnnotation => t("err_InvalidFreshenAnnotation"),
        error.InvalidAlphaAnnotation => t("err_InvalidAlphaAnnotation"),
        error.InvalidFallbackAnnotation => t("err_InvalidFallbackAnnotation"),
        error.DuplicateFallbackAnnotation => t("err_DuplicateFallbackAnnotation"),
        error.UnknownFallbackRule => t("err_UnknownFallbackRule"),
        error.InvalidAutoAnnotation => t("err_InvalidAutoAnnotation"),
        error.EagerRuleDefersWitness => t("err_EagerRuleDefersWitness"),
        error.InvalidTriggerAnnotation => t("err_InvalidTriggerAnnotation"),
        error.UnknownTriggerTerm => t("err_UnknownTriggerTerm"),
        error.UnknownTriggerBinder => t("err_UnknownTriggerBinder"),
        error.TriggerRuleHasHypotheses => t("err_TriggerRuleHasHypotheses"),
        error.TriggerBinderNotGround => t("err_TriggerBinderNotGround"),
        error.TriggerSortMismatch => t("err_TriggerSortMismatch"),
        error.TriggerBoundPosition => t("err_TriggerBoundPosition"),
        error.FallbackCycle => t("err_FallbackCycle"),
        error.UnknownFreshBinder => t("err_UnknownFreshBinder"),
        error.UnknownFreshenBinder => t("err_UnknownFreshenBinder"),
        error.UnknownAlphaBinder => t("err_UnknownAlphaBinder"),
        error.DuplicateFreshBinder => t("err_DuplicateFreshBinder"),
        error.DuplicateFreshenPair => t("err_DuplicateFreshenPair"),
        error.FreshRequiresBoundBinder => t("err_FreshRequiresBoundBinder"),
        error.FreshenTargetMustBeRegularBinder => t("err_FreshenTargetMustBeRegularBinder"),
        error.FreshenBlockerMustBeBoundBinder => t("err_FreshenBlockerMustBeBoundBinder"),
        error.AlphaRequiresBoundBinders => t("err_AlphaRequiresBoundBinders"),
        error.AlphaSortMismatch => t("err_AlphaSortMismatch"),
        error.AlphaConclusionMustBeBinaryRelation => t("err_AlphaConclusionMustBeBinaryRelation"),
        error.AlphaConclusionUnsupported => t("err_AlphaConclusionUnsupported"),
        error.AlphaRuleHasHypotheses => t("err_AlphaRuleHasHypotheses"),
        error.InvalidCongruenceAnnotation => t("err_InvalidCongruenceAnnotation"),
        error.CongruenceBinderOrderMismatch => t("err_CongruenceBinderOrderMismatch"),
        error.CongruenceBinderMissingDeps => t("err_CongruenceBinderMissingDeps"),
        error.RelationBundleBoundBinder => t("err_RelationBundleBoundBinder"),
        error.InvalidConversionAnnotation => t("err_InvalidConversionAnnotation"),
        error.InvalidDefConversionAnnotation => t("err_InvalidDefConversionAnnotation"),
        error.ConversionTermNotDef => t("err_ConversionTermNotDef"),
        error.ConversionDefUnfoldHiddenDummies => t("err_ConversionDefUnfoldHiddenDummies"),
        error.DuplicateConversionAnnotation => t("err_DuplicateConversionAnnotation"),
        error.ConversionRuleHasHypotheses => t("err_ConversionRuleHasHypotheses"),
        error.ConversionCommRuleShape => t("err_ConversionCommRuleShape"),
        error.ConversionAssocRuleShape => t("err_ConversionAssocRuleShape"),
        error.ConversionAlphaRuleShape => t("err_ConversionAlphaRuleShape"),
        error.ConversionRoleBoundBinder => t("err_ConversionRoleBoundBinder"),
        error.ConversionRoleRelationHead => t("err_ConversionRoleRelationHead"),
        error.DuplicateConversionRoleForHead => t("err_DuplicateConversionRoleForHead"),
        error.ConversionConclusionNotRelation => t("err_ConversionConclusionNotRelation"),
        error.ConversionMissingRelation => t("err_ConversionMissingRelation"),
        error.ConversionBareMatchSide => t("err_ConversionBareMatchSide"),
        error.ConversionBinderNotCovered => t("err_ConversionBinderNotCovered"),
        error.InvalidComputeAnnotation => t("err_InvalidComputeAnnotation"),
        error.DuplicateComputeAnnotation => t("err_DuplicateComputeAnnotation"),
        error.ComputeRuleHasHypotheses => t("err_ComputeRuleHasHypotheses"),
        error.ComputeConclusionNotRelation => t("err_ComputeConclusionNotRelation"),
        error.ComputeMissingRelation => t("err_ComputeMissingRelation"),
        error.ComputeBareMatchSide => t("err_ComputeBareMatchSide"),
        error.ComputeBinderNotCovered => t("err_ComputeBinderNotCovered"),
        error.FreshStrictSort => t("err_FreshStrictSort"),
        error.FreshFreeSort => t("err_FreshFreeSort"),
        error.FreshNoAvailableVar => t("err_FreshNoAvailableVar"),
        error.HiddenWitnessNoAvailableVar => t("err_HiddenWitnessNoAvailableVar"),
        error.NoAlphaRewriteAvailable => t("err_NoAlphaRewriteAvailable"),
        error.AlphaRewriteSearchFailed => t("err_AlphaRewriteSearchFailed"),
        error.DepViolation => t("err_DepViolation"),
        error.FreshenMissingRelation => t("err_FreshenMissingRelation"),
        error.FreshenTransportFailed => t("err_FreshenTransportFailed"),
        error.InvalidHoleAnnotation => t("err_InvalidHoleAnnotation"),
        error.DuplicateHoleAnnotation => t("err_DuplicateHoleAnnotation"),
        error.DuplicateHoleToken => t("err_DuplicateHoleToken"),
        error.InvalidVarsAnnotation => t("err_InvalidVarsAnnotation"),
        error.VarsStrictSort => t("err_VarsStrictSort"),
        error.VarsFreeSort => t("err_VarsFreeSort"),
        error.DuplicateVarsToken => t("err_DuplicateVarsToken"),
        error.VarsTokenCollision => t("err_VarsTokenCollision"),
        error.DependencySlotExhausted => t("err_DependencySlotExhausted"),
        error.UnresolvedDummyWitness => t("err_UnresolvedDummyWitness"),
        error.MissingCongruenceRule => t("err_MissingCongruenceRule"),
        error.ExpectedIdentifier,
        error.ExpectedIdent,
        => t("err_ExpectedIdentifier"),
        error.ExpectedNumber => t("err_ExpectedNumber"),
        error.UnknownMathToken => t("err_UnknownMathToken"),
        error.ExpectedMathToken => t("err_ExpectedMathToken"),
        error.ExpectedCloseParen => t("err_ExpectedCloseParen"),
        error.TrailingMathTokens => t("err_TrailingMathTokens"),
        error.NotationMismatch => t("err_NotationMismatch"),
        error.AnonymousNotationBinder => t("err_AnonymousNotationBinder"),
        error.DummyNotationBinder => t("err_DummyNotationBinder"),
        error.InvalidNotationVariables => t("err_InvalidNotationVariables"),
        error.PrecMismatch => t("err_PrecMismatch"),
        error.NotProvable => t("err_NotProvable"),
        error.ExpectedMathString,
        error.ExpectedMathStr,
        => t("err_ExpectedMathString"),
        error.MissingPublicDefBody => t("kind_missing_public_def_body"),
        error.PublicDefBodyNameMismatch => t("kind_public_def_body_name_mismatch"),
        error.PublicDefBodyMustBeHeaderless => t("err_PublicDefBodyMustBeHeaderless"),
        error.FillerBinderMustBeDummy => t("err_FillerBinderMustBeDummy"),
        error.DuplicateFillerBinderName => t("err_DuplicateFillerBinderName"),
        error.TooManyBoundVars => t("err_TooManyBoundVars"),
        error.UnexpectedProofDefItem => t("kind_unexpected_proof_def"),
        error.UnsupportedProofDefAnnotation => t("kind_unsupported_proof_def_annotation"),
        error.ExtraProofItem => t("err_ExtraProofItem"),
        error.ExpectedBy => t("err_ExpectedBy"),
        error.ExpectedKeyword => t("err_ExpectedKeyword"),
        error.ExpectedString => t("err_ExpectedString"),
        error.UnknownTerm => t("err_UnknownTerm"),
        error.UnknownSort => t("err_UnknownSort"),
        error.UnknownVariable => t("err_UnknownVariable"),
        error.UnexpectedKeyword => t("err_UnexpectedKeyword"),
        error.UnexpectedCharacter,
        error.UnexpectedChar,
        => t("err_UnexpectedCharacter"),
        error.ExpectedLineEnd => t("err_ExpectedLineEnd"),
        error.ExpectedBlockUnderline => t("err_ExpectedBlockUnderline"),
        error.UnterminatedMathString,
        error.UnterminatedMathStr,
        => t("err_UnterminatedMathString"),
        error.UnterminatedString => t("err_UnterminatedString"),
        error.ExpectedDefEquals => t("err_ExpectedDefEquals"),
        error.ExpectedProofBlock => t("err_ExpectedProofBlock"),
        error.OutOfMemory => t("err_OutOfMemory"),
        error.UnexpectedInternalError => t("err_UnexpectedInternalError"),
        error.UnknownDummyVar => t("err_UnknownDummyVar"),
        error.UnknownPlaceholder => t("err_UnknownPlaceholder"),
        error.PlaceholderLeakage => t("err_PlaceholderLeakage"),
        error.UnsolvedMetaLeakage => t("err_UnsolvedMetaLeakage"),
        error.Overflow => t("err_Overflow"),
        error.TooManyTheoremExprs => t("err_TooManyTheoremExprs"),
        error.HoleNotConcrete => t("err_HoleNotConcrete"),
        error.HoleNotAllowedInTemplate => t("err_HoleNotAllowedInTemplate"),
        error.TooManyCompilerRules => t("err_TooManyCompilerRules"),
        error.TooManyCompilerTerms => t("err_TooManyCompilerTerms"),
        error.UnknownTemplateVariable => t("err_UnknownTemplateVariable"),
        error.InvalidExprUseCount,
        error.UnknownExprUseCount,
        error.UnboundExprVariable,
        => t("err_InvalidExprUseCount"),
        error.TooManyTheoremVars => t("err_TooManyTheoremVars"),
        error.ExpectedDefinitionBody => t("err_ExpectedDefinitionBody"),
        error.ArgCountMismatch => t("err_ArgCountMismatch"),
        error.DummyHypothesisBinder => t("err_DummyHypothesisBinder"),
        error.DuplicateSort => t("err_DuplicateSort"),
        error.DuplicateTermName => t("err_DuplicateTermName"),
        error.ExpectedFormula => t("err_ExpectedFormula"),
        error.TooManySorts => t("err_TooManySorts"),
        error.TooManyTerms => t("err_TooManyTerms"),
        error.UnexpectedHypothesisBinder => t("err_UnexpectedHypothesisBinder"),
        error.UnexpectedTrailingInput => t("err_UnexpectedTrailingInput"),
        error.UnexpectedEOF => t("err_UnexpectedEOF"),
        error.NumberOutOfRange => t("err_NumberOutOfRange"),
        error.MultiCharacterDelimiter => t("err_MultiCharacterDelimiter"),
        error.InvalidNotationToken => t("err_InvalidNotationToken"),
        error.PrecedenceMismatch => t("err_PrecedenceMismatch"),
        error.PrecedenceAssocMismatch => t("err_PrecedenceAssocMismatch"),
        error.NotationFirstTokenConflict => t("err_NotationFirstTokenConflict"),
        error.ExpectedBinaryOperator => t("err_ExpectedBinaryOperator"),
        error.ExpectedUnaryOperator => t("err_ExpectedUnaryOperator"),
        error.InfixPrecOutOfRange => t("err_InfixPrecOutOfRange"),
        error.CoercionCycle => t("err_CoercionCycle"),
        error.CoercionDiamond => t("err_CoercionDiamond"),
        error.CoercionDiamondToProvable => t("err_CoercionDiamondToProvable"),
        error.ConclusionMismatch => t("kind_conclusion_mismatch"),
        error.DiagnosticsOmitted => t("kind_omitted_diagnostics"),
        error.DuplicateBinderAssignment => t("kind_duplicate_binder_assignment"),
        error.DuplicateLabel => t("kind_duplicate_label"),
        error.EmptyProofBlock => t("kind_empty_proof_block"),
        error.ExtraProofBlock => t("kind_extra_proof_block"),
        error.FinalLineMismatch => t("kind_final_line_mismatch"),
        error.HypothesisMismatch => t("kind_hypothesis_mismatch"),
        error.MissingBinderAssignment => t("kind_missing_binder_assignment"),
        error.MissingProofBlock => t("kind_missing_proof_block"),
        error.RefCountMismatch => t("kind_ref_count_mismatch"),
        error.TheoremNameMismatch => t("kind_theorem_name_mismatch"),
        error.UnknownBinderName => t("kind_unknown_binder_name"),
        error.UnknownLabel => t("kind_unknown_label"),
        error.UnknownRule => t("kind_unknown_rule"),
        error.UnnamedRuleBinder => t("err_UnnamedRuleBinder"),
        error.UnknownHypothesisRef => t("kind_unknown_hypothesis_ref"),
        error.AmbiguousHypothesisRef => t("kind_ambiguous_hypothesis_ref"),
        error.UnusedTheoremParameter => t("kind_unused_theorem_parameter"),
        error.UnusedDefinitionParameter => t("kind_unused_definition_parameter"),
    };
}

pub fn writeMissingCongruenceRuleSummary(
    writer: anytype,
    info: MissingCongruenceRuleDetail,
) !void {
    switch (info.reason) {
        .missing_rule => {
            if (info.term_name) |term_name| {
                try printT(writer, "congr_missing_rule_for_term", .{term_name});
            } else {
                try writer.writeAll(t("congr_missing_rule"));
            }
        },
        .changed_bound_arg => {
            if (info.arg_index) |arg_index| {
                if (info.term_name) |term_name| {
                    try printT(
                        writer,
                        "congr_changed_bound_arg_term",
                        .{ arg_index + 1, term_name },
                    );
                } else {
                    try printT(
                        writer,
                        "congr_changed_bound_arg",
                        .{arg_index + 1},
                    );
                }
            } else {
                try writer.writeAll(t("congr_changed_bound_arg_generic"));
            }
        },
        .missing_child_relation => {
            if (info.arg_index) |arg_index| {
                if (info.term_name) |term_name| {
                    try printT(
                        writer,
                        "congr_missing_child_relation_term",
                        .{ arg_index + 1, term_name },
                    );
                } else {
                    try printT(
                        writer,
                        "congr_missing_child_relation_arg",
                        .{arg_index + 1},
                    );
                }
            } else {
                try writer.writeAll(t("congr_missing_child_relation"));
            }
        },
        .missing_child_proof => {
            if (info.arg_index) |arg_index| {
                if (info.term_name) |term_name| {
                    try printT(
                        writer,
                        "congr_missing_child_proof_term",
                        .{ arg_index + 1, term_name },
                    );
                } else {
                    try printT(
                        writer,
                        "congr_missing_child_proof_arg",
                        .{arg_index + 1},
                    );
                }
            } else {
                try writer.writeAll(t("congr_missing_child_proof"));
            }
        },
        .missing_parent_relation => {
            if (info.term_name) |term_name| {
                try printT(
                    writer,
                    "congr_missing_parent_relation_term",
                    .{term_name},
                );
            } else {
                try writer.writeAll(t("congr_missing_parent_relation"));
            }
        },
        .malformed_rule => {
            if (info.term_name) |term_name| {
                try printT(writer, "congr_malformed_rule_term", .{term_name});
            } else {
                try writer.writeAll(t("congr_malformed_rule"));
            }
        },
        .unknown_term => {
            try writer.writeAll(t("congr_unknown_term"));
        },
    }
}

pub fn writeOmittedDiagnosticsSummary(
    writer: anytype,
    count: usize,
) !void {
    try printT(writer, "omitted_diagnostics_count", .{count});
}

pub fn writeDepViolationSummary(
    writer: anytype,
    info: DepViolationDiagnosticDetail,
) !void {
    var first_buf: DepViolationLabelBuf = undefined;
    var second_buf: DepViolationLabelBuf = undefined;
    const first = depViolationArgLabel(
        &first_buf,
        info.first_arg_name,
        info.first_arg_idx,
    );
    const second = depViolationArgLabel(
        &second_buf,
        info.second_arg_name,
        info.second_arg_idx,
    );
    if (info.first_rule_bound and info.second_rule_bound) {
        try printT(writer, "dep_bound_distinct", .{ first, second });
        return;
    }
    if (info.first_rule_bound != info.second_rule_bound) {
        const bound = if (info.first_rule_bound) first else second;
        const regular = if (info.first_rule_bound) second else first;
        try printT(writer, "dep_regular_mentions_bound", .{ regular, bound });
        return;
    }
    try printT(writer, "dep_conflicting_binders", .{ first, second });
}

/// One "<arg> was assigned: <expr>" line of the dep-violation detail.
fn writeDepViolationAssignment(
    writer: anytype,
    name: ?[]const u8,
    idx: usize,
    text: []const u8,
) !void {
    var label_buf: DepViolationLabelBuf = undefined;
    try printT(
        writer,
        "dep_assignment",
        .{ depViolationArgLabel(&label_buf, name, idx), text },
    );
}

/// Room for the fallback "#N" label: '#' plus a full 64-bit index.
const DepViolationLabelBuf = [21]u8;

fn depViolationArgLabel(
    buf: *DepViolationLabelBuf,
    name: ?[]const u8,
    idx: usize,
) []const u8 {
    if (name) |actual_name| return actual_name;
    return std.fmt.bufPrint(buf, "#{d}", .{idx + 1}) catch unreachable;
}

/// The single human-readable diagnostic renderer, shared by the CLI sink,
/// the LSP message builder, and the wasm JSON message field. Writes the
/// summary followed by one context line per populated field (theorem,
/// proof block, line, rule, name, expected, phase) and the lines for
/// `diag.detail`. `line_separator` is written before each context line;
/// the frontends differ only in that framing (the CLI passes "\n  " and
/// appends a final newline, LSP and wasm pass "\n").
///
/// The note-message catalogue: one template per `NoteMessage` variant,
/// switched exhaustively so a variant without a template is a compile
/// error. Shared by the CLI sink, the LSP message builder, and the wasm
/// JSON notes array.
pub fn renderNoteMessage(writer: anytype, message: NoteMessage) !void {
    switch (message) {
        .missing_semicolon_hint => try writer.writeAll(t("note_missing_semicolon_hint")),
        .unknown_math_token_hint => try writer.writeAll(t("note_unknown_math_token_hint")),
        .trailing_math_token_hint => try writer.writeAll(t("note_trailing_math_token_hint")),
        .search_placeholder_meaning => try writer.writeAll(t("note_search_placeholder_meaning")),
        .search_placeholder_unfinished => try writer.writeAll(t("note_search_placeholder_unfinished")),
        .rule_declared_later => try writer.writeAll(t("note_rule_declared_later")),
        .name_is_term_not_rule => try writer.writeAll(t("note_name_is_term_not_rule")),
        .name_is_label_not_rule => try writer.writeAll(t("note_name_is_label_not_rule")),
        .label_belongs_to_later_line => try writer.writeAll(t("note_label_belongs_to_later_line")),
        .def_body_result_sort => try writer.writeAll(t("note_def_body_result_sort")),
        .def_body_checked_before_unify => try writer.writeAll(t("note_def_body_checked_before_unify")),
        .def_body_free_var_deps => try writer.writeAll(t("note_def_body_free_var_deps")),
        .subexpression_sort_mismatch => try writer.writeAll(t("note_subexpression_sort_mismatch")),
        .subexpression_needs_bound_var => try writer.writeAll(t("note_subexpression_needs_bound_var")),
        .right_sort_but_needs_bound_var => try writer.writeAll(t("note_right_sort_but_needs_bound_var")),
        .holey_fallback_exhausted => try writer.writeAll(t("note_holey_fallback_exhausted")),
        .visible_structure_mismatch => try writer.writeAll(t("note_visible_structure_mismatch")),
        .unnamed_rule_var_two_values => try writer.writeAll(t("note_unnamed_rule_var_two_values")),
        .attempted_normalized_comparison => try writer.writeAll(t("note_attempted_normalized_comparison")),
        .boundary_mismatch_despite_unfolding => try writer.writeAll(t("note_boundary_mismatch_despite_unfolding")),
        .boundary_mismatch_despite_normalization => try writer.writeAll(t("note_boundary_mismatch_despite_normalization")),
        .conclusion_replay_mismatch => try writer.writeAll(t("note_conclusion_replay_mismatch")),
        .identical_positions_matched_differently => try writer.writeAll(t("note_identical_positions_matched_differently")),
        .no_rule_var_completion => try writer.writeAll(t("note_no_rule_var_completion")),
        .rule_requires_bound_var_here => try writer.writeAll(t("note_rule_requires_bound_var_here")),
        .assignment_parses_as_sort => |info| try printT(writer, "note_assignment_parses_as_sort", .{ info.actual_sort, info.expected_sort }),
        .statement_not_provable_sort => |info| try printT(writer, "note_statement_not_provable_sort", .{info.actual_sort}),
        .premise_hypothesis_mismatch => |info| try printT(writer, "note_premise_hypothesis_mismatch", .{info.number}),
        .cited_premise_proves => |info| try printT(writer, "note_cited_premise_proves", .{info.text}),
        .holey_unsolved_binder => |info| try printT(writer, "note_holey_unsolved_binder", .{info.binder_name}),
        .unsolved_binder_index => |info| try printT(writer, "note_unsolved_binder_index", .{info.number}),
        .conclusion_head_clash => |info| try printT(writer, "note_conclusion_head_clash", .{ info.expected_term, info.actual_term }),
        .conclusion_head_clash_with_variable => |info| try printT(writer, "note_conclusion_head_clash_with_variable", .{info.expected_term}),
        .rule_var_two_values => |info| try printT(writer, "note_rule_var_two_values", .{info.binder_name}),
        .already_matched => |info| try printT(writer, "note_already_matched", .{info.text}),
        .in_the_statement => |info| try printT(writer, "note_in_the_statement", .{info.text}),
        .at_the_mismatch => |info| try printT(writer, "note_at_the_mismatch", .{info.text}),
        .hole_sort_mismatch => |info| try printT(writer, "note_hole_sort_mismatch", .{ info.token, info.expected_sort, info.actual_sort }),
        .expected_expr => |info| try printT(writer, "note_expected_expr", .{info.text}),
        .actual_expr => |info| try printT(writer, "note_actual_expr", .{info.text}),
        .normalized_expected_expr => |info| try printT(writer, "note_normalized_expected_expr", .{info.text}),
        .normalized_actual_expr => |info| try printT(writer, "note_normalized_actual_expr", .{info.text}),
        .freshen_attempted_for_target => |info| try printT(writer, "note_freshen_attempted_for_target", .{info.binder_name}),
        .freshen_blocker => |info| try printT(writer, "note_freshen_blocker", .{info.binder_name}),
        .freshen_replacement => |info| try printT(writer, "note_freshen_replacement", .{info.binder_name}),
        .freshen_still_depends_on_blocker => |info| try printT(writer, "note_freshen_still_depends_on_blocker", .{info.binder_name}),
        .freshen_no_longer_depends_on_blocker => |info| try printT(writer, "note_freshen_no_longer_depends_on_blocker", .{info.binder_name}),
        .theorem_concludes => |info| try printT(writer, "note_theorem_concludes", .{info.text}),
        .last_line_proves => |info| try printT(writer, "note_last_line_proves", .{info.text}),
        .explicit_bindings => |info| try printT(writer, "note_explicit_bindings", .{info.summary}),
        .inferred_bindings_before_failure => |info| try printT(writer, "note_inferred_bindings_before_failure", .{info.summary}),
        .rule_requires_term_at_mismatch => |info| try printT(writer, "note_rule_requires_term_at_mismatch", .{ info.term_name, info.found_text }),
        .chosen_bindings => |info| try printT(writer, "note_chosen_bindings", .{info.summary}),
        .alternative_bindings => |info| try printT(writer, "note_alternative_bindings", .{info.summary}),
        .distinct_solutions_considered => |info| try printT(writer, "note_distinct_solutions_considered", .{info.count}),
        .binder_resolved_to => |info| try printT(writer, "note_binder_resolved_to", .{info.text}),
        .binding_sort_mismatch => |info| try printT(writer, "note_binding_sort_mismatch", .{ info.actual_sort, info.expected_sort }),
        .inference_path => |info| try printT(writer, "note_inference_path", .{inferencePathName(info.path)}),
    }
}

/// The related-label catalogue, exhaustive like `renderNoteMessage`.
pub fn renderRelatedLabel(writer: anytype, label: RelatedLabel) !void {
    switch (label) {
        .rule_declaration_here => try writer.writeAll(
            t("related_rule_declaration_here"),
        ),
    }
}

/// Localized frontend framing words ("error", "note", ...), for the
/// prefixes the sink and LSP write around rendered diagnostics.
pub fn severityLabel(severity: DiagnosticSeverity) []const u8 {
    return switch (severity) {
        .@"error" => t("label_error"),
        .warning => t("label_warning"),
    };
}

pub fn noteHeading() []const u8 {
    return t("label_note");
}

pub fn relatedHeading() []const u8 {
    return t("label_related");
}

/// The sink's "omitted N additional warning(s)" line body.
pub fn writeOmittedWarningsSummary(writer: anytype, count: usize) !void {
    try printT(writer, "omitted_warnings", .{count});
}

/// Notes and related spans are not rendered here: the CLI interleaves
/// them with source locations, LSP appends them as text, and the wasm
/// JSON carries them structurally.
pub fn renderDiagnostic(
    writer: anytype,
    diag: Diagnostic,
    line_separator: []const u8,
) !void {
    if (diag.kind == .omitted_diagnostics and
        diag.detail == .omitted_diagnostics)
    {
        try writeOmittedDiagnosticsSummary(
            writer,
            diag.detail.omitted_diagnostics.count,
        );
    } else {
        try writer.writeAll(diagnosticSummary(diag));
    }
    try writeNamedContextLine(
        writer,
        line_separator,
        "ctx_theorem",
        diag.theorem_name,
    );
    try writeNamedContextLine(
        writer,
        line_separator,
        "ctx_proof_block",
        diag.block_name,
    );
    try writeNamedContextLine(writer, line_separator, "ctx_line", diag.line_label);
    try writeNamedContextLine(writer, line_separator, "ctx_rule", diag.rule_name);
    try writeNamedContextLine(writer, line_separator, "ctx_name", diag.name);
    try writeNamedContextLine(
        writer,
        line_separator,
        "ctx_expected",
        diag.expected_name,
    );
    if (diag.phase) |phase| {
        try writeContextLine(
            writer,
            line_separator,
            "ctx_phase",
            .{diagnosticPhaseName(phase)},
        );
    }
    try writeDetailContextLines(writer, diag.detail, line_separator);
}

fn writeDetailContextLines(
    writer: anytype,
    detail: DiagnosticDetail,
    line_separator: []const u8,
) !void {
    switch (detail) {
        .none => {},
        .omitted_diagnostics => {},
        .unknown_math_token => |info| {
            try writeContextLine(
                writer,
                line_separator,
                "detail_token",
                .{info.token},
            );
        },
        .name_suggestion => |info| {
            try writeContextLine(
                writer,
                line_separator,
                "detail_did_you_mean",
                .{info.suggestion},
            );
        },
        .expected_char => |info| {
            try writeContextLine(
                writer,
                line_separator,
                "detail_expected_char",
                .{info.ch},
            );
        },
        .missing_binder_assignment => |info| {
            try writeContextLine(
                writer,
                line_separator,
                "detail_missing_binder",
                .{info.binder_name},
            );
            try writeContextLine(
                writer,
                line_separator,
                "detail_inference_path",
                .{inferencePathName(info.path)},
            );
        },
        .inference_failure => |info| {
            try writeContextLine(
                writer,
                line_separator,
                "detail_inference_path",
                .{inferencePathName(info.path)},
            );
            if (info.first_unsolved_binder_name) |binder_name| {
                try writeContextLine(
                    writer,
                    line_separator,
                    "detail_first_unsolved_binder",
                    .{binder_name},
                );
            }
        },
        .dep_violation => |info| {
            try writer.writeAll(line_separator);
            try writer.writeAll(t("detail_dep_violation_prefix"));
            try writeDepViolationSummary(writer, info);
            if (info.first_binding_text) |text| {
                try writer.writeAll(line_separator);
                try writeDepViolationAssignment(
                    writer,
                    info.first_arg_name,
                    info.first_arg_idx,
                    text,
                );
            }
            if (info.second_binding_text) |text| {
                try writer.writeAll(line_separator);
                try writeDepViolationAssignment(
                    writer,
                    info.second_arg_name,
                    info.second_arg_idx,
                    text,
                );
            }
        },
        .definition_body => |info| {
            try writeContextLine(
                writer,
                line_separator,
                "detail_declared_sort",
                .{info.declared_sort_name},
            );
            try writeContextLine(
                writer,
                line_separator,
                "detail_actual_sort",
                .{info.actual_sort_name},
            );
            try writeContextLine(
                writer,
                line_separator,
                "detail_body_deps",
                .{info.body_deps},
            );
            try writeContextLine(
                writer,
                line_separator,
                "detail_hidden_binders",
                .{info.hidden_binder_count},
            );
        },
        .missing_congruence_rule => |info| {
            try writer.writeAll(line_separator);
            try writer.writeAll(t("detail_missing_congruence_prefix"));
            try writeMissingCongruenceRuleSummary(writer, info);
            try writeNamedContextLine(
                writer,
                line_separator,
                "ctx_sort",
                info.sort_name,
            );
        },
        .hypothesis_ref => |info| {
            if (info.name) |name| {
                try writeContextLine(
                    writer,
                    line_separator,
                    "detail_hypothesis_ref_name",
                    .{name},
                );
            } else {
                try writeContextLine(
                    writer,
                    line_separator,
                    "detail_hypothesis_ref_index",
                    .{info.index},
                );
            }
        },
        .unused_parameter => |info| {
            try writeContextLine(
                writer,
                line_separator,
                "detail_parameter",
                .{info.parameter_name},
            );
        },
    }
}

fn writeContextLine(
    writer: anytype,
    line_separator: []const u8,
    comptime template: []const u8,
    args: anytype,
) !void {
    try writer.writeAll(line_separator);
    try printT(writer, template, args);
}

fn writeNamedContextLine(
    writer: anytype,
    line_separator: []const u8,
    comptime template: []const u8,
    value: ?[]const u8,
) !void {
    if (value) |actual| {
        try writeContextLine(writer, line_separator, template, .{actual});
    }
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
