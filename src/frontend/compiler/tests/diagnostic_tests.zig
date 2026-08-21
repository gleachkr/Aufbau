const helpers = @import("./helpers.zig");
const std = helpers.std;
const mm0 = helpers.mm0;
const Compiler = helpers.Compiler;
const readProofCaseFile = helpers.readProofCaseFile;
const expectHasNote = helpers.expectHasNote;
const expectNoteText = helpers.expectNoteText;
const expectNoteStartsWith = helpers.expectNoteStartsWith;

test "binder assignment sort mismatch names both sorts" {
    const mm0_src =
        \\sort obj;
        \\provable sort wff;
        \\term top: wff;
        \\axiom use_obj (x: obj): $ top $;
        \\theorem target: $ top $;
    ;
    const proof_src =
        \\target
        \\------
        \\l1: $ top $ by use_obj (x := $ top $)
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    try std.testing.expectError(error.SortMismatch, compiler.check());

    const diag = compiler.diagnostics.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(.parse_binding, diag.kind);
    try std.testing.expectEqualStrings(
        "binder assignment has the wrong sort",
        mm0.compilerDiagnosticSummary(diag),
    );
    try expectHasNote(
        diag,
        "the assignment parses, but as sort 'wff'; this binder " ++
            "expects sort 'obj'",
    );
}

test "binder assignment inner sort mismatch gets a subexpression note" {
    const mm0_src =
        \\sort obj;
        \\provable sort wff;
        \\term top: wff;
        \\term pair (a b: obj): obj;
        \\axiom use_obj (x: obj): $ top $;
        \\theorem target: $ top $;
    ;
    const proof_src =
        \\target
        \\------
        \\l1: $ top $ by use_obj (x := $ pair top top $)
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    try std.testing.expectError(error.SortMismatch, compiler.check());

    const diag = compiler.diagnostics.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(.parse_binding, diag.kind);
    try expectHasNote(
        diag,
        "a subexpression here is used where a different sort is expected",
    );
}

test "binder assignment boundness mismatch says bound variable" {
    const mm0_src =
        \\sort obj;
        \\provable sort wff;
        \\term top: wff;
        \\term all_o {x: obj} (p: wff): wff;
        \\axiom alli {x: obj} (p: wff): $ all_o x p $;
        \\theorem target {x: obj} (y: obj): $ all_o x top $;
    ;
    const proof_src =
        \\target
        \\------
        \\l1: $ all_o x top $ by alli (x := $ y $)
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    try std.testing.expectError(error.BoundnessMismatch, compiler.check());

    const diag = compiler.diagnostics.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(.parse_binding, diag.kind);
    try std.testing.expectEqualStrings(
        "binder assignment must be a bound variable",
        mm0.compilerDiagnosticSummary(diag),
    );
    try expectHasNote(
        diag,
        "the assignment parses with the right sort, but this binder " ++
            "requires a single bound variable",
    );
}

test "non-provable proof line statement names its sort" {
    const mm0_src =
        \\sort obj;
        \\provable sort wff;
        \\term top: wff;
        \\axiom top_i: $ top $;
        \\theorem target (y: obj): $ top $;
    ;
    const proof_src =
        \\target
        \\------
        \\l1: $ y $ by top_i
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    try std.testing.expectError(error.NotProvable, compiler.check());

    const diag = compiler.diagnostics.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(.parse_assertion, diag.kind);
    try std.testing.expectEqualStrings(
        "the statement is not of a provable sort",
        mm0.compilerDiagnosticSummary(diag),
    );
    try expectHasNote(
        diag,
        "the statement parses, but as sort 'obj', which is not a " ++
            "provable sort",
    );
}

test "lemma header sort mismatch is not blamed on a rule" {
    const mm0_src =
        \\sort obj;
        \\provable sort wff;
        \\term top: wff;
        \\term pair (a b: obj): obj;
        \\axiom top_i: $ top $;
        \\theorem target: $ top $;
    ;
    const proof_src =
        \\target
        \\------
        \\l1: $ top $ by top_i
        \\
        \\lemma bad (w: obj): $ pair top top $
        \\------
        \\l1: $ top $ by top_i
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    try std.testing.expectError(error.SortMismatch, compiler.check());

    const diag = compiler.diagnostics.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(.parse_block_header, diag.kind);
    try std.testing.expectEqualStrings("bad", diag.block_name.?);
    try std.testing.expectEqualStrings(
        "a subexpression of the statement has the wrong sort",
        mm0.compilerDiagnosticSummary(diag),
    );
}

test "trailing math token is named and pinpointed" {
    const mm0_src =
        \\provable sort wff;
        \\term top: wff;
        \\axiom top_i: $ top $;
        \\theorem target: $ top $;
    ;
    const proof_src =
        \\target
        \\------
        \\l1: $ top /\ top $ by top_i
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    try std.testing.expectError(error.TrailingMathTokens, compiler.check());

    const diag = compiler.diagnostics.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqualStrings("/\\", diag.detail.unknown_math_token.token);
    const span = diag.span orelse return error.ExpectedDiagnosticSpan;
    try std.testing.expectEqualStrings("/\\", proof_src[span.start..span.end]);
    try expectHasNote(
        diag,
        "the expression to the left parses on its own; this token is " ++
            "not a notation that can extend it",
    );
}

test "missing semicolon names the expected character" {
    const mm0_src =
        \\provable sort wff;
        \\term top: wff;
        \\axiom top_i: $ top $
        \\theorem target: $ top $;
    ;

    var compiler = Compiler.init(std.testing.allocator, mm0_src);
    try std.testing.expectError(error.UnexpectedChar, compiler.check());

    const diag = compiler.diagnostics.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(@as(u8, ';'), diag.detail.expected_char.ch);
    try expectHasNote(
        diag,
        "usually a missing ';' at the end of the declaration " ++
            "before this point",
    );
}

test "lemma header math error is remapped onto the real source" {
    const mm0_src =
        \\provable sort wff;
        \\term top: wff;
        \\axiom top_i: $ top $;
        \\theorem target: $ top $;
    ;
    const proof_src =
        \\target
        \\------
        \\l1: $ top $ by top_i
        \\
        \\lemma bad: $ top zz $
        \\------
        \\l1: $ top $ by top_i
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    try std.testing.expectError(error.TrailingMathTokens, compiler.check());

    const diag = compiler.diagnostics.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(.parse_block_header, diag.kind);
    try std.testing.expectEqualStrings("zz", diag.detail.unknown_math_token.token);
    const span = diag.span orelse return error.ExpectedDiagnosticSpan;
    try std.testing.expectEqualStrings("zz", proof_src[span.start..span.end]);
}

test "unknown math token gets a not-declared hint note" {
    const mm0_src =
        \\provable sort wff;
        \\term top: wff;
        \\axiom top_i: $ top $;
        \\theorem target: $ top $;
    ;
    const proof_src =
        \\target
        \\------
        \\l1: $ zz $ by top_i
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    try std.testing.expectError(error.UnknownMathToken, compiler.check());

    const diag = compiler.diagnostics.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(.parse_assertion, diag.kind);
    try expectHasNote(
        diag,
        "the token is not a variable of this theorem, nor a term or " ++
            "notation of the theory",
    );
}

test "compiler preserves nested fallback first failure diagnostics" {
    const mm0_src =
        \\provable sort wff;
        \\term top: wff;
        \\term mid: wff;
        \\term bot: wff;
        \\axiom top_i: $ top $;
        \\axiom keep: $ top $ > $ top $;
        \\axiom need_bot: $ bot $ > $ top $;
        \\--| @fallback need_bot
        \\axiom need_mid: $ mid $ > $ top $;
        \\theorem target: $ top $;
    ;
    const proof_src =
        \\target
        \\------
        \\l1: $ top $ by keep [need_mid [top_i []]]
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    try std.testing.expectError(
        error.HypothesisMismatch,
        compiler.compileMmb(std.testing.allocator),
    );

    const diag = compiler.diagnostics.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.HypothesisMismatch, diag.err);
    try std.testing.expectEqual(.hypothesis_mismatch, diag.kind);
    try std.testing.expectEqual(
        mm0.CompilerDiagnosticPhase.theorem_application,
        diag.phase.?,
    );
    try std.testing.expectEqualStrings("target", diag.theorem_name.?);
    try std.testing.expectEqualStrings("l1", diag.line_label.?);
    try std.testing.expectEqualStrings("need_mid", diag.rule_name.?);
    try std.testing.expectEqualStrings("top_i", diag.name.?);
    const span = diag.span orelse return error.ExpectedDiagnosticSpan;
    try std.testing.expectEqualStrings("top_i []", proof_src[span.start..span.end]);
}

test "compiler pinpoints nested fallback cycles" {
    const mm0_src =
        \\provable sort wff;
        \\term top: wff;
        \\term bot: wff;
        \\axiom top_i: $ top $;
        \\axiom keep: $ top $ > $ top $;
        \\--| @fallback step_a
        \\axiom step_a: $ bot $ > $ top $;
        \\theorem target: $ top $;
    ;
    const proof_src =
        \\target
        \\------
        \\l1: $ top $ by keep [step_a [top_i []]]
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    try std.testing.expectError(error.FallbackCycle, compiler.compileMmb(
        std.testing.allocator,
    ));

    const diag = compiler.diagnostics.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.FallbackCycle, diag.err);
    try std.testing.expectEqual(.generic, diag.kind);
    try std.testing.expectEqual(
        mm0.CompilerDiagnosticPhase.theorem_application,
        diag.phase.?,
    );
    try std.testing.expectEqualStrings("target", diag.theorem_name.?);
    try std.testing.expectEqualStrings("l1", diag.line_label.?);
    try std.testing.expectEqualStrings("step_a", diag.rule_name.?);
    const span = diag.span orelse return error.ExpectedDiagnosticSpan;
    try std.testing.expectEqualStrings("step_a", proof_src[span.start..span.end]);
}

test "compiler pinpoints later nested rules" {
    const mm0_src =
        \\provable sort wff;
        \\term top: wff;
        \\axiom top_i: $ top $;
        \\axiom keep: $ top $ > $ top $;
        \\theorem first: $ top $;
        \\theorem later: $ top $;
    ;
    const proof_src =
        \\first
        \\-----
        \\l1: $ top $ by keep [later []]
        \\
        \\later
        \\-----
        \\l1: $ top $ by top_i []
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    try std.testing.expectError(
        error.RuleNotYetAvailable,
        compiler.compileMmb(std.testing.allocator),
    );

    const diag = compiler.diagnostics.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.RuleNotYetAvailable, diag.err);
    try std.testing.expectEqual(.rule_not_yet_available, diag.kind);
    try std.testing.expectEqualStrings("first", diag.theorem_name.?);
    try std.testing.expectEqualStrings("l1", diag.line_label.?);
    try std.testing.expectEqualStrings("later", diag.rule_name.?);
    const span = diag.span orelse return error.ExpectedDiagnosticSpan;
    try std.testing.expectEqualStrings("later", proof_src[span.start..span.end]);
}

test "compiler pinpoints duplicate proof labels" {
    const mm0_src =
        \\provable sort wff;
        \\term top: wff;
        \\axiom top_i: $ top $;
        \\theorem dup_label: $ top $;
    ;
    const proof_src =
        \\dup_label
        \\---------
        \\l1: $ top $ by top_i []
        \\l1: $ top $ by top_i []
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    try std.testing.expectError(error.DuplicateLabel, compiler.compileMmb(
        std.testing.allocator,
    ));

    const diag = compiler.diagnostics.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.DuplicateLabel, diag.err);
    try std.testing.expectEqualStrings("dup_label", diag.theorem_name.?);
    try std.testing.expectEqualStrings("l1", diag.line_label.?);
    try std.testing.expectEqualStrings("l1", diag.name.?);
    const span = diag.span orelse return error.ExpectedDiagnosticSpan;
    try std.testing.expectEqualStrings("l1", proof_src[span.start..span.end]);
}

test "compiler pinpoints unknown proof rules" {
    const mm0_src =
        \\provable sort wff;
        \\term top: wff;
        \\axiom top_i: $ top $;
        \\theorem bad_rule: $ top $;
    ;
    const proof_src =
        \\bad_rule
        \\--------
        \\l1: $ top $ by missing_rule []
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    try std.testing.expectError(error.UnknownRule, compiler.check());

    const diag = compiler.diagnostics.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.UnknownRule, diag.err);
    try std.testing.expectEqual(mm0.CompilerDiagnosticSource.proof, diag.source);
    try std.testing.expectEqualStrings("bad_rule", diag.theorem_name.?);
    try std.testing.expectEqualStrings("l1", diag.line_label.?);
    try std.testing.expectEqualStrings("missing_rule", diag.rule_name.?);
    const span = diag.span orelse return error.ExpectedDiagnosticSpan;
    try std.testing.expectEqualStrings(
        "missing_rule",
        proof_src[span.start..span.end],
    );
}

test "compiler distinguishes rules declared later in mm0 order" {
    const mm0_src =
        \\provable sort wff;
        \\term top: wff;
        \\axiom top_i: $ top $;
        \\theorem first: $ top $;
        \\theorem second: $ top $;
    ;
    const proof_src =
        \\first
        \\-----
        \\l1: $ top $ by second []
        \\
        \\second
        \\------
        \\l1: $ top $ by top_i []
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    try std.testing.expectError(
        error.RuleNotYetAvailable,
        compiler.check(),
    );

    const diag = compiler.diagnostics.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.RuleNotYetAvailable, diag.err);
    try std.testing.expectEqual(.rule_not_yet_available, diag.kind);
    try std.testing.expectEqual(mm0.CompilerDiagnosticSource.proof, diag.source);
    try std.testing.expectEqualStrings("first", diag.theorem_name.?);
    try std.testing.expectEqualStrings("l1", diag.line_label.?);
    try std.testing.expectEqualStrings("second", diag.rule_name.?);
    try std.testing.expectEqualStrings(
        "rule is declared later and is not yet available here",
        mm0.compilerDiagnosticSummary(diag),
    );
    try std.testing.expectEqual(
        mm0.CompilerDiagnosticPhase.theorem_application,
        diag.phase.?,
    );
    const span = diag.span orelse return error.ExpectedDiagnosticSpan;
    try std.testing.expectEqualStrings("second", proof_src[span.start..span.end]);
    try std.testing.expectEqual(@as(usize, 1), diag.noteSlice().len);
    try expectNoteText(
        "rule is declared later in the mm0 file",
        diag.noteSlice()[0],
    );
    try std.testing.expectEqual(@as(usize, 1), diag.relatedSlice().len);
    try std.testing.expectEqual(
        mm0.CompilerDiagnosticSource.mm0,
        diag.relatedSlice()[0].source,
    );
    try std.testing.expectEqual(
        mm0.CompilerRelatedLabel.rule_declaration_here,
        diag.relatedSlice()[0].label,
    );
    try std.testing.expectEqualStrings(
        "second",
        mm0_src[diag.relatedSlice()[0].span.start..diag.relatedSlice()[0].span.end],
    );
}

test "compiler retries theorem lines through fallback chains" {
    const mm0_src =
        \\provable sort wff;
        \\term and (a b: wff): wff;
        \\term fst (a b: wff): wff;
        \\term snd (a b: wff): wff;
        \\axiom and_elim_right (a b: wff): $ and a b $ > $ snd a b $;
        \\--| @fallback and_elim_right
        \\axiom and_elim_mid (a b: wff): $ and a b $ > $ fst a b $;
        \\--| @fallback and_elim_mid
        \\axiom and_elim (a b: wff): $ and a b $ > $ fst a b $;
        \\theorem use_fallback (a b: wff): $ and a b $ > $ snd a b $;
    ;
    const proof_src =
        \\use_fallback
        \\------------
        \\l1: $ snd a b $ by and_elim [#1]
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    const mmb = try compiler.compileMmb(std.testing.allocator);
    defer std.testing.allocator.free(mmb);
    try mm0.verifyPair(std.testing.allocator, mm0_src, mmb);
}

test "final mismatch reports reconciliation attempts" {
    const mm0_src =
        \\provable sort wff;
        \\term top: wff;
        \\term mid: wff;
        \\axiom top_i: $ top $;
        \\theorem need_mid: $ mid $;
    ;
    const proof_src =
        \\need_mid
        \\--------
        \\l1: $ top $ by top_i []
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    try std.testing.expectError(
        error.FinalLineMismatch,
        compiler.compileMmb(std.testing.allocator),
    );

    const diag = compiler.diagnostics.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.FinalLineMismatch, diag.err);
    try std.testing.expectEqual(.final_line_mismatch, diag.kind);
    try std.testing.expectEqual(
        mm0.CompilerDiagnosticPhase.final_reconciliation,
        diag.phase.?,
    );
    try std.testing.expectEqual(@as(usize, 4), diag.noteSlice().len);
    try expectNoteStartsWith(
        "the theorem concludes: ",
        diag.noteSlice()[0],
    );
    try expectNoteStartsWith(
        "the last line proves: ",
        diag.noteSlice()[1],
    );
    try expectNoteText(
        "the two do not match, even with definitions unfolded",
        diag.noteSlice()[2],
    );
    try expectNoteText(
        "nor after normalization",
        diag.noteSlice()[3],
    );
}

test "compiler reports fallback cycles when every candidate fails" {
    const mm0_src =
        \\provable sort wff;
        \\term top: wff;
        \\term mid: wff;
        \\--| @fallback step_a
        \\axiom step_a: $ top $;
        \\theorem bad_cycle: $ mid $;
    ;
    const proof_src =
        \\bad_cycle
        \\---------
        \\l1: $ mid $ by step_a []
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    try std.testing.expectError(error.FallbackCycle, compiler.compileMmb(
        std.testing.allocator,
    ));

    const diag = compiler.diagnostics.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.FallbackCycle, diag.err);
    try std.testing.expectEqualStrings("bad_cycle", diag.theorem_name.?);
    try std.testing.expectEqualStrings("l1", diag.line_label.?);
    try std.testing.expectEqualStrings("step_a", diag.rule_name.?);
}

test "compiler preserves the first fallback failure diagnostic" {
    const mm0_src =
        \\provable sort wff;
        \\term top: wff;
        \\term bot: wff;
        \\term mid: wff;
        \\axiom step_b: $ bot $;
        \\--| @fallback step_b
        \\axiom step_a: $ top $;
        \\theorem bad_fallback: $ mid $;
    ;
    const proof_src =
        \\bad_fallback
        \\------------
        \\l1: $ mid $ by step_a []
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    try std.testing.expectError(
        error.ConclusionMismatch,
        compiler.compileMmb(std.testing.allocator),
    );

    const diag = compiler.diagnostics.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.ConclusionMismatch, diag.err);
    try std.testing.expectEqual(mm0.CompilerDiagnosticSource.proof, diag.source);
    try std.testing.expectEqualStrings("bad_fallback", diag.theorem_name.?);
    try std.testing.expectEqualStrings("l1", diag.line_label.?);
    try std.testing.expectEqualStrings("step_a", diag.rule_name.?);
    try std.testing.expectEqual(@as(usize, 2), diag.noteSlice().len);
    try expectNoteText(
        "expected: top",
        diag.noteSlice()[0],
    );
    try expectNoteText(
        "actual: mid",
        diag.noteSlice()[1],
    );
}

test "compiler notes exhausted fallback chains for holey assertions" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\--| @hole _obj
        \\provable sort obj;
        \\term top: wff;
        \\term bot: wff;
        \\axiom step_b: $ bot $;
        \\--| @fallback step_b
        \\axiom step_a: $ top $;
        \\theorem bad_fallback: $ top $;
    ;
    const proof_src =
        \\bad_fallback
        \\------------
        \\l1: $ _obj $ by step_a []
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    try std.testing.expectError(
        error.HoleConclusionMismatch,
        compiler.compileMmb(std.testing.allocator),
    );

    const diag = compiler.diagnostics.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.HoleConclusionMismatch, diag.err);
    try std.testing.expectEqual(@as(usize, 2), diag.noteSlice().len);
    try expectNoteText(
        "hole _obj expected sort obj but matched wff",
        diag.noteSlice()[0],
    );
    try expectNoteText(
        "fallback chain exhausted for holey assertion; " ++
            "showing first candidate failure",
        diag.noteSlice()[1],
    );
    const note_span = diag.noteSlice()[1].span orelse {
        return error.ExpectedDiagnosticSpan;
    };
    try std.testing.expectEqualStrings(
        "_obj",
        proof_src[note_span.start..note_span.end],
    );
}

test "compiler pinpoints proof parser identifier errors" {
    const mm0_src =
        \\provable sort wff;
        \\term top: wff;
        \\theorem bad_parse: $ top $;
    ;
    const proof_src =
        \\bad_parse
        \\---------
        \\l1: $ top $ by [#1]
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    try std.testing.expectError(error.ExpectedIdentifier, compiler.check());

    const diag = compiler.diagnostics.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.ExpectedIdentifier, diag.err);
    try std.testing.expectEqual(mm0.CompilerDiagnosticSource.proof, diag.source);
    try std.testing.expectEqualStrings("bad_parse", diag.theorem_name.?);
    try std.testing.expectEqualStrings("bad_parse", diag.block_name.?);
    try std.testing.expectEqualStrings(
        "expected identifier",
        mm0.compilerDiagnosticSummary(diag),
    );
    const span = diag.span orelse return error.ExpectedDiagnosticSpan;
    try std.testing.expectEqualStrings("[", proof_src[span.start..span.end]);
}

test "compiler pinpoints missing proof block underlines" {
    const mm0_src =
        \\provable sort wff;
        \\term top: wff;
        \\theorem bad_parse: $ top $;
    ;
    const proof_src =
        \\bad_parse
        \\l1: $ top $ by keep []
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    try std.testing.expectError(
        error.ExpectedBlockUnderline,
        compiler.check(),
    );

    const diag = compiler.diagnostics.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.ExpectedBlockUnderline, diag.err);
    try std.testing.expectEqual(mm0.CompilerDiagnosticSource.proof, diag.source);
    try std.testing.expectEqualStrings("bad_parse", diag.theorem_name.?);
    try std.testing.expectEqualStrings("bad_parse", diag.block_name.?);
    try std.testing.expectEqualStrings(
        "expected underline after proof block header",
        mm0.compilerDiagnosticSummary(diag),
    );
    const span = diag.span orelse return error.ExpectedDiagnosticSpan;
    try std.testing.expectEqualStrings(
        "l1: $ top $ by keep []",
        proof_src[span.start..span.end],
    );
}

test "compiler check diagnostics are marked as mm0 source" {
    const mm0_src =
        \\provable sort wff;
        \\term foo: wff;
        \\axiom dup: $ foo $;
        \\axiom dup: $ foo $;
    ;

    var compiler = Compiler.init(std.testing.allocator, mm0_src);
    try std.testing.expectError(error.DuplicateRuleName, compiler.check());

    const diag = compiler.diagnostics.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.DuplicateRuleName, diag.err);
    try std.testing.expectEqual(mm0.CompilerDiagnosticSource.mm0, diag.source);
    try std.testing.expectEqualStrings("dup", diag.name.?);
    const span = diag.span orelse return error.ExpectedDiagnosticSpan;
    try std.testing.expectEqualStrings("dup", mm0_src[span.start..span.end]);
}

test "compiler pinpoints mm0 parser identifier errors" {
    const mm0_src =
        \\provable sort wff;
        \\theorem [: $ top $;
    ;

    var compiler = Compiler.init(std.testing.allocator, mm0_src);
    try std.testing.expectError(error.ExpectedIdent, compiler.check());

    const diag = compiler.diagnostics.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.ExpectedIdent, diag.err);
    try std.testing.expectEqual(mm0.CompilerDiagnosticSource.mm0, diag.source);
    try std.testing.expectEqualStrings(
        "expected identifier",
        mm0.compilerDiagnosticSummary(diag),
    );
    const span = diag.span orelse return error.ExpectedDiagnosticSpan;
    try std.testing.expectEqualStrings("[", mm0_src[span.start..span.end]);
}

test "compiler records inference diagnostics for omitted arguments" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term imp (a b: wff): wff; infixr imp: $->$ prec 25;
        \\axiom ax_keep (a b: wff): $ a $ > $ a -> b -> a $;
        \\theorem keep_bad (a b: wff): $ a $ > $ a -> b -> a $;
    ;
    const proof_src =
        \\keep_bad
        \\--------
        \\l1: $ b -> a -> b $ by ax_keep [#1]
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    // All binders are solvable from the stated conclusion (a := b, b := a),
    // so inference completes and defers the bad reference to theorem
    // application, which reports the mismatched hypothesis directly instead
    // of a generic inference failure.
    try std.testing.expectError(error.HypothesisMismatch, compiler.compileMmb(
        std.testing.allocator,
    ));
    const diag = compiler.diagnostics.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.HypothesisMismatch, diag.err);
    try std.testing.expectEqualStrings(
        "a cited premise does not match the hypothesis the rule expects there",
        mm0.compilerDiagnosticSummary(diag),
    );
    try std.testing.expectEqualStrings("keep_bad", diag.theorem_name.?);
    try std.testing.expectEqualStrings("l1", diag.line_label.?);
    try std.testing.expectEqualStrings("ax_keep", diag.rule_name.?);
    const span = diag.span orelse return error.ExpectedDiagnosticSpan;
    try std.testing.expectEqualStrings(
        "#1",
        proof_src[span.start..span.end],
    );
}

test "compiler pinpoints unknown math tokens in proof assertions" {
    const mm0_src =
        \\provable sort wff;
        \\term top: wff;
        \\axiom top_i: $ top $;
        \\theorem bad_token: $ top $;
    ;
    const proof_src =
        \\bad_token
        \\---------
        \\l1: $ bogus $ by top_i []
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    try std.testing.expectError(
        error.UnknownMathToken,
        compiler.compileMmb(std.testing.allocator),
    );

    const diag = compiler.diagnostics.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.UnknownMathToken, diag.err);
    try std.testing.expectEqual(mm0.CompilerDiagnosticSource.proof, diag.source);
    try std.testing.expectEqualStrings("bad_token", diag.theorem_name.?);
    try std.testing.expectEqualStrings("l1", diag.line_label.?);
    const span = diag.span orelse return error.ExpectedDiagnosticSpan;
    try std.testing.expectEqualStrings("bogus", proof_src[span.start..span.end]);
    switch (diag.detail) {
        .unknown_math_token => |detail| {
            try std.testing.expectEqualStrings("bogus", detail.token);
        },
        else => return error.ExpectedUnknownMathTokenDetail,
    }
}

test "compiler explains proof hole sort mismatches" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\--| @hole _obj
        \\provable sort obj;
        \\term top: wff;
        \\term thing: obj;
        \\axiom top_i: $ top $;
        \\theorem bad: $ top $;
    ;
    const proof_src =
        \\bad
        \\---
        \\l1: $ _obj $ by top_i []
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    try std.testing.expectError(
        error.HoleConclusionMismatch,
        compiler.compileMmb(std.testing.allocator),
    );

    const diag = compiler.diagnostics.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.HoleConclusionMismatch, diag.err);
    try std.testing.expectEqual(.conclusion_mismatch, diag.kind);
    try std.testing.expectEqualStrings(
        "the visible parts of the statement do not match the rule's conclusion",
        mm0.compilerDiagnosticSummary(diag),
    );
    const span = diag.span orelse return error.ExpectedDiagnosticSpan;
    try std.testing.expectEqualStrings("_obj", proof_src[span.start..span.end]);
    try std.testing.expectEqual(@as(usize, 1), diag.noteSlice().len);
    try expectNoteText(
        "hole _obj expected sort obj but matched wff",
        diag.noteSlice()[0],
    );
    const note_span = diag.noteSlice()[0].span orelse {
        return error.ExpectedDiagnosticSpan;
    };
    try std.testing.expectEqualStrings(
        "_obj",
        proof_src[note_span.start..note_span.end],
    );
}

test "compiler explains proof hole visible structure mismatches" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\--| @hole _wff
        \\provable sort wff;
        \\term imp (a b: wff): wff; infixr imp: $->$ prec 25;
        \\axiom ax_keep (a b: wff): $ a $ > $ a -> b -> a $;
        \\theorem bad (a b: wff): $ a $ > $ a -> b -> a $;
    ;
    const proof_src =
        \\bad
        \\---
        \\l1: $ b -> _wff $ by ax_keep (a := $ a $, b := $ b $) [#1]
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    try std.testing.expectError(
        error.HoleConclusionMismatch,
        compiler.compileMmb(std.testing.allocator),
    );

    const diag = compiler.diagnostics.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.HoleConclusionMismatch, diag.err);
    try std.testing.expectEqual(.conclusion_mismatch, diag.kind);
    try std.testing.expectEqualStrings(
        "the visible parts of the statement do not match the rule's conclusion",
        mm0.compilerDiagnosticSummary(diag),
    );
    const span = diag.span orelse return error.ExpectedDiagnosticSpan;
    try std.testing.expectEqualStrings(
        "$ b -> _wff $",
        proof_src[span.start..span.end],
    );
    try std.testing.expectEqual(@as(usize, 1), diag.noteSlice().len);
    try expectNoteText(
        "the visible parts of the statement do not match " ++
            "the rule's conclusion",
        diag.noteSlice()[0],
    );
    try std.testing.expect(diag.noteSlice()[0].span == null);
}

test "compiler explains proof holes that leave binders unsolved" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\--| @hole _wff
        \\provable sort wff;
        \\axiom ax_vacuous (a b: wff): $ a $ > $ a $;
        \\theorem bad (a b: wff): $ a $ > $ a $;
    ;
    const proof_src =
        \\bad
        \\---
        \\l1: $ _wff $ by ax_vacuous [#1]
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    try std.testing.expectError(
        error.MissingBinderAssignment,
        compiler.compileMmb(std.testing.allocator),
    );

    const diag = compiler.diagnostics.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.MissingBinderAssignment, diag.err);
    try std.testing.expectEqual(.missing_binder_assignment, diag.kind);
    try std.testing.expectEqualStrings("b", diag.name.?);
    const span = diag.span orelse return error.ExpectedDiagnosticSpan;
    try std.testing.expectEqualStrings("_wff", proof_src[span.start..span.end]);
    switch (diag.detail) {
        .missing_binder_assignment => |detail| {
            try std.testing.expectEqualStrings("b", detail.binder_name);
            try std.testing.expectEqual(.holey_surface_match, detail.path);
        },
        else => return error.ExpectedMissingBinderDetail,
    }
    try std.testing.expectEqual(@as(usize, 1), diag.noteSlice().len);
    try expectNoteText(
        "holey assertion left binder b unsolved",
        diag.noteSlice()[0],
    );
    const note_span = diag.noteSlice()[0].span orelse {
        return error.ExpectedDiagnosticSpan;
    };
    try std.testing.expectEqualStrings(
        "_wff",
        proof_src[note_span.start..note_span.end],
    );
}

test "compiler reports which binder assignment is missing" {
    const mm0_src =
        \\provable sort wff;
        \\axiom ax_vacuous (a b: wff): $ a $ > $ a $;
        \\theorem vacuous (a b: wff): $ a $ > $ a $;
    ;
    const proof_src =
        \\vacuous
        \\--------
        \\l1: $ a $ by ax_vacuous (a := $ a $) [#1]
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    try std.testing.expectError(
        error.MissingBinderAssignment,
        compiler.compileMmb(std.testing.allocator),
    );

    const diag = compiler.diagnostics.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.MissingBinderAssignment, diag.err);
    try std.testing.expectEqual(.missing_binder_assignment, diag.kind);
    try std.testing.expectEqual(mm0.CompilerDiagnosticPhase.inference, diag.phase.?);
    try std.testing.expectEqualStrings("vacuous", diag.theorem_name.?);
    try std.testing.expectEqualStrings("l1", diag.line_label.?);
    try std.testing.expectEqualStrings("ax_vacuous", diag.rule_name.?);
    try std.testing.expectEqualStrings("b", diag.name.?);
    const span = diag.span orelse return error.ExpectedDiagnosticSpan;
    try std.testing.expectEqualStrings(
        "(a := $ a $)",
        proof_src[span.start..span.end],
    );
    switch (diag.detail) {
        .missing_binder_assignment => |detail| {
            try std.testing.expectEqualStrings("b", detail.binder_name);
            try std.testing.expectEqual(.strict_replay, detail.path);
        },
        else => return error.ExpectedMissingBinderDetail,
    }
    try std.testing.expectEqual(@as(usize, 1), diag.noteSlice().len);
    try expectNoteText(
        "explicit bindings: a = a",
        diag.noteSlice()[0],
    );
}

test "inference failure names the clashing operator in the conclusion" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term imp (a b: wff): wff; infixr imp: $->$ prec 25;
        \\term an (a b: wff): wff; infixl an: $&$ prec 30;
        \\axiom ax_keep (a b: wff): $ a $ > $ a -> b -> a $;
        \\theorem bad (a b: wff): $ a $ > $ a & b $;
    ;
    const proof_src =
        \\bad
        \\---
        \\l1: $ a & b $ by ax_keep [#1]
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    try std.testing.expectError(
        error.TermMismatch,
        compiler.compileMmb(std.testing.allocator),
    );

    const diag = compiler.diagnostics.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.TermMismatch, diag.err);
    try std.testing.expectEqual(.inference_failed, diag.kind);
    try std.testing.expectEqualStrings(
        "the statement or a cited premise does not have the shape " ++
            "this rule requires",
        mm0.compilerDiagnosticSummary(diag),
    );
    try std.testing.expect(diag.noteSlice().len >= 2);
    try expectNoteText(
        "the statement does not match the rule's conclusion",
        diag.noteSlice()[0],
    );
    try expectNoteText(
        "the rule requires 'imp' at the mismatch, but found: a & b",
        diag.noteSlice()[1],
    );
}

test "inference failure reports a rule variable needing two values" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term imp (a b: wff): wff; infixr imp: $->$ prec 25;
        \\axiom ax_dup (a b: wff): $ a -> a -> b $;
        \\theorem bad (p q r: wff): $ p -> q -> r $;
    ;
    const proof_src =
        \\bad
        \\---
        \\l1: $ p -> q -> r $ by ax_dup []
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    try std.testing.expectError(
        error.UnifyMismatch,
        compiler.compileMmb(std.testing.allocator),
    );

    const diag = compiler.diagnostics.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.UnifyMismatch, diag.err);
    try std.testing.expectEqualStrings(
        "the statement and cited premises could not be matched " ++
            "against this rule",
        mm0.compilerDiagnosticSummary(diag),
    );
    try std.testing.expect(diag.noteSlice().len >= 4);
    try expectNoteText(
        "the statement does not match the rule's conclusion",
        diag.noteSlice()[0],
    );
    try expectNoteText(
        "rule variable a would need two different values",
        diag.noteSlice()[1],
    );
    try expectNoteText(
        "already matched: p",
        diag.noteSlice()[2],
    );
    try expectNoteText(
        "at the mismatch: q",
        diag.noteSlice()[3],
    );
}

test "inference failure names the mismatching cited premise" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term imp (a b: wff): wff; infixr imp: $->$ prec 25;
        \\term an (a b: wff): wff; infixl an: $&$ prec 30;
        \\axiom cut2 (a b: wff): $ a & a $ > $ b $;
        \\theorem bad (p q: wff): $ p -> p $ > $ q $;
    ;
    const proof_src =
        \\bad
        \\---
        \\l1: $ q $ by cut2 [#1]
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    try std.testing.expectError(
        error.TermMismatch,
        compiler.compileMmb(std.testing.allocator),
    );

    const diag = compiler.diagnostics.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.TermMismatch, diag.err);
    try std.testing.expect(diag.noteSlice().len >= 2);
    try expectNoteText(
        "cited premise 1 does not match hypothesis 1 of the rule",
        diag.noteSlice()[0],
    );
    try expectNoteText(
        "the rule requires 'an' at the mismatch, but found: p -> p",
        diag.noteSlice()[1],
    );
}

// Shared ACUI sequent theory for the structural-solver clash tests: rules
// with ctx binders route inference through the structural solver, whose
// failures used to surface with no clash-site notes at all.
const acui_clash_mm0_prefix =
    \\delimiter $ ( ) $;
    \\provable sort wff;
    \\sort ctx;
    \\term iff (a b: wff): wff;
    \\infixr iff: $<->$ prec 20;
    \\term ctx_eq (g h: ctx): wff;
    \\term emp: ctx;
    \\--| @acui ctx_assoc ctx_comm emp ctx_idem
    \\term join (g h: ctx): ctx;
    \\infixl join: $,$ prec 5;
    \\term hyp (a: wff): ctx;
    \\coercion hyp: wff > ctx;
    \\term seq (g d: ctx): wff;
    \\infixl seq: $==>$ prec 0;
    \\--| @relation wff iff iff_refl iff_trans iff_sym iff_mp
    \\axiom iff_refl (a: wff): $ a <-> a $;
    \\axiom iff_trans (a b c: wff):
    \\  $ a <-> b $ > $ b <-> c $ > $ a <-> c $;
    \\axiom iff_sym (a b: wff): $ a <-> b $ > $ b <-> a $;
    \\axiom iff_mp (a b: wff): $ a <-> b $ > $ a $ > $ b $;
    \\--| @relation ctx ctx_eq ctx_refl ctx_trans ctx_sym _
    \\axiom ctx_refl (g: ctx): $ ctx_eq g g $;
    \\axiom ctx_trans (g h i: ctx):
    \\  $ ctx_eq g h $ > $ ctx_eq h i $ > $ ctx_eq g i $;
    \\axiom ctx_sym (g h: ctx): $ ctx_eq g h $ > $ ctx_eq h g $;
    \\axiom ctx_assoc (g h i: ctx):
    \\  $ ctx_eq ((g , h) , i) (g , (h , i)) $;
    \\axiom ctx_comm (g h: ctx): $ ctx_eq (g , h) (h , g) $;
    \\axiom ctx_idem (g: ctx): $ ctx_eq (g , g) g $;
    \\axiom ctx_unit (g: ctx): $ ctx_eq (emp , g) g $;
    \\--| @congr
    \\axiom seq_congr (g1 g2 d1 d2: ctx):
    \\  $ ctx_eq g1 g2 $ > $ ctx_eq d1 d2 $ > $ (g1 ==> d1) <-> (g2 ==> d2) $;
    \\axiom balance (g h: ctx): $ g , h ==> g , h $;
    \\
;

test "structural solver failure locates the conclusion clash" {
    const mm0_src = acui_clash_mm0_prefix ++
        \\theorem bad_concl (x: wff): $ x <-> x $;
    ;
    const proof_src =
        \\bad_concl
        \\---------
        \\l1: $ x <-> x $ by balance []
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    try std.testing.expectError(
        error.UnifyMismatch,
        compiler.compileMmb(std.testing.allocator),
    );

    const diag = compiler.diagnostics.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.UnifyMismatch, diag.err);
    switch (diag.detail) {
        .inference_failure => |detail| {
            try std.testing.expectEqual(.structural_solver, detail.path);
        },
        else => return error.ExpectedInferenceFailureDetail,
    }
    try std.testing.expect(diag.noteSlice().len >= 2);
    try expectNoteText(
        "the statement does not match the rule's conclusion",
        diag.noteSlice()[0],
    );
    try expectNoteText(
        "no way of filling in the rule's variables makes them match",
        diag.noteSlice()[1],
    );
}

test "structural solver failure names the mismatching cited premise" {
    const mm0_src = acui_clash_mm0_prefix ++
        \\theorem bad_prem (x: wff):
        \\  $ x <-> x $ > $ (x ==> x) <-> (x ==> x) $;
    ;
    const proof_src =
        \\bad_prem
        \\--------
        \\l1: $ (x ==> x) <-> (x ==> x) $ by seq_congr [#1, #1]
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    try std.testing.expectError(
        error.UnifyMismatch,
        compiler.compileMmb(std.testing.allocator),
    );

    const diag = compiler.diagnostics.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.UnifyMismatch, diag.err);
    switch (diag.detail) {
        .inference_failure => |detail| {
            try std.testing.expectEqual(.structural_solver, detail.path);
        },
        else => return error.ExpectedInferenceFailureDetail,
    }
    try std.testing.expect(diag.noteSlice().len >= 3);
    try expectNoteText(
        "cited premise 1 does not match hypothesis 1 of the rule",
        diag.noteSlice()[0],
    );
    try expectNoteText(
        "no way of filling in the rule's variables makes them match",
        diag.noteSlice()[1],
    );
    try expectNoteText(
        "the cited premise proves: x <-> x",
        diag.noteSlice()[2],
    );
}

test "compiler reports conflicting dependency binders by name" {
    const mm0_src =
        \\provable sort wff;
        \\sort obj;
        \\term rel {x y: obj}: wff;
        \\axiom rel_ax {x y: obj}: $ rel x y $;
        \\theorem rel_bad {z: obj}: $ rel z z $;
    ;
    const proof_src =
        \\rel_bad
        \\-------
        \\l1: $ rel z z $ by rel_ax (x := $ z $, y := $ z $) []
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    try std.testing.expectError(
        error.DepViolation,
        compiler.compileMmb(std.testing.allocator),
    );

    const diag = compiler.diagnostics.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.DepViolation, diag.err);
    try std.testing.expectEqual(.generic, diag.kind);
    try std.testing.expectEqual(
        mm0.CompilerDiagnosticPhase.theorem_application,
        diag.phase.?,
    );
    try std.testing.expectEqualStrings(
        "binder assignments violate the rule's dependency constraints",
        mm0.compilerDiagnosticSummary(diag),
    );
    switch (diag.detail) {
        .dep_violation => |detail| {
            try std.testing.expectEqual(@as(usize, 0), detail.first_arg_idx);
            try std.testing.expectEqual(@as(usize, 1), detail.second_arg_idx);
            try std.testing.expectEqualStrings("x", detail.first_arg_name.?);
            try std.testing.expectEqualStrings("y", detail.second_arg_name.?);
            try std.testing.expectEqual(@as(u55, 1), detail.first_deps);
            try std.testing.expectEqual(@as(u55, 1), detail.second_deps);
            try std.testing.expect(detail.first_bound);
            try std.testing.expect(detail.second_bound);
            try std.testing.expect(detail.first_rule_bound);
            try std.testing.expect(detail.second_rule_bound);
            try std.testing.expectEqualStrings(
                "z",
                detail.first_binding_text.?,
            );
            try std.testing.expectEqualStrings(
                "z",
                detail.second_binding_text.?,
            );
        },
        else => return error.ExpectedDepViolationDetail,
    }
}

test "compiler explains one-sided dependency violations logically" {
    const mm0_src =
        \\provable sort wff;
        \\sort obj;
        \\term rel {x y: obj}: wff;
        \\axiom gen {x: obj} (p: wff): $ p $;
        \\theorem gen_bad {z: obj}: $ rel z z $;
    ;
    const proof_src =
        \\gen_bad
        \\-------
        \\l1: $ rel z z $ by gen (x := $ z $, p := $ rel z z $) []
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    try std.testing.expectError(
        error.DepViolation,
        compiler.compileMmb(std.testing.allocator),
    );

    const diag = compiler.diagnostics.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.DepViolation, diag.err);
    switch (diag.detail) {
        .dep_violation => |detail| {
            try std.testing.expectEqualStrings("x", detail.first_arg_name.?);
            try std.testing.expectEqualStrings("p", detail.second_arg_name.?);
            try std.testing.expect(detail.first_rule_bound);
            try std.testing.expect(!detail.second_rule_bound);
            try std.testing.expectEqualStrings(
                "z",
                detail.first_binding_text.?,
            );
            try std.testing.expectEqualStrings(
                "rel z z",
                detail.second_binding_text.?,
            );
        },
        else => return error.ExpectedDepViolationDetail,
    }
}

test "compiler reports checked-ir dep violations before emission" {
    const mm0_src = try readProofCaseFile(
        std.testing.allocator,
        "fail_hidden_dummy_dep",
        "mm0",
    );
    defer std.testing.allocator.free(mm0_src);
    const proof_src = try readProofCaseFile(
        std.testing.allocator,
        "fail_hidden_dummy_dep",
        "auf",
    );
    defer std.testing.allocator.free(proof_src);

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    try std.testing.expectError(
        error.DepViolation,
        compiler.compileMmb(std.testing.allocator),
    );

    const diag = compiler.diagnostics.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.DepViolation, diag.err);
    try std.testing.expectEqual(.generic, diag.kind);
    try std.testing.expectEqual(
        mm0.CompilerDiagnosticPhase.theorem_application,
        diag.phase.?,
    );
    try std.testing.expectEqualStrings("nat_rec_dep_ty", diag.theorem_name.?);
    try std.testing.expectEqualStrings("l7", diag.line_label.?);
    try std.testing.expectEqualStrings("sb_ty_congr", diag.rule_name.?);
    try std.testing.expectEqualStrings(
        "binder assignments violate the rule's dependency constraints",
        mm0.compilerDiagnosticSummary(diag),
    );
    switch (diag.detail) {
        .dep_violation => |detail| {
            try std.testing.expect(detail.first_arg_idx < detail.second_arg_idx);
            try std.testing.expect(detail.first_arg_name != null);
            try std.testing.expect(detail.second_arg_name != null);
            try std.testing.expect(detail.first_bound or detail.second_bound);
            try std.testing.expect(detail.first_deps != 0);
            try std.testing.expect(detail.second_deps != 0);
        },
        else => return error.ExpectedDepViolationDetail,
    }
}

test "compiler rejects def bodies that leave hidden binders free" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\sort obj;
        \\def bad {.x: obj}: obj = $ x $;
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        "",
    );
    try std.testing.expectError(
        error.DepViolation,
        compiler.compileMmb(std.testing.allocator),
    );

    const diag = compiler.diagnostics.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.DepViolation, diag.err);
    try std.testing.expectEqual(.invalid_definition_body, diag.kind);
    try std.testing.expectEqualStrings(
        "definition body has free variables that the result type does not declare",
        mm0.compilerDiagnosticSummary(diag),
    );
    const span = diag.span orelse return error.ExpectedDiagnosticSpan;
    try std.testing.expectEqualStrings("bad", mm0_src[span.start..span.end]);
    switch (diag.detail) {
        .definition_body => |detail| {
            try std.testing.expectEqualStrings("obj", detail.declared_sort_name);
            try std.testing.expectEqualStrings("obj", detail.actual_sort_name);
            try std.testing.expectEqual(
                @as(usize, 1),
                detail.hidden_binder_count,
            );
            try std.testing.expect(detail.body_deps != 0);
        },
        else => return error.ExpectedDefinitionBodyDetail,
    }
    try std.testing.expectEqual(@as(usize, 2), diag.noteSlice().len);
    try expectNoteText(
        "definition bodies are checked before the def unify stream runs",
        diag.noteSlice()[0],
    );
    try expectNoteText(
        "every free variable of the body must be declared as a " ++
            "dependency of the result type",
        diag.noteSlice()[1],
    );
}

test "def result-type deps cover body free variables" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\sort tm;
        \\term sb {x: tm} (e: tm x) (a: tm): tm;
        \\def selfsub {x: tm} (e: tm x) (a: tm x): tm x = $ sb x e a $;
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        "",
    );
    const mmb = try compiler.compileMmb(std.testing.allocator);
    defer std.testing.allocator.free(mmb);
}

test "compiler rejects def bodies freed only by a term's result deps" {
    // `fresh x e` counts as mentioning `x` via fresh's result-type
    // dependency, so a bare `tm` result cannot cover the body.
    const mm0_src =
        \\delimiter $ ( ) $;
        \\sort tm;
        \\term fresh {x: tm} (e: tm): tm x;
        \\def bad {x: tm} (e: tm): tm = $ fresh x e $;
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        "",
    );
    try std.testing.expectError(
        error.DepViolation,
        compiler.compileMmb(std.testing.allocator),
    );
}

test "parser rejects result-type deps naming a hidden binder" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\sort tm;
        \\term pair (a b: tm): tm;
        \\def bad {.y: tm} (a: tm): tm y = $ pair a a $;
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        "",
    );
    try std.testing.expectError(
        error.ResultDependencyOnDummy,
        compiler.compileMmb(std.testing.allocator),
    );
}
