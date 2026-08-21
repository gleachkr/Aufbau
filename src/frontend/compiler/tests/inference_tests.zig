const helpers = @import("./helpers.zig");
const std = helpers.std;
const mm0 = helpers.mm0;
const Compiler = helpers.Compiler;
const FrontendEnv = helpers.FrontendEnv;
const FrontendExpr = helpers.FrontendExpr;
const Expr = helpers.Expr;
const CompilerInference = helpers.CompilerInference;
const MM0Parser = helpers.MM0Parser;
const ProofScript = helpers.ProofScript;
const readProofCaseFile = helpers.readProofCaseFile;
const replaceOnceOwned = helpers.replaceOnceOwned;
const processAnnotatedMetadata = helpers.processAnnotatedMetadata;
const ruleArgIndex = helpers.ruleArgIndex;
const hasFreshenDecl = helpers.hasFreshenDecl;
const expectHasNote = helpers.expectHasNote;
const expectNoteText = helpers.expectNoteText;
const expectNoteStartsWith = helpers.expectNoteStartsWith;

test "multi-remainder inference handles a simple ACUI cover" {
    const allocator = std.testing.allocator;
    const mm0_src = try readProofCaseFile(
        allocator,
        "pass_acui_multi_remainder_infer",
        "mm0",
    );
    defer allocator.free(mm0_src);
    const proof_src = try readProofCaseFile(
        allocator,
        "pass_acui_multi_remainder_infer",
        "auf",
    );
    defer allocator.free(proof_src);

    var compiler = Compiler.initWithProof(allocator, mm0_src, proof_src);
    const mmb = try compiler.compileMmb(allocator);
    defer allocator.free(mmb);
    try mm0.verifyPair(allocator, mm0_src, mmb);
}

test "repeated ACUI remainder binder infers a principal witness" {
    const allocator = std.testing.allocator;
    const mm0_src = try readProofCaseFile(
        allocator,
        "pass_acui_repeated_joint_binder",
        "mm0",
    );
    defer allocator.free(mm0_src);
    const proof_src = try readProofCaseFile(
        allocator,
        "pass_acui_repeated_joint_binder",
        "auf",
    );
    defer allocator.free(proof_src);

    var compiler = Compiler.initWithProof(allocator, mm0_src, proof_src);
    const mmb = try compiler.compileMmb(allocator);
    defer allocator.free(mmb);
    try mm0.verifyPair(allocator, mm0_src, mmb);
    try std.testing.expectEqual(
        @as(usize, 0),
        compiler.warningDiagnostics().len,
    );
}

test "transparent ctx defs satisfy structural intervals" {
    const allocator = std.testing.allocator;
    const mm0_src = try readProofCaseFile(
        allocator,
        "pass_acui_transparent_ctx_reuse",
        "mm0",
    );
    defer allocator.free(mm0_src);
    const proof_src = try readProofCaseFile(
        allocator,
        "pass_acui_transparent_ctx_reuse",
        "auf",
    );
    defer allocator.free(proof_src);

    var compiler = Compiler.initWithProof(allocator, mm0_src, proof_src);
    const mmb = try compiler.compileMmb(allocator);
    defer allocator.free(mmb);
    try mm0.verifyPair(allocator, mm0_src, mmb);
    try std.testing.expectEqual(
        @as(usize, 0),
        compiler.warningDiagnostics().len,
    );
}

test "structural solver matches branch items by normalization" {
    const allocator = std.testing.allocator;
    const mm0_src = try readProofCaseFile(
        allocator,
        "pass_structural_normalized_item",
        "mm0",
    );
    defer allocator.free(mm0_src);
    const proof_src = try readProofCaseFile(
        allocator,
        "pass_structural_normalized_item",
        "auf",
    );
    defer allocator.free(proof_src);

    var compiler = Compiler.initWithProof(allocator, mm0_src, proof_src);
    const mmb = try compiler.compileMmb(allocator);
    defer allocator.free(mmb);
    try mm0.verifyPair(allocator, mm0_src, mmb);
    try std.testing.expectEqual(
        @as(usize, 0),
        compiler.warningDiagnostics().len,
    );
}

test "freshen repairs strict replay dep violation without normalize" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\--| @vars z w
        \\sort obj;
        \\provable sort wff;
        \\term iff (a b: wff): wff;
        \\term all {x: obj} (p: wff x): wff;
        \\term P (t: obj): wff;
        \\term sb (t: obj) {x: obj} (p: wff x): wff;
        \\term marker {x: obj}: wff;
        \\--| @relation wff iff iff_refl iff_trans iff_sym iff_mp
        \\axiom iff_refl (a: wff): $ iff a a $;
        \\axiom iff_trans (a b c: wff):
        \\  $ iff a b $ > $ iff b c $ > $ iff a c $;
        \\axiom iff_sym (a b: wff): $ iff a b $ > $ iff b a $;
        \\axiom iff_mp (a b: wff): $ iff a b $ > $ a $ > $ b $;
        \\--| @congr
        \\axiom all_congr {x: obj} (p q: wff x):
        \\  $ iff p q $ > $ iff (all x p) (all x q) $;
        \\--| @rewrite
        \\axiom sb_P (t: obj) {x: obj}: $ iff (sb t x (P x)) (P t) $;
        \\--| @alpha x y
        \\axiom all_alpha {x y: obj} (p: wff x y):
        \\  $ iff (all x p) (all y (sb y x p)) $;
        \\--| @freshen A x
        \\axiom use {x: obj} (A: wff): $ A $ > $ marker x $;
        \\theorem target {x: obj}: $ all x (P x) $ > $ marker x $;
    ;
    const proof_src =
        \\target
        \\------
        \\l1: $ marker x $ by use [#1]
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

test "prawitz alpha freshen proof compiles and verifies" {
    const allocator = std.testing.allocator;
    const mm0_src = try readProofCaseFile(
        allocator,
        "prawitz",
        "mm0",
    );
    defer allocator.free(mm0_src);
    const proof_src = try readProofCaseFile(
        allocator,
        "prawitz",
        "auf",
    );
    defer allocator.free(proof_src);

    var compiler = Compiler.initWithProof(allocator, mm0_src, proof_src);
    const mmb = try compiler.compileMmb(allocator);
    defer allocator.free(mmb);
    try mm0.verifyPair(allocator, mm0_src, mmb);
}

test "compiler reports freshen attempt notes on failure" {
    const allocator = std.testing.allocator;
    const mm0_src = try readProofCaseFile(
        allocator,
        "fail_alpha_freshen_opaque_theorem_arg",
        "mm0",
    );
    defer allocator.free(mm0_src);
    const proof_src = try readProofCaseFile(
        allocator,
        "fail_alpha_freshen_opaque_theorem_arg",
        "auf",
    );
    defer allocator.free(proof_src);

    var compiler = Compiler.initWithProof(allocator, mm0_src, proof_src);
    try std.testing.expectError(
        error.AlphaRewriteSearchFailed,
        compiler.compileMmb(allocator),
    );

    const diag = compiler.diagnostics.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.AlphaRewriteSearchFailed, diag.err);
    try std.testing.expectEqual(
        mm0.CompilerDiagnosticPhase.theorem_application,
        diag.phase.?,
    );
    try std.testing.expectEqual(@as(usize, 4), diag.noteSlice().len);
    try expectNoteText(
        "attempted @freshen for target binder g",
        diag.noteSlice()[0],
    );
    try expectNoteText(
        "freshen blocker binder: x",
        diag.noteSlice()[1],
    );
    try expectNoteStartsWith(
        "chosen replacement binder:",
        diag.noteSlice()[2],
    );
    try expectNoteText(
        "rewritten target still depends on blocker binder x",
        diag.noteSlice()[3],
    );
}

test "compiler pinpoints invalid @freshen binder kinds" {
    const allocator = std.testing.allocator;
    const mm0_src = try readProofCaseFile(
        allocator,
        "prawitz",
        "mm0",
    );
    defer allocator.free(mm0_src);

    const rewritten = try replaceOnceOwned(
        allocator,
        mm0_src,
        "@freshen g x",
        "@freshen x g",
    );
    defer allocator.free(rewritten);

    var compiler = Compiler.init(allocator, rewritten);
    try std.testing.expectError(
        error.FreshenTargetMustBeRegularBinder,
        compiler.check(),
    );

    const diag = compiler.diagnostics.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(
        error.FreshenTargetMustBeRegularBinder,
        diag.err,
    );
    const span = diag.span orelse return error.ExpectedDiagnosticSpan;
    try std.testing.expectEqualStrings(
        "@freshen x g",
        rewritten[span.start..span.end],
    );
}

test "compiler pinpoints invalid @alpha binder kinds" {
    const allocator = std.testing.allocator;
    const mm0_src = try readProofCaseFile(
        allocator,
        "prawitz",
        "mm0",
    );
    defer allocator.free(mm0_src);

    const rewritten = try replaceOnceOwned(
        allocator,
        mm0_src,
        "@alpha x y",
        "@alpha p y",
    );
    defer allocator.free(rewritten);

    var compiler = Compiler.init(allocator, rewritten);
    try std.testing.expectError(
        error.AlphaRequiresBoundBinders,
        compiler.check(),
    );

    const diag = compiler.diagnostics.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.AlphaRequiresBoundBinders, diag.err);
    const span = diag.span orelse return error.ExpectedDiagnosticSpan;
    try std.testing.expectEqualStrings(
        "@alpha p y",
        rewritten[span.start..span.end],
    );
}

test "prawitz metadata registers alpha and freshen annotations" {
    const allocator = std.testing.allocator;
    const mm0_src = try readProofCaseFile(
        allocator,
        "prawitz",
        "mm0",
    );
    defer allocator.free(mm0_src);

    var arena = std.heap.ArenaAllocator.init(allocator);
    defer arena.deinit();
    const meta = try processAnnotatedMetadata(arena.allocator(), mm0_src);

    const all_term_id = meta.env.term_names.get("all") orelse {
        return error.MissingTerm;
    };
    const ex_term_id = meta.env.term_names.get("ex") orelse {
        return error.MissingTerm;
    };
    const all_alpha_id = meta.env.getRuleId("all_alpha") orelse {
        return error.MissingRule;
    };
    const ex_alpha_id = meta.env.getRuleId("ex_alpha") orelse {
        return error.MissingRule;
    };

    const all_alpha_rules = meta.registry.getAlphaRules(all_term_id);
    try std.testing.expectEqual(@as(usize, 1), all_alpha_rules.len);
    try std.testing.expectEqual(all_alpha_id, all_alpha_rules[0].rule_id);

    const ex_alpha_rules = meta.registry.getAlphaRules(ex_term_id);
    try std.testing.expectEqual(@as(usize, 1), ex_alpha_rules.len);
    try std.testing.expectEqual(ex_alpha_id, ex_alpha_rules[0].rule_id);

    const all_alpha_rule = &meta.env.rules.items[all_alpha_id];
    try std.testing.expectEqual(
        try ruleArgIndex(all_alpha_rule, "x"),
        all_alpha_rules[0].old_idx,
    );
    try std.testing.expectEqual(
        try ruleArgIndex(all_alpha_rule, "y"),
        all_alpha_rules[0].new_idx,
    );

    const ex_alpha_rule = &meta.env.rules.items[ex_alpha_id];
    try std.testing.expectEqual(
        try ruleArgIndex(ex_alpha_rule, "x"),
        ex_alpha_rules[0].old_idx,
    );
    try std.testing.expectEqual(
        try ruleArgIndex(ex_alpha_rule, "y"),
        ex_alpha_rules[0].new_idx,
    );

    const all_intro_id = meta.env.getRuleId("all_intro") orelse {
        return error.MissingRule;
    };
    const all_intro_rule = &meta.env.rules.items[all_intro_id];
    const all_intro_freshen =
        meta.freshen_bindings.get(all_intro_id) orelse {
            return error.MissingFreshenDecl;
        };
    try std.testing.expectEqual(@as(usize, 1), all_intro_freshen.len);
    try std.testing.expect(hasFreshenDecl(
        all_intro_freshen,
        try ruleArgIndex(all_intro_rule, "g"),
        try ruleArgIndex(all_intro_rule, "x"),
    ));

    const ex_intro_id = meta.env.getRuleId("ex_intro") orelse {
        return error.MissingRule;
    };
    const ex_intro_rule = &meta.env.rules.items[ex_intro_id];
    const ex_intro_freshen = meta.freshen_bindings.get(ex_intro_id) orelse {
        return error.MissingFreshenDecl;
    };
    try std.testing.expectEqual(@as(usize, 1), ex_intro_freshen.len);
    try std.testing.expect(hasFreshenDecl(
        ex_intro_freshen,
        try ruleArgIndex(ex_intro_rule, "g"),
        try ruleArgIndex(ex_intro_rule, "x"),
    ));

    const ex_elim_id = meta.env.getRuleId("ex_elim") orelse {
        return error.MissingRule;
    };
    const ex_elim_rule = &meta.env.rules.items[ex_elim_id];
    const ex_elim_freshen = meta.freshen_bindings.get(ex_elim_id) orelse {
        return error.MissingFreshenDecl;
    };
    try std.testing.expectEqual(@as(usize, 2), ex_elim_freshen.len);
    try std.testing.expect(hasFreshenDecl(
        ex_elim_freshen,
        try ruleArgIndex(ex_elim_rule, "h"),
        try ruleArgIndex(ex_elim_rule, "x"),
    ));
    try std.testing.expect(hasFreshenDecl(
        ex_elim_freshen,
        try ruleArgIndex(ex_elim_rule, "c"),
        try ruleArgIndex(ex_elim_rule, "x"),
    ));
}

test "pass_alpha_freshen metadata registers alpha and freshen annotations" {
    const allocator = std.testing.allocator;
    const mm0_src = try readProofCaseFile(
        allocator,
        "pass_alpha_freshen",
        "mm0",
    );
    defer allocator.free(mm0_src);

    var arena = std.heap.ArenaAllocator.init(allocator);
    defer arena.deinit();
    const meta = try processAnnotatedMetadata(arena.allocator(), mm0_src);

    const all_term_id = meta.env.term_names.get("all") orelse {
        return error.MissingTerm;
    };
    const ex_term_id = meta.env.term_names.get("ex") orelse {
        return error.MissingTerm;
    };
    try std.testing.expectEqual(
        @as(usize, 1),
        meta.registry.getAlphaRules(all_term_id).len,
    );
    try std.testing.expectEqual(
        @as(usize, 1),
        meta.registry.getAlphaRules(ex_term_id).len,
    );

    const quantifier_rules = [_][]const u8{
        "all_left",
        "all_right",
        "ex_left",
        "ex_right",
    };
    for (quantifier_rules) |rule_name| {
        const rule_id = meta.env.getRuleId(rule_name) orelse {
            return error.MissingRule;
        };
        const rule = &meta.env.rules.items[rule_id];
        const decls = meta.freshen_bindings.get(rule_id) orelse {
            return error.MissingFreshenDecl;
        };
        try std.testing.expectEqual(@as(usize, 2), decls.len);
        try std.testing.expect(hasFreshenDecl(
            decls,
            try ruleArgIndex(rule, "g"),
            try ruleArgIndex(rule, "x"),
        ));
        try std.testing.expect(hasFreshenDecl(
            decls,
            try ruleArgIndex(rule, "d"),
            try ruleArgIndex(rule, "x"),
        ));
    }
}

test "joint structural cover conflicts fail before missing binders" {
    const allocator = std.testing.allocator;
    const mm0_src = try readProofCaseFile(
        allocator,
        "fail_acui_joint_cover_conflict",
        "mm0",
    );
    defer allocator.free(mm0_src);
    const proof_src = try readProofCaseFile(
        allocator,
        "fail_acui_joint_cover_conflict",
        "auf",
    );
    defer allocator.free(proof_src);

    var compiler = Compiler.initWithProof(allocator, mm0_src, proof_src);
    try std.testing.expectError(
        error.UnifyMismatch,
        compiler.compileMmb(allocator),
    );
}

test "multi-remainder ambiguity survives to final bindings" {
    const allocator = std.testing.allocator;
    const mm0_src = try readProofCaseFile(
        allocator,
        "pass_acui_multi_remainder_ambiguous",
        "mm0",
    );
    defer allocator.free(mm0_src);
    const proof_src = try readProofCaseFile(
        allocator,
        "pass_acui_multi_remainder_ambiguous",
        "auf",
    );
    defer allocator.free(proof_src);

    var compiler = Compiler.initWithProof(allocator, mm0_src, proof_src);
    const mmb = try compiler.compileMmb(allocator);
    defer allocator.free(mmb);
    try mm0.verifyPair(allocator, mm0_src, mmb);

    try std.testing.expectEqual(
        @as(usize, 1),
        compiler.warningDiagnostics().len,
    );
    try std.testing.expect(compiler.diagnostics.last_diagnostic == null);
}

test "compiler reports structural ambiguity without ACUI-only wording" {
    const allocator = std.testing.allocator;
    const mm0_src = try readProofCaseFile(
        allocator,
        "pass_acui_multi_remainder_ambiguous",
        "mm0",
    );
    defer allocator.free(mm0_src);
    const proof_src = try readProofCaseFile(
        allocator,
        "pass_acui_multi_remainder_ambiguous",
        "auf",
    );
    defer allocator.free(proof_src);

    var compiler = Compiler.initWithProof(allocator, mm0_src, proof_src);
    const mmb = try compiler.compileMmb(allocator);
    defer allocator.free(mmb);

    const warnings = compiler.warningDiagnostics();
    try std.testing.expectEqual(@as(usize, 1), warnings.len);
    const diag = warnings[0];
    try std.testing.expectEqual(
        mm0.CompilerDiagnosticSeverity.warning,
        diag.severity,
    );
    try std.testing.expectEqual(error.AmbiguousAcuiMatch, diag.err);
    try std.testing.expectEqual(.inference_failed, diag.kind);
    try std.testing.expectEqual(mm0.CompilerDiagnosticPhase.inference, diag.phase.?);
    try std.testing.expectEqualStrings(
        "the omitted parts of this rule application can be completed " ++
            "in more than one way",
        mm0.compilerDiagnosticSummary(diag),
    );
    switch (diag.detail) {
        .inference_failure => |detail| {
            try std.testing.expectEqual(.structural_solver, detail.path);
        },
        else => return error.ExpectedInferenceFailureDetail,
    }
    try std.testing.expectEqual(@as(usize, 4), diag.noteSlice().len);
    try expectNoteText(
        "inference path: structural matching",
        diag.noteSlice()[0],
    );
    try expectNoteStartsWith(
        "chosen bindings: ",
        diag.noteSlice()[1],
    );
    try expectNoteStartsWith(
        "alternative bindings: ",
        diag.noteSlice()[2],
    );
    try expectNoteText(
        "distinct solutions considered: 3",
        diag.noteSlice()[3],
    );
}

test "-Werror upgrades ambiguity warnings into errors" {
    const allocator = std.testing.allocator;
    const mm0_src = try readProofCaseFile(
        allocator,
        "pass_acui_multi_remainder_ambiguous",
        "mm0",
    );
    defer allocator.free(mm0_src);
    const proof_src = try readProofCaseFile(
        allocator,
        "pass_acui_multi_remainder_ambiguous",
        "auf",
    );
    defer allocator.free(proof_src);

    var compiler = Compiler.initWithProof(allocator, mm0_src, proof_src);
    compiler.diagnostics.warnings_as_errors = true;
    try std.testing.expectError(
        error.AmbiguousAcuiMatch,
        compiler.compileMmb(allocator),
    );

    const warnings = compiler.warningDiagnostics();
    try std.testing.expectEqual(@as(usize, 1), warnings.len);
    try std.testing.expectEqual(
        mm0.CompilerDiagnosticSeverity.warning,
        warnings[0].severity,
    );

    const diag = compiler.diagnostics.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(
        mm0.CompilerDiagnosticSeverity.@"error",
        diag.severity,
    );
    try std.testing.expectEqual(error.AmbiguousAcuiMatch, diag.err);
}

test "holey ACUI conclusion can still report ambiguity" {
    const allocator = std.testing.allocator;
    const mm0_src = try readProofCaseFile(
        allocator,
        "pass_hole_acui_ambiguous",
        "mm0",
    );
    defer allocator.free(mm0_src);
    const proof_src = try readProofCaseFile(
        allocator,
        "pass_hole_acui_ambiguous",
        "auf",
    );
    defer allocator.free(proof_src);

    var compiler = Compiler.initWithProof(allocator, mm0_src, proof_src);
    const mmb = try compiler.compileMmb(allocator);
    defer allocator.free(mmb);
    try mm0.verifyPair(allocator, mm0_src, mmb);

    const warnings = compiler.warningDiagnostics();
    try std.testing.expectEqual(@as(usize, 1), warnings.len);
    try std.testing.expectEqual(error.AmbiguousAcuiMatch, warnings[0].err);

    var werror_compiler = Compiler.initWithProof(
        allocator,
        mm0_src,
        proof_src,
    );
    werror_compiler.diagnostics.warnings_as_errors = true;
    try std.testing.expectError(
        error.AmbiguousAcuiMatch,
        werror_compiler.compileMmb(allocator),
    );
}

test "holey ACUI minimal residuals are warning-free" {
    const allocator = std.testing.allocator;
    const mm0_src = try readProofCaseFile(
        allocator,
        "pass_hole_acui_min_ctx",
        "mm0",
    );
    defer allocator.free(mm0_src);
    const proof_src = try readProofCaseFile(
        allocator,
        "pass_hole_acui_min_ctx",
        "auf",
    );
    defer allocator.free(proof_src);

    var compiler = Compiler.initWithProof(allocator, mm0_src, proof_src);
    const mmb = try compiler.compileMmb(allocator);
    defer allocator.free(mmb);
    try mm0.verifyPair(allocator, mm0_src, mmb);
    try std.testing.expectEqual(
        @as(usize, 0),
        compiler.warningDiagnostics().len,
    );
}

test "holey ACUI refs and visible structure disambiguate" {
    const allocator = std.testing.allocator;
    const mm0_src = try readProofCaseFile(
        allocator,
        "pass_hole_acui_disambiguate",
        "mm0",
    );
    defer allocator.free(mm0_src);
    const proof_src = try readProofCaseFile(
        allocator,
        "pass_hole_acui_disambiguate",
        "auf",
    );
    defer allocator.free(proof_src);

    var compiler = Compiler.initWithProof(allocator, mm0_src, proof_src);
    const mmb = try compiler.compileMmb(allocator);
    defer allocator.free(mmb);
    try mm0.verifyPair(allocator, mm0_src, mmb);
    try std.testing.expectEqual(
        @as(usize, 0),
        compiler.warningDiagnostics().len,
    );
}

test "compiler warns on unused theorem parameters" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\sort obj;
        \\provable sort wff;
        \\term P: wff;
        \\theorem unused_theorem {x: obj}: $ P $;
    ;

    var compiler = Compiler.init(std.testing.allocator, mm0_src);
    try compiler.check();

    const warnings = compiler.warningDiagnostics();
    try std.testing.expectEqual(@as(usize, 1), warnings.len);
    const diag = warnings[0];
    try std.testing.expectEqual(
        mm0.CompilerDiagnosticSeverity.warning,
        diag.severity,
    );
    try std.testing.expectEqual(.unused_theorem_parameter, diag.kind);
    try std.testing.expectEqual(error.UnusedTheoremParameter, diag.err);
    try std.testing.expectEqual(mm0.CompilerDiagnosticSource.mm0, diag.source);
    try std.testing.expectEqualStrings("unused_theorem", diag.name.?);
    try std.testing.expect(std.mem.indexOf(
        u8,
        mm0.compilerDiagnosticSummary(diag),
        "@vars",
    ) != null);
    switch (diag.detail) {
        .unused_parameter => |detail| {
            try std.testing.expectEqualStrings("x", detail.parameter_name);
        },
        else => return error.ExpectedUnusedParameterDetail,
    }
}

test "dependency-only theorem parameter use suppresses warning" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\sort obj;
        \\provable sort wff;
        \\theorem dep_only {x: obj} (p: wff x): $ p $;
    ;

    var compiler = Compiler.init(std.testing.allocator, mm0_src);
    try compiler.check();
    try std.testing.expectEqual(
        @as(usize, 0),
        compiler.warningDiagnostics().len,
    );
}

test "compiler warns on unused proof-local theorem parameters" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term P: wff;
        \\axiom hp: $ P $;
        \\theorem top: $ P $;
    ;
    const proof_src =
        \\lemma unused_local (q: wff): $ P $
        \\--------------------------------
        \\l1: $ P $ by hp []
        \\
        \\top
        \\---
        \\l1: $ P $ by hp []
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    const mmb = try compiler.compileMmb(std.testing.allocator);
    defer std.testing.allocator.free(mmb);
    try mm0.verifyPair(std.testing.allocator, mm0_src, mmb);

    const warnings = compiler.warningDiagnostics();
    try std.testing.expectEqual(@as(usize, 1), warnings.len);
    const diag = warnings[0];
    try std.testing.expectEqual(.unused_theorem_parameter, diag.kind);
    try std.testing.expectEqual(
        mm0.CompilerDiagnosticSource.proof,
        diag.source,
    );
    try std.testing.expectEqualStrings("unused_local", diag.name.?);
    switch (diag.detail) {
        .unused_parameter => |detail| {
            try std.testing.expectEqualStrings("q", detail.parameter_name);
        },
        else => return error.ExpectedUnusedParameterDetail,
    }
}

test "compiler warns on unused definition parameters" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\sort obj;
        \\provable sort wff;
        \\term P: wff;
        \\def unused_def {x: obj}: wff = $ P $;
    ;

    var compiler = Compiler.init(std.testing.allocator, mm0_src);
    try compiler.check();

    const warnings = compiler.warningDiagnostics();
    try std.testing.expectEqual(@as(usize, 1), warnings.len);
    const diag = warnings[0];
    try std.testing.expectEqual(.unused_definition_parameter, diag.kind);
    try std.testing.expectEqual(error.UnusedDefinitionParameter, diag.err);
    try std.testing.expect(std.mem.indexOf(
        u8,
        mm0.compilerDiagnosticSummary(diag),
        "remove",
    ) != null);
    switch (diag.detail) {
        .unused_parameter => |detail| {
            try std.testing.expectEqualStrings("x", detail.parameter_name);
        },
        else => return error.ExpectedUnusedParameterDetail,
    }
}

test "-Werror upgrades unused theorem parameter warnings into errors" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\sort obj;
        \\provable sort wff;
        \\term P: wff;
        \\theorem unused_theorem {x: obj}: $ P $;
    ;

    var compiler = Compiler.init(std.testing.allocator, mm0_src);
    compiler.diagnostics.warnings_as_errors = true;
    try std.testing.expectError(
        error.UnusedTheoremParameter,
        compiler.check(),
    );

    const warnings = compiler.warningDiagnostics();
    try std.testing.expectEqual(@as(usize, 1), warnings.len);
    try std.testing.expectEqual(
        mm0.CompilerDiagnosticSeverity.warning,
        warnings[0].severity,
    );

    const diag = compiler.diagnostics.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(
        mm0.CompilerDiagnosticSeverity.@"error",
        diag.severity,
    );
    try std.testing.expectEqual(.unused_theorem_parameter, diag.kind);
    try std.testing.expectEqual(error.UnusedTheoremParameter, diag.err);
}

test "robinson demo uses omitted binders across two ACUI sorts" {
    const allocator = std.testing.allocator;
    const mm0_src = try readProofCaseFile(
        allocator,
        "robinson",
        "mm0",
    );
    defer allocator.free(mm0_src);
    const proof_src = try readProofCaseFile(
        allocator,
        "robinson",
        "auf",
    );
    defer allocator.free(proof_src);

    var compiler = Compiler.initWithProof(allocator, mm0_src, proof_src);
    const mmb = try compiler.compileMmb(allocator);
    defer allocator.free(mmb);
    try mm0.verifyPair(allocator, mm0_src, mmb);
}

test "fully omitted robinson step emits ambiguity warning" {
    const allocator = std.testing.allocator;
    const mm0_src = try readProofCaseFile(
        allocator,
        "robinson",
        "mm0",
    );
    defer allocator.free(mm0_src);
    const proof_src =
        \\resolve_on_q
        \\------------
        \\step: $ ⊢ ((¬ p ∨ r) ∧ (p ∧ (¬ r))) $ by resolve(d := $ ¬ r $) [#1]
        \\
        \\robinson
        \\--------
        \\l1: $ ⊢ ((¬ p ∨ r) ∧ (p ∧ (¬ r))) $ by resolve [#1]
        \\l2: $ ⊢ (r ∧ (¬ r)) $ by resolve(d := $ ¬ r $) [l1]
        \\l3: $ ⊢ ⊥ $ by resolve(d := $ ⊤ $) [l2]
    ;

    var compiler = Compiler.initWithProof(allocator, mm0_src, proof_src);
    const mmb = try compiler.compileMmb(allocator);
    defer allocator.free(mmb);
    try mm0.verifyPair(allocator, mm0_src, mmb);
    try std.testing.expectEqual(
        @as(usize, 1),
        compiler.warningDiagnostics().len,
    );
}

test "or_left demo works with both contexts omitted" {
    const allocator = std.testing.allocator;
    const mm0_src = try readProofCaseFile(
        allocator,
        "gentzen",
        "mm0",
    );
    defer allocator.free(mm0_src);
    const proof_src = try readProofCaseFile(
        allocator,
        "gentzen",
        "auf",
    );
    defer allocator.free(proof_src);

    const needle = "by or_left(g := $ _ $)";
    const repl = "by or_left";
    const rewritten = if (std.mem.indexOf(u8, proof_src, needle)) |start|
        try std.fmt.allocPrint(
            allocator,
            "{s}{s}{s}",
            .{
                proof_src[0..start],
                repl,
                proof_src[start + needle.len ..],
            },
        )
    else
        try allocator.dupe(u8, proof_src);
    defer allocator.free(rewritten);

    var compiler = Compiler.initWithProof(allocator, mm0_src, rewritten);
    const mmb = try compiler.compileMmb(allocator);
    defer allocator.free(mmb);
    try mm0.verifyPair(allocator, mm0_src, mmb);
}

test "compiler points binding validation errors at explicit assignments" {
    const mm0_src =
        \\sort obj;
        \\provable sort wff;
        \\term top: wff;
        \\axiom use_obj (x: obj): $ top $;
        \\theorem target (x: obj): $ top $;
    ;
    const proof_src =
        \\target
        \\------
        \\l1: $ top $ by use_obj (x := $ top $)
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = MM0Parser.init(mm0_src, arena.allocator());
    var env = FrontendEnv.GlobalEnv.init(arena.allocator());
    var theorem = FrontendExpr.TheoremContext.init(arena.allocator());
    defer theorem.deinit();
    var theorem_vars = std.StringHashMap(*const Expr).init(
        arena.allocator(),
    );
    defer theorem_vars.deinit();

    const assertion = blk: {
        while (try parser.next()) |stmt| {
            try env.addStmt(stmt);
            switch (stmt) {
                .assertion => |value| {
                    if (std.mem.eql(u8, value.name, "target")) {
                        break :blk value;
                    }
                },
                else => {},
            }
        }
        return error.MissingAssertion;
    };
    const rule_id = env.getRuleId("use_obj") orelse return error.MissingRule;
    const rule = &env.rules.items[rule_id];

    try theorem.seedAssertion(assertion);
    const parsed_binding = try parser.parseFormulaText(" top ", &theorem_vars);
    const binding_expr = try theorem.internParsedExpr(parsed_binding);

    const binding_start = std.mem.indexOf(u8, proof_src, "(x := $ top $)") orelse {
        return error.MissingBindingText;
    };
    const binding_span = ProofScript.Span{
        .start = binding_start,
        .end = binding_start + "(x := $ top $)".len,
    };
    const line = ProofScript.ProofLine{
        .label = "l1",
        .label_span = .{ .start = 15, .end = 17 },
        .assertion = .{
            .text = " top ",
            .span = .{ .start = 19, .end = 26 },
        },
        .application = .{
            .rule_name = "use_obj",
            .rule_span = .{ .start = 30, .end = 37 },
            .binding_list_span = binding_span,
            .arg_bindings = &.{.{
                .name = "x",
                .name_span = .{ .start = binding_start + 1, .end = binding_start + 2 },
                .formula = .{
                    .text = " top ",
                    .span = .{ .start = 0, .end = 0 },
                },
                .span = binding_span,
            }},
            .refs_span = null,
            .refs = &.{},
            .span = .{ .start = 30, .end = proof_src.len },
        },
        .span = .{ .start = 15, .end = proof_src.len },
    };

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    var compiler_context = mm0.CompilerSupport.Context.CompilerContext.init(
        mm0_src,
        proof_src,
        compiler.debug,
        &compiler.diagnostics,
    );
    try std.testing.expectError(
        error.SortMismatch,
        CompilerInference.validateResolvedBindings(
            &compiler_context,
            &env,
            &theorem,
            null,
            null,
            assertion,
            line,
            rule,
            &.{binding_expr},
        ),
    );

    const diag = compiler.diagnostics.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.SortMismatch, diag.err);
    const span = diag.span orelse return error.ExpectedDiagnosticSpan;
    try std.testing.expectEqualStrings(
        "(x := $ top $)",
        proof_src[span.start..span.end],
    );
    try expectHasNote(
        diag,
        "it has sort 'wff', but the rule expects sort 'obj' here",
    );
}
