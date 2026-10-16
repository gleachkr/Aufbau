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
const readProofCase = helpers.readProofCase;
const replaceOnceOwned = helpers.replaceOnceOwned;
const processAnnotatedMetadata = helpers.processAnnotatedMetadata;
const ruleArgIndex = helpers.ruleArgIndex;
const hasFreshenDecl = helpers.hasFreshenDecl;
const expectHasNote = helpers.expectHasNote;
const expectNoteText = helpers.expectNoteText;
const expectNoteStartsWith = helpers.expectNoteStartsWith;

test "multi-remainder inference handles a simple ACUI cover" {
    const allocator = std.testing.allocator;
    const mm0_src = try readProofCase(
        allocator,
        "pass_acui_multi_remainder_infer",
        "mm0",
    );
    defer allocator.free(mm0_src);
    const proof_src = try readProofCase(
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
    const mm0_src = try readProofCase(
        allocator,
        "pass_acui_repeated_joint_binder",
        "mm0",
    );
    defer allocator.free(mm0_src);
    const proof_src = try readProofCase(
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
    const mm0_src = try readProofCase(
        allocator,
        "pass_acui_transparent_ctx_reuse",
        "mm0",
    );
    defer allocator.free(mm0_src);
    const proof_src = try readProofCase(
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
    const mm0_src = try readProofCase(
        allocator,
        "pass_structural_normalized_item",
        "mm0",
    );
    defer allocator.free(mm0_src);
    const proof_src = try readProofCase(
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
        \\axiom all_alpha {x y: obj} (p: wff x):
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
    const mm0_src = try readProofCase(
        allocator,
        "prawitz",
        "mm0",
    );
    defer allocator.free(mm0_src);
    const proof_src = try readProofCase(
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
    const mm0_src = try readProofCase(
        allocator,
        "fail_alpha_freshen_opaque_theorem_arg",
        "mm0",
    );
    defer allocator.free(mm0_src);
    const proof_src = try readProofCase(
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
    const mm0_src = try readProofCase(
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
    const mm0_src = try readProofCase(
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
    const mm0_src = try readProofCase(
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
    const mm0_src = try readProofCase(
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
    const mm0_src = try readProofCase(
        allocator,
        "fail_acui_joint_cover_conflict",
        "mm0",
    );
    defer allocator.free(mm0_src);
    const proof_src = try readProofCase(
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
    const mm0_src = try readProofCase(
        allocator,
        "pass_acui_multi_remainder_ambiguous",
        "mm0",
    );
    defer allocator.free(mm0_src);
    const proof_src = try readProofCase(
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
    const mm0_src = try readProofCase(
        allocator,
        "pass_acui_multi_remainder_ambiguous",
        "mm0",
    );
    defer allocator.free(mm0_src);
    const proof_src = try readProofCase(
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

test "uncoupled ACUI cover product is resolved without enumeration" {
    // `frame7` spreads two members over seven context binders (too many for
    // the positional match, so the structural solver runs): 127^2 covers.
    // The solver used to materialize every cover and compare each against
    // all the others; the closed form reports the same count, chosen cover
    // (each member in the last binder alone), and alternative from the
    // per-member choice lists.
    const allocator = std.testing.allocator;
    const mm0_src = try readProofCase(
        allocator,
        "pass_acui_cover_product_ambiguous",
        "mm0",
    );
    defer allocator.free(mm0_src);
    const proof_src = try readProofCase(
        allocator,
        "pass_acui_cover_product_ambiguous",
        "auf",
    );
    defer allocator.free(proof_src);

    var compiler = Compiler.initWithProof(allocator, mm0_src, proof_src);
    const mmb = try compiler.compileMmb(allocator);
    defer allocator.free(mmb);
    try mm0.verifyPair(allocator, mm0_src, mmb);

    const warnings = compiler.warningDiagnostics();
    try std.testing.expectEqual(@as(usize, 1), warnings.len);
    const diag = warnings[0];
    try std.testing.expectEqual(error.AmbiguousAcuiMatch, diag.err);
    try std.testing.expectEqual(@as(usize, 4), diag.noteSlice().len);
    try expectNoteText(
        "chosen bindings: g1 = emp; g2 = emp; g3 = emp; +5 more",
        diag.noteSlice()[1],
    );
    try expectNoteStartsWith(
        "alternative bindings: g1 = join(hyp(v0), hyp(v1)); ",
        diag.noteSlice()[2],
    );
    try expectNoteText(
        "distinct solutions considered: 16129",
        diag.noteSlice()[3],
    );
}

test "identical ACU members are split once per count" {
    // `weaken` splits a context of 24 copies of `x` between two binders.
    // Trying every binder for every copy made 2^24 covers to compare; the
    // copies are interchangeable, so there are 25 splits, and nothing else
    // constrains them, so they are counted without being enumerated. The
    // chosen and alternative covers are the ones per-copy enumeration
    // reached first.
    const allocator = std.testing.allocator;
    const mm0_src = try readProofCase(
        allocator,
        "pass_acu_identical_members_ambiguous",
        "mm0",
    );
    defer allocator.free(mm0_src);
    const proof_src = try readProofCase(
        allocator,
        "pass_acu_identical_members_ambiguous",
        "auf",
    );
    defer allocator.free(proof_src);

    var compiler = Compiler.initWithProof(allocator, mm0_src, proof_src);
    const mmb = try compiler.compileMmb(allocator);
    defer allocator.free(mmb);
    try mm0.verifyPair(allocator, mm0_src, mmb);

    const warnings = compiler.warningDiagnostics();
    try std.testing.expectEqual(@as(usize, 1), warnings.len);
    const diag = warnings[0];
    try std.testing.expectEqual(error.AmbiguousAcuiMatch, diag.err);
    try std.testing.expectEqual(@as(usize, 4), diag.noteSlice().len);
    try expectNoteText(
        "chosen bindings: g = join(join(join(join(join(join(join(join(" ++
            "join(jo...; h = emp; d = hyp(v1)",
        diag.noteSlice()[1],
    );
    try expectNoteText(
        "alternative bindings: g = join(join(join(join(join(join(join(" ++
            "join(join(jo...; h = hyp(v0); d = hyp(v1)",
        diag.noteSlice()[2],
    );
    try expectNoteText(
        "distinct solutions considered: 25",
        diag.noteSlice()[3],
    );
}

/// `x{a} & x{b} & …` over `members`, nested the way `assoc` reads it.
fn appendBag(
    out: *std.ArrayListUnmanaged(u8),
    allocator: std.mem.Allocator,
    members: []const usize,
    assoc: []const u8,
) !void {
    for (members, 0..) |member, idx| {
        if (idx != 0) try out.appendSlice(allocator, " & ");
        if (std.mem.eql(u8, assoc, "infixr") and idx + 1 != members.len) {
            try out.append(allocator, '(');
        }
        try out.print(allocator, "x{d}", .{member});
    }
    if (std.mem.eql(u8, assoc, "infixr")) {
        try out.appendNTimes(allocator, ')', members.len - 1);
    }
}

/// A wff relation and an ACUI context sort `rc` joined by `&` (declared
/// `assoc`, "infixl" or "infixr"), for tests that build their own rules
/// over it.
fn appendRcTheory(
    out: *std.ArrayListUnmanaged(u8),
    allocator: std.mem.Allocator,
    assoc: []const u8,
) !void {
    try out.print(allocator,
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term bi (a b: wff): wff;
        \\--| @relation wff bi biid bitr bisym mpbi
        \\axiom biid (a: wff): $ bi a a $;
        \\axiom bitr (a b c: wff): $ bi a b $ > $ bi b c $ > $ bi a c $;
        \\axiom bisym (a b: wff): $ bi a b $ > $ bi b a $;
        \\axiom mpbi (a b: wff): $ bi a b $ > $ a $ > $ b $;
        \\sort rc;
        \\term rnil: rc;
        \\--| @acui rc_assoc rc_comm rnil _
        \\term rjoin (g h: rc): rc; {s} rjoin: $&$ prec 6;
        \\term rc_eq (g h: rc): wff;
        \\--| @relation rc rc_eq rc_refl rc_trans rc_sym _
        \\axiom rc_refl (g: rc): $ rc_eq g g $;
        \\axiom rc_trans (g h i: rc): $ rc_eq g h $ > $ rc_eq h i $ > $ rc_eq g i $;
        \\axiom rc_sym (g h: rc): $ rc_eq g h $ > $ rc_eq h g $;
        \\axiom rc_assoc (g h i: rc): $ rc_eq ((g & h) & i) (g & (h & i)) $;
        \\axiom rc_comm (g h: rc): $ rc_eq (g & h) (h & g) $;
        \\axiom rc_unit (g: rc): $ rc_eq (g & rnil) g $;
        \\--| @congr
        \\axiom rjoin_congr (g1 g2 h1 h2: rc):
        \\  $ rc_eq g1 g2 $ > $ rc_eq h1 h2 $ > $ rc_eq (g1 & h1) (g2 & h2) $;
        \\
    , .{assoc});
}

test "an inferred context remainder keeps its source's member order" {
    // `unmark` takes one member `a` out of a context written in reverse of
    // its sorted order, leaving the rest to `g`. Rebuilt sorted, `g` made
    // the proof re-sort the whole context, its size the square of the
    // context's (18 KB); in the source's order and nesting, `a` alone
    // moves.
    const n = 20;
    const allocator = std.testing.allocator;
    var reversed: [n]usize = undefined;
    for (&reversed, 0..) |*member, idx| member.* = n - 1 - idx;

    for ([_][]const u8{ "infixl", "infixr" }) |assoc| {
        var mm0_src: std.ArrayListUnmanaged(u8) = .empty;
        defer mm0_src.deinit(allocator);
        try appendRcTheory(&mm0_src, allocator, assoc);
        try mm0_src.appendSlice(allocator,
            \\term mark (g a: rc): wff;
            \\--| @congr
            \\axiom mark_congr (g h a b: rc):
            \\  $ rc_eq g h $ > $ rc_eq a b $ > $ bi (mark g a) (mark h b) $;
            \\term closed (g: rc): wff;
            \\--| @congr
            \\axiom closed_congr (g h: rc): $ rc_eq g h $ > $ bi (closed g) (closed h) $;
            \\axiom unmark (g a: rc): $ mark (g & a) a $ > $ closed (g & a) $;
            \\theorem t (
        );
        for (0..n) |idx| try mm0_src.print(allocator, "x{d} ", .{idx});
        try mm0_src.appendSlice(allocator, ": rc): $ mark (");
        try appendBag(&mm0_src, allocator, &reversed, assoc);
        try mm0_src.appendSlice(allocator, ") x10 $ > $ closed (");
        try appendBag(&mm0_src, allocator, &reversed, assoc);
        try mm0_src.appendSlice(allocator, ") $;\n");

        var proof_src: std.ArrayListUnmanaged(u8) = .empty;
        defer proof_src.deinit(allocator);
        try proof_src.appendSlice(allocator, "t\n---\nl1: $ closed (");
        try appendBag(&proof_src, allocator, &reversed, assoc);
        try proof_src.appendSlice(allocator, ") $ by unmark [#1]\n");

        var compiler = Compiler.initWithProof(allocator, mm0_src.items, proof_src.items);
        const mmb = try compiler.compileMmb(allocator);
        defer allocator.free(mmb);
        try mm0.verifyPair(allocator, mm0_src.items, mmb);
        try std.testing.expect(mmb.len < 8_000);
    }
}

test "a context with two unknown members is split after the arguments that fix them" {
    // `has_ctx` and `has_pair` state one fact, a context holding both
    // halves of a pair, with their arguments in either order. Matched left
    // to right, the context of `has_ctx` was split before `both a b` fixed
    // `a` and `b`: one branch per pair of members (4555 walk ticks against
    // `has_pair`'s 238 at 30 members).
    const n = 30;
    const allocator = std.testing.allocator;
    var members: [n]usize = undefined;
    for (&members, 0..) |*member, idx| member.* = idx;

    var ticks: [2]u64 = undefined;
    for ([_][]const u8{ "has_ctx", "has_pair" }, &ticks) |rule, *rule_ticks| {
        var mm0_src: std.ArrayListUnmanaged(u8) = .empty;
        defer mm0_src.deinit(allocator);
        try appendRcTheory(&mm0_src, allocator, "infixl");
        try mm0_src.appendSlice(allocator,
            \\term hyp (a: wff): rc;
            \\coercion hyp: wff > rc;
            \\--| @congr
            \\axiom hyp_congr (a b: wff): $ bi a b $ > $ rc_eq (hyp a) (hyp b) $;
            \\term both (a b: wff): wff;
            \\--| @congr
            \\axiom both_congr (a b c d: wff):
            \\  $ bi a b $ > $ bi c d $ > $ bi (both a c) (both b d) $;
            \\term has (g: rc) (a: wff): wff;
            \\--| @congr
            \\axiom has_congr (g h: rc) (a b: wff):
            \\  $ rc_eq g h $ > $ bi a b $ > $ bi (has g a) (has h b) $;
            \\term has_r (a: wff) (g: rc): wff;
            \\--| @congr
            \\axiom has_r_congr (a b: wff) (g h: rc):
            \\  $ bi a b $ > $ rc_eq g h $ > $ bi (has_r a g) (has_r b h) $;
            \\axiom has_ctx (g: rc) (a b: wff): $ has (g & a & b) (both a b) $;
            \\axiom has_pair (g: rc) (a b: wff): $ has_r (both a b) (g & a & b) $;
            \\theorem t (
        );
        for (0..n) |idx| try mm0_src.print(allocator, "x{d} ", .{idx});
        var statement: std.ArrayListUnmanaged(u8) = .empty;
        defer statement.deinit(allocator);
        if (std.mem.eql(u8, rule, "has_ctx")) {
            try statement.appendSlice(allocator, "has (");
            try appendBag(&statement, allocator, &members, "infixl");
            try statement.appendSlice(allocator, ") (both x3 x17)");
        } else {
            try statement.appendSlice(allocator, "has_r (both x3 x17) (");
            try appendBag(&statement, allocator, &members, "infixl");
            try statement.appendSlice(allocator, ")");
        }
        try mm0_src.print(allocator, ": wff): $ {s} $;\n", .{statement.items});

        var proof_src: std.ArrayListUnmanaged(u8) = .empty;
        defer proof_src.deinit(allocator);
        try proof_src.print(
            allocator,
            "t\n---\nl1: $ {s} $ by {s} []\n",
            .{ statement.items, rule },
        );

        var compiler = Compiler.initWithProof(allocator, mm0_src.items, proof_src.items);
        const start = FrontendExpr.work_ticks_walk;
        const mmb = try compiler.compileMmb(allocator);
        rule_ticks.* = FrontendExpr.work_ticks_walk -% start;
        defer allocator.free(mmb);
        try mm0.verifyPair(allocator, mm0_src.items, mmb);
    }
    try std.testing.expect(ticks[0] < 2 * ticks[1]);
}

test "a context given by a def is matched member by member" {
    // `has_one` finds a member of the context, and `unmark` takes one out;
    // the context is the def `tree`. Read as one member, `tree` matched
    // neither rule. Opened, the proof moves the one member, as it does for
    // the context written out; sorting both sides instead made it the
    // square of the context's size (12 times the written-out proof at 60
    // members).
    const n = 30;
    const allocator = std.testing.allocator;
    var members: [n]usize = undefined;
    for (&members, 0..) |*member, idx| member.* = idx;

    for ([_][]const u8{ "has_one", "unmark" }) |rule| {
        var sizes: [2]usize = undefined;
        for ([_]bool{ false, true }, &sizes) |as_def, *size| {
            var mm0_src: std.ArrayListUnmanaged(u8) = .empty;
            defer mm0_src.deinit(allocator);
            try appendRcTheory(&mm0_src, allocator, "infixl");
            try mm0_src.appendSlice(allocator,
                \\term hyp (a: wff): rc;
                \\coercion hyp: wff > rc;
                \\--| @congr
                \\axiom hyp_congr (a b: wff): $ bi a b $ > $ rc_eq (hyp a) (hyp b) $;
                \\term has_r (a: wff) (g: rc): wff;
                \\--| @congr
                \\axiom has_r_congr (a b: wff) (g h: rc):
                \\  $ bi a b $ > $ rc_eq g h $ > $ bi (has_r a g) (has_r b h) $;
                \\term mark (g a: rc): wff;
                \\--| @congr
                \\axiom mark_congr (g h a b: rc):
                \\  $ rc_eq g h $ > $ rc_eq a b $ > $ bi (mark g a) (mark h b) $;
                \\term closed (g: rc): wff;
                \\--| @congr
                \\axiom closed_congr (g h: rc): $ rc_eq g h $ > $ bi (closed g) (closed h) $;
                \\axiom has_one (g: rc) (a: wff): $ has_r a (g & a) $;
                \\axiom unmark (g a: rc): $ mark (g & a) a $ > $ closed (g & a) $;
                \\
            );
            var binders: std.ArrayListUnmanaged(u8) = .empty;
            defer binders.deinit(allocator);
            var args: std.ArrayListUnmanaged(u8) = .empty;
            defer args.deinit(allocator);
            for (0..n) |idx| {
                try binders.print(allocator, "x{d} ", .{idx});
                try args.print(allocator, " x{d}", .{idx});
            }
            var bag: std.ArrayListUnmanaged(u8) = .empty;
            defer bag.deinit(allocator);
            if (as_def) {
                try mm0_src.print(allocator, "def tree ({s}: wff): rc = $ ", .{binders.items});
                try appendBag(&mm0_src, allocator, &members, "infixl");
                try mm0_src.appendSlice(allocator, " $;\n");
                try bag.print(allocator, "tree{s}", .{args.items});
            } else {
                try appendBag(&bag, allocator, &members, "infixl");
            }
            try mm0_src.print(allocator, "theorem t ({s}: wff)", .{binders.items});
            var proof_src: std.ArrayListUnmanaged(u8) = .empty;
            defer proof_src.deinit(allocator);
            if (std.mem.eql(u8, rule, "has_one")) {
                try mm0_src.print(allocator, ": $ has_r x3 ({s}) $;\n", .{bag.items});
                try proof_src.print(allocator, "t\n---\nl1: $ has_r x3 ({s}) $ by has_one []\n", .{bag.items});
            } else {
                try mm0_src.print(allocator, ": $ mark ({s}) x3 $ > $ closed ({s}) $;\n", .{ bag.items, bag.items });
                try proof_src.print(allocator, "t\n---\nl1: $ closed ({s}) $ by unmark [#1]\n", .{bag.items});
            }

            var compiler = Compiler.initWithProof(allocator, mm0_src.items, proof_src.items);
            const mmb = try compiler.compileMmb(allocator);
            defer allocator.free(mmb);
            try mm0.verifyPair(allocator, mm0_src.items, mmb);
            size.* = mmb.len;
        }
        try std.testing.expect(sizes[1] < 2 * sizes[0]);
    }
}

test "-Werror upgrades ambiguity warnings into errors" {
    const allocator = std.testing.allocator;
    const mm0_src = try readProofCase(
        allocator,
        "pass_acui_multi_remainder_ambiguous",
        "mm0",
    );
    defer allocator.free(mm0_src);
    const proof_src = try readProofCase(
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
    const mm0_src = try readProofCase(
        allocator,
        "pass_hole_acui_ambiguous",
        "mm0",
    );
    defer allocator.free(mm0_src);
    const proof_src = try readProofCase(
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
    const mm0_src = try readProofCase(
        allocator,
        "pass_hole_acui_min_ctx",
        "mm0",
    );
    defer allocator.free(mm0_src);
    const proof_src = try readProofCase(
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
    const mm0_src = try readProofCase(
        allocator,
        "pass_hole_acui_disambiguate",
        "mm0",
    );
    defer allocator.free(mm0_src);
    const proof_src = try readProofCase(
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
    const mm0_src = try readProofCase(
        allocator,
        "robinson",
        "mm0",
    );
    defer allocator.free(mm0_src);
    const proof_src = try readProofCase(
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
    const mm0_src = try readProofCase(
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
    const mm0_src = try readProofCase(
        allocator,
        "gentzen",
        "mm0",
    );
    defer allocator.free(mm0_src);
    const proof_src = try readProofCase(
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

test "ordinary structural inference retains witnesses without views" {
    const allocator = std.testing.allocator;
    const stem = "pass_rule_symbolic_witness";
    const mm0_src = try readProofCase(allocator, stem, "mm0");
    defer allocator.free(mm0_src);
    const proof_src = try readProofCase(allocator, stem, "auf");
    defer allocator.free(proof_src);
    try std.testing.expect(std.mem.indexOf(u8, mm0_src, "@view") == null);
    try std.testing.expect(std.mem.indexOf(u8, mm0_src, "@vars") == null);
    try std.testing.expect(std.mem.indexOf(u8, proof_src, ":=") == null);

    var compiler = Compiler.initWithProof(allocator, mm0_src, proof_src);
    const mmb = try compiler.compileMmb(allocator);
    defer allocator.free(mmb);
    try mm0.verifyPair(allocator, mm0_src, mmb);
}

test "symbolic rule inference respects an explicit witness constraint" {
    const allocator = std.testing.allocator;
    const stem = "pass_rule_symbolic_witness";
    const mm0_src = try readProofCase(allocator, stem, "mm0");
    defer allocator.free(mm0_src);
    const proof_src = try readProofCase(allocator, stem, "auf");
    defer allocator.free(proof_src);
    const wrong_witness = try replaceOnceOwned(
        allocator,
        proof_src,
        "by ex_elim",
        "by ex_elim (x := $ b $)",
    );
    defer allocator.free(wrong_witness);
    var compiler = Compiler.initWithProof(allocator, mm0_src, wrong_witness);
    try std.testing.expectError(
        error.UnifyMismatch,
        compiler.compileMmb(allocator),
    );
}

test "structural solve aborts at an exhausted search work budget" {
    // A budgeted search installs a `WorkBudget` on the compiler context; the
    // solver polls it at every branch clone and semantic compare, so a solve
    // under a spent budget fails with the search's own exhaustion error
    // instead of running its fan-out to completion.
    const allocator = std.testing.allocator;
    const stem = "pass_acui_cover_product_ambiguous";
    const mm0_src = try readProofCase(allocator, stem, "mm0");
    defer allocator.free(mm0_src);
    const proof_src = try readProofCase(allocator, stem, "auf");
    defer allocator.free(proof_src);

    const Spent = struct {
        polls: usize = 0,
        fn check(ctx: *anyopaque) error{SearchBudgetExhausted}!void {
            const self: *@This() = @ptrCast(@alignCast(ctx));
            self.polls += 1;
            return error.SearchBudgetExhausted;
        }
    };
    var spent = Spent{};
    var compiler = Compiler.initWithProof(allocator, mm0_src, proof_src);
    compiler.work_budget = .{ .ctx = @ptrCast(&spent), .check_fn = Spent.check };
    try std.testing.expectError(
        error.SearchBudgetExhausted,
        compiler.compileMmb(allocator),
    );
    try std.testing.expect(spent.polls >= 1);
}

test "a premise bag member no @recover reads is dropped as it is matched" {
    // The statement goes first and binds the view's pattern, so a choice of
    // branch row for `q` or `r` that is no instance of it is dropped as it
    // is made, rather than every pair of rows being carried to the end.
    const allocator = std.testing.allocator;
    const stem = "fail_view_acui_wrong_instance_long_branch";
    const mm0_src = try readProofCase(allocator, stem, "mm0");
    defer allocator.free(mm0_src);
    const proof_src = try readProofCase(allocator, stem, "auf");
    defer allocator.free(proof_src);

    var stats = Compiler.InferenceStatsSink{};
    var compiler = Compiler.initWithProof(allocator, mm0_src, proof_src);
    compiler.inference_stats_sink = &stats;
    try std.testing.expectError(
        error.RecoverHoleNotFound,
        compiler.compileMmb(allocator),
    );
    try std.testing.expectEqual(@as(usize, 1), stats.peak_solver_branches);
}

test "kept symbolic match state extends a branch rather than duplicating it" {
    // Once the first premise leaves `p` mentioning the hidden witness, each
    // later bare-binder premise is matched through the kept session state.
    // Sixteen such premises must leave the branch population flat; a second
    // whole-constraint match per premise would double it every time.
    const allocator = std.testing.allocator;
    const stem = "pass_symbolic_witness_repeated_premises";
    const mm0_src = try readProofCase(allocator, stem, "mm0");
    defer allocator.free(mm0_src);
    const proof_src = try readProofCase(allocator, stem, "auf");
    defer allocator.free(proof_src);

    var stats = Compiler.InferenceStatsSink{};
    var compiler = Compiler.initWithProof(allocator, mm0_src, proof_src);
    compiler.inference_stats_sink = &stats;
    const mmb = try compiler.compileMmb(allocator);
    defer allocator.free(mmb);
    try mm0.verifyPair(allocator, mm0_src, mmb);
    try std.testing.expectEqual(@as(usize, 2), stats.peak_solver_branches);
}
