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
const expectNoteText = helpers.expectNoteText;

test "compiler rejects @congr binders declared old-old-new-new" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term bi (a b: wff): wff;
        \\term pair (a b: wff): wff;
        \\--| @relation wff bi biid bitr bisym mpbi
        \\axiom biid (a: wff): $ bi a a $;
        \\axiom bitr (a b c: wff):
        \\  $ bi a b $ > $ bi b c $ > $ bi a c $;
        \\axiom bisym (a b: wff): $ bi a b $ > $ bi b a $;
        \\axiom mpbi (a b: wff): $ bi a b $ > $ a $ > $ b $;
        \\--| @congr
        \\axiom pair_congr (a b c d: wff):
        \\  $ bi a c $ > $ bi b d $ >
        \\  $ bi (pair a b) (pair c d) $;
    ;

    var compiler = Compiler.init(std.testing.allocator, mm0_src);
    try std.testing.expectError(
        error.CongruenceBinderOrderMismatch,
        compiler.check(),
    );

    const diag = compiler.diagnostics.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.CongruenceBinderOrderMismatch, diag.err);
    try std.testing.expectEqual(mm0.CompilerDiagnosticSource.mm0, diag.source);
    try std.testing.expectEqualStrings("pair_congr", diag.name.?);
    try std.testing.expectEqualStrings(
        "@congr binders must be ordered old₀ new₀ old₁ new₁ ...",
        mm0.compilerDiagnosticSummary(diag),
    );
    const span = diag.span orelse return error.ExpectedDiagnosticSpan;
    try std.testing.expectEqualStrings("@congr", mm0_src[span.start..span.end]);
}

test "compiler rejects @congr regular args reused on both sides" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term bi (a b: wff): wff;
        \\term box (a: wff): wff;
        \\--| @relation wff bi biid bitr bisym mpbi
        \\axiom biid (a: wff): $ bi a a $;
        \\axiom bitr (a b c: wff):
        \\  $ bi a b $ > $ bi b c $ > $ bi a c $;
        \\axiom bisym (a b: wff): $ bi a b $ > $ bi b a $;
        \\axiom mpbi (a b: wff): $ bi a b $ > $ a $ > $ b $;
        \\--| @congr
        \\axiom box_congr (a: wff): $ bi (box a) (box a) $;
    ;

    var compiler = Compiler.init(std.testing.allocator, mm0_src);
    try std.testing.expectError(
        error.CongruenceBinderOrderMismatch,
        compiler.check(),
    );

    const diag = compiler.diagnostics.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.CongruenceBinderOrderMismatch, diag.err);
    try std.testing.expectEqualStrings("box_congr", diag.name.?);
    const span = diag.span orelse return error.ExpectedDiagnosticSpan;
    try std.testing.expectEqualStrings("@congr", mm0_src[span.start..span.end]);
}

test "compiler rejects @congr with wrong outer relation" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term bi (a b: wff): wff;
        \\term other (a b: wff): wff;
        \\term box (a: wff): wff;
        \\--| @relation wff bi biid bitr bisym mpbi
        \\axiom biid (a: wff): $ bi a a $;
        \\axiom bitr (a b c: wff):
        \\  $ bi a b $ > $ bi b c $ > $ bi a c $;
        \\axiom bisym (a b: wff): $ bi a b $ > $ bi b a $;
        \\axiom mpbi (a b: wff): $ bi a b $ > $ a $ > $ b $;
        \\--| @congr
        \\axiom box_congr (a b: wff):
        \\  $ bi a b $ > $ other (box a) (box b) $;
    ;

    var compiler = Compiler.init(std.testing.allocator, mm0_src);
    try std.testing.expectError(
        error.InvalidCongruenceAnnotation,
        compiler.check(),
    );

    const diag = compiler.diagnostics.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.InvalidCongruenceAnnotation, diag.err);
    try std.testing.expectEqualStrings("box_congr", diag.name.?);
    const span = diag.span orelse return error.ExpectedDiagnosticSpan;
    try std.testing.expectEqualStrings("@congr", mm0_src[span.start..span.end]);
}

test "compiler rejects @congr binders missing head-term dependencies" {
    // `all`'s child position permits x, so lifts substitute x-containing
    // children; a congr rule whose old/new binders don't declare the x
    // dependency would make every such lift violate disjointness.
    const mm0_src =
        \\delimiter $ ( ) $;
        \\sort var;
        \\provable sort wff;
        \\term bi (a b: wff): wff;
        \\term all {x: var} (p: wff x): wff;
        \\--| @relation wff bi biid bitr bisym mpbi
        \\axiom biid (a: wff): $ bi a a $;
        \\axiom bitr (a b c: wff):
        \\  $ bi a b $ > $ bi b c $ > $ bi a c $;
        \\axiom bisym (a b: wff): $ bi a b $ > $ bi b a $;
        \\axiom mpbi (a b: wff): $ bi a b $ > $ a $ > $ b $;
        \\--| @congr
        \\axiom all_congr {x: var} (p q: wff):
        \\  $ bi p q $ > $ bi (all x p) (all x q) $;
    ;

    var compiler = Compiler.init(std.testing.allocator, mm0_src);
    try std.testing.expectError(
        error.CongruenceBinderMissingDeps,
        compiler.check(),
    );

    const diag = compiler.diagnostics.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.CongruenceBinderMissingDeps, diag.err);
    try std.testing.expectEqualStrings("all_congr", diag.name.?);
    const span = diag.span orelse return error.ExpectedDiagnosticSpan;
    try std.testing.expectEqualStrings("@congr", mm0_src[span.start..span.end]);
}

test "compiler accepts @congr binders with full head-term dependencies" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\sort var;
        \\provable sort wff;
        \\term bi (a b: wff): wff;
        \\term all {x: var} (p: wff x): wff;
        \\--| @relation wff bi biid bitr bisym mpbi
        \\axiom biid (a: wff): $ bi a a $;
        \\axiom bitr (a b c: wff):
        \\  $ bi a b $ > $ bi b c $ > $ bi a c $;
        \\axiom bisym (a b: wff): $ bi a b $ > $ bi b a $;
        \\axiom mpbi (a b: wff): $ bi a b $ > $ a $ > $ b $;
        \\--| @congr
        \\axiom all_congr {x: var} (p q: wff x):
        \\  $ bi p q $ > $ bi (all x p) (all x q) $;
    ;

    var compiler = Compiler.init(std.testing.allocator, mm0_src);
    try compiler.check();
}

test "compiler rejects @relation bundle rule with a bound binder" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\sort var;
        \\provable sort wff;
        \\term bi (a b: wff): wff;
        \\term neg (a: wff): wff;
        \\--| @relation wff bi biid bitr bisym mpbi
        \\axiom biid (a: wff): $ bi a a $;
        \\axiom bitr (a b c: wff):
        \\  $ bi a b $ > $ bi b c $ > $ bi a c $;
        \\axiom bisym {x: var} (a b: wff): $ bi a b $ > $ bi b a $;
        \\axiom mpbi (a b: wff): $ bi a b $ > $ a $ > $ b $;
        \\--| @conversion ltr
        \\axiom neg_invol (a: wff): $ bi (neg (neg a)) a $;
    ;

    var compiler = Compiler.init(std.testing.allocator, mm0_src);
    try std.testing.expectError(
        error.RelationBundleBoundBinder,
        compiler.check(),
    );

    const diag = compiler.diagnostics.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.RelationBundleBoundBinder, diag.err);
    try std.testing.expectEqualStrings("neg_invol", diag.name.?);
    const span = diag.span orelse return error.ExpectedDiagnosticSpan;
    try std.testing.expectEqualStrings("@conversion ltr", mm0_src[span.start..span.end]);
}

test "compiler normalizes conclusions with automatic normalization" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term bi (a b: wff): wff; infixr bi: $<->$ prec 20;
        \\term sb (a b: wff): wff;
        \\term pair (a b: wff): wff;
        \\term P: wff;
        \\term Q: wff;
        \\--| @relation wff bi biid bitr bisym mpbi
        \\axiom biid (a: wff): $ a <-> a $;
        \\axiom bitr (a b c: wff):
        \\  $ a <-> b $ > $ b <-> c $ > $ a <-> c $;
        \\axiom bisym (a b: wff): $ a <-> b $ > $ b <-> a $;
        \\axiom mpbi (a b: wff): $ a <-> b $ > $ a $ > $ b $;
        \\--| @rewrite
        \\axiom sb_P (a: wff): $ sb a P <-> a $;
        \\--| @congr
        \\axiom pair_congr (a b c d: wff):
        \\  $ a <-> b $ > $ c <-> d $ >
        \\  $ pair a c <-> pair b d $;
        \\axiom all_elim (b: wff): $ pair (sb P P) b $;
        \\theorem test_normalize: $ pair P Q $;
    ;
    const proof_src =
        \\test_normalize
        \\--------------
        \\l1: $ pair P Q $ by all_elim
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

test "compiler reports normalized comparison snapshots on mismatch" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term im (a b: wff): wff; infixr im: $->$ prec 25;
        \\term bi (a b: wff): wff; infixr bi: $<->$ prec 20;
        \\term sb (a b: wff): wff;
        \\term P: wff;
        \\term Q: wff;
        \\term R: wff;
        \\--| @relation wff bi biid bitr bisym mpbi
        \\axiom biid (a: wff): $ a <-> a $;
        \\axiom bitr (a b c: wff):
        \\  $ a <-> b $ > $ b <-> c $ > $ a <-> c $;
        \\axiom bisym (a b: wff): $ a <-> b $ > $ b <-> a $;
        \\axiom mpbi (a b: wff): $ a <-> b $ > $ a $ > $ b $;
        \\--| @rewrite
        \\axiom sb_im (a b c: wff):
        \\  $ sb a (b -> c) <-> (sb a b -> sb a c) $;
        \\--| @rewrite
        \\axiom sb_P (a: wff): $ sb a P <-> a $;
        \\--| @congr
        \\axiom im_congr (a b c d: wff):
        \\  $ a <-> b $ > $ c <-> d $ > $ (a -> c) <-> (b -> d) $;
        \\axiom all_elim (a b: wff): $ sb a b $;
        \\theorem test_normalize_bad: $ R -> R $;
    ;
    const proof_src =
        \\test_normalize_bad
        \\------------------
        \\l1: $ R -> R $ by all_elim (a := $ Q $, b := $ P -> P $)
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
    try std.testing.expectEqual(.conclusion_mismatch, diag.kind);
    try std.testing.expectEqual(
        mm0.CompilerDiagnosticPhase.theorem_application,
        diag.phase.?,
    );
    try std.testing.expectEqual(@as(usize, 5), diag.noteSlice().len);
    try expectNoteText(
        "expected: sb Q (P -> P)",
        diag.noteSlice()[0],
    );
    try expectNoteText(
        "actual: R -> R",
        diag.noteSlice()[1],
    );
    try expectNoteText(
        "attempted normalized comparison",
        diag.noteSlice()[2],
    );
    try expectNoteText(
        "normalized expected: Q -> Q",
        diag.noteSlice()[3],
    );
    try expectNoteText(
        "normalized actual: R -> R",
        diag.noteSlice()[4],
    );
}

test "compiler reports missing congruence rules for normalization" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term im (a b: wff): wff; infixr im: $->$ prec 25;
        \\term bi (a b: wff): wff; infixr bi: $<->$ prec 20;
        \\term P: wff;
        \\term Q: wff;
        \\term sb (a b: wff): wff;
        \\--| @relation wff bi biid bitr bisym mpbi
        \\axiom biid (a: wff): $ a <-> a $;
        \\axiom bitr (a b c: wff): $ a <-> b $ > $ b <-> c $ > $ a <-> c $;
        \\axiom bisym (a b: wff): $ a <-> b $ > $ b <-> a $;
        \\axiom mpbi (a b: wff): $ a <-> b $ > $ a $ > $ b $;
        \\--| @rewrite
        \\axiom sb_im (a b c: wff): $ sb a (b -> c) <-> (sb a b -> sb a c) $;
        \\--| @rewrite
        \\axiom sb_P (a: wff): $ sb a P <-> a $;
        \\axiom im_congr (a b c d: wff):
        \\  $ a <-> b $ > $ c <-> d $ > $ (a -> c) <-> (b -> d) $;
        \\axiom all_elim (a b: wff): $ sb a b $;
        \\theorem test_normalize: $ Q -> Q $;
    ;
    const proof_src =
        \\test_normalize
        \\--------------
        \\l1: $ Q -> Q $ by all_elim (a := $ Q $, b := $ P -> P $)
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    try std.testing.expectError(
        error.MissingCongruenceRule,
        compiler.compileMmb(std.testing.allocator),
    );

    const diag = compiler.diagnostics.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.MissingCongruenceRule, diag.err);
    try std.testing.expectEqual(.generic, diag.kind);
    try std.testing.expectEqualStrings(
        "test_normalize",
        diag.theorem_name.?,
    );
    try std.testing.expectEqualStrings("l1", diag.line_label.?);
    try std.testing.expectEqualStrings("all_elim", diag.rule_name.?);
    const span = diag.span orelse return error.ExpectedDiagnosticSpan;
    try std.testing.expectEqualStrings(
        "$ Q -> Q $",
        proof_src[span.start..span.end],
    );
    switch (diag.detail) {
        .missing_congruence_rule => |detail| {
            try std.testing.expectEqual(.missing_rule, detail.reason);
            try std.testing.expectEqualStrings("im", detail.term_name.?);
            try std.testing.expectEqualStrings("wff", detail.sort_name.?);
            try std.testing.expect(detail.arg_index == null);
        },
        else => return error.ExpectedMissingCongruenceDetail,
    }
}

test "transparent def compression does not leak temp binders" {
    const mm0_src =
        \\strict provable sort wff;
        \\delimiter $ ( @ [ / $ $ . : ; ) ] $;
        \\term im: wff > wff > wff;
        \\infixr im: $⊢$ prec 0;
        \\strict sort type;
        \\term bool: type;
        \\notation bool: type = ($𝔹$:max);
        \\term obj: type;
        \\notation obj: type = ($𝕆$:max);
        \\sort term;
        \\term app: term > term > term;
        \\infixl app: $·$ prec 1000;
        \\term eq: type > term;
        \\def eqc (A: type) (t u: term): term = $ eq A · t · u $;
        \\notation eqc (A: type) (t u: term): term =
        \\  ($≃[$:50) A ($]$:0) t ($=$:50) u;
        \\notation eqc (A: type) (t u: term): term =
        \\  ($=[$:50) A ($]$:0) t ($=$:50) u;
        \\term thm: term > wff;
        \\coercion thm: term > wff;
        \\def bic (p q: term): term = $ ≃[𝔹] p = q $;
        \\infixr bic: $⇔$ prec 20;
        \\axiom sym (G: wff) (A: type) (a b: term):
        \\  $ G ⊢ ≃[A] a = b $ > $ G ⊢ ≃[A] b = a $;
        \\axiom eqmp (G: wff) (P Q: term):
        \\  $ G ⊢ P ⇔ Q $ > $ G ⊢ P $ > $ G ⊢ Q $;
        \\term T: term;
        \\theorem crash (G: wff) (s: term):
        \\  $ G ⊢ ≃[𝔹] T = =[𝕆] s = s $ >
        \\  $ G ⊢ =[𝕆] s = s $ >
        \\  $ G ⊢ T $;
    ;
    const proof_src =
        \\crash
        \\-----
        \\l1: $ G ⊢ ≃[𝔹] (=[𝕆] s = s) = T $ by sym [#1]
        \\l2: $ G ⊢ T $ by eqmp [l1, #2]
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

test "transparent transport verifies eqmp over bic symmetry" {
    const mm0_src =
        \\strict provable sort wff;
        \\delimiter $ ( @ [ / $ $ . : ; ) ] $;
        \\term im: wff > wff > wff;
        \\infixr im: $⊢$ prec 0;
        \\strict sort type;
        \\term bool: type;
        \\notation bool: type = ($𝔹$:max);
        \\sort term;
        \\term app: term > term > term;
        \\infixl app: $·$ prec 1000;
        \\term eq: type > term;
        \\def eqc (A: type) (t u: term): term = $ eq A · t · u $;
        \\notation eqc (A: type) (t u: term): term =
        \\  ($≃[$:50) A ($]$:0) t ($=$:50) u;
        \\term thm: term > wff;
        \\coercion thm: term > wff;
        \\def bic (p q: term): term = $ ≃[𝔹] p = q $;
        \\infixr bic: $⇔$ prec 20;
        \\axiom symt (G: wff) (A: type) (a b: term):
        \\  $ G ⊢ ≃[A] a = b $ > $ G ⊢ ≃[A] b = a $;
        \\axiom eqmp (G: wff) (P Q: term):
        \\  $ G ⊢ P ⇔ Q $ > $ G ⊢ P $ > $ G ⊢ Q $;
        \\theorem eqmpr (G: wff) (P Q: term):
        \\  $ G ⊢ Q ⇔ P $ > $ G ⊢ P $ > $ G ⊢ Q $;
    ;
    const proof_src =
        \\eqmpr
        \\-----
        \\l1: $ G ⊢ P ⇔ Q $ by symt [#1]
        \\l2: $ G ⊢ Q $ by eqmp [l1, #2]
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

test "transparent final line matching unfolds allc notation" {
    // The last proof line is raw `all A · (λ x: A. t)`, while the theorem
    // statement uses the surface `!x: A. t` notation.
    const mm0_src =
        \\strict provable sort wff;
        \\delimiter $ ( @ [ / ! $ $ . : ; ) ] $;
        \\term im: wff > wff > wff;
        \\infixr im: $⊢$ prec 0;
        \\term an: wff > wff > wff;
        \\infixl an: $∧$ prec 1;
        \\strict sort type;
        \\term bool: type;
        \\notation bool: type = ($𝔹$:max);
        \\sort term;
        \\term ty: term > type > wff;
        \\infixl ty: $:$ prec 2;
        \\term app: term > term > term;
        \\infixl app: $·$ prec 1000;
        \\term lam {x: term}: type > term x > term;
        \\notation lam {x: term} (A: type) (t: term x): term =
        \\  ($λ$:20) x ($:$:2) A ($.$:0) t;
        \\term all: type > term;
        \\def allc {x: term} (A: type) (t: term x): term =
        \\  $ all A · (λ x: A. t) $;
        \\notation allc {x: term} (A: type) (t: term x): term =
        \\  ($!$:20) x ($:$:2) A ($.$:0) t;
        \\axiom allc_raw (G: wff) (A: type) {x: term} (t: term x):
        \\  $ G ∧ x: A ⊢ t: 𝔹 $ >
        \\  $ G ⊢ all A · (λ x: A. t): 𝔹 $;
        \\theorem final_allc (G: wff) (A: type) {x: term} (t: term x):
        \\  $ G ∧ x: A ⊢ t: 𝔹 $ >
        \\  $ G ⊢ !x: A. t: 𝔹 $;
    ;
    const proof_src =
        \\final_allc
        \\----------
        \\l1: $ G ⊢ all A · (λ x: A. t): 𝔹 $ by allc_raw [#1]
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

test "transparent final line matching unfolds bic and allc under coercion" {
    const mm0_src =
        \\strict provable sort wff;
        \\delimiter $ ( @ [ / ! $ $ . : ; ) ] $;
        \\strict sort type;
        \\term bool: type;
        \\notation bool: type = ($𝔹$:max);
        \\sort term;
        \\term app: term > term > term;
        \\infixl app: $·$ prec 1000;
        \\term lam {x: term}: type > term x > term;
        \\notation lam {x: term} (A: type) (t: term x): term =
        \\  ($λ$:20) x ($:$:2) A ($.$:0) t;
        \\term eq: type > term;
        \\def eqc (A: type) (t u: term): term = $ eq A · t · u $;
        \\notation eqc (A: type) (t u: term): term =
        \\  ($≃[$:50) A ($]$:0) t ($=$:50) u;
        \\term thm: term > wff;
        \\coercion thm: term > wff;
        \\def bic (p q: term): term = $ ≃[𝔹] p = q $;
        \\infixr bic: $⇔$ prec 20;
        \\term all: type > term;
        \\def allc {x: term} (A: type) (t: term x): term =
        \\  $ all A · (λ x: A. t) $;
        \\notation allc {x: term} (A: type) (t: term x): term =
        \\  ($!$:20) x ($:$:2) A ($.$:0) t;
        \\axiom all_bic_raw (A: type) {x: term} (t u: term x):
        \\  $ ≃[𝔹] all A · (λ x: A. t) = all A · (λ x: A. u) $;
        \\theorem final_bic_allc (A: type) {x: term} (t u: term x):
        \\  $ (!x: A. t) ⇔ (!x: A. u) $;
    ;
    const proof_src =
        \\final_bic_allc
        \\--------------
        \\l1: $ ≃[𝔹] all A · (λ x: A. t) = all A · (λ x: A. u) $ by all_bic_raw []
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

test "transparent betacv matching handles quantified bic operands" {
    const mm0_src =
        \\strict provable sort wff;
        \\
        \\delimiter $ ( @ [ / ! $ $ . : ; ) ] $;
        \\
        \\term im: wff > wff > wff;
        \\infixr im: $⊢$ prec 0;
        \\
        \\term an: wff > wff > wff;
        \\infixl an: $∧$ prec 1;
        \\
        \\strict sort type;
        \\term bool: type;
        \\notation bool: type = ($𝔹$:max);
        \\
        \\sort term;
        \\term ty: term > type > wff;
        \\infixl ty: $:$ prec 2;
        \\term app: term > term > term;
        \\infixl app: $·$ prec 1000;
        \\term lam {x: term}: type > term x > term;
        \\notation lam {x: term} (A: type) (t: term x): term =
        \\  ($λ$:20) x ($:$:2) A ($.$:0) t;
        \\term eq: type > term;
        \\def eqc (A: type) (t u: term): term = $ eq A · t · u $;
        \\notation eqc (A: type) (t u: term): term =
        \\  ($≃[$:50) A ($]$:0) t ($=$:50) u;
        \\term thm: term > wff;
        \\coercion thm: term > wff;
        \\def bic (p q: term): term = $ ≃[𝔹] p = q $;
        \\infixr bic: $⇔$ prec 20;
        \\term imp: term;
        \\def impc (p q: term): term = $ imp · p · q $;
        \\infixr impc: $⇒$ prec 30;
        \\term all: type > term;
        \\def allc {x: term} (A: type) (t: term x): term =
        \\  $ all A · (λ x: A. t) $;
        \\notation allc {x: term} (A: type) (t: term x): term =
        \\  ($!$:20) x ($:$:2) A ($.$:0) t;
        \\
        \\axiom betacv (G: wff) (A B: type) {x: term} (t u v: term x):
        \\  $ G ∧ x: A ⊢ u: B $ >
        \\  $ G ⊢ t: A $ >
        \\  $ G ⊢ v: B $ >
        \\  $ G ∧ ≃[A] x = t ⊢ ≃[B] u = v $ >
        \\  $ G ⊢ ≃[B] (λ x: A. u) · t = v $;
        \\
        \\theorem orc_betacv_probe (G: wff) (a b: term) {q r: term}:
        \\  $ G ∧ q: 𝔹 ⊢ !r: 𝔹. (a ⇒ r) ⇒ (q ⇒ r) ⇒ r: 𝔹 $ >
        \\  $ G ⊢ b: 𝔹 $ >
        \\  $ G ⊢ all 𝔹 · (λ r: 𝔹. (a ⇒ r) ⇒ (b ⇒ r) ⇒ r): 𝔹 $ >
        \\  $ G ∧ ≃[𝔹] q = b ⊢
        \\      (!r: 𝔹. (a ⇒ r) ⇒ (q ⇒ r) ⇒ r) ⇔
        \\      (all 𝔹 · (λ r: 𝔹. (a ⇒ r) ⇒ (b ⇒ r) ⇒ r)) $ >
        \\  $ G ⊢ ≃[𝔹]
        \\      ((λ q: 𝔹. !r: 𝔹. (a ⇒ r) ⇒ (q ⇒ r) ⇒ r) · b) =
        \\      (all 𝔹 · (λ r: 𝔹. (a ⇒ r) ⇒ (b ⇒ r) ⇒ r)) $;
    ;
    const omitted_proof_src =
        "orc_betacv_probe\n" ++
        "----------------\n" ++
        "l1: $ G ⊢ ≃[𝔹] ((λ q: 𝔹. !r: 𝔹. (a ⇒ r) ⇒ (q ⇒ r) ⇒ r) ·" ++
        " b) = (all 𝔹 · (λ r: 𝔹. (a ⇒ r) ⇒ (b ⇒ r) ⇒ r)) $" ++
        " by betacv [#1, #2, #3, #4]\n";
    const explicit_proof_src =
        "orc_betacv_probe\n" ++
        "----------------\n" ++
        "l1: $ G ⊢ ≃[𝔹] ((λ q: 𝔹. !r: 𝔹. (a ⇒ r) ⇒ (q ⇒ r) ⇒ r) ·" ++
        " b) = (all 𝔹 · (λ r: 𝔹. (a ⇒ r) ⇒ (b ⇒ r) ⇒ r)) $ by" ++
        " betacv (G := $ G $, A := $ 𝔹 $, B := $ 𝔹 $, x := $ q $," ++
        " t := $ b $, u := $ !r: 𝔹. (a ⇒ r) ⇒ (q ⇒ r) ⇒ r $," ++
        " v := $ all 𝔹 · (λ r: 𝔹. (a ⇒ r) ⇒ (b ⇒ r) ⇒ r) $)" ++
        " [#1, #2, #3, #4]\n";

    {
        var compiler = Compiler.initWithProof(
            std.testing.allocator,
            mm0_src,
            omitted_proof_src,
        );
        const mmb = try compiler.compileMmb(std.testing.allocator);
        defer std.testing.allocator.free(mmb);
        try mm0.verifyPair(std.testing.allocator, mm0_src, mmb);
    }

    {
        var compiler = Compiler.initWithProof(
            std.testing.allocator,
            mm0_src,
            explicit_proof_src,
        );
        const mmb = try compiler.compileMmb(std.testing.allocator);
        defer std.testing.allocator.free(mmb);
        try mm0.verifyPair(std.testing.allocator, mm0_src, mmb);
    }
}

test "compiler reports dependency slot exhaustion clearly" {
    const allocator = std.testing.allocator;

    var mm0_buf = std.ArrayListUnmanaged(u8){};
    defer mm0_buf.deinit(allocator);
    try mm0_buf.appendSlice(allocator,
        \\--| @vars y
        \\provable sort wff;
        \\term top: wff;
        \\--| @fresh y
        \\axiom use_fresh {y: wff}: $ top $;
        \\theorem overflow
    );
    for (0..FrontendExpr.tracked_bound_dep_limit) |idx| {
        try mm0_buf.writer(allocator).print(" {{x{d}: wff}}", .{idx});
    }
    try mm0_buf.appendSlice(allocator, ": $ top $;\n");

    const proof_src =
        \\overflow
        \\--------
        \\l1: $ top $ by use_fresh []
    ;

    var compiler = Compiler.initWithProof(
        allocator,
        mm0_buf.items,
        proof_src,
    );
    try std.testing.expectError(
        error.DependencySlotExhausted,
        compiler.compileMmb(allocator),
    );

    const diag = compiler.diagnostics.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.DependencySlotExhausted, diag.err);
    try std.testing.expectEqualStrings("overflow", diag.theorem_name.?);
    try std.testing.expectEqualStrings("l1", diag.line_label.?);
    try std.testing.expectEqualStrings("use_fresh", diag.rule_name.?);
    try std.testing.expectEqualStrings("y", diag.name.?);
    try std.testing.expectEqualStrings(
        "theorem exceeded the 55 tracked bound-variable dependency slots",
        mm0.compilerDiagnosticSummary(diag),
    );
}

test "strict replay does not open defs during omitted inference" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term imp (a b: wff): wff; infixr imp: $->$ prec 25;
        \\def id (a: wff): wff = $ a -> a $;
        \\axiom ax_id (a: wff): $ id a $;
        \\theorem strict_infer_expected (a: wff): $ a -> a $;
    ;
    const proof_src =
        \\strict_infer_expected
        \\---------------------
        \\l1: $ a -> a $ by ax_id []
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    const mmb = try compiler.compileMmb(std.testing.allocator);
    defer std.testing.allocator.free(mmb);
    try mm0.verifyPair(std.testing.allocator, mm0_src, mmb);

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
                    if (value.kind != .theorem) continue;
                    if (!std.mem.eql(
                        u8,
                        value.name,
                        "strict_infer_expected",
                    )) continue;
                    break :blk value;
                },
                else => {},
            }
        }
        return error.MissingAssertion;
    };
    const rule_id = env.getRuleId("ax_id") orelse return error.MissingRule;
    const rule = &env.rules.items[rule_id];

    try theorem.seedAssertion(assertion);
    for (assertion.arg_names, assertion.arg_exprs) |name, expr| {
        if (name) |actual_name| {
            try theorem_vars.put(actual_name, expr);
        }
    }

    const parsed_line = try parser.parseFormulaText(" a -> a ", &theorem_vars);
    const line_expr = try theorem.internParsedExpr(parsed_line);
    const partial_bindings = [_]?FrontendExpr.ExprId{null};
    const ref_exprs = [_]FrontendExpr.ExprId{};
    const line = ProofScript.ProofLine{
        .label = "l1",
        .label_span = .{ .start = 0, .end = 0 },
        .assertion = .{
            .text = " a -> a ",
            .span = .{ .start = 0, .end = 0 },
        },
        .application = .{
            .rule_name = "ax_id",
            .rule_span = .{ .start = 0, .end = 0 },
            .binding_list_span = null,
            .arg_bindings = &.{},
            .refs_span = null,
            .refs = &.{},
            .span = .{ .start = 0, .end = 0 },
        },
        .span = .{ .start = 0, .end = 0 },
    };

    var compiler_context = mm0.CompilerSupport.Context.CompilerContext.init(
        mm0_src,
        proof_src,
        compiler.debug,
        &compiler.diagnostics,
    );
    try std.testing.expectError(
        error.TermMismatch,
        CompilerInference.strictInferBindings(
            &compiler_context,
            arena.allocator(),
            &env,
            &theorem,
            assertion,
            rule,
            line,
            &partial_bindings,
            &ref_exprs,
            line_expr,
        ),
    );
}
