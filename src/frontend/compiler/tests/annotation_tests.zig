const helpers = @import("./helpers.zig");
const std = helpers.std;
const mm0 = helpers.mm0;
const Compiler = helpers.Compiler;
const FrontendEnv = helpers.FrontendEnv;
const MM0Parser = helpers.MM0Parser;
const RewriteRegistry = helpers.RewriteRegistry;
const ConversionRole = helpers.ConversionRole;
const CompilerMetadata = helpers.CompilerMetadata;
const readProofCaseFile = helpers.readProofCaseFile;
const processAnnotatedMetadata = helpers.processAnnotatedMetadata;

test "compiler env retains def dummy metadata" {
    const src = try readProofCaseFile(
        std.testing.allocator,
        "pass_def_dummy",
        "mm0",
    );
    defer std.testing.allocator.free(src);

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = MM0Parser.init(src, arena.allocator());
    var env = FrontendEnv.GlobalEnv.init(arena.allocator());
    while (try parser.next()) |stmt| {
        try env.addStmt(stmt);
    }

    const term_id = env.term_names.get("injective") orelse {
        return error.MissingTerm;
    };
    const term = env.terms.items[term_id];
    try std.testing.expect(term.is_def);
    try std.testing.expectEqual(@as(usize, 2), term.dummy_args.len);
    try std.testing.expectEqualStrings("obj", term.dummy_args[0].sort_name);
    try std.testing.expectEqualStrings("obj", term.dummy_args[1].sort_name);
}

test "compiler ignores plain doc comments on terms" {
    const mm0_src =
        \\sort nat;
        \\--| zero is the base natural number constructor
        \\term zero: nat;
    ;

    var compiler = Compiler.init(std.testing.allocator, mm0_src);
    try compiler.check();
}

test "compiler rejects unknown term annotations" {
    const mm0_src =
        \\sort nat;
        \\--| @bogus
        \\term zero: nat;
    ;

    var compiler = Compiler.init(std.testing.allocator, mm0_src);
    try std.testing.expectError(error.UnknownTermAnnotation, compiler.check());

    const diag = compiler.diagnostics.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.UnknownTermAnnotation, diag.err);
    try std.testing.expectEqual(mm0.CompilerDiagnosticSource.mm0, diag.source);
    try std.testing.expectEqualStrings("zero", diag.name.?);
    const span = diag.span orelse return error.ExpectedDiagnosticSpan;
    try std.testing.expectEqualStrings("@bogus", mm0_src[span.start..span.end]);
}

test "compiler pinpoints invalid fallback annotations" {
    const mm0_src =
        \\provable sort wff;
        \\term top: wff;
        \\--| @fallback
        \\axiom top_i: $ top $;
    ;

    var compiler = Compiler.init(std.testing.allocator, mm0_src);
    try std.testing.expectError(error.InvalidFallbackAnnotation, compiler.check());

    const diag = compiler.diagnostics.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.InvalidFallbackAnnotation, diag.err);
    try std.testing.expectEqual(mm0.CompilerDiagnosticSource.mm0, diag.source);
    try std.testing.expectEqualStrings("top_i", diag.name.?);
    const span = diag.span orelse return error.ExpectedDiagnosticSpan;
    try std.testing.expectEqualStrings("@fallback", mm0_src[span.start..span.end]);
}

test "compiler pinpoints duplicate fallback annotations" {
    const mm0_src =
        \\provable sort wff;
        \\term top: wff;
        \\axiom top_j: $ top $;
        \\axiom top_k: $ top $;
        \\--| @fallback top_j
        \\--| @fallback top_k
        \\axiom top_i: $ top $;
    ;

    var compiler = Compiler.init(std.testing.allocator, mm0_src);
    try std.testing.expectError(error.DuplicateFallbackAnnotation, compiler.check());

    const diag = compiler.diagnostics.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.DuplicateFallbackAnnotation, diag.err);
    try std.testing.expectEqual(mm0.CompilerDiagnosticSource.mm0, diag.source);
    try std.testing.expectEqualStrings("top_i", diag.name.?);
    const span = diag.span orelse return error.ExpectedDiagnosticSpan;
    try std.testing.expectEqualStrings("@fallback top_j", mm0_src[span.start..span.end]);
}

test "compiler pinpoints unknown fallback rules" {
    const mm0_src =
        \\provable sort wff;
        \\term top: wff;
        \\--| @fallback missing_rule
        \\axiom top_i: $ top $;
    ;

    var compiler = Compiler.init(std.testing.allocator, mm0_src);
    try std.testing.expectError(error.UnknownFallbackRule, compiler.check());

    const diag = compiler.diagnostics.last_diagnostic orelse
        return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.UnknownFallbackRule, diag.err);
    try std.testing.expectEqual(mm0.CompilerDiagnosticSource.mm0, diag.source);
    try std.testing.expectEqualStrings("top_i", diag.name.?);
    const span = diag.span orelse return error.ExpectedDiagnosticSpan;
    try std.testing.expectEqualStrings(
        "@fallback missing_rule",
        mm0_src[span.start..span.end],
    );
}

test "compiler stores auto forward annotations" {
    const mm0_src =
        \\provable sort wff;
        \\term top: wff;
        \\--| @auto forward
        \\axiom top_i: $ top $;
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var metadata = try processAnnotatedMetadata(arena.allocator(), mm0_src);
    const rule_id = metadata.env.getRuleId("top_i") orelse {
        return error.MissingRule;
    };
    try std.testing.expect(metadata.registry.isAutoForwardRule(rule_id));
    try std.testing.expectEqual(
        @as(usize, 1),
        metadata.registry.autoForwardRuleCount(),
    );
}

test "compiler stores auto backward annotations" {
    const mm0_src =
        \\provable sort wff;
        \\term top: wff;
        \\--| @auto backward
        \\axiom top_i: $ top $;
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var metadata = try processAnnotatedMetadata(arena.allocator(), mm0_src);
    const rule_id = metadata.env.getRuleId("top_i") orelse {
        return error.MissingRule;
    };
    try std.testing.expect(metadata.registry.isAutoBackwardRule(rule_id));
    try std.testing.expectEqual(
        @as(usize, 1),
        metadata.registry.autoBackwardRuleCount(),
    );
    // forward and backward are independent enrollments.
    try std.testing.expect(!metadata.registry.isAutoForwardRule(rule_id));
    try std.testing.expectEqual(
        @as(usize, 0),
        metadata.registry.autoForwardRuleCount(),
    );
}

test "compiler stores auto eager annotations (default priority, implies backward)" {
    const mm0_src =
        \\provable sort wff;
        \\term top: wff;
        \\term and (p q: wff): wff;
        \\--| @auto eager
        \\axiom and_i (a b: wff) (h1: $ a $) (h2: $ b $): $ and a b $;
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var metadata = try processAnnotatedMetadata(arena.allocator(), mm0_src);
    const rule_id = metadata.env.getRuleId("and_i") orelse {
        return error.MissingRule;
    };
    try std.testing.expectEqual(
        @as(?u8, 1),
        metadata.registry.eagerPriority(rule_id),
    );
    try std.testing.expectEqual(
        @as(usize, 1),
        metadata.registry.autoEagerRuleCount(),
    );
    // Eager implies backward enrollment.
    try std.testing.expect(metadata.registry.isAutoBackwardRule(rule_id));
    // ... but eager rules never defer a witness, so an eager-only theory
    // must not trigger witness-pool setup.
    try std.testing.expect(
        !metadata.registry.hasWitnessBackwardRules(&metadata.env),
    );
}

test "hasWitnessBackwardRules: premise-only binder flips it on" {
    // `mp`'s cut formula `a` occurs only in the hypotheses: enrolling it
    // backward makes it a witness-deferring rule.
    const mm0_src =
        \\provable sort wff;
        \\term imp (p q: wff): wff;
        \\--| @auto backward
        \\axiom mp (a b: wff) (h1: $ imp a b $) (h2: $ a $): $ b $;
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var metadata = try processAnnotatedMetadata(arena.allocator(), mm0_src);
    const rule_id = metadata.env.getRuleId("mp") orelse {
        return error.MissingRule;
    };
    try std.testing.expect(metadata.registry.isAutoBackwardRule(rule_id));
    try std.testing.expect(
        metadata.registry.hasWitnessBackwardRules(&metadata.env),
    );
}

test "hasWitnessBackwardRules: conclusion-determined backward rule stays off" {
    const mm0_src =
        \\provable sort wff;
        \\term and (p q: wff): wff;
        \\--| @auto backward
        \\axiom and_i (a b: wff) (h1: $ a $) (h2: $ b $): $ and a b $;
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var metadata = try processAnnotatedMetadata(arena.allocator(), mm0_src);
    const rule_id = metadata.env.getRuleId("and_i") orelse {
        return error.MissingRule;
    };
    try std.testing.expect(metadata.registry.isAutoBackwardRule(rule_id));
    try std.testing.expect(
        !metadata.registry.hasWitnessBackwardRules(&metadata.env),
    );
}

test "hasWitnessBackwardRules: bound binder counts as a pool consumer" {
    // `ax_gen`-style generalization: every binder occurs in the conclusion
    // (no deferred witness), but the bound `{x}` needs a concrete variable
    // name from the pool when applied backward.
    const mm0_src =
        \\provable sort wff;
        \\sort nat;
        \\term all {x: nat} (p: wff x): wff;
        \\--| @auto backward
        \\axiom gen {x: nat} (p: wff x) (h: $ p $): $ all x p $;
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var metadata = try processAnnotatedMetadata(arena.allocator(), mm0_src);
    const rule_id = metadata.env.getRuleId("gen") orelse {
        return error.MissingRule;
    };
    try std.testing.expect(metadata.registry.isAutoBackwardRule(rule_id));
    try std.testing.expect(
        metadata.registry.hasWitnessBackwardRules(&metadata.env),
    );
}

test "compiler stores auto eager annotations with explicit priority" {
    const mm0_src =
        \\provable sort wff;
        \\term top: wff;
        \\term and (p q: wff): wff;
        \\--| @auto eager 3
        \\axiom and_i (a b: wff) (h1: $ a $) (h2: $ b $): $ and a b $;
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var metadata = try processAnnotatedMetadata(arena.allocator(), mm0_src);
    const rule_id = metadata.env.getRuleId("and_i") orelse {
        return error.MissingRule;
    };
    try std.testing.expectEqual(
        @as(?u8, 3),
        metadata.registry.eagerPriority(rule_id),
    );
}

test "compiler rejects auto eager priority zero and trailing junk" {
    const zero_src =
        \\provable sort wff;
        \\term top: wff;
        \\--| @auto eager 0
        \\axiom top_i: $ top $;
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    try std.testing.expectError(
        error.InvalidAutoAnnotation,
        processAnnotatedMetadata(arena.allocator(), zero_src),
    );

    const junk_src =
        \\provable sort wff;
        \\term top: wff;
        \\--| @auto eager 2 junk
        \\axiom top_i: $ top $;
    ;
    try std.testing.expectError(
        error.InvalidAutoAnnotation,
        processAnnotatedMetadata(arena.allocator(), junk_src),
    );
}

test "compiler rejects auto eager on a witness-deferring rule" {
    // `mp`'s antecedent `a` appears only in the hypotheses: a backward
    // application must defer it as an existential witness, so a depth-free
    // eager step would be a self-feeding cascade — annotation error.
    const mm0_src =
        \\provable sort wff;
        \\term im (p q: wff): wff;
        \\--| @auto eager
        \\axiom mp (a b: wff) (h1: $ im a b $) (h2: $ a $): $ b $;
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    try std.testing.expectError(
        error.EagerRuleDefersWitness,
        processAnnotatedMetadata(arena.allocator(), mm0_src),
    );
}

test "compiler accepts tab-separated auto forward annotations" {
    const mm0_src =
        "provable sort wff;\n" ++
        "term top: wff;\n" ++
        "--| @auto\tforward\n" ++
        "axiom top_i: $ top $;\n";

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var metadata = try processAnnotatedMetadata(arena.allocator(), mm0_src);
    const rule_id = metadata.env.getRuleId("top_i") orelse {
        return error.MissingRule;
    };
    try std.testing.expect(metadata.registry.isAutoForwardRule(rule_id));
    try std.testing.expectEqual(
        @as(usize, 1),
        metadata.registry.autoForwardRuleCount(),
    );
}

test "compiler rejects malformed auto annotations" {
    const mm0_src =
        \\provable sort wff;
        \\term top: wff;
        \\--| @auto sideways
        \\axiom top_i: $ top $;
    ;

    var compiler = Compiler.init(std.testing.allocator, mm0_src);
    try std.testing.expectError(error.InvalidAutoAnnotation, compiler.check());

    const diag = compiler.diagnostics.last_diagnostic orelse
        return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.InvalidAutoAnnotation, diag.err);
    try std.testing.expectEqual(mm0.CompilerDiagnosticSource.mm0, diag.source);
    try std.testing.expectEqualStrings("top_i", diag.name.?);
    try std.testing.expectEqualStrings(
        "@auto expects one mode: forward, backward, " ++
            "eager [PRIORITY >= 1], or trigger PATTERN",
        mm0.compilerDiagnosticSummary(diag),
    );
    const span = diag.span orelse return error.ExpectedDiagnosticSpan;
    try std.testing.expectEqualStrings(
        "@auto sideways",
        mm0_src[span.start..span.end],
    );
}

test "compiler rejects extra tab-separated auto annotation tokens" {
    const mm0_src =
        "provable sort wff;\n" ++
        "term top: wff;\n" ++
        "--| @auto\tforward junk\n" ++
        "axiom top_i: $ top $;\n";

    var compiler = Compiler.init(std.testing.allocator, mm0_src);
    try std.testing.expectError(error.InvalidAutoAnnotation, compiler.check());

    const diag = compiler.diagnostics.last_diagnostic orelse
        return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.InvalidAutoAnnotation, diag.err);
    const span = diag.span orelse return error.ExpectedDiagnosticSpan;
    try std.testing.expectEqualStrings(
        "@auto\tforward junk",
        mm0_src[span.start..span.end],
    );
}

// Shared prelude for the `@conversion` annotation tests: a wff relation
// bundle plus a binary connective to convert under.
const conversion_mm0_prelude =
    \\delimiter $ ( ) $;
    \\provable sort wff;
    \\term top: wff;
    \\term iff (p q: wff): wff;
    \\term an (p q: wff): wff;
    \\--| @relation wff iff iff_refl iff_trans iff_symm mpbi
    \\axiom iff_refl (a: wff): $ iff a a $;
    \\
;

test "compiler stores conversion annotations with direction flags" {
    const mm0_src = conversion_mm0_prelude ++
        \\--| @conversion both
        \\axiom an_comm (a b: wff): $ iff (an a b) (an b a) $;
        \\--| @conversion rtl
        \\axiom an_idem (a: wff): $ iff a (an a a) $;
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var metadata = try processAnnotatedMetadata(arena.allocator(), mm0_src);
    const rules = metadata.registry.conversionRules();
    try std.testing.expectEqual(@as(usize, 2), rules.len);

    const comm_id = metadata.env.getRuleId("an_comm") orelse {
        return error.MissingRule;
    };
    try std.testing.expectEqual(comm_id, rules[0].rule_id);
    try std.testing.expect(rules[0].ltr);
    try std.testing.expect(rules[0].rtl);
    try std.testing.expectEqual(@as(usize, 2), rules[0].num_binders);

    const idem_id = metadata.env.getRuleId("an_idem") orelse {
        return error.MissingRule;
    };
    try std.testing.expectEqual(idem_id, rules[1].rule_id);
    try std.testing.expect(!rules[1].ltr);
    try std.testing.expect(rules[1].rtl);
    try std.testing.expectEqual(@as(usize, 1), rules[1].num_binders);
}

test "compiler validates conversion annotation direction tokens" {
    const cases = [_][]const u8{
        "--| @conversion",
        "--| @conversion sideways",
        "--| @conversion ltr junk",
    };
    for (cases) |annotation_line| {
        var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
        defer arena.deinit();
        const mm0_src = try std.mem.concat(arena.allocator(), u8, &.{
            conversion_mm0_prelude,
            annotation_line,
            "\naxiom an_comm (a b: wff): $ iff (an a b) (an b a) $;\n",
        });
        try std.testing.expectError(
            error.InvalidConversionAnnotation,
            processAnnotatedMetadata(arena.allocator(), mm0_src),
        );
    }
}

test "compiler reports invalid compute annotations with spans" {
    const cases = [_][]const u8{
        "@compute",
        "@compute sideways",
        "@compute ltr junk",
    };
    for (cases) |annotation| {
        var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
        defer arena.deinit();
        const mm0_src = try std.mem.concat(arena.allocator(), u8, &.{
            conversion_mm0_prelude,
            "--| ",
            annotation,
            "\naxiom an_comm (a b: wff): $ iff (an a b) (an b a) $;\n",
        });

        var compiler = Compiler.init(std.testing.allocator, mm0_src);
        try std.testing.expectError(
            error.InvalidComputeAnnotation,
            compiler.check(),
        );

        const diag = compiler.diagnostics.last_diagnostic orelse
            return error.ExpectedDiagnostic;
        try std.testing.expectEqual(error.InvalidComputeAnnotation, diag.err);
        try std.testing.expectEqual(
            mm0.CompilerDiagnosticSource.mm0,
            diag.source,
        );
        try std.testing.expectEqualStrings("an_comm", diag.name.?);
        try std.testing.expectEqualStrings(
            "@compute expects one token: ltr or rtl",
            mm0.compilerDiagnosticSummary(diag),
        );
        const span = diag.span orelse return error.ExpectedDiagnosticSpan;
        try std.testing.expectEqualStrings(
            annotation,
            mm0_src[span.start..span.end],
        );
    }
}

test "compiler reports duplicate compute annotations with a span" {
    const mm0_src = conversion_mm0_prelude ++
        \\--| @compute ltr
        \\--| @compute rtl
        \\axiom an_comm (a b: wff): $ iff (an a b) (an b a) $;
    ;

    var compiler = Compiler.init(std.testing.allocator, mm0_src);
    try std.testing.expectError(
        error.DuplicateComputeAnnotation,
        compiler.check(),
    );

    const diag = compiler.diagnostics.last_diagnostic orelse
        return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.DuplicateComputeAnnotation, diag.err);
    try std.testing.expectEqual(mm0.CompilerDiagnosticSource.mm0, diag.source);
    try std.testing.expectEqualStrings("an_comm", diag.name.?);
    try std.testing.expectEqualStrings(
        "this rule is already enrolled for conversion? " ++
            "(one @compute/@conversion enrollment per rule)",
        mm0.compilerDiagnosticSummary(diag),
    );
    const span = diag.span orelse return error.ExpectedDiagnosticSpan;
    try std.testing.expectEqualStrings(
        "@compute ltr",
        mm0_src[span.start..span.end],
    );
}

test "compiler rejects conversion conclusions that are not a relation" {
    // Not a binary application at all.
    const shape_src = conversion_mm0_prelude ++
        \\--| @conversion ltr
        \\axiom top_i: $ top $;
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    try std.testing.expectError(
        error.ConversionConclusionNotRelation,
        processAnnotatedMetadata(arena.allocator(), shape_src),
    );

    // Binary application, but its head is not the registered @relation term.
    const wrong_rel_src = conversion_mm0_prelude ++
        \\--| @conversion ltr
        \\axiom an_intro (a b: wff): $ an a b $;
    ;
    try std.testing.expectError(
        error.ConversionMissingRelation,
        processAnnotatedMetadata(arena.allocator(), wrong_rel_src),
    );

    // Right shape, but no @relation bundle was registered for the sort.
    const no_relation_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term iff (p q: wff): wff;
        \\term an (p q: wff): wff;
        \\--| @conversion ltr
        \\axiom an_comm (a b: wff): $ iff (an a b) (an b a) $;
    ;
    try std.testing.expectError(
        error.ConversionMissingRelation,
        processAnnotatedMetadata(arena.allocator(), no_relation_src),
    );
}

test "compiler rejects conversion rules with hypotheses" {
    const mm0_src = conversion_mm0_prelude ++
        \\--| @conversion ltr
        \\axiom an_cond (a b: wff) (h: $ a $): $ iff (an a b) (an b a) $;
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    try std.testing.expectError(
        error.ConversionRuleHasHypotheses,
        processAnnotatedMetadata(arena.allocator(), mm0_src),
    );
}

// Prelude for the `@conversion alpha` enrollment tests: a binder head, a
// substitution term, plus decoy heads for the negative shapes (a term
// with a REGULAR nat position and a term with two bound positions).
const alpha_annotation_prelude =
    \\delimiter $ ( ) $;
    \\provable sort wff;
    \\sort nat;
    \\term iff (p q: wff): wff;
    \\term all {x: nat} (p: wff x): wff;
    \\term ex {x: nat} (p: wff x): wff;
    \\term sb {x: nat} (a: nat) (p: wff x): wff;
    \\term at (a: nat) (p: wff): wff;
    \\term pr2 {x y: nat} (p: wff): wff;
    \\--| @relation wff iff iff_refl iff_trans iff_symm mpbi
    \\axiom iff_refl (a: wff): $ iff a a $;
    \\
;

test "compiler stores a valid alpha conversion annotation with its slots" {
    const mm0_src = alpha_annotation_prelude ++
        \\--| @conversion alpha
        \\axiom all_alpha {x y: nat} (p: wff x): $ iff (all x p) (all y (sb x y p)) $;
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var metadata = try processAnnotatedMetadata(arena.allocator(), mm0_src);
    const rules = metadata.registry.conversionRules();
    try std.testing.expectEqual(@as(usize, 1), rules.len);
    try std.testing.expect(rules[0].role == .alpha);
    try std.testing.expectEqual(@as(u32, 0), rules[0].alpha_old_slot);
    try std.testing.expectEqual(@as(u32, 1), rules[0].alpha_new_slot);
}

test "compiler rejects malformed alpha conversion annotations" {
    const cases = [_][]const u8{
        // The renamed pair sits at a REGULAR argument position of the
        // head: the egraph stores that position as a class, so the
        // pairing scheduler could never collect an instance — the rule
        // would enroll but stay permanently inert.
        "axiom bad_pos {x y: nat} (p: wff): $ iff (at x p) (at y p) $;",
        // The fresh binder already occurs on the left.
        "axiom bad_left {x y: nat} (p: wff x): " ++
            "$ iff (all x (sb x y p)) (all y (sb x y p)) $;",
        // A bare-binder side (no head application).
        "axiom bad_bare (a: wff): $ iff a a $;",
        // The two sides have different heads.
        "axiom bad_heads {x y: nat} (p: wff x): " ++
            "$ iff (all x p) (ex y (sb x y p)) $;",
        // No renamed position at all.
        "axiom bad_same {x: nat} (p: wff x): $ iff (all x p) (all x p) $;",
        // Two renamed positions.
        "axiom bad_two {x y z w: nat} (p: wff): " ++
            "$ iff (pr2 x y p) (pr2 z w p) $;",
    };
    for (cases) |axiom_line| {
        var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
        defer arena.deinit();
        const mm0_src = try std.mem.concat(arena.allocator(), u8, &.{
            alpha_annotation_prelude,
            "--| @conversion alpha\n",
            axiom_line,
            "\n",
        });
        try std.testing.expectError(
            error.ConversionAlphaRuleShape,
            processAnnotatedMetadata(arena.allocator(), mm0_src),
        );
    }
}

test "compiler rejects conversion orientations that cannot match or cover" {
    // ltr on `iff a (an a a)`: the match side is a bare binder.
    const bare_src = conversion_mm0_prelude ++
        \\--| @conversion ltr
        \\axiom an_idem (a: wff): $ iff a (an a a) $;
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    try std.testing.expectError(
        error.ConversionBareMatchSide,
        processAnnotatedMetadata(arena.allocator(), bare_src),
    );

    // ltr on `iff (an a a) (an a b)`: the match side never binds `b`, so the
    // instantiate side would have to invent it.
    const coverage_src = conversion_mm0_prelude ++
        \\--| @conversion ltr
        \\axiom an_cov (a b: wff): $ iff (an a a) (an a b) $;
    ;
    try std.testing.expectError(
        error.ConversionBinderNotCovered,
        processAnnotatedMetadata(arena.allocator(), coverage_src),
    );
}

test "compiler rejects duplicate conversion annotations" {
    const mm0_src = conversion_mm0_prelude ++
        \\--| @conversion ltr
        \\--| @conversion rtl
        \\axiom an_comm (a b: wff): $ iff (an a b) (an b a) $;
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    try std.testing.expectError(
        error.DuplicateConversionAnnotation,
        processAnnotatedMetadata(arena.allocator(), mm0_src),
    );
}

test "compiler stores conversion role annotations as both-direction rules" {
    const mm0_src = conversion_mm0_prelude ++
        \\--| @conversion comm
        \\axiom an_comm (a b: wff): $ iff (an a b) (an b a) $;
        \\--| @conversion assoc
        \\axiom an_assoc (a b c: wff):
        \\  $ iff (an (an a b) c) (an a (an b c)) $;
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var metadata = try processAnnotatedMetadata(arena.allocator(), mm0_src);
    const rules = metadata.registry.conversionRules();
    try std.testing.expectEqual(@as(usize, 2), rules.len);

    const an_id = metadata.env.term_names.get("an") orelse {
        return error.MissingTerm;
    };
    for (rules) |rule| {
        // Role rules permanently enroll with both orientations: fully
        // certified heads are absorbed into bag interning at search time
        // (and skipped there), but a single-certificate head relies on
        // these flags to saturate as an ordinary rule.
        try std.testing.expect(rule.ltr);
        try std.testing.expect(rule.rtl);
        try std.testing.expectEqual(an_id, rule.head_term_id.?);
    }
    try std.testing.expectEqual(ConversionRole.comm, rules[0].role);
    try std.testing.expectEqual(ConversionRole.assoc, rules[1].role);
}

test "compiler accepts assoc certificates in either orientation" {
    const mm0_src = conversion_mm0_prelude ++
        \\--| @conversion assoc
        \\axiom an_assoc (a b c: wff):
        \\  $ iff (an a (an b c)) (an (an a b) c) $;
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var metadata = try processAnnotatedMetadata(arena.allocator(), mm0_src);
    const rules = metadata.registry.conversionRules();
    try std.testing.expectEqual(@as(usize, 1), rules.len);
    try std.testing.expectEqual(ConversionRole.assoc, rules[0].role);
}

test "compiler accepts one role certificate per law per operator" {
    // Distinct operators may each certify the same law — the per-operator
    // scoping is exactly what `@acui`'s one-combiner-per-sort rule forbids.
    const mm0_src = conversion_mm0_prelude ++
        \\term or (p q: wff): wff;
        \\--| @conversion comm
        \\axiom an_comm (a b: wff): $ iff (an a b) (an b a) $;
        \\--| @conversion comm
        \\axiom or_comm (a b: wff): $ iff (or a b) (or b a) $;
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var metadata = try processAnnotatedMetadata(arena.allocator(), mm0_src);
    try std.testing.expectEqual(
        @as(usize, 2),
        metadata.registry.conversionRules().len,
    );
}

test "compiler rejects role certificates on a registered relation head" {
    // iff is classically assoc+comm, but certifying the relation itself
    // would intern every rel(lhs, rhs) pool fact as a bag, silently
    // disabling local-equation citation.
    const mm0_src = conversion_mm0_prelude ++
        \\--| @conversion comm
        \\axiom iff_comm (a b: wff): $ iff (iff a b) (iff b a) $;
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    try std.testing.expectError(
        error.ConversionRoleRelationHead,
        processAnnotatedMetadata(arena.allocator(), mm0_src),
    );
}

test "compiler rejects duplicate role certificates for one operator" {
    const mm0_src = conversion_mm0_prelude ++
        \\--| @conversion comm
        \\axiom an_comm (a b: wff): $ iff (an a b) (an b a) $;
        \\--| @conversion comm
        \\axiom an_comm2 (a b: wff): $ iff (an a b) (an b a) $;
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    try std.testing.expectError(
        error.DuplicateConversionRoleForHead,
        processAnnotatedMetadata(arena.allocator(), mm0_src),
    );
}

test "compiler rejects malformed comm certificates" {
    const cases = [_][]const u8{
        // Not swapped.
        "axiom bad (a b: wff): $ iff (an a b) (an a b) $;\n",
        // Idempotence, not commutativity.
        "axiom bad (a: wff): $ iff (an a a) (an a a) $;\n",
        // Bare binder side.
        "axiom bad (a b: wff): $ iff a (an b a) $;\n",
        // Extra binder beyond the law's two.
        "axiom bad (a b c: wff): $ iff (an a b) (an b a) $;\n",
    };
    for (cases) |axiom_line| {
        var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
        defer arena.deinit();
        const mm0_src = try std.mem.concat(arena.allocator(), u8, &.{
            conversion_mm0_prelude,
            "--| @conversion comm\n",
            axiom_line,
        });
        try std.testing.expectError(
            error.ConversionCommRuleShape,
            processAnnotatedMetadata(arena.allocator(), mm0_src),
        );
    }
}

test "compiler rejects malformed assoc certificates" {
    const cases = [_][]const u8{
        // Commutativity shape under the assoc token.
        "axiom bad (a b c: wff): $ iff (an a b) (an b a) $;\n",
        // Repeated binder.
        "axiom bad (a b c: wff): $ iff (an (an a b) a) (an a (an b a)) $;\n",
        // Association that also permutes.
        "axiom bad (a b c: wff): $ iff (an (an a b) c) (an b (an a c)) $;\n",
    };
    for (cases) |axiom_line| {
        var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
        defer arena.deinit();
        const mm0_src = try std.mem.concat(arena.allocator(), u8, &.{
            conversion_mm0_prelude,
            "--| @conversion assoc\n",
            axiom_line,
        });
        try std.testing.expectError(
            error.ConversionAssocRuleShape,
            processAnnotatedMetadata(arena.allocator(), mm0_src),
        );
    }
}

const def_conversion_prelude =
    \\delimiter $ ( ) $;
    \\sort var;
    \\provable sort wff;
    \\term iff (p q: wff): wff;
    \\term an (p q: wff): wff;
    \\term eqv (a b: var): wff;
    \\term ex {x: var} (p: wff x): wff;
    \\--| @relation wff iff iff_refl iff_trans iff_symm mpbi
    \\axiom iff_refl (a: wff): $ iff a a $;
    \\
;

test "compiler stores def conversion orientations" {
    const mm0_src = def_conversion_prelude ++
        \\--| @conversion fold
        \\def dup (a: wff): wff = $ an a a $;
        \\--| @conversion both
        \\def dup2 (a b: wff): wff = $ an a (an b b) $;
        \\--| @conversion fold
        \\def someeq {.w: var} (v: var): wff = $ ex w (eqv w v) $;
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var metadata = try processAnnotatedMetadata(arena.allocator(), mm0_src);
    const rules = metadata.registry.defConversionRules();
    try std.testing.expectEqual(@as(usize, 3), rules.len);

    const dup_id = metadata.env.term_names.get("dup") orelse {
        return error.MissingTerm;
    };
    try std.testing.expectEqual(dup_id, rules[0].term_id);
    try std.testing.expect(rules[0].fold);
    try std.testing.expect(!rules[0].unfold);
    try std.testing.expectEqual(@as(usize, 1), rules[0].num_binders);

    try std.testing.expect(rules[1].fold);
    try std.testing.expect(rules[1].unfold);
    try std.testing.expectEqual(@as(usize, 2), rules[1].num_binders);

    // The hidden dummy claims a binder slot after the args.
    try std.testing.expectEqual(@as(usize, 2), rules[2].num_binders);
    try std.testing.expect(rules[2].fold);
    try std.testing.expect(!rules[2].unfold);
}

test "compiler rejects unfold orientations on hidden-dummy defs" {
    const tokens = [_][]const u8{ "unfold", "both" };
    for (tokens) |token| {
        var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
        defer arena.deinit();
        const mm0_src = try std.mem.concat(arena.allocator(), u8, &.{
            def_conversion_prelude,
            "--| @conversion ",
            token,
            "\ndef someeq {.w: var} (v: var): wff = $ ex w (eqv w v) $;\n",
        });
        try std.testing.expectError(
            error.ConversionDefUnfoldHiddenDummies,
            processAnnotatedMetadata(arena.allocator(), mm0_src),
        );
    }
}

test "compiler validates def conversion tokens and shapes" {
    // A theorem-only token on a def.
    {
        var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
        defer arena.deinit();
        const mm0_src = def_conversion_prelude ++
            \\--| @conversion ltr
            \\def dup (a: wff): wff = $ an a a $;
        ;
        try std.testing.expectError(
            error.InvalidDefConversionAnnotation,
            processAnnotatedMetadata(arena.allocator(), mm0_src),
        );
    }
    // A def-only token on a theorem.
    {
        var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
        defer arena.deinit();
        const mm0_src = def_conversion_prelude ++
            \\--| @conversion fold
            \\axiom an_comm (a b: wff): $ iff (an a b) (an b a) $;
        ;
        try std.testing.expectError(
            error.InvalidConversionAnnotation,
            processAnnotatedMetadata(arena.allocator(), mm0_src),
        );
    }
    // A plain term has no definiens to enroll.
    {
        var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
        defer arena.deinit();
        const mm0_src = def_conversion_prelude ++
            \\--| @conversion fold
            \\term also (p q: wff): wff;
        ;
        try std.testing.expectError(
            error.ConversionTermNotDef,
            processAnnotatedMetadata(arena.allocator(), mm0_src),
        );
    }
    // Folding a definiens that drops an arg would have to invent it.
    {
        var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
        defer arena.deinit();
        const mm0_src = def_conversion_prelude ++
            \\--| @conversion fold
            \\def fst (a b: wff): wff = $ an a a $;
        ;
        try std.testing.expectError(
            error.ConversionBinderNotCovered,
            processAnnotatedMetadata(arena.allocator(), mm0_src),
        );
    }
    // A bare-binder definiens would match every class.
    {
        var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
        defer arena.deinit();
        const mm0_src = def_conversion_prelude ++
            \\--| @conversion fold
            \\def same (a: wff): wff = $ a $;
        ;
        try std.testing.expectError(
            error.ConversionBareMatchSide,
            processAnnotatedMetadata(arena.allocator(), mm0_src),
        );
    }
    // No @relation bundle registered for the def's sort.
    {
        var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
        defer arena.deinit();
        const mm0_src =
            \\delimiter $ ( ) $;
            \\provable sort wff;
            \\term an (p q: wff): wff;
            \\--| @conversion fold
            \\def dup (a: wff): wff = $ an a a $;
        ;
        try std.testing.expectError(
            error.ConversionMissingRelation,
            processAnnotatedMetadata(arena.allocator(), mm0_src),
        );
    }
}

test "compiler rejects role certificates with bound binders" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\sort var;
        \\provable sort wff;
        \\term iff (p q: wff): wff;
        \\term an (p q: wff): wff;
        \\--| @relation wff iff iff_refl iff_trans iff_symm mpbi
        \\axiom iff_refl (a: wff): $ iff a a $;
        \\--| @conversion comm
        \\axiom an_comm {x: var} (a b: wff): $ iff (an a b) (an b a) $;
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    try std.testing.expectError(
        error.ConversionRoleBoundBinder,
        processAnnotatedMetadata(arena.allocator(), mm0_src),
    );
}

test "compiler reports conversion annotation diagnostics with spans" {
    const mm0_src = conversion_mm0_prelude ++
        \\--| @conversion sideways
        \\axiom an_comm (a b: wff): $ iff (an a b) (an b a) $;
    ;

    var compiler = Compiler.init(std.testing.allocator, mm0_src);
    try std.testing.expectError(
        error.InvalidConversionAnnotation,
        compiler.check(),
    );

    const diag = compiler.diagnostics.last_diagnostic orelse
        return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.InvalidConversionAnnotation, diag.err);
    try std.testing.expectEqual(mm0.CompilerDiagnosticSource.mm0, diag.source);
    try std.testing.expectEqualStrings("an_comm", diag.name.?);
    try std.testing.expectEqualStrings(
        "@conversion expects one token: ltr, rtl, both, assoc, or comm",
        mm0.compilerDiagnosticSummary(diag),
    );
    const span = diag.span orelse return error.ExpectedDiagnosticSpan;
    try std.testing.expectEqualStrings(
        "@conversion sideways",
        mm0_src[span.start..span.end],
    );
}

// Shared prelude for the `@auto trigger` annotation tests: enough context
// machinery that `ax`'s unnamed `G` binder can default to the ACUI unit.
const trigger_mm0_prelude =
    \\delimiter $ ( ) $;
    \\provable sort wff;
    \\sort ctx;
    \\term im (p q: wff): wff;
    \\term emp: ctx;
    \\--| @acui ctx_assoc ctx_comm emp
    \\term join (G H: ctx): ctx;
    \\term hyp (p: wff): ctx;
    \\term nd (G: ctx) (p: wff): wff;
    \\
;

test "compiler parses auto trigger annotations" {
    const mm0_src = trigger_mm0_prelude ++
        \\--| @auto trigger (hyp p)
        \\--| @auto trigger (im p _)
        \\axiom ax (G: ctx) (p: wff): $ nd (join G (hyp p)) p $;
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var metadata = try processAnnotatedMetadata(arena.allocator(), mm0_src);
    const rule_id = metadata.env.getRuleId("ax") orelse {
        return error.MissingRule;
    };
    try std.testing.expectEqual(
        @as(usize, 1),
        metadata.registry.triggerRuleCount(),
    );
    const patterns = metadata.registry.trigger_by_rule.get(rule_id) orelse {
        return error.MissingTriggerPatterns;
    };
    try std.testing.expectEqual(@as(usize, 2), patterns.items.len);
    // `(hyp p)`: unary app capturing binder 1 (`p`).
    const hyp_pattern = patterns.items[0];
    try std.testing.expect(hyp_pattern == .app);
    try std.testing.expectEqual(@as(usize, 1), hyp_pattern.app.args.len);
    try std.testing.expectEqual(
        mm0.RewriteRegistry.TriggerPattern{ .binder = 1 },
        hyp_pattern.app.args[0],
    );
    // `(im p _)`: binary app, capture then wildcard.
    const im_pattern = patterns.items[1];
    try std.testing.expect(im_pattern == .app);
    try std.testing.expectEqual(@as(usize, 2), im_pattern.app.args.len);
    try std.testing.expectEqual(
        mm0.RewriteRegistry.TriggerPattern{ .binder = 1 },
        im_pattern.app.args[0],
    );
    try std.testing.expect(im_pattern.app.args[1] == .wildcard);
}

test "compiler rejects auto trigger on a rule with hypotheses" {
    const mm0_src = trigger_mm0_prelude ++
        \\--| @auto trigger (hyp p)
        \\axiom weak (G: ctx) (p q: wff):
        \\  $ nd G p $ > $ nd (join G (hyp q)) p $;
    ;
    var compiler = Compiler.init(std.testing.allocator, mm0_src);
    try std.testing.expectError(
        error.TriggerRuleHasHypotheses,
        compiler.check(),
    );
}

test "compiler rejects auto trigger leaving a non-context binder unnamed" {
    // `(hyp _)` names neither `p` (wff — no ACUI combiner sort) nor `G`;
    // only `G` can default to a unit, so the seed would not be ground.
    const mm0_src = trigger_mm0_prelude ++
        \\--| @auto trigger (hyp _)
        \\axiom ax (G: ctx) (p: wff): $ nd (join G (hyp p)) p $;
    ;
    var compiler = Compiler.init(std.testing.allocator, mm0_src);
    try std.testing.expectError(
        error.TriggerBinderNotGround,
        compiler.check(),
    );
}

test "compiler rejects auto trigger with a wrong-sort capture" {
    // `join`'s argument positions are ctx-sorted; `p` is a wff binder.
    const mm0_src = trigger_mm0_prelude ++
        \\--| @auto trigger (join p _)
        \\axiom ax (G: ctx) (p: wff): $ nd (join G (hyp p)) p $;
    ;
    var compiler = Compiler.init(std.testing.allocator, mm0_src);
    try std.testing.expectError(
        error.TriggerSortMismatch,
        compiler.check(),
    );
}

test "compiler rejects auto trigger with unbalanced pattern" {
    const mm0_src = trigger_mm0_prelude ++
        \\--| @auto trigger (hyp p
        \\axiom ax (G: ctx) (p: wff): $ nd (join G (hyp p)) p $;
    ;
    var compiler = Compiler.init(std.testing.allocator, mm0_src);
    try std.testing.expectError(
        error.InvalidTriggerAnnotation,
        compiler.check(),
    );
}

test "auto forward annotation is unavailable before its rule" {
    const mm0_src =
        \\provable sort wff;
        \\term top: wff;
        \\axiom early: $ top $;
        \\--| @auto forward
        \\axiom late: $ top $;
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();

    var parser = MM0Parser.init(mm0_src, allocator);
    var env = FrontendEnv.GlobalEnv.init(allocator);
    var registry = RewriteRegistry.init(allocator);
    var fresh_bindings = std.AutoHashMap(
        u32,
        []const CompilerMetadata.FreshDecl,
    ).init(allocator);
    var freshen_bindings = std.AutoHashMap(
        u32,
        []const CompilerMetadata.FreshenDecl,
    ).init(allocator);
    var views = std.AutoHashMap(
        u32,
        CompilerMetadata.ViewDecl,
    ).init(allocator);
    var sort_vars = CompilerMetadata.SortVarRegistry.init(allocator);

    while (try parser.next()) |stmt| {
        try env.addStmt(stmt);
        switch (stmt) {
            .sort => |sort_stmt| {
                try CompilerMetadata.processSortMetadata(
                    &parser,
                    sort_stmt,
                    parser.last_annotations,
                    &sort_vars,
                );
            },
            .term => |term_stmt| {
                try CompilerMetadata.processTermMetadata(
                    &env,
                    &registry,
                    term_stmt,
                    parser.last_annotations,
                );
            },
            .assertion => |assertion| {
                try CompilerMetadata.processAssertionMetadata(
                    allocator,
                    &parser,
                    &env,
                    &registry,
                    &fresh_bindings,
                    &freshen_bindings,
                    &views,
                    assertion,
                    parser.last_annotations,
                );
                if (std.mem.eql(u8, assertion.name, "early")) {
                    const early = env.getRuleId("early") orelse {
                        return error.MissingRule;
                    };
                    try std.testing.expect(!registry.isAutoForwardRule(early));
                    try std.testing.expect(env.getRuleId("late") == null);
                    try std.testing.expectEqual(
                        @as(usize, 0),
                        registry.autoForwardRuleCount(),
                    );
                }
            },
        }
    }

    const late = env.getRuleId("late") orelse return error.MissingRule;
    try std.testing.expect(registry.isAutoForwardRule(late));
}
