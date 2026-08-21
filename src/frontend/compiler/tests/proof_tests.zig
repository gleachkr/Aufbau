const helpers = @import("./helpers.zig");
const std = helpers.std;
const mm0 = helpers.mm0;
const Compiler = helpers.Compiler;
const FrontendEnv = helpers.FrontendEnv;
const FrontendExpr = helpers.FrontendExpr;
const Expr = helpers.Expr;
const MM0Parser = helpers.MM0Parser;
const CompilerViews = helpers.CompilerViews;
const DefOps = helpers.DefOps;
const readProofCaseFile = helpers.readProofCaseFile;
const processAnnotatedMetadata = helpers.processAnnotatedMetadata;

test "compiler env converts rules into binder-indexed templates" {
    const src =
        \\provable sort wff;
        \\term imp (a b: wff): wff;
        \\axiom ax_mp (a b: wff): $ imp a b $ > $ a $ > $ b $;
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = MM0Parser.init(src, arena.allocator());
    var env = FrontendEnv.GlobalEnv.init(arena.allocator());
    while (try parser.next()) |stmt| {
        try env.addStmt(stmt);
    }

    try std.testing.expectEqual(@as(usize, 1), env.rules.items.len);
    const rule = env.rules.items[0];
    try std.testing.expect(rule.kind == .axiom);
    try std.testing.expectEqual(@as(usize, 2), rule.arg_names.len);
    try std.testing.expectEqualStrings("a", rule.arg_names[0].?);
    try std.testing.expectEqualStrings("b", rule.arg_names[1].?);
    try std.testing.expectEqual(@as(usize, 2), rule.hyps.len);
    switch (rule.hyps[0]) {
        .app => |app| {
            try std.testing.expectEqual(@as(u32, 0), app.term_id);
            try std.testing.expectEqual(@as(usize, 2), app.args.len);
            switch (app.args[0]) {
                .binder => |idx| try std.testing.expectEqual(@as(usize, 0), idx),
                else => return error.UnexpectedTemplateExpr,
            }
            switch (app.args[1]) {
                .binder => |idx| try std.testing.expectEqual(@as(usize, 1), idx),
                else => return error.UnexpectedTemplateExpr,
            }
        },
        else => return error.UnexpectedTemplateExpr,
    }
    switch (rule.hyps[1]) {
        .binder => |idx| try std.testing.expectEqual(@as(usize, 0), idx),
        else => return error.UnexpectedTemplateExpr,
    }
    switch (rule.concl) {
        .binder => |idx| try std.testing.expectEqual(@as(usize, 1), idx),
        else => return error.UnexpectedTemplateExpr,
    }
}

test "compiler checks proof blocks in theorem order" {
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
        \\l1: $ top $ by top_i []
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
    try compiler.check();
}

test "compiler accepts multiline proof-line whitespace" {
    const mm0_src =
        \\provable sort wff;
        \\term top: wff;
        \\axiom top_i: $ top $;
        \\theorem first: $ top $;
    ;
    const proof_src =
        \\first
        \\-----
        \\l1:
        \\  $ top $
        \\  -- this comment should not break the line
        \\  by
        \\  top_i
        \\  [
        \\  ]
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    try compiler.check();
}

test "compiler accepts multiline local lemma headers" {
    const mm0_src =
        \\provable sort wff;
        \\axiom keep (a: wff): $ a $ > $ a $;
        \\theorem target (a: wff): $ a $ > $ a $;
    ;
    const proof_src =
        \\lemma helper (a: wff):
        \\  $ a $ >
        \\  $ a $
        \\----------------------
        \\l1: $ a $ by keep [#1]
        \\
        \\target
        \\------
        \\l1: $ a $ by helper [#1]
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

test "compiler applies rewrite annotations on local lemmas" {
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
        \\axiom sb_P_base (a: wff): $ sb a P <-> a $;
        \\--| @congr
        \\axiom pair_congr (a b c d: wff):
        \\  $ a <-> b $ > $ c <-> d $ >
        \\  $ pair a c <-> pair b d $;
        \\axiom all_elim (b: wff): $ pair (sb P P) b $;
        \\theorem target: $ pair P Q $;
    ;
    const proof_src =
        \\lemma prelude: $ P <-> P $
        \\---------------------------
        \\l1: $ P <-> P $ by biid
        \\
        \\--| @rewrite
        \\lemma sb_local (a: wff): $ sb a P <-> a $
        \\-------------------------------------------
        \\l1: $ sb a P <-> a $ by sb_P_base
        \\
        \\target
        \\------
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

test "compiler rejects lemma names that collide with earlier rules" {
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
        \\l1: $ top $ by top_i []
        \\
        \\lemma first: $ top $
        \\------------------
        \\l1: $ top $ by top_i []
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
    try std.testing.expectError(error.DuplicateRuleName, compiler.check());
    const diag = compiler.diagnostics.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.DuplicateRuleName, diag.err);
    try std.testing.expectEqualStrings("first", diag.name.?);
    try std.testing.expect(diag.span != null);
}

test "compiler rejects theorem names that collide with earlier lemmas" {
    const mm0_src =
        \\provable sort wff;
        \\term top: wff;
        \\axiom top_i: $ top $;
        \\theorem helper: $ top $;
    ;
    const proof_src =
        \\lemma helper: $ top $
        \\-------------------
        \\l1: $ top $ by top_i []
        \\
        \\helper
        \\------
        \\l1: $ top $ by top_i []
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    try std.testing.expectError(error.DuplicateRuleName, compiler.check());
    const diag = compiler.diagnostics.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.DuplicateRuleName, diag.err);
    try std.testing.expectEqualStrings("helper", diag.name.?);
}

test "compiler preserves local lemma diagnostics after check returns" {
    const mm0_src =
        \\provable sort wff;
        \\term top: wff;
        \\theorem target: $ top $;
    ;
    const proof_src =
        \\lemma helper: $ top $
        \\--------------------
        \\l1: $ top $ by missing_rule []
        \\
        \\target
        \\------
        \\l1: $ top $ by helper []
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    try std.testing.expectError(error.UnknownRule, compiler.check());

    var churn_arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer churn_arena.deinit();
    const churn = try churn_arena.allocator().alloc(u8, 4096);
    @memset(churn, 0xaa);

    const diag = compiler.diagnostics.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.UnknownRule, diag.err);
    try std.testing.expectEqualStrings("helper", diag.theorem_name.?);
    try std.testing.expectEqualStrings("l1", diag.line_label.?);
    try std.testing.expectEqualStrings("missing_rule", diag.rule_name.?);
}

test "compiler rejects out-of-order and extra proof blocks" {
    const mm0_src =
        \\provable sort wff;
        \\term top: wff;
        \\axiom top_i: $ top $;
        \\theorem first: $ top $;
    ;

    var mismatch = Compiler.initWithProof(std.testing.allocator, mm0_src,
        \\second
        \\------
    );
    try std.testing.expectError(error.TheoremNameMismatch, mismatch.check());

    var extra = Compiler.initWithProof(std.testing.allocator, mm0_src,
        \\first
        \\-----
        \\l1: $ top $ by top_i []
        \\
        \\second
        \\------
    );
    try std.testing.expectError(error.ExtraProofBlock, extra.check());
}

test "compiler accepts trailing local lemmas with no anchor" {
    // A local lemma after the last public block has nothing to anchor to, but
    // it is self-contained; it should be checked/emitted, not rejected.
    const mm0_src =
        \\provable sort wff;
        \\term top: wff;
        \\axiom top_i: $ top $;
        \\theorem first: $ top $;
    ;

    var trailing = Compiler.initWithProof(std.testing.allocator, mm0_src,
        \\first
        \\-----
        \\l1: $ top $ by top_i []
        \\
        \\lemma tail_lemma: $ top $
        \\------------------------
        \\l1: $ top $ by top_i []
    );
    const trailing_mmb = try trailing.compileMmb(std.testing.allocator);
    std.testing.allocator.free(trailing_mmb);

    // A lemmas-only proof against a theorem-free theory is also fine (the
    // embeddable-editor "isolated lemma cell" case).
    const axioms_only =
        \\provable sort wff;
        \\term top: wff;
        \\axiom top_i: $ top $;
    ;
    var solo = Compiler.initWithProof(std.testing.allocator, axioms_only,
        \\lemma solo: $ top $
        \\-------------------
        \\l1: $ top $ by top_i []
    );
    const solo_mmb = try solo.compileMmb(std.testing.allocator);
    std.testing.allocator.free(solo_mmb);
}

test "compiler records proof diagnostics for failing proof lines" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\--| @hole _wff
        \\provable sort wff;
        \\term imp (a b: wff): wff; infixr imp: $->$ prec 25;
        \\axiom ax_keep (a b: wff): $ a $ > $ a -> b -> a $;
        \\theorem keep_label (a b: wff): $ a $ > $ a -> b -> a $;
    ;
    const proof_src =
        \\keep_label
        \\----------
        \\l1: $ a -> b -> a $ by ax_keep (a := $ a $, b := $ b $) [missing]
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    try std.testing.expectError(error.UnknownLabel, compiler.compileMmb(
        std.testing.allocator,
    ));
    const diag = compiler.diagnostics.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.UnknownLabel, diag.err);
    try std.testing.expectEqualStrings("keep_label", diag.theorem_name.?);
    try std.testing.expectEqualStrings("l1", diag.line_label.?);
    try std.testing.expectEqualStrings("missing", diag.name.?);
    try std.testing.expect(diag.span != null);
    try std.testing.expectEqual(mm0.CompilerDiagnosticSource.proof, diag.source);
}

test "compiler pinpoints wrong reference count at the ref list" {
    const mm0_src =
        \\provable sort wff;
        \\term top: wff;
        \\axiom keep (a: wff): $ a $ > $ a $;
        \\theorem bad_refs (a: wff): $ a $ > $ a $;
    ;
    const proof_src =
        \\bad_refs
        \\--------
        \\l1: $ a $ by keep []
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    try std.testing.expectError(error.RefCountMismatch, compiler.compileMmb(
        std.testing.allocator,
    ));

    const diag = compiler.diagnostics.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.RefCountMismatch, diag.err);
    try std.testing.expectEqualStrings("bad_refs", diag.theorem_name.?);
    try std.testing.expectEqualStrings("l1", diag.line_label.?);
    try std.testing.expectEqualStrings("keep", diag.rule_name.?);
    const span = diag.span orelse return error.ExpectedDiagnosticSpan;
    try std.testing.expectEqualStrings("[]", proof_src[span.start..span.end]);
}

test "compiler accepts nested rule applications as refs" {
    const mm0_src =
        \\provable sort wff;
        \\term top: wff;
        \\axiom top_i: $ top $;
        \\axiom keep: $ top $ > $ top $;
        \\theorem target: $ top $;
    ;
    const proof_src =
        \\target
        \\------
        \\l1: $ top $ by keep [top_i []]
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

test "compiler accepts deeply nested rule applications as refs" {
    const mm0_src =
        \\provable sort wff;
        \\term top: wff;
        \\axiom top_i: $ top $;
        \\axiom keep: $ top $ > $ top $;
        \\theorem target: $ top $;
    ;
    const proof_src =
        \\target
        \\------
        \\l1: $ top $ by keep [keep [keep [keep [top_i []]]]]
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

test "compiler accepts inline applications using refs and bindings" {
    const mm0_src =
        \\provable sort wff;
        \\axiom keep (a: wff): $ a $ > $ a $;
        \\theorem target (a: wff): $ a $ > $ a $;
    ;
    const proof_src =
        \\target
        \\------
        \\l1: $ a $ by keep [#1]
        \\l2: $ a $ by keep [keep (a := $ a $) [l1]]
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

test "compiler infers inline application conclusions from refs" {
    const mm0_src =
        \\provable sort wff;
        \\axiom keep (a: wff): $ a $ > $ a $;
        \\theorem target (a: wff): $ a $ > $ a $;
    ;
    const proof_src =
        \\target
        \\------
        \\l1: $ a $ by keep [keep [#1]]
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

test "compiler infers inline child binders through views" {
    const mm0_src =
        \\provable sort wff;
        \\term top: wff;
        \\term raw (a: wff): wff;
        \\def surf (a: wff): wff = $ raw a $;
        \\axiom surf_top: $ surf top $;
        \\axiom keep (a: wff): $ a $ > $ a $;
        \\--| @view (a: wff): $ surf a $ > $ raw a $
        \\axiom raw_keep (a: wff): $ raw a $ > $ raw a $;
        \\theorem target: $ raw top $;
    ;
    const proof_src =
        \\target
        \\------
        \\l1: $ raw top $ by keep [raw_keep [surf_top []]]
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

test "compiler infers nested transparent view binders" {
    const allocator = std.testing.allocator;
    const mm0_src = try readProofCaseFile(
        allocator,
        "pass_nested_transparent_view_infer",
        "mm0",
    );
    defer allocator.free(mm0_src);
    const proof_src = try readProofCaseFile(
        allocator,
        "pass_nested_transparent_view_infer",
        "auf",
    );
    defer allocator.free(proof_src);

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    const mmb = try compiler.compileMmb(std.testing.allocator);
    defer std.testing.allocator.free(mmb);
    try mm0.verifyPair(std.testing.allocator, mm0_src, mmb);
}

fn expectNestedView(
    allocator: std.mem.Allocator,
    with_semantic: bool,
) !void {
    const mm0_src = try readProofCaseFile(
        allocator,
        "pass_nested_transparent_view_infer",
        "mm0",
    );

    var metadata = try processAnnotatedMetadata(allocator, mm0_src);

    var parser = MM0Parser.init(mm0_src, allocator);
    var theorem = FrontendExpr.TheoremContext.init(allocator);
    defer theorem.deinit();
    var theorem_vars = std.StringHashMap(*const Expr).init(allocator);
    defer theorem_vars.deinit();

    const assertion = blk: {
        while (try parser.next()) |stmt| {
            switch (stmt) {
                .assertion => |value| {
                    if (!std.mem.eql(
                        u8,
                        value.name,
                        "pass_nested_transparent_view_infer",
                    )) continue;
                    try theorem.seedAssertion(value);
                    for (value.arg_names, value.arg_exprs) |name, expr| {
                        if (name) |actual_name| {
                            try theorem_vars.put(actual_name, expr);
                        }
                    }
                    break :blk value;
                },
                else => {},
            }
        }
        return error.MissingAssertion;
    };
    _ = assertion;

    const view_rule = metadata.env.getRuleId("sep_elim") orelse {
        return error.MissingRule;
    };
    const view = metadata.views.get(view_rule) orelse {
        return error.MissingView;
    };
    const parsed_line = try parser.parseFormulaText(
        " im (outer a b x y) (body (opair x y) a b) ",
        &theorem_vars,
    );
    const line_expr = try theorem.internParsedExpr(parsed_line);
    const partial_bindings = try allocator.alloc(?FrontendExpr.ExprId, 5);
    defer allocator.free(partial_bindings);
    @memset(partial_bindings, null);

    if (with_semantic) {
        try CompilerViews.applyViewBindings(
            allocator,
            &theorem,
            &metadata.env,
            &metadata.registry,
            &view,
            line_expr,
            &.{},
            partial_bindings,
            null,
            null,
            false,
        );
        // Success here means the view/recover pipeline carried enough
        // symbolic state to accept the nested hidden-dummy match. The full
        // compiler test above finalizes that state through MMB emission.
    } else {
        var def_ops = DefOps.Context.initWithRegistry(
            allocator,
            &theorem,
            &metadata.env,
            &metadata.registry,
        );
        defer def_ops.deinit();
        var seeds = [_]DefOps.BindingSeed{
            .none,
            .none,
            .none,
            .none,
            .none,
        };
        var session = try def_ops.beginRuleMatch(view.arg_infos, &seeds);
        defer session.deinit();
        try std.testing.expect(try session.matchSemantic(
            view.concl,
            line_expr,
            DefOps.default_semantic_match_budget,
        ));

        const bad_line = try parser.parseFormulaText(
            " im (mem (opair x y) (carrier a b)) " ++
                "(body (opair x y) a b) ",
            &theorem_vars,
        );
        const bad_expr = try theorem.internParsedExpr(bad_line);
        var bad_session = try def_ops.beginRuleMatch(view.arg_infos, &seeds);
        defer bad_session.deinit();
        try std.testing.expect(!try bad_session.matchSemantic(
            view.concl,
            bad_expr,
            DefOps.default_semantic_match_budget,
        ));
    }
}

test "nested view matching rejects non-separation actual" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    try expectNestedView(arena.allocator(), false);
}

test "nested view matching preserves hidden dummy witnesses" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    try expectNestedView(arena.allocator(), true);
}

test "nested transparent view proof case keeps binders omitted" {
    const allocator = std.testing.allocator;
    const proof = try readProofCaseFile(
        allocator,
        "pass_nested_transparent_view_infer",
        "auf",
    );
    defer allocator.free(proof);

    const line_formula =
        "l1: $ im (outer a b x y) (body (opair x y) a b) $";
    const start = std.mem.indexOf(u8, proof, line_formula) orelse {
        return error.ExpectedNeedle;
    };
    const rest = proof[start..];
    const line_end = std.mem.indexOfScalar(u8, rest, '\n') orelse rest.len;
    const line = rest[0..line_end];
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        line,
        1,
        "by sep_elim",
    ));
    try std.testing.expect(!std.mem.containsAtLeast(u8, line, 1, ":="));
}

test "euclid ex_elim infers symbolic view witness" {
    const allocator = std.testing.allocator;
    const mm0_src = try readProofCaseFile(allocator, "euclid", "mm0");
    defer allocator.free(mm0_src);
    const proof_src = try readProofCaseFile(allocator, "euclid", "auf");
    defer allocator.free(proof_src);

    const witness_free_application = "by ex_elim [#1, l2]";
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        proof_src,
        1,
        witness_free_application,
    ));
    try std.testing.expect(!std.mem.containsAtLeast(
        u8,
        proof_src,
        1,
        "by ex_elim (x := $ k $) [#1, l2]",
    ));

    var compiler = Compiler.initWithProof(allocator, mm0_src, proof_src);
    const mmb = try compiler.compileMmb(allocator);
    defer allocator.free(mmb);
    try mm0.verifyPair(allocator, mm0_src, mmb);
}

// This proof needs the structural solver to keep symbolic view seeds
// available while @recover derives the rule-side witness.
// A view-bindings-only snapshot loses the hidden hole inside `P x`.
//
// The full integration suite also covers this case, but keeping it here makes
// the symbolic @recover requirement visible next to the binder-inference
// regression test.
test "structural view recover uses symbolic snapshot" {
    const allocator = std.testing.allocator;
    const stem = "pass_view_acui_joint_cover";
    const mm0_src = try readProofCaseFile(allocator, stem, "mm0");
    defer allocator.free(mm0_src);
    const proof_src = try readProofCaseFile(allocator, stem, "auf");
    defer allocator.free(proof_src);

    var compiler = Compiler.initWithProof(allocator, mm0_src, proof_src);
    const mmb = try compiler.compileMmb(allocator);
    defer allocator.free(mmb);
    try mm0.verifyPair(allocator, mm0_src, mmb);
}

test "compiler does not treat hidden applications as proof labels" {
    const mm0_src =
        \\provable sort wff;
        \\term top: wff;
        \\axiom top_i: $ top $;
        \\axiom keep: $ top $ > $ top $;
        \\theorem target: $ top $;
    ;
    const proof_src =
        \\target
        \\------
        \\l1: $ top $ by keep [top_i []]
        \\top_i: $ top $ by top_i []
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

test "compiler cannot reference hidden applications by rule name" {
    const mm0_src =
        \\provable sort wff;
        \\term top: wff;
        \\axiom top_i: $ top $;
        \\axiom keep: $ top $ > $ top $;
        \\theorem target: $ top $;
    ;
    const proof_src =
        \\target
        \\------
        \\l1: $ top $ by keep [top_i []]
        \\l2: $ top $ by keep [top_i]
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    try std.testing.expectError(error.UnknownLabel, compiler.compileMmb(
        std.testing.allocator,
    ));

    const diag = compiler.diagnostics.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.UnknownLabel, diag.err);
    try std.testing.expectEqualStrings("target", diag.theorem_name.?);
    try std.testing.expectEqualStrings("l2", diag.line_label.?);
    try std.testing.expectEqualStrings("top_i", diag.name.?);
}

test "compiler pinpoints unknown nested rule applications" {
    const mm0_src =
        \\provable sort wff;
        \\term top: wff;
        \\axiom keep: $ top $ > $ top $;
        \\theorem target: $ top $;
    ;
    const proof_src =
        \\target
        \\------
        \\l1: $ top $ by keep [missing_rule []]
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    try std.testing.expectError(error.UnknownRule, compiler.compileMmb(
        std.testing.allocator,
    ));

    const diag = compiler.diagnostics.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.UnknownRule, diag.err);
    try std.testing.expectEqualStrings("target", diag.theorem_name.?);
    try std.testing.expectEqualStrings("l1", diag.line_label.?);
    try std.testing.expectEqualStrings("missing_rule", diag.rule_name.?);
    const span = diag.span orelse return error.ExpectedDiagnosticSpan;
    try std.testing.expectEqualStrings(
        "missing_rule",
        proof_src[span.start..span.end],
    );
}

test "compiler pinpoints nested application ref-count mismatches" {
    const mm0_src =
        \\provable sort wff;
        \\term top: wff;
        \\axiom keep: $ top $ > $ top $;
        \\theorem target: $ top $;
    ;
    const proof_src =
        \\target
        \\------
        \\l1: $ top $ by keep [keep []]
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    try std.testing.expectError(error.RefCountMismatch, compiler.compileMmb(
        std.testing.allocator,
    ));

    const diag = compiler.diagnostics.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.RefCountMismatch, diag.err);
    try std.testing.expectEqualStrings("target", diag.theorem_name.?);
    try std.testing.expectEqualStrings("l1", diag.line_label.?);
    try std.testing.expectEqualStrings("keep", diag.rule_name.?);
    const span = diag.span orelse return error.ExpectedDiagnosticSpan;
    try std.testing.expectEqualStrings("[]", proof_src[span.start..span.end]);
}

test "compiler pinpoints missing nested application bindings" {
    const mm0_src =
        \\provable sort wff;
        \\axiom need_b (a b: wff): $ a $;
        \\axiom keep (a: wff): $ a $ > $ a $;
        \\theorem target (a b: wff): $ a $;
    ;
    const proof_src =
        \\target
        \\------
        \\l1: $ a $ by keep [need_b (a := $ a $) []]
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
    try std.testing.expectEqualStrings("target", diag.theorem_name.?);
    try std.testing.expectEqualStrings("l1", diag.line_label.?);
    try std.testing.expectEqualStrings("need_b", diag.rule_name.?);
    try std.testing.expectEqualStrings("b", diag.name.?);
    const span = diag.span orelse return error.ExpectedDiagnosticSpan;
    try std.testing.expectEqualStrings(
        "(a := $ a $)",
        proof_src[span.start..span.end],
    );
}

test "compiler reports child applications rejected by parent hypotheses" {
    const mm0_src =
        \\provable sort wff;
        \\term top: wff;
        \\term bot: wff;
        \\axiom top_i: $ top $;
        \\axiom need_bot: $ bot $ > $ top $;
        \\theorem target: $ top $;
    ;
    const proof_src =
        \\target
        \\------
        \\l1: $ top $ by need_bot [top_i []]
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    try std.testing.expectError(error.HypothesisMismatch, compiler.compileMmb(
        std.testing.allocator,
    ));

    const diag = compiler.diagnostics.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.HypothesisMismatch, diag.err);
    try std.testing.expectEqualStrings("target", diag.theorem_name.?);
    try std.testing.expectEqualStrings("l1", diag.line_label.?);
    try std.testing.expectEqualStrings("need_bot", diag.rule_name.?);
    try std.testing.expectEqualStrings("top_i", diag.name.?);
    const span = diag.span orelse return error.ExpectedDiagnosticSpan;
    try std.testing.expectEqualStrings("top_i []", proof_src[span.start..span.end]);
}

test "compiler pinpoints nested binding validation failures" {
    const mm0_src =
        \\sort obj;
        \\provable sort wff;
        \\term top: wff;
        \\axiom keep: $ top $ > $ top $;
        \\axiom use_obj (x: obj): $ top $;
        \\theorem target: $ top $;
    ;
    const proof_src =
        \\target
        \\------
        \\l1: $ top $ by keep [use_obj (x := $ top $) []]
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    try std.testing.expectError(
        error.SortMismatch,
        compiler.compileMmb(std.testing.allocator),
    );

    const diag = compiler.diagnostics.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.SortMismatch, diag.err);
    try std.testing.expectEqual(.parse_binding, diag.kind);
    try std.testing.expectEqual(
        mm0.CompilerDiagnosticPhase.parse,
        diag.phase.?,
    );
    try std.testing.expectEqualStrings("target", diag.theorem_name.?);
    try std.testing.expectEqualStrings("l1", diag.line_label.?);
    try std.testing.expectEqualStrings("use_obj", diag.rule_name.?);
    try std.testing.expectEqualStrings("x", diag.name.?);
    const span = diag.span orelse return error.ExpectedDiagnosticSpan;
    try std.testing.expectEqualStrings(
        "$ top $",
        proof_src[span.start..span.end],
    );
}
