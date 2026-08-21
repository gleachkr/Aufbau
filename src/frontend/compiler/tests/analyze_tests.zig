const helpers = @import("./helpers.zig");
const std = helpers.std;
const mm0 = helpers.mm0;
const Compiler = helpers.Compiler;
const FrontendExpr = helpers.FrontendExpr;
const Expr = helpers.Expr;
const MM0Parser = helpers.MM0Parser;
const CompilerViews = helpers.CompilerViews;

test "compiler primary diagnostic overflow records omitted summary" {
    var compiler = Compiler.init(std.testing.allocator, "");
    for (0..Compiler.max_primary_diagnostics + 7) |_| {
        compiler.addPrimaryDiagnostic(.{
            .kind = .generic,
            .err = error.UnknownTerm,
            .source = .mm0,
        });
    }

    const diags = compiler.primaryDiagnostics();
    try std.testing.expectEqual(
        Compiler.max_primary_diagnostics,
        diags.len,
    );
    const omitted = compiler.omittedPrimaryDiagnostic(.mm0) orelse {
        return error.ExpectedDiagnostic;
    };
    try std.testing.expectEqual(.omitted_diagnostics, omitted.kind);
    switch (omitted.detail) {
        .omitted_diagnostics => |info| {
            try std.testing.expectEqual(@as(usize, 7), info.count);
        },
        else => return error.ExpectedDiagnosticDetail,
    }
    try std.testing.expect(compiler.omittedPrimaryDiagnostic(.proof) == null);
}

test "compiler analyze mm0 collects multiple statement diagnostics" {
    const mm0_src =
        \\provable sort wff;
        \\term top: wff;
        \\--| @fallback missing
        \\axiom bad: $ top $;
        \\--| @fallback still_missing
        \\axiom still_bad: $ top $;
    ;

    var compiler = Compiler.init(std.testing.allocator, mm0_src);
    try compiler.analyzeMm0();

    const diags = compiler.primaryDiagnostics();
    try std.testing.expectEqual(@as(usize, 2), diags.len);
    try std.testing.expect(compiler.diagnostics.last_diagnostic == null);

    try std.testing.expectEqual(error.UnknownFallbackRule, diags[0].err);
    try std.testing.expectEqualStrings("bad", diags[0].name.?);
    try std.testing.expectEqual(error.UnknownFallbackRule, diags[1].err);
    try std.testing.expectEqualStrings("still_bad", diags[1].name.?);
}

test "compiler analyze mm0 suppresses fallback follow-on diagnostics" {
    const mm0_src =
        \\provable sort wff;
        \\term top: wff;
        \\--| @fallback missing
        \\axiom bad: $ top $;
        \\--| @fallback bad
        \\axiom dependent: $ top $;
    ;

    var compiler = Compiler.init(std.testing.allocator, mm0_src);
    try compiler.analyzeMm0();

    const diags = compiler.primaryDiagnostics();
    try std.testing.expectEqual(@as(usize, 1), diags.len);
    try std.testing.expectEqual(error.UnknownFallbackRule, diags[0].err);
    try std.testing.expectEqualStrings("bad", diags[0].name.?);
}

test "compiler analyze mm0 recovers after malformed statements" {
    const mm0_src =
        \\provable sort wff;
        \\term top: wff;
        \\axiom bad $ top $;
        \\--| @fallback missing
        \\axiom still_bad: $ top $;
    ;

    var compiler = Compiler.init(std.testing.allocator, mm0_src);
    try compiler.analyzeMm0();

    const diags = compiler.primaryDiagnostics();
    try std.testing.expectEqual(@as(usize, 2), diags.len);

    try std.testing.expectEqual(error.UnexpectedChar, diags[0].err);
    try std.testing.expectEqualStrings("bad", diags[0].name.?);
    try std.testing.expectEqual(error.UnknownFallbackRule, diags[1].err);
    try std.testing.expectEqualStrings("still_bad", diags[1].name.?);
}

test "compiler analyze mm0 discards annotations from malformed statements" {
    const mm0_src =
        \\provable sort wff;
        \\term top: wff;
        \\--| @fallback missing
        \\axiom bad $ top $;
        \\axiom good: $ top $;
    ;

    var compiler = Compiler.init(std.testing.allocator, mm0_src);
    try compiler.analyzeMm0();

    const diags = compiler.primaryDiagnostics();
    try std.testing.expectEqual(@as(usize, 1), diags.len);
    try std.testing.expectEqual(error.UnexpectedChar, diags[0].err);
    try std.testing.expectEqualStrings("bad", diags[0].name.?);
}

test "compiler analyze mm0 ignores semicolons in comments" {
    const mm0_src =
        \\provable sort wff;
        \\term top: wff;
        \\axiom bad $ top $
        \\-- comment ; not a boundary
        \\;
        \\--| @fallback missing
        \\axiom still_bad: $ top $;
    ;

    var compiler = Compiler.init(std.testing.allocator, mm0_src);
    try compiler.analyzeMm0();

    const diags = compiler.primaryDiagnostics();
    try std.testing.expectEqual(@as(usize, 2), diags.len);
    try std.testing.expectEqual(error.UnexpectedChar, diags[0].err);
    try std.testing.expectEqualStrings("bad", diags[0].name.?);
    try std.testing.expectEqual(error.UnknownFallbackRule, diags[1].err);
    try std.testing.expectEqualStrings("still_bad", diags[1].name.?);
}

test "compiler analyze with proof collects multiple block diagnostics" {
    const mm0_src =
        \\provable sort wff;
        \\term top: wff;
        \\theorem bad_one: $ top $;
        \\theorem bad_two: $ top $;
    ;
    const proof_src =
        \\bad_one
        \\-------
        \\l1: $ top $ by missing_one []
        \\
        \\bad_two
        \\-------
        \\l1: $ top $ by missing_two []
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    try compiler.analyze();

    const diags = compiler.primaryDiagnostics();
    try std.testing.expectEqual(@as(usize, 2), diags.len);
    try std.testing.expect(compiler.diagnostics.last_diagnostic == null);

    try std.testing.expectEqual(error.UnknownRule, diags[0].err);
    try std.testing.expectEqual(mm0.CompilerDiagnosticSource.proof, diags[0].source);
    try std.testing.expectEqualStrings("bad_one", diags[0].theorem_name.?);
    try std.testing.expectEqual(error.UnknownRule, diags[1].err);
    try std.testing.expectEqual(mm0.CompilerDiagnosticSource.proof, diags[1].source);
    try std.testing.expectEqualStrings("bad_two", diags[1].theorem_name.?);
}

test "compiler analyze with proof recovers after failing lemma blocks" {
    const mm0_src =
        \\provable sort wff;
        \\term top: wff;
        \\theorem target: $ top $;
    ;
    const proof_src =
        \\lemma helper: $ top $
        \\--------------------
        \\l1: $ top $ by missing_helper []
        \\
        \\target
        \\------
        \\l1: $ top $ by missing_target []
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    try compiler.analyze();

    const diags = compiler.primaryDiagnostics();
    try std.testing.expectEqual(@as(usize, 2), diags.len);

    try std.testing.expectEqual(error.UnknownRule, diags[0].err);
    try std.testing.expectEqualStrings("helper", diags[0].theorem_name.?);
    try std.testing.expectEqual(error.UnknownRule, diags[1].err);
    try std.testing.expectEqualStrings("target", diags[1].theorem_name.?);
}

test "compiler analyze with proof recovers after malformed theorem blocks" {
    const mm0_src =
        \\provable sort wff;
        \\term top: wff;
        \\theorem bad_parse: $ top $;
        \\theorem later_bad: $ top $;
    ;
    const proof_src =
        \\bad_parse
        \\---------
        \\l1: $ top $ by [#1]
        \\
        \\later_bad
        \\---------
        \\l1: $ top $ by missing_rule []
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    try compiler.analyze();

    const diags = compiler.primaryDiagnostics();
    try std.testing.expectEqual(@as(usize, 2), diags.len);

    try std.testing.expectEqual(error.ExpectedIdentifier, diags[0].err);
    try std.testing.expectEqualStrings("bad_parse", diags[0].theorem_name.?);
    try std.testing.expectEqual(error.UnknownRule, diags[1].err);
    try std.testing.expectEqualStrings("later_bad", diags[1].theorem_name.?);
}

test "compiler analyze with proof recovers to later lemmas with binders" {
    const mm0_src =
        \\provable sort wff;
        \\term top: wff;
        \\theorem target: $ top $;
    ;
    const proof_src =
        \\target
        \\------
        \\l1: $ top $ by [#1]
        \\
        \\lemma helper (a: wff): $ a $
        \\--------------------------
        \\l1: $ a $ by missing_helper [#1]
        \\
        \\target
        \\------
        \\l1: $ top $ by missing_target []
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    try compiler.analyze();

    // The lenient parse keeps the first `target` block as THE proof of
    // `target` (its broken line reported in place), so the trailing
    // duplicate block is suppressed as a repeat of an already-failed
    // theorem; the lemma in between is still processed.
    const diags = compiler.primaryDiagnostics();
    try std.testing.expectEqual(@as(usize, 2), diags.len);

    try std.testing.expectEqual(error.ExpectedIdentifier, diags[0].err);
    try std.testing.expectEqualStrings("target", diags[0].theorem_name.?);
    try std.testing.expectEqual(error.UnknownRule, diags[1].err);
    try std.testing.expectEqualStrings("helper", diags[1].theorem_name.?);
}

// #156, editor semantics: with placeholders tolerated, a broken proof line
// reports the parse failure the strict parse would have raised (same error,
// pinpointed span) and stops the block there — like a placeholder line — so
// the theorem still enters the environment and its dependents stay quiet.
test "compiler analyze in editor mode contains a broken proof line" {
    const mm0_src =
        \\provable sort wff;
        \\term top: wff;
        \\theorem t: $ top $;
        \\theorem u: $ top $;
    ;
    const proof_src =
        \\t
        \\----
        \\l1: $ top $ by [#1]
        \\
        \\u
        \\----
        \\l1: $ top $ by t []
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    compiler.allow_search_placeholders = true;
    try compiler.analyze();

    const diags = compiler.primaryDiagnostics();
    try std.testing.expectEqual(@as(usize, 1), diags.len);
    try std.testing.expectEqual(error.ExpectedIdentifier, diags[0].err);
    try std.testing.expectEqualStrings("t", diags[0].theorem_name.?);
    try std.testing.expectEqualStrings("l1", diags[0].line_label.?);
    // Pinned to where the line stopped parsing.
    try std.testing.expectEqualStrings(
        "[",
        proof_src[diags[0].span.?.start..diags[0].span.?.end],
    );
}

test "compiler analyze with proof ignores stray proof-line comments" {
    const mm0_src =
        \\provable sort wff;
        \\term top: wff;
        \\theorem bad_parse: $ top $;
        \\theorem later_bad: $ top $;
    ;
    const proof_src =
        \\bad_parse
        \\---------
        \\l1: $ top $ by [#1]
        \\l2 -- stray comment on a broken proof line
        \\
        \\later_bad
        \\---------
        \\l1: $ top $ by missing_rule []
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    try compiler.analyze();

    const diags = compiler.primaryDiagnostics();
    try std.testing.expectEqual(@as(usize, 2), diags.len);

    try std.testing.expectEqual(error.ExpectedIdentifier, diags[0].err);
    try std.testing.expectEqualStrings("bad_parse", diags[0].theorem_name.?);
    try std.testing.expectEqual(error.UnknownRule, diags[1].err);
    try std.testing.expectEqualStrings("later_bad", diags[1].theorem_name.?);
}

test "compiler analyze with proof ignores bare identifier fragments" {
    const mm0_src =
        \\provable sort wff;
        \\term top: wff;
        \\theorem bad_parse: $ top $;
        \\theorem later_bad: $ top $;
    ;
    const proof_src =
        \\bad_parse
        \\---------
        \\l1: $ top $ by [#1]
        \\l2
        \\
        \\later_bad
        \\---------
        \\l1: $ top $ by missing_rule []
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    try compiler.analyze();

    const diags = compiler.primaryDiagnostics();
    try std.testing.expectEqual(@as(usize, 2), diags.len);

    try std.testing.expectEqual(error.ExpectedIdentifier, diags[0].err);
    try std.testing.expectEqualStrings("bad_parse", diags[0].theorem_name.?);
    try std.testing.expectEqual(error.UnknownRule, diags[1].err);
    try std.testing.expectEqualStrings("later_bad", diags[1].theorem_name.?);
}

test "compiler analyze with proof recovers after malformed lemma blocks" {
    const mm0_src =
        \\provable sort wff;
        \\term top: wff;
        \\theorem target: $ top $;
    ;
    const proof_src =
        \\lemma helper: $ top $
        \\--------------------
        \\l1: $ top $ by [#1]
        \\
        \\target
        \\------
        \\l1: $ top $ by missing_target []
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    try compiler.analyze();

    const diags = compiler.primaryDiagnostics();
    try std.testing.expectEqual(@as(usize, 2), diags.len);

    try std.testing.expectEqual(error.ExpectedIdentifier, diags[0].err);
    try std.testing.expectEqualStrings("helper", diags[0].theorem_name.?);
    try std.testing.expectEqual(error.UnknownRule, diags[1].err);
    try std.testing.expectEqualStrings("target", diags[1].theorem_name.?);
}

test "compiler analyze mm0 suppresses blocked sort follow-ons" {
    const mm0_src =
        \\provable sort wff;
        \\--| @vars x
        \\strict sort nat;
        \\term zero: nat;
        \\sort obj;
        \\term id: obj;
    ;

    var compiler = Compiler.init(std.testing.allocator, mm0_src);
    try compiler.analyzeMm0();

    const diags = compiler.primaryDiagnostics();
    try std.testing.expectEqual(@as(usize, 1), diags.len);
    try std.testing.expectEqual(error.VarsStrictSort, diags[0].err);
    try std.testing.expectEqualStrings("nat", diags[0].name.?);
}

test "compiler rejects @vars tokens that conflict with hole syntax" {
    const mm0_src =
        \\--| @vars _wff
        \\--| @hole _wff
        \\provable sort wff;
        \\term top: wff;
    ;

    var compiler = Compiler.init(std.testing.allocator, mm0_src);
    try compiler.analyzeMm0();

    const diags = compiler.primaryDiagnostics();
    try std.testing.expectEqual(@as(usize, 1), diags.len);
    try std.testing.expectEqual(error.HoleTokenNameCollision, diags[0].err);
}

test "compiler rejects theorem binders that conflict with hole syntax" {
    const mm0_src =
        \\--| @hole _wff
        \\provable sort wff;
        \\theorem bad (_wff: wff): $ _wff $;
    ;

    var compiler = Compiler.init(std.testing.allocator, mm0_src);
    try compiler.analyzeMm0();

    const diags = compiler.primaryDiagnostics();
    try std.testing.expectEqual(@as(usize, 1), diags.len);
    try std.testing.expectEqual(error.HoleTokenNameCollision, diags[0].err);
}

test "compiler rejects term names that conflict with hole syntax" {
    const mm0_src =
        \\--| @hole _wff
        \\provable sort wff;
        \\term _wff: wff;
    ;

    var compiler = Compiler.init(std.testing.allocator, mm0_src);
    try compiler.analyzeMm0();

    const diags = compiler.primaryDiagnostics();
    try std.testing.expectEqual(@as(usize, 1), diags.len);
    try std.testing.expectEqual(error.HoleTokenNameCollision, diags[0].err);
}

test "compiler rejects notation tokens that conflict with hole syntax" {
    const mm0_src =
        \\--| @hole _wff
        \\provable sort wff;
        \\term top: wff;
        \\prefix top: $_wff$ prec 10;
    ;

    var compiler = Compiler.init(std.testing.allocator, mm0_src);
    try compiler.analyzeMm0();

    const diags = compiler.primaryDiagnostics();
    try std.testing.expectEqual(@as(usize, 1), diags.len);
    try std.testing.expectEqual(error.HoleTokenNameCollision, diags[0].err);
}

test "compiler rejects bare notation markers with hole syntax" {
    const mm0_src =
        \\--| @hole _wff
        \\provable sort wff;
        \\notation "_wff";
    ;

    var compiler = Compiler.init(std.testing.allocator, mm0_src);
    try compiler.analyzeMm0();

    const diags = compiler.primaryDiagnostics();
    try std.testing.expectEqual(@as(usize, 1), diags.len);
    try std.testing.expectEqual(error.HoleTokenNameCollision, diags[0].err);
}

test "compiler rejects general notation tokens with hole syntax" {
    const mm0_src =
        \\--| @hole _wff
        \\provable sort wff;
        \\term box (a: wff): wff;
        \\notation box (a: wff): wff = ($_wff$:10) a;
    ;

    var compiler = Compiler.init(std.testing.allocator, mm0_src);
    try compiler.analyzeMm0();

    const diags = compiler.primaryDiagnostics();
    try std.testing.expectEqual(@as(usize, 1), diags.len);
    try std.testing.expectEqual(error.HoleTokenNameCollision, diags[0].err);
}

test "compiler rejects sorts that make existing tokens into holes" {
    const mm0_src =
        \\sort base;
        \\term _wff: base;
        \\--| @hole _wff
        \\provable sort wff;
    ;

    var compiler = Compiler.init(std.testing.allocator, mm0_src);
    try compiler.analyzeMm0();

    const diags = compiler.primaryDiagnostics();
    try std.testing.expectEqual(@as(usize, 1), diags.len);
    try std.testing.expectEqual(error.HoleTokenNameCollision, diags[0].err);
}

test "compiler permits underscore sort-like tokens without @hole" {
    const mm0_src =
        \\provable sort wff;
        \\term _wff: wff;
        \\theorem ok: $ _wff $;
    ;

    var compiler = Compiler.init(std.testing.allocator, mm0_src);
    try compiler.check();
}

test "compiler accepts custom proof hole tokens" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\--| @hole HOLE
        \\provable sort wff;
        \\term top: wff;
        \\axiom top_i: $ top $;
        \\theorem ok: $ top $;
    ;
    const proof_src =
        \\ok
        \\---
        \\l1: $ HOLE $ by top_i []
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

test "compiler rejects duplicate hole annotations on one sort" {
    const mm0_src =
        \\--| @hole _wff
        \\--| @hole HOLE
        \\provable sort wff;
    ;

    var compiler = Compiler.init(std.testing.allocator, mm0_src);
    try compiler.analyzeMm0();

    const diags = compiler.primaryDiagnostics();
    try std.testing.expectEqual(@as(usize, 1), diags.len);
    try std.testing.expectEqual(error.DuplicateHoleAnnotation, diags[0].err);
}

test "compiler rejects duplicate hole tokens across sorts" {
    const mm0_src =
        \\--| @hole _hole
        \\provable sort wff;
        \\--| @hole _hole
        \\sort obj;
    ;

    var compiler = Compiler.init(std.testing.allocator, mm0_src);
    try compiler.analyzeMm0();

    const diags = compiler.primaryDiagnostics();
    try std.testing.expectEqual(@as(usize, 1), diags.len);
    try std.testing.expectEqual(error.DuplicateHoleToken, diags[0].err);
}

test "compiler rejects @vars tokens registered after hole tokens" {
    const mm0_src =
        \\--| @hole _wff
        \\provable sort wff;
        \\--| @vars _wff
        \\sort obj;
    ;

    var compiler = Compiler.init(std.testing.allocator, mm0_src);
    try compiler.analyzeMm0();

    const diags = compiler.primaryDiagnostics();
    try std.testing.expectEqual(@as(usize, 1), diags.len);
    try std.testing.expectEqual(error.HoleTokenNameCollision, diags[0].err);
}

test "compiler analyze mm0 suppresses blocked term follow-ons" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\sort nat;
        \\--| @bogus
        \\term bad: nat;
        \\def alias: nat = $ bad $;
        \\term good: nat;
    ;

    var compiler = Compiler.init(std.testing.allocator, mm0_src);
    try compiler.analyzeMm0();

    const diags = compiler.primaryDiagnostics();
    try std.testing.expectEqual(@as(usize, 1), diags.len);
    try std.testing.expectEqual(error.UnknownTermAnnotation, diags[0].err);
    try std.testing.expectEqualStrings("bad", diags[0].name.?);
}

test "compiler analyze with proof suppresses blocked theorem follow-ons" {
    const mm0_src =
        \\provable sort wff;
        \\term top: wff;
        \\theorem bad: $ top $;
        \\theorem blocked: $ top $;
        \\theorem later_bad: $ top $;
    ;
    const proof_src =
        \\bad
        \\---
        \\l1: $ top $ by missing []
        \\
        \\blocked
        \\-------
        \\l1: $ top $ by bad []
        \\
        \\later_bad
        \\---------
        \\l1: $ top $ by missing_again []
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    try compiler.analyze();

    const diags = compiler.primaryDiagnostics();
    try std.testing.expectEqual(@as(usize, 2), diags.len);
    try std.testing.expectEqual(error.UnknownRule, diags[0].err);
    try std.testing.expectEqualStrings("bad", diags[0].theorem_name.?);
    try std.testing.expectEqual(error.UnknownRule, diags[1].err);
    try std.testing.expectEqualStrings("later_bad", diags[1].theorem_name.?);
}

test "compiler analyze with proof suppresses missing blocks after eof parse failure" {
    const mm0_src =
        \\provable sort wff;
        \\term top: wff;
        \\theorem bad_rule: $ top $;
        \\theorem bad_parse: $ top $;
        \\theorem blocked_after_eof: $ top $;
    ;
    // The second block's failure is at the HEADER level (no underline, and
    // EOF right after): line-level breakage no longer aborts the stream
    // under the lenient parse, but an unrecoverable header failure still
    // must suppress the missing-block cascade for the theorems behind it.
    const proof_src =
        \\bad_rule
        \\--------
        \\l1: $ top $ by missing []
        \\
        \\bad_parse
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    try compiler.analyze();

    const diags = compiler.primaryDiagnostics();
    try std.testing.expectEqual(@as(usize, 2), diags.len);
    try std.testing.expectEqual(error.UnknownRule, diags[0].err);
    try std.testing.expectEqualStrings("bad_rule", diags[0].theorem_name.?);
    try std.testing.expectEqual(error.ExpectedBlockUnderline, diags[1].err);
    try std.testing.expectEqualStrings("bad_parse", diags[1].theorem_name.?);
}

test "compiler analyze with proof stops after unrecoverable mm0 parse failure" {
    const mm0_src =
        \\provable sort wff;
        \\term top: wff;
        \\theorem bad: $ top $
    ;
    const proof_src =
        \\bad
        \\---
        \\l1: $ top $ by keep []
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    try compiler.analyze();

    const diags = compiler.primaryDiagnostics();
    try std.testing.expectEqual(@as(usize, 1), diags.len);
    try std.testing.expectEqual(error.UnexpectedChar, diags[0].err);
    try std.testing.expectEqual(
        mm0.CompilerDiagnosticSource.mm0,
        diags[0].source,
    );
}

test "compiler analyze with proof suppresses malformed blocks for blocked theorems" {
    const mm0_src =
        \\provable sort wff;
        \\--| @bogus
        \\term bad: wff;
        \\term good: wff;
        \\theorem blocked: $ bad $;
        \\theorem later: $ good $;
    ;
    const proof_src =
        \\blocked
        \\-------
        \\l1: $ bad $ by [#1]
        \\
        \\later
        \\-----
        \\l1: $ good $ by missing_rule []
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    try compiler.analyze();

    const diags = compiler.primaryDiagnostics();
    try std.testing.expectEqual(@as(usize, 2), diags.len);
    try std.testing.expectEqual(error.UnknownTermAnnotation, diags[0].err);
    try std.testing.expectEqualStrings("bad", diags[0].name.?);
    try std.testing.expectEqual(error.UnknownRule, diags[1].err);
    try std.testing.expectEqual(
        mm0.CompilerDiagnosticSource.proof,
        diags[1].source,
    );
    try std.testing.expectEqualStrings("later", diags[1].theorem_name.?);
}

test "compiler analyze with proof ignores malformed blocks for blocked trailing theorems" {
    const mm0_src =
        \\provable sort wff;
        \\--| @bogus
        \\term bad: wff;
        \\theorem blocked: $ bad $;
    ;
    const proof_src =
        \\blocked
        \\-------
        \\l1: $ bad $ by [#1]
    ;

    var compiler = Compiler.initWithProof(
        std.testing.allocator,
        mm0_src,
        proof_src,
    );
    try compiler.analyze();

    const diags = compiler.primaryDiagnostics();
    try std.testing.expectEqual(@as(usize, 1), diags.len);
    try std.testing.expectEqual(error.UnknownTermAnnotation, diags[0].err);
    try std.testing.expectEqual(
        mm0.CompilerDiagnosticSource.mm0,
        diags[0].source,
    );
    try std.testing.expectEqualStrings("bad", diags[0].name.?);
}

test "runtime locale switch renders the German catalogue" {
    mm0.setCompilerLang(.de);
    defer mm0.setCompilerLang(.en);

    try std.testing.expectEqualStrings(
        "dem Compiler ist der Speicher ausgegangen",
        mm0.compilerErrorSummary(error.OutOfMemory),
    );

    var buf = std.ArrayListUnmanaged(u8){};
    defer buf.deinit(std.testing.allocator);
    var writer = buf.writer(std.testing.allocator);
    try mm0.renderCompilerNoteMessage(&writer, .{
        .assignment_parses_as_sort = .{
            .actual_sort = "wff",
            .expected_sort = "nat",
        },
    });
    try std.testing.expectEqualStrings(
        "die Zuweisung parst, aber mit Sorte 'wff'; " ++
            "dieser Binder erwartet Sorte 'nat'",
        buf.items,
    );
}

test "locale names parse and unknown names are rejected" {
    try std.testing.expectEqual(mm0.CompilerLang.en, mm0.parseCompilerLang("en").?);
    try std.testing.expectEqual(mm0.CompilerLang.de, mm0.parseCompilerLang("de").?);
    try std.testing.expectEqual(@as(?mm0.CompilerLang, null), mm0.parseCompilerLang("xx"));
}

// The residual-completion fixtures cannot observe the subtraction semantics
// end-to-end (the structural tier rescues a failed view match), so the
// operation is locked here directly.
test "subtractMembers: multiset order, duplicates, set semantics, strictness" {
    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    const allocator = arena_state.allocator();

    const mm0_src =
        "provable sort wff; term PA: wff; term PB: wff; term PC: wff;";
    var parser = MM0Parser.init(mm0_src, allocator);
    var theorem = FrontendExpr.TheoremContext.init(allocator);
    defer theorem.deinit();
    var theorem_vars = std.StringHashMap(*const Expr).init(allocator);
    defer theorem_vars.deinit();
    while (try parser.next()) |_| {}

    const pa = try theorem.internParsedExpr(
        try parser.parseFormulaText(" PA ", &theorem_vars),
    );
    const pb = try theorem.internParsedExpr(
        try parser.parseFormulaText(" PB ", &theorem_vars),
    );
    const pc = try theorem.internParsedExpr(
        try parser.parseFormulaText(" PC ", &theorem_vars),
    );
    const Subtract = CompilerViews.subtractMembers;

    // Multiset subtraction preserves the order of the remaining items —
    // an order-scrambling removal breaks noncommutative (AU) combiners.
    {
        var residual = (try Subtract(
            allocator,
            &theorem,
            &.{ pa, pb, pc },
            &.{pa},
            false,
            true,
        )).?;
        defer residual.deinit(allocator);
        try std.testing.expectEqualSlices(
            FrontendExpr.ExprId,
            &.{ pb, pc },
            residual.items,
        );
    }
    // Duplicates around the removal boundary: exactly one (the first)
    // occurrence is removed and the rest keep their positions.
    {
        var residual = (try Subtract(
            allocator,
            &theorem,
            &.{ pa, pb, pa, pc },
            &.{pa},
            false,
            true,
        )).?;
        defer residual.deinit(allocator);
        try std.testing.expectEqualSlices(
            FrontendExpr.ExprId,
            &.{ pb, pa, pc },
            residual.items,
        );
    }
    // Multiset counting: one occurrence per covered occurrence, so a
    // duplicated goal member survives a single subtraction (set-diff would
    // wrongly drop both).
    {
        var residual = (try Subtract(
            allocator,
            &theorem,
            &.{ pa, pa, pb },
            &.{pa},
            false,
            true,
        )).?;
        defer residual.deinit(allocator);
        try std.testing.expectEqualSlices(
            FrontendExpr.ExprId,
            &.{ pa, pb },
            residual.items,
        );
    }
    // Set semantics (idempotent combiners): a covered member absorbs every
    // equal occurrence.
    {
        var residual = (try Subtract(
            allocator,
            &theorem,
            &.{ pa, pb, pa },
            &.{pa},
            true,
            true,
        )).?;
        defer residual.deinit(allocator);
        try std.testing.expectEqualSlices(
            FrontendExpr.ExprId,
            &.{pb},
            residual.items,
        );
    }
    // Strict subtraction: a covered member with no occurrence means no
    // residual exists, in both semantics.
    try std.testing.expectEqual(
        @as(?std.ArrayListUnmanaged(FrontendExpr.ExprId), null),
        try Subtract(allocator, &theorem, &.{pa}, &.{pb}, false, true),
    );
    try std.testing.expectEqual(
        @as(?std.ArrayListUnmanaged(FrontendExpr.ExprId), null),
        try Subtract(allocator, &theorem, &.{pa}, &.{pb}, true, true),
    );
    // Non-strict subtraction skips missing covered members.
    {
        var residual = (try Subtract(
            allocator,
            &theorem,
            &.{pa},
            &.{pb},
            false,
            false,
        )).?;
        defer residual.deinit(allocator);
        try std.testing.expectEqualSlices(
            FrontendExpr.ExprId,
            &.{pa},
            residual.items,
        );
    }
}
