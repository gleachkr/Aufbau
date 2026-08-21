const helpers = @import("./helpers.zig");
const std = helpers.std;
const mm0 = helpers.mm0;
const Compiler = helpers.Compiler;

test "compiler pinpoints unknown terms in notation statements" {
    const mm0_src =
        \\sort nat;
        \\prefix succ: $S$ prec 10;
    ;

    var compiler = Compiler.init(std.testing.allocator, mm0_src);
    try std.testing.expectError(error.UnknownTerm, compiler.check());

    const diag = compiler.diagnostics.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.UnknownTerm, diag.err);
    try std.testing.expectEqual(mm0.CompilerDiagnosticSource.mm0, diag.source);
    try std.testing.expectEqualStrings("succ", diag.name.?);
    try std.testing.expectEqualStrings(
        "unknown term",
        mm0.compilerDiagnosticSummary(diag),
    );
    const span = diag.span orelse return error.ExpectedDiagnosticSpan;
    try std.testing.expectEqualStrings("succ", mm0_src[span.start..span.end]);
}

test "compiler rejects anonymous notation binders" {
    const mm0_src =
        \\sort obj;
        \\provable sort wff;
        \\term sb_f {x: obj} (t: obj x) (p: wff x): wff;
        \\notation sb_f {_: obj} (t: obj x) (p: wff x): wff =
        \\  ($L$:10) x ($/$:0) t ($R$:0) p;
    ;

    var compiler = Compiler.init(std.testing.allocator, mm0_src);
    try std.testing.expectError(
        error.AnonymousNotationBinder,
        compiler.check(),
    );

    const diag = compiler.diagnostics.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.AnonymousNotationBinder, diag.err);
    try std.testing.expectEqual(mm0.CompilerDiagnosticSource.mm0, diag.source);
    try std.testing.expectEqualStrings("sb_f", diag.name.?);
    try std.testing.expectEqualStrings(
        "anonymous binders are not permitted in notation declarations",
        mm0.compilerDiagnosticSummary(diag),
    );
    const span = diag.span orelse return error.ExpectedDiagnosticSpan;
    try std.testing.expectEqualStrings("_", mm0_src[span.start..span.end]);
}

test "compiler rejects dummy notation binders" {
    const mm0_src =
        \\sort obj;
        \\provable sort wff;
        \\term sb_f {x: obj} (t: obj x) (p: wff x): wff;
        \\notation sb_f {.x: obj} (t: obj x) (p: wff x): wff =
        \\  ($L$:10) x ($/$:0) t ($R$:0) p;
    ;

    var compiler = Compiler.init(std.testing.allocator, mm0_src);
    try std.testing.expectError(
        error.DummyNotationBinder,
        compiler.check(),
    );

    const diag = compiler.diagnostics.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.DummyNotationBinder, diag.err);
    try std.testing.expectEqual(mm0.CompilerDiagnosticSource.mm0, diag.source);
    try std.testing.expectEqualStrings("sb_f", diag.name.?);
    try std.testing.expectEqualStrings(
        "dummy binders are not permitted in notation declarations",
        mm0.compilerDiagnosticSummary(diag),
    );
    const span = diag.span orelse return error.ExpectedDiagnosticSpan;
    try std.testing.expectEqualStrings(".x", mm0_src[span.start..span.end]);
}

test "compiler rejects notation declarations that omit arguments" {
    const mm0_src =
        \\sort obj;
        \\provable sort wff;
        \\term sb_f {x: obj} (t: obj x) (p: wff x): wff;
        \\notation sb_f {x: obj} (t: obj x) (p: wff x): wff =
        \\  ($L$:10) x ($/$:0) t ($R$:0);
    ;

    var compiler = Compiler.init(std.testing.allocator, mm0_src);
    try std.testing.expectError(
        error.InvalidNotationVariables,
        compiler.check(),
    );

    const diag = compiler.diagnostics.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.InvalidNotationVariables, diag.err);
    try std.testing.expectEqual(mm0.CompilerDiagnosticSource.mm0, diag.source);
    try std.testing.expectEqualStrings("sb_f", diag.name.?);
    try std.testing.expectEqualStrings(
        "notation must mention each declared argument exactly once",
        mm0.compilerDiagnosticSummary(diag),
    );
}

test "compiler rejects unexpected top-level mm0 keywords" {
    const mm0_src =
        \\trict sort obj;
    ;

    var compiler = Compiler.init(std.testing.allocator, mm0_src);
    try std.testing.expectError(error.UnexpectedKeyword, compiler.check());

    const diag = compiler.diagnostics.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.UnexpectedKeyword, diag.err);
    try std.testing.expectEqual(mm0.CompilerDiagnosticSource.mm0, diag.source);
    try std.testing.expectEqualStrings(
        "unexpected keyword",
        mm0.compilerDiagnosticSummary(diag),
    );
    const span = diag.span orelse return error.ExpectedDiagnosticSpan;
    try std.testing.expectEqualStrings("trict", mm0_src[span.start..span.end]);
}

test "compiler still ignores unsupported input and output statements" {
    const mm0_src =
        \\sort nat;
        \\term zero: nat;
        \\output string: $ zero $;
        \\input string: zero;
    ;

    var compiler = Compiler.init(std.testing.allocator, mm0_src);
    try compiler.check();
}

test "compiler pinpoints unknown sorts in mm0 declarations" {
    const mm0_src =
        \\term zero: nat;
    ;

    var compiler = Compiler.init(std.testing.allocator, mm0_src);
    try std.testing.expectError(error.UnknownSort, compiler.check());

    const diag = compiler.diagnostics.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.UnknownSort, diag.err);
    try std.testing.expectEqual(mm0.CompilerDiagnosticSource.mm0, diag.source);
    try std.testing.expectEqualStrings("zero", diag.name.?);
    try std.testing.expectEqualStrings(
        "unknown sort",
        mm0.compilerDiagnosticSummary(diag),
    );
    const span = diag.span orelse return error.ExpectedDiagnosticSpan;
    try std.testing.expectEqualStrings("nat", mm0_src[span.start..span.end]);
}

test "compiler pinpoints unknown math tokens in mm0 declarations" {
    const mm0_src =
        \\provable sort wff;
        \\theorem bad: $ bogus $;
    ;

    var compiler = Compiler.init(std.testing.allocator, mm0_src);
    try std.testing.expectError(error.UnknownMathToken, compiler.check());

    const diag = compiler.diagnostics.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.UnknownMathToken, diag.err);
    try std.testing.expectEqual(mm0.CompilerDiagnosticSource.mm0, diag.source);
    try std.testing.expectEqualStrings("bad", diag.name.?);
    try std.testing.expectEqualStrings(
        "unknown token in math string",
        mm0.compilerDiagnosticSummary(diag),
    );
    const span = diag.span orelse return error.ExpectedDiagnosticSpan;
    try std.testing.expectEqualStrings("bogus", mm0_src[span.start..span.end]);
    switch (diag.detail) {
        .unknown_math_token => |detail| {
            try std.testing.expectEqualStrings("bogus", detail.token);
        },
        else => return error.ExpectedUnknownMathTokenDetail,
    }
}

test "compiler pinpoints trailing math tokens in mm0 declarations" {
    const mm0_src =
        \\provable sort wff;
        \\term top: wff;
        \\theorem bad: $ top top $;
    ;

    var compiler = Compiler.init(std.testing.allocator, mm0_src);
    try std.testing.expectError(error.TrailingMathTokens, compiler.check());

    const diag = compiler.diagnostics.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.TrailingMathTokens, diag.err);
    try std.testing.expectEqual(mm0.CompilerDiagnosticSource.mm0, diag.source);
    try std.testing.expectEqualStrings("bad", diag.name.?);
    try std.testing.expectEqualStrings(
        "unexpected trailing tokens in math string",
        mm0.compilerDiagnosticSummary(diag),
    );
    const span = diag.span orelse return error.ExpectedDiagnosticSpan;
    try std.testing.expectEqualStrings("top", mm0_src[span.start..span.end]);
}

test "compiler pinpoints mismatched closing parens in mm0 math" {
    const mm0_src =
        \\provable sort wff;
        \\term top: wff;
        \\theorem bad: $ ( top bogus $;
    ;

    var compiler = Compiler.init(std.testing.allocator, mm0_src);
    try std.testing.expectError(error.ExpectedCloseParen, compiler.check());

    const diag = compiler.diagnostics.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.ExpectedCloseParen, diag.err);
    try std.testing.expectEqual(mm0.CompilerDiagnosticSource.mm0, diag.source);
    try std.testing.expectEqualStrings("bad", diag.name.?);
    try std.testing.expectEqualStrings(
        "expected closing parenthesis in math string",
        mm0.compilerDiagnosticSummary(diag),
    );
    const span = diag.span orelse return error.ExpectedDiagnosticSpan;
    try std.testing.expectEqualStrings("bogus", mm0_src[span.start..span.end]);
}

test "compiler pinpoints notation mismatches in mm0 math" {
    const mm0_src =
        \\provable sort wff;
        \\term top: wff;
        \\term box (a: wff): wff;
        \\notation box (a: wff): wff = ($L$:10) a ($R$:10);
        \\theorem bad: $ L top X $;
    ;

    var compiler = Compiler.init(std.testing.allocator, mm0_src);
    try std.testing.expectError(error.NotationMismatch, compiler.check());

    const diag = compiler.diagnostics.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.NotationMismatch, diag.err);
    try std.testing.expectEqual(mm0.CompilerDiagnosticSource.mm0, diag.source);
    try std.testing.expectEqualStrings("bad", diag.name.?);
    try std.testing.expectEqualStrings(
        "token sequence does not match declared notation",
        mm0.compilerDiagnosticSummary(diag),
    );
    const span = diag.span orelse return error.ExpectedDiagnosticSpan;
    try std.testing.expectEqualStrings("X", mm0_src[span.start..span.end]);
}

test "compiler pinpoints missing math tokens in mm0 math" {
    const mm0_src =
        \\provable sort wff;
        \\term box (a: wff): wff;
        \\notation box (a: wff): wff = ($L$:10) a ($R$:10);
        \\theorem bad: $ L $;
    ;

    var compiler = Compiler.init(std.testing.allocator, mm0_src);
    try std.testing.expectError(error.ExpectedMathToken, compiler.check());

    const diag = compiler.diagnostics.last_diagnostic orelse return error.ExpectedDiagnostic;
    try std.testing.expectEqual(error.ExpectedMathToken, diag.err);
    try std.testing.expectEqual(mm0.CompilerDiagnosticSource.mm0, diag.source);
    try std.testing.expectEqualStrings("bad", diag.name.?);
    try std.testing.expectEqualStrings(
        "expected token in math string",
        mm0.compilerDiagnosticSummary(diag),
    );
    const span = diag.span orelse return error.ExpectedDiagnosticSpan;
    const dollar = std.mem.lastIndexOf(u8, mm0_src, "$") orelse {
        return error.MissingMathDelimiter;
    };
    try std.testing.expectEqual(dollar, span.start);
    try std.testing.expectEqual(dollar, span.end);
}
