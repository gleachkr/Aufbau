const helpers = @import("./helpers.zig");
const std = helpers.std;
const Compiler = helpers.Compiler;

const mm0_src =
    \\--| @hole _wff
    \\provable sort wff;
    \\term imp (a b: wff): wff; infixr imp: $->$ prec 25;
    \\axiom mp (a b: wff): $ a -> b $ > $ a $ > $ b $;
    \\theorem t (p q: wff): $ p $ > $ q -> p $;
;

fn analyzed(proof_src: []const u8, editor: bool) !Compiler {
    var compiler = Compiler.initWithProof(std.testing.allocator, mm0_src, proof_src);
    compiler.allow_search_placeholders = editor;
    try compiler.analyze();
    return compiler;
}

fn expectOpenGoal(
    diag: helpers.mm0.CompilerDiagnostic,
    proof_src: []const u8,
    goal: ?[]const u8,
) !void {
    try std.testing.expectEqual(error.OpenGoal, diag.err);
    try std.testing.expectEqualStrings("?", proof_src[diag.span.?.start..diag.span.?.end]);
    const detail = diag.detail.open_goal;
    if (goal) |text| {
        try std.testing.expectEqualStrings(text, detail.goal.?);
    } else {
        try std.testing.expect(detail.goal == null);
    }
}

test "an open goal line is admitted and its goal reported" {
    // The editor sees a warning naming the goal, and the line after it,
    // which cites the open line, checks against its statement.
    const proof_src =
        \\t
        \\---
        \\l1: $ p -> q -> p $ by ?
        \\l2: $ q -> p $ by mp [l1, #1]
    ;
    var compiler = try analyzed(proof_src, true);
    try std.testing.expectEqual(@as(usize, 0), compiler.primaryDiagnostics().len);
    const warnings = compiler.warningDiagnostics();
    try std.testing.expectEqual(@as(usize, 1), warnings.len);
    try expectOpenGoal(warnings[0], proof_src, "p -> q -> p");
}

test "an inline open goal reports the goal its siblings fix" {
    // `#1` on the right fixes `mp`'s antecedent before it is elaborated.
    const proof_src =
        \\t
        \\---
        \\l1: $ q -> p $ by mp [?, #1]
    ;
    var compiler = try analyzed(proof_src, true);
    try std.testing.expectEqual(@as(usize, 0), compiler.primaryDiagnostics().len);
    const warnings = compiler.warningDiagnostics();
    try std.testing.expectEqual(@as(usize, 1), warnings.len);
    try expectOpenGoal(warnings[0], proof_src, "p -> q -> p");
}

test "an inline open goal its line does not fully determine is unfinished, not failed" {
    // Nothing fixes `mp`'s antecedent: the first premise's goal is known
    // only up to it, and the line stops there, standing as written.
    const proof_src =
        \\t
        \\---
        \\l1: $ q -> p $ by mp [?, ?]
    ;
    var compiler = try analyzed(proof_src, true);
    try std.testing.expectEqual(@as(usize, 0), compiler.primaryDiagnostics().len);
    const warnings = compiler.warningDiagnostics();
    try std.testing.expectEqual(@as(usize, 2), warnings.len);
    try expectOpenGoal(warnings[0], proof_src, "_wff -> q -> p");
    try std.testing.expectEqual(
        std.mem.indexOf(u8, proof_src, "[?").? + 1,
        warnings[0].span.?.start,
    );
    // The second is never reached, but still counts as an open goal.
    try expectOpenGoal(warnings[1], proof_src, null);
}

test "a holey open goal line leaves the line unfinished" {
    const proof_src =
        \\t
        \\---
        \\l1: $ _wff -> q -> p $ by ?
        \\l2: $ q -> p $ by mp [l1, #1]
    ;
    var compiler = try analyzed(proof_src, true);
    try std.testing.expectEqual(@as(usize, 0), compiler.primaryDiagnostics().len);
    const warnings = compiler.warningDiagnostics();
    try std.testing.expectEqual(@as(usize, 2), warnings.len);
    try expectOpenGoal(warnings[0], proof_src, "_wff -> q -> p");
    try std.testing.expectEqual(error.CitesUnfinishedLine, warnings[1].err);
}

test "an open goal takes no bindings" {
    const proof_src =
        \\t
        \\---
        \\l1: $ q -> p $ by ? (a := $ p $)
    ;
    var compiler = try analyzed(proof_src, true);
    const diags = compiler.primaryDiagnostics();
    try std.testing.expectEqual(@as(usize, 1), diags.len);
    try std.testing.expectEqual(error.OpenGoalBindings, diags[0].err);
}

test "an open goal line may name the facts it uses" {
    // Some rule, not chosen yet, from `#1` and a step still to be proved.
    const proof_src =
        \\t
        \\---
        \\l1: $ q -> p $ by ? [#1, ?]
    ;
    var compiler = try analyzed(proof_src, true);
    try std.testing.expectEqual(@as(usize, 0), compiler.primaryDiagnostics().len);
    const warnings = compiler.warningDiagnostics();
    try std.testing.expectEqual(@as(usize, 2), warnings.len);
    try expectOpenGoal(warnings[0], proof_src, "q -> p");
    try expectOpenGoal(warnings[1], proof_src, null);
}

test "an open goal line's references are checked" {
    const proof_src =
        \\t
        \\---
        \\l1: $ q -> p $ by ? [l9]
    ;
    var compiler = try analyzed(proof_src, true);
    const diags = compiler.primaryDiagnostics();
    try std.testing.expectEqual(@as(usize, 1), diags.len);
    try std.testing.expectEqual(error.UnknownLabel, diags[0].err);
}

test "the analysis behind a failed compile reports every open goal as an error" {
    const proof_src =
        \\t
        \\---
        \\l1: $ p -> q -> p $ by ?
        \\l2: $ q -> p $ by mp [?, #1]
    ;
    var compile = Compiler.initWithProof(std.testing.allocator, mm0_src, proof_src);
    try std.testing.expectError(error.OpenGoal, compile.compileMmb(std.testing.allocator));

    var analysis = compile.failureAnalysis();
    try std.testing.expect(analysis.analyzeCompileFailure(&compile));
    const diags = analysis.primaryDiagnostics();
    try std.testing.expectEqual(@as(usize, 2), diags.len);
    try expectOpenGoal(diags[0], proof_src, "p -> q -> p");
    try expectOpenGoal(diags[1], proof_src, "p -> q -> p");
    try std.testing.expectEqual(@as(usize, 0), analysis.warningDiagnostics().len);
}

test "an open goal in a rule application that falls back is reported once" {
    // `bad` fails on its second premise after its first, the open goal,
    // was admitted; `good` then checks the line. Only the attempt that
    // stands reports the open goal.
    const fallback_mm0 =
        \\provable sort wff;
        \\term top: wff;
        \\term bot: wff;
        \\axiom top_i: $ top $;
        \\axiom good: $ top $ > $ top $ > $ top $;
        \\--| @fallback good
        \\axiom bad: $ top $ > $ bot $ > $ top $;
        \\theorem t: $ top $;
    ;
    const proof_src =
        \\t
        \\---
        \\l1: $ top $ by bad [?, top_i []]
    ;
    var compiler = Compiler.initWithProof(std.testing.allocator, fallback_mm0, proof_src);
    compiler.allow_search_placeholders = true;
    try compiler.analyze();
    try std.testing.expectEqual(@as(usize, 0), compiler.primaryDiagnostics().len);
    const warnings = compiler.warningDiagnostics();
    try std.testing.expectEqual(@as(usize, 1), warnings.len);
    try expectOpenGoal(warnings[0], proof_src, "top");
}

const named_mm0_src =
    \\delimiter $ ( ) $;
    \\--| @unknown ?
    \\--| @hole _wff
    \\provable sort wff;
    \\term imp (a b: wff): wff; infixr imp: $->$ prec 25;
    \\axiom mp (a b: wff): $ a $ > $ a -> b $ > $ b $;
    \\theorem t (p q: wff): $ q $;
;

fn namedGoals(proof_src: []const u8, goals: []const []const u8) !void {
    var compiler = Compiler.initWithProof(std.testing.allocator, named_mm0_src, proof_src);
    compiler.allow_search_placeholders = true;
    try compiler.analyze();
    try std.testing.expectEqual(@as(usize, 0), compiler.primaryDiagnostics().len);
    var seen: usize = 0;
    for (compiler.warningDiagnostics()) |warning| {
        if (warning.err != error.OpenGoal) continue;
        try std.testing.expect(seen < goals.len);
        try expectOpenGoal(warning, proof_src, goals[seen]);
        seen += 1;
    }
    try std.testing.expectEqual(goals.len, seen);
}

test "an open goal line shows the value a later line fixes for its name" {
    try namedGoals(
        \\t
        \\---
        \\l1: $ ?c $ by ?
        \\l2: $ (p -> p) -> q $ by ?
        \\l3: $ q $ by mp [l1, l2]
    , &.{ "p -> p", "(p -> p) -> q" });
}

test "an open goal line shows a partly fixed name with its open names" {
    try namedGoals(
        \\t
        \\---
        \\l1: $ ?c $ by ?
        \\l2: $ (?d -> _wff) -> q $ by ?
        \\l3: $ q $ by mp [l1, l2]
    , &.{ "?d -> _wff", "(?d -> _wff) -> q" });
}

test "an open goal line keeps its statement when nothing fixes its names" {
    try namedGoals(
        \\t
        \\---
        \\l1: $ ?c -> p $ by ?
    , &.{"?c -> p"});
}

fn expectUnknownValue(
    item: anytype,
    name: []const u8,
    value: []const u8,
    partial: bool,
) !void {
    try std.testing.expectEqualStrings("t", item.theorem);
    try std.testing.expectEqualStrings(name, item.name);
    try std.testing.expectEqualStrings(value, item.value);
    try std.testing.expectEqual(partial, item.partial);
}

test "the value sink holds each name's value, by name, past a failed line" {
    const proof_src =
        \\t
        \\---
        \\l0: $ p $ by nothing []
        \\l1: $ ?e -> ?c $ by ?
        \\l2: $ ?c $ by ?
        \\l3: $ (p -> p) -> q $ by ?
        \\l4: $ q $ by mp [l2, l3]
    ;
    var sink = helpers.mm0.UnknownValueSink.init(std.testing.allocator);
    defer sink.deinit();
    // Twice through the same sink: each run starts it afresh.
    for (0..2) |_| {
        var compiler = Compiler.initWithProof(std.testing.allocator, named_mm0_src, proof_src);
        compiler.allow_search_placeholders = true;
        compiler.unknown_value_sink = &sink;
        try compiler.analyze();
        try std.testing.expect(compiler.primaryDiagnostics().len > 0);
    }
    // `?e` is fixed by nothing, so it is left out.
    try std.testing.expectEqual(@as(usize, 1), sink.items.items.len);
    try expectUnknownValue(sink.items.items[0], "?c", "p -> p", false);
}

test "the value sink holds a forced shape with its open names" {
    const proof_src =
        \\t
        \\---
        \\l1: $ ?c $ by ?
        \\l2: $ (?d -> _wff) -> q $ by ?
        \\l3: $ q $ by mp [l1, l2]
    ;
    var sink = helpers.mm0.UnknownValueSink.init(std.testing.allocator);
    defer sink.deinit();
    var compiler = Compiler.initWithProof(std.testing.allocator, named_mm0_src, proof_src);
    compiler.allow_search_placeholders = true;
    compiler.unknown_value_sink = &sink;
    try compiler.analyze();
    try std.testing.expectEqual(@as(usize, 1), sink.items.items.len);
    try expectUnknownValue(sink.items.items[0], "?c", "?d -> _wff", true);
}
