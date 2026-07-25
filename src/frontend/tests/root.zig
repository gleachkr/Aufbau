const std = @import("std");
const mm0 = @import("mm0");

const FrontendEnv = mm0.Frontend.Env;
const FrontendExpr = mm0.Frontend.Expr;
const Expr = mm0.Expr;
const MathSpan = mm0.MathSpan;
const MM0Parser = mm0.MM0Parser;
const ProofScript = mm0.ProofScript;

test "proof script parser reads theorem blocks and proof lines" {
    const src =
        \\id
        \\---
        \\l1: $ a -> a $ by ax_1 (a := $ a $, b := $ a $) []
        \\l2: $ a $ by ax_mp (a := $ a $, b := $ a $) [#1, l1]
        \\
        \\other
        \\-----
        \\l1: $ b $ by ax_b []
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = ProofScript.Parser.init(arena.allocator(), src);
    const first = (try parser.nextBlock()).?;
    try std.testing.expect(first.kind == .theorem);
    try std.testing.expectEqualStrings("id", first.name);
    try std.testing.expect(first.underline_span != null);
    try std.testing.expectEqual(@as(usize, 2), first.lines.len);
    try std.testing.expectEqualStrings("l1", first.lines[0].label);
    try std.testing.expectEqualStrings(" a -> a ", first.lines[0].assertion.text);
    try std.testing.expectEqualStrings("ax_mp", first.lines[1].application.rule_name);
    try std.testing.expectEqual(@as(usize, 2), first.lines[1].application.arg_bindings.len);
    try std.testing.expectEqualStrings(
        "a",
        first.lines[1].application.arg_bindings[0].name,
    );
    try std.testing.expectEqual(@as(usize, 2), first.lines[1].application.refs.len);
    switch (first.lines[1].application.refs[0]) {
        .hyp => |hyp| try std.testing.expectEqual(@as(usize, 1), hyp.index),
        else => return error.UnexpectedRefKind,
    }
    switch (first.lines[1].application.refs[1]) {
        .line => |line| try std.testing.expectEqualStrings("l1", line.label),
        else => return error.UnexpectedRefKind,
    }

    const second = (try parser.nextBlock()).?;
    try std.testing.expect(second.kind == .theorem);
    try std.testing.expectEqualStrings("other", second.name);
    try std.testing.expect(second.underline_span != null);
    try std.testing.expectEqual(@as(usize, 1), second.lines.len);
    try std.testing.expectEqual(
        @as(usize, 0),
        second.lines[0].application.arg_bindings.len,
    );
    try std.testing.expect((try parser.nextBlock()) == null);
}

test "proof script parser reads nested rule applications" {
    const src =
        \\demo
        \\----
        \\l1: $ c $ by rule1 [rule2 (a := $ t $) [#1, prev], #2]
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = ProofScript.Parser.init(arena.allocator(), src);
    const block = (try parser.nextBlock()).?;
    try std.testing.expectEqual(@as(usize, 1), block.lines.len);
    const line = block.lines[0];
    try std.testing.expectEqualStrings("rule1", line.application.rule_name);
    try std.testing.expectEqual(@as(usize, 2), line.application.refs.len);
    switch (line.application.refs[0]) {
        .application => |child| {
            try std.testing.expectEqualStrings("rule2", child.rule_name);
            try std.testing.expectEqual(@as(usize, 1), child.arg_bindings.len);
            try std.testing.expectEqualStrings("a", child.arg_bindings[0].name);
            try std.testing.expectEqual(@as(usize, 2), child.refs.len);
            switch (child.refs[0]) {
                .hyp => |hyp| {
                    try std.testing.expectEqual(@as(usize, 1), hyp.index);
                },
                else => return error.UnexpectedRefKind,
            }
            switch (child.refs[1]) {
                .line => |ref_line| {
                    try std.testing.expectEqualStrings("prev", ref_line.label);
                },
                else => return error.UnexpectedRefKind,
            }
        },
        else => return error.UnexpectedRefKind,
    }
    switch (line.application.refs[1]) {
        .hyp => |hyp| try std.testing.expectEqual(@as(usize, 2), hyp.index),
        else => return error.UnexpectedRefKind,
    }
}

test "proof script parser keeps bare identifiers as line refs" {
    const src =
        \\demo
        \\----
        \\l1: $ c $ by rule1 [rule2]
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = ProofScript.Parser.init(arena.allocator(), src);
    const block = (try parser.nextBlock()).?;
    const line = block.lines[0];
    try std.testing.expectEqual(@as(usize, 1), line.application.refs.len);
    switch (line.application.refs[0]) {
        .line => |ref_line| {
            try std.testing.expectEqualStrings("rule2", ref_line.label);
        },
        else => return error.UnexpectedRefKind,
    }
}

test "proof script parser reads search parameters on placeholders" {
    const src =
        \\demo
        \\----
        \\l1: $ c $ by auto? (depth: 8, fuel: 8192)
        \\l2: $ c $ by rule1 [auto? (t := $ k $, nodes: 400)]
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = ProofScript.Parser.init(arena.allocator(), src);
    const block = (try parser.nextBlock()).?;
    try std.testing.expectEqual(@as(usize, 2), block.lines.len);

    const top = block.lines[0].application;
    try std.testing.expectEqualStrings("auto?", top.rule_name);
    try std.testing.expectEqual(@as(usize, 0), top.arg_bindings.len);
    try std.testing.expectEqual(@as(usize, 2), top.search_params.len);
    try std.testing.expectEqualStrings("depth", top.search_params[0].name);
    try std.testing.expectEqual(@as(u64, 8), top.search_params[0].value);
    try std.testing.expectEqualStrings("fuel", top.search_params[1].name);
    try std.testing.expectEqual(@as(u64, 8192), top.search_params[1].value);
    const fuel_value = top.search_params[1].value_span;
    try std.testing.expectEqualStrings(
        "8192",
        src[fuel_value.start..fuel_value.end],
    );

    // Nested placeholder: params coexist with an explicit `:=` binding.
    const nested = switch (block.lines[1].application.refs[0]) {
        .application => |child| child,
        else => return error.UnexpectedRefKind,
    };
    try std.testing.expectEqualStrings("auto?", nested.rule_name);
    try std.testing.expectEqual(@as(usize, 1), nested.arg_bindings.len);
    try std.testing.expectEqualStrings("t", nested.arg_bindings[0].name);
    try std.testing.expectEqual(@as(usize, 1), nested.search_params.len);
    try std.testing.expectEqualStrings("nodes", nested.search_params[0].name);
    try std.testing.expectEqual(@as(u64, 400), nested.search_params[0].value);
}

test "proof script parser rejects the parameter form on real rules" {
    // Only search placeholders accept `name: INTEGER`; a real rule keeps the
    // strict `name := $ math $` grammar.
    const src =
        \\demo
        \\----
        \\l1: $ c $ by rule1 (a: 4)
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = ProofScript.Parser.init(arena.allocator(), src);
    try std.testing.expectError(
        error.UnexpectedCharacter,
        parser.nextBlock(),
    );
}

test "proof script parser reads zero-ref inline applications" {
    const src =
        \\demo
        \\----
        \\l1: $ c $ by rule1 [rule2 []]
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = ProofScript.Parser.init(arena.allocator(), src);
    const block = (try parser.nextBlock()).?;
    const line = block.lines[0];
    switch (line.application.refs[0]) {
        .application => |child| {
            try std.testing.expectEqualStrings("rule2", child.rule_name);
            try std.testing.expectEqual(@as(usize, 0), child.refs.len);
            try std.testing.expect(child.refs_span != null);
        },
        else => return error.UnexpectedRefKind,
    }
}

test "proof script parser requires theorem underlines" {
    const src =
        \\main
        \\l1: $ a -> a $ by id []
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = ProofScript.Parser.init(arena.allocator(), src);
    try std.testing.expectError(
        error.ExpectedBlockUnderline,
        parser.nextBlock(),
    );
}

test "proof script parser requires lemma underlines" {
    const src =
        \\lemma id (a: wff): $ a -> a $
        \\l1: $ a -> a $ by ax_id (a := $ a $) []
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = ProofScript.Parser.init(arena.allocator(), src);
    try std.testing.expectError(
        error.ExpectedBlockUnderline,
        parser.nextBlock(),
    );
}

test "proof script parser rejects two-dash underlines" {
    const src =
        \\main
        \\--
        \\l1: $ a -> a $ by id []
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = ProofScript.Parser.init(arena.allocator(), src);
    try std.testing.expectError(
        error.ExpectedBlockUnderline,
        parser.nextBlock(),
    );
}

test "proof script parser rejects underline trailing comments" {
    const src =
        \\main
        \\---- -- underline comment
        \\l1: $ a -> a $ by id []
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = ProofScript.Parser.init(arena.allocator(), src);
    try std.testing.expectError(
        error.ExpectedBlockUnderline,
        parser.nextBlock(),
    );
}

test "proof script parser allows header trailing comments" {
    const src =
        \\main -- theorem comment
        \\----
        \\l1: $ a -> a $ by id []
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = ProofScript.Parser.init(arena.allocator(), src);
    const block = (try parser.nextBlock()).?;
    try std.testing.expect(block.kind == .theorem);
    try std.testing.expectEqualStrings("main", block.name);
    try std.testing.expectEqual(@as(usize, 1), block.lines.len);
}

test "proof script parser reads lemma blocks" {
    const src =
        \\lemma id (a: wff): $ a -> a $
        \\---------------------------
        \\l1: $ a -> a $ by ax_id (a := $ a $) []
        \\
        \\main
        \\----
        \\l1: $ a -> a $ by id (a := $ a $) []
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = ProofScript.Parser.init(arena.allocator(), src);
    const lemma = (try parser.nextBlock()).?;
    try std.testing.expect(lemma.kind == .lemma);
    try std.testing.expectEqualStrings("id", lemma.name);
    try std.testing.expectEqualStrings(
        "(a: wff): $ a -> a $",
        lemma.header_tail,
    );
    try std.testing.expectEqual(@as(usize, 1), lemma.lines.len);

    const theorem = (try parser.nextBlock()).?;
    try std.testing.expect(theorem.kind == .theorem);
    try std.testing.expectEqualStrings("main", theorem.name);
    try std.testing.expect((try parser.nextBlock()) == null);
}

test "proof script parser reads multiline lemma headers" {
    const src =
        \\lemma id (a: wff):
        \\  $ a $ >
        \\  $ a $
        \\------------------
        \\l1: $ a $ by ax_keep [#1]
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = ProofScript.Parser.init(arena.allocator(), src);
    const lemma = (try parser.nextBlock()).?;
    try std.testing.expect(lemma.kind == .lemma);
    try std.testing.expectEqualStrings("id", lemma.name);
    try std.testing.expectEqualStrings(
        "(a: wff):\n  $ a $ >\n  $ a $",
        lemma.header_tail,
    );
    try std.testing.expectEqual(@as(usize, 1), lemma.lines.len);
    try std.testing.expect((try parser.nextBlock()) == null);
}

test "proof script parser allows comments before lemma underlines" {
    const src =
        \\lemma id (a: wff):
        \\  $ a $
        \\-- standalone comment before the underline
        \\------------------
        \\l1: $ a $ by ax_keep [#1]
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = ProofScript.Parser.init(arena.allocator(), src);
    const lemma = (try parser.nextBlock()).?;
    try std.testing.expect(lemma.kind == .lemma);
    try std.testing.expectEqualStrings("id", lemma.name);
    try std.testing.expectEqualStrings(
        "(a: wff):\n  $ a $",
        lemma.header_tail,
    );
    try std.testing.expectEqual(@as(usize, 1), lemma.lines.len);
}

test "proof script parser allows newlines inside math strings" {
    const src =
        \\demo
        \\----
        \\l1: $ a ->
        \\  a $ by ax_id (a := $ a ->
        \\  a $) []
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = ProofScript.Parser.init(arena.allocator(), src);
    const block = (try parser.nextBlock()).?;
    try std.testing.expect(block.kind == .theorem);
    try std.testing.expectEqual(@as(usize, 1), block.lines.len);
    try std.testing.expectEqualStrings(
        " a ->\n  a ",
        block.lines[0].assertion.text,
    );
    try std.testing.expectEqual(@as(usize, 1), block.lines[0].application.arg_bindings.len);
    try std.testing.expectEqualStrings(
        " a ->\n  a ",
        block.lines[0].application.arg_bindings[0].formula.text,
    );
}

test "proof script parser allows continuation newlines and comments" {
    const src =
        \\demo
        \\----
        \\l1:
        \\  $ a $
        \\  -- explain the rule choice
        \\  by
        \\  ax_keep
        \\  (
        \\    a := $ a $,
        \\    -- reuse the same witness
        \\    b := $ a $
        \\  )
        \\  [
        \\    #1,
        \\    l0
        \\  ]
        \\l2: $ b $ by ax_b []
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = ProofScript.Parser.init(arena.allocator(), src);
    const block = (try parser.nextBlock()).?;
    try std.testing.expect(block.kind == .theorem);
    try std.testing.expectEqual(@as(usize, 2), block.lines.len);
    try std.testing.expectEqualStrings(" a ", block.lines[0].assertion.text);
    try std.testing.expectEqualStrings("ax_keep", block.lines[0].application.rule_name);
    try std.testing.expectEqual(@as(usize, 2), block.lines[0].application.arg_bindings.len);
    try std.testing.expectEqual(@as(usize, 2), block.lines[0].application.refs.len);
    switch (block.lines[0].application.refs[0]) {
        .hyp => |hyp| try std.testing.expectEqual(@as(usize, 1), hyp.index),
        else => return error.UnexpectedRefKind,
    }
    switch (block.lines[0].application.refs[1]) {
        .line => |line| try std.testing.expectEqualStrings("l0", line.label),
        else => return error.UnexpectedRefKind,
    }
    try std.testing.expectEqualStrings("l2", block.lines[1].label);
}

test "proof script parser recovers to the next block header" {
    const src =
        \\bad_parse
        \\---------
        \\l1: $ top $ by [#1]
        \\
        \\good_block
        \\----------
        \\l1: $ top $ by keep []
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = ProofScript.Parser.init(arena.allocator(), src);
    try std.testing.expectError(error.ExpectedIdentifier, parser.nextBlock());
    try std.testing.expect(parser.recoverToNextBlockBoundary());

    const block = (try parser.nextBlock()).?;
    try std.testing.expect(block.kind == .theorem);
    try std.testing.expectEqualStrings("good_block", block.name);
    try std.testing.expectEqual(@as(usize, 1), block.lines.len);
    try std.testing.expect((try parser.nextBlock()) == null);
}

test "proof script parser recovers to lemma blocks with binders" {
    const src =
        \\bad_parse
        \\---------
        \\l1: $ top $ by [#1]
        \\
        \\lemma helper (a: wff): $ a $
        \\--------------------------
        \\l1: $ a $ by keep [#1]
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = ProofScript.Parser.init(arena.allocator(), src);
    try std.testing.expectError(error.ExpectedIdentifier, parser.nextBlock());
    try std.testing.expect(parser.recoverToNextBlockBoundary());

    const block = (try parser.nextBlock()).?;
    try std.testing.expect(block.kind == .lemma);
    try std.testing.expectEqualStrings("helper", block.name);
    try std.testing.expectEqualStrings(
        "(a: wff): $ a $",
        block.header_tail,
    );
    try std.testing.expectEqual(@as(usize, 1), block.lines.len);
    try std.testing.expect((try parser.nextBlock()) == null);
}

test "proof script parser recovery ignores proof-line comments" {
    const src =
        \\bad_parse
        \\---------
        \\l1: $ top $ by [#1]
        \\l2 -- stray comment on a broken proof line
        \\
        \\good_block
        \\----------
        \\l1: $ top $ by keep []
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = ProofScript.Parser.init(arena.allocator(), src);
    try std.testing.expectError(error.ExpectedIdentifier, parser.nextBlock());
    try std.testing.expect(parser.recoverToNextBlockBoundary());

    const block = (try parser.nextBlock()).?;
    try std.testing.expect(block.kind == .theorem);
    try std.testing.expectEqualStrings("good_block", block.name);
    try std.testing.expectEqual(@as(usize, 1), block.lines.len);
    try std.testing.expect((try parser.nextBlock()) == null);
}

test "proof script parser recovery ignores bare identifier fragments" {
    const src =
        \\bad_parse
        \\---------
        \\l1: $ top $ by [#1]
        \\l2
        \\
        \\good_block
        \\----------
        \\l1: $ top $ by keep []
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = ProofScript.Parser.init(arena.allocator(), src);
    try std.testing.expectError(error.ExpectedIdentifier, parser.nextBlock());
    try std.testing.expect(parser.recoverToNextBlockBoundary());

    const block = (try parser.nextBlock()).?;
    try std.testing.expect(block.kind == .theorem);
    try std.testing.expectEqualStrings("good_block", block.name);
    try std.testing.expectEqual(@as(usize, 1), block.lines.len);
    try std.testing.expect((try parser.nextBlock()) == null);
}

test "proof script parser recovery ignores bare identifiers at eof" {
    const src =
        \\bad_parse
        \\---------
        \\l1: $ top $ by [#1]
        \\junk
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = ProofScript.Parser.init(arena.allocator(), src);
    try std.testing.expectError(error.ExpectedIdentifier, parser.nextBlock());
    try std.testing.expect(!parser.recoverToNextBlockBoundary());
}

test "proof script parser recovery requires underlines on later blocks" {
    const src =
        \\bad_parse
        \\---------
        \\l1: $ top $ by [#1]
        \\
        \\good_block
        \\l1: $ top $ by keep []
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = ProofScript.Parser.init(arena.allocator(), src);
    try std.testing.expectError(error.ExpectedIdentifier, parser.nextBlock());
    try std.testing.expect(!parser.recoverToNextBlockBoundary());
}

test "lenient parser keeps a broken line's label and goal" {
    // `by a?` is the shape a reader is mid-keystroke in: a rule name that no
    // longer parses because a `?` is being typed after it.
    const src =
        \\main
        \\----
        \\l1: $ top $ by keep []
        \\l2: $ top $ by a?
        \\l3: $ top $ by keep [l1]
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = ProofScript.Parser.initLenient(arena.allocator(), src);
    const block = (try parser.nextBlock()).?;
    try std.testing.expectEqual(@as(usize, 3), block.lines.len);

    try std.testing.expect(!block.lines[0].incomplete);
    try std.testing.expect(!block.lines[2].incomplete);

    const broken = block.lines[1];
    try std.testing.expect(broken.incomplete);
    try std.testing.expectEqualStrings("l2", broken.label);
    try std.testing.expectEqualStrings(" top ", broken.assertion.text);
    try std.testing.expectEqualStrings("", broken.application.rule_name);
    try std.testing.expectEqualStrings(
        "l2",
        src[broken.label_span.start..broken.label_span.end],
    );
    // The line claims its own text and no more.
    try std.testing.expectEqualStrings(
        "l2: $ top $ by a?",
        src[broken.span.start..broken.span.end],
    );
    try std.testing.expect((try parser.nextBlock()) == null);
}

test "lenient parser keeps the label when the goal is half-typed" {
    const src =
        \\main
        \\----
        \\l1: $ top
        \\l2: $ top $ by keep []
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = ProofScript.Parser.initLenient(arena.allocator(), src);
    const block = (try parser.nextBlock()).?;
    try std.testing.expectEqual(@as(usize, 2), block.lines.len);
    try std.testing.expect(block.lines[0].incomplete);
    try std.testing.expectEqualStrings("l1", block.lines[0].label);
    try std.testing.expectEqualStrings("", block.lines[0].assertion.text);
    try std.testing.expect(!block.lines[1].incomplete);
    try std.testing.expectEqualStrings("l2", block.lines[1].label);
}

test "lenient parser resyncs past a broken line's continuation" {
    const src =
        \\main
        \\----
        \\l1: $ top $ by keep [] junk
        \\    more junk
        \\l2: $ top $ by keep []
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = ProofScript.Parser.initLenient(arena.allocator(), src);
    const block = (try parser.nextBlock()).?;
    try std.testing.expectEqual(@as(usize, 2), block.lines.len);
    try std.testing.expect(block.lines[0].incomplete);
    try std.testing.expect(!block.lines[1].incomplete);
    try std.testing.expectEqualStrings("l2", block.lines[1].label);
}

test "lenient parser stops a block at the next item header" {
    const src =
        \\main
        \\----
        \\l1: $ top $ by a?
        \\
        \\later
        \\-----
        \\l1: $ top $ by keep []
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = ProofScript.Parser.initLenient(arena.allocator(), src);
    const first = (try parser.nextBlock()).?;
    try std.testing.expectEqualStrings("main", first.name);
    try std.testing.expectEqual(@as(usize, 1), first.lines.len);
    try std.testing.expect(first.lines[0].incomplete);

    const second = (try parser.nextBlock()).?;
    try std.testing.expectEqualStrings("later", second.name);
    try std.testing.expectEqual(@as(usize, 1), second.lines.len);
    try std.testing.expect(!second.lines[0].incomplete);
    try std.testing.expect((try parser.nextBlock()) == null);
}

test "lenient parser terminates on a run of broken lines at eof" {
    const src =
        \\main
        \\----
        \\l1: $ top $ by a?
        \\l2: $ top $ by a?
        \\l3: $ top $ by a?
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = ProofScript.Parser.initLenient(arena.allocator(), src);
    const block = (try parser.nextBlock()).?;
    try std.testing.expectEqual(@as(usize, 3), block.lines.len);
    for (block.lines) |line| try std.testing.expect(line.incomplete);
    try std.testing.expect((try parser.nextBlock()) == null);
}

test "strict parser still rejects a broken proof line" {
    const src =
        \\main
        \\----
        \\l1: $ top $ by keep []
        \\l2: $ top $ by a?
        \\l3: $ top $ by keep [l1]
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = ProofScript.Parser.init(arena.allocator(), src);
    try std.testing.expectError(error.ExpectedLineEnd, parser.nextBlock());
}

test "proof script parser reads headerless def items" {
    const src =
        \\def foo = $ x $
        \\
        \\main
        \\----
        \\l1: $ x $ by keep []
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = ProofScript.Parser.init(arena.allocator(), src);
    const item = (try parser.nextItem()).?;
    switch (item) {
        .def => |def| {
            try std.testing.expectEqualStrings("foo", def.name);
            try std.testing.expect(def.header_tail == null);
            try std.testing.expectEqualStrings(" x ", def.body.text);
        },
        else => return error.UnexpectedProofItem,
    }

    const block = (try parser.nextBlock()).?;
    try std.testing.expectEqualStrings("main", block.name);
}

test "proof script parser reads full-header def items" {
    const src =
        \\def local_foo (x: obj): obj = $ x $
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = ProofScript.Parser.init(arena.allocator(), src);
    const item = (try parser.nextItem()).?;
    switch (item) {
        .def => |def| {
            try std.testing.expectEqualStrings("local_foo", def.name);
            try std.testing.expectEqualStrings(
                "(x: obj): obj",
                def.header_tail.?,
            );
            try std.testing.expect(def.header_tail_span != null);
            try std.testing.expectEqualStrings(" x ", def.body.text);
        },
        else => return error.UnexpectedProofItem,
    }
    try std.testing.expect((try parser.nextItem()) == null);
}

test "proof script parser preserves comments and annotations before defs" {
    const src =
        \\-- ordinary comment
        \\--| @local-note
        \\def local_foo (x: obj): obj = $ x $
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = ProofScript.Parser.init(arena.allocator(), src);
    const item = (try parser.nextItem()).?;
    switch (item) {
        .def => |def| {
            try std.testing.expectEqual(@as(usize, 1), def.annotations.len);
            try std.testing.expectEqualStrings("@local-note", def.annotations[0]);
        },
        else => return error.UnexpectedProofItem,
    }
}

test "proof script parser recovers from malformed def items" {
    const src =
        \\def bad = not_math
        \\
        \\good_block
        \\----------
        \\l1: $ top $ by keep []
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = ProofScript.Parser.init(arena.allocator(), src);
    try std.testing.expectError(error.ExpectedMathString, parser.nextItem());
    try std.testing.expect(parser.diagnosticSpan() != null);
    try std.testing.expect(parser.recoverToNextItemBoundary());

    const block = (try parser.nextBlock()).?;
    try std.testing.expectEqualStrings("good_block", block.name);
    try std.testing.expectEqual(@as(usize, 1), block.lines.len);
}

test "mm0 parser preserves hidden dummy names" {
    const src =
        \\sort obj;
        \\def quote (.d ._: obj): obj;
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = MM0Parser.init(src, arena.allocator());
    _ = (try parser.next()).?;
    const stmt = (try parser.next()).?;
    const term = switch (stmt) {
        .term => |value| value,
        else => return error.UnexpectedStatementKind,
    };

    try std.testing.expectEqual(@as(usize, 2), term.dummy_args.len);
    try std.testing.expectEqual(@as(usize, 2), term.dummy_names.len);
    try std.testing.expectEqualStrings("d", term.dummy_names[0].?);
    try std.testing.expect(term.dummy_names[1] == null);
}

test "public def body parser sees visible args" {
    const src =
        \\sort obj;
        \\def id (x: obj): obj;
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = MM0Parser.init(src, arena.allocator());
    _ = (try parser.next()).?;
    const stmt = (try parser.next()).?;
    const term = switch (stmt) {
        .term => |value| value,
        else => return error.UnexpectedStatementKind,
    };

    const body = try parser.parsePublicDefBodyText(
        term,
        "x",
        .{ .start = 0, .end = 1 },
    );
    try std.testing.expect(body == term.arg_exprs[0]);
}

test "public def body parser sees named hidden dummy binders" {
    const src =
        \\sort obj;
        \\def pick (.d: obj): obj;
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = MM0Parser.init(src, arena.allocator());
    _ = (try parser.next()).?;
    const stmt = (try parser.next()).?;
    const term = switch (stmt) {
        .term => |value| value,
        else => return error.UnexpectedStatementKind,
    };

    const body = try parser.parsePublicDefBodyText(
        term,
        "d",
        .{ .start = 0, .end = 1 },
    );
    try std.testing.expect(body == term.dummy_exprs[0]);
}

test "public def body parser rejects unknown and anonymous binders" {
    const src =
        \\sort obj;
        \\def pick (._: obj): obj;
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = MM0Parser.init(src, arena.allocator());
    _ = (try parser.next()).?;
    const stmt = (try parser.next()).?;
    const term = switch (stmt) {
        .term => |value| value,
        else => return error.UnexpectedStatementKind,
    };

    try std.testing.expectError(
        error.UnknownMathToken,
        parser.parsePublicDefBodyText(
            term,
            "_",
            .{ .start = 0, .end = 1 },
        ),
    );
    try std.testing.expectError(
        error.UnknownMathToken,
        parser.parsePublicDefBodyText(
            term,
            "missing",
            .{ .start = 0, .end = 7 },
        ),
    );
}

test "filler dummy tail extends a bodyless def's dummies" {
    const src =
        \\sort obj;
        \\def pick {x: obj} (y: obj): obj;
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = MM0Parser.init(src, arena.allocator());
    _ = (try parser.next()).?;
    const stmt = (try parser.next()).?;
    const term = switch (stmt) {
        .term => |value| value,
        else => return error.UnexpectedStatementKind,
    };

    const extended = try parser.extendStmtWithFillerDummies(
        term,
        "(.d: obj)",
        0,
    );
    try std.testing.expectEqual(@as(usize, 1), extended.dummy_args.len);
    try std.testing.expectEqualStrings("d", extended.dummy_names[0].?);
    const dummy = extended.dummy_exprs[0];
    try std.testing.expect(dummy.bound());
    // The bound var x occupies dep bit 0; the filler dummy comes next.
    try std.testing.expectEqual(@as(u55, 1) << 1, dummy.deps());

    const body = try parser.parsePublicDefBodyText(
        extended,
        "d",
        .{ .start = 0, .end = 1 },
    );
    try std.testing.expect(body == dummy);
}

test "filler dummies append after mm0-declared dummies" {
    const src =
        \\sort obj;
        \\def pick (.m: obj): obj;
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = MM0Parser.init(src, arena.allocator());
    _ = (try parser.next()).?;
    const stmt = (try parser.next()).?;
    const term = switch (stmt) {
        .term => |value| value,
        else => return error.UnexpectedStatementKind,
    };

    const extended = try parser.extendStmtWithFillerDummies(
        term,
        "(.d .e: obj)",
        0,
    );
    try std.testing.expectEqual(@as(usize, 3), extended.dummy_args.len);
    try std.testing.expectEqualStrings("m", extended.dummy_names[0].?);
    try std.testing.expectEqualStrings("d", extended.dummy_names[1].?);
    try std.testing.expectEqualStrings("e", extended.dummy_names[2].?);
    try std.testing.expectEqual(@as(u55, 1) << 0, extended.dummy_exprs[0].deps());
    try std.testing.expectEqual(@as(u55, 1) << 1, extended.dummy_exprs[1].deps());
    try std.testing.expectEqual(@as(u55, 1) << 2, extended.dummy_exprs[2].deps());
}

test "filler dummy tail rejects invalid binders" {
    const src =
        \\sort obj;
        \\def pick (y: obj): obj;
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = MM0Parser.init(src, arena.allocator());
    _ = (try parser.next()).?;
    const stmt = (try parser.next()).?;
    const term = switch (stmt) {
        .term => |value| value,
        else => return error.UnexpectedStatementKind,
    };

    try std.testing.expectError(
        error.FillerBinderMustBeDummy,
        parser.extendStmtWithFillerDummies(term, "(x: obj)", 0),
    );
    try std.testing.expectError(
        error.DuplicateFillerBinderName,
        parser.extendStmtWithFillerDummies(term, "(.y: obj)", 0),
    );
    try std.testing.expectError(
        error.DuplicateFillerBinderName,
        parser.extendStmtWithFillerDummies(term, "(.d .d: obj)", 0),
    );
    try std.testing.expectError(
        error.UnknownSort,
        parser.extendStmtWithFillerDummies(term, "(.d: nope)", 0),
    );
    try std.testing.expectError(
        error.PublicDefBodyMustBeHeaderless,
        parser.extendStmtWithFillerDummies(term, "junk", 0),
    );
    try std.testing.expectError(
        error.PublicDefBodyMustBeHeaderless,
        parser.extendStmtWithFillerDummies(term, "(.d: obj", 0),
    );
}

test "def item classifier separates local defs from filler tails" {
    const src =
        \\def plain = $ x $
        \\def filler (.d: obj) = $ d $
        \\def local (x: obj): obj = $ x $
        \\def nullary: obj = $ z $
        \\def depped {x: obj} (p: obj x): obj = $ p $
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = ProofScript.Parser.init(arena.allocator(), src);
    const expected = [_]bool{ false, false, true, true, true };
    for (expected) |is_local| {
        const item = (try parser.nextItem()).?;
        const def = switch (item) {
            .def => |value| value,
            else => return error.UnexpectedItemKind,
        };
        try std.testing.expectEqual(is_local, def.isLocalDef());
    }
}

test "local def parser mutates live term table" {
    const src =
        \\sort obj;
        \\term zero: obj;
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = MM0Parser.init(src, arena.allocator());
    _ = (try parser.next()).?;
    _ = (try parser.next()).?;

    const local = try parser.parseLocalDefText(
        "id",
        .{ .start = 10, .end = 12 },
        "(x: obj): obj",
        "x",
        .{ .start = 24, .end = 25 },
    );
    try std.testing.expectEqualStrings("id", local.name);

    var vars = std.StringHashMap(*const Expr).init(arena.allocator());
    const expr = try parser.parseMathText("id zero", &vars);
    switch (expr.*) {
        .term => |app| {
            try std.testing.expectEqual(@as(u32, 1), app.id);
            try std.testing.expectEqual(@as(usize, 1), app.args.len);
        },
        else => return error.UnexpectedExprNode,
    }
}

test "local def parser rejects duplicate term names" {
    const src =
        \\sort obj;
        \\term zero: obj;
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = MM0Parser.init(src, arena.allocator());
    _ = (try parser.next()).?;
    _ = (try parser.next()).?;

    const span = MathSpan{ .start = 5, .end = 9 };
    try std.testing.expectError(
        error.DuplicateTermName,
        parser.parseLocalDefText(
            "zero",
            span,
            "(x: obj): obj",
            "x",
            null,
        ),
    );
    const diag = parser.diagnosticSpan().?;
    try std.testing.expectEqual(span.start, diag.start);
    try std.testing.expectEqual(span.end, diag.end);
}

test "local def parser maps body diagnostics to proof spans" {
    const src =
        \\sort obj;
        \\term zero: obj;
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = MM0Parser.init(src, arena.allocator());
    _ = (try parser.next()).?;
    _ = (try parser.next()).?;

    const body_span = MathSpan{ .start = 100, .end = 107 };
    try std.testing.expectError(
        error.UnknownMathToken,
        parser.parseLocalDefText(
            "bad",
            .{ .start = 4, .end = 7 },
            ": obj",
            "missing",
            body_span,
        ),
    );
    const diag = parser.diagnosticSpan().?;
    try std.testing.expectEqual(body_span.start, diag.start);
    try std.testing.expectEqual(body_span.end, diag.end);
}

test "theorem context preserves theorem var identity" {
    const src =
        \\provable sort wff;
        \\theorem thm (a b: wff): $ a $;
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = MM0Parser.init(src, arena.allocator());
    _ = (try parser.next()).?;
    const stmt = (try parser.next()).?;
    const assertion = switch (stmt) {
        .assertion => |value| value,
        else => return error.UnexpectedStatementKind,
    };

    var ctx = FrontendExpr.TheoremContext.init(std.testing.allocator);
    defer ctx.deinit();

    try ctx.seedAssertion(assertion);
    try std.testing.expectEqual(@as(usize, 2), ctx.theorem_vars.items.len);

    const first = ctx.theorem_vars.items[0];
    const second = ctx.theorem_vars.items[1];
    try std.testing.expect(first != second);

    const first_node = ctx.interner.node(first);
    const first_value = first_node.*;
    switch (first_value) {
        .variable => |var_id| switch (var_id) {
            .theorem_var => |idx| {
                try std.testing.expectEqual(@as(u32, 0), idx);
            },
            else => return error.UnexpectedVariableKind,
        },
        else => return error.UnexpectedExprNode,
    }

    const second_node = ctx.interner.node(second);
    const second_value = second_node.*;
    switch (second_value) {
        .variable => |var_id| switch (var_id) {
            .theorem_var => |idx| {
                try std.testing.expectEqual(@as(u32, 1), idx);
            },
            else => return error.UnexpectedVariableKind,
        },
        else => return error.UnexpectedExprNode,
    }
}

test "theorem context rejects dummy dependency slot overflow" {
    var ctx = FrontendExpr.TheoremContext.init(std.testing.allocator);
    defer ctx.deinit();

    const limit = FrontendExpr.tracked_bound_dep_limit;
    try ctx.seedBinderCount(limit - 1);
    ctx.next_dummy_dep = limit - 1;

    const last_dummy = try ctx.addDummyVarResolved("wff", 0);
    try std.testing.expectEqual(@as(usize, 1), ctx.theorem_dummies.items.len);
    try std.testing.expectEqual(
        @as(u55, 1) << @intCast(limit - 1),
        ctx.theorem_dummies.items[0].deps,
    );
    try std.testing.expectEqual(limit, ctx.next_dummy_dep);

    const node = ctx.interner.node(last_dummy);
    switch (node.*) {
        .variable => |var_id| switch (var_id) {
            .dummy_var => |idx| try std.testing.expectEqual(@as(u32, 0), idx),
            else => return error.UnexpectedVariableKind,
        },
        else => return error.UnexpectedExprNode,
    }

    try std.testing.expectError(
        error.DependencySlotExhausted,
        ctx.addDummyVarResolved("wff", 0),
    );
    try std.testing.expectEqual(@as(usize, 1), ctx.theorem_dummies.items.len);
    try std.testing.expectEqual(limit, ctx.next_dummy_dep);
}

test "theorem context interns parsed expressions with sharing" {
    const src =
        \\provable sort wff;
        \\term imp (a b: wff): wff;
        \\theorem thm (a b: wff): $ imp a b $ > $ imp a b $;
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = MM0Parser.init(src, arena.allocator());
    _ = (try parser.next()).?;
    _ = (try parser.next()).?;
    const stmt = (try parser.next()).?;
    const assertion = switch (stmt) {
        .assertion => |value| value,
        else => return error.UnexpectedStatementKind,
    };

    var ctx = FrontendExpr.TheoremContext.init(std.testing.allocator);
    defer ctx.deinit();

    try ctx.seedAssertion(assertion);
    const concl_id = try ctx.internParsedExpr(assertion.concl);

    try std.testing.expectEqual(@as(usize, 1), ctx.theorem_hyps.items.len);
    try std.testing.expectEqual(ctx.theorem_hyps.items[0], concl_id);
    try std.testing.expectEqual(@as(usize, 3), ctx.interner.count());
}

test "template instantiation shares repeated substitutions" {
    const src =
        \\provable sort wff;
        \\term imp (a b: wff): wff;
        \\axiom dup (a: wff): $ imp a a $;
        \\theorem host (p q: wff): $ imp p q $;
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = MM0Parser.init(src, arena.allocator());
    var env = FrontendEnv.GlobalEnv.init(arena.allocator());

    const sort_stmt = (try parser.next()).?;
    try env.addStmt(sort_stmt);
    const term_stmt = (try parser.next()).?;
    try env.addStmt(term_stmt);
    const axiom_stmt = (try parser.next()).?;
    try env.addStmt(axiom_stmt);
    const host_stmt = (try parser.next()).?;
    try env.addStmt(host_stmt);

    const host = switch (host_stmt) {
        .assertion => |value| value,
        else => return error.UnexpectedStatementKind,
    };
    const rule = env.rules.items[0];

    var ctx = FrontendExpr.TheoremContext.init(std.testing.allocator);
    defer ctx.deinit();

    try ctx.seedAssertion(host);
    const subst = try ctx.internParsedExpr(host.concl);
    const inst = try ctx.instantiateTemplate(rule.concl, &.{subst});

    const inst_node = ctx.interner.node(inst);
    const inst_value = inst_node.*;
    switch (inst_value) {
        .app => |app| {
            try std.testing.expectEqual(@as(u32, 0), app.term_id);
            try std.testing.expectEqual(@as(usize, 2), app.args.len);
            try std.testing.expectEqual(subst, app.args[0]);
            try std.testing.expectEqual(subst, app.args[1]);
        },
        else => return error.UnexpectedExprNode,
    }
}

test "expr interner clone snapshot hides later base nodes" {
    var base = FrontendExpr.ExprInterner.init(std.testing.allocator);
    defer base.deinit();

    const v0 = try base.internVar(.{ .theorem_var = 0 });
    try std.testing.expectEqual(@as(FrontendExpr.ExprId, 0), v0);

    var clone = try base.clone();
    defer clone.deinit();

    _ = try base.internVar(.{ .theorem_var = 1 });
    try std.testing.expectEqual(@as(usize, 2), base.count());
    try std.testing.expectEqual(@as(usize, 1), clone.count());

    const overlay_before = clone.nodes.items.len;
    const clone_v1 = try clone.internVar(.{ .theorem_var = 1 });
    try std.testing.expectEqual(@as(FrontendExpr.ExprId, 1), clone_v1);
    try std.testing.expectEqual(overlay_before + 1, clone.nodes.items.len);
}

test "expr interner flatten survives deinit of former base" {
    var base = FrontendExpr.ExprInterner.init(std.testing.allocator);
    var base_owned = true;
    defer if (base_owned) base.deinit();

    const v0 = try base.internVar(.{ .theorem_var = 0 });
    const app0 = try base.internApp(10, &.{v0});

    var clone = try base.clone();
    defer clone.deinit();

    const v1 = try clone.internVar(.{ .theorem_var = 1 });
    const app1 = try clone.internApp(11, &.{ app0, v1 });

    try clone.flatten();
    try std.testing.expect(clone.base == null);
    base.deinit();
    base_owned = false;

    try std.testing.expectEqual(@as(usize, 4), clone.count());
    try std.testing.expectEqual(app0, try clone.internApp(10, &.{v0}));
    try std.testing.expectEqual(app1, try clone.internApp(11, &.{ app0, v1 }));

    switch (clone.node(app1).*) {
        .app => |app| {
            try std.testing.expectEqual(@as(u32, 11), app.term_id);
            try std.testing.expectEqual(@as(usize, 2), app.args.len);
            try std.testing.expectEqual(app0, app.args[0]);
            try std.testing.expectEqual(v1, app.args[1]);
        },
        else => return error.UnexpectedExprNode,
    }
}

test "expr interner supports clone chains" {
    var base = FrontendExpr.ExprInterner.init(std.testing.allocator);
    var base_owned = true;
    defer if (base_owned) base.deinit();

    const v0 = try base.internVar(.{ .theorem_var = 0 });

    var clone1 = try base.clone();
    var clone1_owned = true;
    defer if (clone1_owned) clone1.deinit();

    const v1 = try clone1.internVar(.{ .theorem_var = 1 });
    const app1 = try clone1.internApp(10, &.{ v0, v1 });

    var clone2 = try clone1.clone();
    defer clone2.deinit();

    const found_app1 = try clone2.internApp(10, &.{ v0, v1 });
    try std.testing.expectEqual(app1, found_app1);
    try std.testing.expectEqual(@as(usize, 0), clone2.nodes.items.len);

    const v2 = try clone2.internVar(.{ .theorem_var = 2 });
    const app2 = try clone2.internApp(11, &.{ app1, v2 });

    try clone2.flatten();
    clone1.deinit();
    clone1_owned = false;
    base.deinit();
    base_owned = false;

    try std.testing.expectEqual(@as(usize, 5), clone2.count());
    try std.testing.expectEqual(app1, try clone2.internApp(10, &.{ v0, v1 }));
    try std.testing.expectEqual(app2, try clone2.internApp(11, &.{ app1, v2 }));

    switch (clone2.node(app2).*) {
        .app => |app| {
            try std.testing.expectEqual(@as(u32, 11), app.term_id);
            try std.testing.expectEqual(@as(usize, 2), app.args.len);
            try std.testing.expectEqual(app1, app.args[0]);
            try std.testing.expectEqual(v2, app.args[1]);
        },
        else => return error.UnexpectedExprNode,
    }
}

test "explicit source dummy allocation is allowed and tracks dependency slots" {
    // Explicit user/source dummies (seedTerm, applyDummyBindings) are
    // legitimate and must keep working. This test verifies the low-level
    // addDummyVarResolved API that those paths use.
    var ctx = FrontendExpr.TheoremContext.init(std.testing.allocator);
    defer ctx.deinit();

    // Allocate two explicit dummies — simulates what seedTerm does for
    // dummies declared in .mm0 source.
    const d0 = try ctx.addDummyVarResolved("wff", 0);
    const d1 = try ctx.addDummyVarResolved("wff", 0);

    // Each allocation should produce a distinct ExprId.
    try std.testing.expect(d0 != d1);

    // Both should be tracked in theorem_dummies.
    try std.testing.expectEqual(@as(usize, 2), ctx.theorem_dummies.items.len);

    // Each should consume a distinct dependency slot (one-hot bit).
    try std.testing.expect(ctx.theorem_dummies.items[0].deps != ctx.theorem_dummies.items[1].deps);

    // The dependency counter should advance by 2.
    try std.testing.expectEqual(@as(u32, 2), ctx.next_dummy_dep);
}

test "placeholder allocation leaves real dummy bookkeeping unchanged" {
    var ctx = FrontendExpr.TheoremContext.init(std.testing.allocator);
    defer ctx.deinit();

    _ = try ctx.addDummyVarResolved("wff", 0);
    const start_dummy_id = ctx.next_dummy_id;
    const start_dummy_dep = ctx.next_dummy_dep;

    _ = try ctx.addPlaceholderResolved("wff");
    _ = try ctx.addPlaceholderResolved("wff");

    try std.testing.expectEqual(start_dummy_id, ctx.next_dummy_id);
    try std.testing.expectEqual(start_dummy_dep, ctx.next_dummy_dep);
    try std.testing.expectEqual(
        @as(usize, 1),
        ctx.theorem_dummies.items.len,
    );
    try std.testing.expectEqual(
        @as(usize, 2),
        ctx.theorem_placeholders.items.len,
    );
    try std.testing.expect(
        ctx.theorem_placeholders.items[0].deps !=
            ctx.theorem_placeholders.items[1].deps,
    );
    try std.testing.expect(
        (ctx.theorem_placeholders.items[0].deps &
            ctx.theorem_dummies.items[0].deps) == 0,
    );
}

test "placeholder deps share the global u55 mask budget" {
    var ctx = FrontendExpr.TheoremContext.init(std.testing.allocator);
    defer ctx.deinit();

    const limit = FrontendExpr.tracked_bound_dep_limit;
    ctx.next_dummy_dep = limit - 1;

    const placeholder = try ctx.addPlaceholderResolved("wff");
    try std.testing.expectEqual(
        @as(u55, 1) << @intCast(limit - 1),
        ctx.theorem_placeholders.items[0].deps,
    );
    try std.testing.expectEqual(@as(u32, 0), ctx.next_dummy_id);
    try std.testing.expectEqual(limit - 1, ctx.next_dummy_dep);
    switch (ctx.interner.node(placeholder).*) {
        .placeholder => |idx| try std.testing.expectEqual(@as(u32, 0), idx),
        else => return error.UnexpectedExprNode,
    }

    try std.testing.expectError(
        error.DependencySlotExhausted,
        ctx.addPlaceholderResolved("wff"),
    );
    try std.testing.expectEqual(@as(usize, 1), ctx.theorem_placeholders.items.len);
}

test "dummy allocation respects placeholder dep reservations" {
    var ctx = FrontendExpr.TheoremContext.init(std.testing.allocator);
    defer ctx.deinit();

    const limit = FrontendExpr.tracked_bound_dep_limit;
    const placeholder = try ctx.addPlaceholderResolved("wff");
    _ = placeholder;

    for (0..limit - 1) |_| {
        _ = try ctx.addDummyVarResolved("wff", 0);
    }

    try std.testing.expectEqual(limit - 1, ctx.next_dummy_dep);
    try std.testing.expectError(
        error.DependencySlotExhausted,
        ctx.addDummyVarResolved("wff", 0),
    );
    try std.testing.expectEqual(
        @as(usize, limit - 1),
        ctx.theorem_dummies.items.len,
    );
    for (ctx.theorem_dummies.items) |dummy| {
        try std.testing.expect(
            dummy.deps & ctx.theorem_placeholders.items[0].deps == 0,
        );
    }
}

test "placeholder info lookup reports placeholder-specific errors" {
    var ctx = FrontendExpr.TheoremContext.init(std.testing.allocator);
    defer ctx.deinit();

    try std.testing.expectError(
        error.UnknownPlaceholder,
        ctx.requirePlaceholderInfo(0),
    );
}

test "leaf info helpers cover theorem vars dummies and placeholders" {
    var ctx = FrontendExpr.TheoremContext.init(std.testing.allocator);
    defer ctx.deinit();

    const ArgInfo = @typeInfo(@TypeOf(ctx.arg_infos)).pointer.child;
    const args = [_]ArgInfo{
        .{ .sort_name = "wff", .bound = false, .deps = 0 },
        .{ .sort_name = "obj", .bound = true, .deps = 1 },
    };
    const arg_exprs = [_]*const Expr{
        &.{ .variable = .{ .sort = 0, .bound = false, .deps = 0 } },
        &.{ .variable = .{ .sort = 0, .bound = true, .deps = 1 } },
    };
    try ctx.seedArgs(args[0..], arg_exprs[0..]);

    const theorem_leaf = (try ctx.currentLeafInfo(ctx.theorem_vars.items[1])) orelse {
        return error.MissingLeafInfo;
    };
    try std.testing.expectEqualStrings("obj", theorem_leaf.sort_name);
    try std.testing.expect(theorem_leaf.bound);
    try std.testing.expectEqual(@as(u55, 1), theorem_leaf.deps);

    const dummy = try ctx.addDummyVarResolved("wff", 0);
    const dummy_leaf = (try ctx.currentLeafInfo(dummy)) orelse {
        return error.MissingLeafInfo;
    };
    try std.testing.expectEqualStrings("wff", dummy_leaf.sort_name);
    try std.testing.expect(dummy_leaf.bound);

    const placeholder = try ctx.addPlaceholderResolved("obj");
    const placeholder_leaf = (try ctx.currentLeafInfo(placeholder)) orelse {
        return error.MissingLeafInfo;
    };
    try std.testing.expectEqualStrings(
        "obj",
        placeholder_leaf.sort_name,
    );
    try std.testing.expect(placeholder_leaf.bound);
    try std.testing.expectEqual(
        placeholder_leaf.sort_name,
        ctx.currentLeafSortName(placeholder).?,
    );
}

test "mirror-only dummy allocation does not affect source theorem context" {
    // Mirror-only allocations (mirror_support.zig, normalized_match.zig)
    // create dummies in a temporary TheoremContext. This test verifies that
    // allocating dummies in a separate mirror context leaves the original
    // source context's dummy count untouched.
    var source = FrontendExpr.TheoremContext.init(std.testing.allocator);
    defer source.deinit();

    // Allocate one explicit dummy in the source context.
    _ = try source.addDummyVarResolved("wff", 0);
    try std.testing.expectEqual(@as(usize, 1), source.theorem_dummies.items.len);
    const source_dep_after = source.next_dummy_dep;

    // Create a separate mirror context (simulates MirroredTheoremContext).
    var mirror = FrontendExpr.TheoremContext.init(std.testing.allocator);
    defer mirror.deinit();

    // Allocate several dummies in the mirror context.
    _ = try mirror.addDummyVarResolved("wff", 0);
    _ = try mirror.addDummyVarResolved("wff", 0);
    _ = try mirror.addDummyVarResolved("wff", 0);

    // Mirror allocations should not have touched the source context.
    try std.testing.expectEqual(@as(usize, 1), source.theorem_dummies.items.len);
    try std.testing.expectEqual(source_dep_after, source.next_dummy_dep);

    // Mirror context should have its own independent count.
    try std.testing.expectEqual(@as(usize, 3), mirror.theorem_dummies.items.len);
}

test "MM0 parser recovers to the next statement boundary" {
    const src =
        \\provable sort wff;
        \\term top: wff;
        \\axiom bad $ top $;
        \\axiom good: $ top $;
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = MM0Parser.init(src, arena.allocator());
    _ = (try parser.next()).?;
    _ = (try parser.next()).?;
    try std.testing.expectError(error.UnexpectedChar, parser.next());
    try parser.recoverToStatementBoundary();

    const stmt = (try parser.next()).?;
    switch (stmt) {
        .assertion => |assert_stmt| {
            try std.testing.expectEqualStrings("good", assert_stmt.name);
        },
        else => return error.UnexpectedStatementKind,
    }

    try std.testing.expect((try parser.next()) == null);
}

test "MM0 parser recovery skips semicolons inside math strings" {
    const src =
        \\provable sort wff;
        \\term top: wff;
        \\axiom bad $ top ; top $;
        \\axiom good: $ top $;
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = MM0Parser.init(src, arena.allocator());
    _ = (try parser.next()).?;
    _ = (try parser.next()).?;
    try std.testing.expectError(error.UnexpectedChar, parser.next());
    try parser.recoverToStatementBoundary();

    const stmt = (try parser.next()).?;
    switch (stmt) {
        .assertion => |assert_stmt| {
            try std.testing.expectEqualStrings("good", assert_stmt.name);
        },
        else => return error.UnexpectedStatementKind,
    }
}

test "MM0 parser recovery skips semicolons inside comments" {
    const src =
        \\provable sort wff;
        \\term top: wff;
        \\axiom bad $ top $
        \\-- comment ; not a boundary
        \\;
        \\axiom good: $ top $;
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = MM0Parser.init(src, arena.allocator());
    _ = (try parser.next()).?;
    _ = (try parser.next()).?;
    try std.testing.expectError(error.UnexpectedChar, parser.next());
    try parser.recoverToStatementBoundary();

    const stmt = (try parser.next()).?;
    switch (stmt) {
        .assertion => |assert_stmt| {
            try std.testing.expectEqualStrings("good", assert_stmt.name);
        },
        else => return error.UnexpectedStatementKind,
    }
}

test "MM0 parser recovery skips semicolons inside quoted strings" {
    const src =
        \\provable sort wff;
        \\term top: wff;
        \\axiom bad "not ; a boundary";
        \\axiom good: $ top $;
    ;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var parser = MM0Parser.init(src, arena.allocator());
    _ = (try parser.next()).?;
    _ = (try parser.next()).?;
    try std.testing.expectError(error.UnexpectedChar, parser.next());
    try parser.recoverToStatementBoundary();

    const stmt = (try parser.next()).?;
    switch (stmt) {
        .assertion => |assert_stmt| {
            try std.testing.expectEqualStrings("good", assert_stmt.name);
        },
        else => return error.UnexpectedStatementKind,
    }
}
