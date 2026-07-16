const std = @import("std");
const mm0 = @import("mm0");

const Unpack = mm0.CompilerSupport.Unpack;

const test_mm0 =
    \\delimiter $ ( ) $;
    \\provable sort wff;
    \\term top: wff;
    \\term imp (a b: wff): wff;
    \\infixr imp: $->$ prec 25;
    \\term and (a b: wff): wff;
    \\infixr and: $/\$ prec 30;
    \\axiom top_i: $ top $;
    \\axiom conj_i (a b: wff): $ a $ > $ b $ > $ a /\ b $;
    \\axiom weaken (a b: wff): $ a $ > $ b -> a $;
    \\theorem t1 (b: wff): $ b -> top $;
    \\theorem t2: $ (top /\ top) /\ top $;
    \\theorem t3 (p: wff): $ p $ > $ (top -> p) /\ top $;
;

const test_auf =
    \\t1
    \\---
    \\l1_1: $ top $ by top_i []
    \\l1: $ b -> top $ by weaken (b := $ b $) [top_i []]
    \\
    \\t2
    \\---
    \\l1: $ (top /\ top) /\ top $ by conj_i [conj_i [top_i [], top_i []], top_i []]
    \\
    \\t3
    \\---
    \\l1: $ (top -> p) /\ top $ by conj_i [weaken [#1], top_i []]
    \\
;

fn offsetOf(needle: []const u8) usize {
    return std.mem.indexOf(u8, test_auf, needle).?;
}

fn expectUnpack(
    offset: usize,
    expected_title: []const u8,
    expected_original: []const u8,
    expected_replacement: []const u8,
) !void {
    const allocator = std.testing.allocator;
    const suggestion = (try Unpack.unpackAtSourceOffset(
        allocator,
        test_mm0,
        test_auf,
        offset,
    )) orelse return error.ExpectedUnpackSuggestion;
    defer suggestion.deinit(allocator);
    try std.testing.expectEqualStrings(expected_title, suggestion.title);
    try std.testing.expectEqualStrings(
        expected_original,
        test_auf[suggestion.replace_span.start..suggestion.replace_span.end],
    );
    try std.testing.expectEqualStrings(
        expected_replacement,
        suggestion.replacement,
    );
}

test "unpack materializes a single inline application, dodging label collisions" {
    // `l1_1` is already a label in the block, so the fresh label is `l1_2`.
    // The explicit binding is preserved verbatim.
    try expectUnpack(
        offsetOf("by weaken (b"),
        "Unpack inline application",
        "l1: $ b -> top $ by weaken (b := $ b $) [top_i []]\n",
        \\l1_2: $ top $ by top_i
        \\l1: $ b -> top $ by weaken (b := $ b $) [l1_2]
        \\
        ,
    );
}

test "unpack flattens nested inline applications in reference order" {
    try expectUnpack(
        offsetOf("by conj_i [conj_i"),
        "Unpack 4 inline applications",
        "l1: $ (top /\\ top) /\\ top $ " ++
            "by conj_i [conj_i [top_i [], top_i []], top_i []]\n",
        \\l1_1: $ top $ by top_i
        \\l1_2: $ top $ by top_i
        \\l1_3: $ top /\ top $ by conj_i [l1_1, l1_2]
        \\l1_4: $ top $ by top_i
        \\l1: $ (top /\ top) /\ top $ by conj_i [l1_3, l1_4]
        \\
        ,
    );
}

test "unpack preserves hypothesis refs and renders variable conclusions" {
    try expectUnpack(
        offsetOf("by conj_i [weaken"),
        "Unpack 2 inline applications",
        "l1: $ (top -> p) /\\ top $ by conj_i [weaken [#1], top_i []]\n",
        \\l1_1: $ top -> p $ by weaken [#1]
        \\l1_2: $ top $ by top_i
        \\l1: $ (top -> p) /\ top $ by conj_i [l1_1, l1_2]
        \\
        ,
    );
}

test "unpack offers nothing on lines without inline applications" {
    const allocator = std.testing.allocator;
    const offset = offsetOf("l1_1: $ top $");
    try std.testing.expectEqual(
        @as(?Unpack.UnpackSuggestion, null),
        try Unpack.unpackAtSourceOffset(allocator, test_mm0, test_auf, offset),
    );
    try std.testing.expect(
        !Unpack.hasTargetAt(allocator, test_auf, offset),
    );
    try std.testing.expect(
        Unpack.hasTargetAt(allocator, test_auf, offsetOf("by conj_i [conj_i")),
    );
}

test "unpack offers nothing on a line containing a search placeholder" {
    const allocator = std.testing.allocator;
    const auf =
        \\t1
        \\---
        \\l1: $ b -> top $ by weaken (b := $ b $) [auto?]
        \\
    ;
    const offset = std.mem.indexOf(u8, auf, "by weaken").?;
    try std.testing.expect(!Unpack.hasTargetAt(allocator, auf, offset));
    try std.testing.expectEqual(
        @as(?Unpack.UnpackSuggestion, null),
        try Unpack.unpackAtSourceOffset(allocator, test_mm0, auf, offset),
    );
}

test "unpack round-trips on a real fixture with rich notation" {
    const allocator = std.testing.allocator;
    var arena_state = std.heap.ArenaAllocator.init(allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();

    const mm0_src = try std.fs.cwd().readFileAlloc(
        arena,
        "tests/proof_cases/hoare.mm0",
        16 * 1024 * 1024,
    );
    const auf_src = try std.fs.cwd().readFileAlloc(
        arena,
        "tests/proof_cases/hoare.auf",
        16 * 1024 * 1024,
    );

    // `valid_mp [box_k [], l1]` — an inline application whose conclusion
    // renders through hoare's unicode notation (modal boxes, `→`, `⊨`).
    // The internal validation pass re-analyzes the rewritten document, so a
    // non-null result means the pretty-printed conclusion re-parsed to a
    // checking proof.
    const marker = "by valid_mp [box_k []";
    const offset = std.mem.indexOf(u8, auf_src, marker) orelse
        return error.MissingFixtureMarker;
    const suggestion = (try Unpack.unpackAtSourceOffset(
        allocator,
        mm0_src,
        auf_src,
        offset,
    )) orelse return error.ExpectedUnpackSuggestion;
    defer suggestion.deinit(allocator);
    try std.testing.expect(
        std.mem.indexOf(u8, suggestion.replacement, "by box_k") != null,
    );
}

test "unpack offers nothing when the document does not analyze cleanly" {
    const allocator = std.testing.allocator;
    // Unknown rule inside the inline application: there is a syntactic
    // target, but no trustworthy conclusions to materialize.
    const auf =
        \\t1
        \\---
        \\l1: $ b -> top $ by weaken (b := $ b $) [nope_i []]
        \\
    ;
    const offset = std.mem.indexOf(u8, auf, "by weaken").?;
    try std.testing.expect(Unpack.hasTargetAt(allocator, auf, offset));
    try std.testing.expectEqual(
        @as(?Unpack.UnpackSuggestion, null),
        try Unpack.unpackAtSourceOffset(allocator, test_mm0, auf, offset),
    );
}
