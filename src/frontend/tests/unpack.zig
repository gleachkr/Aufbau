const std = @import("std");
const mm0 = @import("mm0");

const ProofScript = mm0.ProofScript;
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

/// Expect a rewrite of the line at `needle` in `auf` that reads
/// `expected`, or none when it is null.
fn expectReplacement(
    mm0_src: []const u8,
    auf: []const u8,
    needle: []const u8,
    expected: ?[]const u8,
) !void {
    const allocator = std.testing.allocator;
    const offset = std.mem.indexOf(u8, auf, needle).?;
    const suggestion = (try unpackAt(allocator, mm0_src, auf, offset)) orelse {
        return std.testing.expectEqual(expected, null);
    };
    defer suggestion.deinit(allocator);
    try std.testing.expectEqualStrings(
        expected orelse return error.UnexpectedSuggestion,
        suggestion.replacement,
    );
}

fn offsetOf(needle: []const u8) usize {
    return std.mem.indexOf(u8, test_auf, needle).?;
}

fn unpackAt(
    allocator: std.mem.Allocator,
    mm0_src: []const u8,
    auf: []const u8,
    offset: usize,
) !?Unpack.UnpackSuggestion {
    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    const block = try ProofScript.blockTouching(arena_state.allocator(), auf, offset);
    return try Unpack.unpackAtSourceOffset(
        allocator,
        mm0_src,
        auf,
        block.?,
        offset,
        null,
    );
}

/// Expect no rewrite at `offset`, decided without checking anything.
fn expectNoTarget(auf: []const u8, offset: usize) !void {
    try std.testing.expectEqual(
        @as(?Unpack.UnpackSuggestion, null),
        try unpackAt(std.testing.failing_allocator, test_mm0, auf, offset),
    );
}

fn expectUnpack(
    offset: usize,
    expected_title: []const u8,
    expected_original: []const u8,
    expected_replacement: []const u8,
) !void {
    const allocator = std.testing.allocator;
    const suggestion = (try unpackAt(allocator, test_mm0, test_auf, offset)) orelse
        return error.ExpectedUnpackSuggestion;
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
    try expectNoTarget(test_auf, offsetOf("l1_1: $ top $"));
}

test "unpack targets a line after local def and notation items" {
    const allocator = std.testing.allocator;
    const auf =
        \\t1
        \\---
        \\l1_1: $ top $ by top_i []
        \\l1: $ b -> top $ by weaken (b := $ b $) [top_i []]
        \\
        \\def limp (a b: wff): wff = $ a -> b $
        \\infixr limp: $=>$ prec 25;
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
    const offset = std.mem.indexOf(u8, auf, "by conj_i [conj_i").?;
    const suggestion = (try unpackAt(allocator, test_mm0, auf, offset)) orelse
        return error.ExpectedUnpackSuggestion;
    defer suggestion.deinit(allocator);
    try std.testing.expectEqualStrings(
        "Unpack 4 inline applications",
        suggestion.title,
    );
    try std.testing.expectEqualStrings(
        \\l1_1: $ top $ by top_i
        \\l1_2: $ top $ by top_i
        \\l1_3: $ top /\ top $ by conj_i [l1_1, l1_2]
        \\l1_4: $ top $ by top_i
        \\l1: $ (top /\ top) /\ top $ by conj_i [l1_3, l1_4]
        \\
    ,
        suggestion.replacement,
    );
}

test "unpack offers nothing on a line containing a search placeholder" {
    const auf =
        \\t1
        \\---
        \\l1: $ b -> top $ by weaken (b := $ b $) [auto?]
        \\
    ;
    try expectNoTarget(auf, std.mem.indexOf(u8, auf, "by weaken").?);
}

test "unpack offers nothing in a block with a line that does not parse" {
    const auf =
        \\t1
        \\---
        \\l0: $ top $ by
        \\l1: $ b -> top $ by weaken (b := $ b $) [top_i []]
        \\
    ;
    try expectNoTarget(auf, std.mem.indexOf(u8, auf, "by weaken").?);
}

test "unpack offers nothing on the offset shared with a line before it" {
    // A line takes the offset its newline ends at.
    const auf =
        \\t1
        \\---
        \\l0: $ top $ by top_i []
        \\l1: $ b -> top $ by weaken (b := $ b $) [top_i []]
        \\
    ;
    try expectNoTarget(auf, std.mem.indexOf(u8, auf, "l1:").?);
}

test "unpack round-trips on a real fixture with rich notation" {
    const allocator = std.testing.allocator;
    var arena_state = std.heap.ArenaAllocator.init(allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();

    const mm0_src = try std.Io.Dir.cwd().readFileAlloc(std.testing.io, "tests/proof_cases/hoare.mm0", arena, .limited(16 * 1024 * 1024));
    const auf_src = try std.Io.Dir.cwd().readFileAlloc(std.testing.io, "tests/proof_cases/hoare.auf", arena, .limited(16 * 1024 * 1024));

    // `valid_mp [box_k [], l1]` — an inline application whose conclusion
    // renders through hoare's unicode notation (modal boxes, `→`, `⊨`).
    // The rewritten proof is checked, so a non-null result means the
    // pretty-printed conclusion re-parsed to a checking proof.
    const marker = "by valid_mp [box_k []";
    const offset = std.mem.indexOf(u8, auf_src, marker) orelse
        return error.MissingFixtureMarker;
    const suggestion = (try unpackAt(allocator, mm0_src, auf_src, offset)) orelse
        return error.ExpectedUnpackSuggestion;
    defer suggestion.deinit(allocator);
    try std.testing.expect(
        std.mem.indexOf(u8, suggestion.replacement, "by box_k") != null,
    );
}

test "unpack offers nothing when the line does not check" {
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
    try std.testing.expectError(
        error.OutOfMemory,
        unpackAt(std.testing.failing_allocator, test_mm0, auf, offset),
    );
    try std.testing.expectEqual(
        @as(?Unpack.UnpackSuggestion, null),
        try unpackAt(allocator, test_mm0, auf, offset),
    );
}

// Any other proof's check is the same before and after the rewrite, so only
// the target's own proof has to hold. The rewrite may even cite a lemma
// whose proof fails.
test "unpack offers its rewrite beside broken proofs and statements" {
    const mm0_src = test_mm0 ++ "\naxiom bad: $ nope $;\ntheorem t4: $ top $;\n";
    const auf =
        \\t1
        \\---
        \\l1: $ b -> top $ by nope_i []
        \\
        \\lemma broken: $ top /\ top $
        \\---------------------------
        \\l1: $ top /\ top $ by top_i
        \\
        \\t2
        \\---
        \\l1: $ (top /\ top) /\ top $ by conj_i [broken [], top_i []]
        \\
        \\t3
        \\---
        \\l1: $ p $ by auto?
        \\
        \\t4
        \\---
        \\l1: $ top /\ top $ by top_i
        \\
    ;
    try expectReplacement(mm0_src, auf, "by conj_i",
        \\l1_1: $ top /\ top $ by broken
        \\l1_2: $ top $ by top_i
        \\l1: $ (top /\ top) /\ top $ by conj_i [l1_1, l1_2]
        \\
    );
}

test "unpack rewrites a line of a lemma" {
    const auf =
        \\lemma other: $ top $
        \\-------------------
        \\l1: $ top $ by top_i
        \\
        \\lemma pair (p: wff): $ p $ > $ p /\ top $
        \\----------------------------------------
        \\l1: $ p /\ top $ by conj_i [#1, other []]
        \\
        \\t1
        \\---
        \\l1: $ b -> top $ by weaken [other []]
        \\
    ;
    try expectReplacement(test_mm0, auf, "by conj_i",
        \\l1_1: $ top $ by other
        \\l1: $ p /\ top $ by conj_i [#1, l1_1]
        \\
    );
}

test "unpack offers nothing when another line of the proof fails" {
    const auf =
        \\t1
        \\---
        \\l1: $ b -> top $ by weaken [top_i []]
        \\l2: $ b -> top $ by nope_i
        \\l3: $ b -> top $ by l1
        \\
    ;
    try expectReplacement(test_mm0, auf, "by weaken", null);
}

test "unpack offers its rewrite beside a search placeholder on another line" {
    const auf =
        \\t1
        \\---
        \\l1: $ top /\ top $ by auto?
        \\l2: $ b -> top $ by weaken [top_i []]
        \\
    ;
    try expectReplacement(test_mm0, auf, "by weaken",
        \\l2_1: $ top $ by top_i
        \\l2: $ b -> top $ by weaken [l2_1]
        \\
    );
}

// The hidden line proves the constant `top`, which reads back as the
// theorem's variable of that name.
test "unpack offers nothing when the rewritten proof does not check" {
    const mm0_src = test_mm0 ++
        \\
        \\axiom drop (a b: wff): $ a $ > $ b -> b $;
        \\theorem shadow (top: wff): $ top -> top $;
    ;
    const auf =
        \\shadow
        \\------
        \\l1: $ top -> top $ by drop [top_i []]
        \\
    ;
    try expectReplacement(mm0_src, auf, "by drop", null);
}
