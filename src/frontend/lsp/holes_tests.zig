const std = @import("std");
const Index = @import("index.zig");
const CompilerModule = @import("../compiler.zig");
const Snapshot = Index.Snapshot;

/// What an analysis of a proof found for its holes.
const HoleHovers = struct {
    snapshot: Snapshot,
    found: CompilerModule.HoleInferenceSink,
    arena: std.heap.ArenaAllocator,

    fn init(mm0_text: []const u8, proof_text: []const u8) !HoleHovers {
        const allocator = std.testing.allocator;
        var found = CompilerModule.HoleInferenceSink{ .allocator = allocator };
        errdefer found.deinit();
        var compiler = CompilerModule.Compiler.initWithProof(allocator, mm0_text, proof_text);
        compiler.allow_search_placeholders = true;
        compiler.hole_inference_sink = &found;
        compiler.analyze() catch |err| {
            if (err == error.OutOfMemory) return err;
        };
        // An editor's analysis fills no lines in; the fill action does.
        try std.testing.expectEqual(0, found.assertions.items.len);
        return .{
            .snapshot = try Snapshot.build(allocator, .{
                .mm0_text = mm0_text,
                .proof_text = proof_text,
            }),
            .found = found,
            .arena = std.heap.ArenaAllocator.init(allocator),
        };
    }

    fn deinit(self: *HoleHovers) void {
        self.arena.deinit();
        self.found.deinit();
        self.snapshot.deinit();
    }

    /// The hover at `offset`, which the index must know as a hole. A check of
    /// its proof alone finds the same.
    fn at(self: *HoleHovers, offset: usize) !Index.HoverResult {
        const arena = self.arena.allocator();
        const hover = try Index.holes.hoverAt(
            arena,
            &self.found,
            offset,
        ) orelse return error.MissingHoleHover;
        try std.testing.expect(self.snapshot.isHoleAt(offset));
        const block = (try self.snapshot.blockTouching(arena, offset)).?;
        const alone = try Index.holes.ofBlock(
            arena,
            self.snapshot.mm0_text,
            self.snapshot.proof_text.?,
            block,
            false,
            self.snapshot.knownBodies(),
        );
        try std.testing.expectEqualDeep(
            hover,
            (try Index.holes.hoverAt(arena, &alone, offset)).?,
        );
        return hover;
    }
};

test "proof hole hover shows the inferred expression" {
    const mm0_text =
        \\delimiter $ ( ) $;
        \\--| @hole _wff
        \\provable sort wff;
        \\term pair (a b: wff): wff;
        \\term imp (a b: wff): wff;
        \\infixr imp: $->$ prec 25;
        \\axiom select_right (a b: wff): $ pair a b $ > $ b $;
        \\theorem main (p r s: wff):
        \\  $ pair p (r -> s) $ > $ r -> s $;
    ;
    const proof_text =
        \\main
        \\----
        \\l1: $ _wff $ by select_right [#1]
    ;
    var hovers = try HoleHovers.init(mm0_text, proof_text);
    defer hovers.deinit();

    const offset =
        (std.mem.indexOf(u8, proof_text, "_wff") orelse unreachable) + 1;
    const hover = try hovers.at(offset);
    try std.testing.expectEqualStrings(
        "_wff",
        proof_text[hover.range.start..hover.range.end],
    );
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        hover.markdown,
        1,
        "$ r -> s $",
    ));
}

test "proof hole hover reads a hole against the math string's delimiters" {
    const mm0_text =
        \\delimiter $ ( ) $;
        \\--| @hole _
        \\provable sort wff;
        \\term imp (a b: wff): wff;
        \\infixr imp: $->$ prec 25;
        \\axiom mp (a b: wff): $ a -> b $ > $ a $ > $ b $;
        \\theorem main (p q: wff): $ p -> q $ > $ p $ > $ q $;
    ;
    const proof_text =
        \\main
        \\----
        \\l1: $_$ by mp [#1, #2]
    ;
    var hovers = try HoleHovers.init(mm0_text, proof_text);
    defer hovers.deinit();
    const offset = std.mem.indexOf(u8, proof_text, "_$") orelse unreachable;
    const hover = try hovers.at(offset);
    try std.testing.expectEqualStrings(
        "_",
        proof_text[hover.range.start..hover.range.end],
    );
}

test "proof hole hover goes past a search placeholder in its proof" {
    const mm0_text =
        \\delimiter $ ( ) $;
        \\--| @hole _wff
        \\provable sort wff;
        \\term imp (a b: wff): wff;
        \\infixr imp: $->$ prec 25;
        \\axiom mp (a b: wff): $ a -> b $ > $ a $ > $ b $;
        \\theorem main (p q: wff): $ p -> q $ > $ p $ > $ q $;
    ;
    const proof_text =
        \\main
        \\----
        \\l1: $ p $ by exact?
        \\l2: $ _wff $ by mp [#1, l1]
    ;
    var hovers = try HoleHovers.init(mm0_text, proof_text);
    defer hovers.deinit();
    const offset = std.mem.indexOf(u8, proof_text, "_wff") orelse unreachable;
    const hover = try hovers.at(offset + 1);
    try std.testing.expect(std.mem.containsAtLeast(u8, hover.markdown, 1, "$ q $"));
}

test "a bare named-unknown prefix is not a hole" {
    const mm0_text =
        \\delimiter $ ( ) $;
        \\--| @unknown ?
        \\provable sort wff;
        \\theorem main (p: wff): $ p $ > $ p $;
    ;
    const proof_text =
        \\main
        \\----
        \\l1: $ ? ?a $ by ?
    ;
    var hovers = try HoleHovers.init(mm0_text, proof_text);
    defer hovers.deinit();
    const bare = std.mem.indexOf(u8, proof_text, "? ?a") orelse unreachable;
    try std.testing.expect(!hovers.snapshot.isHoleAt(bare));
    try std.testing.expect(hovers.snapshot.isHoleAt(bare + 2));
}

test "named unknown hovers show the value at every occurrence" {
    const mm0_text =
        \\delimiter $ ( ) $;
        \\--| @unknown ?
        \\provable sort wff;
        \\term imp (a b: wff): wff;
        \\infixr imp: $->$ prec 25;
        \\axiom mp (a b: wff): $ a -> b $ > $ a $ > $ b $;
        \\axiom ax1 (a b: wff): $ a -> b -> a $;
        \\theorem main (p q: wff): $ p $ > $ q -> p $;
    ;
    // `?c` is fixed only by the later `mp`, so both lines are written
    // concrete before the walk checks them.
    const proof_text =
        \\main
        \\----
        \\l1: $ ?c $ by ax1 []
        \\l2: $ ?c $ by ax1 []
        \\l3: $ q -> p $ by mp [l1, #1]
    ;
    var hovers = try HoleHovers.init(mm0_text, proof_text);
    defer hovers.deinit();

    var start: usize = 0;
    var seen: usize = 0;
    while (std.mem.indexOfPos(u8, proof_text, start, "?c")) |at| : (start = at + 2) {
        const hover = try hovers.at(at + 1);
        try std.testing.expectEqualStrings(
            "?c",
            proof_text[hover.range.start..hover.range.end],
        );
        try std.testing.expect(std.mem.containsAtLeast(
            u8,
            hover.markdown,
            1,
            "$ p -> q -> p $",
        ));
        seen += 1;
    }
    try std.testing.expectEqual(@as(usize, 2), seen);
}

fn expectPartlyInferredHover(
    mm0_text: []const u8,
    proof_text: []const u8,
    token: []const u8,
    expected: []const u8,
) !void {
    var hovers = try HoleHovers.init(mm0_text, proof_text);
    defer hovers.deinit();
    const at = std.mem.indexOf(u8, proof_text, token) orelse unreachable;
    const hover = try hovers.at(at + 1);
    try std.testing.expectEqualStrings(
        token,
        proof_text[hover.range.start..hover.range.end],
    );
    try std.testing.expect(std.mem.startsWith(u8, hover.markdown, "Partly inferred expression:"));
    try std.testing.expect(std.mem.containsAtLeast(u8, hover.markdown, 1, expected));
}

const partly_inferred_mm0 =
    \\delimiter $ ( ) $;
    \\--| @unknown ?
    \\--| @hole _wff
    \\provable sort wff;
    \\term imp (a b: wff): wff;
    \\infixr imp: $->$ prec 25;
    \\axiom mp (a b: wff): $ a -> b $ > $ a $ > $ b $;
    \\theorem main (p q: wff): $ q -> p $;
;

test "named unknown hover shows a partly inferred shape with its open names" {
    try expectPartlyInferredHover(partly_inferred_mm0,
        \\main
        \\----
        \\l1: $ ?a $ by ?
        \\l2: $ ?b $ by ?
        \\l3: $ q -> p $ by mp [l1, l2]
    , "?a", "$ ?b -> q -> p $");
}

test "named unknown hover prints an anonymous open part as its sort's hole" {
    try expectPartlyInferredHover(partly_inferred_mm0,
        \\main
        \\----
        \\l1: $ ?a $ by ?
        \\l2: $ q -> p $ by mp [l1, ?]
    , "?a", "$ _wff -> q -> p $");
}

test "proof hole hovers are independent for each occurrence" {
    const mm0_text =
        \\delimiter $ ( ) $;
        \\--| @hole _wff
        \\provable sort wff;
        \\term pair (a b: wff): wff;
        \\term imp (a b: wff): wff;
        \\infixr imp: $->$ prec 25;
        \\axiom keep_pair (a b: wff):
        \\  $ pair a b $ > $ pair a b $;
        \\theorem main (p r s: wff):
        \\  $ pair p (r -> s) $ > $ pair p (r -> s) $;
    ;
    const proof_text =
        \\main
        \\----
        \\l1: $ pair _wff _wff $ by keep_pair [#1]
    ;
    var hovers = try HoleHovers.init(mm0_text, proof_text);
    defer hovers.deinit();

    const first_offset = std.mem.indexOf(u8, proof_text, "_wff") orelse {
        return error.MissingFirstHole;
    };
    const second_offset = std.mem.lastIndexOf(u8, proof_text, "_wff") orelse {
        return error.MissingSecondHole;
    };
    try std.testing.expect(first_offset != second_offset);

    const first = try hovers.at(first_offset + 1);
    const second = try hovers.at(second_offset + 1);
    try std.testing.expectEqual(first_offset, first.range.start);
    try std.testing.expectEqual(second_offset, second.range.start);
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        first.markdown,
        1,
        "$ p $",
    ));
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        second.markdown,
        1,
        "$ r -> s $",
    ));
}
