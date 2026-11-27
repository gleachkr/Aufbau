const std = @import("std");
const Index = @import("index.zig");
const CheckMemo = @import("../compiler/check_memo.zig").CheckMemo;
const CompilerModule = @import("../compiler.zig");
const proof_script = @import("../proof_script.zig");
const Snapshot = Index.Snapshot;

const support = @import("./test_support.zig");
const buildSnapshot = support.buildSnapshot;

test "snapshot build propagates allocation failure" {
    var buffer: [1]u8 = undefined;
    var fixed = std.heap.FixedBufferAllocator.init(&buffer);
    try std.testing.expectError(error.OutOfMemory, Snapshot.build(
        fixed.allocator(),
        .{
            .mm0_uri = "file:///test.mm0",
            .mm0_text = "provable sort wff;",
        },
    ));
}

test "malformed sources still index parsed prefixes" {
    const mm0_text =
        \\provable sort wff;
        \\term top: wff;
        \\axiom top_i: $ top $;
        \\theorem main: $ top $;
        \\not a valid statement
    ;
    const proof_text =
        \\main
        \\----
        \\l1: $ top $ by top_i []
        \\
        \\bad_block
    ;
    var snapshot = try buildSnapshot(mm0_text, proof_text);
    defer snapshot.deinit();

    const rule_offset =
        (std.mem.indexOf(u8, proof_text, "top_i") orelse unreachable) + 1;
    const def = try snapshot.definitionAt(.proof, rule_offset) orelse {
        return error.MissingPrefixDefinition;
    };
    try std.testing.expectEqualStrings("file:///test.mm0", def.uri);
    try std.testing.expectEqualStrings(
        "top_i",
        snapshot.mm0_text[def.range.start..def.range.end],
    );
}

test "snapshot indexes global mm0 declarations" {
    var snapshot = try Snapshot.build(std.testing.allocator, .{
        .mm0_uri = "file:///test.mm0",
        .mm0_text =
        \\provable sort wff;
        \\term imp (a b: wff): wff;
        \\axiom ax_mp (a b: wff): $ imp a b $ > $ a $ > $ b $;
        \\theorem imp_refl (a: wff): $ imp a a $;
        ,
    });
    defer snapshot.deinit();

    try std.testing.expectEqual(@as(usize, 4), snapshot.declarations.len);
    try std.testing.expect(snapshot.decl_by_name.contains("wff"));
    try std.testing.expect(snapshot.decl_by_name.contains("imp"));
    try std.testing.expect(snapshot.decl_by_name.contains("ax_mp"));
    try std.testing.expect(snapshot.decl_by_name.contains("imp_refl"));
}

test "snapshot outlines mm0 declarations" {
    const text =
        \\provable sort wff;
        \\term top: wff;
        \\axiom top_i: $ top $;
        \\theorem main: $ top $;
    ;
    var snapshot = try buildSnapshot(text, null);
    defer snapshot.deinit();

    const outline = snapshot.outline(.mm0);
    try std.testing.expectEqual(@as(usize, 4), outline.len);
    try std.testing.expectEqualStrings("wff", outline[0].name);
    try std.testing.expectEqual(Index.DeclarationKind.sort, outline[0].kind);
    try std.testing.expectEqualStrings("top", outline[1].name);
    try std.testing.expectEqual(Index.DeclarationKind.term, outline[1].kind);
    try std.testing.expectEqualStrings("top_i", outline[2].name);
    try std.testing.expectEqual(Index.DeclarationKind.axiom, outline[2].kind);
    try std.testing.expectEqualStrings("main", outline[3].name);
    try std.testing.expectEqual(
        Index.DeclarationKind.theorem,
        outline[3].kind,
    );
    try std.testing.expectEqualStrings(
        "theorem main: $ top $;",
        snapshot.mm0_text[outline[3].range.start..outline[3].range.end],
    );
}

test "snapshot outlines proof blocks without line children" {
    const mm0_text =
        \\provable sort wff;
        \\term top: wff;
        \\axiom top_i: $ top $;
        \\theorem main: $ top $;
    ;
    const proof_text =
        \\main
        \\----
        \\l1: $ top $ by top_i []
        \\l2: $ top $ by top_i []
    ;
    var snapshot = try buildSnapshot(mm0_text, proof_text);
    defer snapshot.deinit();

    const outline = snapshot.outline(.proof);
    try std.testing.expectEqual(@as(usize, 1), outline.len);
    try std.testing.expectEqualStrings("main", outline[0].name);
    try std.testing.expectEqual(Index.DeclarationKind.theorem, outline[0].kind);
    try std.testing.expectEqual(@as(usize, 0), outline[0].children.len);
}

test "a proof body sees only the names declared before it" {
    const mm0_text =
        \\provable sort wff;
        \\term top: wff;
        \\axiom top_i: $ top $;
        \\theorem first: $ top $;
        \\theorem second: $ top $;
    ;
    const proof_text =
        \\lemma tl: $ top $
        \\----
        \\l1: $ top $ by top_i []
        \\
        \\first
        \\-----
        \\l1: $ lt $ by tl []
        \\l2: $ ! $ by later []
        \\
        \\def lt: wff = $ top $
        \\prefix lt: $!$ prec max;
        \\
        \\lemma tl: $ top $
        \\----
        \\l1: $ top $ by top_i []
        \\
        \\lemma later: $ top $
        \\----
        \\l1: $ top $ by top_i []
        \\
        \\second
        \\------
        \\l1: $ lt $ by tl []
        \\l2: $ ! $ by later []
    ;
    var snapshot = try buildSnapshot(mm0_text, proof_text);
    defer snapshot.deinit();

    const first = std.mem.indexOf(u8, proof_text, "first").?;
    const second = std.mem.indexOf(u8, proof_text, "second").?;
    const lemma_one = std.mem.indexOf(u8, proof_text, "tl:").?;
    const lemma_two = std.mem.lastIndexOf(u8, proof_text, "tl:").?;
    const local_def = std.mem.indexOf(u8, proof_text, "lt: wff").?;

    for ([_][]const u8{ "lt $", "! $" }) |use| {
        const before = std.mem.indexOfPos(u8, proof_text, first, use).?;
        try std.testing.expect(try snapshot.hoverAt(.proof, before) == null);
        const after = std.mem.indexOfPos(u8, proof_text, second, use).?;
        const def = (try snapshot.definitionAt(.proof, after)).?;
        try std.testing.expectEqual(local_def, def.range.start);
    }
    for ([_]usize{ first, second }, [_]usize{ lemma_one, lemma_two }) |from, lemma| {
        const use = std.mem.indexOfPos(u8, proof_text, from, "tl []").?;
        const def = (try snapshot.definitionAt(.proof, use)).?;
        try std.testing.expectEqual(lemma, def.range.start);
    }
    const unknown = std.mem.indexOfPos(u8, proof_text, first, "later []").?;
    const hover = (try snapshot.hoverAt(.proof, unknown)).?;
    try std.testing.expect(std.mem.indexOf(u8, hover.markdown, "unknown") != null);
}

test "a snapshot with known bodies answers as one that parsed them" {
    const allocator = std.testing.allocator;
    const mm0_text =
        \\provable sort wff;
        \\term top: wff;
        \\axiom top_i: $ top $;
        \\theorem main: $ top $;
    ;
    const proof_text =
        \\lemma tl: $ top $
        \\----
        \\l1: $ top $ by top_i []
        \\l2: $ top $ by top_i []
        \\
        \\main
        \\----
        \\l1: $ top $ by tl []
        \\
    ;
    var memo = CheckMemo.init(allocator);
    defer memo.deinit();
    // The memo serves an editor's runs, which collect holes.
    var holes = CompilerModule.HoleInferenceSink{ .allocator = allocator };
    defer holes.deinit();
    var compiler = CompilerModule.Compiler.initWithProof(allocator, mm0_text, proof_text);
    compiler.hole_inference_sink = &holes;
    compiler.check_memo = &memo;
    try compiler.analyze();

    const broken_text = proof_text ++ "l2: $ top $ by\n";
    const close_text = try std.mem.replaceOwned(u8, allocator, proof_text, "\n\n", "\n");
    defer allocator.free(close_text);
    for (
        [_][]const u8{ proof_text, close_text, broken_text },
        [_]bool{ true, true, false },
    ) |text, whole| {
        var input: Index.SnapshotInput = .{
            .mm0_uri = "file:///test.mm0",
            .mm0_text = mm0_text,
            .proof_uri = "file:///test.auf",
            .proof_text = text,
        };
        var parsed = try Snapshot.build(allocator, input);
        defer parsed.deinit();
        input.check_memo = &memo;
        var known = try Snapshot.build(allocator, input);
        defer known.deinit();

        // Neither keeps a body's lines; a request parses them again.
        for (parsed.proof_blocks, known.proof_blocks) |a, b| {
            try std.testing.expectEqual(@as(usize, 0), a.source.lines.len);
            try std.testing.expectEqual(@as(usize, 0), b.source.lines.len);
        }
        // With the memo a parser passes over the first body, and over the
        // second while it is whole.
        var parse_arena = std.heap.ArenaAllocator.init(allocator);
        defer parse_arena.deinit();
        var parser = proof_script.Parser.initLenient(parse_arena.allocator(), text);
        parser.known_bodies = memo.knownBodies();
        for ([_]bool{ true, whole }) |passed| {
            const block = (try parser.nextBlockRecovering()).?;
            try std.testing.expectEqual(passed, block.known_body != null);
        }
        try std.testing.expectEqual(whole, known.complete);
        try std.testing.expectEqual(whole, parsed.complete);
        for (0..text.len) |offset| {
            try std.testing.expectEqualDeep(
                try parsed.hoverAt(.proof, offset),
                try known.hoverAt(.proof, offset),
            );
        }
        for (0..text.len + 1) |offset| {
            var arena_state = std.heap.ArenaAllocator.init(allocator);
            defer arena_state.deinit();
            const arena = arena_state.allocator();
            const block = try proof_script.blockTouching(arena, text, offset);
            try std.testing.expectEqualDeep(block, try parsed.blockTouching(arena, offset));
            try std.testing.expectEqualDeep(block, try known.blockTouching(arena, offset));
        }
    }
}

test "a snapshot keeps slices of its texts and copies the rest once" {
    const allocator = std.testing.allocator;
    const Compactor = @import("compact.zig").Compactor;
    const Record = struct {
        name: []const u8,
        markdown: []const u8,
        parts: []const []const u8,
        tag: ?union(enum) { none, label: []const u8 },
    };
    const text = "sort wff;";
    var built = std.heap.ArenaAllocator.init(allocator);
    defer built.deinit();
    const markdown = try built.allocator().dupe(u8, "**wff**");
    const parts = try built.allocator().dupe([]const u8, &.{ markdown, text[0..4] });
    const records = [_]Record{
        .{ .name = text[5..8], .markdown = markdown, .parts = parts, .tag = .{ .label = markdown } },
        .{ .name = text[0..4], .markdown = markdown, .parts = &.{}, .tag = null },
    };

    var kept = std.heap.ArenaAllocator.init(allocator);
    defer kept.deinit();
    var keep: Compactor = .{
        .arena = kept.allocator(),
        .allocator = allocator,
        .texts = &.{text},
    };
    defer keep.deinit();
    const copies = try keep.copy([]const Record, &records);
    @memset(markdown, 'x');

    try std.testing.expectEqual(text[5..].ptr, copies[0].name.ptr);
    try std.testing.expectEqual(text[0..].ptr, copies[0].parts[1].ptr);
    try std.testing.expectEqualStrings("**wff**", copies[0].markdown);
    // One copy of the string however many records share it.
    try std.testing.expectEqual(copies[0].markdown.ptr, copies[1].markdown.ptr);
    try std.testing.expectEqual(copies[0].markdown.ptr, copies[0].parts[0].ptr);
    try std.testing.expectEqual(copies[0].markdown.ptr, copies[0].tag.?.label.ptr);
    try std.testing.expect(copies[1].tag == null);
}

test "a snapshot tells a parser of its own proof text where the bodies end" {
    const allocator = std.testing.allocator;
    const mm0_text =
        \\provable sort wff;
        \\term top: wff;
        \\axiom top_i: $ top $;
        \\theorem main: $ top $;
        \\theorem other: $ top $;
    ;
    const proof_text =
        \\lemma tl: $ top $
        \\----
        \\l1: $ top $ by top_i []
        \\l2: $ top $ by top_i []
        \\
        \\main
        \\----
        \\l1: $ top $ by tl []
        \\other
        \\----
        \\l1: $ top $ by
        \\
    ;
    var snapshot = try Snapshot.build(allocator, .{
        .mm0_uri = "file:///test.mm0",
        .mm0_text = mm0_text,
        .proof_uri = "file:///test.auf",
        .proof_text = proof_text,
    });
    defer snapshot.deinit();
    var arena_state = std.heap.ArenaAllocator.init(allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();

    const copy = try arena.dupe(u8, proof_text);
    for ([_][]const u8{ proof_text, copy }) |text| {
        var plain = proof_script.Parser.initLenient(arena, text);
        var passing = proof_script.Parser.initLenient(arena, text);
        passing.known_bodies = snapshot.knownBodies();
        var blocks: usize = 0;
        while (try plain.nextBlockRecovering()) |block| : (blocks += 1) {
            const passed = (try passing.nextBlockRecovering()).?;
            try std.testing.expectEqual(block.span, passed.span);
            try std.testing.expectEqual(block.body_end, passed.body_end);
            // A different text, even an equal one, and a body that did not
            // parse cleanly are parsed.
            if (text.ptr != proof_text.ptr or !block.self_contained) {
                try std.testing.expectEqualDeep(block, passed);
                continue;
            }
            try std.testing.expectEqual(0, passed.lines.len);
            try std.testing.expectEqual(
                proof_script.KnownBodies.bodyHash(text[block.header_span.end..block.body_end]),
                passed.known_body.?,
            );
            // A header the snapshot did not parse there gets no answer.
            const known = snapshot.knownBodies();
            var shifted = block.header_span;
            shifted.start += 1;
            try std.testing.expectEqual(null, known.findFn(known.ctx, text, shifted));
        }
        try std.testing.expectEqual(3, blocks);
        try std.testing.expectEqual(null, try passing.nextBlockRecovering());
    }
}
