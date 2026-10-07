const std = @import("std");
const lsp = @import("lsp");
const lsp_diagnostics = @import("lsp_diagnostics");

const offsets = lsp_diagnostics.offsets;
const Position = lsp.types.Position;

test "a span inside a character widens to the whole character" {
    const text = "a ⊢ b";
    // One byte of the three-byte `⊢`.
    const range = offsets.locToRange(text, .{ .start = 2, .end = 3 }, .@"utf-16");
    try std.testing.expectEqual(Position{ .line = 0, .character = 2 }, range.start);
    try std.testing.expectEqual(Position{ .line = 0, .character = 3 }, range.end);
    const inner = offsets.locToRange(text, .{ .start = 3, .end = 4 }, .@"utf-8");
    try std.testing.expectEqual(@as(u32, 2), inner.start.character);
    try std.testing.expectEqual(@as(u32, 5), inner.end.character);
}

test "invalid bytes count as one replacement character each" {
    const text = "x\xff\xe2\x8ay\n\xf0\x9f\x98\x80z";
    for ([_]offsets.Encoding{ .@"utf-8", .@"utf-16", .@"utf-32" }) |encoding| {
        for (0..text.len + 1) |index| {
            const position = offsets.indexToPosition(text, index, encoding, false);
            try std.testing.expect(offsets.positionToIndex(text, position, encoding) <= index);
        }
    }
    // `\xe2\x8a` is a truncated sequence: two replacements before `y`.
    const y = offsets.indexToPosition(text, 4, .@"utf-16", false);
    try std.testing.expectEqual(Position{ .line = 0, .character = 4 }, y);
    // The emoji is a surrogate pair in UTF-16.
    const z = offsets.indexToPosition(text, text.len - 1, .@"utf-16", false);
    try std.testing.expectEqual(Position{ .line = 1, .character = 2 }, z);
}

test "positions past the line or the text clamp" {
    const text = "ab\ncd";
    const past_line = offsets.positionToIndex(text, .{ .line = 0, .character = 9 }, .@"utf-16");
    try std.testing.expectEqual(@as(usize, 2), past_line);
    const past_text = offsets.positionToIndex(text, .{ .line = 7, .character = 0 }, .@"utf-16");
    try std.testing.expectEqual(text.len, past_text);
}

test "valid text converts like lsp_kit" {
    const text = "a¶↉🠁\nb ⊢ c\n";
    for ([_]offsets.Encoding{ .@"utf-8", .@"utf-16", .@"utf-32" }) |encoding| {
        var index: usize = 0;
        while (index <= text.len) : (index += 1) {
            // Only character boundaries are lsp_kit's to answer.
            if (index < text.len and (text[index] & 0xC0) == 0x80) continue;
            const expected = lsp.offsets.indexToPosition(text, index, encoding);
            try std.testing.expectEqual(expected, offsets.indexToPosition(text, index, encoding, false));
            try std.testing.expectEqual(index, offsets.positionToIndex(text, expected, encoding));
        }
    }
}
