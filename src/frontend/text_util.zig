const std = @import("std");

/// Largest prefix of `text` no longer than `limit` bytes that does not split a
/// UTF-8 codepoint. Returns `text` unchanged when it already fits. Used to
/// truncate user-facing diagnostic text, which (since notation-aware rendering)
/// may contain multibyte tokens — a raw byte slice could emit invalid UTF-8.
pub fn truncateUtf8(text: []const u8, limit: usize) []const u8 {
    if (text.len <= limit) return text;
    var end = limit;
    // A continuation byte (0b10xxxxxx) means `end` lands inside a codepoint;
    // back up to the codepoint's start. At most 3 steps for valid UTF-8.
    while (end > 0 and text[end] & 0xC0 == 0x80) end -= 1;
    return text[0..end];
}

/// The text `render(writer, args...)` writes, as a slice owned by
/// `allocator`. An allocating writer fails only when its allocator does, so a
/// write failure comes back as `error.OutOfMemory`; callers that tell OOM
/// apart from other errors keep working.
pub fn allocRender(
    allocator: std.mem.Allocator,
    comptime render: anytype,
    args: anytype,
) ![]u8 {
    var out: std.Io.Writer.Allocating = .init(allocator);
    errdefer out.deinit();
    @call(.auto, render, .{&out.writer} ++ args) catch |err| switch (err) {
        error.WriteFailed => return error.OutOfMemory,
        else => |e| return e,
    };
    return out.toOwnedSlice();
}

test "allocRender reports a failed write as OutOfMemory" {
    const render = struct {
        fn render(writer: *std.Io.Writer, n: usize) std.Io.Writer.Error!void {
            try writer.splatByteAll('x', n);
        }
    }.render;
    const text = try allocRender(std.testing.allocator, render, .{3});
    defer std.testing.allocator.free(text);
    try std.testing.expectEqualStrings("xxx", text);
    var buffer: [8]u8 = undefined;
    var fixed: std.heap.FixedBufferAllocator = .init(&buffer);
    try std.testing.expectError(
        error.OutOfMemory,
        allocRender(fixed.allocator(), render, .{4096}),
    );
}

test "truncateUtf8 leaves short text untouched" {
    try std.testing.expectEqualStrings("abc", truncateUtf8("abc", 8));
    try std.testing.expectEqualStrings("abc", truncateUtf8("abc", 3));
}

test "truncateUtf8 cuts ASCII at the exact byte" {
    try std.testing.expectEqualStrings("abcd", truncateUtf8("abcdef", 4));
}

test "truncateUtf8 backs off a split multibyte codepoint" {
    // "a→b" is 1 + 3 + 1 = 5 bytes; "→" occupies bytes 1..4.
    const s = "a\u{2192}b";
    // Limit 2 lands inside "→" (byte 2 is a continuation byte) → back to 1.
    try std.testing.expectEqualStrings("a", truncateUtf8(s, 2));
    try std.testing.expectEqualStrings("a", truncateUtf8(s, 3));
    // Limit 4 is the boundary just after "→".
    try std.testing.expectEqualStrings("a\u{2192}", truncateUtf8(s, 4));
}

/// A token of scanned text and its byte span there.
pub const Token = struct {
    text: []const u8,
    start: usize,
    end: usize,
};

pub fn isMathWhitespace(ch: u8) bool {
    return ch == ' ' or ch == '\n' or ch == '\t' or ch == '\r';
}

/// The tokens of a math string as MM0 reads them (`specs/mm0.md`): split
/// on whitespace, after each left delimiter and before each right one.
pub const MathTokenCursor = struct {
    src: []const u8,
    pos: usize = 0,
    left_delims: [256]bool,
    right_delims: [256]bool,

    pub fn next(self: *MathTokenCursor) ?Token {
        while (self.pos < self.src.len and
            isMathWhitespace(self.src[self.pos]))
        {
            self.pos += 1;
        }
        if (self.pos >= self.src.len) return null;

        const start = self.pos;
        while (self.pos < self.src.len) {
            const ch = self.src[self.pos];
            self.pos += 1;
            if (self.left_delims[ch]) break;
            if (self.pos >= self.src.len) break;
            const next_ch = self.src[self.pos];
            if (isMathWhitespace(next_ch) or self.right_delims[next_ch]) {
                break;
            }
        }
        return .{
            .text = self.src[start..self.pos],
            .start = start,
            .end = self.pos,
        };
    }
};
