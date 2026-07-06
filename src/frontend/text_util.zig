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
