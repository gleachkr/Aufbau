//! Byte offset <-> LSP position conversion that tolerates any bytes.
//!
//! lsp_kit's `offsets` assumes valid UTF-8 and offsets on character
//! boundaries; either assumption failing indexes past the slice. Neither
//! holds here: compiler spans may cover one byte of a multi-byte character,
//! and documents read from disk are arbitrary bytes. Each byte that does not
//! start a well-formed sequence counts as one U+FFFD, as clients decode it.
const std = @import("std");
const lsp = @import("lsp");

const types = lsp.types;
pub const Encoding = lsp.offsets.Encoding;
pub const Loc = lsp.offsets.Loc;

/// The character starting at `index`: its byte length and its length in
/// `encoding` code units.
const Char = struct { bytes: usize, units: usize };

fn charAt(text: []const u8, index: usize, encoding: Encoding) Char {
    const replacement: Char = .{ .bytes = 1, .units = 1 };
    const len = std.unicode.utf8ByteSequenceLength(text[index]) catch
        return replacement;
    if (index + len > text.len) return replacement;
    const codepoint = std.unicode.utf8Decode(text[index..][0..len]) catch
        return replacement;
    return .{ .bytes = len, .units = switch (encoding) {
        .@"utf-8" => len,
        .@"utf-16" => if (codepoint < 0x10000) 1 else 2,
        .@"utf-32" => 1,
    } };
}

/// The position of `index`; an index inside a character resolves to the
/// character's start, or its end when `round_up`.
pub fn indexToPosition(
    text: []const u8,
    index: usize,
    encoding: Encoding,
    round_up: bool,
) types.Position {
    const target = @min(index, text.len);
    const line_start = if (std.mem.lastIndexOfScalar(u8, text[0..target], '\n')) |nl|
        nl + 1
    else
        0;
    var i = line_start;
    var character: usize = 0;
    while (i < target) {
        const char = charAt(text, i, encoding);
        if (i + char.bytes > target and !round_up) break;
        character += char.units;
        i += char.bytes;
    }
    return .{
        .line = @intCast(std.mem.count(u8, text[0..line_start], "\n")),
        .character = @intCast(character),
    };
}

/// The byte index of `position`, clamped to its line and to the text.
pub fn positionToIndex(
    text: []const u8,
    position: types.Position,
    encoding: Encoding,
) usize {
    var i: usize = 0;
    var line: u32 = 0;
    while (line < position.line) : (line += 1) {
        const nl = std.mem.indexOfScalarPos(u8, text, i, '\n') orelse
            return text.len;
        i = nl + 1;
    }
    var character: usize = 0;
    while (i < text.len and text[i] != '\n' and character < position.character) {
        const char = charAt(text, i, encoding);
        character += char.units;
        i += char.bytes;
    }
    return i;
}

/// The smallest range covering every character `loc` touches.
pub fn locToRange(text: []const u8, loc: Loc, encoding: Encoding) types.Range {
    return .{
        .start = indexToPosition(text, loc.start, encoding, false),
        .end = indexToPosition(text, loc.end, encoding, true),
    };
}

pub fn rangeToLoc(text: []const u8, range: types.Range, encoding: Encoding) Loc {
    return .{
        .start = positionToIndex(text, range.start, encoding),
        .end = positionToIndex(text, range.end, encoding),
    };
}
