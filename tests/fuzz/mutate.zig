//! Token-level mutation of source text, driven by a `Smith`.
//!
//! Text splits into runs of whitespace and non-whitespace, so an edit moves
//! whole tokens and keeps the layout. Raw byte flips almost never get past
//! the lexer; token edits keep most of the file well formed and push the
//! damage into the parser and checker.
const std = @import("std");
const Smith = std.testing.Smith;

/// Tokens worth inserting anywhere: punctuation, keywords, proof markers,
/// annotations, and a few shapes that stress nesting.
pub const dictionary = [_][]const u8{
    "$",           "(",        ")",       "[",        "]",         ";",           ":",
    ",",           "_",        "auto?",   "exact?",   "apply?",    "conversion?", "by",
    "sorry!",      "theorem",  "axiom",   "term",     "def",       "sort",        "pure",
    "strict",      "provable", "free",    "bound",    "infixl",    "infixr",      "prefix",
    "notation",    "prec",     "max",     "=",        ">",         "@relation",   "@rewrite",
    "@acui",       "@congr",   "@view",   "@recover", "@abstract", "@fresh",      "@auto",
    "@conversion", "@compute", "@hole",   "\n",       " ",         "(((((((((",   ")))))))))",
    "--",          "--|",      "include", "import",   "local",     "#",
};

/// At most this many edits per mutation.
pub const max_edits = 16;

const Op = enum(u8) { delete, duplicate, swap, insert_token, insert_dictionary, byte };

/// `text` with up to `max_edits` Smith-chosen token edits applied.
/// The caller owns the result.
pub fn mutate(gpa: std.mem.Allocator, smith: *Smith, text: []const u8) ![]u8 {
    var tokens: std.ArrayList([]const u8) = .fromOwnedSlice(try tokenize(gpa, text));
    defer tokens.deinit(gpa);
    // The original tokens, so an insert can borrow from anywhere in the text.
    const pool = try gpa.dupe([]const u8, tokens.items);
    defer gpa.free(pool);
    // Bytes of edited tokens; `tokens` borrows them until the concat.
    var edited: std.ArrayList([]u8) = .empty;
    defer {
        for (edited.items) |bytes| gpa.free(bytes);
        edited.deinit(gpa);
    }

    var edits: usize = 0;
    while (edits < max_edits and tokens.items.len != 0 and !smith.eos()) : (edits += 1) {
        const at = smith.index(tokens.items.len);
        switch (smith.value(Op)) {
            .delete => {
                const n = @min(smith.valueRangeAtMost(u8, 1, 8), tokens.items.len - at);
                tokens.replaceRangeAssumeCapacity(at, n, &.{});
            },
            .duplicate => {
                const n = @min(smith.valueRangeAtMost(u8, 1, 8), tokens.items.len - at);
                const copy = try gpa.dupe([]const u8, tokens.items[at .. at + n]);
                defer gpa.free(copy);
                try tokens.insertSlice(gpa, at, copy);
            },
            .swap => {
                const other = smith.index(tokens.items.len);
                std.mem.swap([]const u8, &tokens.items[at], &tokens.items[other]);
            },
            .insert_token => try tokens.insert(gpa, at, pool[smith.index(pool.len)]),
            .insert_dictionary => try tokens.insert(gpa, at, dictionary[smith.index(dictionary.len)]),
            .byte => {
                const bytes = try gpa.dupe(u8, tokens.items[at]);
                errdefer gpa.free(bytes);
                try edited.append(gpa, bytes);
                bytes[smith.index(bytes.len)] = smith.value(u8);
                tokens.items[at] = bytes;
            },
        }
    }
    return std.mem.concat(gpa, u8, tokens.items);
}

/// Alternating runs of whitespace and non-whitespace; never an empty run.
fn tokenize(gpa: std.mem.Allocator, text: []const u8) ![][]const u8 {
    var out: std.ArrayList([]const u8) = .empty;
    errdefer out.deinit(gpa);
    var start: usize = 0;
    while (start < text.len) {
        const space = std.ascii.isWhitespace(text[start]);
        var end = start + 1;
        while (end < text.len and std.ascii.isWhitespace(text[end]) == space) end += 1;
        try out.append(gpa, text[start..end]);
        start = end;
    }
    return out.toOwnedSlice(gpa);
}

test "tokenize keeps every byte" {
    const text = "theorem a:  $ x $;\n";
    const tokens = try tokenize(std.testing.allocator, text);
    defer std.testing.allocator.free(tokens);
    const joined = try std.mem.concat(std.testing.allocator, u8, tokens);
    defer std.testing.allocator.free(joined);
    try std.testing.expectEqualStrings(text, joined);
    for (tokens) |token| try std.testing.expect(token.len != 0);
}

test "no edits leaves the text alone" {
    // An exhausted Smith reports end of stream at once.
    var smith: Smith = .{ .in = "" };
    const out = try mutate(std.testing.allocator, &smith, "sort s;");
    defer std.testing.allocator.free(out);
    try std.testing.expectEqualStrings("sort s;", out);
}
