//! Token-level mutation of source text, driven by a `Smith`.
//!
//! Text splits into runs of whitespace and non-whitespace, so an edit moves
//! whole tokens and keeps the layout. Raw byte flips almost never get past
//! the lexer; token edits keep most of the file well formed and push the
//! damage into the parser and checker. Edits come at three sizes: a token,
//! a line, and a unit (an `.mm0` statement, which ends in `;`, or an `.auf`
//! block, which ends at a blank line).
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

/// Pairs an edit can wrap around a run of tokens, so brackets stay balanced.
const brackets = [_][2][]const u8{
    .{ "(", ")" },
    .{ "[", "]" },
    .{ "$ ", " $" },
    .{ "{", "}" },
};

/// At most this many edits per mutation.
pub const max_edits = 16;

const Op = enum(u8) {
    delete,
    duplicate,
    swap,
    insert_token,
    insert_dictionary,
    byte,
    wrap,
    delete_line,
    duplicate_line,
    move_line,
    delete_unit,
    duplicate_unit,
    move_unit,
};

const Unit = enum { line, unit };

/// `text` with up to `max_edits` Smith-chosen edits applied. Inserted
/// tokens come from `text`, from `other` (the other file of the pair, so
/// proofs can name what the spec declares), or from `dictionary`. The
/// caller owns the result.
pub fn mutate(gpa: std.mem.Allocator, smith: *Smith, text: []const u8, other: []const u8) ![]u8 {
    var tokens: std.ArrayList([]const u8) = .fromOwnedSlice(try tokenize(gpa, text));
    defer tokens.deinit(gpa);
    const pool = try tokenize(gpa, other);
    defer gpa.free(pool);
    const own = try gpa.dupe([]const u8, tokens.items);
    defer gpa.free(own);
    // Bytes of edited tokens; `tokens` borrows them until the concat.
    var edited: std.ArrayList([]u8) = .empty;
    defer {
        for (edited.items) |bytes| gpa.free(bytes);
        edited.deinit(gpa);
    }

    var edits: usize = 0;
    while (edits < max_edits and tokens.items.len != 0 and !smith.eos()) : (edits += 1) {
        const len = tokens.items.len;
        const at = smith.index(len);
        switch (smith.value(Op)) {
            .delete => {
                const n = @min(smith.valueRangeAtMost(u8, 1, 8), len - at);
                tokens.replaceRangeAssumeCapacity(at, n, &.{});
            },
            .duplicate => {
                const n = @min(smith.valueRangeAtMost(u8, 1, 8), len - at);
                try duplicateRange(gpa, &tokens, at, at + n, at);
            },
            .swap => {
                const other_at = smith.index(len);
                std.mem.swap([]const u8, &tokens.items[at], &tokens.items[other_at]);
            },
            .insert_token => {
                const from_other = pool.len != 0 and smith.value(bool);
                const source = if (from_other) pool else own;
                try tokens.insert(gpa, at, source[smith.index(source.len)]);
            },
            .insert_dictionary => try tokens.insert(gpa, at, dictionary[smith.index(dictionary.len)]),
            .byte => {
                const bytes = try gpa.dupe(u8, tokens.items[at]);
                errdefer gpa.free(bytes);
                try edited.append(gpa, bytes);
                bytes[smith.index(bytes.len)] = smith.value(u8);
                tokens.items[at] = bytes;
            },
            .wrap => {
                const pair = brackets[smith.index(brackets.len)];
                const end = @min(at + smith.valueRangeAtMost(u8, 1, 16), len);
                try tokens.insert(gpa, end, pair[1]);
                try tokens.insert(gpa, at, pair[0]);
            },
            inline .delete_line, .delete_unit => |op| {
                const range = unitAround(tokens.items, at, if (op == .delete_line) .line else .unit);
                tokens.replaceRangeAssumeCapacity(range[0], range[1] - range[0], &.{});
            },
            inline .duplicate_line, .duplicate_unit => |op| {
                const range = unitAround(tokens.items, at, if (op == .duplicate_line) .line else .unit);
                try duplicateRange(gpa, &tokens, range[0], range[1], range[1]);
            },
            inline .move_line, .move_unit => |op| {
                const kind: Unit = if (op == .move_line) .line else .unit;
                const range = unitAround(tokens.items, at, kind);
                const moved = try gpa.dupe([]const u8, tokens.items[range[0]..range[1]]);
                defer gpa.free(moved);
                tokens.replaceRangeAssumeCapacity(range[0], moved.len, &.{});
                // Land at the start of another unit of the same kind.
                const dest = if (tokens.items.len == 0)
                    0
                else
                    unitAround(tokens.items, smith.index(tokens.items.len), kind)[0];
                try tokens.insertSlice(gpa, dest, moved);
            },
        }
    }
    return std.mem.concat(gpa, u8, tokens.items);
}

/// Insert a copy of `tokens[start..end]` at `dest`.
fn duplicateRange(
    gpa: std.mem.Allocator,
    tokens: *std.ArrayList([]const u8),
    start: usize,
    end: usize,
    dest: usize,
) !void {
    const copy = try gpa.dupe([]const u8, tokens.items[start..end]);
    defer gpa.free(copy);
    try tokens.insertSlice(gpa, dest, copy);
}

/// The token range `[start, end)` of the line or unit holding `at`. A
/// range ends after its closing token: the newline run for a line; for a
/// unit, a token ending in `;` or a run holding a blank line.
fn unitAround(tokens: []const []const u8, at: usize, kind: Unit) [2]usize {
    var start = at;
    while (start > 0 and !endsUnit(tokens[start - 1], kind)) start -= 1;
    var end = at;
    while (end < tokens.len) {
        end += 1;
        if (endsUnit(tokens[end - 1], kind)) break;
    }
    return .{ start, end };
}

fn endsUnit(token: []const u8, kind: Unit) bool {
    const space = std.ascii.isWhitespace(token[0]);
    return switch (kind) {
        .line => space and std.mem.indexOfScalar(u8, token, '\n') != null,
        .unit => if (space)
            std.mem.count(u8, token, "\n") >= 2
        else
            token[token.len - 1] == ';',
    };
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
    const out = try mutate(std.testing.allocator, &smith, "sort s;", "");
    defer std.testing.allocator.free(out);
    try std.testing.expectEqualStrings("sort s;", out);
}

test "lines and units cover the tokens around an index" {
    const text = "sort s; term t: s;\n\nl1: $ a $ by h\nl2: $ b $ by h\n";
    const tokens = try tokenize(std.testing.allocator, text);
    defer std.testing.allocator.free(tokens);
    const at = find(tokens, "term");
    const unit = unitAround(tokens, at, .unit);
    const unit_text = try std.mem.concat(std.testing.allocator, u8, tokens[unit[0]..unit[1]]);
    defer std.testing.allocator.free(unit_text);
    try std.testing.expectEqualStrings(" term t: s;", unit_text);

    const l2 = find(tokens, "l2:");
    const line = unitAround(tokens, l2 + 2, .line);
    const line_text = try std.mem.concat(std.testing.allocator, u8, tokens[line[0]..line[1]]);
    defer std.testing.allocator.free(line_text);
    try std.testing.expectEqualStrings("l2: $ b $ by h\n", line_text);
}

fn find(tokens: []const []const u8, needle: []const u8) usize {
    for (tokens, 0..) |token, index| {
        if (std.mem.eql(u8, token, needle)) return index;
    }
    unreachable;
}
