//! Finding the uses of a declaration. A use in a proof body shows only once
//! the body is indexed, so a search indexes every body whose block's text
//! spells the declaration, one at a time in reused memory.
const std = @import("std");
const ArenaAllocator = @import("../arena_allocator.zig").ArenaAllocator;

const Snapshot = @import("index.zig").Snapshot;
const indexBody = @import("builder_body.zig").indexBody;
const model = @import("model.zig");
const source = @import("source.zig");
const Types = @import("types.zig");

const NavigationSymbol = model.NavigationSymbol;
const ProofBody = model.ProofBody;
const SourceRange = Types.SourceRange;

pub const Occurrence = struct {
    range: SourceRange,
    /// See `NavigationSymbol.via_notation`.
    via_notation: bool,
};

/// Every symbol that targets `declaration`, the declaration's own included,
/// in no particular order and perhaps repeated. With `within`, only those in
/// one of its ranges.
pub fn occurrences(
    snapshot: *Snapshot,
    allocator: std.mem.Allocator,
    declaration: SourceRange,
    within: ?[]const SourceRange,
) std.mem.Allocator.Error![]const Occurrence {
    var found = std.ArrayListUnmanaged(Occurrence).empty;
    errdefer found.deinit(allocator);
    if (snapshot.blockWithBodyAt(declaration.document, declaration.start)) |block_index| {
        // A line: only its own block can refer to it.
        const body = try snapshot.bodyOf(block_index);
        try collect(allocator, &found, body.symbols, declaration, within);
    } else {
        try collect(allocator, &found, snapshot.symbols, declaration, within);
        const spellings = try spellingsOf(snapshot, allocator, declaration);
        defer allocator.free(spellings);
        var bodies = BodyWalk.init(snapshot, allocator, spellings, within);
        defer bodies.deinit();
        while (try bodies.next()) |body| {
            try collect(allocator, &found, body.symbols, declaration, within);
        }
    }
    return try found.toOwnedSlice(allocator);
}

fn collect(
    allocator: std.mem.Allocator,
    found: *std.ArrayListUnmanaged(Occurrence),
    symbols: []const NavigationSymbol,
    declaration: SourceRange,
    within: ?[]const SourceRange,
) !void {
    for (symbols) |symbol| {
        const target = symbol.target_range orelse continue;
        if (!target.eql(declaration)) continue;
        if (within) |ranges| {
            if (!symbol.source_range.overlapsAny(ranges)) continue;
        }
        try found.append(allocator, .{
            .range = symbol.source_range,
            .via_notation = symbol.via_notation,
        });
    }
}

/// Sort `ranges` by document and position, and drop the repeats.
pub fn sortedUnique(ranges: *std.ArrayListUnmanaged(SourceRange)) void {
    std.mem.sortUnstable(SourceRange, ranges.items, {}, SourceRange.lessThan);
    var kept: usize = 0;
    for (ranges.items) |range| {
        if (kept != 0 and ranges.items[kept - 1].eql(range)) continue;
        ranges.items[kept] = range;
        kept += 1;
    }
    ranges.shrinkRetainingCapacity(kept);
}

/// Words for `declaration`: the text of every block whose body refers to it
/// spells one of them. A body names what it refers to, except that a binder
/// or hypothesis may go by its position. But those belong to a theorem or
/// lemma that the block proves or applies, so it spells that name.
fn spellingsOf(
    snapshot: *const Snapshot,
    allocator: std.mem.Allocator,
    declaration: SourceRange,
) ![]const []const u8 {
    var words = std.ArrayListUnmanaged([]const u8).empty;
    errdefer words.deinit(allocator);
    for (snapshot.declarations, 0..) |decl, decl_index| {
        if (decl.name_range.eql(declaration)) {
            try words.append(allocator, decl.name);
            for (snapshot.notations) |notation| {
                if (notation.decl_index != decl_index) continue;
                try words.append(allocator, notation.token);
            }
        } else if (decl.declaresBinder(declaration) or
            decl.declaresHypothesis(declaration) or
            decl.statesHypothesis(declaration))
        {
            try words.append(allocator, decl.name);
        }
    }
    return try words.toOwnedSlice(allocator);
}

/// The bodies of the blocks whose text spells one of `words`, in source
/// order. With `within`, only of the blocks that reach into it.
pub const BodyWalk = struct {
    snapshot: *const Snapshot,
    words: []const []const u8,
    within: ?[]const SourceRange,
    arena: ArenaAllocator,
    next_block: usize = 0,

    pub fn init(
        snapshot: *const Snapshot,
        allocator: std.mem.Allocator,
        words: []const []const u8,
        within: ?[]const SourceRange,
    ) BodyWalk {
        return .{
            .snapshot = snapshot,
            .words = words,
            .within = within,
            .arena = ArenaAllocator.init(allocator),
        };
    }

    pub fn deinit(self: *BodyWalk) void {
        self.arena.deinit();
    }

    /// Valid until the next call.
    pub fn next(self: *BodyWalk) std.mem.Allocator.Error!?ProofBody {
        while (self.next_block < self.snapshot.proof_blocks.len) {
            const block_index = self.next_block;
            self.next_block += 1;
            if (!self.reaches(block_index)) continue;
            _ = self.arena.reset(.retain_capacity);
            return try indexBody(self.arena.allocator(), self.snapshot, block_index);
        }
        return null;
    }

    fn reaches(self: *const BodyWalk, block_index: usize) bool {
        const block = self.snapshot.proof_blocks[block_index].source;
        const start = block.header_span.start;
        const end = block.body_end;
        if (self.within) |ranges| {
            const block_range: SourceRange = .{ .document = .proof, .start = start, .end = end };
            if (!block_range.overlapsAny(ranges)) return false;
        }
        const text = self.snapshot.proof_text.?[start..end];
        for (self.words) |word| {
            if (self.spells(text, word)) return true;
        }
        return false;
    }

    /// Whether `word` is a token somewhere in `text`. Where a token starts
    /// or ends depends on the delimiters; beyond them, all that is sure is
    /// that a token does not stop between two identifier characters.
    fn spells(self: *const BodyWalk, text: []const u8, word: []const u8) bool {
        if (word.len == 0) return false;
        var pos: usize = 0;
        while (std.mem.indexOfPos(u8, text, pos, word)) |at| : (pos = at + 1) {
            const end = at + word.len;
            if (at > 0 and self.joined(text[at - 1], word[0])) continue;
            if (end < text.len and self.joined(word[word.len - 1], text[end])) continue;
            return true;
        }
        return false;
    }

    fn joined(self: *const BodyWalk, left: u8, right: u8) bool {
        return source.isIdentChar(left) and source.isIdentChar(right) and
            !self.snapshot.left_delims[left] and !self.snapshot.right_delims[right];
    }
};
