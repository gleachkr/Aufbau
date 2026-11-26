const std = @import("std");
const proof_script = @import("../proof_script.zig");
const Types = @import("types.zig");

pub const SourceRange = Types.SourceRange;

pub const NavigationSymbol = struct {
    source_range: SourceRange,
    target_range: ?SourceRange,
    markdown: []const u8,
    /// A notation token standing for its term: a use of the term, but not
    /// of its name, so a rename leaves it alone.
    via_notation: bool = false,
};

pub const ProofBlockInfo = struct {
    /// The parsed block; it lacks the lines of a body the parser knew.
    source: proof_script.ProofBlock,
    global_available_before: ?usize = null,
    decl_index: ?usize = null,
    hyp_count: usize = 0,
    hyp_count_known: bool = false,

    /// Whether `offset` is in the block's body: past the header, at or
    /// before its last line.
    pub fn bodyContains(self: ProofBlockInfo, offset: usize) bool {
        return offset >= self.source.header_span.end and offset < self.source.body_end;
    }
};

/// What indexing one block's proof lines yields.
pub const ProofBody = struct {
    symbols: []const NavigationSymbol = &.{},
    lines: []const ProofLineDecl = &.{},
    applications: []const ProofApplicationInfo = &.{},
};

pub const ProofRuleDecl = struct {
    name: []const u8,
    decl_index: usize,
    available_start: usize,
    sort_text: []const u8,
};

pub const ProofLineDecl = struct {
    name: []const u8,
    name_range: SourceRange,
    markdown: []const u8,
    line_start: usize,
    sort_text: []const u8,
};

pub const ProofApplicationInfo = struct {
    block_index: usize,
    rule_name: []const u8,
    rule_span: SourceRange,
    binding_list_span: ?SourceRange = null,
    refs_span: ?SourceRange = null,
    span: SourceRange,
    use_start: usize,
    line_start: usize,
};

pub const RuleResolution = struct {
    decl_index: usize,
    available: bool,
};

/// What each name stands for, and what it stood for at each proof block: a
/// block sees only what was declared before it.
pub const NameTable = struct {
    latest: std.StringHashMapUnmanaged(Entry) = .empty,
    /// Entries replaced by a later one with the same name.
    replaced: std.ArrayListUnmanaged(Entry) = .empty,

    pub const Entry = struct {
        index: usize,
        /// The first block to see the entry.
        from_block: usize,
        /// The entry this one replaced, in `replaced`.
        previous: ?usize = null,
    };

    pub fn put(
        self: *NameTable,
        allocator: std.mem.Allocator,
        name: []const u8,
        index: usize,
        from_block: usize,
    ) !void {
        const slot = try self.latest.getOrPut(allocator, name);
        var entry: Entry = .{ .index = index, .from_block = from_block };
        if (slot.found_existing) {
            // No block sees an entry replaced before the next one.
            if (slot.value_ptr.from_block == from_block) {
                entry.previous = slot.value_ptr.previous;
            } else {
                entry.previous = self.replaced.items.len;
                try self.replaced.append(allocator, slot.value_ptr.*);
            }
        }
        slot.value_ptr.* = entry;
    }

    /// The latest declaration of `name`.
    pub fn get(self: *const NameTable, name: []const u8) ?usize {
        return if (self.latest.get(name)) |entry| entry.index else null;
    }

    pub fn contains(self: *const NameTable, name: []const u8) bool {
        return self.latest.contains(name);
    }

    /// The declaration of `name` that block `block_index` sees.
    pub fn seenBy(self: *const NameTable, name: []const u8, block_index: usize) ?usize {
        var entry = self.latest.get(name) orelse return null;
        while (entry.from_block > block_index) {
            entry = self.replaced.items[entry.previous orelse return null];
        }
        return entry.index;
    }
};

/// Project an indexed declaration's hypothesis table into the name slice
/// `proof_script.resolveHypRef` takes, so hover and completion resolve
/// refs through the same resolver the compiler applies to a written proof
/// instead of re-implementing the rule. Caller owns the result.
pub fn hypNamesFromHypotheses(
    allocator: std.mem.Allocator,
    hypotheses: []const Types.HypothesisDecl,
) ![]const ?[]const u8 {
    const names = try allocator.alloc(?[]const u8, hypotheses.len);
    for (hypotheses, names) |item, *slot| slot.* = item.name;
    return names;
}
