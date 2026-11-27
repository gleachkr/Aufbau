//! What the language server keeps of a root between messages: its joined
//! unit and what has been found in it.

const std = @import("std");
const lsp = @import("lsp");
const mm0 = @import("mm0");
const protocol = @import("./protocol.zig");
const lsp_texts = @import("../lsp_texts.zig");
const unit_mod = @import("./unit.zig");

const types = lsp.types.flat;
const ArenaAllocator = mm0.ArenaAllocator;
const FileTexts = lsp_texts.FileTexts;
const HoleInferenceSink = mm0.CompilerSupport.Context.HoleInferenceSink;
const LspIndex = mm0.Frontend.LspIndex;
const Search = mm0.CompilerSupport.Search;
const Unit = unit_mod.Unit;
const UnitFile = unit_mod.UnitFile;
const UnitSide = unit_mod.UnitSide;

/// The unit joined for a root and what has been found in it: the index
/// requests read, the holes its last analysis inferred, and what the
/// searches in it found. It stands while every file its join looked up is
/// as the join found it (`Handler.currentUnit`). All it holds is of those
/// texts and goes with it, so none of it is compared with them again.
pub const UnitState = struct {
    allocator: std.mem.Allocator,
    /// Backs `unit` (its joined texts and file records) and the names
    /// below.
    arena: ArenaAllocator,
    unit: Unit,
    /// Where `unit` holds its file texts from.
    texts: *FileTexts,
    /// The root `.mm0` URI: the key it is kept under.
    mm0_uri: []const u8,
    /// The root proof file's URI, whether or not there is such a file.
    proof_uri: []const u8,
    /// The index over the joined texts, built when a request first reads
    /// it.
    snapshot: ?LspIndex.Snapshot = null,
    /// The holes the last analysis found.
    holes: ?HoleInferenceSink = null,
    /// What the last search found.
    search: ?SearchResults = null,
    /// The outcome of each search run, by the marker it ran for.
    outcomes: std.ArrayListUnmanaged(PlaceholderOutcome) = .empty,

    pub fn destroy(self: *UnitState) void {
        const allocator = self.allocator;
        // The snapshot may index a root's own text, when nothing is joined
        // to it.
        if (self.snapshot) |*snapshot| snapshot.deinit();
        if (self.holes) |*holes| holes.deinit();
        if (self.search) |*search| search.deinit(allocator);
        for (self.outcomes.items) |outcome| allocator.free(outcome.detail);
        self.outcomes.deinit(allocator);
        self.unit.release(self.texts);
        var arena = self.arena;
        arena.deinit();
        allocator.destroy(self);
    }

    pub fn lookedUp(self: *const UnitState, uri: []const u8, path: ?[]const u8) bool {
        for (self.unit.lookups) |lookup| {
            if (std.mem.eql(u8, lookup.state.uri, uri)) return true;
            if (path) |changed| if (std.mem.eql(u8, lookup.path, changed)) return true;
        }
        return false;
    }

    /// Keep `holes` (owned from here on) as what the last analysis found.
    pub fn keepHoles(self: *UnitState, holes: HoleInferenceSink) void {
        if (self.holes) |*old| old.deinit();
        self.holes = holes;
    }

    /// Keep copies of `suggestions`, what a search for the marker at
    /// `target_span` found, in place of the last search's. The copies stay
    /// until the next search or the unit goes.
    pub fn keepSearch(
        self: *UnitState,
        target_span: Search.Span,
        suggestions: []const Search.SourceSuggestion,
    ) ![]const Search.SourceSuggestion {
        const allocator = self.allocator;
        const owned = try allocator.alloc(Search.SourceSuggestion, suggestions.len);
        var filled: usize = 0;
        errdefer {
            for (owned[0..filled]) |suggestion| {
                allocator.free(suggestion.title);
                allocator.free(suggestion.replacement);
            }
            allocator.free(owned);
        }
        for (suggestions, 0..) |suggestion, index| {
            const title = try allocator.dupe(u8, suggestion.title);
            errdefer allocator.free(title);
            owned[index] = .{
                .title = title,
                .replacement = try allocator.dupe(u8, suggestion.replacement),
                .replace_span = suggestion.replace_span,
                .cursor = suggestion.cursor,
            };
            filled = index + 1;
        }
        if (self.search) |*old| old.deinit(allocator);
        self.search = .{ .target_span = target_span, .suggestions = owned };
        return owned;
    }

    /// Record how the search for the marker at `target_span` ended, in
    /// place of what an earlier search for it recorded.
    pub fn recordOutcome(
        self: *UnitState,
        target_span: Search.Span,
        status: Search.SearchStatus,
        detail: []const u8,
    ) !void {
        const allocator = self.allocator;
        const outcome: PlaceholderOutcome = .{
            .target_span = target_span,
            .status = status,
            .detail = try allocator.dupe(u8, detail),
        };
        errdefer allocator.free(outcome.detail);
        for (self.outcomes.items) |*existing| {
            if (existing.target_span.start == target_span.start and
                existing.target_span.end == target_span.end)
            {
                allocator.free(existing.detail);
                existing.* = outcome;
                return;
            }
        }
        try self.outcomes.append(allocator, outcome);
    }
};

/// A navigation request's view of its unit: the index over the joined
/// texts plus which file of the unit the request document is.
pub const NavigationSnapshot = struct {
    state: *UnitState,
    snapshot: *LspIndex.Snapshot,
    unit: *const Unit,
    document: LspIndex.DocumentId,
    file_index: usize,

    pub fn side(self: NavigationSnapshot) *const UnitSide {
        return self.unit.side(self.document).?;
    }

    pub fn file(self: NavigationSnapshot) UnitFile {
        return self.side().files[self.file_index];
    }

    /// The joined offset of an editor position in the request document,
    /// or null when it sits inside an import/include statement.
    pub fn joinedPosition(
        self: NavigationSnapshot,
        position: types.Position,
        encoding: lsp.offsets.Encoding,
    ) ?usize {
        const offset = protocol.offsets.positionToIndex(
            self.file().text,
            position,
            encoding,
        );
        return self.side().joinedOffset(self.file_index, offset);
    }

    /// The runs of the joined text that come from the request document.
    pub fn fileRanges(
        self: NavigationSnapshot,
        arena: std.mem.Allocator,
    ) ![]const LspIndex.SourceRange {
        var ranges = std.ArrayListUnmanaged(LspIndex.SourceRange).empty;
        for (self.side().joined.map.segments) |segment| {
            if (segment.file_index != self.file_index) continue;
            try ranges.append(arena, .{
                .document = self.document,
                .start = segment.joined_start,
                .end = segment.joined_start + segment.len,
            });
        }
        return ranges.items;
    }
};

// Proof-search results (`exact?`/`auto?`/`conversion?` code-action suggestions) are
// expensive to compute and editors fire `textDocument/codeAction` repeatedly
// around the same proof step (lightbulb, quick-fix menu, cursor settle/drift).
// A unit keeps its last search's; they serve every cursor offset that
// resolves to the same placeholder (the search's `target_span`), so cursor
// movement within a step still hits.
pub const SearchResults = struct {
    // The placeholder span (in the joined proof text) these suggestions
    // resolve to: a lookup hits only when the requested offset falls inside
    // it (inclusive), so every offset within one proof step reuses this
    // result.
    target_span: Search.Span,
    // Owned copies. An empty slice is a kept "no suggestions" result, which
    // is the most expensive search to repeat.
    suggestions: []Search.SourceSuggestion,

    pub fn matchesOffset(self: SearchResults, offset: usize) bool {
        return offset >= self.target_span.start and offset <= self.target_span.end;
    }

    pub fn deinit(self: *SearchResults, allocator: std.mem.Allocator) void {
        for (self.suggestions) |suggestion| {
            allocator.free(suggestion.title);
            allocator.free(suggestion.replacement);
        }
        allocator.free(self.suggestions);
        self.* = undefined;
    }
};

// The recorded outcome of one placeholder's search, backing that placeholder's
// status diagnostic (info on success, error on failure). Placeholders with no
// recorded outcome publish as a "not yet searched" warning. A unit gathers
// them across its placeholders (`UnitState.outcomes`), so an edit to any of
// its files returns every one to that warning.
pub const PlaceholderOutcome = struct {
    // The search's catchment span (`SourceSuggestions.target_span`, in the
    // joined proof text): the whole proof line for a top-level placeholder,
    // the nested application for an inline one. A placeholder is matched to
    // its outcome by span containment.
    target_span: Search.Span,
    status: Search.SearchStatus,
    // Owned by the unit's allocator. The first suggestion's replacement text
    // on success, empty otherwise.
    detail: []const u8,
};

// A placeholder is matched to a recorded outcome by containment in the
// outcome's catchment span (equal spans for a nested placeholder, the
// placeholder within its whole proof line for a top-level one).
pub fn outcomeForPlaceholder(
    outcomes: []const PlaceholderOutcome,
    span: Search.Span,
) ?*const PlaceholderOutcome {
    for (outcomes) |*outcome| {
        if (span.start >= outcome.target_span.start and
            span.end <= outcome.target_span.end)
        {
            return outcome;
        }
    }
    return null;
}
