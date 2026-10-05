//! `abc search`: run every search marker of a proof unit in checking order.
//!
//! Each marker is searched like an editor code action
//! (`suggestionsAtSourceOffset`) on a working copy of the proof text. A
//! found proof replaces its marker in the working text, so later markers
//! and lines see it proven; a missed marker stays as written, and the
//! analysis admits it like `sorry!` when its assertion is concrete.
//! `apply?` lists candidate rules rather than a proof, so its result is
//! reported and never substituted. A marker after a line of its block that
//! does not check is not searched: there is no context to search in.

const std = @import("std");
const Search = @import("./compiler/search.zig");
const ProofScript = @import("./proof_script.zig");
const CompilerModule = @import("./compiler.zig");

const Span = ProofScript.Span;

pub const HoleValue = struct {
    name: []const u8,
    value: []const u8,
};

pub const Outcome = enum {
    /// A proof was found and put in the marker's place.
    found,
    /// `apply?` listed candidate rules; none is put in place.
    candidates,
    /// The search ran to the end without a proof.
    missed,
    /// A limit cut the search short; a proof may still exist.
    cut_short,
    /// Not searched, because an earlier line of the block does not check.
    not_searched,
    /// The search itself failed (`failure`).
    failed,
};

pub const Marker = struct {
    kind: Search.SearchPlaceholder.Kind,
    /// The marker's span in the proof text the run was given.
    span: Span,
    theorem: []const u8,
    label: []const u8,
    outcome: Outcome,
    /// The proof put in the marker's place, or every candidate rule of an
    /// `apply?`. Empty otherwise.
    suggestions: []const []const u8 = &.{},
    /// After a miss that larger limits might fix: the marker rewritten
    /// with those limits.
    retry: ?[]const u8 = null,
    /// The holes on a found marker's line, with the values its proof gives
    /// them.
    holes: []const HoleValue = &.{},
    /// When not searched: the label of the earlier line that does not
    /// check.
    blocked_by: ?[]const u8 = null,
    /// When the search failed: its error.
    failure: ?anyerror = null,
};

pub const Result = struct {
    arena: std.heap.ArenaAllocator,
    markers: []const Marker,
    /// The proof text with every found proof in place.
    text: []const u8,

    pub fn deinit(self: *Result) void {
        self.arena.deinit();
        self.* = undefined;
    }
};

const search_options: Search.SourceSuggestionOptions = .{
    // The editor's settings: one proof for `exact?`/`auto?`/`conversion?`,
    // the full candidate list for `apply?`, and the miss detail behind the
    // retry advice.
    .exact_result_limit = 1,
    .generate = .{ .enabled = true },
    .status_detail = true,
};

pub fn run(
    allocator: std.mem.Allocator,
    mm0_src: []const u8,
    proof_src: []const u8,
) !Result {
    var result_arena = std.heap.ArenaAllocator.init(allocator);
    errdefer result_arena.deinit();
    const out = result_arena.allocator();

    var markers = std.ArrayListUnmanaged(Marker){};
    // Working-text offsets of the found markers whose lines may have holes.
    var found_at = std.ArrayListUnmanaged(struct { marker: usize, at: usize }){};
    defer found_at.deinit(allocator);

    var working = try allocator.dupe(u8, proof_src);
    defer allocator.free(working);
    // Every substitution lies before `cursor`, and the next marker after
    // it, so the marker's offset in the original text is its working
    // offset less the growth so far.
    var cursor: usize = 0;
    var growth: isize = 0;
    while (true) {
        var scan_arena = std.heap.ArenaAllocator.init(allocator);
        defer scan_arena.deinit();
        const placeholders = try Search.searchPlaceholders(
            scan_arena.allocator(),
            working,
        );
        const next = for (placeholders) |placeholder| {
            if (placeholder.span.start >= cursor) break placeholder;
        } else break;

        var marker: Marker = .{
            .kind = next.kind,
            .span = .{
                .start = shift(next.span.start, growth),
                .end = shift(next.span.end, growth),
            },
            .theorem = try out.dupe(u8, next.theorem),
            .label = try out.dupe(u8, next.label),
            .outcome = .missed,
        };
        cursor = next.span.start + 1;

        var search = Search.suggestionsAtSourceOffset(
            allocator,
            mm0_src,
            working,
            next.span.start,
            search_options,
        ) catch |err| {
            if (err == error.OutOfMemory) return err;
            marker.outcome = .failed;
            marker.failure = err;
            try markers.append(out, marker);
            continue;
        };
        defer search.deinit();

        if (search.target_span == null) {
            marker.outcome = .not_searched;
            if (search.blocked_by) |span| {
                marker.blocked_by = try out.dupe(u8, working[span.start..span.end]);
            }
            try markers.append(out, marker);
            continue;
        }
        marker.outcome = switch (search.status) {
            .found => if (next.kind == .apply) .candidates else .found,
            .miss => .missed,
            .budget_exhausted => .cut_short,
        };
        if (search.retry) |retry| {
            marker.retry = try out.dupe(u8, retry.replacement);
        }
        if (search.items.len != 0) {
            const suggestions = try out.alloc([]const u8, search.items.len);
            for (search.items, suggestions) |item, *text| {
                text.* = try out.dupe(u8, item.replacement);
            }
            marker.suggestions = suggestions;
        }
        if (search.items.len != 0 and next.kind != .apply) {
            const item = search.items[0];
            const spliced = try std.mem.concat(allocator, u8, &.{
                working[0..item.replace_span.start],
                item.replacement,
                working[item.replace_span.end..],
            });
            allocator.free(working);
            working = spliced;
            growth += @as(isize, @intCast(item.replacement.len)) -
                @as(isize, @intCast(item.replace_span.end - item.replace_span.start));
            cursor = item.replace_span.start + item.replacement.len;
            // A `conversion?` proof replaces its whole line with a chain
            // of lines ending in it, so `at` would name the chain's first
            // line; its goal is concrete, though, so it has no holes to
            // report.
            if (next.kind != .conversion) {
                try found_at.append(allocator, .{
                    .marker = markers.items.len,
                    .at = item.replace_span.start,
                });
            }
        }
        try markers.append(out, marker);
    }

    if (found_at.items.len != 0 and
        std.mem.indexOf(u8, mm0_src, "@hole") != null)
    {
        try fillHoleValues(
            allocator,
            out,
            mm0_src,
            working,
            markers.items,
            found_at.items,
        );
    }

    return .{
        .arena = result_arena,
        .markers = try markers.toOwnedSlice(out),
        .text = try out.dupe(u8, working),
    };
}

fn shift(offset: usize, growth: isize) usize {
    return @intCast(@as(isize, @intCast(offset)) - growth);
}

/// Give each found marker the holes on its line, read off one analysis of
/// the finished text.
fn fillHoleValues(
    allocator: std.mem.Allocator,
    out: std.mem.Allocator,
    mm0_src: []const u8,
    text: []const u8,
    markers: []Marker,
    found_at: anytype,
) !void {
    var sink = CompilerModule.HoleInferenceSink{ .allocator = allocator };
    defer sink.deinit();
    var compiler = CompilerModule.Compiler.initWithProof(
        allocator,
        mm0_src,
        text,
    );
    compiler.allow_search_placeholders = true;
    compiler.hole_inference_sink = &sink;
    compiler.analyze() catch |err| {
        if (err == error.OutOfMemory) return err;
    };
    if (sink.items.items.len == 0) return;

    var parse_arena = std.heap.ArenaAllocator.init(allocator);
    defer parse_arena.deinit();
    var lines = std.ArrayListUnmanaged(Span){};
    var parser = ProofScript.Parser.initLenient(parse_arena.allocator(), text);
    while (parser.nextBlockSkippingLocalItems() catch null) |block| {
        for (block.lines) |line| {
            try lines.append(parse_arena.allocator(), line.span);
        }
    }

    for (found_at) |entry| {
        const line = for (lines.items) |span| {
            if (entry.at >= span.start and entry.at < span.end) break span;
        } else continue;
        var holes = std.ArrayListUnmanaged(HoleValue){};
        for (sink.items.items) |hole| {
            if (hole.span.start < line.start or hole.span.end > line.end) {
                continue;
            }
            const name = text[hole.span.start..hole.span.end];
            const seen = for (holes.items) |listed| {
                if (std.mem.eql(u8, listed.name, name)) break true;
            } else false;
            if (seen) continue;
            try holes.append(out, .{
                .name = try out.dupe(u8, name),
                .value = try out.dupe(u8, hole.expression),
            });
        }
        markers[entry.marker].holes = try holes.toOwnedSlice(out);
    }
}
