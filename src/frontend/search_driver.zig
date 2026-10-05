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

/// A replacement in the proof text the run was given.
pub const Edit = struct {
    span: Span,
    text: []const u8,
};

pub const RuleTally = struct {
    name: []const u8,
    attempts: usize,
    accepted: usize,
    rejected: usize,
};

/// What a marker's search cost.
pub const Cost = struct {
    /// The weighted work ticks of `auto?` generation
    /// (`Search.weightedTicks`), which the per-call budget charges. Unlike
    /// wall time they repeat from run to run.
    ticks: u64 = 0,
    /// Rule applications validated.
    candidates: usize = 0,
    wall_ns: u64 = 0,
    /// The generation cell that found the proof, or the last one started
    /// on a miss: its depth and its 1-based phase (`Search.phaseName`).
    /// Both 0 when generation did not run.
    depth: usize = 0,
    phase: usize = 0,
    /// The rules with the most validation attempts, most first.
    rules: []const RuleTally = &.{},
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
    /// When found: the proof put in place, as an edit.
    edit: ?Edit = null,
    /// When found: the line's assertion with its holes filled, as an edit.
    /// Null when the line has no holes, or the filled assertion does not
    /// print with source names.
    filled_assertion: ?Edit = null,
    /// After a miss: why, and which limits cut it short.
    detail: ?[]const u8 = null,
    cost: Cost = .{},
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

/// How many of the most-tried rules `Cost.rules` lists.
const max_rules = 5;

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
    // The found markers whose lines may have holes: where each proof went
    // in the working text, and the growth before it.
    var found_at = std.ArrayListUnmanaged(FoundAt){};
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

        var counters = Search.SearchCounters{ .collect = true };
        var options = search_options;
        options.counters = &counters;
        var search = Search.suggestionsAtSourceOffset(
            allocator,
            mm0_src,
            working,
            next.span.start,
            options,
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
        marker.cost = try costOf(out, &counters);
        if (search.status_detail) |detail| {
            // `cost.rules` lists the most-tried rules, so drop the
            // sentence that names them.
            const kept = Search.statusDetailWithoutRules(detail);
            if (kept.len != 0) marker.detail = try out.dupe(u8, kept);
        }
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
            marker.edit = .{
                .span = .{
                    .start = shift(item.replace_span.start, growth),
                    .end = shift(item.replace_span.end, growth),
                },
                .text = marker.suggestions[0],
            };
            // A `conversion?` proof replaces its whole line with a chain
            // of lines ending in it, so `at` would name the chain's first
            // line; its goal is concrete, though, so it has no holes to
            // report.
            if (next.kind != .conversion) {
                try found_at.append(allocator, .{
                    .marker = markers.items.len,
                    .at = item.replace_span.start,
                    .growth = growth,
                });
            }
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

const FoundAt = struct {
    marker: usize,
    /// Where the proof went in the working text.
    at: usize,
    /// The growth of the working text before it, which also maps the
    /// rest of its line before `at` back to the text the run was given.
    growth: isize,
};

fn costOf(out: std.mem.Allocator, counters: *const Search.SearchCounters) !Cost {
    const tallies = counters.rule_attempt_diagnostics[0..counters.rule_attempt_diagnostics_len];
    var order_buf: [counters.rule_attempt_diagnostics.len]usize = undefined;
    const order = order_buf[0..tallies.len];
    for (order, 0..) |*index, i| index.* = i;
    std.mem.sort(usize, order, tallies, struct {
        fn moreAttempts(
            context: []const Search.RuleAttemptDiagnostic,
            a: usize,
            b: usize,
        ) bool {
            return context[a].attempts > context[b].attempts;
        }
    }.moreAttempts);
    const rules = try out.alloc(RuleTally, @min(order.len, max_rules));
    for (rules, order[0..rules.len]) |*rule, index| {
        const tally = &tallies[index];
        rule.* = .{
            .name = try out.dupe(u8, tally.rule_name.slice()),
            .attempts = tally.attempts,
            .accepted = tally.accepted,
            .rejected = tally.rejected,
        };
    }
    const generated = counters.gen_last_phase != 0;
    return .{
        .ticks = if (generated) Search.weightedTicks(
            counters.gen_work_ticks,
            counters.gen_sym_ticks,
            counters.gen_walk_ticks,
            counters.full_try_candidate_calls,
        ) else 0,
        .candidates = counters.full_try_candidate_calls,
        .wall_ns = counters.cold_setup_ns + counters.warm_search_ns,
        .depth = counters.gen_last_depth,
        .phase = counters.gen_last_phase,
        .rules = rules,
    };
}

/// Give each found marker the holes on its line and its filled
/// assertion, read off one analysis of the finished text.
fn fillHoleValues(
    allocator: std.mem.Allocator,
    out: std.mem.Allocator,
    mm0_src: []const u8,
    text: []const u8,
    markers: []Marker,
    found_at: []const FoundAt,
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
        const marker = &markers[entry.marker];
        marker.holes = try holes.toOwnedSlice(out);
        for (sink.assertions.items) |filled| {
            if (filled.line.start != line.start) continue;
            marker.filled_assertion = .{
                .span = .{
                    .start = shift(filled.assertion.start, entry.growth),
                    .end = shift(filled.assertion.end, entry.growth),
                },
                .text = try std.fmt.allocPrint(out, "$ {s} $", .{filled.text}),
            };
            break;
        }
    }
}
