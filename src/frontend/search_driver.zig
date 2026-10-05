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
//!
//! With `Options.retries`, a missed `auto?` whose report advises larger
//! limits is rewritten with them and searched again. The rewrite stays in
//! the working text only when that finds a proof, which then replaces it.

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

/// A search of a marker that missed and was searched again with larger
/// limits.
pub const Round = struct {
    /// `missed` or `cut_short`.
    outcome: Outcome,
    cost: Cost,
    /// The marker with the larger limits, which the next round searched.
    retry: []const u8,
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
    /// The rounds before the last, when the marker was searched again
    /// (`Options.retries`). The other fields describe the last round.
    rounds: []const Round = &.{},
};

/// Names the markers a run searches: those of one theorem, or of one of
/// its lines.
pub const Only = struct {
    theorem: []const u8,
    /// Every line of the theorem when null.
    label: ?[]const u8 = null,

    fn selects(self: Only, placeholder: Search.SearchPlaceholder) bool {
        if (!std.mem.eql(u8, self.theorem, placeholder.theorem)) return false;
        const label = self.label orelse return true;
        return std.mem.eql(u8, label, placeholder.label);
    }
};

pub const Options = struct {
    /// Search only these markers. The others stay as written, and the
    /// analysis admits them like a miss.
    only: ?Only = null,
    /// How many times a missed `auto?` is searched again with the larger
    /// limits its retry advice gives.
    retries: usize = 0,
    /// `auto?` parameters for every marker that does not set them itself.
    params: []const ProofScript.SearchParam = &.{},
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
    options: Options,
) !Result {
    var result_arena = std.heap.ArenaAllocator.init(allocator);
    errdefer result_arena.deinit();
    const out = result_arena.allocator();

    // A marker's own parameters are applied over these by the search.
    var marker_options = search_options;
    Search.tunables.applySearchParams(&marker_options.generate, options.params);

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
        cursor = next.span.start + 1;
        if (options.only) |only| {
            if (!only.selects(next)) continue;
        }

        const unsearched: Marker = .{
            .kind = next.kind,
            .span = .{
                .start = shift(next.span.start, growth),
                .end = shift(next.span.end, growth),
            },
            .theorem = try out.dupe(u8, next.theorem),
            .label = try out.dupe(u8, next.label),
            .outcome = .missed,
        };

        // After a retry, the working text with the marker rewritten, and
        // how much longer that made it.
        var retried: ?[]u8 = null;
        defer if (retried) |text| allocator.free(text);
        var retry_growth: isize = 0;
        var rounds = std.ArrayListUnmanaged(Round){};
        var offset = next.span.start;
        var marker = unsearched;
        const proof_span = while (true) {
            marker = unsearched;
            const spans = try searchMarker(
                allocator,
                out,
                mm0_src,
                retried orelse working,
                offset,
                marker_options,
                &marker,
            );
            const retry_span = spans.retry orelse break spans.proof;
            if (rounds.items.len == options.retries) break spans.proof;
            try rounds.append(out, .{
                .outcome = marker.outcome,
                .cost = marker.cost,
                .retry = marker.retry.?,
            });
            const text = try splice(
                allocator,
                retried orelse working,
                retry_span,
                marker.retry.?,
            );
            if (retried) |old| allocator.free(old);
            retried = text;
            retry_growth += growthOf(retry_span, marker.retry.?);
            offset = retry_span.start;
        };
        marker.rounds = try rounds.toOwnedSlice(out);

        if (proof_span) |span| {
            const proof = marker.suggestions[0];
            // A retry rewrote the marker inside `span`, so the growth it
            // made lies before the span's end but not its start.
            marker.edit = .{
                .span = .{
                    .start = shift(span.start, growth),
                    .end = shift(span.end, growth + retry_growth),
                },
                .text = proof,
            };
            // A `conversion?` proof replaces its whole line with a chain
            // of lines ending in it, so `at` would name the chain's first
            // line; its goal is concrete, though, so it has no holes to
            // report.
            if (next.kind != .conversion) {
                try found_at.append(allocator, .{
                    .marker = markers.items.len,
                    .at = span.start,
                    .growth = growth,
                });
            }
            const text = try splice(allocator, retried orelse working, span, proof);
            allocator.free(working);
            working = text;
            growth += retry_growth + growthOf(span, proof);
            cursor = span.start + proof.len;
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

/// Where a search's results go in the text it searched.
const Spans = struct {
    /// The span the proof replaces, when one was found to put in place.
    proof: ?Span = null,
    /// The span a retry replaces, when the marker missed and larger
    /// limits might find a proof.
    retry: ?Span = null,
};

/// Search the marker at `offset` in `text` and record the result in
/// `marker`.
fn searchMarker(
    allocator: std.mem.Allocator,
    out: std.mem.Allocator,
    mm0_src: []const u8,
    text: []const u8,
    offset: usize,
    base_options: Search.SourceSuggestionOptions,
    marker: *Marker,
) !Spans {
    var counters = Search.SearchCounters{ .collect = true };
    var options = base_options;
    options.counters = &counters;
    var search = Search.suggestionsAtSourceOffset(
        allocator,
        mm0_src,
        text,
        offset,
        options,
    ) catch |err| {
        if (err == error.OutOfMemory) return err;
        marker.outcome = .failed;
        marker.failure = err;
        return .{};
    };
    defer search.deinit();

    if (search.target_span == null) {
        marker.outcome = .not_searched;
        if (search.blocked_by) |span| {
            marker.blocked_by = try out.dupe(u8, text[span.start..span.end]);
        }
        return .{};
    }
    marker.outcome = switch (search.status) {
        .found => if (marker.kind == .apply) .candidates else .found,
        .miss => .missed,
        .budget_exhausted => .cut_short,
    };
    marker.cost = try costOf(out, &counters);
    if (search.status_detail) |detail| {
        // `cost.rules` lists the most-tried rules, so drop the sentence
        // that names them.
        const kept = Search.statusDetailWithoutRules(detail);
        if (kept.len != 0) marker.detail = try out.dupe(u8, kept);
    }
    var spans: Spans = .{};
    if (search.retry) |retry| {
        marker.retry = try out.dupe(u8, retry.replacement);
        spans.retry = retry.replace_span;
    }
    if (search.items.len != 0) {
        const suggestions = try out.alloc([]const u8, search.items.len);
        for (search.items, suggestions) |item, *suggestion| {
            suggestion.* = try out.dupe(u8, item.replacement);
        }
        marker.suggestions = suggestions;
        if (marker.kind != .apply) spans.proof = search.items[0].replace_span;
    }
    return spans;
}

/// `text` with `span` replaced by `replacement`.
fn splice(
    allocator: std.mem.Allocator,
    text: []const u8,
    span: Span,
    replacement: []const u8,
) ![]u8 {
    return std.mem.concat(allocator, u8, &.{
        text[0..span.start],
        replacement,
        text[span.end..],
    });
}

fn growthOf(span: Span, replacement: []const u8) isize {
    return @as(isize, @intCast(replacement.len)) -
        @as(isize, @intCast(span.end - span.start));
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
