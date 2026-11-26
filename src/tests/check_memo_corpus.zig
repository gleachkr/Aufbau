//! Differential guard for the proof-block check memo (`CheckMemo`): over
//! the whole `tests/proof_cases` corpus, an analysis served from a warm memo
//! must produce exactly what a cold analysis produces — every diagnostic,
//! span, note, sink entry and error — under the edits an editor makes:
//! nothing (all hits), a body edit that only shifts later blocks, a body
//! edit that flips an outcome and its undo, comments that shift every
//! `.mm0` position (all hits), and a theory edit every check can see (no
//! hits). A run with the unknown-value sink must bypass the memo.

const std = @import("std");
const mm0 = @import("../lib.zig");

const Compiler = mm0.Compiler;
const CheckMemo = mm0.CheckMemo;
const Context = mm0.CompilerSupport.Context;
const HoleInferenceSink = Context.HoleInferenceSink;
const ProofScript = mm0.ProofScript;
const scanToStatementEnd = @import("../trusted/parse.zig").scanToStatementEnd;

/// Everything an analysis reports, rendered canonically.
fn analyzeDump(
    allocator: std.mem.Allocator,
    mm0_text: []const u8,
    proof_text: []const u8,
    memo: ?*CheckMemo,
    unknowns_sink: bool,
) ![]u8 {
    return analyzeDumpStopping(allocator, mm0_text, proof_text, memo, unknowns_sink, null);
}

fn analyzeDumpStopping(
    allocator: std.mem.Allocator,
    mm0_text: []const u8,
    proof_text: []const u8,
    memo: ?*CheckMemo,
    unknowns_sink: bool,
    interrupt: ?mm0.AnalysisInterrupt,
) ![]u8 {
    return analyzeDumpWith(allocator, mm0_text, proof_text, .{
        .memo = memo,
        .unknowns_sink = unknowns_sink,
        .interrupt = interrupt,
    });
}

const DumpOptions = struct {
    memo: ?*CheckMemo = null,
    unknowns_sink: bool = false,
    interrupt: ?mm0.AnalysisInterrupt = null,
    scope: ?*mm0.CheckScope = null,
    /// Dump only what lies in this scope's spans of the proof text, and
    /// what lies in the theory: no `last` or `dropped` line.
    only: ?*const mm0.CheckScope = null,

    fn dumps(self: DumpOptions, source: mm0.CompilerDiagnosticSource, span: ?ProofScript.Span) bool {
        const only = self.only orelse return true;
        if (source != .proof) return true;
        const actual = span orelse return true;
        return only.covers(actual.start);
    }
};

fn analyzeDumpWith(
    allocator: std.mem.Allocator,
    mm0_text: []const u8,
    proof_text: []const u8,
    options: DumpOptions,
) ![]u8 {
    var arena_state = std.heap.ArenaAllocator.init(allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();

    var holes = mm0.CompilerSupport.Context.HoleInferenceSink{ .allocator = arena };
    var unknowns = mm0.UnknownValueSink.init(arena);
    var compiler = Compiler.initWithProof(arena, mm0_text, proof_text);
    compiler.allow_search_placeholders = true;
    compiler.hole_inference_sink = &holes;
    if (options.unknowns_sink) compiler.unknown_value_sink = &unknowns;
    compiler.check_memo = options.memo;
    compiler.interrupt = options.interrupt;
    compiler.check_scope = options.scope;

    var out: std.Io.Writer.Allocating = .init(arena);
    const writer = &out.writer;
    if (compiler.analyze()) |_| {
        try writer.writeAll("result: ok\n");
    } else |err| {
        if (err == error.AnalysisInterrupted) return err;
        try writer.print("result: {s}\n", .{@errorName(err)});
    }
    for (compiler.primaryDiagnostics()) |diag| {
        if (!options.dumps(diag.source, diag.span)) continue;
        try writer.writeAll("primary ");
        try dumpDiagnostic(writer, diag);
    }
    for (compiler.warningDiagnostics()) |diag| {
        if (!options.dumps(diag.source, diag.span)) continue;
        try writer.writeAll("warning ");
        try dumpDiagnostic(writer, diag);
    }
    if (options.only == null) {
        if (compiler.diagnostics.last_diagnostic) |diag| {
            try writer.writeAll("last ");
            try dumpDiagnostic(writer, diag);
        }
        try writer.print("dropped {d} {d} {d} {d}\n", .{
            compiler.diagnostics.dropped_primary_diagnostic_count,
            compiler.diagnostics.dropped_mm0_primary_diagnostic_count,
            compiler.diagnostics.dropped_proof_primary_diagnostic_count,
            compiler.diagnostics.dropped_warning_count,
        });
    }
    for (holes.items.items) |hole| {
        if (!options.dumps(.proof, hole.span)) continue;
        try writer.print("hole {d}-{d} {s}\n", .{
            hole.span.start,
            hole.span.end,
            hole.expression,
        });
    }
    for (holes.assertions.items) |filled| {
        if (!options.dumps(.proof, filled.line)) continue;
        try writer.print("filled {d}-{d} {d}-{d} {s}\n", .{
            filled.line.start,
            filled.line.end,
            filled.assertion.start,
            filled.assertion.end,
            filled.text,
        });
    }
    for (unknowns.items.items) |item| {
        try writer.print("unknown {s} {s} {s} {}\n", .{
            item.theorem,
            item.name,
            item.value,
            item.partial,
        });
    }
    return try allocator.dupe(u8, out.written());
}

fn dumpSpan(writer: anytype, span: ?ProofScript.Span) !void {
    if (span) |actual| {
        try writer.print("{d}-{d}", .{ actual.start, actual.end });
    } else {
        try writer.writeAll("none");
    }
}

fn dumpDiagnostic(writer: anytype, diag: mm0.CompilerDiagnostic) !void {
    try writer.print("{s} {s} {s} {s} phase={s} span=", .{
        @tagName(diag.severity),
        @tagName(diag.kind),
        @errorName(diag.err),
        @tagName(diag.source),
        if (diag.phase) |phase| @tagName(phase) else "none",
    });
    try dumpSpan(writer, diag.span);
    try writer.print(" names={?s}/{?s}/{?s}/{?s}/{?s}/{?s} detail={any} msg=", .{
        diag.theorem_name,
        diag.block_name,
        diag.line_label,
        diag.rule_name,
        diag.name,
        diag.expected_name,
        diag.detail,
    });
    try mm0.renderCompilerDiagnostic(writer, diag, " | ");
    for (diag.noteSlice()) |note| {
        try writer.print("\n  note {s} ", .{@tagName(note.source)});
        try dumpSpan(writer, note.span);
        try writer.writeAll(" ");
        try mm0.renderCompilerNoteMessage(writer, note.message);
    }
    for (diag.relatedSlice()) |related| {
        try writer.print("\n  related {s} {s} ", .{
            @tagName(related.label),
            @tagName(related.source),
        });
        try dumpSpan(writer, related.span);
    }
    try writer.writeAll("\n");
}

const Edit = struct {
    /// Replace `[start, end)` of the proof text with `text`.
    start: usize,
    end: usize,
    text: []const u8,
};

fn applyEdit(allocator: std.mem.Allocator, source: []const u8, edit: Edit) ![]u8 {
    var out = std.ArrayListUnmanaged(u8).empty;
    try out.appendSlice(allocator, source[0..edit.start]);
    try out.appendSlice(allocator, edit.text);
    try out.appendSlice(allocator, source[edit.end..]);
    return try out.toOwnedSlice(allocator);
}

/// `mm0_text` with comments and blank lines before its first statement and
/// after each one.
fn spaceOut(allocator: std.mem.Allocator, mm0_text: []const u8) ![]u8 {
    var out = std.ArrayListUnmanaged(u8).empty;
    try out.appendSlice(allocator, "-- a comment; with $\n\n");
    var pos: usize = 0;
    while (pos < mm0_text.len) {
        const start = pos;
        _ = scanToStatementEnd(mm0_text, &pos);
        try out.appendSlice(allocator, mm0_text[start..pos]);
        try out.appendSlice(allocator, "\n-- \"more; of them\n--| and prose\n  ");
    }
    return try out.toOwnedSlice(allocator);
}

const Counts = struct { blocks: usize = 0, hits_seen: bool = false };

const Scenario = struct {
    name: []const u8,
    mm0_text: []const u8,
    proof_text: []const u8,
    /// Also attach the unknown-value sink.
    unknowns_sink: bool = false,
};

/// Cold vs warm must agree; returns the warm dump's hit delta.
fn expectSameAnalysis(
    allocator: std.mem.Allocator,
    memo: *CheckMemo,
    stem: []const u8,
    scenario: Scenario,
) !void {
    const cold = try analyzeDump(allocator, scenario.mm0_text, scenario.proof_text, null, scenario.unknowns_sink);
    defer allocator.free(cold);
    const warm = try analyzeDump(allocator, scenario.mm0_text, scenario.proof_text, memo, scenario.unknowns_sink);
    defer allocator.free(warm);
    if (!std.mem.eql(u8, cold, warm)) {
        std.debug.print(
            "check memo divergence: {s} ({s})\n--- cold ---\n{s}\n--- warm ---\n{s}\n",
            .{ stem, scenario.name, cold, warm },
        );
        return error.CheckMemoDivergence;
    }
}

/// The proof blocks of a proof text, in stream order.
fn proofBlocks(
    allocator: std.mem.Allocator,
    proof_text: []const u8,
) ![]const ProofScript.ProofBlock {
    var blocks = std.ArrayListUnmanaged(ProofScript.ProofBlock).empty;
    var parser = ProofScript.Parser.initLenient(allocator, proof_text);
    while (true) {
        const item = parser.nextItem() catch {
            if (!parser.recoverToNextItemBoundary()) break;
            continue;
        } orelse break;
        switch (item) {
            .block => |block| try blocks.append(allocator, block),
            else => {},
        }
    }
    return try blocks.toOwnedSlice(allocator);
}

fn fixtureStems(allocator: std.mem.Allocator) ![]const []const u8 {
    var stems = std.ArrayListUnmanaged([]const u8).empty;
    const io = std.testing.io;
    var dir = try std.Io.Dir.cwd().openDir(io, "tests/proof_cases", .{ .iterate = true });
    defer dir.close(io);
    var it = dir.iterate();
    while (try it.next(io)) |entry| {
        if (entry.kind != .file) continue;
        if (!std.mem.endsWith(u8, entry.name, ".auf")) continue;
        const stem = entry.name[0 .. entry.name.len - ".auf".len];
        const mm0_name = try std.fmt.allocPrint(allocator, "{s}.mm0", .{stem});
        defer allocator.free(mm0_name);
        dir.access(io, mm0_name, .{}) catch continue;
        try stems.append(allocator, try allocator.dupe(u8, stem));
    }
    std.sort.pdq([]const u8, stems.items, {}, struct {
        fn lessThan(_: void, a: []const u8, b: []const u8) bool {
            return std.mem.lessThan(u8, a, b);
        }
    }.lessThan);
    return try stems.toOwnedSlice(allocator);
}

/// Fail unless the run just made missed at most the edited block and the
/// blocks the memo never records.
fn expectOnlyEditedMissed(
    allocator: std.mem.Allocator,
    memo: *const CheckMemo,
    stem: []const u8,
    scenario: []const u8,
    index: usize,
    block_count: usize,
    block_name: []const u8,
    misses_before: usize,
    unrecordable: usize,
    mm0_text: []const u8,
    proof_text: []const u8,
) !void {
    const misses = memo.misses - misses_before;
    if (misses <= unrecordable + 1) return;
    const dump = try analyzeDump(allocator, mm0_text, proof_text, null, false);
    defer allocator.free(dump);
    std.debug.print(
        "check memo {s} over-miss: {s} block {d}/{d} ({s}): {d} misses, {d} unrecordable\n--- edited analysis ---\n{s}\n--- edited text ---\n{s}\n",
        .{ scenario, stem, index, block_count, block_name, misses, unrecordable, dump, proof_text },
    );
    return error.CheckMemoOverMiss;
}

fn runFixture(
    allocator: std.mem.Allocator,
    memo: *CheckMemo,
    stem: []const u8,
    counts: *Counts,
) !void {
    var arena_state = std.heap.ArenaAllocator.init(allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();

    const mm0_path = try std.fmt.allocPrint(arena, "tests/proof_cases/{s}.mm0", .{stem});
    const proof_path = try std.fmt.allocPrint(arena, "tests/proof_cases/{s}.auf", .{stem});
    var failure: ?mm0.Imports.LoadFailure = null;
    const pair = mm0.Imports.loadPair(std.testing.io, arena, mm0_path, proof_path, &failure) catch return;
    const mm0_text = pair.mm0.text;
    const proof_text = (pair.proof orelse return).text;

    // Cold population, then a verbatim rerun: every block must hit.
    try expectSameAnalysis(allocator, memo, stem, .{
        .name = "populate",
        .mm0_text = mm0_text,
        .proof_text = proof_text,
    });
    const blocks = try proofBlocks(arena, proof_text);
    counts.blocks += blocks.len;
    const hits_before = memo.hits;
    const misses_before = memo.misses;
    try expectSameAnalysis(allocator, memo, stem, .{
        .name = "rerun",
        .mm0_text = mm0_text,
        .proof_text = proof_text,
    });
    if (blocks.len > 0 and memo.hits > hits_before) counts.hits_seen = true;
    // A verbatim rerun of a recordable block never misses; blocks whose
    // output the memo refuses to record (spans outside the block) miss
    // every time. Their count is the floor for every scenario below.
    const unrecordable = memo.misses - misses_before;
    try std.testing.expect(unrecordable <= blocks.len);

    // Body edits on the first, middle and last block.
    const picks = [_]usize{ 0, blocks.len / 2, blocks.len -| 1 };
    for (picks) |index| {
        if (index >= blocks.len) continue;
        const block = blocks[index];
        if (block.lines.len == 0) continue;
        const last = block.lines[block.lines.len - 1];

        // Text after the last line that the block takes in, so that a body
        // whose own text is unchanged no longer ends where it did: one more
        // proof line, and a reference list for a last line without one. The
        // parser must not pass over the body then.
        for ([_][]const u8{ "zz_more: $ x $ by zz_no_such_rule []\n", "[#1]\n" }) |more| {
            try expectSameAnalysis(allocator, memo, stem, .{
                .name = "extend",
                .mm0_text = mm0_text,
                .proof_text = try applyEdit(arena, proof_text, .{
                    .start = block.body_end,
                    .end = block.body_end,
                    .text = more,
                }),
            });
            try expectSameAnalysis(allocator, memo, stem, .{
                .name = "extend undone",
                .mm0_text = mm0_text,
                .proof_text = proof_text,
            });
        }
        // Whitespace inside the body (after the last line's application,
        // before its newline): same outcome, later blocks shift. Only the
        // edited block re-checks; the ones after it replay through
        // relocation.
        {
            const at = last.application.span.end;
            const edited = try applyEdit(arena, proof_text, .{
                .start = at,
                .end = at,
                .text = "  ",
            });
            const misses = memo.misses;
            try expectSameAnalysis(allocator, memo, stem, .{
                .name = "shift",
                .mm0_text = mm0_text,
                .proof_text = edited,
            });
            try expectOnlyEditedMissed(allocator, memo, stem, "shift", index, blocks.len, block.name, misses, unrecordable, mm0_text, edited);
        }
        // A bogus rule on the last line: the outcome flips. Later proofs
        // cannot see an earlier one's outcome (its theorem stays in
        // scope), so again only the edited block re-checks.
        const rule_span = last.application.rule_span;
        const broken = try applyEdit(arena, proof_text, .{
            .start = rule_span.start,
            .end = rule_span.end,
            .text = "zz_no_such_rule",
        });
        const break_misses = memo.misses;
        try expectSameAnalysis(allocator, memo, stem, .{
            .name = "break",
            .mm0_text = mm0_text,
            .proof_text = broken,
        });
        try expectOnlyEditedMissed(allocator, memo, stem, "break", index, blocks.len, block.name, break_misses, unrecordable, mm0_text, broken);
        // Fixed again: the break run kept the entries of every block but
        // the edited one, whose original entry it replaced.
        const fix_misses = memo.misses;
        try expectSameAnalysis(allocator, memo, stem, .{
            .name = "fix",
            .mm0_text = mm0_text,
            .proof_text = proof_text,
        });
        try expectOnlyEditedMissed(allocator, memo, stem, "fix", index, blocks.len, block.name, fix_misses, unrecordable, mm0_text, proof_text);
    }

    // Comments and blank lines between the statements shift every `.mm0`
    // position, and nothing a check sees: no block re-checks.
    {
        const misses = memo.misses;
        const edited = try spaceOut(arena, mm0_text);
        try expectSameAnalysis(allocator, memo, stem, .{
            .name = "theory shift",
            .mm0_text = edited,
            .proof_text = proof_text,
        });
        if (memo.misses - misses > unrecordable) {
            std.debug.print(
                "check memo theory shift: {s}: {d} misses, {d} unrecordable\n{s}\n",
                .{ stem, memo.misses - misses, unrecordable, edited },
            );
            return error.CheckMemoOverMiss;
        }
    }

    // Every check sees a statement before its own, so all re-check. (The
    // memo is shared across fixtures, so the statement names this one: two
    // fixtures with the same theory and proof prefix would otherwise
    // legitimately share entries.)
    {
        const hits = memo.hits;
        try expectSameAnalysis(allocator, memo, stem, .{
            .name = "theory edit",
            .mm0_text = try std.fmt.allocPrint(arena, "sort zz_{s};\n{s}", .{ stem, mm0_text }),
            .proof_text = proof_text,
        });
        try std.testing.expectEqual(hits, memo.hits);
    }

    // Back to the original: the theory-edit run kept only the entries it
    // used, so every block re-checks.
    {
        const hits = memo.hits;
        try expectSameAnalysis(allocator, memo, stem, .{
            .name = "restore",
            .mm0_text = mm0_text,
            .proof_text = proof_text,
        });
        try std.testing.expectEqual(hits, memo.hits);
    }

    // The memo records no values of named unknowns, so a run that collects
    // them checks every block.
    {
        const hits = memo.hits;
        const misses = memo.misses;
        try expectSameAnalysis(allocator, memo, stem, .{
            .name = "unknown-value sink",
            .mm0_text = mm0_text,
            .proof_text = proof_text,
            .unknowns_sink = true,
        });
        try std.testing.expectEqual(hits, memo.hits);
        try std.testing.expectEqual(misses, memo.misses);
    }
}

test "check memo matches cold analysis across the proof-case corpus" {
    const allocator = std.testing.allocator;
    const stems = try fixtureStems(allocator);
    defer {
        for (stems) |stem| allocator.free(stem);
        allocator.free(stems);
    }
    try std.testing.expect(stems.len > 100);

    var memo = CheckMemo.init(allocator);
    defer memo.deinit();

    var counts: Counts = .{};
    for (stems) |stem| {
        try runFixture(allocator, &memo, stem, &counts);
    }
    try std.testing.expect(counts.blocks > 0);
    try std.testing.expect(counts.hits_seen);
}

/// Stops an analysis at each proof the memo newly recorded.
const StopAtNew = struct {
    memo: *const CheckMemo,
    recorded: usize = 0,

    fn stopRequested(context: *anyopaque) bool {
        const self: *StopAtNew = @ptrCast(@alignCast(context));
        const recorded = self.memo.entries.count();
        defer self.recorded = recorded;
        return recorded != self.recorded;
    }
};

test "an analysis stopped at every proof ends as one that ran through" {
    const allocator = std.testing.allocator;
    const stems = try fixtureStems(allocator);
    defer {
        for (stems) |stem| allocator.free(stem);
        allocator.free(stems);
    }
    var all_stops: usize = 0;
    for (stems) |stem| {
        var arena_state = std.heap.ArenaAllocator.init(allocator);
        defer arena_state.deinit();
        const arena = arena_state.allocator();
        const mm0_path = try std.fmt.allocPrint(arena, "tests/proof_cases/{s}.mm0", .{stem});
        const proof_path = try std.fmt.allocPrint(arena, "tests/proof_cases/{s}.auf", .{stem});
        var failure: ?mm0.Imports.LoadFailure = null;
        const pair = mm0.Imports.loadPair(std.testing.io, arena, mm0_path, proof_path, &failure) catch continue;
        const proof_text = (pair.proof orelse continue).text;

        const through = try analyzeDump(arena, pair.mm0.text, proof_text, null, false);
        var memo = CheckMemo.init(allocator);
        defer memo.deinit();
        var stopping: StopAtNew = .{ .memo = &memo };
        var stops: usize = 0;
        const stopped = while (true) {
            break analyzeDumpStopping(arena, pair.mm0.text, proof_text, &memo, false, .{
                .context = &stopping,
                .stopFn = StopAtNew.stopRequested,
            }) catch |err| {
                if (err != error.AnalysisInterrupted) return err;
                stops += 1;
                continue;
            };
        };
        try std.testing.expectEqualStrings(through, stopped);
        // One stop for each proof, and no stopped run dropped one.
        try std.testing.expectEqual(memo.entries.count(), stops);
        all_stops += stops;
    }
    try std.testing.expect(all_stops > 1000);
}

test "an analysis that checks some proofs first ends as one that checked them all" {
    const allocator = std.testing.allocator;
    const stems = try fixtureStems(allocator);
    defer {
        for (stems) |stem| allocator.free(stem);
        allocator.free(stems);
    }
    var all_skipped: usize = 0;
    for (stems) |stem| {
        var arena_state = std.heap.ArenaAllocator.init(allocator);
        defer arena_state.deinit();
        const arena = arena_state.allocator();
        const mm0_path = try std.fmt.allocPrint(arena, "tests/proof_cases/{s}.mm0", .{stem});
        const proof_path = try std.fmt.allocPrint(arena, "tests/proof_cases/{s}.auf", .{stem});
        var failure: ?mm0.Imports.LoadFailure = null;
        const pair = mm0.Imports.loadPair(std.testing.io, arena, mm0_path, proof_path, &failure) catch continue;
        const proof_text = (pair.proof orelse continue).text;

        const through = try analyzeDump(arena, pair.mm0.text, proof_text, null, false);
        var cold = CheckMemo.init(allocator);
        defer cold.deinit();
        _ = try analyzeDump(arena, pair.mm0.text, proof_text, &cold, false);
        // The open file is the second half of the proof text (a root after
        // its includes) or the first (an open library file), split between
        // two blocks as files are.
        const blocks = try proofBlocks(arena, proof_text);
        if (blocks.len < 2) continue;
        const middle = blocks[blocks.len / 2].span.start;
        const halves = [_]ProofScript.Span{
            .{ .start = middle, .end = proof_text.len },
            .{ .start = 0, .end = middle },
        };
        for (halves) |half| {
            var scope: mm0.CheckScope = .{ .spans = &.{half} };
            var memo = CheckMemo.init(allocator);
            defer memo.deinit();
            // What lies in the scope is what checking every proof finds there.
            const first = try analyzeDumpWith(arena, pair.mm0.text, proof_text, .{
                .memo = &memo,
                .scope = &scope,
                .only = &scope,
            });
            const expected = try analyzeDumpWith(arena, pair.mm0.text, proof_text, .{
                .only = &scope,
            });
            try std.testing.expectEqualStrings(expected, first);
            all_skipped += scope.skipped;
            // Then the rest: all of it as if checked at once.
            const rest = try analyzeDump(arena, pair.mm0.text, proof_text, &memo, false);
            try std.testing.expectEqualStrings(through, rest);
            try std.testing.expectEqual(cold.entries.count(), memo.entries.count());
            // And the next first pass replays every proof it leaves out.
            var again: mm0.CheckScope = .{ .spans = &.{half} };
            const replayed = try analyzeDumpWith(arena, pair.mm0.text, proof_text, .{
                .memo = &memo,
                .scope = &again,
                .only = &again,
            });
            try std.testing.expectEqualStrings(expected, replayed);
            try std.testing.expectEqual(@as(usize, 0), again.skipped);
        }
    }
    try std.testing.expect(all_skipped > 1000);
}

fn alwaysStop(_: *anyopaque) bool {
    return true;
}

test "a proof checked alone has the holes an analysis finds in it" {
    const allocator = std.testing.allocator;
    const stems = try fixtureStems(allocator);
    defer {
        for (stems) |stem| allocator.free(stem);
        allocator.free(stems);
    }
    var blocks: usize = 0;
    for (stems) |stem| {
        var arena_state = std.heap.ArenaAllocator.init(allocator);
        defer arena_state.deinit();
        const arena = arena_state.allocator();
        const mm0_path = try std.fmt.allocPrint(arena, "tests/proof_cases/{s}.mm0", .{stem});
        const proof_path = try std.fmt.allocPrint(arena, "tests/proof_cases/{s}.auf", .{stem});
        var failure: ?mm0.Imports.LoadFailure = null;
        const pair = mm0.Imports.loadPair(std.testing.io, arena, mm0_path, proof_path, &failure) catch continue;
        const proof_text = (pair.proof orelse continue).text;

        var found = HoleInferenceSink{ .allocator = arena };
        var compiler = Compiler.initWithProof(allocator, pair.mm0.text, proof_text);
        compiler.allow_search_placeholders = true;
        compiler.hole_inference_sink = &found;
        compiler.analyze() catch {};
        if (found.items.items.len + found.assertions.items.len == 0) continue;

        var items: []const Context.HoleInference = found.items.items;
        var assertions: []const Context.FilledAssertion = found.assertions.items;
        var parser = ProofScript.Parser.initLenient(arena, proof_text);
        while (try parser.nextBlockRecovering()) |block| {
            var item_count: usize = 0;
            while (item_count < items.len and
                items[item_count].span.end <= block.span.end) item_count += 1;
            var fill_count: usize = 0;
            while (fill_count < assertions.len and
                assertions[fill_count].line.end <= block.span.end) fill_count += 1;
            if (item_count + fill_count == 0) continue;
            const alone = try mm0.Frontend.LspIndex.holes.ofBlock(
                arena,
                pair.mm0.text,
                proof_text,
                block,
            );
            try std.testing.expectEqualDeep(items[0..item_count], alone.items.items);
            try std.testing.expectEqualDeep(assertions[0..fill_count], alone.assertions.items);
            items = items[item_count..];
            assertions = assertions[fill_count..];
            blocks += 1;
        }
        try std.testing.expectEqual(0, items.len + assertions.len);
    }
    try std.testing.expect(blocks > 100);
}

test "an analysis that is always stopped checks one proof a run" {
    const allocator = std.testing.allocator;
    const mm0_text =
        \\provable sort wff;
        \\term top: wff;
        \\axiom top_i: $ top $;
        \\theorem first: $ top $;
        \\theorem second: $ top $;
    ;
    const proof_text =
        \\lemma before: $ top $
        \\----
        \\l1: $ top $ by top_i []
        \\
        \\first
        \\----
        \\l1: $ top $ by no_such_rule []
        \\
        \\second
        \\----
        \\l1: $ top $ by top_i []
        \\
    ;
    var memo = CheckMemo.init(allocator);
    defer memo.deinit();
    for (1..4) |proofs| {
        try std.testing.expectError(error.AnalysisInterrupted, analyzeDumpStopping(
            allocator,
            mm0_text,
            proof_text,
            &memo,
            false,
            .{ .context = &memo, .stopFn = alwaysStop },
        ));
        try std.testing.expectEqual(proofs, memo.entries.count());
    }
    const stopped = try analyzeDumpStopping(allocator, mm0_text, proof_text, &memo, false, .{
        .context = &memo,
        .stopFn = alwaysStop,
    });
    defer allocator.free(stopped);
    const through = try analyzeDump(allocator, mm0_text, proof_text, null, false);
    defer allocator.free(through);
    try std.testing.expectEqualStrings(through, stopped);
}

test "an analysis that is always stopped gets past a proof the memo cannot record" {
    const allocator = std.testing.allocator;
    // `first` cites a rule declared after it: its error points into the
    // `.mm0` text, so the memo cannot keep its check.
    const mm0_text =
        \\provable sort wff;
        \\term top: wff;
        \\axiom top_i: $ top $;
        \\theorem first: $ top $;
        \\theorem second: $ top $;
        \\axiom ax_late: $ top $;
    ;
    const proof_text =
        \\first
        \\----
        \\l1: $ top $ by ax_late []
        \\
        \\second
        \\----
        \\l1: $ top $ by top_i []
        \\
    ;
    var memo = CheckMemo.init(allocator);
    defer memo.deinit();
    const always: mm0.AnalysisInterrupt = .{ .context = &memo, .stopFn = alwaysStop };
    // The first run stops after `second`, the one check it could keep.
    try std.testing.expectError(error.AnalysisInterrupted, analyzeDumpStopping(
        allocator,
        mm0_text,
        proof_text,
        &memo,
        false,
        always,
    ));
    try std.testing.expectEqual(@as(usize, 1), memo.entries.count());
    const stopped = try analyzeDumpStopping(allocator, mm0_text, proof_text, &memo, false, always);
    defer allocator.free(stopped);
    const through = try analyzeDump(allocator, mm0_text, proof_text, null, false);
    defer allocator.free(through);
    try std.testing.expectEqualStrings(through, stopped);
}

/// `count` lemmas of `statement`, each justified by `justification`, then
/// `last` (its statement is the same).
fn lemmasThenLast(
    allocator: std.mem.Allocator,
    count: usize,
    statement: []const u8,
    justification: []const u8,
    last_body: []const u8,
) ![]u8 {
    var out: std.Io.Writer.Allocating = .init(allocator);
    defer out.deinit();
    for (0..count) |i| {
        try out.writer.print(
            "lemma e{d}: $ {s} $\n----\nl1: $ {s} $ by {s}\n\n",
            .{ i, statement, statement, justification },
        );
    }
    try out.writer.print("last\n----\n{s}", .{last_body});
    return try out.toOwnedSlice();
}

test "check memo replays a proof checked after the run's diagnostics ran out as a cold check would" {
    const allocator = std.testing.allocator;
    // A long formula, for open goals whose printed goals fill the sink's
    // string storage: a premise's goal is printed, and the sink copies it,
    // unlike text the sources hold.
    var long_buffer: [1203]u8 = undefined;
    for (0..600) |i| @memcpy(long_buffer[2 * i ..][0..2], "~ ");
    @memcpy(long_buffer[1200..], "top");
    const long: []const u8 = &long_buffer;
    var long_mm0_buffer: [1400]u8 = undefined;
    const long_mm0 = try std.fmt.bufPrint(&long_mm0_buffer,
        \\provable sort wff;
        \\term top: wff;
        \\term neg: wff > wff;
        \\prefix neg: $~$ prec 100;
        \\axiom top_i: $ top $;
        \\axiom dn (a: wff): $ a $ > $ ~ a $;
        \\theorem last: $ ~ {s} $;
    , .{long});
    var long_last_buffer: [1300]u8 = undefined;
    const long_last = try std.fmt.bufPrint(&long_last_buffer, "l1: $ ~ {s} $ by dn [?]\n", .{long});
    var long_statement_buffer: [1205]u8 = undefined;
    const long_statement = try std.fmt.bufPrint(&long_statement_buffer, "~ {s}", .{long});
    // How the dump shows a string the sink truncated.
    const truncated = try std.fmt.allocPrint(allocator, "{any}", .{@as([]const u8, "<diagnostic string truncated>")});
    defer allocator.free(truncated);
    const short_mm0 =
        \\provable sort wff;
        \\term top: wff;
        \\axiom top_i: $ top $;
        \\theorem last: $ top $;
    ;
    const short_last = "l1: $ top $ by sorry!\nl2: $ top $ by no_such_rule []\n";
    const Limit = struct {
        name: []const u8,
        mm0: []const u8,
        count: usize,
        statement: []const u8,
        broken: []const u8,
        fixed: []const u8,
        last: []const u8,
        /// Whether the broken text's cold analysis shows `marker`: so the
        /// case reaches the sink limit it is about.
        marker: []const u8,
        marked: bool,
    };
    const limits = [_]Limit{
        // More errors, or more warnings, than the sink keeps.
        .{ .name = "errors", .mm0 = short_mm0, .count = 300, .statement = "top", .broken = "no_such_rule []", .fixed = "top_i []", .last = short_last, .marker = "dropped 0 0 0 0", .marked = false },
        .{ .name = "warnings", .mm0 = short_mm0, .count = 40, .statement = "top", .broken = "sorry!", .fixed = "top_i []", .last = short_last, .marker = "dropped 0 0 0 0", .marked = false },
        // Fewer, but more text than its string storage holds.
        .{ .name = "text", .mm0 = long_mm0, .count = 30, .statement = long_statement, .broken = "dn [?]", .fixed = "sorry!", .last = long_last, .marker = truncated, .marked = true },
    };
    for (limits) |limit| {
        const broken = try lemmasThenLast(allocator, limit.count, limit.statement, limit.broken, limit.last);
        defer allocator.free(broken);
        const fixed = try lemmasThenLast(allocator, limit.count, limit.statement, limit.fixed, limit.last);
        defer allocator.free(fixed);

        const cold_broken = try analyzeDump(allocator, limit.mm0, broken, null, false);
        defer allocator.free(cold_broken);
        const marked = std.mem.find(u8, cold_broken, limit.marker) != null;
        if (marked != limit.marked) {
            std.debug.print("case {s} misses its limit:\n{s}\n", .{ limit.name, cold_broken });
            return error.TestUnexpectedResult;
        }
        const cold_fixed = try analyzeDump(allocator, limit.mm0, fixed, null, false);
        defer allocator.free(cold_fixed);
        try std.testing.expect(std.mem.find(u8, cold_fixed, "dropped 0 0 0 0") != null);
        try std.testing.expect(std.mem.find(u8, cold_fixed, truncated) == null);

        var memo = CheckMemo.init(allocator);
        defer memo.deinit();
        const first = try analyzeDump(allocator, limit.mm0, broken, &memo, false);
        defer allocator.free(first);
        try std.testing.expectEqualStrings(cold_broken, first);
        // Every proof was kept, `last` too.
        const misses = memo.misses;
        const again = try analyzeDump(allocator, limit.mm0, broken, &memo, false);
        defer allocator.free(again);
        try std.testing.expectEqualStrings(cold_broken, again);
        try std.testing.expectEqual(misses, memo.misses);
        // With the lemmas fixed, `last` is replayed into a sink with room.
        const after_fix = try analyzeDump(allocator, limit.mm0, fixed, &memo, false);
        defer allocator.free(after_fix);
        try std.testing.expectEqualStrings(cold_fixed, after_fix);
        try std.testing.expectEqual(misses + limit.count, memo.misses);
    }
}

test "check memo keeps what a stopped run checked while another root's run ends" {
    const allocator = std.testing.allocator;
    const mm0_text =
        \\provable sort wff;
        \\term top: wff;
        \\axiom top_i: $ top $;
        \\theorem first: $ top $;
        \\theorem second: $ top $;
    ;
    const proof_text =
        \\first
        \\-----
        \\l1: $ top $ by top_i []
        \\
        \\second
        \\------
        \\l1: $ top $ by top_i []
        \\
    ;
    const edited_text =
        \\first
        \\-----
        \\l2: $ top $ by top_i []
        \\
        \\second
        \\------
        \\l1: $ top $ by top_i []
        \\
    ;
    const other_mm0_text =
        \\provable sort wff;
        \\term bot: wff;
        \\axiom bot_i: $ bot $;
        \\theorem main: $ bot $;
    ;
    const other_proof_text =
        \\main
        \\----
        \\l1: $ bot $ by bot_i []
        \\
    ;
    var memo = CheckMemo.init(allocator);
    defer memo.deinit();
    const always: mm0.AnalysisInterrupt = .{ .context = &memo, .stopFn = alwaysStop };
    const runOther = struct {
        fn run(m: *CheckMemo) !void {
            m.root = 2;
            allocator.free(try analyzeDump(allocator, other_mm0_text, other_proof_text, m, false));
            m.root = 1;
        }
    }.run;

    // The first run is stopped, then one that replays the first proof.
    memo.root = 1;
    for (1..3) |proofs| {
        try std.testing.expectError(error.AnalysisInterrupted, analyzeDumpStopping(
            allocator,
            mm0_text,
            proof_text,
            &memo,
            false,
            always,
        ));
        try runOther(&memo);
        try std.testing.expectEqual(proofs + 1, memo.entries.count());
    }
    allocator.free(try analyzeDump(allocator, mm0_text, proof_text, &memo, false));
    try std.testing.expectEqual(3, memo.entries.count());

    // Stopped after an edit, it keeps the edited proof and the old one, which
    // goes when a run ends.
    try std.testing.expectError(error.AnalysisInterrupted, analyzeDumpStopping(
        allocator,
        mm0_text,
        edited_text,
        &memo,
        false,
        always,
    ));
    try runOther(&memo);
    try std.testing.expectEqual(4, memo.entries.count());
    const misses = memo.misses;
    allocator.free(try analyzeDump(allocator, mm0_text, edited_text, &memo, false));
    try std.testing.expectEqual(misses, memo.misses);
    try std.testing.expectEqual(3, memo.entries.count());
}

test "check memo keeps what each root's latest run used" {
    const allocator = std.testing.allocator;
    var memo = CheckMemo.init(allocator);
    defer memo.deinit();

    const mm0_text =
        \\provable sort wff;
        \\term top: wff;
        \\axiom ax_top: $ top $;
        \\theorem t1: $ top $;
        \\theorem t2: $ top $;
        \\theorem t3: $ top $;
    ;
    const proof_text =
        \\t1
        \\---
        \\p: $ top $ by ax_top []
        \\
        \\t2
        \\---
        \\p: $ top $ by ax_top []
        \\
        \\t3
        \\---
        \\p: $ top $ by ax_top []
    ;
    // t3's body changes; its outcome does not.
    const edited_text =
        \\t1
        \\---
        \\p: $ top $ by ax_top []
        \\
        \\t2
        \\---
        \\p: $ top $ by ax_top []
        \\
        \\t3
        \\---
        \\q: $ top $ by ax_top []
    ;
    const other_mm0_text =
        \\provable sort wff;
        \\term bot: wff;
        \\axiom ax_bot: $ bot $;
        \\theorem u1: $ bot $;
    ;
    const other_proof_text =
        \\u1
        \\---
        \\p: $ bot $ by ax_bot []
    ;

    memo.root = 1;
    const first = try analyzeDump(allocator, mm0_text, proof_text, &memo, false);
    allocator.free(first);
    try std.testing.expectEqual(@as(usize, 3), memo.entries.count());

    // Another root's run keeps the first root's entries.
    memo.root = 2;
    const other = try analyzeDump(allocator, other_mm0_text, other_proof_text, &memo, false);
    allocator.free(other);
    try std.testing.expectEqual(@as(usize, 4), memo.entries.count());

    // The edit replaces t3's entry: the old one is no longer used.
    memo.root = 1;
    const misses = memo.misses;
    const edited = try analyzeDump(allocator, mm0_text, edited_text, &memo, false);
    allocator.free(edited);
    try std.testing.expectEqual(misses + 1, memo.misses);
    try std.testing.expectEqual(@as(usize, 4), memo.entries.count());

    // Both roots replay everything they last used.
    const hits = memo.hits;
    const again = try analyzeDump(allocator, mm0_text, edited_text, &memo, false);
    allocator.free(again);
    memo.root = 2;
    const other_again = try analyzeDump(allocator, other_mm0_text, other_proof_text, &memo, false);
    allocator.free(other_again);
    try std.testing.expectEqual(hits + 4, memo.hits);
    try std.testing.expectEqual(misses + 1, memo.misses);
}

/// The blocks of `proof_text`, parsed past the bodies `memo` knows.
fn knownBlocks(
    arena: std.mem.Allocator,
    memo: *CheckMemo,
    proof_text: []const u8,
) ![]const ProofScript.ProofBlock {
    var blocks = std.ArrayListUnmanaged(ProofScript.ProofBlock).empty;
    var parser = ProofScript.Parser.initLenient(arena, proof_text);
    parser.known_bodies = memo.knownBodies();
    while (try parser.nextBlockRecovering()) |block| try blocks.append(arena, block);
    return blocks.items;
}

test "the parser passes over the bodies the check memo knows" {
    const allocator = std.testing.allocator;
    var arena_state = std.heap.ArenaAllocator.init(allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    var memo = CheckMemo.init(allocator);
    defer memo.deinit();

    const mm0_text =
        \\provable sort wff;
        \\term top: wff;
        \\axiom ax_top: $ top $;
        \\theorem t1: $ top $;
        \\theorem t2: $ top $;
        \\theorem t3: $ top $;
        \\
    ;
    const t1 = "t1\n---\np: $ top $ by ax_top []\nq: $ top $ by ax_top\n";
    const t2 = "t2\n---\np: $ top $ by ax_top []\n";
    // A line that does not parse may read into whatever follows the body:
    // here `p`'s bindings run on through `q`, and end in the next `$`.
    const t3 = "t3\n---\np: $ top $ by ax_top (a := $ x\nq: $ , b := $ by ax_top []\n";
    const proof_text = t1 ++ "\n-- t2 is next\n" ++ t2 ++ "\n" ++ t3;

    allocator.free(try analyzeDump(allocator, mm0_text, proof_text, &memo, false));
    const plain = try proofBlocks(arena, proof_text);
    const known = try knownBlocks(arena, &memo, proof_text);
    try std.testing.expectEqual(plain.len, known.len);
    for (plain, known, [_]bool{ true, true, false }) |expected, block, passed| {
        try std.testing.expectEqual(passed, block.known_body != null);
        try std.testing.expectEqualDeep(
            expected,
            try block.withLines(arena, proof_text),
        );
    }

    // The same body is passed over wherever it lies, but not changed, and
    // not where more text belongs to it.
    const cases = [_]struct { text: []const u8, passed: bool }{
        .{ .text = "-- moved\n" ++ t1 ++ "-- | not a doc\n" ++ t2, .passed = true },
        .{ .text = t1 ++ "--| doc\n" ++ t2, .passed = true },
        .{ .text = t1, .passed = true },
        .{ .text = t1 ++ "r: $ top $ by ax_top []\n", .passed = false },
        .{ .text = t1 ++ "\n-- comment\n  r : $ top $ by ax_top []\n", .passed = false },
        .{ .text = t1 ++ "\n-- comment\n  []\n", .passed = false },
        .{ .text = t1 ++ "(a := $ top $) []\n", .passed = false },
        .{ .text = t1[0 .. t1.len - 1], .passed = false },
        .{ .text = t3 ++ "$ ) []\n", .passed = false },
        .{ .text = "t1\n---\np: $ top $ by ax_top []\nq: $ bot $ by ax_top\n", .passed = false },
    };
    for (cases) |case| {
        const expected = (try proofBlocks(arena, case.text))[0];
        const block = (try knownBlocks(arena, &memo, case.text))[0];
        try std.testing.expectEqual(case.passed, block.known_body != null);
        try std.testing.expectEqualDeep(
            expected,
            try block.withLines(arena, case.text),
        );
    }
}

test "the parser parses a body that ended the text without a newline" {
    const allocator = std.testing.allocator;
    var arena_state = std.heap.ArenaAllocator.init(allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    var memo = CheckMemo.init(allocator);
    defer memo.deinit();

    const mm0_text =
        \\provable sort wff;
        \\term top: wff;
        \\axiom ax_top: $ top $;
        \\theorem t1: $ top $;
    ;
    const proof_text = "t1\n---\np: $ top $ by ax_top";
    allocator.free(try analyzeDump(allocator, mm0_text, proof_text, &memo, false));
    try std.testing.expectEqual(@as(usize, 1), memo.entries.count());
    const longer = proof_text ++ "_2\n";
    const block = (try knownBlocks(arena, &memo, longer))[0];
    try std.testing.expectEqual(@as(?u64, null), block.known_body);
    try std.testing.expectEqualStrings("ax_top_2", block.lines[0].application.rule_name);
}

test "check memo drops a block whose output it cannot record" {
    const allocator = std.testing.allocator;
    var memo = CheckMemo.init(allocator);
    defer memo.deinit();

    // The rule is declared after the theorem, so the diagnostic points into
    // the .mm0 text and cannot be replayed.
    const mm0_text =
        \\provable sort wff;
        \\term top: wff;
        \\theorem t1: $ top $;
        \\axiom ax_top: $ top $;
    ;
    const proof_text =
        \\t1
        \\---
        \\p: $ top $ by ax_top []
    ;
    const first = try analyzeDump(allocator, mm0_text, proof_text, &memo, false);
    defer allocator.free(first);
    try std.testing.expectEqual(@as(usize, 0), memo.entries.count());
    const second = try analyzeDump(allocator, mm0_text, proof_text, &memo, false);
    defer allocator.free(second);
    try std.testing.expectEqualStrings(first, second);
    try std.testing.expectEqual(@as(usize, 0), memo.entries.count());
}

test "check memo asks again whether a rule is declared later" {
    const allocator = std.testing.allocator;
    var memo = CheckMemo.init(allocator);
    defer memo.deinit();

    const mm0_text =
        \\provable sort wff;
        \\term top: wff;
        \\theorem t1: $ top $;
    ;
    const proof_text =
        \\t1
        \\---
        \\p: $ top $ by ax_top []
    ;
    try expectSameAnalysis(allocator, &memo, "later", .{
        .name = "unknown rule",
        .mm0_text = mm0_text,
        .proof_text = proof_text,
    });
    try std.testing.expectEqual(@as(usize, 1), memo.entries.count());
    // The rule is still unknown when the theory text moves.
    try expectSameAnalysis(allocator, &memo, "later", .{
        .name = "moved",
        .mm0_text = "-- moved\n" ++ mm0_text ++ "\naxiom ax_bot: $ top $;",
        .proof_text = proof_text,
    });
    try std.testing.expectEqual(@as(usize, 1), memo.hits);
    // Nothing the fingerprint covers differs here.
    try expectSameAnalysis(allocator, &memo, "later", .{
        .name = "declared later",
        .mm0_text = mm0_text ++ "\naxiom ax_top: $ top $;",
        .proof_text = proof_text,
    });
    try std.testing.expectEqual(@as(usize, 1), memo.hits);
}
