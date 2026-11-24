//! Differential guard for the proof-block check memo (`CheckMemo`): over
//! the whole `tests/proof_cases` corpus, an analysis served from a warm memo
//! must produce exactly what a cold analysis produces — every diagnostic,
//! span, note, sink entry and error — under the edits an editor makes:
//! nothing (all hits), a body edit that only shifts later blocks, a body
//! edit that flips an outcome and its undo, and a theory edit that shifts
//! every `.mm0` position. A run with the inline conclusion sink must bypass the memo.

const std = @import("std");
const mm0 = @import("../lib.zig");

const Compiler = mm0.Compiler;
const CheckMemo = mm0.CheckMemo;
const ProofScript = mm0.ProofScript;

/// Everything an analysis reports, rendered canonically.
fn analyzeDump(
    allocator: std.mem.Allocator,
    mm0_text: []const u8,
    proof_text: []const u8,
    memo: ?*CheckMemo,
    inlines_sink: bool,
) ![]u8 {
    var arena_state = std.heap.ArenaAllocator.init(allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();

    var holes = mm0.CompilerSupport.Context.HoleInferenceSink{ .allocator = arena };
    var inlines = mm0.CompilerSupport.Context.InlineConclusionSink{ .allocator = arena };
    var compiler = Compiler.initWithProof(arena, mm0_text, proof_text);
    compiler.allow_search_placeholders = true;
    compiler.hole_inference_sink = &holes;
    if (inlines_sink) compiler.inline_conclusion_sink = &inlines;
    compiler.check_memo = memo;

    var out: std.Io.Writer.Allocating = .init(arena);
    const writer = &out.writer;
    if (compiler.analyze()) |_| {
        try writer.writeAll("result: ok\n");
    } else |err| {
        try writer.print("result: {s}\n", .{@errorName(err)});
    }
    for (compiler.primaryDiagnostics()) |diag| {
        try writer.writeAll("primary ");
        try dumpDiagnostic(writer, diag);
    }
    for (compiler.warningDiagnostics()) |diag| {
        try writer.writeAll("warning ");
        try dumpDiagnostic(writer, diag);
    }
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
    for (holes.items.items) |hole| {
        try writer.print("hole {d}-{d} {s}\n", .{
            hole.span.start,
            hole.span.end,
            hole.expression,
        });
    }
    for (holes.assertions.items) |filled| {
        try writer.print("filled {d}-{d} {d}-{d} {s}\n", .{
            filled.line.start,
            filled.line.end,
            filled.assertion.start,
            filled.assertion.end,
            filled.text,
        });
    }
    for (inlines.items.items) |item| {
        try writer.print("inline {d}-{d} {s}\n", .{
            item.span.start,
            item.span.end,
            item.conclusion,
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

const Counts = struct { blocks: usize = 0, hits_seen: bool = false };

const Scenario = struct {
    name: []const u8,
    mm0_text: []const u8,
    proof_text: []const u8,
    /// Also attach the inline conclusion sink.
    inlines_sink: bool = false,
};

/// Cold vs warm must agree; returns the warm dump's hit delta.
fn expectSameAnalysis(
    allocator: std.mem.Allocator,
    memo: *CheckMemo,
    stem: []const u8,
    scenario: Scenario,
) !void {
    const cold = try analyzeDump(allocator, scenario.mm0_text, scenario.proof_text, null, scenario.inlines_sink);
    defer allocator.free(cold);
    const warm = try analyzeDump(allocator, scenario.mm0_text, scenario.proof_text, memo, scenario.inlines_sink);
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

    // A comment at the top of the theory shifts every `.mm0` position:
    // the theory prefix differs for every block, so all re-check. (The
    // memo is shared across fixtures, so the comment names this one:
    // two fixtures with the same theory and proof prefix would otherwise
    // legitimately share entries.)
    {
        const edited = try applyEdit(arena, mm0_text, .{
            .start = 0,
            .end = 0,
            .text = try std.fmt.allocPrint(arena, "-- check memo corpus test {s}\n", .{stem}),
        });
        const hits = memo.hits;
        try expectSameAnalysis(allocator, memo, stem, .{
            .name = "theory shift",
            .mm0_text = edited,
            .proof_text = proof_text,
        });
        try std.testing.expectEqual(hits, memo.hits);
    }

    // Back to the original: the theory-shift run kept only the entries it
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

    // The memo records no inline conclusions, so a run that collects them
    // checks every block.
    {
        const hits = memo.hits;
        const misses = memo.misses;
        try expectSameAnalysis(allocator, memo, stem, .{
            .name = "inline sink",
            .mm0_text = mm0_text,
            .proof_text = proof_text,
            .inlines_sink = true,
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

    // The rule is declared after the theorem, so the diagnostic points past
    // the theorem's place in the .mm0 text and cannot be replayed.
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
