//! Differential guard for the proof-block check memo (`CheckMemo`): over
//! the whole `tests/proof_cases` corpus, an analysis served from a warm memo
//! must produce exactly what a cold analysis produces — every diagnostic,
//! span, note, sink entry and error — under the edits an editor makes:
//! nothing (all hits), a body edit that only shifts later blocks, a body
//! edit that flips an outcome, and a theory edit that shifts every `.mm0`
//! position.

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
) ![]u8 {
    var arena_state = std.heap.ArenaAllocator.init(allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();

    var holes = mm0.CompilerSupport.Context.HoleInferenceSink{ .allocator = arena };
    var inlines = mm0.CompilerSupport.Context.InlineConclusionSink{ .allocator = arena };
    var compiler = Compiler.initWithProof(arena, mm0_text, proof_text);
    compiler.allow_search_placeholders = true;
    compiler.hole_inference_sink = &holes;
    compiler.inline_conclusion_sink = &inlines;
    compiler.check_memo = memo;

    var out = std.ArrayListUnmanaged(u8){};
    const writer = out.writer(arena);
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
    for (inlines.items.items) |item| {
        try writer.print("inline {d}-{d} {s}\n", .{
            item.span.start,
            item.span.end,
            item.conclusion,
        });
    }
    return try allocator.dupe(u8, out.items);
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
    var out = std.ArrayListUnmanaged(u8){};
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
};

/// Cold vs warm must agree; returns the warm dump's hit delta.
fn expectSameAnalysis(
    allocator: std.mem.Allocator,
    memo: *CheckMemo,
    stem: []const u8,
    scenario: Scenario,
) !void {
    const cold = try analyzeDump(allocator, scenario.mm0_text, scenario.proof_text, null);
    defer allocator.free(cold);
    const warm = try analyzeDump(allocator, scenario.mm0_text, scenario.proof_text, memo);
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
    var blocks = std.ArrayListUnmanaged(ProofScript.ProofBlock){};
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
    var stems = std.ArrayListUnmanaged([]const u8){};
    var dir = try std.fs.cwd().openDir("tests/proof_cases", .{ .iterate = true });
    defer dir.close();
    var it = dir.iterate();
    while (try it.next()) |entry| {
        if (entry.kind != .file) continue;
        if (!std.mem.endsWith(u8, entry.name, ".auf")) continue;
        const stem = entry.name[0 .. entry.name.len - ".auf".len];
        const mm0_name = try std.fmt.allocPrint(allocator, "{s}.mm0", .{stem});
        defer allocator.free(mm0_name);
        dir.access(mm0_name, .{}) catch continue;
        try stems.append(allocator, try allocator.dupe(u8, stem));
    }
    std.sort.pdq([]const u8, stems.items, {}, struct {
        fn lessThan(_: void, a: []const u8, b: []const u8) bool {
            return std.mem.lessThan(u8, a, b);
        }
    }.lessThan);
    return try stems.toOwnedSlice(allocator);
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
    const pair = mm0.Imports.loadPair(arena, mm0_path, proof_path, &failure) catch return;
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
            if (memo.misses - misses > unrecordable + 1) {
                const dump = try analyzeDump(allocator, mm0_text, edited, null);
                defer allocator.free(dump);
                std.debug.print(
                    "check memo shift over-miss: {s} block {d}/{d} ({s}): {d} misses, {d} unrecordable\n--- edited analysis ---\n{s}\n--- edited text ---\n{s}\n",
                    .{ stem, index, blocks.len, block.name, memo.misses - misses, unrecordable, dump, edited },
                );
                return error.CheckMemoOverMiss;
            }
        }
        // A bogus rule on the last line: the outcome flips.
        {
            const rule_span = last.application.rule_span;
            const edited = try applyEdit(arena, proof_text, .{
                .start = rule_span.start,
                .end = rule_span.end,
                .text = "zz_no_such_rule",
            });
            try expectSameAnalysis(allocator, memo, stem, .{
                .name = "break",
                .mm0_text = mm0_text,
                .proof_text = edited,
            });
        }
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

    // Back to the original: the entries recorded first still serve.
    {
        const misses = memo.misses;
        try expectSameAnalysis(allocator, memo, stem, .{
            .name = "restore",
            .mm0_text = mm0_text,
            .proof_text = proof_text,
        });
        try std.testing.expectEqual(unrecordable, memo.misses - misses);
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
    memo.max_entries = 1 << 16;

    var counts: Counts = .{};
    for (stems) |stem| {
        try runFixture(allocator, &memo, stem, &counts);
    }
    try std.testing.expect(counts.blocks > 0);
    try std.testing.expect(counts.hits_seen);
    try std.testing.expect(memo.hits > memo.misses);
}

test "check memo evicts least recently used entries past its cap" {
    const allocator = std.testing.allocator;
    var memo = CheckMemo.init(allocator);
    defer memo.deinit();
    memo.max_entries = 4;

    const mm0_text =
        \\provable sort wff;
        \\term top: wff;
        \\axiom ax_top: $ top $;
        \\theorem t1: $ top $;
        \\theorem t2: $ top $;
        \\theorem t3: $ top $;
        \\theorem t4: $ top $;
        \\theorem t5: $ top $;
        \\theorem t6: $ top $;
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
        \\
        \\t4
        \\---
        \\p: $ top $ by ax_top []
        \\
        \\t5
        \\---
        \\p: $ top $ by ax_top []
        \\
        \\t6
        \\---
        \\p: $ top $ by ax_top []
    ;
    const first = try analyzeDump(allocator, mm0_text, proof_text, &memo);
    defer allocator.free(first);
    try std.testing.expect(memo.entries.count() <= 4);
    const second = try analyzeDump(allocator, mm0_text, proof_text, &memo);
    defer allocator.free(second);
    try std.testing.expectEqualStrings(first, second);
    try std.testing.expect(memo.entries.count() <= 4);
}
