//! Memo of proof-block check outcomes for editor re-analysis.
//!
//! The analyze path (`pipeline/analyze.zig`) walks the statements in order
//! and calls `Check.checkTheoremBlock` on every theorem and lemma block. On
//! a corpus like zermelo that walk costs ~70 ms per keystroke, ~95% of it
//! in block checks; parsing and registering the theory is a few ms. So an
//! edit is made incremental by memoizing the checks, not by snapshotting
//! the compiler state: a run re-checks a block only when something the
//! check can observe has changed.
//!
//! What a check observes is a prefix of the two sources: the `.mm0` text
//! up to the theory parser's position (less trailing whitespace), and the
//! `.auf` text up to the block, except that an EARLIER block's proof body influences later
//! checks only through its outcome (registered, or marked invalid). The
//! run keeps a running fingerprint of exactly that: theory text and
//! proof text are hashed lazily up to each check (`sync`), proof bodies
//! are skipped, and each block's outcome is hashed after it
//! (`feedOutcome`). Local defs, notation items, filler defs, comments and
//! parse garbage all lie in the hashed ranges, so they invalidate what
//! follows, as they should. The memo key is that fingerprint plus a hash of
//! the block body; the value is everything the check emitted: its
//! error, the diagnostics and warnings it added, its hole and inline
//! conclusion sink entries, and the `last_diagnostic` it left behind.
//!
//! One thing a check reads outside the hashed prefix is the rule catalog
//! (`RuleCatalog`), built from the whole `.mm0` up front and consulted
//! for "rule declared later" diagnostics. Those lookups are recorded per
//! entry and re-verified on a hit.
//!
//! Positions: identical hashed theory text means identical theory
//! offsets, so `.mm0` spans replay unchanged (the record refuses spans
//! past the hashed prefix). Proof offsets shift when an earlier body
//! changes length, so `.auf` spans are relocated by the block's
//! displacement; spans outside the block are not relocatable and make the
//! block unrecordable (it is simply re-checked each run).
//!
//! The memo is opt-in through `CompilerContext.check_memo`; the compile
//! path never sets it, so MMB output is untouched.

const std = @import("std");
const CompilerDiag = @import("../diag.zig");
const Diagnostic = CompilerDiag.Diagnostic;
const Span = @import("../proof_script.zig").Span;
const ProofBlock = @import("../proof_script.zig").ProofBlock;
const RuleCatalog = @import("./rule_catalog.zig");
const Context = @import("./context.zig");
const CompilerContext = Context.CompilerContext;
const HoleInference = Context.HoleInference;
const InlineConclusion = Context.InlineConclusion;

pub const CheckMemo = struct {
    /// Bumped when what a check observes, or what an entry stores, changes
    /// shape, so a stale entry can never match.
    const schema_version: u32 = 1;
    pub const default_max_entries: usize = 4096;

    pub const Key = struct {
        fingerprint: u64,
        body: u64,
    };

    pub const RunConfig = struct {
        allow_search_placeholders: bool,
    };

    /// One rule-catalog lookup a check made, with what it saw.
    pub const CatalogLookup = struct {
        name: []const u8,
        entry: ?RuleCatalog.Entry,
    };

    pub const Entry = struct {
        arena: std.heap.ArenaAllocator,
        last_used: u32,
        /// Null when the check succeeded, else the error it returned.
        outcome: ?anyerror,
        /// Where the block lay in the proof text when recorded.
        block: Span,
        primary: []const Diagnostic,
        warnings: []const Diagnostic,
        last_diagnostic: ?Diagnostic,
        holes: []const HoleInference,
        inlines: []const InlineConclusion,
        lookups: []const CatalogLookup,

        /// Re-emit everything the recorded check produced, with proof
        /// spans moved to where the block lies now.
        pub fn replay(
            self: *const Entry,
            ctx: *CompilerContext,
            block_start: usize,
        ) !void {
            const delta: i64 = @as(i64, @intCast(block_start)) -
                @as(i64, @intCast(self.block.start));
            for (self.primary) |diag| {
                ctx.addPrimaryDiagnostic(relocateDiagnostic(diag, delta));
            }
            for (self.warnings) |diag| {
                ctx.addWarning(relocateDiagnostic(diag, delta));
            }
            if (ctx.hole_inference_sink) |sink| {
                for (self.holes) |hole| {
                    try sink.addOwned(
                        shiftSpan(hole.span, delta),
                        try sink.allocator.dupe(u8, hole.expression),
                    );
                }
            }
            if (ctx.inline_conclusion_sink) |sink| {
                for (self.inlines) |inline_conclusion| {
                    try sink.addOwned(
                        shiftSpan(inline_conclusion.span, delta),
                        try sink.allocator.dupe(u8, inline_conclusion.conclusion),
                    );
                }
            }
            if (self.last_diagnostic) |diag| {
                ctx.setDiagnostic(relocateDiagnostic(diag, delta));
            } else {
                ctx.restoreDiagnostic(null);
            }
        }
    };

    /// Sink positions at the start of a check, so its output can be
    /// cut out afterwards.
    pub const Recording = struct {
        /// The theory position the fingerprint covers; `.mm0` spans past
        /// it are not recordable.
        mm0_limit: usize,
        primary_count: usize,
        warning_count: usize,
        dropped_primary: usize,
        dropped_warnings: usize,
        holes: usize,
        inlines: usize,
    };

    const Domain = enum(u8) { config = 1, mm0 = 2, proof = 3, outcome = 4 };

    allocator: std.mem.Allocator,
    entries: std.AutoHashMapUnmanaged(Key, *Entry) = .empty,
    max_entries: usize = default_max_entries,
    /// Bumped per run; entries remember the last run that used them.
    run: u32 = 0,
    active: bool = false,
    fingerprint: u64 = 0,
    mm0_cursor: usize = 0,
    proof_cursor: usize = 0,
    hits: usize = 0,
    misses: usize = 0,
    /// Catalog lookups of the check being recorded.
    lookups: std.ArrayListUnmanaged(CatalogLookup) = .empty,
    recording: bool = false,
    recording_failed: bool = false,

    pub fn init(allocator: std.mem.Allocator) CheckMemo {
        return .{ .allocator = allocator };
    }

    pub fn deinit(self: *CheckMemo) void {
        var it = self.entries.valueIterator();
        while (it.next()) |entry| self.destroyEntry(entry.*);
        self.entries.deinit(self.allocator);
        self.lookups.deinit(self.allocator);
        self.* = undefined;
    }

    pub fn beginRun(self: *CheckMemo, config: RunConfig) void {
        self.run +%= 1;
        self.active = true;
        self.fingerprint = 0;
        self.mm0_cursor = 0;
        self.proof_cursor = 0;
        self.recording = false;
        const bytes = [_]u8{
            @intCast(schema_version),
            @intFromBool(config.allow_search_placeholders),
        };
        self.feed(.config, &bytes);
    }

    pub fn endRun(self: *CheckMemo) void {
        self.active = false;
        self.recording = false;
        self.evict();
    }

    /// Hash `bytes` into the running fingerprint. The domain tag and the
    /// length keep differently split feeds of the same bytes distinct, so
    /// an equal fingerprint means equal theory text up to the cursor.
    fn feed(self: *CheckMemo, domain: Domain, bytes: []const u8) void {
        var hasher = std.hash.Wyhash.init(self.fingerprint);
        hasher.update(&[_]u8{@intFromEnum(domain)});
        const len: u64 = bytes.len;
        hasher.update(std.mem.asBytes(&len));
        hasher.update(bytes);
        self.fingerprint = hasher.final();
    }

    /// Hash the text between the cursors and the given positions.
    fn sync(
        self: *CheckMemo,
        mm0: []const u8,
        mm0_pos: usize,
        proof: []const u8,
        proof_pos: usize,
    ) void {
        const mm0_end = @min(mm0_pos, mm0.len);
        if (mm0_end > self.mm0_cursor) {
            self.feed(.mm0, mm0[self.mm0_cursor..mm0_end]);
            self.mm0_cursor = mm0_end;
        }
        const proof_end = @min(proof_pos, proof.len);
        if (proof_end > self.proof_cursor) {
            self.feed(.proof, proof[self.proof_cursor..proof_end]);
            self.proof_cursor = proof_end;
        }
    }

    /// Record a block's outcome: what later checks may observe of it.
    pub fn feedOutcome(self: *CheckMemo, name: []const u8, ok: bool) void {
        if (!self.active) return;
        self.feed(.outcome, name);
        self.feed(.outcome, &[_]u8{@intFromBool(ok)});
    }

    /// The key of the check about to run on `block`: the fingerprint of
    /// everything before its body, and the body itself. Advances the
    /// cursors past the block. The body ends with the block's last line:
    /// the block's span runs on through the trivia before the next item,
    /// which differs between a block at the end of a file and the same
    /// block followed by another (a library's own analysis vs. an
    /// importer's join), and the checker never looks at it.
    pub fn keyForBlock(
        self: *CheckMemo,
        mm0: []const u8,
        mm0_pos: usize,
        proof: []const u8,
        block: ProofBlock,
    ) Key {
        // The parser's position after a statement runs over the whitespace
        // that follows it, which is one newline more when another file is
        // joined behind a library's last statement; a check cannot see it.
        var mm0_end = @min(mm0_pos, mm0.len);
        while (mm0_end > self.mm0_cursor and
            std.ascii.isWhitespace(mm0[mm0_end - 1])) mm0_end -= 1;
        self.sync(mm0, mm0_end, proof, block.header_span.end);
        const body_start = @min(block.header_span.end, proof.len);
        const body_end = @min(bodyEnd(block), proof.len);
        const body = proof[body_start..@max(body_start, body_end)];
        const block_end = @min(block.span.end, proof.len);
        if (block_end > self.proof_cursor) self.proof_cursor = block_end;
        return .{
            .fingerprint = self.fingerprint,
            .body = std.hash.Wyhash.hash(0, body),
        };
    }

    fn bodyEnd(block: ProofBlock) usize {
        if (block.lines.len > 0) return block.lines[block.lines.len - 1].span.end;
        if (block.underline_span) |underline| return underline.end;
        return block.header_span.end;
    }

    /// The entry for `key` whose recorded catalog lookups still hold.
    pub fn find(
        self: *CheckMemo,
        key: Key,
        catalog: *const RuleCatalog.Catalog,
    ) ?*const Entry {
        const entry = self.entries.get(key) orelse {
            self.misses += 1;
            return null;
        };
        for (entry.lookups) |lookup| {
            if (!catalogEntryEql(lookup.entry, catalog.get(lookup.name))) {
                self.misses += 1;
                return null;
            }
        }
        entry.last_used = self.run;
        self.hits += 1;
        return entry;
    }

    pub fn beginRecording(self: *CheckMemo, ctx: *const CompilerContext) Recording {
        self.lookups.clearRetainingCapacity();
        self.recording = true;
        self.recording_failed = false;
        return .{
            .mm0_limit = self.mm0_cursor,
            .primary_count = ctx.diagnostics.primary_diagnostic_count,
            .warning_count = ctx.diagnostics.warning_count,
            .dropped_primary = ctx.diagnostics.dropped_primary_diagnostic_count,
            .dropped_warnings = ctx.diagnostics.dropped_warning_count,
            .holes = if (ctx.hole_inference_sink) |sink| sink.items.items.len else 0,
            .inlines = if (ctx.inline_conclusion_sink) |sink| sink.items.items.len else 0,
        };
    }

    /// Called at the catalog lookup site while a check is being recorded.
    pub fn noteCatalogLookup(
        self: *CheckMemo,
        name: []const u8,
        entry: ?RuleCatalog.Entry,
    ) void {
        if (!self.recording) return;
        self.lookups.append(self.allocator, .{ .name = name, .entry = entry }) catch {
            self.recording_failed = true;
        };
    }

    /// Store what the check emitted since `recording`. Skipped when the
    /// output cannot be replayed faithfully: an out-of-memory outcome, a
    /// sink that overflowed, or a span outside the relocatable ranges.
    pub fn finishRecording(
        self: *CheckMemo,
        ctx: *const CompilerContext,
        recording: Recording,
        key: Key,
        outcome: ?anyerror,
        block: Span,
    ) void {
        self.recording = false;
        if (self.recording_failed) return;
        if (outcome) |err| if (err == error.OutOfMemory) return;
        const sink = ctx.diagnostics;
        if (sink.dropped_primary_diagnostic_count != recording.dropped_primary or
            sink.dropped_warning_count != recording.dropped_warnings)
        {
            return;
        }
        self.record(ctx, recording, key, outcome, block) catch {};
    }

    fn record(
        self: *CheckMemo,
        ctx: *const CompilerContext,
        recording: Recording,
        key: Key,
        outcome: ?anyerror,
        block: Span,
    ) !void {
        const mm0_limit = recording.mm0_limit;
        const entry = try self.allocator.create(Entry);
        errdefer self.allocator.destroy(entry);
        entry.* = .{
            .arena = std.heap.ArenaAllocator.init(self.allocator),
            .last_used = self.run,
            .outcome = outcome,
            .block = block,
            .primary = &.{},
            .warnings = &.{},
            .last_diagnostic = null,
            .holes = &.{},
            .inlines = &.{},
            .lookups = &.{},
        };
        errdefer entry.arena.deinit();
        const arena = entry.arena.allocator();

        const sink = ctx.diagnostics;
        entry.primary = try dupeDiagnostics(
            arena,
            sink.primaryDiagnostics()[recording.primary_count..],
            block,
            mm0_limit,
        ) orelse return;
        entry.warnings = try dupeDiagnostics(
            arena,
            sink.warningDiagnostics()[recording.warning_count..],
            block,
            mm0_limit,
        ) orelse return;
        if (sink.last_diagnostic) |diag| {
            if (!spansRecordable(diag, block, mm0_limit)) return;
            entry.last_diagnostic = try dupeDiagnostic(arena, diag);
        }
        if (ctx.hole_inference_sink) |holes| {
            const items = holes.items.items[recording.holes..];
            const copies = try arena.alloc(HoleInference, items.len);
            for (items, copies) |item, *copy| {
                if (!spanWithin(item.span, block)) return;
                copy.* = .{
                    .span = item.span,
                    .expression = try arena.dupe(u8, item.expression),
                };
            }
            entry.holes = copies;
        }
        if (ctx.inline_conclusion_sink) |inlines| {
            const items = inlines.items.items[recording.inlines..];
            const copies = try arena.alloc(InlineConclusion, items.len);
            for (items, copies) |item, *copy| {
                if (!spanWithin(item.span, block)) return;
                copy.* = .{
                    .span = item.span,
                    .conclusion = try arena.dupe(u8, item.conclusion),
                };
            }
            entry.inlines = copies;
        }
        const lookups = try arena.alloc(CatalogLookup, self.lookups.items.len);
        for (self.lookups.items, lookups) |lookup, *copy| {
            copy.* = .{
                .name = try arena.dupe(u8, lookup.name),
                .entry = lookup.entry,
            };
        }
        entry.lookups = lookups;

        const gop = try self.entries.getOrPut(self.allocator, key);
        if (gop.found_existing) self.destroyEntry(gop.value_ptr.*);
        gop.value_ptr.* = entry;
    }

    fn destroyEntry(self: *CheckMemo, entry: *Entry) void {
        entry.arena.deinit();
        self.allocator.destroy(entry);
    }

    /// Drop the least recently used entries once the memo outgrows its
    /// cap, down to three quarters of it.
    fn evict(self: *CheckMemo) void {
        if (self.entries.count() <= self.max_entries) return;
        const Aged = struct {
            key: Key,
            last_used: u32,
            fn olderFirst(_: void, a: @This(), b: @This()) bool {
                return a.last_used < b.last_used;
            }
        };
        var aged = std.ArrayListUnmanaged(Aged){};
        defer aged.deinit(self.allocator);
        var it = self.entries.iterator();
        while (it.next()) |kv| {
            aged.append(self.allocator, .{
                .key = kv.key_ptr.*,
                .last_used = kv.value_ptr.*.last_used,
            }) catch return;
        }
        std.sort.pdq(Aged, aged.items, {}, Aged.olderFirst);
        const target = self.max_entries - self.max_entries / 4;
        for (aged.items) |old| {
            if (self.entries.count() <= target) break;
            if (self.entries.fetchRemove(old.key)) |removed| {
                self.destroyEntry(removed.value);
            }
        }
    }
};

fn catalogEntryEql(a: ?RuleCatalog.Entry, b: ?RuleCatalog.Entry) bool {
    if (a == null or b == null) return a == null and b == null;
    return a.?.ordinal == b.?.ordinal and
        a.?.name_span.start == b.?.name_span.start and
        a.?.name_span.end == b.?.name_span.end;
}

fn spanWithin(span: Span, block: Span) bool {
    return span.start >= block.start and span.end <= block.end and
        span.start <= span.end;
}

fn spanRecordable(
    source: CompilerDiag.DiagnosticSource,
    span: ?Span,
    block: Span,
    mm0_limit: usize,
) bool {
    const actual = span orelse return true;
    return switch (source) {
        .proof => spanWithin(actual, block),
        .mm0 => actual.end <= mm0_limit,
    };
}

fn spansRecordable(diag: Diagnostic, block: Span, mm0_limit: usize) bool {
    if (!spanRecordable(diag.source, diag.span, block, mm0_limit)) return false;
    for (diag.noteSlice()) |note| {
        if (!spanRecordable(note.source, note.span, block, mm0_limit)) {
            return false;
        }
    }
    for (diag.relatedSlice()) |related| {
        if (!spanRecordable(related.source, related.span, block, mm0_limit)) {
            return false;
        }
    }
    return true;
}

fn shiftSpan(span: Span, delta: i64) Span {
    return .{
        .start = @intCast(@as(i64, @intCast(span.start)) + delta),
        .end = @intCast(@as(i64, @intCast(span.end)) + delta),
    };
}

fn shiftOptionalSpan(span: ?Span, delta: i64) ?Span {
    return shiftSpan(span orelse return null, delta);
}

fn relocateDiagnostic(diag: Diagnostic, delta: i64) Diagnostic {
    var out = diag;
    if (out.source == .proof) out.span = shiftOptionalSpan(out.span, delta);
    for (out.notes[0..out.note_count]) |*note| {
        if (note.source == .proof) note.span = shiftOptionalSpan(note.span, delta);
    }
    for (out.related[0..out.related_count]) |*related| {
        if (related.source == .proof) related.span = shiftSpan(related.span, delta);
    }
    return out;
}

/// Null when a diagnostic cannot be relocated.
fn dupeDiagnostics(
    arena: std.mem.Allocator,
    diagnostics: []const Diagnostic,
    block: Span,
    mm0_limit: usize,
) !?[]const Diagnostic {
    const copies = try arena.alloc(Diagnostic, diagnostics.len);
    for (diagnostics, copies) |diag, *copy| {
        if (!spansRecordable(diag, block, mm0_limit)) return null;
        copy.* = try dupeDiagnostic(arena, diag);
    }
    return copies;
}

/// A copy whose every string lives in `arena`. Mirrors the sink's
/// stable-copy (`DiagnosticSink.stableDiagnostic`): named string fields,
/// the detail payload, and each note's message payload.
fn dupeDiagnostic(arena: std.mem.Allocator, diag: Diagnostic) !Diagnostic {
    var out = diag;
    out.theorem_name = try dupeOptional(arena, diag.theorem_name);
    out.block_name = try dupeOptional(arena, diag.block_name);
    out.line_label = try dupeOptional(arena, diag.line_label);
    out.rule_name = try dupeOptional(arena, diag.rule_name);
    out.name = try dupeOptional(arena, diag.name);
    out.expected_name = try dupeOptional(arena, diag.expected_name);
    out.detail = try dupeUnionStrings(CompilerDiag.DiagnosticDetail, arena, diag.detail);
    for (out.notes[0..out.note_count]) |*note| {
        note.message = try dupeUnionStrings(
            CompilerDiag.NoteMessage,
            arena,
            note.message,
        );
    }
    return out;
}

fn dupeOptional(arena: std.mem.Allocator, text: ?[]const u8) !?[]const u8 {
    return try arena.dupe(u8, text orelse return null);
}

/// Copy the string fields of a tagged union's active struct payload, so a
/// new variant gets the copy for free (like the sink's stable copies).
fn dupeUnionStrings(comptime U: type, arena: std.mem.Allocator, value: U) !U {
    switch (value) {
        inline else => |payload, tag| {
            const Payload = @TypeOf(payload);
            if (Payload == void) return value;
            var copy = payload;
            inline for (@typeInfo(Payload).@"struct".fields) |field| {
                if (field.type == []const u8) {
                    @field(copy, field.name) =
                        try arena.dupe(u8, @field(payload, field.name));
                } else if (field.type == ?[]const u8) {
                    @field(copy, field.name) =
                        try dupeOptional(arena, @field(payload, field.name));
                }
            }
            return @unionInit(U, @tagName(tag), copy);
        },
    }
}

test "relocation shifts proof spans only" {
    var diag: Diagnostic = .{
        .kind = .unknown_rule,
        .err = error.UnknownRule,
        .source = .proof,
        .span = .{ .start = 10, .end = 14 },
    };
    CompilerDiag.addNote(&diag, .rule_declared_later, .mm0, .{ .start = 3, .end = 5 });
    CompilerDiag.addRelated(&diag, .rule_declaration_here, .proof, .{ .start = 2, .end = 4 });
    const moved = relocateDiagnostic(diag, 5);
    try std.testing.expectEqual(@as(usize, 15), moved.span.?.start);
    try std.testing.expectEqual(@as(usize, 3), moved.notes[0].span.?.start);
    try std.testing.expectEqual(@as(usize, 7), moved.related[0].span.start);
    const back = relocateDiagnostic(moved, -5);
    try std.testing.expectEqual(@as(usize, 10), back.span.?.start);
}

test "spans outside the block are not recordable" {
    const block: Span = .{ .start = 100, .end = 200 };
    var inside: Diagnostic = .{
        .kind = .unknown_rule,
        .err = error.UnknownRule,
        .source = .proof,
        .span = .{ .start = 100, .end = 200 },
    };
    try std.testing.expect(spansRecordable(inside, block, 50));
    CompilerDiag.addRelated(&inside, .rule_declaration_here, .mm0, .{ .start = 40, .end = 60 });
    try std.testing.expect(!spansRecordable(inside, block, 50));
    const earlier: Diagnostic = .{
        .kind = .unknown_rule,
        .err = error.UnknownRule,
        .source = .proof,
        .span = .{ .start = 90, .end = 110 },
    };
    try std.testing.expect(!spansRecordable(earlier, block, 50));
}

test "dupeDiagnostic copies every string payload" {
    var text = [_]u8{ 'a', 'b', 'c' };
    var diag: Diagnostic = .{
        .kind = .unknown_rule,
        .err = error.UnknownRule,
        .rule_name = &text,
        .detail = .{ .name_suggestion = .{ .suggestion = &text } },
    };
    CompilerDiag.addNote(&diag, .{ .already_matched = .{ .text = &text } }, .proof, null);
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const copy = try dupeDiagnostic(arena.allocator(), diag);
    text[0] = 'z';
    try std.testing.expectEqualStrings("abc", copy.rule_name.?);
    try std.testing.expectEqualStrings("abc", copy.detail.name_suggestion.suggestion);
    try std.testing.expectEqualStrings("abc", copy.notes[0].message.already_matched.text);
}
