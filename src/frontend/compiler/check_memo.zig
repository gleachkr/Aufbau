//! Memo of proof-block check outcomes for editor re-analysis.
//!
//! The analyze path (`pipeline/analyze.zig`) walks the statements in order
//! and checks every theorem and lemma block (`Common.analyzeBlock`). On
//! a corpus like zermelo that walk costs ~70 ms per keystroke, ~95% of it
//! in block checks; parsing and registering the theory is a few ms. So an
//! edit is made incremental by memoizing the checks, not by snapshotting
//! the compiler state: a run re-checks a block only when something the
//! check can observe has changed.
//!
//! What a check observes is a prefix of the two sources: the `.mm0`
//! statements up to the theory parser's position, with their directives,
//! and the `.auf` text up to the block, less the earlier blocks' proof
//! bodies. An earlier proof is invisible to later checks: the analysis
//! keeps its theorem or lemma in scope whether the proof holds or not, so
//! only its statement (in the hashed text) matters. Comments and
//! whitespace between two `.mm0` statements are invisible too, so a
//! comment edit re-checks nothing, and a library's blocks are shared by
//! the files that import it, whatever comments those start with. The run
//! keeps a running fingerprint of exactly that: theory and proof text are
//! hashed lazily up to each check (`keyForBlock`). So an edit inside one
//! proof re-checks that proof alone. Local defs, notation items, filler
//! defs, proof-side comments and parse garbage all lie in the hashed
//! ranges, so they invalidate what follows, as they should. The memo key
//! is that fingerprint plus a hash of the block body; the value is
//! everything the check emitted: its error, the diagnostics and warnings
//! it added, its hole sink entries, and the `last_diagnostic` it left
//! behind. So a memo-backed run collects holes, and only holes: a run
//! without the hole sink, or with the unknown-value or stats sink, checks
//! every block (`beginRun`).
//!
//! The memo keeps what each root's latest run used (`root`): an entry no
//! later run of its root found is one that root's texts no longer reach,
//! and the entries of an edit's other roots stay for their next run.
//!
//! One thing a check reads outside the hashed prefix is the rule catalog
//! (`RuleCatalog`), which spans the whole `.mm0` and is consulted for
//! "rule declared later" diagnostics. What those lookups found is recorded
//! per entry and re-verified on a hit.
//!
//! Positions: proof offsets shift when an earlier body changes length, so
//! an entry's spans are relocated by the block's displacement. A span
//! outside the block is not relocatable, be it in the `.auf` or the `.mm0`
//! text, and makes the block unrecordable (it is simply re-checked each
//! run). The only `.mm0` span a check reports is the declaration of a rule
//! declared later.
//!
//! Parsing: a replayed block's lines are not needed, so the memo also
//! tells the proof parser which bodies it knows (`knownBodies`), and the
//! parser passes over them. It needs the body's length before any key can
//! be had, hence the index by header alone (`by_header`).
//!
//! The memo is opt-in through `CompilerContext.check_memo`; the compile
//! path never sets it, so MMB output is untouched.

const std = @import("std");
const ArenaAllocator = @import("../arena_allocator.zig").ArenaAllocator;
const CompilerDiag = @import("../diag.zig");
const Diagnostic = CompilerDiag.Diagnostic;
const Span = @import("../proof_script.zig").Span;
const ProofBlock = @import("../proof_script.zig").ProofBlock;
const KnownBodies = @import("../proof_script.zig").KnownBodies;
const scanToStatementEnd = @import("../../trusted/parse.zig").scanToStatementEnd;
const Metadata = @import("./metadata.zig");
const RuleCatalog = @import("./rule_catalog.zig");
const Context = @import("./context.zig");
const CompilerContext = Context.CompilerContext;
const HoleInference = Context.HoleInference;
const FilledAssertion = Context.FilledAssertion;

pub const CheckMemo = struct {
    pub const Key = struct {
        fingerprint: u64,
        body: u64,
    };

    /// One rule-catalog lookup a check made, with what it saw: whether the
    /// `.mm0` declares the rule later.
    pub const CatalogLookup = struct {
        name: []const u8,
        later: bool,
    };

    /// A run that found or recorded an entry: the run's number and the root
    /// it was for.
    pub const Use = struct {
        root: u64,
        run: u32,
    };

    pub const Entry = struct {
        arena: ArenaAllocator,
        /// At most one per root, its latest.
        uses: std.ArrayListUnmanaged(Use) = .empty,
        /// Null when the check succeeded, else the error it returned.
        outcome: ?anyerror,
        /// Where the block lay in the proof text when recorded.
        block: Span,
        /// The hash of the block's header, and its body's length and hash.
        header: u64,
        body_len: usize,
        body: u64,
        primary: []const Diagnostic,
        warnings: []const Diagnostic,
        last_diagnostic: ?Diagnostic,
        holes: []const HoleInference,
        assertions: []const FilledAssertion,
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
            const sink = ctx.hole_inference_sink.?;
            for (self.holes) |hole| {
                try sink.addItemOwned(.{
                    .span = shiftSpan(hole.span, delta),
                    .expression = try sink.allocator.dupe(u8, hole.expression),
                    .partial = hole.partial,
                });
            }
            for (self.assertions) |filled| {
                try sink.addAssertionOwned(
                    shiftSpan(filled.line, delta),
                    shiftSpan(filled.assertion, delta),
                    try sink.allocator.dupe(u8, filled.text),
                );
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
        primary_count: usize,
        warning_count: usize,
        dropped_primary: usize,
        dropped_warnings: usize,
        holes: usize,
        assertions: usize,
    };

    const Domain = enum(u8) { config = 1, mm0 = 2, proof = 3 };

    allocator: std.mem.Allocator,
    entries: std.AutoHashMapUnmanaged(Key, *Entry) = .empty,
    /// For each header of a self-contained block, the entry last recorded or
    /// found for a block with it: `knownBodies`.
    by_header: std.AutoHashMapUnmanaged(u64, *Entry) = .empty,
    /// Bumped per run.
    run: u32 = 0,
    /// The root the next run is for. A host that analyses several units
    /// (an editor with several files open) names each by a root of its
    /// own, so that one unit's run keeps what another's last run used.
    root: u64 = 0,
    /// Each root's latest run. An entry is kept while the latest run of
    /// some root used it: what a run did not use, its root no longer needs.
    latest_runs: std.AutoHashMapUnmanaged(u64, u32) = .empty,
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
        self.by_header.deinit(self.allocator);
        self.latest_runs.deinit(self.allocator);
        self.lookups.deinit(self.allocator);
        self.* = undefined;
    }

    /// Start a run over `ctx`'s sources. The memo stays inactive, and every
    /// block is checked, unless the run collects exactly what an entry
    /// records: hole inferences, and neither named unknowns' values nor
    /// solver stats (whose running maximum cannot be replayed).
    pub fn beginRun(self: *CheckMemo, ctx: *const CompilerContext) void {
        self.run +%= 1;
        self.active = ctx.hole_inference_sink != null and
            ctx.unknown_value_sink == null and
            ctx.inference_stats_sink == null;
        self.fingerprint = 0;
        self.mm0_cursor = 0;
        self.proof_cursor = 0;
        self.recording = false;
        self.feed(.config, &.{@intFromBool(ctx.allow_search_placeholders)});
    }

    /// End the run. Only a run that `walked` its whole unit drops what it
    /// did not use: one stopped early keeps every entry, its own included.
    pub fn endRun(self: *CheckMemo, walked: bool) void {
        // A run that left the memo inactive used nothing of it, and drops
        // nothing.
        const used_memo = self.active;
        self.active = false;
        self.recording = false;
        if (used_memo and walked) self.dropUnused();
    }

    /// Hash `bytes` into the running fingerprint. The domain tag and the
    /// length keep differently split feeds of the same bytes distinct.
    fn feed(self: *CheckMemo, domain: Domain, bytes: []const u8) void {
        var hasher = std.hash.Wyhash.init(self.fingerprint);
        hasher.update(&[_]u8{@backingInt(domain)});
        const len: u64 = bytes.len;
        hasher.update(std.mem.asBytes(&len));
        hasher.update(bytes);
        self.fingerprint = hasher.final();
    }

    /// Hash the theory text from the cursor to `end`, a position the parser
    /// stops at: each statement, and what a check can see of the text
    /// between statements. The parser finds its statements' ends where
    /// `scanToStatementEnd` does (`MM0Parser.checkWhitechars`), so `end`
    /// lies between statements. The scan never stops inside a statement or
    /// a comment, so equal text is fed alike wherever the checks lie.
    fn syncTheory(self: *CheckMemo, mm0: []const u8, end: usize) void {
        while (self.mm0_cursor < end) {
            const start = self.mm0_cursor;
            if (std.mem.startsWith(u8, mm0[start..], "--")) {
                self.mm0_cursor = std.mem.findScalarPos(u8, mm0, start, '\n') orelse mm0.len;
                if (!seesComment(mm0[start..self.mm0_cursor])) continue;
            } else switch (mm0[start]) {
                ' ', '\n' => {
                    self.mm0_cursor += 1;
                    continue;
                },
                // The parser rejects the statement that follows.
                '\t', '\r' => self.mm0_cursor += 1,
                else => _ = scanToStatementEnd(mm0, &self.mm0_cursor),
            }
            self.feed(.mm0, mm0[start..self.mm0_cursor]);
        }
    }

    /// Whether a check can see `comment` (`--...`), written between two
    /// `.mm0` statements: a directive (`--| @...`) sets up the theory, and
    /// the parser rejects the statement after a NUL. Doc prose is for hover.
    fn seesComment(comment: []const u8) bool {
        if (std.mem.findScalar(u8, comment, 0) != null) return true;
        if (!std.mem.startsWith(u8, comment, "--|")) return false;
        return Metadata.hasDirective(&.{std.mem.trimStart(u8, comment[3..], " \t")});
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
        self.syncTheory(mm0, @min(mm0_pos, mm0.len));
        const header_end = @min(block.header_span.end, proof.len);
        if (header_end > self.proof_cursor) {
            self.feed(.proof, proof[self.proof_cursor..header_end]);
            self.proof_cursor = header_end;
        }
        const block_end = @min(block.span.end, proof.len);
        if (block_end > self.proof_cursor) self.proof_cursor = block_end;
        return .{
            .fingerprint = self.fingerprint,
            .body = block.known_body orelse
                bodyHash(proof[block.header_span.end..block.body_end]),
        };
    }

    fn bodyHash(body: []const u8) u64 {
        return std.hash.Wyhash.hash(0, body);
    }

    fn headerHash(header: []const u8) u64 {
        return std.hash.Wyhash.hash(0, header);
    }

    /// The bodies of the blocks this memo holds, for the parser to pass
    /// over: an entry found for such a block needs none of its lines.
    pub fn knownBodies(self: *CheckMemo) KnownBodies {
        return .{ .ctx = self, .findFn = findKnownBody };
    }

    fn findKnownBody(
        ctx: *anyopaque,
        header: []const u8,
        rest: []const u8,
    ) ?KnownBodies.Body {
        const self: *CheckMemo = @ptrCast(@alignCast(ctx));
        const entry = self.by_header.get(headerHash(header)) orelse return null;
        if (entry.body_len > rest.len) return null;
        const hash = bodyHash(rest[0..entry.body_len]);
        if (hash != entry.body) return null;
        return .{ .len = entry.body_len, .hash = hash };
    }

    /// Without the memory to note it, the block is parsed again next time.
    fn noteKnownBody(self: *CheckMemo, entry: *Entry) void {
        self.by_header.put(self.allocator, entry.header, entry) catch {};
    }

    /// The entry for `key`, `block`'s, whose recorded catalog lookups still
    /// hold with the parser at `mm0_pos`.
    pub fn find(
        self: *CheckMemo,
        key: Key,
        block: ProofBlock,
        catalog: *RuleCatalog.Catalog,
        mm0_pos: usize,
    ) ?*const Entry {
        const entry = self.entries.get(key) orelse {
            self.misses += 1;
            return null;
        };
        for (entry.lookups) |lookup| {
            const later = catalog.declaredLater(lookup.name, mm0_pos) != null;
            if (lookup.later != later) {
                self.misses += 1;
                return null;
            }
        }
        // An entry this run cannot mark used would be dropped at its end.
        self.noteUse(entry) catch {
            self.misses += 1;
            return null;
        };
        // The parser did not know the body, though an entry has it.
        if (block.self_contained and block.known_body == null) {
            self.noteKnownBody(entry);
        }
        self.hits += 1;
        return entry;
    }

    pub fn beginRecording(self: *CheckMemo, ctx: *const CompilerContext) Recording {
        self.lookups.clearRetainingCapacity();
        self.recording = true;
        self.recording_failed = false;
        return .{
            .primary_count = ctx.diagnostics.primary_diagnostic_count,
            .warning_count = ctx.diagnostics.warning_count,
            .dropped_primary = ctx.diagnostics.dropped_primary_diagnostic_count,
            .dropped_warnings = ctx.diagnostics.dropped_warning_count,
            .holes = ctx.hole_inference_sink.?.items.items.len,
            .assertions = ctx.hole_inference_sink.?.assertions.items.len,
        };
    }

    /// Called at the catalog lookup site while a check is being recorded.
    pub fn noteCatalogLookup(self: *CheckMemo, name: []const u8, later: bool) void {
        if (!self.recording) return;
        self.lookups.append(self.allocator, .{ .name = name, .later = later }) catch {
            self.recording_failed = true;
        };
    }

    /// Store what the check emitted since `recording`. Skipped when the
    /// output cannot be replayed faithfully: an out-of-memory outcome, a
    /// sink that overflowed, or a span outside the block.
    pub fn finishRecording(
        self: *CheckMemo,
        ctx: *const CompilerContext,
        recording: Recording,
        key: Key,
        outcome: ?anyerror,
        proof: []const u8,
        block: ProofBlock,
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
        self.record(ctx, recording, key, outcome, proof, block) catch {};
    }

    fn record(
        self: *CheckMemo,
        ctx: *const CompilerContext,
        recording: Recording,
        key: Key,
        outcome: ?anyerror,
        proof: []const u8,
        proof_block: ProofBlock,
    ) !void {
        const block = proof_block.span;
        const header = proof_block.header_span;
        const entry = try self.allocator.create(Entry);
        entry.* = .{
            .arena = ArenaAllocator.init(self.allocator),
            .outcome = outcome,
            .block = block,
            .header = headerHash(proof[header.start..header.end]),
            .body_len = proof_block.body_end - header.end,
            .body = key.body,
            .primary = &.{},
            .warnings = &.{},
            .last_diagnostic = null,
            .holes = &.{},
            .assertions = &.{},
            .lookups = &.{},
        };
        // Every early return below means the output cannot be replayed, so
        // the entry is dropped unless it reaches the table.
        var stored = false;
        defer if (!stored) self.destroyEntry(entry);
        const arena = entry.arena.allocator();

        const sink = ctx.diagnostics;
        entry.primary = try dupeDiagnostics(
            arena,
            sink.primaryDiagnostics()[recording.primary_count..],
            block,
        ) orelse return;
        entry.warnings = try dupeDiagnostics(
            arena,
            sink.warningDiagnostics()[recording.warning_count..],
            block,
        ) orelse return;
        if (sink.last_diagnostic) |diag| {
            if (!spansRecordable(diag, block)) return;
            entry.last_diagnostic = try dupeDiagnostic(arena, diag);
        }
        const holes = ctx.hole_inference_sink.?;
        const items = holes.items.items[recording.holes..];
        const copies = try arena.alloc(HoleInference, items.len);
        for (items, copies) |item, *copy| {
            if (!spanWithin(item.span, block)) return;
            copy.* = .{
                .span = item.span,
                .expression = try arena.dupe(u8, item.expression),
                .partial = item.partial,
            };
        }
        entry.holes = copies;
        const filled_items = holes.assertions.items[recording.assertions..];
        const filled_copies = try arena.alloc(FilledAssertion, filled_items.len);
        for (filled_items, filled_copies) |item, *copy| {
            if (!spanWithin(item.line, block)) return;
            copy.* = .{
                .line = item.line,
                .assertion = item.assertion,
                .text = try arena.dupe(u8, item.text),
            };
        }
        entry.assertions = filled_copies;
        const lookups = try arena.alloc(CatalogLookup, self.lookups.items.len);
        for (self.lookups.items, lookups) |lookup, *copy| {
            copy.* = .{
                .name = try arena.dupe(u8, lookup.name),
                .later = lookup.later,
            };
        }
        entry.lookups = lookups;
        try self.noteUse(entry);

        const gop = try self.entries.getOrPut(self.allocator, key);
        if (gop.found_existing) self.destroyEntry(gop.value_ptr.*);
        gop.value_ptr.* = entry;
        stored = true;
        if (proof_block.self_contained) self.noteKnownBody(entry);
    }

    fn destroyEntry(self: *CheckMemo, entry: *Entry) void {
        if (self.by_header.get(entry.header) == entry) {
            _ = self.by_header.remove(entry.header);
        }
        entry.arena.deinit();
        self.allocator.destroy(entry);
    }

    /// Mark `entry` used by this run, in place of any earlier run of the
    /// same root.
    fn noteUse(self: *CheckMemo, entry: *Entry) !void {
        for (entry.uses.items) |*use| {
            if (use.root == self.root) {
                use.run = self.run;
                return;
            }
        }
        try entry.uses.append(entry.arena.allocator(), .{
            .root = self.root,
            .run = self.run,
        });
    }

    /// The run just ended is its root's latest: the root's uses by earlier
    /// runs lapse, and an entry no root's latest run used is dropped.
    fn dropUnused(self: *CheckMemo) void {
        // Without the record of this run, every entry stays.
        self.latest_runs.put(self.allocator, self.root, self.run) catch return;
        var unused = std.ArrayListUnmanaged(Key).empty;
        defer unused.deinit(self.allocator);
        var it = self.entries.iterator();
        while (it.next()) |kv| {
            const uses = &kv.value_ptr.*.uses;
            var kept: usize = 0;
            for (uses.items) |use| {
                if (self.latest_runs.get(use.root) != use.run) continue;
                uses.items[kept] = use;
                kept += 1;
            }
            uses.shrinkRetainingCapacity(kept);
            if (kept == 0) unused.append(self.allocator, kv.key_ptr.*) catch return;
        }
        for (unused.items) |key| {
            if (self.entries.fetchRemove(key)) |removed| {
                self.destroyEntry(removed.value);
            }
        }
    }
};

fn spanWithin(span: Span, block: Span) bool {
    return span.start >= block.start and span.end <= block.end and
        span.start <= span.end;
}

fn spanRecordable(source: CompilerDiag.DiagnosticSource, span: ?Span, block: Span) bool {
    const actual = span orelse return true;
    return source == .proof and spanWithin(actual, block);
}

fn spansRecordable(diag: Diagnostic, block: Span) bool {
    if (!spanRecordable(diag.source, diag.span, block)) return false;
    for (diag.noteSlice()) |note| {
        if (!spanRecordable(note.source, note.span, block)) return false;
    }
    for (diag.relatedSlice()) |related| {
        if (!spanRecordable(related.source, related.span, block)) return false;
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

/// Every span of a recorded diagnostic lies in the block.
fn relocateDiagnostic(diag: Diagnostic, delta: i64) Diagnostic {
    var out = diag;
    out.span = shiftOptionalSpan(out.span, delta);
    for (out.notes[0..out.note_count]) |*note| {
        note.span = shiftOptionalSpan(note.span, delta);
    }
    for (out.related[0..out.related_count]) |*related| {
        related.span = shiftSpan(related.span, delta);
    }
    return out;
}

/// Null when a diagnostic cannot be relocated.
fn dupeDiagnostics(
    arena: std.mem.Allocator,
    diagnostics: []const Diagnostic,
    block: Span,
) !?[]const Diagnostic {
    const copies = try arena.alloc(Diagnostic, diagnostics.len);
    for (diagnostics, copies) |diag, *copy| {
        if (!spansRecordable(diag, block)) return null;
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
            const info = @typeInfo(Payload).@"struct";
            inline for (info.field_names, info.field_types) |name, field_type| {
                if (field_type == []const u8) {
                    @field(copy, name) =
                        try arena.dupe(u8, @field(payload, name));
                } else if (field_type == ?[]const u8) {
                    @field(copy, name) =
                        try dupeOptional(arena, @field(payload, name));
                } else if (comptime holdsPointer(field_type)) {
                    @compileError("flatten " ++ @typeName(U) ++ "." ++
                        @tagName(tag) ++ "." ++ name ++
                        ": only top-level string fields are copied");
                }
            }
            return @unionInit(U, @tagName(tag), copy);
        },
    }
}

fn holdsPointer(comptime T: type) bool {
    return switch (@typeInfo(T)) {
        .pointer => true,
        .optional => |info| holdsPointer(info.child),
        .array => |info| holdsPointer(info.child),
        .@"struct" => |info| for (info.field_types) |field_type| {
            if (holdsPointer(field_type)) break true;
        } else false,
        .@"union" => |info| for (info.field_types) |field_type| {
            if (holdsPointer(field_type)) break true;
        } else false,
        else => false,
    };
}

test "relocation shifts every span" {
    var diag: Diagnostic = .{
        .kind = .unknown_rule,
        .err = error.UnknownRule,
        .source = .proof,
        .span = .{ .start = 10, .end = 14 },
    };
    CompilerDiag.addNote(&diag, .rule_declared_later, .proof, .{ .start = 3, .end = 5 });
    CompilerDiag.addNote(&diag, .rule_declared_later, .mm0, null);
    CompilerDiag.addRelated(&diag, .rule_declaration_here, .proof, .{ .start = 2, .end = 4 });
    const moved = relocateDiagnostic(diag, 5);
    try std.testing.expectEqual(@as(usize, 15), moved.span.?.start);
    try std.testing.expectEqual(@as(usize, 8), moved.notes[0].span.?.start);
    try std.testing.expectEqual(null, moved.notes[1].span);
    try std.testing.expectEqual(@as(usize, 7), moved.related[0].span.start);
    const back = relocateDiagnostic(moved, -5);
    try std.testing.expectEqual(@as(usize, 10), back.span.?.start);
}

test "spans outside the block are not recordable" {
    const block: Span = .{ .start = 100, .end = 200 };
    const inside: Diagnostic = .{
        .kind = .unknown_rule,
        .err = error.UnknownRule,
        .source = .proof,
        .span = .{ .start = 100, .end = 200 },
    };
    try std.testing.expect(spansRecordable(inside, block));
    // A span of the theory text, wherever it lies.
    var theory = inside;
    CompilerDiag.addRelated(&theory, .rule_declaration_here, .mm0, .{ .start = 100, .end = 120 });
    try std.testing.expect(!spansRecordable(theory, block));
    var earlier = inside;
    earlier.span = .{ .start = 90, .end = 110 };
    try std.testing.expect(!spansRecordable(earlier, block));
}

/// The fingerprint of a theory's text up to each position in `stops`.
fn theoryFingerprint(mm0: []const u8, stops: []const usize) u64 {
    var memo = CheckMemo.init(std.testing.allocator);
    defer memo.deinit();
    for (stops) |stop| memo.syncTheory(mm0, stop);
    memo.syncTheory(mm0, mm0.len);
    return memo.fingerprint;
}

test "the fingerprint covers what a check can see of the theory" {
    const base = "sort s;\n--| @vars x\nterm c: s; -- $ ; $\nterm d: s;";
    const same = [_][]const u8{
        "-- head; $ \n\nsort s;\n--| @vars x\nterm c: s; -- $ ; $\nterm d: s;",
        "sort s;--| @vars x\nterm c: s;\n--| prose\n--|\n\nterm d: s;\n  -- end",
        "--\tno tab\r\nsort s;\n --| @vars x\nterm c: s;--\nterm d: s; ",
    };
    const other = [_][]const u8{
        // A statement's own text, its comments included.
        "sort s;\n--| @vars x\nterm c: s; -- $ ; $\nterm d:  s;",
        "sort s;\n--| @vars x\nterm c: s; -- $ ; $\nterm -- d\n d: s;",
        // Directives, and where they stand.
        "sort s;\nterm c: s; -- $ ; $\nterm d: s;",
        "sort s;\n--| @vars y\nterm c: s; -- $ ; $\nterm d: s;",
        "--| @vars x\nsort s;\nterm c: s; -- $ ; $\nterm d: s;",
        "sort s;\n--|@vars x\n--| \t @auto\nterm c: s; -- $ ; $\nterm d: s;",
        // Bytes the parser rejects.
        "sort s;\n--| @vars x\n\tterm c: s; -- $ ; $\nterm d: s;",
        "sort s;\n--| @vars x\n\rterm c: s; -- $ ; $\nterm d: s;",
        "sort s;\n--| @vars x\nterm c: s; -- \x00\nterm d: s;",
        "sort s;\n--| @vars x\n\x00term c: s; -- $ ; $\nterm d: s;",
    };
    const expected = theoryFingerprint(base, &.{});
    for (same) |text| try std.testing.expectEqual(expected, theoryFingerprint(text, &.{}));
    for (other, 0..) |text, i| {
        const actual = theoryFingerprint(text, &.{});
        try std.testing.expect(actual != expected);
        for (other[0..i]) |earlier| {
            try std.testing.expect(actual != theoryFingerprint(earlier, &.{}));
        }
    }
    // Wherever the checks lie.
    for (0..base.len + 1) |stop| {
        try std.testing.expectEqual(expected, theoryFingerprint(base, &.{stop}));
    }
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
    var arena = ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const copy = try dupeDiagnostic(arena.allocator(), diag);
    text[0] = 'z';
    try std.testing.expectEqualStrings("abc", copy.rule_name.?);
    try std.testing.expectEqualStrings("abc", copy.detail.name_suggestion.suggestion);
    try std.testing.expectEqualStrings("abc", copy.notes[0].message.already_matched.text);
}

test "dupeDiagnostic copies a cited hypothesis name" {
    var text = [_]u8{ 'h', 'a', 'b' };
    const diag: Diagnostic = .{
        .kind = .hypothesis_mismatch,
        .err = error.HypothesisMismatch,
        .detail = .{ .premise_mismatch = .{ .premise = 1, .hypothesis_name = &text } },
    };
    var arena = ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const copy = try dupeDiagnostic(arena.allocator(), diag);
    text[0] = 'z';
    try std.testing.expectEqualStrings("hab", copy.detail.premise_mismatch.hypothesis_name.?);
}
