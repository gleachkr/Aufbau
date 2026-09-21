//! Multi-file `.mm0` sources: `import "file";` scanning and joining.
//!
//! `import` is not part of MM0 (mm0-c never sees it); mm0-rs resolves it by
//! textual inclusion (`mm0-rs join`). This module reproduces those
//! semantics in the frontend so the trusted parser keeps seeing a single
//! source string:
//!
//! - imports are resolved relative to the importing file, depth first, in
//!   post-order: an imported file's text replaces the `import` statement;
//! - a file already joined is not joined again (a diamond A -> {B, C} -> D
//!   includes D once, where it is first reached);
//! - an import cycle is an error.
//!
//! The joined text comes with a [`SourceMap`] that maps joined offsets back
//! to (file, offset) so diagnostics can name the file they belong to. How a
//! file is found is the caller's business: the [`Resolver`] is injected
//! (filesystem for the CLI, a host callback for the editor).
//!
//! Proof files (`.auf`) get the same treatment with `include "file";`, a
//! line-level item that splices a file of proof-local items (lemmas, local
//! defs, notation) at that position. Includes are not deduplicated: an item
//! is anchored where its `include` sits, so including a file twice is
//! including its items twice. Cycles are still an error.
const std = @import("std");
const builtin = @import("builtin");

pub const Span = struct {
    start: usize,
    end: usize,
};

/// One `import "spec";` (`.mm0`) or `include "spec";` (`.auf`) statement
/// in a source text.
pub const ImportStmt = struct {
    /// The whole statement, keyword through `;`.
    span: Span,
    /// The string contents (no quotes).
    spec: []const u8,
    /// The quoted string, quotes included.
    spec_span: Span,
};

pub const ScanError = error{
    /// The keyword not followed by a `"..."` string and a `;`.
    MalformedImport,
    /// The `"..."` string of a statement never closes.
    UnterminatedString,
} || std.mem.Allocator.Error;

/// Which file kind a scanner or joiner works on. The two differ in the
/// statement it looks for and in how the rest of the text is skipped:
/// `.mm0` statements end at `;` (so `import` may sit anywhere a statement
/// may), `.auf` items are line based (so `include` must start a line).
pub const Syntax = enum {
    mm0,
    auf,

    pub fn keyword(self: Syntax) []const u8 {
        return switch (self) {
            .mm0 => "import",
            .auf => "include",
        };
    }
};

pub const Scanner = struct {
    src: []const u8,
    syntax: Syntax,
    pos: usize = 0,
    /// The span of the token a scan error refers to.
    error_span: ?Span = null,

    pub fn init(src: []const u8, syntax: Syntax) Scanner {
        return .{ .src = src, .syntax = syntax };
    }

    /// Advance to the next `import`/`include` statement and return it,
    /// skipping everything else. Returns null at end of input. An
    /// unterminated `$...$` math string ends the scan (the rest of the text
    /// is left for the real parser to diagnose).
    pub fn next(self: *Scanner) ScanError!?ImportStmt {
        switch (self.syntax) {
            .mm0 => while (true) {
                self.skipWhitespaceAndComments();
                if (self.pos >= self.src.len) return null;
                if (std.mem.eql(u8, self.peekWord(), "import")) {
                    return try self.parseImport();
                }
                self.skipStatement();
            },
            .auf => while (true) {
                if (self.pos != 0 and self.src[self.pos - 1] != '\n') {
                    self.skipLine();
                }
                if (self.pos >= self.src.len) return null;
                self.skipHorizontalSpace();
                if (self.startsInclude()) return try self.parseImport();
                self.skipLine();
            },
        }
    }

    /// `include` followed by a `"`: a line whose first word is `include`
    /// but which is not followed by a string is an ordinary item (a
    /// theorem block may be named `include`).
    fn startsInclude(self: *const Scanner) bool {
        if (!std.mem.eql(u8, self.peekWord(), "include")) return false;
        var i = self.pos + "include".len;
        while (i < self.src.len and (self.src[i] == ' ' or self.src[i] == '\t')) {
            i += 1;
        }
        return i < self.src.len and self.src[i] == '"';
    }

    fn parseImport(self: *Scanner) ScanError!ImportStmt {
        const start = self.pos;
        self.pos += self.syntax.keyword().len;
        self.skipWhitespaceAndComments();
        if (self.pos >= self.src.len or self.src[self.pos] != '"') {
            self.error_span = .{ .start = start, .end = self.pos };
            return error.MalformedImport;
        }
        const quote_start = self.pos;
        self.pos += 1;
        while (self.pos < self.src.len and self.src[self.pos] != '"') {
            self.pos += 1;
        }
        if (self.pos >= self.src.len) {
            self.error_span = .{ .start = quote_start, .end = self.src.len };
            return error.UnterminatedString;
        }
        const spec = self.src[quote_start + 1 .. self.pos];
        self.pos += 1;
        const quote_end = self.pos;
        self.skipWhitespaceAndComments();
        if (self.pos >= self.src.len or self.src[self.pos] != ';') {
            self.error_span = .{ .start = start, .end = quote_end };
            return error.MalformedImport;
        }
        self.pos += 1;
        return .{
            .span = .{ .start = start, .end = self.pos },
            .spec = spec,
            .spec_span = .{ .start = quote_start, .end = quote_end },
        };
    }

    /// Skip to just past the next statement-terminating `;`, stepping over
    /// `$...$` math strings (which may contain `;`) and comments.
    fn skipStatement(self: *Scanner) void {
        while (self.pos < self.src.len) {
            const ch = self.src[self.pos];
            if (ch == '$') {
                self.skipMathString();
            } else if (ch == '-' and
                self.pos + 1 < self.src.len and
                self.src[self.pos + 1] == '-')
            {
                self.skipWhitespaceAndComments();
            } else {
                self.pos += 1;
                if (ch == ';') return;
            }
        }
    }

    /// Skip to the start of the next line, stepping over `$...$` math
    /// strings (which may span lines) and comments.
    fn skipLine(self: *Scanner) void {
        while (self.pos < self.src.len) {
            const ch = self.src[self.pos];
            if (ch == '$') {
                self.skipMathString();
            } else if (ch == '-' and
                self.pos + 1 < self.src.len and
                self.src[self.pos + 1] == '-')
            {
                while (self.pos < self.src.len and self.src[self.pos] != '\n') {
                    self.pos += 1;
                }
            } else {
                self.pos += 1;
                if (ch == '\n') return;
            }
        }
    }

    /// At a `$`: skip past the closing `$`. An unterminated string consumes
    /// the rest of the input, which ends the scan.
    fn skipMathString(self: *Scanner) void {
        self.pos += 1;
        while (self.pos < self.src.len and self.src[self.pos] != '$') {
            self.pos += 1;
        }
        if (self.pos < self.src.len) self.pos += 1;
    }

    fn skipHorizontalSpace(self: *Scanner) void {
        while (self.pos < self.src.len and
            (self.src[self.pos] == ' ' or self.src[self.pos] == '\t'))
        {
            self.pos += 1;
        }
    }

    fn skipWhitespaceAndComments(self: *Scanner) void {
        while (self.pos < self.src.len) {
            const ch = self.src[self.pos];
            if (ch == ' ' or ch == '\t' or ch == '\n' or ch == '\r') {
                self.pos += 1;
            } else if (ch == '-' and
                self.pos + 1 < self.src.len and
                self.src[self.pos + 1] == '-')
            {
                while (self.pos < self.src.len and self.src[self.pos] != '\n') {
                    self.pos += 1;
                }
            } else break;
        }
    }

    fn peekWord(self: *const Scanner) []const u8 {
        var end = self.pos;
        while (end < self.src.len and isWordChar(self.src[end])) : (end += 1) {}
        return self.src[self.pos..end];
    }

    fn isWordChar(ch: u8) bool {
        return std.ascii.isAlphanumeric(ch) or ch == '_';
    }
};

/// Does `src` contain any `import` statement? Cheap pre-check so a
/// single-file source is passed through untouched.
pub fn hasImports(src: []const u8) bool {
    var scanner = Scanner.init(src, .mm0);
    const first = scanner.next() catch return true;
    return first != null;
}

/// A file the resolver handed back.
pub const Resolved = struct {
    /// Identity of the file: two imports naming the same file must produce
    /// equal keys (the CLI uses the canonical path). Also the display name
    /// used in diagnostics.
    key: []const u8,
    text: []const u8,
};

/// How an import spec is turned into a file. `from_key` is the key of the
/// importing file (`Resolved.key`, or the root key), so relative specs can
/// be resolved against it.
pub const Resolver = struct {
    ctx: *anyopaque,
    resolveFn: *const fn (
        ctx: *anyopaque,
        allocator: std.mem.Allocator,
        from_key: []const u8,
        spec: []const u8,
    ) anyerror!Resolved,

    pub fn resolve(
        self: Resolver,
        allocator: std.mem.Allocator,
        from_key: []const u8,
        spec: []const u8,
    ) anyerror!Resolved {
        return self.resolveFn(self.ctx, allocator, from_key, spec);
    }
};

/// One file of a join, in post-order (imports before importers, a root
/// after everything it pulls in).
pub const File = struct {
    key: []const u8,
    text: []const u8,
};

pub const Location = struct {
    file_index: usize,
    offset: usize,
};

/// A contiguous run of the joined text copied verbatim from one file.
pub const Segment = struct {
    joined_start: usize,
    len: usize,
    /// Index into `Joined.files`, or null for separator bytes the joiner
    /// inserted itself.
    file_index: ?usize,
    file_offset: usize,
};

pub const SourceMap = struct {
    segments: []const Segment,

    /// The file position a joined offset came from. Separator bytes and
    /// offsets past the end map to the nearest preceding file byte.
    pub fn locate(self: SourceMap, joined_offset: usize) ?Location {
        var best: ?Location = null;
        for (self.segments) |seg| {
            if (seg.joined_start > joined_offset) break;
            if (seg.file_index) |file_index| {
                const rel = @min(joined_offset - seg.joined_start, seg.len);
                best = .{ .file_index = file_index, .offset = seg.file_offset + rel };
            }
        }
        return best;
    }

    /// Translate a joined span into its file; a span that straddles files
    /// is clipped to the file its start lies in.
    pub fn locateSpan(self: SourceMap, span: Span) ?struct {
        file_index: usize,
        span: Span,
    } {
        const start = self.locate(span.start) orelse return null;
        const len = span.end -| span.start;
        var end = start.offset + len;
        for (self.segments) |seg| {
            if (seg.joined_start > span.start) break;
            if (seg.joined_start + seg.len > span.start) {
                end = @min(end, seg.file_offset + seg.len);
                break;
            }
        }
        return .{
            .file_index = start.file_index,
            .span = .{ .start = start.offset, .end = @max(end, start.offset) },
        };
    }

    /// The joined offset a file position was copied to, or null when the
    /// position lies inside an import/include statement (which the joined
    /// text does not contain). A position at the very end of a file maps
    /// to the end of its last run.
    pub fn joinedOffset(
        self: SourceMap,
        file_index: usize,
        file_offset: usize,
    ) ?usize {
        var last: ?Segment = null;
        for (self.segments) |seg| {
            if (seg.file_index != file_index) continue;
            if (file_offset >= seg.file_offset and
                file_offset < seg.file_offset + seg.len)
            {
                return seg.joined_start + (file_offset - seg.file_offset);
            }
            last = seg;
        }
        const seg = last orelse return null;
        if (file_offset == seg.file_offset + seg.len) {
            return seg.joined_start + seg.len;
        }
        return null;
    }
};

pub const JoinErrorKind = enum {
    cycle,
    unresolved,
    malformed,
};

/// Where a join failed: the import/include statement (in `file_key`'s own
/// text) that could not be followed.
pub const JoinFailure = struct {
    kind: JoinErrorKind,
    /// Whether the failing statement is an `import` or an `include`.
    syntax: Syntax = .mm0,
    file_key: []const u8,
    file_text: []const u8,
    span: Span,
    /// The spec of the failing import (for `cycle`/`unresolved`).
    spec: []const u8,
    /// The resolver's error, for `unresolved`.
    err: ?anyerror = null,

    /// The failure as one line of prose, without a location.
    pub fn message(
        self: JoinFailure,
        allocator: std.mem.Allocator,
    ) std.mem.Allocator.Error![]u8 {
        const keyword = self.syntax.keyword();
        return switch (self.kind) {
            .cycle => std.fmt.allocPrint(
                allocator,
                "{s} cycle: '{s}' is already being {s}d",
                .{ keyword, self.spec, keyword },
            ),
            .unresolved => std.fmt.allocPrint(
                allocator,
                "unable to {s} '{s}': {s}",
                .{
                    keyword,
                    self.spec,
                    if (self.err) |err| @errorName(err) else "unresolved",
                },
            ),
            .malformed => std.fmt.allocPrint(
                allocator,
                "malformed {s} statement",
                .{keyword},
            ),
        };
    }
};

pub const JoinError = error{
    ImportCycle,
    ImportUnresolved,
    MalformedImport,
} || std.mem.Allocator.Error;

pub const Joined = struct {
    /// The joined text. When a single root has no imports this is the root
    /// text itself (not owned); otherwise a buffer owned by `arena`.
    text: []const u8,
    map: SourceMap,
    /// Post-order file list; `map` file indices point into it.
    files: []const File,

    /// Is the joined text exactly the root text (one root, no imports)?
    pub fn isPassthrough(self: Joined) bool {
        return self.files.len == 1 and self.map.segments.len == 1 and
            self.map.segments[0].len == self.text.len;
    }
};

/// `text` with every import/include statement replaced by spaces, so a
/// host that could not follow them can still parse the rest of the file
/// with positions unchanged. Scanning stops at a malformed statement, which
/// stays in place for the parser to report.
pub fn blankStatements(
    allocator: std.mem.Allocator,
    syntax: Syntax,
    text: []const u8,
) std.mem.Allocator.Error![]u8 {
    const out = try allocator.dupe(u8, text);
    var scanner = Scanner.init(text, syntax);
    while (true) {
        const stmt = scanner.next() catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            else => break,
        } orelse break;
        @memset(out[stmt.span.start..stmt.span.end], ' ');
    }
    return out;
}

/// A one-file join: `text` with an identity map. Hosts fall back to this
/// when a join fails (typically with `blankStatements` applied), so the
/// root can still be analysed on its own.
pub fn single(
    allocator: std.mem.Allocator,
    key: []const u8,
    text: []const u8,
) std.mem.Allocator.Error!Joined {
    const files = try allocator.alloc(File, 1);
    files[0] = .{ .key = key, .text = text };
    const segments = try allocator.alloc(Segment, 1);
    segments[0] = .{
        .joined_start = 0,
        .len = text.len,
        .file_index = 0,
        .file_offset = 0,
    };
    return .{ .text = text, .map = .{ .segments = segments }, .files = files };
}

/// Join `root_text` (identified by `root_key`) with everything it imports.
/// All allocations come from `allocator`; the caller typically passes an
/// arena. On error, `failure` (when non-null) says which import failed.
pub fn join(
    allocator: std.mem.Allocator,
    resolver: Resolver,
    root_key: []const u8,
    root_text: []const u8,
    failure: ?*?JoinFailure,
) JoinError!Joined {
    return joinAll(
        allocator,
        resolver,
        .mm0,
        &.{.{ .key = root_key, .text = root_text }},
        failure,
    );
}

/// Join several roots in order, each with everything it pulls in, a
/// newline between roots. `.mm0` roots follow `import` with
/// deduplication; `.auf` roots follow `include` without it (the paired
/// proof files of a join are the roots on that side). A single root
/// without statements is passed through untouched.
pub fn joinAll(
    allocator: std.mem.Allocator,
    resolver: Resolver,
    syntax: Syntax,
    roots: []const File,
    failure: ?*?JoinFailure,
) JoinError!Joined {
    var joiner = Joiner{
        .allocator = allocator,
        .resolver = resolver,
        .syntax = syntax,
        .failure = failure,
        .passthrough = roots.len == 1,
    };
    defer joiner.deinit();
    for (roots, 0..) |root, index| {
        if (index != 0 and (joiner.out.items.len == 0 or
            joiner.out.items[joiner.out.items.len - 1] != '\n'))
        {
            try joiner.emitSeparator();
        }
        try joiner.write(root.key, root.text, true);
    }
    const files = try joiner.files.toOwnedSlice(allocator);
    const segments = try joiner.segments.toOwnedSlice(allocator);
    return .{
        .text = if (joiner.passthrough)
            roots[0].text
        else
            try joiner.out.toOwnedSlice(allocator),
        .map = .{ .segments = segments },
        .files = files,
    };
}

const Joiner = struct {
    allocator: std.mem.Allocator,
    resolver: Resolver,
    syntax: Syntax,
    failure: ?*?JoinFailure,
    out: std.ArrayListUnmanaged(u8) = .{},
    files: std.ArrayListUnmanaged(File) = .{},
    segments: std.ArrayListUnmanaged(Segment) = .{},
    /// Keys of files being joined or already joined (mm0-rs `working`).
    working: std.StringHashMapUnmanaged(void) = .{},
    /// Keys on the current import path (mm0-rs `stack`), for cycles.
    stack: std.ArrayListUnmanaged([]const u8) = .{},
    /// True while a single root has shown no statement: its text can be
    /// reused.
    passthrough: bool,

    fn deinit(self: *Joiner) void {
        self.out.deinit(self.allocator);
        self.files.deinit(self.allocator);
        self.segments.deinit(self.allocator);
        self.working.deinit(self.allocator);
        self.stack.deinit(self.allocator);
    }

    fn write(
        self: *Joiner,
        key: []const u8,
        text: []const u8,
        is_root: bool,
    ) JoinError!void {
        try self.stack.append(self.allocator, key);
        defer _ = self.stack.pop();
        if (is_root and self.syntax == .mm0) {
            try self.working.put(self.allocator, key, {});
        }

        // Files are numbered in post-order, so this file's index is only
        // known once its imports are done; segments record it via a
        // placeholder patched below.
        var pending: std.ArrayListUnmanaged(usize) = .{};
        defer pending.deinit(self.allocator);

        var scanner = Scanner.init(text, self.syntax);
        var start: usize = 0;
        while (true) {
            const stmt = scanner.next() catch |err| switch (err) {
                error.OutOfMemory => return error.OutOfMemory,
                else => {
                    self.fail(.{
                        .kind = .malformed,
                        .file_key = key,
                        .file_text = text,
                        .span = scanner.error_span orelse
                            .{ .start = scanner.pos, .end = scanner.pos },
                        .spec = "",
                    });
                    return error.MalformedImport;
                },
            } orelse break;
            self.passthrough = false;
            try self.emit(&pending, text, start, stmt.span.start);
            start = stmt.span.end;

            const resolved = self.resolver.resolve(
                self.allocator,
                key,
                stmt.spec,
            ) catch |err| {
                if (err == error.OutOfMemory) return error.OutOfMemory;
                self.fail(.{
                    .kind = .unresolved,
                    .file_key = key,
                    .file_text = text,
                    .span = stmt.spec_span,
                    .spec = stmt.spec,
                    .err = err,
                });
                return error.ImportUnresolved;
            };
            for (self.stack.items) |on_path| {
                if (std.mem.eql(u8, on_path, resolved.key)) {
                    self.fail(.{
                        .kind = .cycle,
                        .file_key = key,
                        .file_text = text,
                        .span = stmt.spec_span,
                        .spec = stmt.spec,
                    });
                    return error.ImportCycle;
                }
            }
            if (self.syntax == .mm0) {
                const gop = try self.working.getOrPut(self.allocator, resolved.key);
                if (gop.found_existing) continue;
            }
            try self.write(resolved.key, resolved.text, false);
            // Keep the importer's text out of a trailing comment in the
            // imported file (mm0-rs does the same in comments mode).
            if (resolved.text.len == 0 or
                resolved.text[resolved.text.len - 1] != '\n')
            {
                try self.emitSeparator();
            }
        }
        try self.emit(&pending, text, start, text.len);

        const file_index = self.files.items.len;
        try self.files.append(self.allocator, .{ .key = key, .text = text });
        for (pending.items) |seg_index| {
            self.segments.items[seg_index].file_index = file_index;
        }
    }

    fn emit(
        self: *Joiner,
        pending: *std.ArrayListUnmanaged(usize),
        text: []const u8,
        from: usize,
        to: usize,
    ) JoinError!void {
        // Zero-length runs are dropped, except a whole empty file, so an
        // empty root still maps.
        if (to == from and !(from == 0 and to == text.len)) return;
        try pending.append(self.allocator, self.segments.items.len);
        try self.segments.append(self.allocator, .{
            .joined_start = self.out.items.len,
            .len = to - from,
            .file_index = null,
            .file_offset = from,
        });
        try self.out.appendSlice(self.allocator, text[from..to]);
    }

    fn emitSeparator(self: *Joiner) JoinError!void {
        try self.segments.append(self.allocator, .{
            .joined_start = self.out.items.len,
            .len = 1,
            .file_index = null,
            .file_offset = 0,
        });
        try self.out.append(self.allocator, '\n');
    }

    fn fail(self: *Joiner, info: JoinFailure) void {
        if (self.failure) |slot| {
            if (slot.* == null) {
                slot.* = info;
                slot.*.?.syntax = self.syntax;
            }
        }
    }
};

/// Filesystem resolver for native hosts: specs resolve relative to the
/// importing file's directory; keys are canonical paths so the same file
/// reached by two routes is joined once (`.mm0`) or recognised on a cycle.
pub const FsResolver = struct {
    pub fn resolver(self: *FsResolver) Resolver {
        return .{ .ctx = @ptrCast(self), .resolveFn = resolveFn };
    }

    /// Canonical key for a root path (what `join` should be given as
    /// `root_key` so imports of the root itself are detected as cycles).
    pub fn rootKey(allocator: std.mem.Allocator, path: []const u8) ![]const u8 {
        return std.fs.cwd().realpathAlloc(allocator, path);
    }

    fn resolveFn(
        ctx: *anyopaque,
        allocator: std.mem.Allocator,
        from_key: []const u8,
        spec: []const u8,
    ) anyerror!Resolved {
        _ = ctx;
        if (builtin.os.tag == .freestanding) return error.FileNotFound;
        const dir = std.fs.path.dirname(from_key) orelse ".";
        const relative = try std.fs.path.join(allocator, &.{ dir, spec });
        const key = std.fs.cwd().realpathAlloc(allocator, relative) catch |err|
            return err;
        const text = try std.fs.cwd().readFileAlloc(
            allocator,
            key,
            std.math.maxInt(usize),
        );
        return .{ .key = key, .text = text };
    }
};

/// The path an import/include spec names, relative to the importing file's
/// directory, with `.` and `..` segments collapsed. Purely lexical: hosts
/// without a filesystem (the language server's open documents, the browser)
/// key their files by such paths, and the same form keys both.
pub fn resolveSpecPath(
    allocator: std.mem.Allocator,
    from_path: []const u8,
    spec: []const u8,
) std.mem.Allocator.Error![]const u8 {
    const base = if (std.fs.path.isAbsolutePosix(spec))
        ""
    else
        std.fs.path.dirnamePosix(from_path) orelse "";
    const absolute = std.fs.path.isAbsolutePosix(spec) or
        std.fs.path.isAbsolutePosix(base);

    var parts = std.ArrayListUnmanaged([]const u8){};
    defer parts.deinit(allocator);
    const sources = [_][]const u8{ base, spec };
    for (sources) |source| {
        var it = std.mem.splitScalar(u8, source, '/');
        while (it.next()) |part| {
            if (part.len == 0 or std.mem.eql(u8, part, ".")) continue;
            if (std.mem.eql(u8, part, "..")) {
                if (parts.items.len != 0 and
                    !std.mem.eql(u8, parts.items[parts.items.len - 1], ".."))
                {
                    _ = parts.pop();
                    continue;
                }
                if (absolute) continue;
            }
            try parts.append(allocator, part);
        }
    }

    var out = std.ArrayListUnmanaged(u8){};
    if (absolute) try out.append(allocator, '/');
    for (parts.items, 0..) |part, index| {
        if (index != 0) try out.append(allocator, '/');
        try out.appendSlice(allocator, part);
    }
    if (out.items.len == 0) try out.append(allocator, '.');
    return try out.toOwnedSlice(allocator);
}

/// Resolver over an in-memory file table for hosts without a filesystem
/// (the browser compiler). Keys are lexical paths; a spec resolves against
/// the importing file's key with `resolveSpecPath`, so the host must key
/// its files in that normalised form (`/dir/file.mm0`, no `.` or `..`).
pub const TableResolver = struct {
    files: []const File,

    pub fn resolver(self: *TableResolver) Resolver {
        return .{ .ctx = @ptrCast(self), .resolveFn = resolveFn };
    }

    pub fn get(self: TableResolver, key: []const u8) ?File {
        for (self.files) |file| {
            if (std.mem.eql(u8, file.key, key)) return file;
        }
        return null;
    }

    fn resolveFn(
        ctx: *anyopaque,
        allocator: std.mem.Allocator,
        from_key: []const u8,
        spec: []const u8,
    ) anyerror!Resolved {
        const self: *TableResolver = @ptrCast(@alignCast(ctx));
        const path = try resolveSpecPath(allocator, from_key, spec);
        const file = self.get(path) orelse return error.FileNotFound;
        return .{ .key = file.key, .text = file.text };
    }
};

/// `loadPair` over an in-memory table (see `TableResolver` for the keys).
/// `root_key` names the root `.mm0`; its proof file is `proof_key` when
/// given, else its `<stem>.auf` sibling when the table holds one. Every
/// other joined file pairs with its sibling. Labels are the keys.
pub fn loadPairFromTable(
    allocator: std.mem.Allocator,
    files: []const File,
    root_key: []const u8,
    proof_key: ?[]const u8,
    failure: *?LoadFailure,
) LoadPairError!LoadedPair {
    var table = TableResolver{ .files = files };
    const root = table.get(root_key) orelse {
        failure.* = .{ .read = .{ .path = root_key, .err = error.FileNotFound } };
        return error.ReadFailed;
    };
    var join_failure: ?JoinFailure = null;
    const joined = join(
        allocator,
        table.resolver(),
        root.key,
        root.text,
        &join_failure,
    ) catch |err| {
        if (join_failure) |info| failure.* = .{ .join = info };
        return err;
    };
    const mm0_mapping = try Mapping.fromJoined(
        allocator,
        joined,
        keyLabel,
        @ptrCast(&label_ctx),
    );

    var proof_files: std.ArrayListUnmanaged(File) = .{};
    for (joined.files, 0..) |file, index| {
        const is_root = index + 1 == joined.files.len;
        if (is_root and proof_key != null) {
            const proof = table.get(proof_key.?) orelse {
                failure.* = .{
                    .read = .{ .path = proof_key.?, .err = error.FileNotFound },
                };
                return error.ReadFailed;
            };
            try proof_files.append(allocator, proof);
            continue;
        }
        const sibling = proofSibling(allocator, file.key) catch continue;
        const paired = table.get(sibling) orelse continue;
        try proof_files.append(allocator, paired);
    }
    if (proof_files.items.len == 0) {
        return .{
            .mm0 = joined,
            .mm0_mapping = mm0_mapping,
            .proof = null,
            .proof_mapping = null,
        };
    }
    join_failure = null;
    const proof_joined = joinAll(
        allocator,
        table.resolver(),
        .auf,
        proof_files.items,
        &join_failure,
    ) catch |err| {
        if (join_failure) |info| failure.* = .{ .join = info };
        return err;
    };
    return .{
        .mm0 = joined,
        .mm0_mapping = mm0_mapping,
        .proof = proof_joined,
        .proof_mapping = try Mapping.fromJoined(
            allocator,
            proof_joined,
            keyLabel,
            @ptrCast(&label_ctx),
        ),
    };
}

var label_ctx: u8 = 0;

fn keyLabel(ctx: *anyopaque, key: []const u8) []const u8 {
    _ = ctx;
    return key;
}

/// A joined text plus the names its files go by in diagnostics.
pub const Mapping = struct {
    map: SourceMap,
    files: []const File,
    labels: []const []const u8,

    pub fn fromJoined(
        allocator: std.mem.Allocator,
        joined: Joined,
        labelFn: *const fn (ctx: *anyopaque, key: []const u8) []const u8,
        ctx: *anyopaque,
    ) std.mem.Allocator.Error!Mapping {
        const labels = try allocator.alloc([]const u8, joined.files.len);
        for (joined.files, 0..) |file, index| {
            labels[index] = labelFn(ctx, file.key);
        }
        return .{ .map = joined.map, .files = joined.files, .labels = labels };
    }

    pub const Located = struct {
        label: []const u8,
        text: []const u8,
        span: Span,
    };

    pub fn locateSpan(self: Mapping, span: Span) ?Located {
        const hit = self.map.locateSpan(span) orelse return null;
        return .{
            .label = self.labels[hit.file_index],
            .text = self.files[hit.file_index].text,
            .span = hit.span,
        };
    }
};

/// A root `.mm0` joined with its imports, and the `.auf` files paired with
/// every joined file (by name: `foo.mm0` <-> `foo.auf`), joined in the same
/// order with their `include`s. Native hosts only.
pub const LoadedPair = struct {
    mm0: Joined,
    mm0_mapping: Mapping,
    /// Null when no file of the join has a paired `.auf` (and none was
    /// given explicitly).
    proof: ?Joined,
    proof_mapping: ?Mapping,
};

pub const LoadPairError = JoinError || error{ReadFailed};

/// What went wrong in `loadPair` beyond the join itself.
pub const LoadFailure = union(enum) {
    join: JoinFailure,
    /// A file could not be read: the path and the error.
    read: struct { path: []const u8, err: anyerror },
};

/// Load `mm0_path` with its imports and the paired proof files. The root's
/// proof file is `proof_path` when given (it need not sit next to the
/// root); every imported file pairs with its `<stem>.auf` sibling when that
/// exists. Display labels are `mm0_path`/`proof_path` for the roots and
/// paths relative to the current directory for imports. Allocations come
/// from `allocator` (use an arena).
pub fn loadPair(
    allocator: std.mem.Allocator,
    mm0_path: []const u8,
    proof_path: ?[]const u8,
    failure: *?LoadFailure,
) LoadPairError!LoadedPair {
    if (builtin.os.tag == .freestanding) return error.ReadFailed;
    const root_text = std.fs.cwd().readFileAlloc(
        allocator,
        mm0_path,
        std.math.maxInt(usize),
    ) catch |err| {
        failure.* = .{ .read = .{ .path = mm0_path, .err = err } };
        return error.ReadFailed;
    };
    const root_key = FsResolver.rootKey(allocator, mm0_path) catch |err| {
        failure.* = .{ .read = .{ .path = mm0_path, .err = err } };
        return error.ReadFailed;
    };
    var fs = FsResolver{};
    var join_failure: ?JoinFailure = null;
    const joined = join(
        allocator,
        fs.resolver(),
        root_key,
        root_text,
        &join_failure,
    ) catch |err| {
        if (join_failure) |info| failure.* = .{ .join = info };
        return err;
    };

    const cwd = std.process.getCwdAlloc(allocator) catch "";
    var labeller = Labeller{
        .cwd = cwd,
        .root_key = root_key,
        .root_label = mm0_path,
    };
    const mm0_mapping = try Mapping.fromJoined(
        allocator,
        joined,
        Labeller.label,
        @ptrCast(&labeller),
    );

    var proof_files: std.ArrayListUnmanaged(File) = .{};
    var proof_labeller = Labeller{
        .cwd = cwd,
        .root_key = "",
        .root_label = proof_path orelse "",
    };
    for (joined.files, 0..) |file, index| {
        const is_root = index + 1 == joined.files.len;
        const explicit = is_root and proof_path != null;
        const path: []const u8 = if (explicit)
            proof_path.?
        else
            proofSibling(allocator, file.key) catch continue;
        const key = FsResolver.rootKey(allocator, path) catch |err| {
            if (!explicit and err == error.FileNotFound) continue;
            failure.* = .{ .read = .{ .path = path, .err = err } };
            return error.ReadFailed;
        };
        const text = std.fs.cwd().readFileAlloc(
            allocator,
            key,
            std.math.maxInt(usize),
        ) catch |err| {
            failure.* = .{ .read = .{ .path = path, .err = err } };
            return error.ReadFailed;
        };
        try proof_files.append(allocator, .{ .key = key, .text = text });
        if (explicit) proof_labeller.root_key = key;
    }
    if (proof_files.items.len == 0) {
        return .{
            .mm0 = joined,
            .mm0_mapping = mm0_mapping,
            .proof = null,
            .proof_mapping = null,
        };
    }
    join_failure = null;
    const proof_joined = joinAll(
        allocator,
        fs.resolver(),
        .auf,
        proof_files.items,
        &join_failure,
    ) catch |err| {
        if (join_failure) |info| failure.* = .{ .join = info };
        return err;
    };
    return .{
        .mm0 = joined,
        .mm0_mapping = mm0_mapping,
        .proof = proof_joined,
        .proof_mapping = try Mapping.fromJoined(
            allocator,
            proof_joined,
            Labeller.label,
            @ptrCast(&proof_labeller),
        ),
    };
}

const Labeller = struct {
    cwd: []const u8,
    root_key: []const u8,
    root_label: []const u8,

    fn label(ctx: *anyopaque, key: []const u8) []const u8 {
        const self: *Labeller = @ptrCast(@alignCast(ctx));
        if (self.root_key.len != 0 and std.mem.eql(u8, key, self.root_key)) {
            return self.root_label;
        }
        return displayPath(self.cwd, key);
    }
};

fn proofSibling(allocator: std.mem.Allocator, mm0_key: []const u8) ![]const u8 {
    const ext = std.fs.path.extension(mm0_key);
    return std.fmt.allocPrint(allocator, "{s}.auf", .{mm0_key[0 .. mm0_key.len - ext.len]});
}

/// Display name for a file key: the path relative to the current directory
/// when it is underneath it, else the key as is.
pub fn displayPath(cwd: []const u8, key: []const u8) []const u8 {
    if (cwd.len > 0 and std.mem.startsWith(u8, key, cwd) and
        key.len > cwd.len and key[cwd.len] == std.fs.path.sep)
    {
        return key[cwd.len + 1 ..];
    }
    return key;
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

const MemResolver = struct {
    files: []const File,

    fn resolver(self: *MemResolver) Resolver {
        return .{ .ctx = @ptrCast(self), .resolveFn = resolveFn };
    }

    fn resolveFn(
        ctx: *anyopaque,
        allocator: std.mem.Allocator,
        from_key: []const u8,
        spec: []const u8,
    ) anyerror!Resolved {
        _ = allocator;
        _ = from_key;
        const self: *MemResolver = @ptrCast(@alignCast(ctx));
        for (self.files) |file| {
            if (std.mem.eql(u8, file.key, spec)) {
                return .{ .key = file.key, .text = file.text };
            }
        }
        return error.FileNotFound;
    }
};

fn joinMem(
    arena: std.mem.Allocator,
    files: []const File,
    root_key: []const u8,
    root_text: []const u8,
    failure: *?JoinFailure,
) JoinError!Joined {
    var mem = MemResolver{ .files = files };
    return join(arena, mem.resolver(), root_key, root_text, failure);
}

fn includeMem(
    arena: std.mem.Allocator,
    files: []const File,
    roots: []const File,
    failure: *?JoinFailure,
) JoinError!Joined {
    var mem = MemResolver{ .files = files };
    return joinAll(arena, mem.resolver(), .auf, roots, failure);
}

test "table loader chains cells the way the browser editor does" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const files = [_]File{
        .{ .key = "/d/prelude.mm0", .text = "sort s;\n" },
        .{ .key = "/d/c1.mm0", .text = "import \"prelude.mm0\";\n" },
        .{ .key = "/d/c1.auf", .text = "lemma a\n" },
        .{ .key = "/d/c2.mm0", .text = "import \"c1.mm0\";\nterm t: s;\n" },
        .{ .key = "/d/c2.auf", .text = "main\n" },
    };
    var failure: ?LoadFailure = null;

    // The root pairs with its sibling when no proof key is given; every
    // earlier cell pairs with its own; the prelude has none.
    const pair = try loadPairFromTable(arena.allocator(), &files, "/d/c2.mm0", null, &failure);
    try std.testing.expectEqualStrings("sort s;\n\n\nterm t: s;\n", pair.mm0.text);
    try std.testing.expectEqual(@as(usize, 3), pair.mm0.files.len);
    try std.testing.expectEqualStrings("lemma a\nmain\n", pair.proof.?.text);
    // Labels are the keys, and a span in the joined proof lands in its file.
    const hit = pair.proof_mapping.?.locateSpan(.{ .start = 8, .end = 12 }).?;
    try std.testing.expectEqualStrings("/d/c2.auf", hit.label);
    try std.testing.expectEqual(@as(usize, 0), hit.span.start);

    // An explicit proof key overrides the sibling.
    const explicit = try loadPairFromTable(arena.allocator(), &files, "/d/c2.mm0", "/d/c1.auf", &failure);
    try std.testing.expectEqualStrings("lemma a\nlemma a\n", explicit.proof.?.text);

    // A root without any proof file yields no proof side.
    const bare = try loadPairFromTable(arena.allocator(), &files, "/d/prelude.mm0", null, &failure);
    try std.testing.expect(bare.proof == null);
}

test "table loader reports missing files and unresolved imports" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const files = [_]File{
        .{ .key = "/d/a.mm0", .text = "import \"lib/x.mm0\";\n" },
    };
    var failure: ?LoadFailure = null;
    try std.testing.expectError(
        error.ReadFailed,
        loadPairFromTable(arena.allocator(), &files, "/d/nope.mm0", null, &failure),
    );
    try std.testing.expectEqualStrings("/d/nope.mm0", failure.?.read.path);

    failure = null;
    try std.testing.expectError(
        error.ImportUnresolved,
        loadPairFromTable(arena.allocator(), &files, "/d/a.mm0", null, &failure),
    );
    try std.testing.expectEqualStrings("lib/x.mm0", failure.?.join.spec);
    try std.testing.expectEqualStrings("/d/a.mm0", failure.?.join.file_key);
    const message = try failure.?.join.message(arena.allocator());
    try std.testing.expectEqualStrings(
        "unable to import 'lib/x.mm0': FileNotFound",
        message,
    );

    const plain = [_]File{.{ .key = "/d/b.mm0", .text = "sort s;\n" }};
    failure = null;
    try std.testing.expectError(
        error.ReadFailed,
        loadPairFromTable(arena.allocator(), &plain, "/d/b.mm0", "/d/b.auf", &failure),
    );
    try std.testing.expectEqualStrings("/d/b.auf", failure.?.read.path);
}

test "import specs resolve lexically against the importing file" {
    const allocator = std.testing.allocator;
    const cases = [_]struct { from: []const u8, spec: []const u8, want: []const u8 }{
        .{ .from = "/a/b/c.mm0", .spec = "d.mm0", .want = "/a/b/d.mm0" },
        .{ .from = "/a/b/c.mm0", .spec = "../x/./y.mm0", .want = "/a/x/y.mm0" },
        .{ .from = "/a/b/c.mm0", .spec = "/abs/z.mm0", .want = "/abs/z.mm0" },
        .{ .from = "/c.mm0", .spec = "../../q.mm0", .want = "/q.mm0" },
        .{ .from = "c.mm0", .spec = "../q.mm0", .want = "../q.mm0" },
        .{ .from = "/aufbau-editor/doc3.mm0", .spec = "prelude.mm0", .want = "/aufbau-editor/prelude.mm0" },
    };
    for (cases) |case| {
        const got = try resolveSpecPath(allocator, case.from, case.spec);
        defer allocator.free(got);
        try std.testing.expectEqualStrings(case.want, got);
    }
}

test "scanner finds imports and skips other statements" {
    const src =
        \\-- import "not.mm0"; in a comment
        \\sort wff;
        \\import "a.mm0";
        \\term x: wff; -- trailing
        \\axiom ax: $ x $; -- ; in math
        \\theorem t: $ x $;
        \\  import  "b.mm0" ;
    ;
    var scanner = Scanner.init(src, .mm0);
    const a = (try scanner.next()).?;
    try std.testing.expectEqualStrings("a.mm0", a.spec);
    try std.testing.expectEqualStrings("import \"a.mm0\";", src[a.span.start..a.span.end]);
    const b = (try scanner.next()).?;
    try std.testing.expectEqualStrings("b.mm0", b.spec);
    try std.testing.expectEqualStrings("import  \"b.mm0\" ;", src[b.span.start..b.span.end]);
    try std.testing.expect((try scanner.next()) == null);
    try std.testing.expect(hasImports(src));
    try std.testing.expect(!hasImports("sort wff; axiom a: $ x ; $;"));
}

test "scanner reports malformed imports" {
    var scanner = Scanner.init("import a.mm0;", .mm0);
    try std.testing.expectError(error.MalformedImport, scanner.next());
    scanner = Scanner.init("import \"a.mm0\"", .mm0);
    try std.testing.expectError(error.MalformedImport, scanner.next());
    scanner = Scanner.init("import \"a.mm0", .mm0);
    try std.testing.expectError(error.UnterminatedString, scanner.next());
    // An unterminated math string is the parser's to report; it just ends
    // the scan.
    scanner = Scanner.init("axiom a: $ x;\nimport \"a.mm0\";", .mm0);
    try std.testing.expect((try scanner.next()) == null);
}

test "auf scanner finds includes at line starts only" {
    const src =
        \\-- include "not.auf"; in a comment
        \\include "a.auf";
        \\include
        \\-------
        \\l1: $ x $ by ax [] -- include "no.auf";
        \\l2: $ multi
        \\include "still math.auf";
        \\line $ by ax []
        \\  include  "b.auf" ; -- trailing
        \\lemma include "c.auf"; is not an item
    ;
    var scanner = Scanner.init(src, .auf);
    const a = (try scanner.next()).?;
    try std.testing.expectEqualStrings("a.auf", a.spec);
    try std.testing.expectEqualStrings("include \"a.auf\";", src[a.span.start..a.span.end]);
    const b = (try scanner.next()).?;
    try std.testing.expectEqualStrings("b.auf", b.spec);
    try std.testing.expectEqualStrings("include  \"b.auf\" ;", src[b.span.start..b.span.end]);
    try std.testing.expect((try scanner.next()) == null);

    scanner = Scanner.init("include \"a.auf\"\nfoo\n---\n", .auf);
    try std.testing.expectError(error.MalformedImport, scanner.next());
}

test "join without imports passes the root through" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const root = "sort wff;\n";
    var failure: ?JoinFailure = null;
    const joined = try joinMem(arena.allocator(), &.{}, "root", root, &failure);
    try std.testing.expect(joined.isPassthrough());
    try std.testing.expect(joined.text.ptr == root.ptr);
    try std.testing.expectEqual(@as(usize, 1), joined.files.len);
    try std.testing.expectEqualStrings("root", joined.files[0].key);
    const loc = joined.map.locate(4).?;
    try std.testing.expectEqual(@as(usize, 0), loc.file_index);
    try std.testing.expectEqual(@as(usize, 4), loc.offset);
}

test "join splices imports in post-order and dedups a diamond" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const files = [_]File{
        .{ .key = "d", .text = "sort d;" },
        .{ .key = "b", .text = "import \"d\";\nsort b;\n" },
        .{ .key = "c", .text = "import \"d\";\nsort c;\n" },
    };
    const root = "import \"b\";\nimport \"c\";\nsort a;\n";
    var failure: ?JoinFailure = null;
    const joined = try joinMem(arena.allocator(), &files, "a", root, &failure);
    try std.testing.expectEqualStrings(
        "sort d;\n\nsort b;\n\n\nsort c;\n\nsort a;\n",
        joined.text,
    );
    try std.testing.expectEqual(@as(usize, 4), joined.files.len);
    try std.testing.expectEqualStrings("d", joined.files[0].key);
    try std.testing.expectEqualStrings("b", joined.files[1].key);
    try std.testing.expectEqualStrings("c", joined.files[2].key);
    try std.testing.expectEqualStrings("a", joined.files[3].key);
    try std.testing.expect(!joined.isPassthrough());

    // "sort c;" starts at joined offset 17 and is c's offset 12.
    const c_start = std.mem.indexOf(u8, joined.text, "sort c;").?;
    const loc = joined.map.locate(c_start).?;
    try std.testing.expectEqualStrings("c", joined.files[loc.file_index].key);
    try std.testing.expectEqualStrings(
        "sort c;",
        joined.files[loc.file_index].text[loc.offset .. loc.offset + 7],
    );
    const span = joined.map.locateSpan(.{ .start = c_start, .end = c_start + 7 }).?;
    try std.testing.expectEqual(loc.file_index, span.file_index);
    try std.testing.expectEqual(loc.offset, span.span.start);
    try std.testing.expectEqual(loc.offset + 7, span.span.end);
    // The separator after "sort d;" belongs to no file: it maps to the end
    // of d.
    const sep = joined.map.locate(7).?;
    try std.testing.expectEqualStrings("d", joined.files[sep.file_index].key);
    try std.testing.expectEqual(@as(usize, 7), sep.offset);

    // The inverse map: file positions back to the joined text. Positions
    // inside an import statement have no joined counterpart.
    try std.testing.expectEqual(c_start, joined.map.joinedOffset(2, 12).?);
    const a_start = std.mem.indexOf(u8, joined.text, "sort a;").?;
    try std.testing.expectEqual(a_start, joined.map.joinedOffset(3, 24).?);
    try std.testing.expectEqual(joined.text.len, joined.map.joinedOffset(3, root.len).?);
    try std.testing.expect(joined.map.joinedOffset(3, 0) == null);
    try std.testing.expect(joined.map.joinedOffset(3, 14) == null);
    try std.testing.expect(joined.map.joinedOffset(3, root.len + 1) == null);
}

test "blankStatements spaces out imports and includes in place" {
    const mm0 = try blankStatements(std.testing.allocator, .mm0, "sort s;\nimport \"a\";\nsort t;");
    defer std.testing.allocator.free(mm0);
    try std.testing.expectEqualStrings("sort s;\n           \nsort t;", mm0);
    const auf = try blankStatements(std.testing.allocator, .auf, "include \"a.auf\";\nfoo\n---\n");
    defer std.testing.allocator.free(auf);
    try std.testing.expectEqualStrings("                \nfoo\n---\n", auf);
    // A malformed statement ends the scan and stays for the parser.
    const bad = try blankStatements(std.testing.allocator, .mm0, "import \"a\";\nimport b;");
    defer std.testing.allocator.free(bad);
    try std.testing.expectEqualStrings("           \nimport b;", bad);
}

test "single join maps identically" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const text = "sort wff;\n";
    const joined = try single(arena.allocator(), "root", text);
    try std.testing.expect(joined.isPassthrough());
    try std.testing.expect(joined.text.ptr == text.ptr);
    try std.testing.expectEqual(@as(usize, 4), joined.map.joinedOffset(0, 4).?);
    try std.testing.expectEqual(text.len, joined.map.joinedOffset(0, text.len).?);
    try std.testing.expectEqual(@as(usize, 4), joined.map.locate(4).?.offset);
}

test "join reports cycles and unresolved imports" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const files = [_]File{
        .{ .key = "a", .text = "import \"b\";\n" },
        .{ .key = "b", .text = "import \"a\";\n" },
    };
    var failure: ?JoinFailure = null;
    try std.testing.expectError(
        error.ImportCycle,
        joinMem(arena.allocator(), &files, "a", files[0].text, &failure),
    );
    try std.testing.expectEqual(JoinErrorKind.cycle, failure.?.kind);
    try std.testing.expectEqualStrings("b", failure.?.file_key);
    try std.testing.expectEqualStrings("a", failure.?.spec);

    failure = null;
    try std.testing.expectError(
        error.ImportUnresolved,
        joinMem(arena.allocator(), &files, "a", "import \"zz\";\n", &failure),
    );
    try std.testing.expectEqual(JoinErrorKind.unresolved, failure.?.kind);
    try std.testing.expectEqualStrings("zz", failure.?.spec);
    try std.testing.expectEqual(@as(anyerror, error.FileNotFound), failure.?.err.?);

    failure = null;
    try std.testing.expectError(
        error.ImportCycle,
        joinMem(arena.allocator(), &.{.{ .key = "a", .text = "" }}, "a", "import \"a\";\n", &failure),
    );

    failure = null;
    try std.testing.expectError(
        error.MalformedImport,
        joinMem(arena.allocator(), &files, "a", "sort x;\nimport b;\n", &failure),
    );
    try std.testing.expectEqual(JoinErrorKind.malformed, failure.?.kind);
    try std.testing.expectEqual(@as(usize, 8), failure.?.span.start);
}

test "include join splices in place without dedup and joins roots" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const files = [_]File{
        .{ .key = "d", .text = "lemma d\n---\n" },
        .{ .key = "b", .text = "include \"d\";\nlemma b\n---\n" },
    };
    const roots = [_]File{
        .{ .key = "p", .text = "lemma p\n---" },
        .{ .key = "r", .text = "include \"b\";\nt\n---\ninclude \"d\";\n" },
    };
    var failure: ?JoinFailure = null;
    const joined = try includeMem(arena.allocator(), &files, &roots, &failure);
    try std.testing.expectEqualStrings(
        "lemma p\n---\nlemma d\n---\n\nlemma b\n---\n\nt\n---\nlemma d\n---\n\n",
        joined.text,
    );
    // Post-order per root, d twice: p, d, b, d, r.
    try std.testing.expectEqual(@as(usize, 5), joined.files.len);
    try std.testing.expectEqualStrings("p", joined.files[0].key);
    try std.testing.expectEqualStrings("d", joined.files[1].key);
    try std.testing.expectEqualStrings("b", joined.files[2].key);
    try std.testing.expectEqualStrings("d", joined.files[3].key);
    try std.testing.expectEqualStrings("r", joined.files[4].key);
    try std.testing.expect(!joined.isPassthrough());
    const t_start = std.mem.indexOf(u8, joined.text, "t\n---").?;
    const loc = joined.map.locate(t_start).?;
    try std.testing.expectEqualStrings("r", joined.files[loc.file_index].key);
    try std.testing.expectEqual(@as(usize, "include \"b\";\n".len), loc.offset);
    const second_d = std.mem.lastIndexOf(u8, joined.text, "lemma d").?;
    try std.testing.expectEqual(@as(usize, 3), joined.map.locate(second_d).?.file_index);

    // A single root without includes is passed through.
    const one = try includeMem(arena.allocator(), &files, roots[0..1], &failure);
    try std.testing.expect(one.isPassthrough());
    try std.testing.expect(one.text.ptr == roots[0].text.ptr);
}

test "include join reports cycles, misses, and malformed includes" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const files = [_]File{
        .{ .key = "a", .text = "include \"b\";\n" },
        .{ .key = "b", .text = "include \"a\";\n" },
    };
    var failure: ?JoinFailure = null;
    try std.testing.expectError(
        error.ImportCycle,
        includeMem(arena.allocator(), &files, files[0..1], &failure),
    );
    try std.testing.expectEqual(JoinErrorKind.cycle, failure.?.kind);
    try std.testing.expectEqual(Syntax.auf, failure.?.syntax);
    try std.testing.expectEqualStrings("b", failure.?.file_key);

    failure = null;
    const missing = [_]File{.{ .key = "r", .text = "foo\n---\ninclude \"zz\";\n" }};
    try std.testing.expectError(
        error.ImportUnresolved,
        includeMem(arena.allocator(), &files, &missing, &failure),
    );
    try std.testing.expectEqualStrings("zz", failure.?.spec);
    try std.testing.expectEqual(@as(usize, 16), failure.?.span.start);

    failure = null;
    const malformed = [_]File{.{ .key = "r", .text = "include \"a\"\n" }};
    try std.testing.expectError(
        error.MalformedImport,
        includeMem(arena.allocator(), &files, &malformed, &failure),
    );
    try std.testing.expectEqual(JoinErrorKind.malformed, failure.?.kind);
}
