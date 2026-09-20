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
const std = @import("std");
const builtin = @import("builtin");

pub const Span = struct {
    start: usize,
    end: usize,
};

/// One `import "spec";` statement in a source text.
pub const ImportStmt = struct {
    /// The whole statement, `import` through `;`.
    span: Span,
    /// The string contents (no quotes).
    spec: []const u8,
    /// The quoted string, quotes included.
    spec_span: Span,
};

pub const ScanError = error{
    /// `import` not followed by a `"..."` string and a `;`.
    MalformedImport,
    /// A `$...$` math string or `"..."` string never closes.
    UnterminatedString,
} || std.mem.Allocator.Error;

pub const Scanner = struct {
    src: []const u8,
    pos: usize = 0,
    /// The span of the token a scan error refers to.
    error_span: ?Span = null,

    pub fn init(src: []const u8) Scanner {
        return .{ .src = src };
    }

    /// Advance to the next `import` statement and return it, skipping every
    /// other statement. Returns null at end of input.
    pub fn next(self: *Scanner) ScanError!?ImportStmt {
        while (true) {
            self.skipWhitespaceAndComments();
            if (self.pos >= self.src.len) return null;
            const word = self.peekWord();
            if (std.mem.eql(u8, word, "import")) {
                return try self.parseImport();
            }
            try self.skipStatement();
        }
    }

    fn parseImport(self: *Scanner) ScanError!ImportStmt {
        const start = self.pos;
        self.pos += "import".len;
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
    fn skipStatement(self: *Scanner) ScanError!void {
        while (self.pos < self.src.len) {
            const ch = self.src[self.pos];
            if (ch == '$') {
                const dollar_start = self.pos;
                self.pos += 1;
                while (self.pos < self.src.len and self.src[self.pos] != '$') {
                    self.pos += 1;
                }
                if (self.pos >= self.src.len) {
                    self.error_span = .{
                        .start = dollar_start,
                        .end = self.src.len,
                    };
                    return error.UnterminatedString;
                }
                self.pos += 1;
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
    var scanner = Scanner.init(src);
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

/// One file of a join, in post-order (imports before importers, the root
/// last).
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
};

pub const JoinErrorKind = enum {
    cycle,
    unresolved,
    malformed,
};

/// Where a join failed: the import statement (in `file_key`'s own text)
/// that could not be followed.
pub const JoinFailure = struct {
    kind: JoinErrorKind,
    file_key: []const u8,
    file_text: []const u8,
    span: Span,
    /// The spec of the failing import (for `cycle`/`unresolved`).
    spec: []const u8,
    /// The resolver's error, for `unresolved`.
    err: ?anyerror = null,
};

pub const JoinError = error{
    ImportCycle,
    ImportUnresolved,
    MalformedImport,
} || std.mem.Allocator.Error;

pub const Joined = struct {
    /// The joined text. When the root has no imports this is the root text
    /// itself (not owned); otherwise a buffer owned by `arena`.
    text: []const u8,
    map: SourceMap,
    /// Post-order file list; `map` file indices point into it.
    files: []const File,

    /// Is the joined text exactly the root text (no imports)?
    pub fn isPassthrough(self: Joined) bool {
        return self.files.len == 1 and self.map.segments.len == 1 and
            self.map.segments[0].len == self.text.len;
    }
};

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
    var joiner = Joiner{
        .allocator = allocator,
        .resolver = resolver,
        .failure = failure,
    };
    defer joiner.deinit();
    try joiner.write(root_key, root_text, true);
    const files = try joiner.files.toOwnedSlice(allocator);
    const segments = try joiner.segments.toOwnedSlice(allocator);
    return .{
        .text = if (joiner.passthrough) root_text else try joiner.out.toOwnedSlice(allocator),
        .map = .{ .segments = segments },
        .files = files,
    };
}

const Joiner = struct {
    allocator: std.mem.Allocator,
    resolver: Resolver,
    failure: ?*?JoinFailure,
    out: std.ArrayListUnmanaged(u8) = .{},
    files: std.ArrayListUnmanaged(File) = .{},
    segments: std.ArrayListUnmanaged(Segment) = .{},
    /// Keys of files being joined or already joined (mm0-rs `working`).
    working: std.StringHashMapUnmanaged(void) = .{},
    /// Keys on the current import path (mm0-rs `stack`), for cycles.
    stack: std.ArrayListUnmanaged([]const u8) = .{},
    /// True while no import has been seen: the root text can be reused.
    passthrough: bool = true,

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
        if (is_root) try self.working.put(self.allocator, key, {});

        // Files are numbered in post-order, so this file's index is only
        // known once its imports are done; segments record it via a
        // placeholder patched below.
        var pending: std.ArrayListUnmanaged(usize) = .{};
        defer pending.deinit(self.allocator);

        var scanner = Scanner.init(text);
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
            const gop = try self.working.getOrPut(self.allocator, resolved.key);
            if (gop.found_existing) continue;
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
            if (slot.* == null) slot.* = info;
        }
    }
};

/// Filesystem resolver for native hosts: specs resolve relative to the
/// importing file's directory; keys are canonical paths so the same file
/// reached by two routes is joined once.
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

/// Concatenate already-ordered files (the paired `.auf` files of a join)
/// into one text with a source map, a newline between files.
pub fn concat(
    allocator: std.mem.Allocator,
    files: []const File,
) std.mem.Allocator.Error!Joined {
    if (files.len == 1) {
        const segments = try allocator.alloc(Segment, 1);
        segments[0] = .{
            .joined_start = 0,
            .len = files[0].text.len,
            .file_index = 0,
            .file_offset = 0,
        };
        return .{
            .text = files[0].text,
            .map = .{ .segments = segments },
            .files = files,
        };
    }
    var out: std.ArrayListUnmanaged(u8) = .{};
    defer out.deinit(allocator);
    var segments: std.ArrayListUnmanaged(Segment) = .{};
    defer segments.deinit(allocator);
    for (files, 0..) |file, index| {
        if (index != 0 and (out.items.len == 0 or
            out.items[out.items.len - 1] != '\n'))
        {
            try segments.append(allocator, .{
                .joined_start = out.items.len,
                .len = 1,
                .file_index = null,
                .file_offset = 0,
            });
            try out.append(allocator, '\n');
        }
        try segments.append(allocator, .{
            .joined_start = out.items.len,
            .len = file.text.len,
            .file_index = index,
            .file_offset = 0,
        });
        try out.appendSlice(allocator, file.text);
    }
    return .{
        .text = try out.toOwnedSlice(allocator),
        .map = .{ .segments = try segments.toOwnedSlice(allocator) },
        .files = files,
    };
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
/// every joined file (by name: `foo.mm0` <-> `foo.auf`), concatenated in
/// the same order. Native hosts only.
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
    var proof_labels: std.ArrayListUnmanaged([]const u8) = .{};
    for (joined.files, 0..) |file, index| {
        const is_root = index + 1 == joined.files.len;
        const path: []const u8 = if (is_root)
            proof_path orelse (proofSibling(allocator, file.key) catch continue)
        else
            proofSibling(allocator, file.key) catch continue;
        const text = std.fs.cwd().readFileAlloc(
            allocator,
            path,
            std.math.maxInt(usize),
        ) catch |err| {
            if (is_root and proof_path != null) {
                failure.* = .{ .read = .{ .path = path, .err = err } };
                return error.ReadFailed;
            }
            if (err == error.FileNotFound) continue;
            failure.* = .{ .read = .{ .path = path, .err = err } };
            return error.ReadFailed;
        };
        try proof_files.append(allocator, .{ .key = path, .text = text });
        try proof_labels.append(
            allocator,
            if (is_root and proof_path != null) path else displayPath(cwd, path),
        );
    }
    if (proof_files.items.len == 0) {
        return .{
            .mm0 = joined,
            .mm0_mapping = mm0_mapping,
            .proof = null,
            .proof_mapping = null,
        };
    }
    const proof_joined = try concat(allocator, try proof_files.toOwnedSlice(allocator));
    return .{
        .mm0 = joined,
        .mm0_mapping = mm0_mapping,
        .proof = proof_joined,
        .proof_mapping = .{
            .map = proof_joined.map,
            .files = proof_joined.files,
            .labels = try proof_labels.toOwnedSlice(allocator),
        },
    };
}

const Labeller = struct {
    cwd: []const u8,
    root_key: []const u8,
    root_label: []const u8,

    fn label(ctx: *anyopaque, key: []const u8) []const u8 {
        const self: *Labeller = @ptrCast(@alignCast(ctx));
        if (std.mem.eql(u8, key, self.root_key)) return self.root_label;
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
    var scanner = Scanner.init(src);
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
    var scanner = Scanner.init("import a.mm0;");
    try std.testing.expectError(error.MalformedImport, scanner.next());
    scanner = Scanner.init("import \"a.mm0\"");
    try std.testing.expectError(error.MalformedImport, scanner.next());
    scanner = Scanner.init("import \"a.mm0");
    try std.testing.expectError(error.UnterminatedString, scanner.next());
    scanner = Scanner.init("axiom a: $ x;");
    try std.testing.expectError(error.UnterminatedString, scanner.next());
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
