//! A unit: a root `.mm0` joined with its imports and, when it has a proof
//! file, the paired `.auf` files joined with their includes. The language
//! server checks and indexes the joined texts and maps what it finds back
//! to the files.

const std = @import("std");
const lsp = @import("lsp");
const mm0 = @import("mm0");
const lsp_diagnostics = @import("lsp_diagnostics");
const lsp_texts = @import("../lsp_texts.zig");
const uris = @import("./uris.zig");

const FileText = lsp_texts.FileText;
const FileTexts = lsp_texts.FileTexts;
const Imports = mm0.Imports;
const LspIndex = mm0.Frontend.LspIndex;
const Search = mm0.CompilerSupport.Search;
const pathToUri = uris.pathToUri;
const DiagnosticContext = lsp_diagnostics.DiagnosticContext;

pub const OpenDocument = struct {
    text: []u8,
    version: i32,
};

pub const NavigationDocumentState = struct {
    uri: []const u8,
    version: ?i32,
    mtime: ?i128,

    pub fn eql(
        self: NavigationDocumentState,
        other: NavigationDocumentState,
    ) bool {
        return std.mem.eql(u8, self.uri, other.uri) and
            self.version == other.version and
            self.mtime == other.mtime;
    }

    /// Return a copy whose `uri` is owned by `allocator` (version/mtime are
    /// plain values). Release it with `freeUri`.
    pub fn dupe(
        self: NavigationDocumentState,
        allocator: std.mem.Allocator,
    ) !NavigationDocumentState {
        return .{
            .uri = try allocator.dupe(u8, self.uri),
            .version = self.version,
            .mtime = self.mtime,
        };
    }

    pub fn freeUri(self: NavigationDocumentState, allocator: std.mem.Allocator) void {
        allocator.free(self.uri);
    }
};

/// One file of an analysis unit: an open document (with its version) or a
/// file read from disk (with its mtime), keyed by its path.
pub const UnitFile = struct {
    uri: []const u8,
    path: []const u8,
    text: []const u8,
    version: ?i32,
    mtime: ?i128,

    pub fn state(self: UnitFile) NavigationDocumentState {
        return .{ .uri = self.uri, .version = self.version, .mtime = self.mtime };
    }
};

/// What a unit's join found at `path`. Neither a version nor an mtime means
/// nothing it could read.
pub const UnitLookup = struct {
    path: []const u8,
    state: NavigationDocumentState,

    /// Opening, changing or closing a document drops every unit that looked
    /// it up (`dropUnitsOf`), so only what was read from disk is checked
    /// here.
    pub fn stands(lookup: UnitLookup, io: std.Io) bool {
        const state = lookup.state;
        return state.version != null or
            state.mtime == fileMtime(io, lookup.path);
    }
};

/// A span of a joined text resolved to the file it was copied from.
pub const UnitLocation = struct {
    file: UnitFile,
    span: Search.Span,
};

/// One side of a unit (`.mm0` or `.auf`): its files, joined in post-order.
pub const UnitSide = struct {
    joined: Imports.Joined,
    /// Parallel to `joined.files`.
    files: []const UnitFile,
    /// Index of the root file in `files`.
    root: usize,

    pub fn rootFile(self: UnitSide) UnitFile {
        return self.files[self.root];
    }

    pub fn fileIndex(self: UnitSide, uri: []const u8) ?usize {
        for (self.files, 0..) |file, index| {
            if (std.mem.eql(u8, file.uri, uri)) return index;
        }
        return null;
    }

    /// The joined offset of a position in one file, or null inside an
    /// import/include statement (the joined text does not contain those).
    pub fn joinedOffset(self: UnitSide, file_index: usize, offset: usize) ?usize {
        return self.joined.map.joinedOffset(file_index, offset);
    }

    pub fn locate(self: UnitSide, span: Search.Span) ?UnitLocation {
        const hit = self.joined.map.locateSpan(.{
            .start = span.start,
            .end = span.end,
        }) orelse return null;
        return .{
            .file = self.files[hit.file_index],
            .span = .{ .start = hit.span.start, .end = hit.span.end },
        };
    }
};

/// An import/include that could not be followed: a diagnostic on the file
/// holding the statement.
pub const UnitFailure = struct {
    file: UnitFile,
    span: Search.Span,
    message: []const u8,
};

/// What one analysis or navigation request works on: the root `.mm0`
/// joined with its imports and, when the root has a proof file, the paired
/// `.auf` files joined with their includes — the same texts `abc compile`
/// sees. The compiler and the index run over the joined texts; spans map
/// back to files through `locate`, positions in a file map forward through
/// `UnitSide.joinedOffset`. A document without imports is passed through,
/// so both maps are the identity for it.
pub const Unit = struct {
    mm0: UnitSide,
    proof: ?UnitSide,
    failures: []const UnitFailure,
    /// Every file the join looked up, found or not. While each is as it was
    /// then, the same join gives the same unit.
    lookups: []const UnitLookup,
    /// The texts of `files`, held from the handler's `texts` until
    /// `release`.
    held: []const *FileText,

    pub fn release(self: *const Unit, texts: *FileTexts) void {
        for (self.held) |text| texts.release(text);
    }

    pub const Found = struct {
        document: LspIndex.DocumentId,
        file_index: usize,
    };

    pub fn side(self: *const Unit, document: LspIndex.DocumentId) ?*const UnitSide {
        return switch (document) {
            .mm0 => &self.mm0,
            .proof => if (self.proof) |*proof| proof else null,
        };
    }

    pub fn find(self: *const Unit, uri: []const u8) ?Found {
        if (self.mm0.fileIndex(uri)) |index| {
            return .{ .document = .mm0, .file_index = index };
        }
        if (self.proof) |proof| {
            if (proof.fileIndex(uri)) |index| {
                return .{ .document = .proof, .file_index = index };
            }
        }
        return null;
    }

    pub fn isRootUri(self: *const Unit, uri: []const u8) bool {
        if (std.mem.eql(u8, self.mm0.rootFile().uri, uri)) return true;
        if (self.proof) |proof| {
            if (std.mem.eql(u8, proof.rootFile().uri, uri)) return true;
        }
        return false;
    }

    pub fn diagnosticContext(self: *const Unit) DiagnosticContext {
        return .{
            .mm0 = diagnosticDocument(self.mm0.rootFile()),
            .proof = if (self.proof) |proof|
                diagnosticDocument(proof.rootFile())
            else
                null,
            .locator = .{ .ctx = @ptrCast(self), .locateFn = locateSpan },
        };
    }

    pub fn rangeLocator(self: *const Unit) lsp_diagnostics.RangeLocator {
        return .{ .ctx = @ptrCast(self), .locateFn = locateRange };
    }

    pub fn diagnosticDocument(file: UnitFile) lsp_diagnostics.DiagnosticDocument {
        return .{ .uri = file.uri, .text = file.text, .version = file.version };
    }

    pub fn locateSpan(
        ctx: *const anyopaque,
        source: mm0.CompilerDiagnosticSource,
        span: lsp_diagnostics.Span,
    ) ?lsp_diagnostics.LocatedSpan {
        const self: *const Unit = @ptrCast(@alignCast(ctx));
        const document: LspIndex.DocumentId = switch (source) {
            .mm0 => .mm0,
            .proof => .proof,
        };
        const unit_side = self.side(document) orelse return null;
        const hit = unit_side.locate(.{
            .start = span.start,
            .end = span.end,
        }) orelse return null;
        return .{
            .uri = hit.file.uri,
            .text = hit.file.text,
            .version = hit.file.version,
            .span = .{ .start = hit.span.start, .end = hit.span.end },
        };
    }

    pub fn locateRange(
        ctx: *const anyopaque,
        range: LspIndex.SourceRange,
    ) ?lsp_diagnostics.LocatedRange {
        const self: *const Unit = @ptrCast(@alignCast(ctx));
        const unit_side = self.side(range.document) orelse return null;
        const hit = unit_side.locate(.{
            .start = range.start,
            .end = range.end,
        }) orelse return null;
        return .{
            .uri = hit.file.uri,
            .text = hit.file.text,
            .span = .{ .start = hit.span.start, .end = hit.span.end },
        };
    }

    /// The files of `unit`, each once: the proof root, the theory root, then
    /// the rest.
    pub fn allFiles(unit: *const Unit, arena: std.mem.Allocator) ![]const UnitFile {
        var files = std.StringArrayHashMapUnmanaged(UnitFile).empty;
        if (unit.proof) |proof| try addUnitFile(arena, &files, proof.rootFile());
        try addUnitFile(arena, &files, unit.mm0.rootFile());
        for (unit.mm0.files) |file| try addUnitFile(arena, &files, file);
        if (unit.proof) |proof| {
            for (proof.files) |file| try addUnitFile(arena, &files, file);
        }
        // A failed join leaves the failing file out of the degraded unit.
        for (unit.failures) |failure| try addUnitFile(arena, &files, failure.file);
        return files.values();
    }

    fn addUnitFile(
        arena: std.mem.Allocator,
        files: *std.StringArrayHashMapUnmanaged(UnitFile),
        file: UnitFile,
    ) !void {
        const gop = try files.getOrPut(arena, file.uri);
        if (!gop.found_existing) gop.value_ptr.* = file;
    }

    /// The files of `unit` besides its roots.
    pub fn deps(unit: *const Unit, arena: std.mem.Allocator) ![]const []const u8 {
        var others = std.ArrayListUnmanaged([]const u8).empty;
        for (try unit.allFiles(arena)) |file| {
            if (!unit.isRootUri(file.uri)) try others.append(arena, file.uri);
        }
        return others.items;
    }
};

/// Where a join finds its files: the open documents first, then the disk.
pub const Sources = struct {
    docs: *const std.StringHashMapUnmanaged(OpenDocument),
    texts: *FileTexts,
    io: std.Io,

    /// The file at `path` (named `uri`) as a unit file, its text held from
    /// `texts`: an open document first (unsaved edits count), else the disk
    /// copy. Names are copied into `arena`.
    fn hold(
        self: Sources,
        arena: std.mem.Allocator,
        uri: []const u8,
        path: []const u8,
    ) !struct { file: UnitFile, text: *FileText } {
        const text = if (self.docs.get(uri)) |doc|
            try self.texts.document(path, doc.text, doc.version)
        else
            try self.texts.disk(self.io, path);
        errdefer self.texts.release(text);
        return .{
            .file = .{
                .uri = try arena.dupe(u8, uri),
                .path = try arena.dupe(u8, path),
                .text = text.text,
                .version = text.version,
                .mtime = text.mtime,
            },
            .text = text,
        };
    }

    /// Does `path` name an open document or a readable file?
    pub fn exists(self: Sources, arena: std.mem.Allocator, path: []const u8) bool {
        const uri = pathToUri(arena, path) catch return false;
        if (self.docs.contains(uri)) return true;
        return fileOpens(self.io, path);
    }
};

/// Join a root `.mm0` with its imports and, when `proof_path` is given,
/// the paired `.auf` files with their includes (`Imports.loadUnit`). A
/// join that fails (a missing file, a cycle, a malformed statement)
/// degrades that side to its root alone with its statements blanked, and
/// records the failure as a diagnostic on the file holding the statement
/// (and, when that file is not the root, on the root statement leading
/// there). A proof root that cannot be read leaves the unit without a
/// proof side; a `.mm0` root that cannot be read fails the build.
/// Everything the unit references is allocated from `arena`, apart from
/// the file texts, which it holds until `Unit.release`.
pub fn join(
    sources: Sources,
    arena: std.mem.Allocator,
    mm0_uri: []const u8,
    mm0_path: []const u8,
    proof_uri: ?[]const u8,
    proof_path: ?[]const u8,
) !Unit {
    var loader = UnitLoader{ .sources = sources, .arena = arena };
    errdefer loader.release();
    const mm0_root = try loader.loadRoot(mm0_uri, mm0_path);
    var proof_root: ?UnitFile = null;
    var proof: Imports.ProofRoot = .none;
    if (proof_path) |path| {
        proof_root = try loader.load(proof_uri.?, path);
        if (proof_root) |file| {
            proof = .{ .file = .{ .key = file.path, .text = file.text } };
        }
    }
    // `.degrade` reports join failures in `unit.failures`; the loader
    // only fails on running out of memory.
    var failure: ?Imports.LoadFailure = null;
    const unit = try Imports.loadUnit(
        arena,
        loader.resolver(),
        .{ .key = mm0_root.path, .text = mm0_root.text },
        proof,
        .degrade,
        &failure,
    );

    var failures = std.ArrayListUnmanaged(UnitFailure).empty;
    for (unit.failures) |info| {
        try recordJoinFailure(arena, &loader, &failures, info);
    }
    return .{
        .mm0 = .{
            .joined = unit.mm0,
            .files = try loader.filesFor(unit.mm0),
            .root = indexOfKey(unit.mm0, mm0_root.path),
        },
        .proof = if (unit.proof) |joined| .{
            .joined = joined,
            .files = try loader.filesFor(joined),
            .root = indexOfKey(joined, proof_root.?.path),
        } else null,
        .failures = try failures.toOwnedSlice(arena),
        .lookups = try loader.lookups(),
        .held = loader.held.items,
    };
}

fn indexOfKey(joined: Imports.Joined, key: []const u8) usize {
    for (joined.files, 0..) |file, index| {
        if (std.mem.eql(u8, file.key, key)) return index;
    }
    unreachable;
}

fn recordJoinFailure(
    arena: std.mem.Allocator,
    loader: *UnitLoader,
    failures: *std.ArrayListUnmanaged(UnitFailure),
    info: Imports.JoinFailure,
) !void {
    // The statement's file was loaded before its statements were
    // followed, so it is always on record.
    const file = loader.found(info.file_key) orelse return;
    try failures.append(arena, .{
        .file = file,
        .span = .{ .start = info.span.start, .end = info.span.end },
        .message = try info.message(arena),
    });
    // A failure deeper down also shows on the root statement that led
    // there: the degraded unit has only the root left, whose errors
    // would otherwise just be knock-on ones.
    const via = info.via orelse return;
    const via_file = loader.found(via.file_key) orelse return;
    try failures.append(arena, .{
        .file = via_file,
        .span = .{ .start = via.span.start, .end = via.span.end },
        .message = try info.viaMessage(arena, via),
    });
}

/// Resolves imports and includes for `join`: a spec is joined
/// to the importing file's directory and normalised lexically, then looked
/// up as an open document or read from disk. `files` keeps every answer under
/// its path, null where there was no file, so a unit sees one state of each
/// and can list them afterwards.
const UnitLoader = struct {
    sources: Sources,
    arena: std.mem.Allocator,
    files: std.StringArrayHashMapUnmanaged(?UnitFile) = .empty,
    /// The texts of the files found, held from the handler's `texts`.
    held: std.ArrayListUnmanaged(*FileText) = .empty,

    fn resolver(self: *UnitLoader) Imports.Resolver {
        return .{ .ctx = @ptrCast(self), .resolveFn = resolveFn };
    }

    /// Let go of every text held, when the unit is not built after all.
    fn release(self: *UnitLoader) void {
        for (self.held.items) |text| self.sources.texts.release(text);
    }

    /// The root `.mm0`, which has to be there: its read error otherwise.
    fn loadRoot(self: *UnitLoader, uri: []const u8, path: []const u8) !UnitFile {
        const file = try self.hold(uri, path);
        try self.files.put(self.arena, file.path, file);
        return file;
    }

    /// Null when there is no file at `path`.
    fn load(self: *UnitLoader, uri: []const u8, path: []const u8) !?UnitFile {
        if (self.files.get(path)) |known| return known;
        const file = self.hold(uri, path) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            // On wasm there is no disk; the read reports FileNotFound.
            else => null,
        };
        const key = if (file) |found_file| found_file.path else try self.arena.dupe(u8, path);
        try self.files.put(self.arena, key, file);
        return file;
    }

    fn hold(self: *UnitLoader, uri: []const u8, path: []const u8) !UnitFile {
        try self.held.ensureUnusedCapacity(self.arena, 1);
        const held = try self.sources.hold(self.arena, uri, path);
        self.held.appendAssumeCapacity(held.text);
        return held.file;
    }

    /// The file loaded from `path`, if it was.
    fn found(self: *const UnitLoader, path: []const u8) ?UnitFile {
        return self.files.get(path) orelse null;
    }

    fn lookups(self: *const UnitLoader) ![]const UnitLookup {
        const out = try self.arena.alloc(UnitLookup, self.files.count());
        for (out, self.files.keys(), self.files.values()) |*lookup, path, entry| {
            lookup.* = .{
                .path = path,
                .state = if (entry) |file| file.state() else .{
                    .uri = try pathToUri(self.arena, path),
                    .version = null,
                    .mtime = null,
                },
            };
        }
        return out;
    }

    /// The unit files behind a join, parallel to `joined.files`.
    fn filesFor(self: *UnitLoader, joined: Imports.Joined) ![]const UnitFile {
        const out = try self.arena.alloc(UnitFile, joined.files.len);
        for (joined.files, 0..) |file, index| {
            out[index] = self.found(file.key).?;
        }
        return out;
    }

    fn resolveFn(
        ctx: *anyopaque,
        allocator: std.mem.Allocator,
        from_key: []const u8,
        spec: []const u8,
    ) anyerror!Imports.Resolved {
        const self: *UnitLoader = @ptrCast(@alignCast(ctx));
        const path = try Imports.resolveSpecPath(allocator, from_key, spec);
        const file = try self.load(try pathToUri(self.arena, path), path) orelse
            return error.FileNotFound;
        return .{ .key = file.path, .text = file.text };
    }
};

/// The mtime of the file at `path`; null when there is none.
fn fileMtime(io: std.Io, path: []const u8) ?i128 {
    const stat = std.Io.Dir.cwd().statFile(io, path, .{}) catch return null;
    return stat.mtime.nanoseconds;
}

/// Can `path` be opened for reading? Checked without reading the contents.
fn fileOpens(io: std.Io, path: []const u8) bool {
    const file = std.Io.Dir.cwd().openFile(io, path, .{}) catch return false;
    file.close(io);
    return true;
}
