//! What the language server tells the client about each file: the
//! diagnostics of an analysis, published on the files they lie in, and
//! the record of what each analysis read and published. `Handler` names
//! these as its own methods.

const std = @import("std");
const lsp = @import("lsp");
const mm0 = @import("mm0");
const lsp_diagnostics = @import("lsp_diagnostics");
const handler_mod = @import("../lsp.zig");
const uri_names = @import("./uris.zig");
const unit_mod = @import("./unit.zig");
const unit_state = @import("./unit_state.zig");

const types = lsp.types.flat;
const ArenaAllocator = mm0.ArenaAllocator;
const Handler = handler_mod.Handler;
const HoleInferenceSink = mm0.CompilerSupport.Context.HoleInferenceSink;
const LocatedDiagnostic = lsp_diagnostics.LocatedDiagnostic;
const LSP_SERVER_NAME = lsp_diagnostics.SERVER_NAME;
const Search = mm0.CompilerSupport.Search;
const Unit = unit_mod.Unit;
const UnitRoots = uri_names.UnitRoots;
const UnitSide = unit_mod.UnitSide;
const UnitState = unit_state.UnitState;
const documentKind = uri_names.documentKind;
const outcomeForPlaceholder = unit_state.outcomeForPlaceholder;
const pathToUri = uri_names.pathToUri;
const siblingPathForMm0 = uri_names.siblingPathForMm0;
const siblingPathForProof = uri_names.siblingPathForProof;
const uriToPath = uri_names.uriToPath;
const zeroRange = lsp_diagnostics.zeroRange;
const AnalysisOutcome = @import("./analysis.zig").AnalysisOutcome;

/// What the analysis of one open document touched: the other files it read
/// (so the document is analysed again when one of them changes) and the
/// closed files it published diagnostics for (so those are cleared when they
/// drop out).
pub const Report = struct {
    deps: []const []const u8,
    published: []const []const u8,

    pub fn deinit(self: *Report, allocator: std.mem.Allocator) void {
        freeUriList(allocator, self.deps);
        freeUriList(allocator, self.published);
        self.* = undefined;
    }
};

pub fn dupeUriList(
    allocator: std.mem.Allocator,
    uris: []const []const u8,
) ![]const []const u8 {
    const owned = try allocator.alloc([]const u8, uris.len);
    var filled: usize = 0;
    errdefer freeUriList(allocator, owned[0..filled]);
    for (uris, 0..) |uri, index| {
        owned[index] = try allocator.dupe(u8, uri);
        filled = index + 1;
    }
    return owned;
}

pub fn freeUriList(allocator: std.mem.Allocator, uris: []const []const u8) void {
    for (uris) |uri| allocator.free(uri);
    allocator.free(uris);
}

pub fn uriListContains(uris: []const []const u8, uri: []const u8) bool {
    for (uris) |candidate| {
        if (std.mem.eql(u8, candidate, uri)) return true;
    }
    return false;
}

/// Does the open document at `uri` report its own diagnostics (a `.mm0`
/// file, or a `.auf` file with a sibling theory)? A root's analysis
/// leaves such files alone; it publishes for closed files and for
/// library proof files that have no analysis of their own.
pub fn ownsDiagnostics(
    self: *Handler,
    arena: std.mem.Allocator,
    uri: []const u8,
) bool {
    if (!self.docs.contains(uri)) return false;
    const path = uriToPath(arena, uri) catch return true;
    return switch (documentKind(path)) {
        .mm0, .other => true,
        .proof => blk: {
            const mm0_path = siblingPathForProof(arena, path) catch
                break :blk true;
            break :blk self.sources().exists(arena, mm0_path);
        },
    };
}

/// Publish the diagnostics of one analysis, each on the file it lies
/// in. The roots always receive a set (an empty one clears them); other
/// files receive theirs only when they do not report on themselves
/// (`ownsDiagnostics`), and closed ones only when there is something to
/// report and the analysis checked them. Records what the analysis read
/// and published under `record_uri`.
pub fn publishUnitDiagnostics(
    self: *Handler,
    arena: std.mem.Allocator,
    record_uri: []const u8,
    unit: *const Unit,
    outcome: AnalysisOutcome,
    primary: []const mm0.CompilerDiagnostic,
    warnings: []const mm0.CompilerDiagnostic,
    extra: ?mm0.CompilerDiagnostic,
    proof_omitted: ?mm0.CompilerDiagnostic,
    mm0_omitted: ?mm0.CompilerDiagnostic,
    extra_located: []const LocatedDiagnostic,
) !void {
    var all = std.ArrayListUnmanaged(LocatedDiagnostic).empty;
    try all.appendSlice(arena, try lsp_diagnostics.locateCompilerDiagnostics(
        arena,
        unit.diagnosticContext(),
        primary,
        warnings,
        extra,
        proof_omitted,
        mm0_omitted,
        self.offset_encoding,
    ));
    for (unit.failures) |failure| {
        try all.append(arena, .{
            .uri = failure.file.uri,
            .version = failure.file.version,
            .diagnostic = .{
                .range = lsp_diagnostics.offsets.locToRange(
                    failure.file.text,
                    .{ .start = failure.span.start, .end = failure.span.end },
                    self.offset_encoding,
                ),
                .severity = .Error,
                .source = LSP_SERVER_NAME,
                .message = .{ .string = failure.message },
            },
        });
    }
    try all.appendSlice(arena, extra_located);

    var published = std.ArrayListUnmanaged([]const u8).empty;
    for (try unit.allFiles(arena)) |target| {
        const is_root = unit.isRootUri(target.uri);
        var diagnostics = std.ArrayListUnmanaged(types.Diagnostic).empty;
        for (all.items) |located| {
            if (!std.mem.eql(u8, located.uri, target.uri)) continue;
            try diagnostics.append(arena, located.diagnostic);
        }
        if (is_root) {
            try publishDiagnostics(
                self,
                arena,
                target.uri,
                target.version,
                diagnostics.items,
            );
            continue;
        }
        // A closed file is left alone when it has nothing to report, or
        // when its proofs are not yet checked: what it shows stays until
        // they are. An open library file always receives the root's
        // view, which also clears the note its own analysis left ("no
        // sibling theory").
        if (!self.docs.contains(target.uri) and
            (diagnostics.items.len == 0 or outcome == .own_checked))
        {
            continue;
        }
        if (self.ownsDiagnostics(arena, target.uri)) continue;
        try publishDiagnostics(
            self,
            arena,
            target.uri,
            target.version,
            diagnostics.items,
        );
        try published.append(arena, target.uri);
    }

    // The closed files published for before stay so until the check of
    // the rest says otherwise.
    if (outcome == .own_checked) if (self.reports.get(record_uri)) |record| {
        for (record.published) |uri| {
            if (uriListContains(published.items, uri)) continue;
            try published.append(arena, uri);
        }
    };
    try storeReport(
        self,
        arena,
        record_uri,
        try unit.deps(arena),
        published.items,
    );
}

/// Record the files the analysis of `root_uri` is about to check, so
/// that a request about one finds the unit meanwhile.
pub fn recordUnitFiles(
    self: *Handler,
    arena: std.mem.Allocator,
    root_uri: []const u8,
    unit: *const Unit,
) !void {
    const published: []const []const u8 =
        if (self.reports.get(root_uri)) |record| record.published else &.{};
    try storeReport(self, arena, root_uri, try unit.deps(arena), published);
}

/// Replace the record for `root_uri`, clearing diagnostics on files the
/// previous analysis published for but this one did not.
fn storeReport(
    self: *Handler,
    arena: std.mem.Allocator,
    root_uri: []const u8,
    deps: []const []const u8,
    published: []const []const u8,
) !void {
    const owned_deps = try dupeUriList(self.allocator, deps);
    errdefer freeUriList(self.allocator, owned_deps);
    const owned_published = try dupeUriList(self.allocator, published);
    errdefer freeUriList(self.allocator, owned_published);

    const gop = try self.reports.getOrPut(self.allocator, root_uri);
    if (gop.found_existing) {
        for (gop.value_ptr.published) |old| {
            if (uriListContains(published, old)) continue;
            try self.clearDiagnostics(arena, old, null);
        }
        gop.value_ptr.deinit(self.allocator);
    } else {
        errdefer _ = self.reports.remove(root_uri);
        gop.key_ptr.* = try self.allocator.dupe(u8, root_uri);
    }
    gop.value_ptr.* = .{ .deps = owned_deps, .published = owned_published };
}

/// Drop the record for `root_uri`, clearing what it published.
pub fn forgetUnit(
    self: *Handler,
    arena: std.mem.Allocator,
    root_uri: []const u8,
) !void {
    const removed = self.reports.fetchRemove(root_uri) orelse return;
    var record = removed.value;
    defer {
        record.deinit(self.allocator);
        self.allocator.free(removed.key);
    }
    for (record.published) |uri| {
        try self.clearDiagnostics(arena, uri, null);
    }
}

/// Is `uri` read by some root's analysis?
pub fn isDependency(self: *Handler, uri: []const u8) bool {
    var it = self.reports.iterator();
    while (it.next()) |entry| {
        if (uriListContains(entry.value_ptr.deps, uri)) return true;
    }
    return false;
}

/// The roots whose analyses read `uri`, copied into `arena` (analysing
/// them rewrites the records).
pub fn dependentRoots(
    self: *Handler,
    arena: std.mem.Allocator,
    uri: []const u8,
) ![]const []const u8 {
    var roots = std.ArrayListUnmanaged([]const u8).empty;
    var it = self.reports.iterator();
    while (it.next()) |entry| {
        if (!uriListContains(entry.value_ptr.deps, uri)) continue;
        try roots.append(arena, try arena.dupe(u8, entry.key_ptr.*));
    }
    return roots.items;
}

pub fn publishMessageDiagnostic(
    self: *Handler,
    arena: std.mem.Allocator,
    uri: []const u8,
    version: ?i32,
    text: []const u8,
    message: []const u8,
) !void {
    const diagnostics = try arena.alloc(types.Diagnostic, 1);
    diagnostics[0] = .{
        .range = zeroRange(text, self.offset_encoding),
        .severity = .Error,
        .source = LSP_SERVER_NAME,
        .message = .{ .string = message },
    };
    try publishDiagnostics(self, arena, uri, version, diagnostics);
}

pub fn clearDiagnostics(
    self: *Handler,
    arena: std.mem.Allocator,
    uri: []const u8,
    version: ?i32,
) !void {
    try publishDiagnostics(self, arena, uri, version, &.{});
}

fn publishDiagnostics(
    self: *Handler,
    arena: std.mem.Allocator,
    uri: []const u8,
    version: ?i32,
    diagnostics: []const types.Diagnostic,
) !void {
    try self.transport.writeNotification(
        self.io,
        arena,
        "textDocument/publishDiagnostics",
        types.PublishDiagnosticsParams,
        .{
            .uri = uri,
            .version = version,
            .diagnostics = diagnostics,
        },
        .{ .emit_null_optional_fields = false },
    );
}
