const std = @import("std");
const mm0 = @import("mm0");

// Structured diagnostic-field renderers live in `diag_json.zig`: the
// exhaustive `DiagnosticDetail` switch must be analyzed by the native test
// build, not just this wasm-only file. Every string goes through
// `std.json.Stringify`, so the result buffer is always valid JSON, even when a
// diagnostic echoes a source token with quotes or backslashes in it.
const diag_json = @import("diag_json.zig");
const writeFields = diag_json.writeFields;

const allocator = std.heap.wasm_allocator;

var result_json: []u8 = &.{};
var result_mmb: []u8 = &.{};

pub export fn alloc(len: u32) u32 {
    if (len == 0) return 0;
    const buf = allocator.alloc(u8, len) catch return 0;
    return @intCast(@intFromPtr(buf.ptr));
}

pub export fn free(ptr: u32, len: u32) void {
    if (ptr == 0 or len == 0) return;
    allocator.free(ptrToSlice(ptr, len));
}

/// Select the diagnostic locale ("en", "de") for all subsequent compiles.
/// Returns 1 on success, 0 for an unknown locale name (the current locale
/// is left unchanged). The embedding JS calls this once after
/// instantiation; there is no environment in browser wasm.
pub export fn set_locale(name_ptr: u32, name_len: u32) u32 {
    const name = ptrToConstSlice(name_ptr, name_len);
    const lang = mm0.parseCompilerLang(name) orelse return 0;
    mm0.setCompilerLang(lang);
    return 1;
}

pub export fn compile_sources(
    mm0_ptr: u32,
    mm0_len: u32,
    proof_ptr: u32,
    proof_len: u32,
) u32 {
    clearState();
    return compileUnit(.{
        .mm0 = ptrToConstSlice(mm0_ptr, mm0_len),
        .proof = ptrToConstSlice(proof_ptr, proof_len),
    });
}

/// One file of a `compile_files` request.
const FileEntry = struct {
    path: []const u8,
    text: []const u8,
};

/// A `compile_files` request: `{"root": "/a/main.mm0", "proof":
/// "/a/main.auf" | null, "files": [{"path": "...", "text": "..."}, ...]}`.
/// Paths are normalised absolute POSIX paths (`Imports.TableResolver`).
const FilesRequest = struct {
    root: []const u8,
    proof: ?[]const u8 = null,
    files: []const FileEntry,
};

/// Compile a root `.mm0` out of an in-memory file table (JSON, see
/// `FilesRequest`): imports and includes resolve against the table, the
/// root's proof is `proof` when given and its `<stem>.auf` sibling
/// otherwise, and every diagnostic names the file it lies in (`file`) with
/// offsets local to that file. `compile_sources` is the one-pair form.
pub export fn compile_files(json_ptr: u32, json_len: u32) u32 {
    clearState();
    var arena_state = std.heap.ArenaAllocator.init(allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();

    const request = std.json.parseFromSliceLeaky(
        FilesRequest,
        arena,
        ptrToConstSlice(json_ptr, json_len),
        .{ .ignore_unknown_fields = true },
    ) catch |err| {
        writeRequestFailure(err) catch clearState();
        return 0;
    };
    const files = arena.alloc(mm0.Imports.File, request.files.len) catch {
        writeRequestFailure(error.OutOfMemory) catch clearState();
        return 0;
    };
    for (request.files, 0..) |entry, index| {
        files[index] = .{ .key = entry.path, .text = entry.text };
    }

    var failure: ?mm0.Imports.LoadFailure = null;
    const pair = mm0.Imports.loadPairFromTable(
        arena,
        files,
        request.root,
        request.proof,
        &failure,
    ) catch |err| {
        writeLoadFailure(arena, failure, err) catch clearState();
        return 0;
    };
    return compileUnit(.{
        .mm0 = pair.mm0.text,
        .proof = if (pair.proof) |proof| proof.text else "",
        .mm0_mapping = pair.mm0_mapping,
        .proof_mapping = pair.proof_mapping,
    });
}

/// What one compile runs over: the (joined) texts and, for a join, the
/// mappings that place diagnostics back in their files.
const Unit = struct {
    mm0: []const u8,
    proof: []const u8,
    mm0_mapping: ?mm0.Imports.Mapping = null,
    proof_mapping: ?mm0.Imports.Mapping = null,

    fn compiler(self: Unit) mm0.Compiler {
        var result = mm0.Compiler.initWithProof(allocator, self.mm0, self.proof);
        result.diagnostics.setMapping(.mm0, self.mm0_mapping);
        result.diagnostics.setMapping(.proof, self.proof_mapping);
        return result;
    }
};

fn compileUnit(unit: Unit) u32 {
    // Pretty-printed statement snapshots for the meta JSON, captured at the
    // end of the pipeline run (or of the analysis rerun on failure, which
    // resets and re-captures with recovery's richer environment).
    var statements = mm0.StatementSink.init(allocator);
    defer statements.deinit();
    var compiler = unit.compiler();
    compiler.statement_sink = &statements;

    result_mmb = compiler.compileMmb(allocator) catch |err| {
        var analysis_compiler = unit.compiler();
        // Match the LSP's analysis posture: a search placeholder (`auto?` /
        // `exact?` / `apply?`) is an unfilled hole, not an unknown rule — the
        // checker admits its line and goes on, and a warning-severity
        // diagnostic per placeholder is synthesized below
        // (`writePlaceholderDiagnostics`).
        analysis_compiler.allow_search_placeholders = true;
        analysis_compiler.statement_sink = &statements;
        analysis_compiler.analyze() catch {};
        writeCompileFailure(
            &compiler,
            &analysis_compiler,
            &statements,
            unit.proof,
            err,
        ) catch clearState();
        return 0;
    };
    writeCompileSuccess(&compiler, result_mmb.len, &statements) catch {
        clearState();
        return 0;
    };
    return 1;
}

pub export fn result_json_ptr() u32 {
    return slicePtr(result_json);
}

pub export fn result_json_len() u32 {
    return @intCast(result_json.len);
}

pub export fn result_mmb_ptr() u32 {
    return slicePtr(result_mmb);
}

pub export fn result_mmb_len() u32 {
    return @intCast(result_mmb.len);
}

fn clearState() void {
    if (result_json.len != 0) allocator.free(result_json);
    if (result_mmb.len != 0) allocator.free(result_mmb);
    result_json = &.{};
    result_mmb = &.{};
}

fn ptrToSlice(ptr: u32, len: u32) []u8 {
    return @as([*]u8, @ptrFromInt(ptr))[0..len];
}

fn ptrToConstSlice(ptr: u32, len: u32) []const u8 {
    if (ptr == 0 or len == 0) return &.{};
    return @as([*]const u8, @ptrFromInt(ptr))[0..len];
}

fn slicePtr(bytes: []const u8) u32 {
    if (bytes.len == 0) return 0;
    return @intCast(@intFromPtr(bytes.ptr));
}

/// An empty JSON array.
const no_items: []const struct {} = &.{};

fn writeCompileSuccess(
    compiler: *const mm0.Compiler,
    mmb_len: usize,
    statements: *const mm0.StatementSink,
) !void {
    var out: std.Io.Writer.Allocating = .init(allocator);
    errdefer out.deinit();
    var jw: std.json.Stringify = .{ .writer = &out.writer };

    try jw.beginObject();
    try writeFields(&jw, .{
        .ok = true,
        .phase = "compile",
        .message = "ok",
        .@"error" = null,
        .mmbLen = mmb_len,
        .diagnostic = null,
    });
    // A clean compile still carries warnings — an admitted line (`sorry!`)
    // above all, which the editor must see to withhold its seal.
    try writeDiagnosticsField(&jw, compiler, null);
    try writeStatementsField(&jw, statements);
    try jw.endObject();

    result_json = try out.toOwnedSlice();
}

fn writeCompileFailure(
    compiler: *const mm0.Compiler,
    analysis_compiler: *const mm0.Compiler,
    statements: *const mm0.StatementSink,
    proof_src: []const u8,
    err: anyerror,
) !void {
    var out: std.Io.Writer.Allocating = .init(allocator);
    errdefer out.deinit();
    var jw: std.json.Stringify = .{ .writer = &out.writer };

    try jw.beginObject();
    try writeFields(&jw, .{ .ok = false, .phase = "compile", .@"error" = err });
    if (compiler.diagnostics.last_diagnostic) |diag| {
        try writeFields(&jw, .{
            .message = mm0.compilerDiagnosticSummary(diag),
            .mmbLen = 0,
        });
        try jw.objectField("diagnostic");
        try writeDiagnostic(&jw, compiler, diag);
    } else {
        try writeFields(&jw, .{
            .message = mm0.compilerErrorSummary(err),
            .mmbLen = 0,
            .diagnostic = null,
        });
    }
    try writeDiagnosticsField(&jw, analysis_compiler, proof_src);
    try writeStatementsField(&jw, statements);
    try jw.endObject();

    result_json = try out.toOwnedSlice();
}

/// A `compile_files` request that could not be read at all.
fn writeRequestFailure(err: anyerror) !void {
    result_json = try std.json.Stringify.valueAlloc(allocator, .{
        .ok = false,
        .phase = "compile",
        .@"error" = err,
        .message = "malformed compile request",
        .mmbLen = 0,
        .diagnostic = null,
        .diagnostics = no_items,
        .statements = no_items,
    }, .{});
}

/// A file table whose imports or includes could not be joined: one error
/// diagnostic on the failing statement (or, for a missing root, none).
fn writeLoadFailure(
    arena: std.mem.Allocator,
    failure: ?mm0.Imports.LoadFailure,
    err: anyerror,
) !void {
    var synthetic: ?SyntheticDiagnostic = null;
    if (failure) |info| {
        const message = try info.message(arena);
        synthetic = switch (info) {
            .read => |read| .{
                .message = message,
                .source = if (std.mem.endsWith(u8, read.path, ".auf")) .proof else .mm0,
                .err = read.err,
            },
            .join => |join| .{
                .message = message,
                .source = switch (join.syntax) {
                    .mm0 => .mm0,
                    .auf => .proof,
                },
                .err = err,
                .file = join.file_key,
                .span = .{ .start = join.span.start, .end = join.span.end },
            },
        };
    }
    const diagnostics: []const SyntheticDiagnostic = if (synthetic) |*diag|
        diag[0..1]
    else
        &.{};
    result_json = try std.json.Stringify.valueAlloc(allocator, .{
        .ok = false,
        .phase = "compile",
        .@"error" = err,
        .message = if (synthetic) |diag| diag.message else @errorName(err),
        .mmbLen = 0,
        .diagnostic = synthetic,
        .diagnostics = diagnostics,
        .statements = no_items,
    }, .{});
}

fn writeDiagnosticsField(
    jw: *std.json.Stringify,
    compiler: ?*const mm0.Compiler,
    proof_src: ?[]const u8,
) !void {
    try jw.objectField("diagnostics");
    try jw.beginArray();
    if (compiler) |actual| {
        for (actual.primaryDiagnostics()) |diag| {
            try writeDiagnostic(jw, actual, diag);
        }
        if (actual.omittedPrimaryDiagnostic(.mm0)) |diag| {
            try writeDiagnostic(jw, actual, diag);
        }
        if (actual.omittedPrimaryDiagnostic(.proof)) |diag| {
            try writeDiagnostic(jw, actual, diag);
        }
        for (actual.warningDiagnostics()) |diag| {
            try writeDiagnostic(jw, actual, diag);
        }
    }
    if (proof_src) |src| try writePlaceholderDiagnostics(jw, compiler, src);
    try jw.endArray();
}

// One warning per search placeholder and one error per parameter it
// rejects (`Search.placeholderNotices`, the same notices the LSP publishes).
// The analysis pass tolerates placeholders (`allow_search_placeholders`), so
// they produce no compiler diagnostic of their own; without these a
// placeholder would look finished and a typo'd parameter would be silently
// ignored in the browser editor.
fn writePlaceholderDiagnostics(
    jw: *std.json.Stringify,
    compiler: ?*const mm0.Compiler,
    proof_src: []const u8,
) !void {
    var arena_state = std.heap.ArenaAllocator.init(allocator);
    defer arena_state.deinit();
    const notices = mm0.CompilerSupport.Search.placeholderNotices(
        arena_state.allocator(),
        proof_src,
    ) catch return;
    for (notices) |notice| {
        try jw.write(placed(compiler, .{
            .message = notice.message,
            .severity = switch (notice.kind) {
                .placeholder => .warning,
                .parameter => .@"error",
            },
            .source = .proof,
            .err = switch (notice.kind) {
                .placeholder => error.SearchPlaceholder,
                .parameter => error.InvalidSearchParameter,
            },
            .span = .{ .start = notice.span.start, .end = notice.span.end },
        }));
    }
}

/// A diagnostic this file makes up itself (placeholder status, a failed
/// join): the same JSON shape as a compiler diagnostic, with the fields the
/// compiler would leave empty set to null.
const SyntheticDiagnostic = struct {
    message: []const u8,
    severity: enum { @"error", warning } = .@"error",
    source: enum { mm0, proof },
    err: anyerror,
    /// The file the span lies in, when known (a join), else null.
    file: ?[]const u8 = null,
    /// Offsets into `file` when set, else into the whole source text.
    span: ?mm0.Imports.Span = null,

    pub fn jsonStringify(self: SyntheticDiagnostic, jw: *std.json.Stringify) !void {
        try jw.beginObject();
        try writeFields(jw, .{
            .message = self.message,
            .severity = self.severity,
            .source = self.source,
            .@"error" = self.err,
            .theorem = null,
            .block = null,
            .lineLabel = null,
            .rule = null,
            .name = null,
            .expected = null,
            .phase = null,
            .file = self.file,
            .spanStart = if (self.span) |span| span.start else null,
            .spanEnd = if (self.span) |span| span.end else null,
            .detail = null,
            .notes = no_items,
            .related = no_items,
        });
        try jw.endObject();
    }
};

/// `diag` with its whole-source span placed in its file, when the compiler
/// ran over a join.
fn placed(
    compiler: ?*const mm0.Compiler,
    diag: SyntheticDiagnostic,
) SyntheticDiagnostic {
    const actual = compiler orelse return diag;
    const span = diag.span orelse return diag;
    const source: mm0.CompilerDiagnosticSource = switch (diag.source) {
        .mm0 => .mm0,
        .proof => .proof,
    };
    const hit = actual.diagnostics.locateInFile(
        source,
        .{ .start = span.start, .end = span.end },
    ) orelse return diag;
    var out = diag;
    out.file = hit.label;
    out.span = hit.span;
    return out;
}

/// Write `"file":…,"spanStart":…,"spanEnd":…` for a span of `source`: the
/// file and file-local offsets when the compiler ran over a join, else a
/// null file and offsets into the whole source text.
fn writeSpanFields(
    jw: *std.json.Stringify,
    compiler: *const mm0.Compiler,
    source: mm0.CompilerDiagnosticSource,
    span: ?mm0.CompilerDiagnosticSpan,
) !void {
    var file: ?[]const u8 = null;
    var start: ?usize = null;
    var end: ?usize = null;
    if (span) |actual| {
        start = actual.start;
        end = actual.end;
        if (compiler.diagnostics.locateInFile(source, actual)) |hit| {
            file = hit.label;
            start = hit.span.start;
            end = hit.span.end;
        }
    }
    try writeFields(jw, .{ .file = file, .spanStart = start, .spanEnd = end });
}

fn writeDiagnostic(
    jw: *std.json.Stringify,
    compiler: *const mm0.Compiler,
    diag: mm0.CompilerDiagnostic,
) !void {
    // The shared renderer's full text (summary + context lines), matching
    // what the CLI and LSP show; notes/related stay in their structured
    // arrays.
    var text: std.Io.Writer.Allocating = .init(allocator);
    defer text.deinit();
    try mm0.renderCompilerDiagnostic(&text.writer, diag, "\n");

    try jw.beginObject();
    try writeFields(jw, .{
        .message = text.written(),
        .severity = diag.severity,
        .source = diag.source,
        .@"error" = diag.err,
        .theorem = diag.theorem_name,
        .block = diag.block_name,
        .lineLabel = diag.line_label,
        .rule = diag.rule_name,
        .name = diag.name,
        .expected = diag.expected_name,
        .phase = diag.phase,
    });
    try writeSpanFields(jw, compiler, diag.source, diag.span);
    try jw.objectField("detail");
    try diag_json.writeDetail(jw, allocator, diag);

    try jw.objectField("notes");
    try jw.beginArray();
    for (diag.noteSlice()) |note| {
        text.clearRetainingCapacity();
        try mm0.renderCompilerNoteMessage(&text.writer, note.message);
        try jw.beginObject();
        try writeFields(jw, .{ .message = text.written(), .source = note.source });
        try writeSpanFields(jw, compiler, note.source, note.span);
        try jw.endObject();
    }
    try jw.endArray();

    try jw.objectField("related");
    try jw.beginArray();
    for (diag.relatedSlice()) |related| {
        text.clearRetainingCapacity();
        try mm0.renderCompilerRelatedLabel(&text.writer, related.label);
        try jw.beginObject();
        try writeFields(jw, .{ .label = text.written(), .source = related.source });
        try writeSpanFields(jw, compiler, related.source, related.span);
        try jw.endObject();
    }
    try jw.endArray();
    try jw.endObject();
}

// Pretty-printed statement snapshots: `[{name, kind, local, hyps, concl,
// signature, body}]`.
fn writeStatementsField(
    jw: *std.json.Stringify,
    statements: *const mm0.StatementSink,
) !void {
    try jw.objectField("statements");
    try jw.beginArray();
    for (statements.items()) |stmt| {
        try jw.write(.{
            .name = stmt.name,
            .kind = stmt.kind,
            .local = stmt.is_local,
            .hyps = stmt.hyps,
            .concl = stmt.concl,
            .signature = stmt.signature,
            .body = stmt.body,
        });
    }
    try jw.endArray();
}
