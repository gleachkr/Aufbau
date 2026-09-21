const std = @import("std");
const mm0 = @import("mm0");
const json_out = @import("json_out.zig");

// JSON string emitters live in `json_out.zig` so they can be unit-tested
// natively (this file pins `wasm_allocator` and only builds for wasm32). Every
// string value — including source-derived ones like a diagnostic's echoed math
// token — is escaped, so the result buffer is always valid JSON.
const writeJsonString = json_out.writeString;
const writeOptionalJsonString = json_out.writeOptionalString;
const writeJsonStringField = json_out.writeStringField;
const writeOptionalStringField = json_out.writeOptionalStringField;

// Structured diagnostic-field renderers live in `diag_json.zig` for the same
// reason: the exhaustive `DiagnosticDetail` switch must be analyzed by the
// native test build, not just this wasm-only file.
const diag_json = @import("diag_json.zig");
const writeDiagnosticDetailField = diag_json.writeDetailField;
const diagnosticPhaseName = diag_json.phaseName;
const writeOptionalUsizeField = diag_json.writeOptionalUsizeField;

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
        // checker stops cleanly at it, and a warning-severity diagnostic per
        // placeholder is synthesized below (`writePlaceholderDiagnostics`).
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

fn writeCompileSuccess(
    compiler: *const mm0.Compiler,
    mmb_len: usize,
    statements: *const mm0.StatementSink,
) !void {
    var out: std.io.Writer.Allocating = .init(allocator);
    errdefer out.deinit();

    try out.writer.writeAll("{");
    try out.writer.writeAll("\"ok\":true,");
    try out.writer.writeAll("\"phase\":\"compile\",");
    try out.writer.writeAll("\"message\":\"ok\",");
    try out.writer.writeAll("\"error\":null,");
    try out.writer.writeAll("\"mmbLen\":");
    try out.writer.print("{d}", .{mmb_len});
    try out.writer.writeAll(",\"diagnostic\":null,");
    // A clean compile still carries warnings — an admitted line (`sorry!`)
    // above all, which the editor must see to withhold its seal.
    try writeDiagnosticsField(&out.writer, compiler, null);
    try out.writer.writeByte(',');
    try writeStatementsField(&out.writer, statements);
    try out.writer.writeByte('}');

    result_json = try out.toOwnedSlice();
}

fn writeCompileFailure(
    compiler: *const mm0.Compiler,
    analysis_compiler: *const mm0.Compiler,
    statements: *const mm0.StatementSink,
    proof_src: []const u8,
    err: anyerror,
) !void {
    var out: std.io.Writer.Allocating = .init(allocator);
    errdefer out.deinit();

    try out.writer.writeAll("{");
    try out.writer.writeAll("\"ok\":false,");
    try out.writer.writeAll("\"phase\":\"compile\",");
    try writeJsonStringField(&out.writer, "error", @errorName(err));
    try out.writer.writeByte(',');

    if (compiler.diagnostics.last_diagnostic) |diag| {
        try writeJsonStringField(
            &out.writer,
            "message",
            mm0.compilerDiagnosticSummary(diag),
        );
        try out.writer.writeAll(",\"mmbLen\":0,\"diagnostic\":");
        try writeDiagnosticObject(&out.writer, compiler, diag);
    } else {
        try writeJsonStringField(&out.writer, "message", mm0.compilerErrorSummary(err));
        try out.writer.writeAll(",\"mmbLen\":0,\"diagnostic\":null");
    }
    try out.writer.writeByte(',');
    try writeDiagnosticsField(&out.writer, analysis_compiler, proof_src);
    try out.writer.writeByte(',');
    try writeStatementsField(&out.writer, statements);
    try out.writer.writeByte('}');

    result_json = try out.toOwnedSlice();
}

/// A `compile_files` request that could not be read at all.
fn writeRequestFailure(err: anyerror) !void {
    var out: std.io.Writer.Allocating = .init(allocator);
    errdefer out.deinit();
    try out.writer.writeAll("{\"ok\":false,\"phase\":\"compile\",");
    try writeJsonStringField(&out.writer, "error", @errorName(err));
    try out.writer.writeByte(',');
    try writeJsonStringField(
        &out.writer,
        "message",
        "malformed compile request",
    );
    try out.writer.writeAll(
        ",\"mmbLen\":0,\"diagnostic\":null,\"diagnostics\":[],\"statements\":[]}",
    );
    result_json = try out.toOwnedSlice();
}

/// A file table whose imports or includes could not be joined: one error
/// diagnostic on the failing statement (or, for a missing root, none).
fn writeLoadFailure(
    arena: std.mem.Allocator,
    failure: ?mm0.Imports.LoadFailure,
    err: anyerror,
) !void {
    var out: std.io.Writer.Allocating = .init(allocator);
    errdefer out.deinit();
    try out.writer.writeAll("{\"ok\":false,\"phase\":\"compile\",");
    try writeJsonStringField(&out.writer, "error", @errorName(err));
    try out.writer.writeByte(',');

    var synthetic: ?SyntheticDiagnostic = null;
    if (failure) |info| switch (info) {
        .read => |read| synthetic = .{
            .message = try std.fmt.allocPrint(
                arena,
                "unable to read '{s}': {s}",
                .{ read.path, @errorName(read.err) },
            ),
            .source = if (std.mem.endsWith(u8, read.path, ".auf")) .proof else .mm0,
            .err = read.err,
        },
        .join => |join_info| {
            var join = join_info;
            if (join.err == null) join.err = err;
            synthetic = .{
                .message = try join.message(arena),
                .source = switch (join.syntax) {
                    .mm0 => .mm0,
                    .auf => .proof,
                },
                .err = err,
                .file = join.file_key,
                .span = .{ .start = join.span.start, .end = join.span.end },
            };
        },
    };
    try writeJsonStringField(
        &out.writer,
        "message",
        if (synthetic) |diag| diag.message else @errorName(err),
    );
    try out.writer.writeAll(",\"mmbLen\":0,\"diagnostic\":");
    if (synthetic) |diag| {
        try writeSyntheticDiagnostic(&out.writer, diag);
        try out.writer.writeAll(",\"diagnostics\":[");
        try writeSyntheticDiagnostic(&out.writer, diag);
        try out.writer.writeAll("],");
    } else {
        try out.writer.writeAll("null,\"diagnostics\":[],");
    }
    try out.writer.writeAll("\"statements\":[]}");
    result_json = try out.toOwnedSlice();
}

fn writeDiagnosticsField(
    writer: anytype,
    compiler: ?*const mm0.Compiler,
    proof_src: ?[]const u8,
) !void {
    try writer.writeAll("\"diagnostics\":[");

    var need_comma = false;
    if (compiler) |actual| {
        for (actual.primaryDiagnostics()) |diag| {
            if (need_comma) try writer.writeByte(',');
            try writeDiagnosticObject(writer, actual, diag);
            need_comma = true;
        }
        if (actual.omittedPrimaryDiagnostic(.mm0)) |diag| {
            if (need_comma) try writer.writeByte(',');
            try writeDiagnosticObject(writer, actual, diag);
            need_comma = true;
        }
        if (actual.omittedPrimaryDiagnostic(.proof)) |diag| {
            if (need_comma) try writer.writeByte(',');
            try writeDiagnosticObject(writer, actual, diag);
            need_comma = true;
        }
        for (actual.warningDiagnostics()) |diag| {
            if (need_comma) try writer.writeByte(',');
            try writeDiagnosticObject(writer, actual, diag);
            need_comma = true;
        }
    }
    if (proof_src) |src| {
        try writePlaceholderDiagnostics(writer, compiler, src, &need_comma);
    }

    try writer.writeByte(']');
}

// One warning per search placeholder, mirroring the LSP's "search not yet
// run". The analysis pass tolerates placeholders (`allow_search_placeholders`)
// so they produce no compiler diagnostic of their own; this is the signal
// that marks them as unfilled holes rather than errors. Rejected search
// parameters (unknown name, out-of-range value) additionally get one error
// each, mirroring the LSP's `validateSearchParams` diagnostics — without
// them a typo'd parameter is silently ignored in the browser editor.
fn writePlaceholderDiagnostics(
    writer: anytype,
    compiler: ?*const mm0.Compiler,
    proof_src: []const u8,
    need_comma: *bool,
) !void {
    const placeholders = mm0.CompilerSupport.Search.searchPlaceholders(
        allocator,
        proof_src,
    ) catch return;
    defer allocator.free(placeholders);

    var message: std.io.Writer.Allocating = .init(allocator);
    defer message.deinit();
    for (placeholders) |placeholder| {
        if (need_comma.*) try writer.writeByte(',');
        need_comma.* = true;
        message.clearRetainingCapacity();
        try message.writer.print(
            "{s} placeholder: proof search has not filled this hole",
            .{placeholder.kind.keyword()},
        );
        try writeSyntheticDiagnostic(writer, placed(compiler, .{
            .message = message.written(),
            .severity = .warning,
            .source = .proof,
            .err = error.SearchPlaceholder,
            .span = .{
                .start = placeholder.span.start,
                .end = placeholder.span.end,
            },
        }));

        const issues = mm0.CompilerSupport.Search.tunables.validateSearchParams(
            allocator,
            placeholder.kind.paramContext(),
            placeholder.params,
        ) catch continue;
        defer {
            for (issues) |issue| allocator.free(issue.message);
            allocator.free(issues);
        }
        for (issues) |issue| {
            try writer.writeByte(',');
            try writeSyntheticDiagnostic(writer, placed(compiler, .{
                .message = issue.message,
                .severity = .@"error",
                .source = .proof,
                .err = error.InvalidSearchParameter,
                .span = .{ .start = issue.span.start, .end = issue.span.end },
            }));
        }
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

fn writeSyntheticDiagnostic(
    writer: anytype,
    diag: SyntheticDiagnostic,
) !void {
    try writer.writeByte('{');
    try writeJsonStringField(writer, "message", diag.message);
    try writer.writeByte(',');
    try writeJsonStringField(writer, "severity", @tagName(diag.severity));
    try writer.writeByte(',');
    try writeJsonStringField(writer, "source", @tagName(diag.source));
    try writer.writeByte(',');
    try writeJsonStringField(writer, "error", @errorName(diag.err));
    try writer.writeAll(
        ",\"theorem\":null,\"block\":null,\"lineLabel\":null,\"rule\":null," ++
            "\"name\":null,\"expected\":null,\"phase\":null,",
    );
    try writeOptionalStringField(writer, "file", diag.file);
    try writer.writeByte(',');
    try writeOptionalUsizeField(
        writer,
        "spanStart",
        if (diag.span) |span| span.start else null,
    );
    try writer.writeByte(',');
    try writeOptionalUsizeField(
        writer,
        "spanEnd",
        if (diag.span) |span| span.end else null,
    );
    try writer.writeAll(",\"detail\":null,\"notes\":[],\"related\":[]}");
}

/// Write `"file":…,"spanStart":…,"spanEnd":…` for a span of `source`: the
/// file and file-local offsets when the compiler ran over a join, else a
/// null file and offsets into the whole source text.
fn writeSpanFields(
    writer: anytype,
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
    try writeOptionalStringField(writer, "file", file);
    try writer.writeByte(',');
    try writeOptionalUsizeField(writer, "spanStart", start);
    try writer.writeByte(',');
    try writeOptionalUsizeField(writer, "spanEnd", end);
}

fn writeDiagnosticObject(
    writer: anytype,
    compiler: *const mm0.Compiler,
    diag: mm0.CompilerDiagnostic,
) !void {
    // The shared renderer's full text (summary + context lines), matching
    // what the CLI and LSP show. Rendered to a scratch buffer first so it
    // can be JSON-escaped; notes/related stay in their structured arrays.
    var message: std.io.Writer.Allocating = .init(allocator);
    defer message.deinit();
    try mm0.renderCompilerDiagnostic(&message.writer, diag, "\n");

    try writer.writeByte('{');
    try writeJsonStringField(writer, "message", message.written());
    try writer.writeByte(',');
    try writeJsonStringField(writer, "severity", @tagName(diag.severity));
    try writer.writeByte(',');
    try writeJsonStringField(writer, "source", @tagName(diag.source));
    try writer.writeByte(',');
    try writeJsonStringField(writer, "error", @errorName(diag.err));
    try writer.writeByte(',');
    try writeOptionalStringField(writer, "theorem", diag.theorem_name);
    try writer.writeByte(',');
    try writeOptionalStringField(writer, "block", diag.block_name);
    try writer.writeByte(',');
    try writeOptionalStringField(writer, "lineLabel", diag.line_label);
    try writer.writeByte(',');
    try writeOptionalStringField(writer, "rule", diag.rule_name);
    try writer.writeByte(',');
    try writeOptionalStringField(writer, "name", diag.name);
    try writer.writeByte(',');
    try writeOptionalStringField(writer, "expected", diag.expected_name);
    try writer.writeByte(',');
    try writeOptionalStringField(
        writer,
        "phase",
        if (diag.phase) |phase|
            diagnosticPhaseName(phase)
        else
            null,
    );
    try writer.writeByte(',');
    try writeSpanFields(writer, compiler, diag.source, diag.span);
    try writer.writeByte(',');
    try writeDiagnosticDetailField(writer, diag);
    try writer.writeByte(',');
    try writeDiagnosticNotesField(writer, compiler, diag);
    try writer.writeByte(',');
    try writeDiagnosticRelatedField(writer, compiler, diag);
    try writer.writeByte('}');
}

// Pretty-printed statement snapshots: `[{name, kind, local, hyps, concl,
// signature, body}]`. Rendered math can contain any notation token (`\/`,
// quotes), so these values are JSON-escaped via `writeJsonString` — as are all
// the diagnostic string fields above.
fn writeStatementsField(
    writer: anytype,
    statements: *const mm0.StatementSink,
) !void {
    try writer.writeAll("\"statements\":[");
    for (statements.items(), 0..) |stmt, idx| {
        if (idx != 0) try writer.writeByte(',');
        try writer.writeAll("{\"name\":");
        try writeJsonString(writer, stmt.name);
        try writer.print(
            ",\"kind\":\"{s}\",\"local\":{},\"hyps\":[",
            .{ @tagName(stmt.kind), stmt.is_local },
        );
        for (stmt.hyps, 0..) |hyp, hyp_idx| {
            if (hyp_idx != 0) try writer.writeByte(',');
            try writeJsonString(writer, hyp);
        }
        try writer.writeAll("],\"concl\":");
        try writeOptionalJsonString(writer, stmt.concl);
        try writer.writeAll(",\"signature\":");
        try writeOptionalJsonString(writer, stmt.signature);
        try writer.writeAll(",\"body\":");
        try writeOptionalJsonString(writer, stmt.body);
        try writer.writeByte('}');
    }
    try writer.writeByte(']');
}

fn writeDiagnosticNotesField(
    writer: anytype,
    compiler: *const mm0.Compiler,
    diag: mm0.CompilerDiagnostic,
) !void {
    var message: std.io.Writer.Allocating = .init(allocator);
    defer message.deinit();
    try writer.writeAll("\"notes\":[");
    for (diag.noteSlice(), 0..) |note, idx| {
        if (idx != 0) try writer.writeByte(',');
        message.clearRetainingCapacity();
        try mm0.renderCompilerNoteMessage(&message.writer, note.message);
        try writer.writeAll("{");
        try writeJsonStringField(writer, "message", message.written());
        try writer.writeByte(',');
        try writeJsonStringField(writer, "source", @tagName(note.source));
        try writer.writeByte(',');
        try writeSpanFields(writer, compiler, note.source, note.span);
        try writer.writeAll("}");
    }
    try writer.writeByte(']');
}

fn writeDiagnosticRelatedField(
    writer: anytype,
    compiler: *const mm0.Compiler,
    diag: mm0.CompilerDiagnostic,
) !void {
    var label: std.io.Writer.Allocating = .init(allocator);
    defer label.deinit();
    try writer.writeAll("\"related\":[");
    for (diag.relatedSlice(), 0..) |related, idx| {
        if (idx != 0) try writer.writeByte(',');
        label.clearRetainingCapacity();
        try mm0.renderCompilerRelatedLabel(&label.writer, related.label);
        try writer.writeAll("{");
        try writeJsonStringField(writer, "label", label.written());
        try writer.writeByte(',');
        try writeJsonStringField(
            writer,
            "source",
            @tagName(related.source),
        );
        try writer.writeByte(',');
        try writeSpanFields(writer, compiler, related.source, related.span);
        try writer.writeAll("}");
    }
    try writer.writeByte(']');
}
