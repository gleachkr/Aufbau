const std = @import("std");
const lsp = @import("lsp");
const mm0 = @import("mm0");

pub const SERVER_NAME = "Aufbau";

const LspIndex = mm0.Frontend.LspIndex;
const types = lsp.types;

pub const DiagnosticDocument = struct {
    uri: []const u8,
    text: []const u8,
    version: ?i32,
};

pub const DiagnosticContext = struct {
    mm0: ?DiagnosticDocument = null,
    proof: ?DiagnosticDocument = null,

    pub fn sourceDocument(
        self: DiagnosticContext,
        source: mm0.CompilerDiagnosticSource,
    ) ?DiagnosticDocument {
        return switch (source) {
            .mm0 => self.mm0,
            .proof => self.proof,
        };
    }
};

pub fn compilerDiagnosticsToLsp(
    arena: std.mem.Allocator,
    diag_context: DiagnosticContext,
    diags: []const mm0.CompilerDiagnostic,
    source: mm0.CompilerDiagnosticSource,
    encoding: lsp.offsets.Encoding,
) ![]types.Diagnostic {
    var count: usize = 0;
    for (diags) |diag| {
        if (diag.source == source) count += 1;
    }
    const result = try arena.alloc(types.Diagnostic, count);
    var out_idx: usize = 0;
    for (diags) |diag| {
        if (diag.source != source) continue;
        result[out_idx] = try compilerDiagnosticToLsp(
            arena,
            diag_context,
            diag,
            encoding,
        );
        out_idx += 1;
    }
    return result;
}

pub fn compilerSourceDiagnosticsToLsp(
    arena: std.mem.Allocator,
    diag_context: DiagnosticContext,
    primary: []const mm0.CompilerDiagnostic,
    warnings: []const mm0.CompilerDiagnostic,
    extra: ?mm0.CompilerDiagnostic,
    omitted: ?mm0.CompilerDiagnostic,
    source: mm0.CompilerDiagnosticSource,
    encoding: lsp.offsets.Encoding,
) ![]types.Diagnostic {
    var count: usize = 0;
    if (extra) |diag| {
        if (diag.source == source) count += 1;
    }
    for (primary) |diag| {
        if (diag.source == source) count += 1;
    }
    for (warnings) |diag| {
        if (diag.source == source) count += 1;
    }
    if (omitted) |diag| {
        if (diag.source == source) count += 1;
    }

    const result = try arena.alloc(types.Diagnostic, count);
    var out_idx: usize = 0;
    if (extra) |diag| {
        if (diag.source == source) {
            result[out_idx] = try compilerDiagnosticToLsp(
                arena,
                diag_context,
                diag,
                encoding,
            );
            out_idx += 1;
        }
    }
    for (primary) |diag| {
        if (diag.source != source) continue;
        result[out_idx] = try compilerDiagnosticToLsp(
            arena,
            diag_context,
            diag,
            encoding,
        );
        out_idx += 1;
    }
    if (omitted) |diag| {
        if (diag.source == source) {
            result[out_idx] = try compilerDiagnosticToLsp(
                arena,
                diag_context,
                diag,
                encoding,
            );
            out_idx += 1;
        }
    }
    for (warnings) |diag| {
        if (diag.source != source) continue;
        result[out_idx] = try compilerDiagnosticToLsp(
            arena,
            diag_context,
            diag,
            encoding,
        );
        out_idx += 1;
    }
    return result;
}

pub fn compilerDiagnosticToLsp(
    arena: std.mem.Allocator,
    diag_context: DiagnosticContext,
    diag: mm0.CompilerDiagnostic,
    encoding: lsp.offsets.Encoding,
) !types.Diagnostic {
    const doc = diag_context.sourceDocument(diag.source) orelse {
        return error.MissingDiagnosticDocument;
    };
    return .{
        .range = rangeForDiagnostic(doc.text, diag, encoding),
        .severity = diagnosticSeverityToLsp(diag.severity),
        .source = SERVER_NAME,
        .message = try compilerDiagnosticMessage(arena, diag),
        .relatedInformation = try compilerDiagnosticRelatedInformation(
            arena,
            diag_context,
            diag,
            encoding,
        ),
    };
}

pub fn diagnosticSeverityToLsp(
    severity: mm0.CompilerDiagnosticSeverity,
) types.DiagnosticSeverity {
    return switch (severity) {
        .@"error" => .Error,
        .warning => .Warning,
    };
}

fn rangeForDiagnostic(
    text: []const u8,
    diag: mm0.CompilerDiagnostic,
    encoding: lsp.offsets.Encoding,
) types.Range {
    const span = diag.span orelse return zeroRange(text, encoding);
    const start = @min(span.start, text.len);
    const end = @max(start, @min(span.end, text.len));
    return lsp.offsets.locToRange(
        text,
        .{ .start = start, .end = end },
        encoding,
    );
}

pub fn zeroRange(
    text: []const u8,
    encoding: lsp.offsets.Encoding,
) types.Range {
    return lsp.offsets.locToRange(
        text,
        .{ .start = 0, .end = 0 },
        encoding,
    );
}

pub fn sourceRangeToLsp(
    snapshot: *const LspIndex.Snapshot,
    range: LspIndex.SourceRange,
    encoding: lsp.offsets.Encoding,
) types.Range {
    const text = snapshot.textForDocument(range.document) orelse "";
    const start = @min(range.start, text.len);
    const end = @max(start, @min(range.end, text.len));
    return lsp.offsets.locToRange(
        text,
        .{ .start = start, .end = end },
        encoding,
    );
}

pub fn sourceRangesToLocations(
    allocator: std.mem.Allocator,
    snapshot: *const LspIndex.Snapshot,
    ranges: []const LspIndex.SourceRange,
    encoding: lsp.offsets.Encoding,
) ![]const types.Location {
    var locations = std.ArrayListUnmanaged(types.Location){};
    for (ranges) |range| {
        const uri = snapshot.uriForDocument(range.document) orelse continue;
        try locations.append(allocator, .{
            .uri = uri,
            .range = sourceRangeToLsp(snapshot, range, encoding),
        });
    }
    return try locations.toOwnedSlice(allocator);
}

pub fn completionsToLsp(
    arena: std.mem.Allocator,
    snapshot: *const LspIndex.Snapshot,
    completions: []const LspIndex.CompletionItem,
    encoding: lsp.offsets.Encoding,
) ![]const types.CompletionItem {
    const result = try arena.alloc(types.CompletionItem, completions.len);
    for (completions, 0..) |item, i| {
        result[i] = .{
            .label = item.label,
            .kind = completionKindToLsp(item.kind),
            .detail = item.detail,
            .documentation = if (item.documentation_markdown) |doc|
                .{ .MarkupContent = .{ .kind = .markdown, .value = doc } }
            else
                null,
            .sortText = item.sort_text,
            .filterText = item.filter_text,
            .insertTextFormat = if (item.snippet_replacement_text != null)
                .Snippet
            else
                .PlainText,
            .textEdit = .{ .TextEdit = .{
                .range = sourceRangeToLsp(
                    snapshot,
                    item.replacement,
                    encoding,
                ),
                .newText = item.snippet_replacement_text orelse
                    item.replacement_text,
            } },
        };
    }
    return result;
}

fn completionKindToLsp(
    kind: LspIndex.CompletionKind,
) types.CompletionItemKind {
    return switch (kind) {
        .keyword, .modifier, .annotation => .Keyword,
        .sort => .Class,
        .term, .def => .Function,
        .notation => .Operator,
        .snippet => .Snippet,
        .axiom, .theorem, .lemma => .Method,
        .proof_line => .Reference,
        .hypothesis => .Value,
        .binder => .Variable,
    };
}

pub fn outlineSymbolsToLsp(
    arena: std.mem.Allocator,
    snapshot: *const LspIndex.Snapshot,
    symbols: []const LspIndex.OutlineSymbol,
    encoding: lsp.offsets.Encoding,
) ![]const types.DocumentSymbol {
    const result = try arena.alloc(types.DocumentSymbol, symbols.len);
    for (symbols, 0..) |symbol, i| {
        result[i] = .{
            .name = symbol.name,
            .detail = symbol.kind.label(),
            .kind = declarationSymbolKind(symbol.kind),
            .range = sourceRangeToLsp(snapshot, symbol.range, encoding),
            .selectionRange = sourceRangeToLsp(
                snapshot,
                symbol.selection_range,
                encoding,
            ),
            .children = if (symbol.children.len == 0)
                null
            else
                try outlineSymbolsToLsp(
                    arena,
                    snapshot,
                    symbol.children,
                    encoding,
                ),
        };
    }
    return result;
}

fn declarationSymbolKind(kind: LspIndex.DeclarationKind) types.SymbolKind {
    return switch (kind) {
        .sort => .Class,
        .term, .def => .Function,
        .axiom, .theorem, .lemma => .Method,
        .proof_line, .sort_var => .Variable,
    };
}

pub fn compilerDiagnosticRelatedInformation(
    arena: std.mem.Allocator,
    diag_context: DiagnosticContext,
    diag: mm0.CompilerDiagnostic,
    encoding: lsp.offsets.Encoding,
) !?[]const types.DiagnosticRelatedInformation {
    var count: usize = 0;
    for (diag.noteSlice()) |note| {
        if (note.span != null and
            diag_context.sourceDocument(note.source) != null)
        {
            count += 1;
        }
    }
    for (diag.relatedSlice()) |related| {
        if (diag_context.sourceDocument(related.source) != null) {
            count += 1;
        }
    }
    if (count == 0) return null;

    const result = try arena.alloc(types.DiagnosticRelatedInformation, count);
    var idx: usize = 0;
    for (diag.noteSlice()) |note| {
        const span = note.span orelse continue;
        const doc = diag_context.sourceDocument(note.source) orelse continue;
        result[idx] = .{
            .location = .{
                .uri = doc.uri,
                .range = lsp.offsets.locToRange(
                    doc.text,
                    .{ .start = span.start, .end = span.end },
                    encoding,
                ),
            },
            .message = try noteMessageText(arena, note.message),
        };
        idx += 1;
    }
    for (diag.relatedSlice()) |related| {
        const doc = diag_context.sourceDocument(related.source) orelse continue;
        result[idx] = .{
            .location = .{
                .uri = doc.uri,
                .range = lsp.offsets.locToRange(
                    doc.text,
                    .{ .start = related.span.start, .end = related.span.end },
                    encoding,
                ),
            },
            .message = try relatedLabelText(arena, related.label),
        };
        idx += 1;
    }
    return result;
}

fn noteMessageText(
    arena: std.mem.Allocator,
    message: mm0.CompilerNoteMessage,
) ![]const u8 {
    var buf = std.ArrayListUnmanaged(u8){};
    var writer = buf.writer(arena);
    try mm0.renderCompilerNoteMessage(&writer, message);
    return buf.items;
}

fn relatedLabelText(
    arena: std.mem.Allocator,
    label: mm0.CompilerRelatedLabel,
) ![]const u8 {
    var buf = std.ArrayListUnmanaged(u8){};
    var writer = buf.writer(arena);
    try mm0.renderCompilerRelatedLabel(&writer, label);
    return buf.items;
}

pub fn compilerDiagnosticMessage(
    arena: std.mem.Allocator,
    diag: mm0.CompilerDiagnostic,
) ![]const u8 {
    var buf = std.ArrayListUnmanaged(u8){};
    var writer = buf.writer(arena);

    try mm0.renderCompilerDiagnostic(&writer, diag, "\n");
    for (diag.noteSlice()) |note| {
        try writer.print("\n{s}: ", .{mm0.compilerNoteHeading()});
        try mm0.renderCompilerNoteMessage(&writer, note.message);
    }
    for (diag.relatedSlice()) |related| {
        try writer.print("\n{s}: ", .{mm0.compilerRelatedHeading()});
        try mm0.renderCompilerRelatedLabel(&writer, related.label);
    }

    return buf.items;
}
