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

pub const Span = struct {
    start: usize,
    end: usize,
};

/// A compiler span resolved to the document it should be reported against.
pub const LocatedSpan = struct {
    uri: []const u8,
    text: []const u8,
    version: ?i32,
    span: Span,
};

/// Maps a span in the text the compiler saw to the file it was copied
/// from. A host that joins several files (imports, includes) supplies one;
/// without it every span is read against the context's own documents.
pub const SpanLocator = struct {
    ctx: *const anyopaque,
    locateFn: *const fn (
        ctx: *const anyopaque,
        source: mm0.CompilerDiagnosticSource,
        span: Span,
    ) ?LocatedSpan,
};

pub const DiagnosticContext = struct {
    mm0: ?DiagnosticDocument = null,
    proof: ?DiagnosticDocument = null,
    locator: ?SpanLocator = null,

    pub fn sourceDocument(
        self: DiagnosticContext,
        source: mm0.CompilerDiagnosticSource,
    ) ?DiagnosticDocument {
        return switch (source) {
            .mm0 => self.mm0,
            .proof => self.proof,
        };
    }

    /// The document and span a compiler span reports against: the file
    /// the locator names when there is one, else the source's document. A
    /// missing span lands at the start of the source's document.
    pub fn locate(
        self: DiagnosticContext,
        source: mm0.CompilerDiagnosticSource,
        span: ?Span,
    ) ?LocatedSpan {
        if (span) |s| {
            if (self.locator) |locator| {
                if (locator.locateFn(locator.ctx, source, s)) |hit| return hit;
            }
        }
        const doc = self.sourceDocument(source) orelse return null;
        return .{
            .uri = doc.uri,
            .text = doc.text,
            .version = doc.version,
            .span = span orelse .{ .start = 0, .end = 0 },
        };
    }
};

/// An LSP diagnostic with the document it belongs to.
pub const LocatedDiagnostic = struct {
    uri: []const u8,
    version: ?i32,
    diagnostic: types.Diagnostic,
};

/// Every diagnostic of a compile, located: proof-side first, then
/// `.mm0`-side, each in the order `compilerSourceDiagnosticsToLsp` uses.
/// A diagnostic whose document the context cannot name is dropped.
pub fn locateCompilerDiagnostics(
    arena: std.mem.Allocator,
    diag_context: DiagnosticContext,
    primary: []const mm0.CompilerDiagnostic,
    warnings: []const mm0.CompilerDiagnostic,
    extra: ?mm0.CompilerDiagnostic,
    proof_omitted: ?mm0.CompilerDiagnostic,
    mm0_omitted: ?mm0.CompilerDiagnostic,
    encoding: lsp.offsets.Encoding,
) ![]LocatedDiagnostic {
    var out = std.ArrayListUnmanaged(LocatedDiagnostic){};
    const sources = [_]mm0.CompilerDiagnosticSource{ .proof, .mm0 };
    for (sources) |source| {
        const omitted = switch (source) {
            .proof => proof_omitted,
            .mm0 => mm0_omitted,
        };
        if (extra) |diag| {
            if (diag.source == source) {
                try appendLocated(arena, &out, diag_context, diag, encoding);
            }
        }
        for (primary) |diag| {
            if (diag.source != source) continue;
            try appendLocated(arena, &out, diag_context, diag, encoding);
        }
        if (omitted) |diag| {
            if (diag.source == source) {
                try appendLocated(arena, &out, diag_context, diag, encoding);
            }
        }
        for (warnings) |diag| {
            if (diag.source != source) continue;
            try appendLocated(arena, &out, diag_context, diag, encoding);
        }
    }
    return try out.toOwnedSlice(arena);
}

fn appendLocated(
    arena: std.mem.Allocator,
    out: *std.ArrayListUnmanaged(LocatedDiagnostic),
    diag_context: DiagnosticContext,
    diag: mm0.CompilerDiagnostic,
    encoding: lsp.offsets.Encoding,
) !void {
    const hit = diag_context.locate(diag.source, spanOf(diag.span)) orelse return;
    try out.append(arena, .{
        .uri = hit.uri,
        .version = hit.version,
        .diagnostic = try compilerDiagnosticToLsp(
            arena,
            diag_context,
            diag,
            encoding,
        ),
    });
}

fn spanOf(span: anytype) ?Span {
    const s = span orelse return null;
    return .{ .start = s.start, .end = s.end };
}

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
    const hit = diag_context.locate(diag.source, spanOf(diag.span)) orelse {
        return error.MissingDiagnosticDocument;
    };
    return .{
        .range = clampedRange(hit.text, hit.span, encoding),
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

fn clampedRange(
    text: []const u8,
    span: Span,
    encoding: lsp.offsets.Encoding,
) types.Range {
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

/// A navigation range resolved to the document it lies in.
pub const LocatedRange = struct {
    uri: []const u8,
    text: []const u8,
    span: Span,
};

/// Maps an index range (in the text the index was built over) to a
/// document. Hosts that index a join supply their own; `snapshotLocator`
/// reads ranges against the snapshot's own texts.
pub const RangeLocator = struct {
    ctx: *const anyopaque,
    locateFn: *const fn (
        ctx: *const anyopaque,
        range: LspIndex.SourceRange,
    ) ?LocatedRange,

    pub fn locate(
        self: RangeLocator,
        range: LspIndex.SourceRange,
    ) ?LocatedRange {
        return self.locateFn(self.ctx, range);
    }

    pub fn toLsp(
        self: RangeLocator,
        range: LspIndex.SourceRange,
        encoding: lsp.offsets.Encoding,
    ) ?types.Range {
        const hit = self.locate(range) orelse return null;
        return clampedRange(hit.text, hit.span, encoding);
    }

    pub fn toLocation(
        self: RangeLocator,
        range: LspIndex.SourceRange,
        encoding: lsp.offsets.Encoding,
    ) ?types.Location {
        const hit = self.locate(range) orelse return null;
        return .{
            .uri = hit.uri,
            .range = clampedRange(hit.text, hit.span, encoding),
        };
    }
};

pub fn snapshotLocator(snapshot: *const LspIndex.Snapshot) RangeLocator {
    return .{ .ctx = @ptrCast(snapshot), .locateFn = locateInSnapshot };
}

fn locateInSnapshot(
    ctx: *const anyopaque,
    range: LspIndex.SourceRange,
) ?LocatedRange {
    const snapshot: *const LspIndex.Snapshot = @ptrCast(@alignCast(ctx));
    const uri = snapshot.uriForDocument(range.document) orelse return null;
    const text = snapshot.textForDocument(range.document) orelse return null;
    return .{
        .uri = uri,
        .text = text,
        .span = .{ .start = range.start, .end = range.end },
    };
}

pub fn sourceRangesToLocations(
    allocator: std.mem.Allocator,
    locator: RangeLocator,
    ranges: []const LspIndex.SourceRange,
    encoding: lsp.offsets.Encoding,
) ![]const types.Location {
    var locations = std.ArrayListUnmanaged(types.Location){};
    for (ranges) |range| {
        const location = locator.toLocation(range, encoding) orelse continue;
        try locations.append(allocator, location);
    }
    return try locations.toOwnedSlice(allocator);
}

/// Completion items whose replacement range lies outside the requesting
/// document (it never should) are dropped rather than mis-ranged.
pub fn completionsToLsp(
    arena: std.mem.Allocator,
    locator: RangeLocator,
    completions: []const LspIndex.CompletionItem,
    encoding: lsp.offsets.Encoding,
) ![]const types.CompletionItem {
    var result = try std.ArrayListUnmanaged(types.CompletionItem).initCapacity(
        arena,
        completions.len,
    );
    for (completions) |item| {
        const range = locator.toLsp(item.replacement, encoding) orelse continue;
        result.appendAssumeCapacity(.{
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
                .range = range,
                .newText = item.snippet_replacement_text orelse
                    item.replacement_text,
            } },
        });
    }
    return result.items;
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

/// The outline of one document: symbols the locator places in `uri`
/// (with all their children), skipping those from other files of a join.
pub fn outlineSymbolsToLsp(
    arena: std.mem.Allocator,
    locator: RangeLocator,
    uri: []const u8,
    symbols: []const LspIndex.OutlineSymbol,
    encoding: lsp.offsets.Encoding,
) ![]const types.DocumentSymbol {
    var result = try std.ArrayListUnmanaged(types.DocumentSymbol).initCapacity(
        arena,
        symbols.len,
    );
    for (symbols) |symbol| {
        const hit = locator.locate(symbol.range) orelse continue;
        if (!std.mem.eql(u8, hit.uri, uri)) continue;
        const selection = locator.toLsp(symbol.selection_range, encoding) orelse
            continue;
        result.appendAssumeCapacity(.{
            .name = symbol.name,
            .detail = symbol.kind.label(),
            .kind = declarationSymbolKind(symbol.kind),
            .range = clampedRange(hit.text, hit.span, encoding),
            .selectionRange = selection,
            .children = if (symbol.children.len == 0)
                null
            else
                try outlineSymbolsToLsp(
                    arena,
                    locator,
                    uri,
                    symbol.children,
                    encoding,
                ),
        });
    }
    return result.items;
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
    var result = std.ArrayListUnmanaged(types.DiagnosticRelatedInformation){};
    for (diag.noteSlice()) |note| {
        const span = spanOf(note.span) orelse continue;
        const hit = diag_context.locate(note.source, span) orelse continue;
        try result.append(arena, .{
            .location = .{
                .uri = hit.uri,
                .range = lsp.offsets.locToRange(
                    hit.text,
                    .{ .start = hit.span.start, .end = hit.span.end },
                    encoding,
                ),
            },
            .message = try noteMessageText(arena, note.message),
        });
    }
    for (diag.relatedSlice()) |related| {
        const hit = diag_context.locate(
            related.source,
            .{ .start = related.span.start, .end = related.span.end },
        ) orelse continue;
        try result.append(arena, .{
            .location = .{
                .uri = hit.uri,
                .range = lsp.offsets.locToRange(
                    hit.text,
                    .{ .start = hit.span.start, .end = hit.span.end },
                    encoding,
                ),
            },
            .message = try relatedLabelText(arena, related.label),
        });
    }
    if (result.items.len == 0) return null;
    return result.items;
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
