const std = @import("std");
const ArenaAllocator = @import("../arena_allocator.zig").ArenaAllocator;

const completion = @import("completion.zig");
const CompilerModule = @import("../compiler.zig");
const Builder = @import("builder.zig").Builder;
const markdown = @import("markdown.zig");
const model = @import("model.zig");
const notation = @import("notation.zig");
const rename = @import("rename.zig");
const Types = @import("types.zig");

pub const DocumentId = Types.DocumentId;
pub const SnapshotInput = Types.SnapshotInput;
pub const SourceRange = Types.SourceRange;
pub const DefinitionResult = Types.DefinitionResult;
pub const HoverResult = Types.HoverResult;
pub const CompletionOptions = Types.CompletionOptions;
pub const CompletionKind = Types.CompletionKind;
pub const CompletionItem = Types.CompletionItem;
pub const OutlineSymbol = Types.OutlineSymbol;
pub const DeclarationKind = Types.DeclarationKind;
pub const BinderDecl = Types.BinderDecl;
pub const Declaration = Types.Declaration;
pub const escapeSnippetText = notation.escapeSnippetText;
pub const RenameTarget = rename.RenameTarget;
pub const RenameError = rename.RenameError;
pub const Highlight = rename.Highlight;

const NavigationSymbol = model.NavigationSymbol;
const ProofBlockInfo = model.ProofBlockInfo;
const ProofRuleDecl = model.ProofRuleDecl;
const ProofLineDecl = model.ProofLineDecl;
const ProofApplicationInfo = model.ProofApplicationInfo;
const NotationCompletionDecl = notation.NotationCompletionDecl;

const InferredHoleHover = struct {
    range: SourceRange,
    markdown: []const u8,
};

/// A holey proof line's assertion with its holes filled in.
pub const HoleFill = struct {
    /// The whole proof line.
    line: SourceRange,
    /// The assertion's math string, `$` delimiters included.
    assertion: SourceRange,
    /// The math string to put in its place, delimiters included.
    replacement: []const u8,
};

const HoleInfo = struct {
    hovers: []const InferredHoleHover = &.{},
    fills: []const HoleFill = &.{},
};

pub const Snapshot = struct {
    arena: ArenaAllocator,
    mm0_uri: []const u8,
    mm0_text: []const u8,
    proof_uri: ?[]const u8,
    proof_text: ?[]const u8,
    declarations: []const Declaration,
    decl_by_name: std.StringHashMapUnmanaged(usize),
    symbols: []const NavigationSymbol,
    inferred_hole_hovers: []const InferredHoleHover,
    hole_fills: []const HoleFill,
    mm0_outline: []const OutlineSymbol,
    proof_outline: []const OutlineSymbol,
    proof_blocks: []const ProofBlockInfo,
    proof_rules: []const ProofRuleDecl,
    proof_lines: []const ProofLineDecl,
    proof_applications: []const ProofApplicationInfo,
    notations: []const NotationCompletionDecl,
    hole_tokens: []const []const u8,
    /// Whether every statement, proof item and line parsed.
    complete: bool,
    left_delims: [256]bool,
    right_delims: [256]bool,

    pub fn build(
        allocator: std.mem.Allocator,
        input: SnapshotInput,
    ) !Snapshot {
        var arena_state = ArenaAllocator.init(allocator);
        errdefer arena_state.deinit();

        const arena = arena_state.allocator();
        var builder = Builder.init(arena);

        const mm0_uri = try arena.dupe(u8, input.mm0_uri);
        const mm0_text = try arena.dupe(u8, input.mm0_text);
        const proof_uri = if (input.proof_uri) |uri|
            try arena.dupe(u8, uri)
        else
            null;
        const proof_text = if (input.proof_text) |text|
            try arena.dupe(u8, text)
        else
            null;

        try builder.indexMm0(mm0_text);
        if (proof_text) |text| {
            try builder.indexProof(text);
        }
        const hole_info: HoleInfo = if (proof_text) |text|
            try buildHoleInfo(arena, mm0_text, text, input.check_memo)
        else
            .{};

        // Copy the arena last: the slices below can add buffers to it.
        var snapshot: Snapshot = .{
            .arena = undefined,
            .mm0_uri = mm0_uri,
            .mm0_text = mm0_text,
            .proof_uri = proof_uri,
            .proof_text = proof_text,
            .declarations = try builder.declarations.toOwnedSlice(arena),
            .decl_by_name = builder.decl_by_name,
            .symbols = try builder.symbols.toOwnedSlice(arena),
            .inferred_hole_hovers = hole_info.hovers,
            .hole_fills = hole_info.fills,
            .mm0_outline = try builder.mm0_outline.toOwnedSlice(arena),
            .proof_outline = try builder.proof_outline.toOwnedSlice(arena),
            .proof_blocks = try builder.proof_blocks.toOwnedSlice(arena),
            .proof_rules = try builder.proof_rules.toOwnedSlice(arena),
            .proof_lines = try builder.proof_lines.toOwnedSlice(arena),
            .proof_applications = try builder.proof_applications.toOwnedSlice(arena),
            .notations = try builder.notations.toOwnedSlice(arena),
            .hole_tokens = try builder.hole_tokens.toOwnedSlice(arena),
            .complete = builder.complete,
            .left_delims = builder.left_delims,
            .right_delims = builder.right_delims,
        };
        snapshot.arena = arena_state;
        return snapshot;
    }

    pub fn deinit(self: *Snapshot) void {
        self.arena.deinit();
        self.* = undefined;
    }

    pub fn hoverAt(
        self: *const Snapshot,
        document: DocumentId,
        offset: usize,
    ) ?HoverResult {
        if (document == .proof) {
            for (self.inferred_hole_hovers) |hover| {
                if (hover.range.contains(document, offset)) {
                    return .{
                        .range = hover.range,
                        .markdown = hover.markdown,
                    };
                }
            }
        }
        const hit = self.lookupAt(document, offset) orelse return null;
        return .{
            .range = hit.source_range,
            .markdown = hit.markdown,
        };
    }

    /// The fill for the holey proof line containing `offset`, if its
    /// filled assertion can be written in the proof. A line's range ends
    /// past its newline, so only a line ending the text also takes the
    /// offset just past its end.
    pub fn holeFillAt(self: *const Snapshot, offset: usize) ?HoleFill {
        const text_len = if (self.proof_text) |text| text.len else 0;
        for (self.hole_fills) |fill| {
            if (offset < fill.line.start) continue;
            if (offset < fill.line.end or
                (offset == fill.line.end and offset == text_len))
            {
                return fill;
            }
        }
        return null;
    }

    pub fn definitionAt(
        self: *const Snapshot,
        document: DocumentId,
        offset: usize,
    ) ?DefinitionResult {
        const hit = self.lookupAt(document, offset) orelse return null;
        const target_range = hit.target_range orelse return null;
        return self.locationForRange(target_range);
    }

    pub fn implementationAt(
        self: *const Snapshot,
        document: DocumentId,
        offset: usize,
    ) ?DefinitionResult {
        if (document != .mm0) return null;
        const decl_index = self.theoremDeclarationAt(offset) orelse return null;
        const target_range = self.proofBlockForTheorem(decl_index) orelse {
            return null;
        };
        return self.locationForRange(target_range);
    }

    pub fn referencesAt(
        self: *const Snapshot,
        allocator: std.mem.Allocator,
        document: DocumentId,
        offset: usize,
        include_declaration: bool,
    ) ![]const SourceRange {
        const hit = self.lookupAt(document, offset) orelse {
            return try allocator.alloc(SourceRange, 0);
        };
        const target_range = hit.target_range orelse {
            return try allocator.alloc(SourceRange, 0);
        };

        var list = std.ArrayListUnmanaged(SourceRange).empty;
        for (self.symbols) |symbol| {
            const symbol_target = symbol.target_range orelse continue;
            if (!symbol_target.eql(target_range)) continue;
            if (!include_declaration and symbol.source_range.eql(target_range)) continue;
            if (symbol.source_range.listedIn(list.items)) continue;
            try list.append(allocator, symbol.source_range);
        }
        return try list.toOwnedSlice(allocator);
    }

    pub fn renameTargetAt(
        self: *const Snapshot,
        document: DocumentId,
        offset: usize,
    ) ?RenameTarget {
        return rename.renameTargetAt(self, document, offset);
    }

    pub fn renameEdits(
        self: *const Snapshot,
        allocator: std.mem.Allocator,
        target: RenameTarget,
        new_name: []const u8,
    ) (RenameError || std.mem.Allocator.Error)![]const SourceRange {
        return rename.renameEdits(self, allocator, target, new_name);
    }

    pub fn highlightsAt(
        self: *const Snapshot,
        allocator: std.mem.Allocator,
        document: DocumentId,
        offset: usize,
    ) ![]const Highlight {
        return rename.highlightsAt(self, allocator, document, offset);
    }

    pub fn textForDocument(
        self: *const Snapshot,
        document: DocumentId,
    ) ?[]const u8 {
        return switch (document) {
            .mm0 => self.mm0_text,
            .proof => self.proof_text,
        };
    }

    pub fn outline(
        self: *const Snapshot,
        document: DocumentId,
    ) []const OutlineSymbol {
        return switch (document) {
            .mm0 => self.mm0_outline,
            .proof => self.proof_outline,
        };
    }

    pub fn completionsAt(
        self: *const Snapshot,
        allocator: std.mem.Allocator,
        document: DocumentId,
        offset: usize,
        options: CompletionOptions,
    ) ![]const CompletionItem {
        return completion.completionsAt(
            self,
            allocator,
            document,
            offset,
            options,
        );
    }

    pub fn isProofRuleCompletionAt(
        self: *const Snapshot,
        offset: usize,
    ) bool {
        return completion.isProofRuleCompletionAt(self, offset);
    }

    /// The first symbol containing `offset`.
    pub fn lookupAt(
        self: *const Snapshot,
        document: DocumentId,
        offset: usize,
    ) ?NavigationSymbol {
        for (self.symbols) |symbol| {
            if (symbol.source_range.contains(document, offset)) return symbol;
        }
        return null;
    }

    pub fn uriForDocument(
        self: *const Snapshot,
        document: DocumentId,
    ) ?[]const u8 {
        return switch (document) {
            .mm0 => self.mm0_uri,
            .proof => self.proof_uri,
        };
    }

    fn locationForRange(
        self: *const Snapshot,
        range: SourceRange,
    ) ?DefinitionResult {
        return .{
            .uri = self.uriForDocument(range.document) orelse return null,
            .range = range,
            .selection_range = range,
        };
    }

    fn theoremDeclarationAt(
        self: *const Snapshot,
        offset: usize,
    ) ?usize {
        for (self.declarations, 0..) |decl, i| {
            if (decl.kind != .theorem) continue;
            if (decl.name_range.contains(.mm0, offset)) return i;
        }
        return null;
    }

    fn proofBlockForTheorem(
        self: *const Snapshot,
        decl_index: usize,
    ) ?SourceRange {
        for (self.proof_blocks) |block| {
            if (block.kind != .theorem) continue;
            if (block.decl_index != decl_index) continue;
            return block.name_range;
        }
        return null;
    }
};

fn buildHoleInfo(
    allocator: std.mem.Allocator,
    mm0_text: []const u8,
    proof_text: []const u8,
    check_memo: ?*CompilerModule.CheckMemo,
) !HoleInfo {
    if (std.mem.indexOf(u8, mm0_text, "@hole") == null) return .{};

    var sink = CompilerModule.HoleInferenceSink{
        .allocator = allocator,
    };
    defer sink.deinit();

    var compiler = CompilerModule.Compiler.initWithProof(
        allocator,
        mm0_text,
        proof_text,
    );
    compiler.allow_search_placeholders = true;
    compiler.hole_inference_sink = &sink;
    compiler.check_memo = check_memo;
    compiler.analyze() catch |err| {
        if (err == error.OutOfMemory) return err;
    };

    var hovers = std.ArrayListUnmanaged(InferredHoleHover).empty;
    for (sink.items.items) |inference| {
        try hovers.append(allocator, .{
            .range = .{
                .document = .proof,
                .start = inference.span.start,
                .end = inference.span.end,
            },
            .markdown = try markdown.inferredHoleMarkdown(
                allocator,
                inference.expression,
            ),
        });
    }
    const fills = try allocator.alloc(HoleFill, sink.assertions.items.len);
    for (sink.assertions.items, fills) |filled, *fill| {
        fill.* = .{
            .line = .{
                .document = .proof,
                .start = filled.line.start,
                .end = filled.line.end,
            },
            .assertion = .{
                .document = .proof,
                .start = filled.assertion.start,
                .end = filled.assertion.end,
            },
            .replacement = try std.fmt.allocPrint(
                allocator,
                "$ {s} $",
                .{filled.text},
            ),
        };
    }
    return .{
        .hovers = try hovers.toOwnedSlice(allocator),
        .fills = fills,
    };
}
