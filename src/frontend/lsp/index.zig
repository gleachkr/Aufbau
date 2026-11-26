const std = @import("std");
const ArenaAllocator = @import("../arena_allocator.zig").ArenaAllocator;

const completion = @import("completion.zig");
const Builder = @import("builder.zig").Builder;
const Compactor = @import("compact.zig").Compactor;
pub const holes = @import("holes.zig");
const indexBody = @import("builder_body.zig").indexBody;
const model = @import("model.zig");
const notation = @import("notation.zig");
const references = @import("references.zig");
const rename = @import("rename.zig");
const source = @import("source.zig");
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
const ProofBody = model.ProofBody;
const NameTable = model.NameTable;
const NotationCompletionDecl = notation.NotationCompletionDecl;
const ProofBlock = @import("../proof_script.zig").ProofBlock;
const KnownBodies = @import("../proof_script.zig").KnownBodies;
const Span = @import("../proof_script.zig").Span;
const proofSpanRange = @import("builder_support.zig").proofSpanRange;

/// The index of one unit: its `.mm0` text and proof headers, plus the proof
/// body last asked about. A proof's bodies are nearly all of its text, and
/// most requests look into one.
pub const Snapshot = struct {
    arena: ArenaAllocator,
    /// Backs `body`.
    body_arena: ArenaAllocator,
    body: ?struct { block_index: usize, body: ProofBody } = null,
    mm0_uri: []const u8,
    mm0_text: []const u8,
    proof_uri: ?[]const u8,
    proof_text: ?[]const u8,
    declarations: []const Declaration,
    decl_by_name: NameTable,
    notation_by_token: NameTable,
    proof_rule_by_name: NameTable,
    sort_var_by_token: std.StringHashMapUnmanaged(usize),
    /// The symbols outside proof bodies.
    symbols: []const NavigationSymbol,
    mm0_outline: []const OutlineSymbol,
    proof_outline: []const OutlineSymbol,
    proof_blocks: []const ProofBlockInfo,
    proof_rules: []const ProofRuleDecl,
    notations: []const NotationCompletionDecl,
    hole_tokens: []const []const u8,
    unknown_prefixes: []const []const u8,
    /// Whether every statement, proof item and line parsed.
    complete: bool,
    left_delims: [256]bool,
    right_delims: [256]bool,

    pub fn build(
        allocator: std.mem.Allocator,
        input: SnapshotInput,
    ) !Snapshot {
        // Building leaves its parses and the lists' old buffers behind; only
        // what the snapshot keeps is copied out of it.
        var build_arena = ArenaAllocator.init(allocator);
        defer build_arena.deinit();
        var builder = Builder.init(build_arena.allocator());
        try builder.indexMm0(input.mm0_text);
        if (input.proof_text) |text| {
            try builder.indexProof(
                text,
                if (input.check_memo) |memo| memo.knownBodies() else null,
            );
            // A body's lines are parsed again when a request needs them.
            for (builder.proof_blocks.items) |*info| info.source = info.source.withoutLines(text);
        }

        var arena_state = ArenaAllocator.init(allocator);
        errdefer arena_state.deinit();
        const texts = [_][]const u8{ input.mm0_text, input.proof_text orelse "" };
        var keep: Compactor = .{
            .arena = arena_state.allocator(),
            .allocator = allocator,
            .texts = &texts,
        };
        defer keep.deinit();
        // Copy the arena last: the copies below add buffers to it.
        var snapshot: Snapshot = .{
            .arena = undefined,
            .body_arena = ArenaAllocator.init(allocator),
            .mm0_uri = try keep.copy([]const u8, input.mm0_uri),
            .mm0_text = input.mm0_text,
            .proof_uri = try keep.copy(?[]const u8, input.proof_uri),
            .proof_text = input.proof_text,
            .declarations = try keep.copy([]const Declaration, builder.declarations.items),
            .decl_by_name = try keep.nameTable(builder.decl_by_name),
            .notation_by_token = try keep.nameTable(builder.notation_by_token),
            .proof_rule_by_name = try keep.nameTable(builder.proof_rule_by_name),
            .sort_var_by_token = try keep.stringMap(usize, builder.sort_var_by_token),
            .symbols = try keep.copy([]const NavigationSymbol, builder.symbols.items),
            .mm0_outline = try keep.copy([]const OutlineSymbol, builder.mm0_outline.items),
            .proof_outline = try keep.copy([]const OutlineSymbol, builder.proof_outline.items),
            .proof_blocks = try keep.copy([]const ProofBlockInfo, builder.proof_blocks.items),
            .proof_rules = try keep.copy([]const ProofRuleDecl, builder.proof_rules.items),
            .notations = try keep.copy([]const NotationCompletionDecl, builder.notations.items),
            .hole_tokens = try keep.copy([]const []const u8, builder.hole_tokens.items),
            .unknown_prefixes = try keep.copy([]const []const u8, builder.unknown_prefixes.items),
            .complete = builder.complete,
            .left_delims = builder.left_delims,
            .right_delims = builder.right_delims,
        };
        snapshot.arena = arena_state;
        return snapshot;
    }

    pub fn deinit(self: *Snapshot) void {
        self.body_arena.deinit();
        self.arena.deinit();
        self.* = undefined;
    }

    pub fn hoverAt(
        self: *Snapshot,
        document: DocumentId,
        offset: usize,
    ) !?HoverResult {
        const hit = try self.lookupAt(document, offset) orelse return null;
        return .{
            .range = hit.source_range,
            .markdown = hit.markdown,
        };
    }

    pub fn mathTokens(self: *const Snapshot, math: []const u8) source.MathTokenCursor {
        return .{
            .src = math,
            .left_delims = self.left_delims,
            .right_delims = self.right_delims,
        };
    }

    /// Whether a math token is a hole or a named unknown.
    fn isHole(self: *const Snapshot, token: []const u8) bool {
        for (self.hole_tokens) |hole| {
            if (std.mem.eql(u8, token, hole)) return true;
        }
        var named = false;
        for (self.unknown_prefixes) |prefix| {
            if (std.mem.eql(u8, token, prefix)) return false;
            if (std.mem.startsWith(u8, token, prefix)) named = true;
        }
        return named;
    }

    /// Whether the token at `offset` of the proof text is a hole or a named
    /// unknown, if it is math.
    pub fn isHoleAt(self: *const Snapshot, offset: usize) bool {
        const text = self.proof_text.?;
        var start = @min(offset, text.len);
        while (start > 0 and !endsMath(text[start - 1])) start -= 1;
        var end = start;
        while (end < text.len and !endsMath(text[end])) end += 1;
        var tokens = self.mathTokens(text[start..end]);
        while (tokens.next()) |token| {
            if (offset < start + token.end) return self.isHole(token.text);
        }
        return false;
    }

    fn endsMath(char: u8) bool {
        return char == '$' or source.isMathWhitespace(char);
    }

    /// Whether the line of `block` that takes `offset` has holes in its
    /// assertion.
    pub fn holeyLineAt(self: *const Snapshot, block: ProofBlock, offset: usize) bool {
        for (block.lines) |line| {
            if (!holes.lineTakes(line.span, offset, self.proof_text.?)) continue;
            var tokens = self.mathTokens(line.assertion.text);
            while (tokens.next()) |token| {
                if (self.isHole(token.text)) return true;
            }
        }
        return false;
    }

    pub fn definitionAt(
        self: *Snapshot,
        document: DocumentId,
        offset: usize,
    ) !?DefinitionResult {
        const hit = try self.lookupAt(document, offset) orelse return null;
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
        self: *Snapshot,
        allocator: std.mem.Allocator,
        document: DocumentId,
        offset: usize,
        include_declaration: bool,
    ) ![]const SourceRange {
        const hit = try self.lookupAt(document, offset) orelse return &.{};
        const declaration = hit.target_range orelse return &.{};
        const ranges = try self.referencesTo(allocator, declaration, null);
        if (include_declaration) return ranges;

        defer allocator.free(ranges);
        var uses = std.ArrayListUnmanaged(SourceRange).empty;
        for (ranges) |range| {
            if (!range.eql(declaration)) try uses.append(allocator, range);
        }
        return try uses.toOwnedSlice(allocator);
    }

    /// Where `declaration` is referred to, itself included: in all of the
    /// unit, or in one of the ranges `within`.
    pub fn referencesTo(
        self: *Snapshot,
        allocator: std.mem.Allocator,
        declaration: SourceRange,
        within: ?[]const SourceRange,
    ) ![]const SourceRange {
        const found = try references.occurrences(self, allocator, declaration, within);
        defer allocator.free(found);
        var ranges = std.ArrayListUnmanaged(SourceRange).empty;
        errdefer ranges.deinit(allocator);
        for (found) |occurrence| try ranges.append(allocator, occurrence.range);
        references.sortedUnique(&ranges);
        return try ranges.toOwnedSlice(allocator);
    }

    pub fn renameTargetAt(
        self: *Snapshot,
        document: DocumentId,
        offset: usize,
    ) !?RenameTarget {
        return rename.renameTargetAt(self, document, offset);
    }

    pub fn renameEdits(
        self: *Snapshot,
        allocator: std.mem.Allocator,
        target: RenameTarget,
        new_name: []const u8,
    ) (RenameError || std.mem.Allocator.Error)![]const SourceRange {
        return rename.renameEdits(self, allocator, target, new_name);
    }

    pub fn highlightsAt(
        self: *Snapshot,
        allocator: std.mem.Allocator,
        document: DocumentId,
        offset: usize,
        within: []const SourceRange,
    ) ![]const Highlight {
        return rename.highlightsAt(self, allocator, document, offset, within);
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
        self: *Snapshot,
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
        self: *Snapshot,
        offset: usize,
    ) !bool {
        return completion.isProofRuleCompletionAt(self, offset);
    }

    /// The first symbol containing `offset`.
    pub fn lookupAt(
        self: *Snapshot,
        document: DocumentId,
        offset: usize,
    ) std.mem.Allocator.Error!?NavigationSymbol {
        const symbols = if (self.blockWithBodyAt(document, offset)) |block_index|
            (try self.bodyOf(block_index)).symbols
        else
            self.symbols;
        for (symbols) |symbol| {
            if (symbol.source_range.contains(document, offset)) return symbol;
        }
        return null;
    }

    /// The block whose body `offset` is in.
    pub fn blockWithBodyAt(
        self: *const Snapshot,
        document: DocumentId,
        offset: usize,
    ) ?usize {
        if (document != .proof) return null;
        const block_index = self.proofBlockNear(offset) orelse return null;
        if (!self.proof_blocks[block_index].bodyContains(offset)) return null;
        return block_index;
    }

    /// The last block that starts at or before `offset`.
    pub fn proofBlockNear(self: *const Snapshot, offset: usize) ?usize {
        const after = std.sort.upperBound(
            ProofBlockInfo,
            self.proof_blocks,
            offset,
            struct {
                fn order(at: usize, block: ProofBlockInfo) std.math.Order {
                    return std.math.order(at, block.source.span.start);
                }
            }.order,
        );
        return if (after == 0) null else after - 1;
    }

    /// What `proof_script.blockTouching` finds in the proof text. Unlike
    /// `blockWithBodyAt`, the body's end counts: a line takes the offset its
    /// newline ends at.
    pub fn blockTouching(
        self: *const Snapshot,
        allocator: std.mem.Allocator,
        offset: usize,
    ) std.mem.Allocator.Error!?ProofBlock {
        // A body that ends at `offset` can belong to the block before the
        // one that starts there.
        const near = self.proofBlockNear(offset) orelse return null;
        for (self.proof_blocks[near -| 1 .. near + 1]) |info| {
            if (!info.source.bodyTouches(offset)) continue;
            return try info.source.withLines(allocator, self.proof_text.?);
        }
        return null;
    }

    /// Where the bodies of this snapshot's proof blocks end, for a parser of
    /// its own proof text to pass over them (an analysis walk that needs no
    /// lines). A different text, even an equal one, gets no answers.
    pub fn knownBodies(self: *const Snapshot) KnownBodies {
        return .{ .ctx = @constCast(self), .findFn = findKnownBody };
    }

    fn findKnownBody(ctx: *anyopaque, src: []const u8, header: Span) ?KnownBodies.Body {
        const self: *const Snapshot = @ptrCast(@alignCast(ctx));
        const text = self.proof_text orelse return null;
        if (src.ptr != text.ptr or src.len != text.len) return null;
        const info = self.proof_blocks[self.proofBlockNear(header.start) orelse return null];
        const block = info.source;
        if (!block.self_contained) return null;
        if (block.header_span.start != header.start or block.header_span.end != header.end) return null;
        return .{
            .len = block.body_end - header.end,
            .hash = block.known_body orelse
                KnownBodies.bodyHash(text[header.end..block.body_end]),
        };
    }

    /// The index of a block's body, valid until another block's is asked
    /// for.
    pub fn bodyOf(
        self: *Snapshot,
        block_index: usize,
    ) std.mem.Allocator.Error!ProofBody {
        if (self.body) |cached| {
            if (cached.block_index == block_index) return cached.body;
        }
        self.body = null;
        _ = self.body_arena.reset(.free_all);
        const body = try indexBody(self.body_arena.allocator(), self, block_index);
        self.body = .{ .block_index = block_index, .body = body };
        return body;
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
            if (block.source.kind != .theorem) continue;
            if (block.decl_index != decl_index) continue;
            return proofSpanRange(block.source.name_span);
        }
        return null;
    }
};
