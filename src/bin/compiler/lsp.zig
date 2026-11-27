const builtin = @import("builtin");
const build_options = @import("build_options");
const std = @import("std");
const lsp = @import("lsp");
const mm0 = @import("mm0");
const Input = @import("./lsp_input.zig").Input;
const lsp_texts = @import("./lsp_texts.zig");
const FileTexts = lsp_texts.FileTexts;
const client = @import("./lsp/client.zig");
const uri_names = @import("./lsp/uris.zig");
const unit_mod = @import("./lsp/unit.zig");
const unit_state = @import("./lsp/unit_state.zig");
const analysis = @import("./lsp/analysis.zig");
const publish = @import("./lsp/publish.zig");
const PendingAnalysis = analysis.PendingAnalysis;
const Report = publish.Report;

pub const DocumentKind = uri_names.DocumentKind;
pub const uriToPath = uri_names.uriToPath;
pub const pathToUri = uri_names.pathToUri;
pub const siblingPathForProof = uri_names.siblingPathForProof;
pub const siblingPathForMm0 = uri_names.siblingPathForMm0;
pub const documentKind = uri_names.documentKind;
const UnitRoots = uri_names.UnitRoots;
const OpenDocument = unit_mod.OpenDocument;
const Unit = unit_mod.Unit;
const UnitSide = unit_mod.UnitSide;
const UnitState = unit_state.UnitState;
const NavigationSnapshot = unit_state.NavigationSnapshot;
const PlaceholderOutcome = unit_state.PlaceholderOutcome;
const outcomeForPlaceholder = unit_state.outcomeForPlaceholder;
const ArenaAllocator = mm0.ArenaAllocator;

const types = lsp.types.flat;
const LspIndex = mm0.Frontend.LspIndex;
const HoleInferenceSink = mm0.CompilerSupport.Context.HoleInferenceSink;
const Search = mm0.CompilerSupport.Search;
const Unpack = mm0.CompilerSupport.Unpack;
const Imports = mm0.Imports;
const ProofBlock = mm0.ProofScript.ProofBlock;
const lsp_diagnostics = @import("lsp_diagnostics");
const DiagnosticContext = lsp_diagnostics.DiagnosticContext;
const LocatedDiagnostic = lsp_diagnostics.LocatedDiagnostic;
const LSP_SERVER_NAME = lsp_diagnostics.SERVER_NAME;
/// The command an open-goal action runs after its edit: select the first
/// open goal `?` it added (arguments: the document uri and the range).
const show_open_goal_command = "aufbau.showOpenGoal";
const zeroRange = lsp_diagnostics.zeroRange;
const highlightsToLsp = lsp_diagnostics.highlightsToLsp;
const sourceRangesToLocations = lsp_diagnostics.sourceRangesToLocations;
const completionsToLsp = lsp_diagnostics.completionsToLsp;
const outlineSymbolsToLsp = lsp_diagnostics.outlineSymbolsToLsp;
const CodeActionResult = lsp.ResultType("textDocument/codeAction");

const CodeActionItems = @typeInfo(CodeActionResult).optional.child;
const CodeActionItem = @typeInfo(CodeActionItems).pointer.child;

/// Filter static rule completions through the conclusion probe an open
/// goal's actions use. Search locates the ordinary application at `offset` and
/// probes every rule against its goal, preserving prior-line checking, local-lemma
/// availability, and inline expected-goal inference.
fn applicableRuleCompletions(
    arena: std.mem.Allocator,
    work_allocator: std.mem.Allocator,
    snapshot: *const LspIndex.Snapshot,
    proof_src: []const u8,
    offset: usize,
    completions: []const LspIndex.CompletionItem,
) ![]const LspIndex.CompletionItem {
    if (completions.len == 0) return completions;
    // Every tactic is exempt from the filter below, so a list holding nothing
    // else cannot lose an entry — and the search that would decide it costs
    // tens of milliseconds on a large proof, once per keystroke. This is the
    // list you get while typing a placeholder, which is exactly when the
    // reader is typing fastest.
    if (allSearchTactics(completions)) return completions;
    const block = try snapshot.blockTouching(arena, offset) orelse return completions;

    var suggestions = Search.suggestionsAtSourceOffset(
        arena,
        snapshot.mm0_text,
        proof_src,
        offset,
        .{
            .max_results = completions.len,
            .apply_at_offset = true,
            .work_allocator = work_allocator,
            .block = block,
            .known_bodies = snapshot.knownBodies(),
        },
    ) catch |err| switch (err) {
        error.OutOfMemory => return err,
        // Completion must remain useful while surrounding source is
        // malformed. A recognized search target with no candidates is handled
        // below and correctly returns an empty list; only setup/parse failure
        // falls back.
        else => return completions,
    };
    defer suggestions.deinit();
    if (suggestions.target_span == null) return completions;

    var filtered = std.ArrayListUnmanaged(LspIndex.CompletionItem).empty;
    for (completions) |item| {
        // The tactics are what you write *instead of* naming a rule, so the
        // search has no opinion on them and the filter must not eat them.
        if (!isSearchTactic(item) and
            !searchOffersRule(suggestions.items, item.label))
        {
            continue;
        }
        try filtered.append(arena, item);
    }
    return try filtered.toOwnedSlice(arena);
}

/// A completion this filter has no business judging. In a proof-rule
/// position the keyword kind belongs to the search tactics alone — every
/// name the theory supplies arrives as a rule, a label, or a hypothesis.
fn isSearchTactic(item: LspIndex.CompletionItem) bool {
    return item.kind == .keyword;
}

fn allSearchTactics(items: []const LspIndex.CompletionItem) bool {
    for (items) |item| {
        if (!isSearchTactic(item)) return false;
    }
    return true;
}

fn searchOffersRule(
    suggestions: []const Search.SourceSuggestion,
    rule_name: []const u8,
) bool {
    // Each suggestion is a rule's bare name.
    for (suggestions) |suggestion| {
        if (std.mem.eql(u8, suggestion.replacement, rule_name)) return true;
    }
    return false;
}

/// What reads the handler's messages, which settles when its analyses run.
pub const Host = union(enum) {
    /// Each message is handled to its end before the next is read (the
    /// browser worker, `lsp_wasm.zig`). A change is analysed at once and
    /// whole: nothing can come between two passes, no request waits to be
    /// answered meanwhile, and what the handler writes is not seen until
    /// the message is handled, so a check shows no progress.
    serial,
    /// Input is read ahead into a queue (the native server,
    /// `lsp_input.zig`). A change leaves its root pending, and the host
    /// calls `Handler.analyzePending` when nothing is queued. An analysis
    /// checks the proofs of the open files first and publishes on them,
    /// shows its progress, and stops when the queue says so; a request
    /// asks the same to learn that the client cancelled it.
    queued: mm0.AnalysisInterrupt,

    pub fn interrupt(self: Host) ?mm0.AnalysisInterrupt {
        return switch (self) {
            .serial => null,
            .queued => |stop| stop,
        };
    }
};

pub const Handler = struct {
    allocator: std.mem.Allocator,
    io: std.Io,
    transport: *lsp.Transport,
    host: Host,
    docs: std.StringHashMapUnmanaged(OpenDocument),
    /// The file texts units are built from, one copy of each across them.
    texts: FileTexts,
    /// The unit joined for each root, keyed by the root's `.mm0` URI
    /// (`UnitState.mm0_uri`), with what was found in it.
    units: std.StringHashMapUnmanaged(*UnitState),
    /// What the last analysis of each open document read and published,
    /// keyed by the analysed URI (owned).
    reports: std.StringHashMapUnmanaged(Report),
    /// Proof-block check outcomes shared by every analysis this handler
    /// runs, so an edit re-checks only what it can affect. It keeps what
    /// each root's last analysis used.
    check_memo: mm0.CheckMemo,
    /// The documents whose diagnostics are out of date, by the URI whose
    /// analysis covers them, in the order they last changed (owned).
    pending: std.StringArrayHashMapUnmanaged(PendingAnalysis),
    offset_encoding: lsp.offsets.Encoding,
    snippet_support: bool,
    /// Whether the client opens a document at a selection on request
    /// (`window/showDocument`), which `show_open_goal_command` uses.
    show_document_support: bool,
    /// The id of the last request this server sent the client.
    last_request_id: i64,
    /// Whether the client shows progress the server starts
    /// (`window.workDoneProgress`).
    progress_support: bool,
    /// The last progress token this server made.
    last_progress_token: i32,
    /// How long a check runs before its progress shows.
    progress_delay_ns: i96,

    // When and how a document is checked (`lsp/analysis.zig`).
    pub const analyzeDependentsSoon = analysis.analyzeDependentsSoon;
    pub const analyzeSoon = analysis.analyzeSoon;
    pub const hasPendingAnalysis = analysis.hasPendingAnalysis;
    pub const analyzePending = analysis.analyzePending;
    pub const dropPending = analysis.dropPending;
    // What the client is told of each file (`lsp/publish.zig`).
    pub const ownsDiagnostics = publish.ownsDiagnostics;
    pub const publishUnitDiagnostics = publish.publishUnitDiagnostics;
    pub const recordUnitFiles = publish.recordUnitFiles;
    pub const forgetUnit = publish.forgetUnit;
    pub const isDependency = publish.isDependency;
    pub const dependentRoots = publish.dependentRoots;
    pub const publishMessageDiagnostic = publish.publishMessageDiagnostic;
    pub const clearDiagnostics = publish.clearDiagnostics;

    pub fn init(
        allocator: std.mem.Allocator,
        io: std.Io,
        transport: *lsp.Transport,
        host: Host,
    ) Handler {
        return .{
            .allocator = allocator,
            .io = io,
            .transport = transport,
            .host = host,
            .docs = .empty,
            .texts = FileTexts.init(allocator),
            .units = .empty,
            .reports = .empty,
            .check_memo = mm0.CheckMemo.init(allocator),
            .pending = .empty,
            .offset_encoding = .@"utf-16",
            .snippet_support = false,
            .show_document_support = false,
            .last_request_id = 0,
            .progress_support = false,
            .last_progress_token = 0,
            .progress_delay_ns = std.time.ns_per_s,
        };
    }

    /// Where this handler's units find their files.
    pub fn sources(self: *Handler) unit_mod.Sources {
        return .{ .docs = &self.docs, .texts = &self.texts, .io = self.io };
    }

    pub fn deinit(self: *Handler) void {
        var it = self.docs.iterator();
        while (it.next()) |entry| {
            self.allocator.free(entry.key_ptr.*);
            self.allocator.free(entry.value_ptr.text);
        }
        self.docs.deinit(self.allocator);

        var units_it = self.units.valueIterator();
        while (units_it.next()) |state| state.*.destroy();
        self.units.deinit(self.allocator);
        self.texts.deinit();

        var reports_it = self.reports.iterator();
        while (reports_it.next()) |entry| {
            self.allocator.free(entry.key_ptr.*);
            entry.value_ptr.deinit(self.allocator);
        }
        self.reports.deinit(self.allocator);
        for (self.pending.keys()) |uri| self.allocator.free(uri);
        self.pending.deinit(self.allocator);
        self.check_memo.deinit();
        self.* = undefined;
    }

    pub fn initialize(
        self: *Handler,
        _: std.mem.Allocator,
        request: types.InitializeParams,
    ) types.InitializeResult {
        if (request.capabilities.general) |general| {
            for (general.positionEncodings orelse &.{}) |encoding| {
                self.offset_encoding = switch (encoding) {
                    .@"utf-8" => .@"utf-8",
                    .@"utf-16" => .@"utf-16",
                    .@"utf-32" => .@"utf-32",
                    .custom_value => continue,
                };
                break;
            }
        }

        self.snippet_support = client.snippets(request.capabilities);
        self.show_document_support = client.showDocument(request.capabilities);
        self.progress_support = client.workDoneProgress(request.capabilities);

        const supports_hierarchical_document_symbols =
            client.hierarchicalDocumentSymbols(request.capabilities);
        const supports_prepare_rename =
            client.prepareRename(request.capabilities);

        const capabilities: types.ServerCapabilities = .{
            .positionEncoding = switch (self.offset_encoding) {
                .@"utf-8" => .@"utf-8",
                .@"utf-16" => .@"utf-16",
                .@"utf-32" => .@"utf-32",
            },
            .textDocumentSync = .{
                .text_document_sync_options = .{
                    .openClose = true,
                    .change = .Full,
                },
            },
            .hoverProvider = .{ .bool = true },
            .definitionProvider = .{ .bool = true },
            .implementationProvider = .{ .bool = true },
            .referencesProvider = .{ .bool = true },
            .documentHighlightProvider = .{ .bool = true },
            .renameProvider = if (supports_prepare_rename)
                .{ .rename_options = .{ .prepareProvider = true } }
            else
                .{ .bool = true },
            .completionProvider = .{
                .resolveProvider = false,
                // `?` is the one completion-worthy character that is not part
                // of an identifier: it turns a rule name into a search
                // placeholder. Clients only auto-open the popup on identifier
                // characters unless the server says otherwise, and several
                // also treat a declared trigger character as belonging to the
                // token — which is what keeps the list open while `auto?` is
                // being typed.
                .triggerCharacters = &.{"?"},
            },
            .codeActionProvider = .{ .bool = true },
            .executeCommandProvider = .{ .commands = &.{show_open_goal_command} },
            .documentSymbolProvider = if (supports_hierarchical_document_symbols)
                .{ .bool = true }
            else
                null,
        };

        if (builtin.mode == .debug) {
            // The validator only understands static capabilities. Validate
            // against the superset of implemented handlers while returning
            // the client-specific capabilities above.
            var validation_capabilities = capabilities;
            validation_capabilities.documentSymbolProvider = .{ .bool = true };
            validation_capabilities.codeActionProvider = .{ .bool = true };
            validation_capabilities.renameProvider = .{
                .rename_options = .{ .prepareProvider = true },
            };
            lsp.basic_server.validateServerCapabilities(
                Handler,
                validation_capabilities,
            );
        }

        return .{
            .serverInfo = .{
                .name = LSP_SERVER_NAME,
                .version = build_options.version,
            },
            .capabilities = capabilities,
        };
    }

    pub fn initialized(
        _: *Handler,
        _: std.mem.Allocator,
        _: types.InitializedParams,
    ) void {}

    pub fn shutdown(
        _: *Handler,
        _: std.mem.Allocator,
        _: void,
    ) ?void {
        return null;
    }

    pub fn exit(
        _: *Handler,
        _: std.mem.Allocator,
        _: void,
    ) void {}

    pub fn @"textDocument/didOpen"(
        self: *Handler,
        arena: std.mem.Allocator,
        params: types.DidOpenTextDocumentParams,
    ) !void {
        try self.putDocument(
            params.textDocument.uri,
            params.textDocument.text,
            params.textDocument.version,
        );
        self.dropUnitsOf(arena, params.textDocument.uri);
        try self.analyzeSoon(arena, params.textDocument.uri);
        try self.analyzeDependentsSoon(arena, params.textDocument.uri);
    }

    pub fn @"textDocument/didChange"(
        self: *Handler,
        arena: std.mem.Allocator,
        params: types.DidChangeTextDocumentParams,
    ) !void {
        const doc = self.docs.getPtr(params.textDocument.uri) orelse return;

        var buffer = std.ArrayListUnmanaged(u8).empty;
        try buffer.appendSlice(arena, doc.text);

        for (params.contentChanges) |change| {
            switch (change) {
                .text_document_content_change_partial => |partial| {
                    const loc = lsp_diagnostics.offsets.rangeToLoc(
                        buffer.items,
                        partial.range,
                        self.offset_encoding,
                    );
                    try buffer.replaceRange(
                        arena,
                        loc.start,
                        loc.end - loc.start,
                        partial.text,
                    );
                },
                .text_document_content_change_whole_document => |whole| {
                    buffer.clearRetainingCapacity();
                    try buffer.appendSlice(arena, whole.text);
                },
            }
        }

        const new_text = try self.allocator.dupe(u8, buffer.items);
        self.allocator.free(doc.text);
        doc.text = new_text;
        doc.version = params.textDocument.version;

        self.dropUnitsOf(arena, params.textDocument.uri);
        try self.analyzeSoon(arena, params.textDocument.uri);
        try self.analyzeDependentsSoon(arena, params.textDocument.uri);
    }

    pub fn @"textDocument/didClose"(
        self: *Handler,
        arena: std.mem.Allocator,
        params: types.DidCloseTextDocumentParams,
    ) !void {
        const uri = params.textDocument.uri;
        self.dropUnitsOf(arena, uri);
        try self.dropPending(uri);
        try self.removeDocument(uri);
        try self.clearDiagnostics(arena, uri, null);
        try self.forgetUnit(arena, uri);

        if (uriToPath(arena, uri)) |path| {
            switch (documentKind(path)) {
                .mm0 => if (siblingPathForMm0(arena, path)) |proof_path| {
                    const proof_uri = try pathToUri(arena, proof_path);
                    if (self.docs.contains(proof_uri)) {
                        try self.analyzeSoon(arena, proof_uri);
                    }
                } else |_| {},
                .proof => if (siblingPathForProof(arena, path)) |mm0_path| {
                    const mm0_uri = try pathToUri(arena, mm0_path);
                    if (self.docs.contains(mm0_uri)) {
                        try self.analyzeSoon(arena, mm0_uri);
                    } else {
                        try self.clearDiagnostics(arena, mm0_uri, null);
                    }
                } else |_| {},
                .other => {},
            }
        } else |_| {}

        // The file may still exist on disk, so roots that import or include
        // it re-analyse against that copy.
        try self.analyzeDependentsSoon(arena, uri);
    }

    pub fn @"textDocument/hover"(
        self: *Handler,
        arena: std.mem.Allocator,
        params: types.HoverParams,
    ) !lsp.ResultType("textDocument/hover") {
        const nav = try self.navigationSnapshotForUri(
            arena,
            params.textDocument.uri,
        ) orelse return null;
        const offset = nav.joinedPosition(
            params.position,
            self.offset_encoding,
        ) orelse return null;
        const hover = try holeHover(arena, nav, offset) orelse
            try nav.snapshot.hoverAt(nav.document, offset) orelse
            return null;
        return .{
            .contents = .{
                .markup_content = .{
                    .kind = .markdown,
                    .value = hover.markdown,
                },
            },
            .range = nav.unit.rangeLocator().toLsp(
                hover.range,
                self.offset_encoding,
            ),
        };
    }

    /// The value of the hole at `offset`.
    fn holeHover(
        arena: std.mem.Allocator,
        nav: NavigationSnapshot,
        offset: usize,
    ) !?LspIndex.HoverResult {
        if (nav.document != .proof) return null;
        const analysed: ?*const HoleInferenceSink =
            if (nav.state.holes) |*holes| holes else null;
        const found = analysed orelse checked: {
            if (!nav.snapshot.isHoleAt(offset)) return null;
            const block = try nav.snapshot.blockTouching(arena, offset) orelse return null;
            break :checked try blockHoles(arena, nav, block, false);
        };
        return try LspIndex.holes.hoverAt(arena, found, offset);
    }

    pub fn @"textDocument/completion"(
        self: *Handler,
        arena: std.mem.Allocator,
        params: types.CompletionParams,
    ) !lsp.ResultType("textDocument/completion") {
        const nav = try self.navigationSnapshotForUri(
            arena,
            params.textDocument.uri,
        ) orelse return null;
        const offset = nav.joinedPosition(
            params.position,
            self.offset_encoding,
        ) orelse return null;
        var completions = try nav.snapshot.completionsAt(
            arena,
            nav.document,
            offset,
            .{ .snippet_support = self.snippet_support },
        );
        if (nav.document == .proof and
            try nav.snapshot.isProofRuleCompletionAt(offset))
        {
            completions = try applicableRuleCompletions(
                arena,
                self.allocator,
                nav.snapshot,
                nav.side().joined.text,
                offset,
                completions,
            );
        }
        const items = try completionsToLsp(
            arena,
            nav.unit.rangeLocator(),
            completions,
            self.offset_encoding,
        );
        // Incomplete, always: what we return depends on the token under the
        // cursor, so the list cannot be narrowed by filtering a previous one.
        // A rule position runs the proof search and keeps only the rules that
        // can actually close the goal, which differs between `by a` and `by m`
        // for reasons no client-side filter could reconstruct; a token holding
        // a `?` drops the rules entirely. Saying `isIncomplete` asks the
        // client to re-query per keystroke instead of reusing a stale list.
        return .{ .completion_list = .{
            .isIncomplete = true,
            .items = items,
        } };
    }

    pub fn @"textDocument/codeAction"(
        self: *Handler,
        arena: std.mem.Allocator,
        params: types.CodeActionParams,
    ) !lsp.ResultType("textDocument/codeAction") {
        const nav = try self.navigationSnapshotForUri(
            arena,
            params.textDocument.uri,
        ) orelse return null;
        if (nav.document != .proof) return null;
        const offset = nav.joinedPosition(
            params.range.start,
            self.offset_encoding,
        ) orelse return null;

        const block = try nav.snapshot.blockTouching(arena, offset) orelse return null;
        var actions = std.ArrayListUnmanaged(CodeActionItem).empty;
        if (try self.suggestionsForUnit(arena, nav, block, offset)) |suggestions| {
            for (suggestions) |suggestion| {
                const action = try self.searchCodeAction(
                    arena,
                    nav,
                    suggestion,
                ) orelse continue;
                try actions.append(arena, .{ .code_action = action });
            }
        }
        if (try self.unpackCodeAction(arena, nav, block, offset)) |action| {
            try actions.append(arena, .{ .code_action = action });
        }
        if (try self.fillHolesCodeAction(arena, nav, block, offset)) |action| {
            try actions.append(arena, .{ .code_action = action });
        }
        if (actions.items.len == 0) return null;
        return try actions.toOwnedSlice(arena);
    }

    /// Offer the `unpack` rewrite when the cursor sits on a checked proof
    /// line containing inline rule applications. The common case, no inline
    /// application under the cursor, costs no analysis.
    fn unpackCodeAction(
        self: *Handler,
        arena: std.mem.Allocator,
        nav: NavigationSnapshot,
        block: ProofBlock,
        offset: usize,
    ) !?types.CodeAction {
        const proof_side = nav.side();
        const suggestion = try Unpack.unpackAtSourceOffset(
            arena,
            nav.unit.mm0.joined.text,
            proof_side.joined.text,
            block,
            offset,
            nav.snapshot.knownBodies(),
        ) orelse return null;

        return try self.replacementCodeAction(
            arena,
            proof_side.*,
            suggestion.title,
            .@"refactor.rewrite",
            suggestion.replace_span,
            suggestion.replacement,
            null,
        );
    }

    /// Offer to write a checked holey line's conclusion over its assertion,
    /// filling in every hole on the line. The analysis does not fill lines
    /// in (`HoleInferenceSink.fills`), so the proof is checked here.
    fn fillHolesCodeAction(
        self: *Handler,
        arena: std.mem.Allocator,
        nav: NavigationSnapshot,
        block: ProofBlock,
        offset: usize,
    ) !?types.CodeAction {
        if (!nav.snapshot.holeyLineAt(block, offset)) return null;
        const found = try blockHoles(arena, nav, block, true);
        const fill = try LspIndex.holes.fillAt(
            arena,
            found,
            nav.side().joined.text,
            offset,
        ) orelse return null;
        return try self.replacementCodeAction(
            arena,
            nav.side().*,
            "Fill in the holes",
            .@"refactor.rewrite",
            fill.assertion,
            fill.replacement,
            null,
        );
    }

    /// A code action replacing `span` of the joined proof text with
    /// `replacement`, addressed to the file the span lies in. With a
    /// `cursor` (an offset in `replacement`), the action then runs
    /// `show_open_goal_command` to select that character.
    fn replacementCodeAction(
        self: *Handler,
        arena: std.mem.Allocator,
        proof_side: UnitSide,
        title: []const u8,
        kind: types.CodeActionKind,
        span: Search.Span,
        replacement: []const u8,
        cursor: ?usize,
    ) !?types.CodeAction {
        const hit = proof_side.locate(span) orelse return null;
        const edits = try arena.alloc(types.TextEdit, 1);
        edits[0] = .{
            .range = lsp_diagnostics.offsets.locToRange(
                hit.file.text,
                .{ .start = hit.span.start, .end = hit.span.end },
                self.offset_encoding,
            ),
            .newText = replacement,
        };
        var changes: std.json.ArrayHashMap([]const types.TextEdit) = .{};
        try changes.map.put(arena, hit.file.uri, edits);
        return .{
            .title = title,
            .kind = kind,
            .edit = .{ .changes = changes },
            .command = if (cursor != null) blk: {
                const at = positionAfterEdit(
                    hit.file.text,
                    hit.span.start,
                    replacement[0..cursor.?],
                    self.offset_encoding,
                );
                // The character there is a `?`: one code unit in every encoding.
                const selection: types.Range = .{
                    .start = at,
                    .end = .{ .line = at.line, .character = at.character + 1 },
                };
                const arguments = try arena.alloc(std.json.Value, 2);
                arguments[0] = .{ .string = hit.file.uri };
                arguments[1] = try rangeValue(arena, selection);
                break :blk .{
                    .title = "Go to the new open goal",
                    .command = show_open_goal_command,
                    .arguments = arguments,
                };
            } else null,
        };
    }

    /// `show_open_goal_command` [uri, range]: ask the client to show the
    /// document at uri with range selected, when it can
    /// (`window/showDocument`); a client that cannot may run the command
    /// itself. Any other command does nothing.
    pub fn @"workspace/executeCommand"(
        self: *Handler,
        arena: std.mem.Allocator,
        params: types.ExecuteCommandParams,
    ) !lsp.ResultType("workspace/executeCommand") {
        if (!std.mem.eql(u8, params.command, show_open_goal_command)) return null;
        if (!self.show_document_support) return null;
        const arguments = params.arguments orelse return null;
        if (arguments.len != 2 or arguments[0] != .string) return null;
        const selection = std.json.parseFromValueLeaky(
            types.Range,
            arena,
            arguments[1],
            .{ .ignore_unknown_fields = true },
        ) catch return null;
        self.last_request_id += 1;
        try self.transport.writeRequest(
            self.io,
            arena,
            .{ .number = self.last_request_id },
            "window/showDocument",
            types.ShowDocumentParams,
            .{ .uri = arguments[0].string, .takeFocus = true, .selection = selection },
            .{ .emit_null_optional_fields = false },
        );
        return null;
    }

    /// Return the search suggestions for the unit at `offset` (in the joined
    /// proof text), or the actions on the open goal there, plus the retry
    /// edit after a miss that larger limits might fix, serving the
    /// unit's last search when the offset falls within its placeholder
    /// span, and searching otherwise. The returned slice is the unit's and
    /// stays valid until its next search or until it goes, neither of
    /// which happens within one request. Returns null only when the search
    /// itself fails (a kept empty result is a non-null empty slice).
    ///
    /// A search that ran also records its outcome in the unit and
    /// re-publishes the proof document's diagnostics, upgrading the target
    /// placeholder's "not yet searched" warning; a kept result, or an open
    /// goal, which runs no search, changes nothing, so it publishes nothing.
    fn suggestionsForUnit(
        self: *Handler,
        arena: std.mem.Allocator,
        nav: NavigationSnapshot,
        block: ProofBlock,
        offset: usize,
    ) !?[]const Search.SourceSuggestion {
        const proof_side = nav.side();
        const proof_uri = proof_side.rootFile().uri;
        if (nav.state.search) |kept| {
            if (kept.matchesOffset(offset)) return kept.suggestions;
        }

        const suggestions = Search.suggestionsAtSourceOffset(
            arena,
            nav.unit.mm0.joined.text,
            proof_side.joined.text,
            offset,
            // One best proof for `exact?`/`auto?`; this also lets `exact?`
            // short-circuit recursive generation once it has a proof. Grant
            // the generation permit; the keyword under the cursor decides
            // whether recursive generation actually runs. `status_detail`
            // asks for the human-readable failure elaboration the
            // placeholder diagnostics surface.
            .{
                .exact_result_limit = 1,
                .generate = .{ .enabled = true },
                .status_detail = true,
                .work_allocator = self.allocator,
                .block = block,
                .known_bodies = nav.snapshot.knownBodies(),
            },
        ) catch |err| switch (err) {
            error.OutOfMemory => return err,
            else => return null,
        };

        // No placeholder at this offset → nothing worth keeping (the search
        // already short-circuited cheaply); just hand back the empty result.
        const target_span = suggestions.target_span orelse return suggestions.items;

        // A miss that larger limits might fix also offers the retry: the
        // placeholder rewritten with those limits, searched on the next
        // request.
        const actions = if (suggestions.retry) |retry|
            try std.mem.concat(arena, Search.SourceSuggestion, &.{
                suggestions.items,
                &.{retry},
            })
        else
            suggestions.items;
        const stored = try nav.state.keepSearch(target_span, actions);

        // An open goal's actions come from no search, so there is no outcome
        // to show.
        if (suggestions.target_kind == .open_goal) return stored;

        // A fresh search just concluded: record its outcome and re-publish the
        // proof document's diagnostics so this placeholder's "not yet searched"
        // warning upgrades to info (success) or error (failure) immediately.
        // Kept results skip this — their outcome is already recorded.
        try nav.state.recordOutcome(
            target_span,
            suggestions.status,
            if (suggestions.items.len > 0)
                suggestions.items[0].replacement
            else
                suggestions.status_detail orelse "",
        );
        try self.analyzeSoon(arena, proof_uri);
        return stored;
    }

    fn searchCodeAction(
        self: *Handler,
        arena: std.mem.Allocator,
        nav: NavigationSnapshot,
        suggestion: Search.SourceSuggestion,
    ) !?types.CodeAction {
        return try self.replacementCodeAction(
            arena,
            nav.side().*,
            suggestion.title,
            .quickfix,
            suggestion.replace_span,
            suggestion.replacement,
            suggestion.cursor,
        );
    }

    pub fn @"textDocument/documentSymbol"(
        self: *Handler,
        arena: std.mem.Allocator,
        params: types.DocumentSymbolParams,
    ) !lsp.ResultType("textDocument/documentSymbol") {
        const nav = try self.navigationSnapshotForUri(
            arena,
            params.textDocument.uri,
        ) orelse return null;
        const symbols = try outlineSymbolsToLsp(
            arena,
            nav.unit.rangeLocator(),
            params.textDocument.uri,
            nav.snapshot.outline(nav.document),
            self.offset_encoding,
        );
        return .{ .document_symbols = symbols };
    }

    pub fn @"textDocument/definition"(
        self: *Handler,
        arena: std.mem.Allocator,
        params: types.DefinitionParams,
    ) !lsp.ResultType("textDocument/definition") {
        const nav = try self.navigationSnapshotForUri(
            arena,
            params.textDocument.uri,
        ) orelse return null;
        const offset = nav.joinedPosition(
            params.position,
            self.offset_encoding,
        ) orelse return null;
        const definition = try nav.snapshot.definitionAt(
            nav.document,
            offset,
        ) orelse return null;
        const location = nav.unit.rangeLocator().toLocation(
            definition,
            self.offset_encoding,
        ) orelse return null;
        return .{ .definition = .{ .location = location } };
    }

    pub fn @"textDocument/implementation"(
        self: *Handler,
        arena: std.mem.Allocator,
        params: types.ImplementationParams,
    ) !lsp.ResultType("textDocument/implementation") {
        const nav = try self.navigationSnapshotForUri(
            arena,
            params.textDocument.uri,
        ) orelse return null;
        const offset = nav.joinedPosition(
            params.position,
            self.offset_encoding,
        ) orelse return null;
        const implementation = nav.snapshot.implementationAt(
            nav.document,
            offset,
        ) orelse return null;
        const location = nav.unit.rangeLocator().toLocation(
            implementation,
            self.offset_encoding,
        ) orelse return null;
        return .{ .definition = .{ .location = location } };
    }

    pub fn @"textDocument/references"(
        self: *Handler,
        arena: std.mem.Allocator,
        params: types.ReferenceParams,
    ) !lsp.ResultType("textDocument/references") {
        const nav = try self.navigationSnapshotForUri(
            arena,
            params.textDocument.uri,
        ) orelse return null;
        const offset = nav.joinedPosition(
            params.position,
            self.offset_encoding,
        ) orelse return null;
        const ranges = try nav.snapshot.referencesAt(
            arena,
            nav.document,
            offset,
            params.context.includeDeclaration,
        );
        return try sourceRangesToLocations(
            arena,
            nav.unit.rangeLocator(),
            ranges,
            self.offset_encoding,
        );
    }

    pub fn @"textDocument/documentHighlight"(
        self: *Handler,
        arena: std.mem.Allocator,
        params: types.DocumentHighlightParams,
    ) !lsp.ResultType("textDocument/documentHighlight") {
        const nav = try self.navigationSnapshotForUri(
            arena,
            params.textDocument.uri,
        ) orelse return null;
        const offset = nav.joinedPosition(
            params.position,
            self.offset_encoding,
        ) orelse return null;
        const highlights = try nav.snapshot.highlightsAt(
            arena,
            nav.document,
            offset,
            // Highlights belong to the requested file; the others are
            // references.
            try nav.fileRanges(arena),
        );
        return try highlightsToLsp(
            arena,
            nav.unit.rangeLocator(),
            highlights,
            self.offset_encoding,
        );
    }

    pub fn @"textDocument/prepareRename"(
        self: *Handler,
        arena: std.mem.Allocator,
        params: types.PrepareRenameParams,
    ) !lsp.ResultType("textDocument/prepareRename") {
        const nav = try self.navigationSnapshotForUri(
            arena,
            params.textDocument.uri,
        ) orelse return null;
        const offset = nav.joinedPosition(
            params.position,
            self.offset_encoding,
        ) orelse return null;
        const target = try nav.snapshot.renameTargetAt(
            nav.document,
            offset,
        ) orelse return null;
        if (!nav.snapshot.complete) {
            try self.showError(arena, syntax_error_message, .{});
            return null;
        }
        const range = nav.unit.rangeLocator().toLsp(
            target.range,
            self.offset_encoding,
        ) orelse return null;
        return .{ .prepare_rename_placeholder = .{ .range = range, .placeholder = target.name } };
    }

    /// A refused rename answers null and says why in a message: an error
    /// response would carry only an error name.
    pub fn @"textDocument/rename"(
        self: *Handler,
        arena: std.mem.Allocator,
        params: types.RenameParams,
    ) !lsp.ResultType("textDocument/rename") {
        const nav = try self.navigationSnapshotForUri(
            arena,
            params.textDocument.uri,
        ) orelse return null;
        const offset = nav.joinedPosition(
            params.position,
            self.offset_encoding,
        ) orelse return null;
        const target = try nav.snapshot.renameTargetAt(nav.document, offset) orelse {
            try self.showError(arena, "Nothing here can be renamed.", .{});
            return null;
        };
        const ranges = nav.snapshot.renameEdits(
            arena,
            target,
            params.newName,
        ) catch |err| switch (err) {
            error.OutOfMemory => return err,
            error.InvalidName => {
                try self.showError(arena, "`{s}` is not a valid name.", .{params.newName});
                return null;
            },
            error.NameInUse => {
                try self.showError(arena, "`{s}` is already in use.", .{params.newName});
                return null;
            },
            error.SyntaxError => {
                try self.showError(arena, syntax_error_message, .{});
                return null;
            },
            error.DuplicateName => {
                try self.showError(
                    arena,
                    "`{s}` is declared more than once; rename can't tell which one each use means.",
                    .{target.name},
                );
                return null;
            },
        };

        var by_uri: std.StringArrayHashMapUnmanaged(
            std.ArrayListUnmanaged(types.TextEdit),
        ) = .empty;
        const locations = try sourceRangesToLocations(
            arena,
            nav.unit.rangeLocator(),
            ranges,
            self.offset_encoding,
        );
        for (locations) |location| {
            const entry = try by_uri.getOrPut(arena, location.uri);
            if (!entry.found_existing) entry.value_ptr.* = .empty;
            try entry.value_ptr.append(arena, .{
                .range = location.range,
                .newText = params.newName,
            });
        }
        var changes: std.json.ArrayHashMap([]const types.TextEdit) = .{};
        for (by_uri.keys(), by_uri.values()) |uri, edits| {
            try changes.map.put(arena, uri, edits.items);
        }
        return .{ .changes = changes };
    }

    const syntax_error_message =
        "Rename needs every file of the theory to parse; fix the syntax errors first.";

    fn showError(
        self: *Handler,
        arena: std.mem.Allocator,
        comptime fmt: []const u8,
        args: anytype,
    ) !void {
        try self.transport.writeNotification(
            self.io,
            arena,
            "window/showMessage",
            types.ShowMessageParams,
            .{
                .type = .Error,
                .message = try std.fmt.allocPrint(arena, fmt, args),
            },
            .{ .emit_null_optional_fields = false },
        );
    }

    pub fn onResponse(
        _: *Handler,
        _: std.mem.Allocator,
        _: lsp.JsonRPCMessage.Response,
    ) void {}

    pub fn putDocument(
        self: *Handler,
        uri: []const u8,
        text: []const u8,
        version: i32,
    ) !void {
        const new_text = try self.allocator.dupe(u8, text);
        errdefer self.allocator.free(new_text);

        const gop = try self.docs.getOrPut(self.allocator, uri);
        if (gop.found_existing) {
            self.allocator.free(gop.value_ptr.text);
        } else {
            errdefer _ = self.docs.remove(uri);
            gop.key_ptr.* = try self.allocator.dupe(u8, uri);
        }

        gop.value_ptr.* = .{
            .text = new_text,
            .version = version,
        };
    }

    fn removeDocument(self: *Handler, uri: []const u8) !void {
        const entry = self.docs.fetchRemove(uri) orelse return;
        self.allocator.free(entry.key);
        self.allocator.free(entry.value.text);
    }

    /// The holes of `block`, a proof of `nav`'s unit, by a check of it alone,
    /// with `fills` its holey lines filled in.
    fn blockHoles(
        arena: std.mem.Allocator,
        nav: NavigationSnapshot,
        block: ProofBlock,
        fills: bool,
    ) !*const HoleInferenceSink {
        const found = try arena.create(HoleInferenceSink);
        found.* = try LspIndex.holes.ofBlock(
            arena,
            nav.unit.mm0.joined.text,
            nav.side().joined.text,
            block,
            fills,
            nav.snapshot.knownBodies(),
        );
        return found;
    }

    /// Whether the client cancelled the request being answered.
    pub fn requestCancelled(self: *Handler) bool {
        const interrupt = self.host.interrupt() orelse return false;
        return interrupt.stopRequested();
    }

    /// The check memo, set for a run over the unit rooted at `mm0_uri`.
    pub fn checkMemoFor(self: *Handler, mm0_uri: []const u8) *mm0.CheckMemo {
        self.check_memo.root = std.hash.Wyhash.hash(0, mm0_uri);
        return &self.check_memo;
    }

    fn navigationSnapshotForUri(
        self: *Handler,
        arena: std.mem.Allocator,
        uri: []const u8,
    ) !?NavigationSnapshot {
        if (try UnitRoots.of(arena, uri)) |roots| {
            if (try self.navigationSnapshotForRoot(uri, roots)) |nav| return nav;
        }
        // A library proof file without a theory of its own navigates
        // through a root that includes it.
        for (try self.dependentRoots(arena, uri)) |root| {
            if (std.mem.eql(u8, root, uri)) continue;
            const roots = try UnitRoots.of(arena, root) orelse continue;
            return try self.navigationSnapshotForRoot(uri, roots) orelse continue;
        }
        return null;
    }

    /// The unit kept for `roots`, if every file its join looked up is as the
    /// join found it.
    pub fn currentUnit(self: *const Handler, roots: UnitRoots) ?*UnitState {
        const state = self.units.get(roots.mm0_uri) orelse return null;
        if (!std.mem.eql(u8, state.proof_uri, roots.proof_uri)) return null;
        for (state.unit.lookups) |lookup| {
            if (!lookup.stands(self.io)) return null;
        }
        return state;
    }

    /// The unit at `roots`, joined anew when a file of the one kept
    /// changed. Fails when its `.mm0` cannot be loaded.
    pub fn unitFor(self: *Handler, roots: UnitRoots) !*UnitState {
        return self.currentUnit(roots) orelse try self.joinUnit(roots);
    }

    fn joinUnit(self: *Handler, roots: UnitRoots) !*UnitState {
        var arena = ArenaAllocator.init(self.allocator);
        errdefer arena.deinit();
        // Joined before the old unit goes, so that the texts it holds of
        // files that did not change are taken over rather than read again.
        const unit = try unit_mod.join(
            self.sources(),
            arena.allocator(),
            roots.mm0_uri,
            roots.mm0_path,
            roots.proof_uri,
            roots.proof_path,
        );
        errdefer unit.release(&self.texts);
        const mm0_uri = try arena.allocator().dupe(u8, roots.mm0_uri);
        const proof_uri = try arena.allocator().dupe(u8, roots.proof_uri);
        const state = try self.allocator.create(UnitState);
        errdefer self.allocator.destroy(state);
        try self.units.ensureUnusedCapacity(self.allocator, 1);
        self.dropUnit(roots.mm0_uri);
        state.* = .{
            .allocator = self.allocator,
            .arena = arena,
            .unit = unit,
            .texts = &self.texts,
            .mm0_uri = mm0_uri,
            .proof_uri = proof_uri,
        };
        self.units.putAssumeCapacity(mm0_uri, state);
        return state;
    }

    /// The index over `state`'s joined texts, built when first asked for.
    fn snapshotOf(self: *Handler, state: *UnitState) !*LspIndex.Snapshot {
        if (state.snapshot == null) {
            const unit = &state.unit;
            state.snapshot = try LspIndex.Snapshot.build(self.allocator, .{
                .mm0_text = unit.mm0.joined.text,
                .proof_text = if (unit.proof) |proof| proof.joined.text else null,
                .known_bodies = self.checkMemoFor(state.mm0_uri).knownBodies(),
            });
        }
        return &state.snapshot.?;
    }

    /// The index over the unit at `roots`, viewed from `request_uri`. Null
    /// when the unit's `.mm0` cannot be loaded or the unit has no such
    /// file.
    fn navigationSnapshotForRoot(
        self: *Handler,
        request_uri: []const u8,
        roots: UnitRoots,
    ) !?NavigationSnapshot {
        const state = self.unitFor(roots) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            else => return null,
        };
        const found = state.unit.find(request_uri) orelse return null;
        const snapshot = try self.snapshotOf(state);
        if (self.requestCancelled()) return error.RequestCancelled;
        return .{
            .state = state,
            .snapshot = snapshot,
            .unit = &state.unit,
            .document = found.document,
            .file_index = found.file_index,
        };
    }

    pub fn dropUnit(self: *Handler, mm0_uri: []const u8) void {
        const removed = self.units.fetchRemove(mm0_uri) orelse return;
        removed.value.destroy();
    }

    /// Drop every unit whose join looked up the document `uri`: what it
    /// holds is of texts that no longer stand. Called when a document is
    /// opened, changed or closed; a file that changes on disk is seen when
    /// its unit is next asked for (`currentUnit`).
    fn dropUnitsOf(self: *Handler, arena: std.mem.Allocator, uri: []const u8) void {
        // The join keys a file by its path, which several URIs may spell.
        const path: ?[]const u8 = uriToPath(arena, uri) catch null;
        // Removing invalidates the iterator, so the scan starts over; there
        // are a handful of units.
        scan: while (true) {
            var it = self.units.valueIterator();
            while (it.next()) |state| {
                if (!state.*.lookedUp(uri, path)) continue;
                self.dropUnit(state.*.mm0_uri);
                continue :scan;
            }
            return;
        }
    }
};

pub fn run(io: std.Io, allocator: std.mem.Allocator) !void {
    try serve(io, allocator, .stdin(), .stdout(), .{}, std.log.err);
}

pub const ServeOptions = struct {
    /// How long a check runs before its progress shows.
    progress_delay_ns: i96 = std.time.ns_per_s,
};

/// Serve the client at the other end of `read_from` and `write_to` until
/// it ends the session or the input does. `log` reports a message the
/// server could not handle; null drops it.
pub fn serve(
    io: std.Io,
    allocator: std.mem.Allocator,
    read_from: std.Io.File,
    write_to: std.Io.File,
    options: ServeOptions,
    comptime log: ?fn (comptime []const u8, anytype) void,
) !void {
    var read_buffer: [4096]u8 = undefined;
    var input = Input.init(allocator, io, &read_buffer, read_from, write_to);
    defer input.deinit();

    var handler = Handler.init(allocator, io, &input.transport, input.host());
    defer handler.deinit();
    handler.progress_delay_ns = options.progress_delay_ns;
    input.attach(&handler);

    try lsp.basic_server.run(io, allocator, &input.transport, &handler, log);
}

/// `range` as a JSON command argument.
fn rangeValue(arena: std.mem.Allocator, range: types.Range) !std.json.Value {
    return .{ .object = try .init(arena, &.{ "start", "end" }, &.{
        try positionValue(arena, range.start),
        try positionValue(arena, range.end),
    }) };
}

fn positionValue(arena: std.mem.Allocator, position: types.Position) !std.json.Value {
    return .{ .object = try .init(arena, &.{ "line", "character" }, &.{
        .{ .integer = position.line },
        .{ .integer = position.character },
    }) };
}

/// The position, once `inserted` replaces the text from byte `start` of
/// `text` on, of the end of `inserted`.
fn positionAfterEdit(
    text: []const u8,
    start: usize,
    inserted: []const u8,
    encoding: lsp.offsets.Encoding,
) types.Position {
    const at = lsp_diagnostics.offsets.indexToPosition(text, start, encoding, false);
    const within = lsp_diagnostics.offsets.indexToPosition(inserted, inserted.len, encoding, false);
    if (within.line == 0) return .{ .line = at.line, .character = at.character + within.character };
    return .{ .line = at.line + within.line, .character = within.character };
}
