const std = @import("std");
const lsp = @import("lsp");
const mm0 = @import("mm0");

const lsp_server = @import("../lsp.zig");
const lsp_diagnostics = @import("lsp_diagnostics");

const types = lsp.types;
const CodeActionResult = lsp.ResultType("textDocument/codeAction");
const CodeActionItems = @typeInfo(CodeActionResult).optional.child;
const CodeActionItem = @typeInfo(CodeActionItems).pointer.child;
const Handler = lsp_server.Handler;
const DocumentKind = lsp_server.DocumentKind;
const DiagnosticContext = lsp_diagnostics.DiagnosticContext;

const compilerDiagnosticsToLsp = lsp_diagnostics.compilerDiagnosticsToLsp;
const compilerSourceDiagnosticsToLsp =
    lsp_diagnostics.compilerSourceDiagnosticsToLsp;
const compilerDiagnosticToLsp = lsp_diagnostics.compilerDiagnosticToLsp;
const diagnosticSeverityToLsp = lsp_diagnostics.diagnosticSeverityToLsp;
const pathToUri = lsp_server.pathToUri;
const uriToPath = lsp_server.uriToPath;
const siblingPathForProof = lsp_server.siblingPathForProof;
const documentKind = lsp_server.documentKind;

const TestTransport = struct {
    transport: lsp.Transport = .{ .vtable = &vtable },
    messages: [64][]const u8 = undefined,
    message_count: usize = 0,
    // Backs the copies made in `writeJsonMessage`: the caller's `message`
    // buffer is transient (freed once the write returns), so storing the slice
    // directly would leave `messages` dangling by the time a test asserts on
    // it. Deliberately page_allocator-backed and never freed — test-lifetime
    // storage outside the testing allocator's leak accounting.
    storage: std.heap.ArenaAllocator =
        std.heap.ArenaAllocator.init(std.heap.page_allocator),

    const vtable: lsp.Transport.VTable = .{
        .readJsonMessage = readJsonMessage,
        .writeJsonMessage = writeJsonMessage,
    };

    fn clearMessages(self: *TestTransport) void {
        self.message_count = 0;
    }

    fn containsMessage(self: *const TestTransport, needle: []const u8) bool {
        for (self.messages[0..self.message_count]) |message| {
            if (std.mem.containsAtLeast(u8, message, 1, needle)) {
                return true;
            }
        }
        return false;
    }

    fn readJsonMessage(
        _: *lsp.Transport,
        _: std.mem.Allocator,
    ) lsp.Transport.ReadError![]u8 {
        return error.EndOfStream;
    }

    fn writeJsonMessage(
        transport: *lsp.Transport,
        message: []const u8,
    ) lsp.Transport.WriteError!void {
        const self: *TestTransport = @fieldParentPtr(
            "transport",
            transport,
        );
        if (self.message_count >= self.messages.len) unreachable;
        const copy = self.storage.allocator().dupe(u8, message) catch
            unreachable;
        self.messages[self.message_count] = copy;
        self.message_count += 1;
    }
};

fn testPosition(text: []const u8, needle: []const u8) !types.Position {
    const offset = std.mem.indexOf(u8, text, needle) orelse {
        return error.MissingNeedle;
    };
    return lsp.offsets.indexToPosition(text, offset, .@"utf-16");
}

fn testLastPosition(text: []const u8, needle: []const u8) !types.Position {
    const offset = std.mem.lastIndexOf(u8, text, needle) orelse {
        return error.MissingNeedle;
    };
    return lsp.offsets.indexToPosition(text, offset, .@"utf-16");
}

fn expectRangeText(
    text: []const u8,
    range: types.Range,
    expected: []const u8,
) !void {
    const loc = lsp.offsets.rangeToLoc(text, range, .@"utf-16");
    try std.testing.expectEqualStrings(expected, text[loc.start..loc.end]);
}

fn expectDefinitionLocation(
    result: lsp.ResultType("textDocument/definition"),
) !types.Location {
    const value = result orelse return error.ExpectedDefinition;
    return switch (value) {
        .Definition => |definition| switch (definition) {
            .Location => |location| location,
            else => error.ExpectedDefinitionLocation,
        },
        else => error.ExpectedDefinitionLocation,
    };
}

fn expectImplementationLocation(
    result: lsp.ResultType("textDocument/implementation"),
) !types.Location {
    const value = result orelse return error.ExpectedImplementation;
    return switch (value) {
        .Definition => |definition| switch (definition) {
            .Location => |location| location,
            else => error.ExpectedImplementationLocation,
        },
        else => error.ExpectedImplementationLocation,
    };
}

fn expectDocumentSymbols(
    result: lsp.ResultType("textDocument/documentSymbol"),
) ![]const types.DocumentSymbol {
    const value = result orelse return error.ExpectedDocumentSymbols;
    return switch (value) {
        .array_of_DocumentSymbol => |symbols| symbols,
        else => error.ExpectedDocumentSymbols,
    };
}

fn expectCompletionItems(
    result: lsp.ResultType("textDocument/completion"),
) ![]const types.CompletionItem {
    const value = result orelse return error.ExpectedCompletions;
    return switch (value) {
        // Always a list, and always incomplete: the items depend on the token
        // under the cursor, so a client must re-query rather than filter the
        // previous answer.
        .CompletionList => |list| blk: {
            if (!list.isIncomplete) return error.ExpectedIncompleteCompletions;
            break :blk list.items;
        },
        else => error.ExpectedCompletions,
    };
}

fn completionItemNamed(
    items: []const types.CompletionItem,
    label: []const u8,
) ?types.CompletionItem {
    for (items) |item| {
        if (std.mem.eql(u8, item.label, label)) return item;
    }
    return null;
}

fn expectCompletionEditText(
    text: []const u8,
    item: types.CompletionItem,
    expected_old: []const u8,
    expected_new: []const u8,
) !void {
    const edit = item.textEdit orelse return error.ExpectedTextEdit;
    const text_edit = switch (edit) {
        .TextEdit => |value| value,
        else => return error.ExpectedTextEdit,
    };
    try expectRangeText(text, text_edit.range, expected_old);
    try std.testing.expectEqualStrings(expected_new, text_edit.newText);
}

fn expectCodeActionItems(
    result: CodeActionResult,
) ![]const CodeActionItem {
    return result orelse error.ExpectedCodeActions;
}

fn codeActionSingleEdit(
    action: types.CodeAction,
    uri: []const u8,
) ?types.TextEdit {
    const workspace_edit = action.edit orelse return null;
    const changes = workspace_edit.changes orelse return null;
    const edits = changes.map.get(uri) orelse return null;
    if (edits.len != 1) return null;
    return edits[0];
}

fn firstCodeAction(items: []const CodeActionItem) ?types.CodeAction {
    for (items) |item| switch (item) {
        .CodeAction => |action| return action,
        .Command => {},
    };
    return null;
}

fn codeActionWithReplacement(
    items: []const CodeActionItem,
    uri: []const u8,
    expected_new: []const u8,
) ?types.CodeAction {
    for (items) |item| switch (item) {
        .CodeAction => |action| {
            const edit = codeActionSingleEdit(action, uri) orelse continue;
            if (std.mem.eql(u8, edit.newText, expected_new)) {
                return action;
            }
        },
        .Command => {},
    };
    return null;
}

// Verify the (uncapped) search API offers `expected_replacement` at `marker`.
// Used where the LSP code action caps results below the rank of the suggestion
// under test (e.g. a local lemma outranked by an axiom), so the indexing must be
// checked at the search layer rather than the capped action list.
fn expectSearchOffers(
    allocator: std.mem.Allocator,
    proof_text: []const u8,
    marker: []const u8,
    expected_replacement: []const u8,
) !void {
    const Search = mm0.CompilerSupport.Search;
    const offset = std.mem.indexOf(u8, proof_text, marker) orelse
        return error.MissingMarker;
    var suggestions = try Search.suggestionsAtSourceOffset(
        allocator,
        lsp_search_mm0_text,
        proof_text,
        offset,
        .{},
    );
    defer suggestions.deinit();
    for (suggestions.items) |item| {
        if (std.mem.eql(u8, item.replacement, expected_replacement)) return;
    }
    return error.SearchDidNotOfferExpected;
}

fn codeActionParamsAt(
    uri: []const u8,
    text: []const u8,
    needle: []const u8,
) !types.CodeActionParams {
    const position = try testPosition(text, needle);
    return .{
        .textDocument = .{ .uri = uri },
        .range = .{ .start = position, .end = position },
        .context = .{ .diagnostics = &.{} },
    };
}

const lsp_navigation_mm0_text =
    \\provable sort wff;
    \\term top: wff;
    \\axiom top_i: $ top $;
    \\axiom keep: $ top $ > $ top $;
    \\theorem main: $ top $ > $ top $;
;

const lsp_navigation_proof_text =
    \\main
    \\----
    \\l1: $ top $ by top_i []
    \\l2: $ top $ by keep [l1]
;

fn putLspNavigationDocuments(
    handler: *Handler,
    mm0_uri: []const u8,
    proof_uri: []const u8,
) !void {
    try handler.putDocument(mm0_uri, lsp_navigation_mm0_text, 1);
    try handler.putDocument(proof_uri, lsp_navigation_proof_text, 1);
}

const lsp_search_mm0_text =
    \\provable sort wff;
    \\term top: wff;
    \\axiom top_i: $ top $;
    \\axiom keep: $ top $ > $ top $;
    \\theorem main: $ top $ > $ top $;
;

const lsp_search_exact_proof_text =
    \\main
    \\----
    \\l1: $ top $ by exact?
;

const lsp_search_apply_proof_text =
    \\main
    \\----
    \\l1: $ top $ by apply?
;

test "LSP initialize advertises navigation capabilities" {
    var transport_state: TestTransport = .{};
    var handler = Handler.init(
        std.testing.allocator,
        &transport_state.transport,
    );
    defer handler.deinit();

    const result = handler.initialize(std.testing.allocator, .{
        .capabilities = .{
            .textDocument = .{
                .documentSymbol = .{
                    .hierarchicalDocumentSymbolSupport = true,
                },
            },
        },
    });

    const hover = result.capabilities.hoverProvider orelse {
        return error.ExpectedHoverProvider;
    };
    switch (hover) {
        .bool => |enabled| try std.testing.expect(enabled),
        else => return error.ExpectedBooleanHoverProvider,
    }

    const definition = result.capabilities.definitionProvider orelse {
        return error.ExpectedDefinitionProvider;
    };
    switch (definition) {
        .bool => |enabled| try std.testing.expect(enabled),
        else => return error.ExpectedBooleanDefinitionProvider,
    }

    const implementation = result.capabilities.implementationProvider orelse {
        return error.ExpectedImplementationProvider;
    };
    switch (implementation) {
        .bool => |enabled| try std.testing.expect(enabled),
        else => return error.ExpectedBooleanImplementationProvider,
    }

    const references = result.capabilities.referencesProvider orelse {
        return error.ExpectedReferencesProvider;
    };
    switch (references) {
        .bool => |enabled| try std.testing.expect(enabled),
        else => return error.ExpectedBooleanReferencesProvider,
    }

    const completion = result.capabilities.completionProvider orelse {
        return error.ExpectedCompletionProvider;
    };
    try std.testing.expectEqual(false, completion.resolveProvider.?);
    // `?` must be declared: clients only auto-open the popup on identifier
    // characters otherwise, and several close it when a non-word character
    // lands in the token — which is every keystroke that finishes `auto?`.
    const triggers = completion.triggerCharacters orelse {
        return error.ExpectedCompletionTriggerCharacters;
    };
    try std.testing.expectEqual(@as(usize, 1), triggers.len);
    try std.testing.expectEqualStrings("?", triggers[0]);

    const code_action = result.capabilities.codeActionProvider orelse {
        return error.ExpectedCodeActionProvider;
    };
    switch (code_action) {
        .bool => |enabled| try std.testing.expect(enabled),
        else => return error.ExpectedBooleanCodeActionProvider,
    }

    const document_symbol = result.capabilities.documentSymbolProvider orelse {
        return error.ExpectedDocumentSymbolProvider;
    };
    switch (document_symbol) {
        .bool => |enabled| try std.testing.expect(enabled),
        else => return error.ExpectedBooleanDocumentSymbolProvider,
    }
}

test "LSP initialize omits document symbols for non-hierarchical clients" {
    var transport_state: TestTransport = .{};
    var handler = Handler.init(
        std.testing.allocator,
        &transport_state.transport,
    );
    defer handler.deinit();

    const result = handler.initialize(std.testing.allocator, .{
        .capabilities = .{},
    });

    try std.testing.expect(result.capabilities.documentSymbolProvider == null);
}

test "LSP code action replaces exact placeholder" {
    const mm0_uri = "file:///tmp/lsp-code-action-exact.mm0";
    const proof_uri = "file:///tmp/lsp-code-action-exact.auf";

    var transport_state: TestTransport = .{};
    var handler = Handler.init(
        std.testing.allocator,
        &transport_state.transport,
    );
    defer handler.deinit();
    try handler.putDocument(mm0_uri, lsp_search_mm0_text, 1);
    try handler.putDocument(proof_uri, lsp_search_exact_proof_text, 1);

    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    const actions = try expectCodeActionItems(
        try handler.@"textDocument/codeAction"(
            arena_state.allocator(),
            try codeActionParamsAt(
                proof_uri,
                lsp_search_exact_proof_text,
                "exact?",
            ),
        ),
    );
    const action = codeActionWithReplacement(actions, proof_uri, "top_i") orelse {
        return error.MissingExactCodeAction;
    };
    try std.testing.expectEqual(types.CodeActionKind.quickfix, action.kind.?);
    const edit = codeActionSingleEdit(action, proof_uri) orelse {
        return error.ExpectedCodeActionEdit;
    };
    try expectRangeText(lsp_search_exact_proof_text, edit.range, "exact?");
}

test "LSP code action offers unpack for inline applications" {
    const mm0_uri = "file:///tmp/lsp-code-action-unpack.mm0";
    const proof_uri = "file:///tmp/lsp-code-action-unpack.auf";
    const proof_text =
        \\main
        \\----
        \\l1: $ top $ by keep [top_i []]
        \\
    ;

    var transport_state: TestTransport = .{};
    var handler = Handler.init(
        std.testing.allocator,
        &transport_state.transport,
    );
    defer handler.deinit();
    try handler.putDocument(mm0_uri, lsp_search_mm0_text, 1);
    try handler.putDocument(proof_uri, proof_text, 1);

    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    const actions = try expectCodeActionItems(
        try handler.@"textDocument/codeAction"(
            arena_state.allocator(),
            try codeActionParamsAt(proof_uri, proof_text, "keep [top_i"),
        ),
    );
    const expected_replacement =
        \\l1_1: $ top $ by top_i
        \\l1: $ top $ by keep [l1_1]
        \\
    ;
    const action = codeActionWithReplacement(
        actions,
        proof_uri,
        expected_replacement,
    ) orelse return error.MissingUnpackCodeAction;
    try std.testing.expectEqual(
        types.CodeActionKind.@"refactor.rewrite",
        action.kind.?,
    );
    try std.testing.expectEqualStrings(
        "Unpack inline application",
        action.title,
    );
    const edit = codeActionSingleEdit(action, proof_uri) orelse {
        return error.ExpectedCodeActionEdit;
    };
    try expectRangeText(
        proof_text,
        edit.range,
        "l1: $ top $ by keep [top_i []]\n",
    );
}

test "LSP code action caches search results across identical requests" {
    const mm0_uri = "file:///tmp/lsp-code-action-cache.mm0";
    const proof_uri = "file:///tmp/lsp-code-action-cache.auf";

    var transport_state: TestTransport = .{};
    var handler = Handler.init(
        std.testing.allocator,
        &transport_state.transport,
    );
    defer handler.deinit();
    try handler.putDocument(mm0_uri, lsp_search_mm0_text, 1);
    try handler.putDocument(proof_uri, lsp_search_exact_proof_text, 1);

    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();

    const first = try expectCodeActionItems(
        try handler.@"textDocument/codeAction"(
            arena_state.allocator(),
            try codeActionParamsAt(
                proof_uri,
                lsp_search_exact_proof_text,
                "exact?",
            ),
        ),
    );
    try std.testing.expectEqual(@as(usize, 1), handler.search_cache.count());
    const cached_ptr = handler.search_cache.getPtr(proof_uri).?.suggestions.ptr;
    const first_action =
        codeActionWithReplacement(first, proof_uri, "top_i") orelse
        return error.MissingExactCodeAction;

    // A second identical request must reuse the cached entry (same backing
    // suggestions, no eviction/recompute) rather than re-running the search.
    const second = try expectCodeActionItems(
        try handler.@"textDocument/codeAction"(
            arena_state.allocator(),
            try codeActionParamsAt(
                proof_uri,
                lsp_search_exact_proof_text,
                "exact?",
            ),
        ),
    );
    try std.testing.expectEqual(@as(usize, 1), handler.search_cache.count());
    try std.testing.expectEqual(
        cached_ptr,
        handler.search_cache.getPtr(proof_uri).?.suggestions.ptr,
    );
    const second_action =
        codeActionWithReplacement(second, proof_uri, "top_i") orelse
        return error.MissingExactCodeAction;

    const first_edit =
        codeActionSingleEdit(first_action, proof_uri).?;
    const second_edit =
        codeActionSingleEdit(second_action, proof_uri).?;
    try std.testing.expectEqualStrings(
        first_edit.newText,
        second_edit.newText,
    );
}

test "LSP code action cache hits across different offsets on the same step" {
    const mm0_uri = "file:///tmp/lsp-code-action-cache-offset.mm0";
    const proof_uri = "file:///tmp/lsp-code-action-cache-offset.auf";

    var transport_state: TestTransport = .{};
    var handler = Handler.init(
        std.testing.allocator,
        &transport_state.transport,
    );
    defer handler.deinit();
    try handler.putDocument(mm0_uri, lsp_search_mm0_text, 1);
    try handler.putDocument(proof_uri, lsp_search_exact_proof_text, 1);

    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();

    // First request lands inside the goal text `$ top $`...
    _ = try expectCodeActionItems(
        try handler.@"textDocument/codeAction"(
            arena_state.allocator(),
            try codeActionParamsAt(proof_uri, lsp_search_exact_proof_text, "top"),
        ),
    );
    try std.testing.expectEqual(@as(usize, 1), handler.search_cache.count());
    const cached_ptr = handler.search_cache.getPtr(proof_uri).?.suggestions.ptr;

    // ...a second request at a different column of the SAME proof step (the
    // `exact?` keyword) must reuse the cached result via its placeholder span,
    // not re-run the search and evict.
    const second = try expectCodeActionItems(
        try handler.@"textDocument/codeAction"(
            arena_state.allocator(),
            try codeActionParamsAt(proof_uri, lsp_search_exact_proof_text, "exact?"),
        ),
    );
    try std.testing.expectEqual(@as(usize, 1), handler.search_cache.count());
    try std.testing.expectEqual(
        cached_ptr,
        handler.search_cache.getPtr(proof_uri).?.suggestions.ptr,
    );
    try std.testing.expect(
        codeActionWithReplacement(second, proof_uri, "top_i") != null,
    );
}

test "LSP code action search cache is freed when the document closes" {
    const mm0_uri = "file:///tmp/lsp-code-action-cache-close.mm0";
    const proof_uri = "file:///tmp/lsp-code-action-cache-close.auf";

    var transport_state: TestTransport = .{};
    var handler = Handler.init(
        std.testing.allocator,
        &transport_state.transport,
    );
    defer handler.deinit();
    try handler.putDocument(mm0_uri, lsp_search_mm0_text, 1);
    try handler.putDocument(proof_uri, lsp_search_exact_proof_text, 1);

    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();

    _ = try expectCodeActionItems(
        try handler.@"textDocument/codeAction"(
            arena_state.allocator(),
            try codeActionParamsAt(
                proof_uri,
                lsp_search_exact_proof_text,
                "exact?",
            ),
        ),
    );
    try std.testing.expectEqual(@as(usize, 1), handler.search_cache.count());

    try handler.@"textDocument/didClose"(
        arena_state.allocator(),
        .{ .textDocument = .{ .uri = proof_uri } },
    );
    try std.testing.expectEqual(@as(usize, 0), handler.search_cache.count());
}

test "LSP code action replaces entire placeholder application" {
    const mm0_uri = "file:///tmp/lsp-code-action-stale-ref.mm0";
    const proof_uri = "file:///tmp/lsp-code-action-stale-ref.auf";
    const proof_text =
        \\main
        \\----
        \\l1: $ top $ by exact? [#1]
    ;

    var transport_state: TestTransport = .{};
    var handler = Handler.init(
        std.testing.allocator,
        &transport_state.transport,
    );
    defer handler.deinit();
    try handler.putDocument(mm0_uri, lsp_search_mm0_text, 1);
    try handler.putDocument(proof_uri, proof_text, 1);

    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    const actions = try expectCodeActionItems(
        try handler.@"textDocument/codeAction"(
            arena_state.allocator(),
            try codeActionParamsAt(proof_uri, proof_text, "exact?"),
        ),
    );
    const action = codeActionWithReplacement(actions, proof_uri, "top_i") orelse {
        return error.MissingWholeApplicationCodeAction;
    };
    const edit = codeActionSingleEdit(action, proof_uri) orelse {
        return error.ExpectedCodeActionEdit;
    };
    try expectRangeText(proof_text, edit.range, "exact? [#1]");
}

test "LSP code action completes inline exact placeholder" {
    const mm0_uri = "file:///tmp/lsp-code-action-inline-exact.mm0";
    const proof_uri = "file:///tmp/lsp-code-action-inline-exact.auf";
    const proof_text =
        \\main
        \\----
        \\l1: $ top $ by keep [exact?]
    ;

    var transport_state: TestTransport = .{};
    var handler = Handler.init(
        std.testing.allocator,
        &transport_state.transport,
    );
    defer handler.deinit();
    try handler.putDocument(mm0_uri, lsp_search_mm0_text, 1);
    try handler.putDocument(proof_uri, proof_text, 1);

    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    const actions = try expectCodeActionItems(
        try handler.@"textDocument/codeAction"(
            arena_state.allocator(),
            try codeActionParamsAt(proof_uri, proof_text, "exact?"),
        ),
    );
    const action = codeActionWithReplacement(actions, proof_uri, "#1") orelse {
        return error.MissingInlineExactCodeAction;
    };
    const edit = codeActionSingleEdit(action, proof_uri) orelse {
        return error.ExpectedCodeActionEdit;
    };
    try expectRangeText(proof_text, edit.range, "exact?");
}

test "LSP diagnostics ignore inline search placeholders" {
    const mm0_uri = "file:///tmp/lsp-inline-placeholder-diag.mm0";
    const proof_uri = "file:///tmp/lsp-inline-placeholder-diag.auf";
    const proof_text =
        \\main
        \\----
        \\l1: $ top $ by keep [exact?]
    ;

    var transport_state: TestTransport = .{};
    var handler = Handler.init(
        std.testing.allocator,
        &transport_state.transport,
    );
    defer handler.deinit();

    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();

    try handler.@"textDocument/didOpen"(arena, .{
        .textDocument = .{
            .uri = mm0_uri,
            .languageId = "mm0",
            .version = 1,
            .text = lsp_search_mm0_text,
        },
    });
    transport_state.clearMessages();
    try handler.@"textDocument/didOpen"(arena, .{
        .textDocument = .{
            .uri = proof_uri,
            .languageId = "auf",
            .version = 1,
            .text = proof_text,
        },
    });

    try std.testing.expect(transport_state.message_count > 0);
    try std.testing.expect(!transport_state.containsMessage("unknown rule"));
}

test "LSP placeholder status diagnostics upgrade after code action search" {
    const mm0_uri = "file:///tmp/lsp-status-diag.mm0";
    const proof_uri = "file:///tmp/lsp-status-diag.auf";

    var transport_state: TestTransport = .{};
    var handler = Handler.init(
        std.testing.allocator,
        &transport_state.transport,
    );
    defer handler.deinit();

    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();

    try handler.@"textDocument/didOpen"(arena, .{
        .textDocument = .{
            .uri = mm0_uri,
            .languageId = "mm0",
            .version = 1,
            .text = lsp_search_mm0_text,
        },
    });
    transport_state.clearMessages();
    try handler.@"textDocument/didOpen"(arena, .{
        .textDocument = .{
            .uri = proof_uri,
            .languageId = "auf",
            .version = 1,
            .text = lsp_search_exact_proof_text,
        },
    });

    // An unsearched placeholder publishes a warning (severity 2).
    try std.testing.expect(
        transport_state.containsMessage("search not yet run"),
    );
    try std.testing.expect(transport_state.containsMessage("\"severity\":2"));

    // Running the search via code actions records the outcome and re-publishes
    // the placeholder diagnostic as info (severity 3) with the found proof.
    transport_state.clearMessages();
    _ = try handler.@"textDocument/codeAction"(
        arena,
        try codeActionParamsAt(
            proof_uri,
            lsp_search_exact_proof_text,
            "exact?",
        ),
    );
    try std.testing.expectEqual(@as(usize, 1), handler.search_status.count());
    try std.testing.expectEqual(
        mm0.CompilerSupport.Search.SearchStatus.found,
        handler.search_status.getPtr(proof_uri).?.statuses.items[0].status,
    );
    try std.testing.expect(
        transport_state.containsMessage("exact? search succeeded: top_i"),
    );
    try std.testing.expect(transport_state.containsMessage("\"severity\":3"));
    try std.testing.expect(
        !transport_state.containsMessage("search not yet run"),
    );

    // A cache-hit code action publishes nothing new (the outcome is already
    // recorded and published).
    transport_state.clearMessages();
    _ = try handler.@"textDocument/codeAction"(
        arena,
        try codeActionParamsAt(
            proof_uri,
            lsp_search_exact_proof_text,
            "exact?",
        ),
    );
    try std.testing.expectEqual(@as(usize, 0), transport_state.message_count);

    // An edit drops the recorded outcome: the placeholder returns to the
    // "not yet searched" warning.
    transport_state.clearMessages();
    try handler.@"textDocument/didChange"(arena, .{
        .textDocument = .{ .uri = proof_uri, .version = 2 },
        .contentChanges = &.{
            .{ .literal_1 = .{ .text = lsp_search_exact_proof_text } },
        },
    });
    try std.testing.expectEqual(@as(usize, 0), handler.search_status.count());
    try std.testing.expect(
        transport_state.containsMessage("search not yet run"),
    );
    try std.testing.expect(
        !transport_state.containsMessage("search succeeded"),
    );
}

test "LSP placeholder status diagnostics report a search miss as error" {
    const mm0_uri = "file:///tmp/lsp-status-miss.mm0";
    const proof_uri = "file:///tmp/lsp-status-miss.auf";
    // `bot` has no proof rule, so the placeholder search runs to completion
    // without a result.
    const miss_mm0_text =
        \\provable sort wff;
        \\term top: wff;
        \\term bot: wff;
        \\axiom top_i: $ top $;
        \\theorem main: $ top $;
    ;
    const miss_proof_text =
        \\main
        \\----
        \\l1: $ bot $ by exact?
    ;

    var transport_state: TestTransport = .{};
    var handler = Handler.init(
        std.testing.allocator,
        &transport_state.transport,
    );
    defer handler.deinit();

    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();

    try handler.@"textDocument/didOpen"(arena, .{
        .textDocument = .{
            .uri = mm0_uri,
            .languageId = "mm0",
            .version = 1,
            .text = miss_mm0_text,
        },
    });
    try handler.@"textDocument/didOpen"(arena, .{
        .textDocument = .{
            .uri = proof_uri,
            .languageId = "auf",
            .version = 1,
            .text = miss_proof_text,
        },
    });

    transport_state.clearMessages();
    _ = try handler.@"textDocument/codeAction"(
        arena,
        try codeActionParamsAt(proof_uri, miss_proof_text, "exact?"),
    );
    try std.testing.expect(transport_state.containsMessage(
        "exact? search failed: no rule application closes this goal",
    ));
    // The failure detail elaborates the coverage and points at auto?.
    try std.testing.expect(transport_state.containsMessage(
        "auto? can additionally synthesize sub-proofs",
    ));
    try std.testing.expect(transport_state.containsMessage("\"severity\":1"));
    // The code is how a client running its own compile (the browser editor)
    // tells search status apart from the diagnostics it already has.
    try std.testing.expect(transport_state.containsMessage(
        "\"code\":\"search-status\"",
    ));
}

test "LSP placeholder diagnostics report invalid search parameters" {
    const mm0_uri = "file:///tmp/lsp-status-params.mm0";
    const proof_uri = "file:///tmp/lsp-status-params.auf";
    const mm0_text =
        \\provable sort wff;
        \\term top: wff;
        \\axiom top_i: $ top $;
        \\theorem main: $ top $;
    ;
    // One typo'd name and one out-of-range value: each gets its own error
    // diagnostic straight from the analyze pass, no search required.
    const proof_text =
        \\main
        \\----
        \\l1: $ top $ by auto? (depht: 8, depth: 0)
    ;

    var transport_state: TestTransport = .{};
    var handler = Handler.init(
        std.testing.allocator,
        &transport_state.transport,
    );
    defer handler.deinit();

    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();

    try handler.@"textDocument/didOpen"(arena, .{
        .textDocument = .{
            .uri = mm0_uri,
            .languageId = "mm0",
            .version = 1,
            .text = mm0_text,
        },
    });
    try handler.@"textDocument/didOpen"(arena, .{
        .textDocument = .{
            .uri = proof_uri,
            .languageId = "auf",
            .version = 1,
            .text = proof_text,
        },
    });

    try std.testing.expect(transport_state.containsMessage(
        "unknown auto? parameter 'depht'",
    ));
    try std.testing.expect(transport_state.containsMessage(
        "'depth' must be between 1 and 64",
    ));
}

test "LSP code action replaces apply placeholder with plain refs" {
    const mm0_uri = "file:///tmp/lsp-code-action-apply.mm0";
    const proof_uri = "file:///tmp/lsp-code-action-apply.auf";

    var transport_state: TestTransport = .{};
    var handler = Handler.init(
        std.testing.allocator,
        &transport_state.transport,
    );
    defer handler.deinit();
    try handler.putDocument(mm0_uri, lsp_search_mm0_text, 1);
    try handler.putDocument(proof_uri, lsp_search_apply_proof_text, 1);

    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    const actions = try expectCodeActionItems(
        try handler.@"textDocument/codeAction"(
            arena_state.allocator(),
            try codeActionParamsAt(
                proof_uri,
                lsp_search_apply_proof_text,
                "apply?",
            ),
        ),
    );
    const action = codeActionWithReplacement(
        actions,
        proof_uri,
        "keep [ref1]",
    ) orelse return error.MissingApplyCodeAction;
    const edit = codeActionSingleEdit(action, proof_uri) orelse {
        return error.ExpectedCodeActionEdit;
    };
    try expectRangeText(lsp_search_apply_proof_text, edit.range, "apply?");
}

test "LSP code action uses UTF-16 ranges after non-ASCII text" {
    const mm0_uri = "file:///tmp/lsp-code-action-utf16.mm0";
    const proof_uri = "file:///tmp/lsp-code-action-utf16.auf";
    const proof_text =
        \\-- 💡
        \\main
        \\----
        \\l1: $ top $ by exact?
    ;

    var transport_state: TestTransport = .{};
    var handler = Handler.init(
        std.testing.allocator,
        &transport_state.transport,
    );
    defer handler.deinit();
    try handler.putDocument(mm0_uri, lsp_search_mm0_text, 1);
    try handler.putDocument(proof_uri, proof_text, 1);

    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    const actions = try expectCodeActionItems(
        try handler.@"textDocument/codeAction"(
            arena_state.allocator(),
            try codeActionParamsAt(proof_uri, proof_text, "exact?"),
        ),
    );
    const action = codeActionWithReplacement(actions, proof_uri, "top_i") orelse {
        return error.MissingUtf16CodeAction;
    };
    const edit = codeActionSingleEdit(action, proof_uri) orelse {
        return error.ExpectedCodeActionEdit;
    };
    try expectRangeText(proof_text, edit.range, "exact?");
}

test "LSP code action is absent outside search placeholders" {
    const mm0_uri = "file:///tmp/lsp-code-action-none.mm0";
    const proof_uri = "file:///tmp/lsp-code-action-none.auf";

    var transport_state: TestTransport = .{};
    var handler = Handler.init(
        std.testing.allocator,
        &transport_state.transport,
    );
    defer handler.deinit();
    try putLspNavigationDocuments(&handler, mm0_uri, proof_uri);

    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    const result = try handler.@"textDocument/codeAction"(
        arena_state.allocator(),
        try codeActionParamsAt(proof_uri, lsp_navigation_proof_text, "top_i"),
    );
    try std.testing.expect(result == null);
}

test "LSP code action is absent for invalid search contexts" {
    const mm0_uri = "file:///tmp/lsp-code-action-invalid.mm0";
    const proof_uri = "file:///tmp/lsp-code-action-invalid.auf";
    const proof_text =
        \\main
        \\----
        \\l1: $ unknown_token $ by exact?
    ;

    var transport_state: TestTransport = .{};
    var handler = Handler.init(
        std.testing.allocator,
        &transport_state.transport,
    );
    defer handler.deinit();
    try handler.putDocument(mm0_uri, lsp_search_mm0_text, 1);
    try handler.putDocument(proof_uri, proof_text, 1);

    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    const result = try handler.@"textDocument/codeAction"(
        arena_state.allocator(),
        try codeActionParamsAt(proof_uri, proof_text, "exact?"),
    );
    try std.testing.expect(result == null);
}

test "LSP code action is absent without sibling mm0" {
    const proof_uri = "file:///tmp/lsp-code-action-missing-sibling.auf";

    var transport_state: TestTransport = .{};
    var handler = Handler.init(
        std.testing.allocator,
        &transport_state.transport,
    );
    defer handler.deinit();
    try handler.putDocument(proof_uri, lsp_search_exact_proof_text, 1);

    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    const result = try handler.@"textDocument/codeAction"(
        arena_state.allocator(),
        try codeActionParamsAt(
            proof_uri,
            lsp_search_exact_proof_text,
            "exact?",
        ),
    );
    try std.testing.expect(result == null);
}

test "LSP code action uses prior local lemma in theorem search" {
    const mm0_uri = "file:///tmp/lsp-code-action-local-theorem.mm0";
    const proof_uri = "file:///tmp/lsp-code-action-local-theorem.auf";
    const proof_text =
        \\lemma local_top: $ top $
        \\---------
        \\h1: $ top $ by top_i
        \\
        \\main
        \\----
        \\l1: $ top $ by exact?
    ;

    var transport_state: TestTransport = .{};
    var handler = Handler.init(
        std.testing.allocator,
        &transport_state.transport,
    );
    defer handler.deinit();
    try handler.putDocument(mm0_uri, lsp_search_mm0_text, 1);
    try handler.putDocument(proof_uri, proof_text, 1);

    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    const actions = try expectCodeActionItems(
        try handler.@"textDocument/codeAction"(
            arena_state.allocator(),
            try codeActionParamsAt(proof_uri, proof_text, "exact?"),
        ),
    );
    // Local-lemma *indexing* is a search-layer property; verify it with the
    // uncapped search API. The LSP code action caps `exact?` at one best result,
    // where the `top_i` axiom outranks the local lemma, so the capped action list
    // need not contain `local_top` — but the search must still find it.
    try expectSearchOffers(arena_state.allocator(), proof_text, "exact?", "local_top");
    const action = firstCodeAction(actions) orelse return error.ExpectedCodeAction;
    const edit = codeActionSingleEdit(action, proof_uri) orelse {
        return error.ExpectedCodeActionEdit;
    };
    try expectRangeText(proof_text, edit.range, "exact?");
}

test "LSP code action works inside local lemma blocks" {
    const mm0_uri = "file:///tmp/lsp-code-action-local-target.mm0";
    const proof_uri = "file:///tmp/lsp-code-action-local-target.auf";
    const proof_text =
        \\lemma local_top: $ top $
        \\---------
        \\h1: $ top $ by top_i
        \\
        \\lemma use_local: $ top $
        \\---------
        \\u1: $ top $ by exact?
        \\
        \\main
        \\----
        \\l1: $ top $ by top_i
    ;

    var transport_state: TestTransport = .{};
    var handler = Handler.init(
        std.testing.allocator,
        &transport_state.transport,
    );
    defer handler.deinit();
    try handler.putDocument(mm0_uri, lsp_search_mm0_text, 1);
    try handler.putDocument(proof_uri, proof_text, 1);

    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    const actions = try expectCodeActionItems(
        try handler.@"textDocument/codeAction"(
            arena_state.allocator(),
            try codeActionParamsAt(proof_uri, proof_text, "exact?"),
        ),
    );
    // See the prior test: local-lemma indexing is verified at the (uncapped)
    // search layer; the capped LSP action need not surface the outranked lemma.
    try expectSearchOffers(arena_state.allocator(), proof_text, "exact?", "local_top");
    const action = firstCodeAction(actions) orelse return error.ExpectedCodeAction;
    const edit = codeActionSingleEdit(action, proof_uri) orelse {
        return error.ExpectedCodeActionEdit;
    };
    try expectRangeText(proof_text, edit.range, "exact?");
}

test "LSP code action excludes future local lemmas" {
    const mm0_uri = "file:///tmp/lsp-code-action-local-future.mm0";
    const proof_uri = "file:///tmp/lsp-code-action-local-future.auf";
    const proof_text =
        \\lemma use_future: $ top $
        \\---------
        \\u1: $ top $ by exact?
        \\
        \\lemma future_top: $ top $
        \\---------
        \\f1: $ top $ by top_i
        \\
        \\main
        \\----
        \\l1: $ top $ by top_i
    ;

    var transport_state: TestTransport = .{};
    var handler = Handler.init(
        std.testing.allocator,
        &transport_state.transport,
    );
    defer handler.deinit();
    try handler.putDocument(mm0_uri, lsp_search_mm0_text, 1);
    try handler.putDocument(proof_uri, proof_text, 1);

    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    const actions = try expectCodeActionItems(
        try handler.@"textDocument/codeAction"(
            arena_state.allocator(),
            try codeActionParamsAt(proof_uri, proof_text, "exact?"),
        ),
    );
    try std.testing.expect(
        codeActionWithReplacement(actions, proof_uri, "future_top") == null,
    );
}

test "LSP code action uses open unsaved mm0 and proof documents" {
    const mm0_uri = "file:///tmp/lsp-code-action-unsaved.mm0";
    const proof_uri = "file:///tmp/lsp-code-action-unsaved.auf";
    const mm0_text =
        \\provable sort wff;
        \\term top: wff;
        \\axiom unsaved_i: $ top $;
        \\theorem main: $ top $;
    ;
    const proof_text =
        \\main
        \\----
        \\l1: $ top $ by exact?
    ;

    var transport_state: TestTransport = .{};
    var handler = Handler.init(
        std.testing.allocator,
        &transport_state.transport,
    );
    defer handler.deinit();
    try handler.putDocument(mm0_uri, mm0_text, 1);
    try handler.putDocument(proof_uri, proof_text, 1);

    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    const actions = try expectCodeActionItems(
        try handler.@"textDocument/codeAction"(
            arena_state.allocator(),
            try codeActionParamsAt(proof_uri, proof_text, "exact?"),
        ),
    );
    const action = codeActionWithReplacement(
        actions,
        proof_uri,
        "unsaved_i",
    ) orelse return error.MissingUnsavedCodeAction;
    const edit = codeActionSingleEdit(action, proof_uri) orelse {
        return error.ExpectedCodeActionEdit;
    };
    try expectRangeText(proof_text, edit.range, "exact?");
}

test "LSP proof hover accepts UTF-16 positions after non-ASCII text" {
    const mm0_uri = "file:///tmp/lsp-utf16.mm0";
    const proof_uri = "file:///tmp/lsp-utf16.auf";
    const proof_text =
        \\main
        \\----
        \\l1: $ 💡 top $ by top_i []
        \\l2: $ top $ by keep [l1]
    ;

    var transport_state: TestTransport = .{};
    var handler = Handler.init(
        std.testing.allocator,
        &transport_state.transport,
    );
    defer handler.deinit();
    try handler.putDocument(mm0_uri, lsp_navigation_mm0_text, 1);
    try handler.putDocument(proof_uri, proof_text, 1);

    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    const hover_result = try handler.@"textDocument/hover"(
        arena_state.allocator(),
        .{
            .textDocument = .{ .uri = proof_uri },
            .position = try testPosition(proof_text, "top_i"),
        },
    );
    const hover = hover_result orelse return error.ExpectedHover;
    const range = hover.range orelse return error.ExpectedHoverRange;
    try expectRangeText(proof_text, range, "top_i");

    const markdown = switch (hover.contents) {
        .MarkupContent => |content| content.value,
        else => return error.ExpectedMarkdownHover,
    };
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        markdown,
        1,
        "axiom top_i",
    ));
}

test "LSP proof hole hover shows the inferred expression" {
    const mm0_uri = "file:///tmp/lsp-hole-hover.mm0";
    const proof_uri = "file:///tmp/lsp-hole-hover.auf";
    const mm0_text =
        \\delimiter $ ( ) $;
        \\--| @hole _wff
        \\provable sort wff;
        \\term pair (a b: wff): wff;
        \\term imp (a b: wff): wff;
        \\infixr imp: $->$ prec 25;
        \\axiom select_right (a b: wff): $ pair a b $ > $ b $;
        \\theorem main (p r s: wff):
        \\  $ pair p (r -> s) $ > $ r -> s $;
    ;
    const proof_text =
        \\main
        \\----
        \\l1: $ _wff $ by select_right [#1]
    ;

    var transport_state: TestTransport = .{};
    var handler = Handler.init(
        std.testing.allocator,
        &transport_state.transport,
    );
    defer handler.deinit();
    try handler.putDocument(mm0_uri, mm0_text, 1);
    try handler.putDocument(proof_uri, proof_text, 1);

    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    const hover_result = try handler.@"textDocument/hover"(
        arena_state.allocator(),
        .{
            .textDocument = .{ .uri = proof_uri },
            .position = try testPosition(proof_text, "_wff"),
        },
    );
    const hover = hover_result orelse return error.ExpectedHover;
    const range = hover.range orelse return error.ExpectedHoverRange;
    try expectRangeText(proof_text, range, "_wff");

    const rendered = switch (hover.contents) {
        .MarkupContent => |content| content.value,
        else => return error.ExpectedMarkdownHover,
    };
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        rendered,
        1,
        "$ r -> s $",
    ));
}

test "LSP proof hover resolves rule applications" {
    const mm0_uri = "file:///tmp/lsp-stage2.mm0";
    const proof_uri = "file:///tmp/lsp-stage2.auf";

    var transport_state: TestTransport = .{};
    var handler = Handler.init(
        std.testing.allocator,
        &transport_state.transport,
    );
    defer handler.deinit();
    try putLspNavigationDocuments(&handler, mm0_uri, proof_uri);

    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    const hover_result = try handler.@"textDocument/hover"(
        arena_state.allocator(),
        .{
            .textDocument = .{ .uri = proof_uri },
            .position = try testLastPosition(lsp_navigation_proof_text, "keep"),
        },
    );
    const hover = hover_result orelse return error.ExpectedHover;
    const range = hover.range orelse return error.ExpectedHoverRange;
    try expectRangeText(lsp_navigation_proof_text, range, "keep");

    const markdown = switch (hover.contents) {
        .MarkupContent => |content| content.value,
        else => return error.ExpectedMarkdownHover,
    };
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        markdown,
        1,
        "axiom keep",
    ));
}

test "LSP completion returns only rules applicable to the line goal" {
    const mm0_uri = "file:///tmp/lsp-applicable-completion.mm0";
    const proof_uri = "file:///tmp/lsp-applicable-completion.auf";
    const mm0_text =
        \\provable sort wff;
        \\term top: wff;
        \\term bot: wff;
        \\axiom top_i: $ top $;
        \\axiom bot_i: $ bot $;
        \\axiom keep: $ top $ > $ top $;
        \\theorem main: $ top $;
    ;
    const proof_text =
        \\main
        \\----
        \\l1: $ top $ by ke
    ;

    var transport_state: TestTransport = .{};
    var handler = Handler.init(
        std.testing.allocator,
        &transport_state.transport,
    );
    defer handler.deinit();
    try handler.putDocument(mm0_uri, mm0_text, 1);
    try handler.putDocument(proof_uri, proof_text, 1);

    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    const result = try handler.@"textDocument/completion"(
        arena_state.allocator(),
        .{
            .textDocument = .{ .uri = proof_uri },
            .position = lsp.offsets.indexToPosition(
                proof_text,
                proof_text.len,
                .@"utf-16",
            ),
        },
    );
    const items = try expectCompletionItems(result);
    try std.testing.expect(completionItemNamed(items, "top_i") != null);
    try std.testing.expect(completionItemNamed(items, "keep") != null);
    try std.testing.expect(completionItemNamed(items, "bot_i") == null);

    const keep = completionItemNamed(items, "keep") orelse {
        return error.MissingApplicableKeepCompletion;
    };
    try expectCompletionEditText(proof_text, keep, "ke", "keep");
}

test "LSP completion filters rules inside nested applications" {
    const mm0_uri = "file:///tmp/lsp-nested-applicable-completion.mm0";
    const proof_uri = "file:///tmp/lsp-nested-applicable-completion.auf";
    const mm0_text =
        \\provable sort wff;
        \\term top: wff;
        \\term bot: wff;
        \\axiom top_i: $ top $;
        \\axiom bot_i: $ bot $;
        \\axiom keep: $ top $ > $ top $;
        \\theorem main: $ top $;
    ;
    const proof_text =
        \\main
        \\----
        \\l1: $ top $ by keep [to []]
    ;
    const offset = (std.mem.indexOf(u8, proof_text, "to []") orelse {
        return error.MissingNestedCompletionContext;
    }) + "to".len;

    var transport_state: TestTransport = .{};
    var handler = Handler.init(
        std.testing.allocator,
        &transport_state.transport,
    );
    defer handler.deinit();
    try handler.putDocument(mm0_uri, mm0_text, 1);
    try handler.putDocument(proof_uri, proof_text, 1);

    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    const result = try handler.@"textDocument/completion"(
        arena_state.allocator(),
        .{
            .textDocument = .{ .uri = proof_uri },
            .position = lsp.offsets.indexToPosition(
                proof_text,
                offset,
                .@"utf-16",
            ),
        },
    );
    const items = try expectCompletionItems(result);
    try std.testing.expect(completionItemNamed(items, "top_i") != null);
    try std.testing.expect(completionItemNamed(items, "bot_i") == null);
}

test "LSP completion returns explicit edits" {
    const mm0_uri = "file:///tmp/lsp-completion.mm0";
    const proof_uri = "file:///tmp/lsp-completion.auf";
    const proof_text =
        \\main
        \\----
        \\l1: $ top $ by top_i []
        \\l2: $ top $ by ke
    ;

    var transport_state: TestTransport = .{};
    var handler = Handler.init(
        std.testing.allocator,
        &transport_state.transport,
    );
    defer handler.deinit();
    try handler.putDocument(mm0_uri, lsp_navigation_mm0_text, 1);
    try handler.putDocument(proof_uri, proof_text, 1);

    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    const result = try handler.@"textDocument/completion"(
        arena_state.allocator(),
        .{
            .textDocument = .{ .uri = proof_uri },
            .position = lsp.offsets.indexToPosition(
                proof_text,
                proof_text.len,
                .@"utf-16",
            ),
        },
    );
    const items = try expectCompletionItems(result);
    const keep = completionItemNamed(items, "keep") orelse {
        return error.MissingKeepCompletion;
    };
    try std.testing.expectEqual(types.CompletionItemKind.Method, keep.kind.?);
    try expectCompletionEditText(proof_text, keep, "ke", "keep");
}

test "LSP completion uses UTF-16 ranges after non-ASCII text" {
    const mm0_uri = "file:///tmp/lsp-completion-utf16.mm0";
    const proof_uri = "file:///tmp/lsp-completion-utf16.auf";
    const proof_text =
        \\main
        \\----
        \\l1: $ top $ by top_i []
        \\l2: $ 💡 top $ by ke
    ;
    const offset = (std.mem.indexOf(u8, proof_text, "ke") orelse {
        return error.MissingUtf16CompletionContext;
    }) + "ke".len;

    var transport_state: TestTransport = .{};
    var handler = Handler.init(
        std.testing.allocator,
        &transport_state.transport,
    );
    defer handler.deinit();
    try handler.putDocument(mm0_uri, lsp_navigation_mm0_text, 1);
    try handler.putDocument(proof_uri, proof_text, 1);

    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    const result = try handler.@"textDocument/completion"(
        arena_state.allocator(),
        .{
            .textDocument = .{ .uri = proof_uri },
            .position = lsp.offsets.indexToPosition(
                proof_text,
                offset,
                .@"utf-16",
            ),
        },
    );
    const items = try expectCompletionItems(result);
    const keep = completionItemNamed(items, "keep") orelse {
        return error.MissingKeepUtf16Completion;
    };
    try expectCompletionEditText(proof_text, keep, "ke", "keep");
}

test "LSP completion returns notation snippets for snippet clients" {
    const mm0_uri = "file:///tmp/lsp-snippet.mm0";
    const mm0_text =
        \\provable sort wff;
        \\term forall (p: wff): wff;
        \\theorem main (p: wff): $ fo $;
        \\prefix forall: $∀$ prec 40;
    ;
    const offset = (std.mem.indexOf(u8, mm0_text, "fo $") orelse {
        return error.MissingSnippetContext;
    }) + "fo".len;

    var transport_state: TestTransport = .{};
    var handler = Handler.init(
        std.testing.allocator,
        &transport_state.transport,
    );
    defer handler.deinit();
    _ = handler.initialize(std.testing.allocator, .{
        .capabilities = .{
            .textDocument = .{
                .completion = .{
                    .completionItem = .{
                        .snippetSupport = true,
                    },
                },
            },
        },
    });
    try handler.putDocument(mm0_uri, mm0_text, 1);

    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    const result = try handler.@"textDocument/completion"(
        arena_state.allocator(),
        .{
            .textDocument = .{ .uri = mm0_uri },
            .position = lsp.offsets.indexToPosition(
                mm0_text,
                offset,
                .@"utf-16",
            ),
        },
    );
    const items = try expectCompletionItems(result);
    const snippet = completionItemNamed(items, "∀ …") orelse {
        return error.MissingSnippetCompletion;
    };
    try std.testing.expectEqual(types.CompletionItemKind.Snippet, snippet.kind.?);
    try std.testing.expectEqual(
        types.InsertTextFormat.Snippet,
        snippet.insertTextFormat.?,
    );
    try expectCompletionEditText(mm0_text, snippet, "fo", "∀ ${1:p}$0");
    try std.testing.expectEqualStrings(
        "forall ∀",
        snippet.filterText orelse "",
    );
}

test "LSP completion avoids snippets for plain completion clients" {
    const mm0_uri = "file:///tmp/lsp-no-snippet.mm0";
    const mm0_text =
        \\provable sort wff;
        \\term forall (p: wff): wff;
        \\theorem main (p: wff): $ fo $;
        \\prefix forall: $∀$ prec 40;
    ;
    const offset = (std.mem.indexOf(u8, mm0_text, "fo $") orelse {
        return error.MissingSnippetContext;
    }) + "fo".len;

    var transport_state: TestTransport = .{};
    var handler = Handler.init(
        std.testing.allocator,
        &transport_state.transport,
    );
    defer handler.deinit();
    _ = handler.initialize(std.testing.allocator, .{
        .capabilities = .{},
    });
    try handler.putDocument(mm0_uri, mm0_text, 1);

    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    const result = try handler.@"textDocument/completion"(
        arena_state.allocator(),
        .{
            .textDocument = .{ .uri = mm0_uri },
            .position = lsp.offsets.indexToPosition(
                mm0_text,
                offset,
                .@"utf-16",
            ),
        },
    );
    const items = try expectCompletionItems(result);
    try std.testing.expect(completionItemNamed(items, "∀ …") == null);
    for (items) |item| {
        if (item.insertTextFormat) |format| {
            try std.testing.expect(format != .Snippet);
        }
    }
}

test "LSP proof definition resolves rules and line references" {
    const mm0_uri = "file:///tmp/lsp-stage2.mm0";
    const proof_uri = "file:///tmp/lsp-stage2.auf";

    var transport_state: TestTransport = .{};
    var handler = Handler.init(
        std.testing.allocator,
        &transport_state.transport,
    );
    defer handler.deinit();
    try putLspNavigationDocuments(&handler, mm0_uri, proof_uri);

    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();

    const rule_location = try expectDefinitionLocation(
        try handler.@"textDocument/definition"(arena, .{
            .textDocument = .{ .uri = proof_uri },
            .position = try testLastPosition(lsp_navigation_proof_text, "keep"),
        }),
    );
    try std.testing.expectEqualStrings(mm0_uri, rule_location.uri);
    try expectRangeText(lsp_navigation_mm0_text, rule_location.range, "keep");

    const line_location = try expectDefinitionLocation(
        try handler.@"textDocument/definition"(arena, .{
            .textDocument = .{ .uri = proof_uri },
            .position = try testLastPosition(lsp_navigation_proof_text, "l1"),
        }),
    );
    try std.testing.expectEqualStrings(proof_uri, line_location.uri);
    try expectRangeText(lsp_navigation_proof_text, line_location.range, "l1");
}

test "LSP implementation resolves theorem declarations to proofs" {
    const mm0_uri = "file:///tmp/lsp-stage2.mm0";
    const proof_uri = "file:///tmp/lsp-stage2.auf";

    var transport_state: TestTransport = .{};
    var handler = Handler.init(
        std.testing.allocator,
        &transport_state.transport,
    );
    defer handler.deinit();
    try putLspNavigationDocuments(&handler, mm0_uri, proof_uri);

    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();

    const location = try expectImplementationLocation(
        try handler.@"textDocument/implementation"(arena, .{
            .textDocument = .{ .uri = mm0_uri },
            .position = try testLastPosition(lsp_navigation_mm0_text, "main"),
        }),
    );
    try std.testing.expectEqualStrings(proof_uri, location.uri);
    try expectRangeText(lsp_navigation_proof_text, location.range, "main");

    const axiom = try handler.@"textDocument/implementation"(arena, .{
        .textDocument = .{ .uri = mm0_uri },
        .position = try testLastPosition(lsp_navigation_mm0_text, "keep"),
    });
    try std.testing.expect(axiom == null);
}

test "LSP references returns matching indexed symbol uses" {
    const mm0_uri = "file:///tmp/lsp-stage2.mm0";
    const proof_uri = "file:///tmp/lsp-stage2.auf";

    var transport_state: TestTransport = .{};
    var handler = Handler.init(
        std.testing.allocator,
        &transport_state.transport,
    );
    defer handler.deinit();
    try putLspNavigationDocuments(&handler, mm0_uri, proof_uri);

    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();

    const rule_refs = (try handler.@"textDocument/references"(arena, .{
        .textDocument = .{ .uri = proof_uri },
        .position = try testPosition(lsp_navigation_proof_text, "top_i"),
        .context = .{ .includeDeclaration = true },
    })) orelse return error.ExpectedReferences;
    try std.testing.expectEqual(@as(usize, 2), rule_refs.len);
    try std.testing.expectEqualStrings(mm0_uri, rule_refs[0].uri);
    try expectRangeText(lsp_navigation_mm0_text, rule_refs[0].range, "top_i");
    try std.testing.expectEqualStrings(proof_uri, rule_refs[1].uri);
    try expectRangeText(lsp_navigation_proof_text, rule_refs[1].range, "top_i");

    const rule_uses = (try handler.@"textDocument/references"(arena, .{
        .textDocument = .{ .uri = proof_uri },
        .position = try testPosition(lsp_navigation_proof_text, "top_i"),
        .context = .{ .includeDeclaration = false },
    })) orelse return error.ExpectedReferences;
    try std.testing.expectEqual(@as(usize, 1), rule_uses.len);
    try std.testing.expectEqualStrings(proof_uri, rule_uses[0].uri);
    try expectRangeText(lsp_navigation_proof_text, rule_uses[0].range, "top_i");

    const theorem_uses = (try handler.@"textDocument/references"(arena, .{
        .textDocument = .{ .uri = mm0_uri },
        .position = try testLastPosition(lsp_navigation_mm0_text, "main"),
        .context = .{ .includeDeclaration = false },
    })) orelse return error.ExpectedReferences;
    try std.testing.expectEqual(@as(usize, 1), theorem_uses.len);
    try std.testing.expectEqualStrings(proof_uri, theorem_uses[0].uri);
    try expectRangeText(lsp_navigation_proof_text, theorem_uses[0].range, "main");
}

test "LSP document symbols returns quiet proof outline" {
    const mm0_uri = "file:///tmp/lsp-stage2.mm0";
    const proof_uri = "file:///tmp/lsp-stage2.auf";

    var transport_state: TestTransport = .{};
    var handler = Handler.init(
        std.testing.allocator,
        &transport_state.transport,
    );
    defer handler.deinit();
    try putLspNavigationDocuments(&handler, mm0_uri, proof_uri);

    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();

    const symbols = try expectDocumentSymbols(
        try handler.@"textDocument/documentSymbol"(arena, .{
            .textDocument = .{ .uri = proof_uri },
        }),
    );
    try std.testing.expectEqual(@as(usize, 1), symbols.len);
    try std.testing.expectEqualStrings("main", symbols[0].name);
    try std.testing.expectEqual(types.SymbolKind.Method, symbols[0].kind);
    try std.testing.expect(symbols[0].children == null);
}

test "LSP navigation cache invalidates changed mm0 sibling" {
    const mm0_uri = "file:///tmp/lsp-stage5.mm0";
    const proof_uri = "file:///tmp/lsp-stage5.auf";
    const changed_mm0_text =
        \\provable sort wff;
        \\term top: wff;
        \\axiom top_i: $ top $;
        \\axiom keep2: $ top $ > $ top $;
        \\theorem main: $ top $ > $ top $;
    ;

    var transport_state: TestTransport = .{};
    var handler = Handler.init(
        std.testing.allocator,
        &transport_state.transport,
    );
    defer handler.deinit();
    try putLspNavigationDocuments(&handler, mm0_uri, proof_uri);

    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();

    const first_hover = try handler.@"textDocument/hover"(arena, .{
        .textDocument = .{ .uri = proof_uri },
        .position = try testLastPosition(lsp_navigation_proof_text, "keep"),
    });
    try std.testing.expect(first_hover != null);
    try std.testing.expectEqual(@as(usize, 1), handler.nav_cache.count());

    try handler.@"textDocument/didChange"(arena, .{
        .textDocument = .{ .uri = mm0_uri, .version = 2 },
        .contentChanges = &.{
            .{ .literal_1 = .{ .text = changed_mm0_text } },
        },
    });
    try std.testing.expectEqual(@as(usize, 0), handler.nav_cache.count());

    const hover_result = try handler.@"textDocument/hover"(arena, .{
        .textDocument = .{ .uri = proof_uri },
        .position = try testLastPosition(lsp_navigation_proof_text, "keep"),
    });
    const hover = hover_result orelse return error.ExpectedHover;
    const markdown = switch (hover.contents) {
        .MarkupContent => |content| content.value,
        else => return error.ExpectedMarkdownHover,
    };
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        markdown,
        1,
        "unknown rule `keep`",
    ));
}

test "LSP navigation cache invalidates closed proof sibling" {
    const mm0_uri = "file:///tmp/lsp-stage5-close.mm0";
    const proof_uri = "file:///tmp/lsp-stage5-close.auf";

    var transport_state: TestTransport = .{};
    var handler = Handler.init(
        std.testing.allocator,
        &transport_state.transport,
    );
    defer handler.deinit();
    try putLspNavigationDocuments(&handler, mm0_uri, proof_uri);

    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();

    const hover_result = try handler.@"textDocument/hover"(arena, .{
        .textDocument = .{ .uri = proof_uri },
        .position = try testLastPosition(lsp_navigation_proof_text, "keep"),
    });
    try std.testing.expect(hover_result != null);
    try std.testing.expectEqual(@as(usize, 1), handler.nav_cache.count());

    try handler.@"textDocument/didClose"(arena, .{
        .textDocument = .{ .uri = proof_uri },
    });
    try std.testing.expectEqual(@as(usize, 0), handler.nav_cache.count());
}

test "LSP proof unknown rule has hover but no definition" {
    const mm0_uri = "file:///tmp/lsp-stage2-unknown.mm0";
    const proof_uri = "file:///tmp/lsp-stage2-unknown.auf";
    const mm0_text =
        \\provable sort wff;
        \\term top: wff;
        \\theorem main: $ top $;
    ;
    const proof_text =
        \\main
        \\----
        \\l1: $ top $ by missing []
    ;

    var transport_state: TestTransport = .{};
    var handler = Handler.init(
        std.testing.allocator,
        &transport_state.transport,
    );
    defer handler.deinit();
    try handler.putDocument(mm0_uri, mm0_text, 1);
    try handler.putDocument(proof_uri, proof_text, 1);

    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();

    const hover_result = try handler.@"textDocument/hover"(arena, .{
        .textDocument = .{ .uri = proof_uri },
        .position = try testPosition(proof_text, "missing"),
    });
    const hover = hover_result orelse return error.ExpectedHover;
    const markdown = switch (hover.contents) {
        .MarkupContent => |content| content.value,
        else => return error.ExpectedMarkdownHover,
    };
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        markdown,
        1,
        "unknown rule `missing`",
    ));

    const definition = try handler.@"textDocument/definition"(arena, .{
        .textDocument = .{ .uri = proof_uri },
        .position = try testPosition(proof_text, "missing"),
    });
    try std.testing.expect(definition == null);
}

test "uri path roundtrip" {
    const allocator = std.testing.allocator;
    const path = "/tmp/a path/example.mm0";
    const uri = try pathToUri(allocator, path);
    defer allocator.free(uri);

    const roundtrip = try uriToPath(allocator, uri);
    defer allocator.free(roundtrip);
    try std.testing.expectEqualStrings(path, roundtrip);
}

test "proof sibling path" {
    const allocator = std.testing.allocator;
    const path = try siblingPathForProof(allocator, "/tmp/demo.auf");
    defer allocator.free(path);
    try std.testing.expectEqualStrings("/tmp/demo.mm0", path);
}

test "document kind" {
    try std.testing.expectEqual(DocumentKind.mm0, documentKind("/tmp/a.mm0"));
    try std.testing.expectEqual(DocumentKind.proof, documentKind("/tmp/a.auf"));
    try std.testing.expectEqual(DocumentKind.other, documentKind("/tmp/a.txt"));
}

test "compiler diagnostic severity maps to LSP severity" {
    try std.testing.expectEqual(
        types.DiagnosticSeverity.Error,
        diagnosticSeverityToLsp(mm0.CompilerDiagnosticSeverity.@"error"),
    );
    try std.testing.expectEqual(
        types.DiagnosticSeverity.Warning,
        diagnosticSeverityToLsp(mm0.CompilerDiagnosticSeverity.warning),
    );
}

test "compiler diagnostics filter by source for LSP publishing" {
    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    const allocator = arena_state.allocator();
    const diags = [_]mm0.CompilerDiagnostic{
        .{
            .severity = .warning,
            .kind = .generic,
            .err = error.AmbiguousAcuiMatch,
            .source = .proof,
        },
        .{
            .severity = .warning,
            .kind = .generic,
            .err = error.UnknownTerm,
            .source = .mm0,
        },
    };
    const diag_context: DiagnosticContext = .{
        .mm0 = .{
            .uri = "file:///tmp/test.mm0",
            .text = "",
            .version = 1,
        },
        .proof = .{
            .uri = "file:///tmp/test.auf",
            .text = "",
            .version = 1,
        },
    };
    const proof = try compilerDiagnosticsToLsp(
        allocator,
        diag_context,
        &diags,
        .proof,
        .@"utf-16",
    );
    try std.testing.expectEqual(@as(usize, 1), proof.len);
    try std.testing.expectEqual(
        types.DiagnosticSeverity.Warning,
        proof[0].severity.?,
    );

    const mm0_diags = try compilerDiagnosticsToLsp(
        allocator,
        diag_context,
        &diags,
        .mm0,
        .@"utf-16",
    );
    try std.testing.expectEqual(@as(usize, 1), mm0_diags.len);
    try std.testing.expectEqual(
        types.DiagnosticSeverity.Warning,
        mm0_diags[0].severity.?,
    );
}

test "compiler source diagnostics merge primaries and warnings" {
    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    const allocator = arena_state.allocator();

    const primary = [_]mm0.CompilerDiagnostic{
        .{
            .kind = .generic,
            .err = error.UnknownTerm,
            .source = .mm0,
        },
    };
    const warnings = [_]mm0.CompilerDiagnostic{
        .{
            .severity = .warning,
            .kind = .generic,
            .err = error.AmbiguousAcuiMatch,
            .source = .mm0,
        },
        .{
            .severity = .warning,
            .kind = .generic,
            .err = error.UnknownLabel,
            .source = .proof,
        },
    };
    const extra: mm0.CompilerDiagnostic = .{
        .kind = .generic,
        .err = error.ExpectedIdent,
        .source = .mm0,
    };
    const diag_context: DiagnosticContext = .{
        .mm0 = .{
            .uri = "file:///tmp/test.mm0",
            .text = "",
            .version = 1,
        },
        .proof = .{
            .uri = "file:///tmp/test.auf",
            .text = "",
            .version = 1,
        },
    };

    const diags = try compilerSourceDiagnosticsToLsp(
        allocator,
        diag_context,
        &primary,
        &warnings,
        extra,
        null,
        .mm0,
        .@"utf-16",
    );
    try std.testing.expectEqual(@as(usize, 3), diags.len);
    try std.testing.expectEqual(
        types.DiagnosticSeverity.Error,
        diags[0].severity.?,
    );
    try std.testing.expectEqual(
        types.DiagnosticSeverity.Error,
        diags[1].severity.?,
    );
    try std.testing.expectEqual(
        types.DiagnosticSeverity.Warning,
        diags[2].severity.?,
    );
}

test "compiler source diagnostics append omitted summary" {
    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    const allocator = arena_state.allocator();

    const primary = [_]mm0.CompilerDiagnostic{
        .{
            .kind = .generic,
            .err = error.UnknownTerm,
            .source = .mm0,
        },
    };
    const omitted: mm0.CompilerDiagnostic = .{
        .kind = .omitted_diagnostics,
        .err = error.DiagnosticsOmitted,
        .source = .mm0,
        .detail = .{ .omitted_diagnostics = .{ .count = 17 } },
    };
    const diag_context: DiagnosticContext = .{
        .mm0 = .{
            .uri = "file:///tmp/test.mm0",
            .text = "",
            .version = 1,
        },
    };

    const diags = try compilerSourceDiagnosticsToLsp(
        allocator,
        diag_context,
        &primary,
        &.{},
        null,
        omitted,
        .mm0,
        .@"utf-16",
    );
    try std.testing.expectEqual(@as(usize, 2), diags.len);
    try std.testing.expectEqualStrings(
        "17 more diagnostics omitted",
        diags[1].message,
    );
}

test "compiler diagnostics publish related information" {
    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    const allocator = arena_state.allocator();

    const mm0_text =
        \\provable sort wff;
        \\term top: wff;
        \\theorem first: $ top $;
        \\theorem second: $ top $;
    ;
    const proof_text =
        \\first
        \\-----
        \\l1: $ top $ by second []
    ;

    const rule_start = std.mem.indexOf(u8, mm0_text, "second") orelse {
        return error.MissingNeedle;
    };
    const use_start = std.mem.lastIndexOf(u8, proof_text, "second") orelse {
        return error.MissingNeedle;
    };

    var diag: mm0.CompilerDiagnostic = .{
        .kind = .rule_not_yet_available,
        .err = error.RuleNotYetAvailable,
        .source = .proof,
        .phase = .theorem_application,
        .theorem_name = "first",
        .line_label = "l1",
        .rule_name = "second",
        .span = .{
            .start = use_start,
            .end = use_start + "second".len,
        },
    };
    diag.note_count = 1;
    diag.notes[0] = .{
        .message = .rule_declared_later,
        .source = .mm0,
    };
    diag.related_count = 1;
    diag.related[0] = .{
        .label = .rule_declaration_here,
        .source = .mm0,
        .span = .{
            .start = rule_start,
            .end = rule_start + "second".len,
        },
    };

    const diag_context: DiagnosticContext = .{
        .mm0 = .{
            .uri = "file:///tmp/test.mm0",
            .text = mm0_text,
            .version = 1,
        },
        .proof = .{
            .uri = "file:///tmp/test.auf",
            .text = proof_text,
            .version = 1,
        },
    };

    const lsp_diag = try compilerDiagnosticToLsp(
        allocator,
        diag_context,
        diag,
        .@"utf-16",
    );
    const related = lsp_diag.relatedInformation orelse {
        return error.ExpectedRelatedInformation;
    };
    try std.testing.expectEqual(@as(usize, 1), related.len);
    try std.testing.expectEqualStrings(
        "file:///tmp/test.mm0",
        related[0].location.uri,
    );
    try std.testing.expectEqualStrings(
        "rule declaration is here",
        related[0].message,
    );
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        lsp_diag.message,
        1,
        "phase: theorem application",
    ));
}

test "compiler dependency diagnostics render detail in LSP messages" {
    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    const allocator = arena_state.allocator();

    const proof_text =
        \\rel_bad
        \\-------
        \\l1: $ rel z z $ by rel_ax (x := $ z $, y := $ z $) []
    ;

    const diag_context: DiagnosticContext = .{
        .proof = .{
            .uri = "file:///tmp/test.auf",
            .text = proof_text,
            .version = 1,
        },
    };
    const lsp_diag = try compilerDiagnosticToLsp(
        allocator,
        diag_context,
        .{
            .kind = .generic,
            .err = error.DepViolation,
            .source = .proof,
            .phase = .theorem_application,
            .theorem_name = "rel_bad",
            .line_label = "l1",
            .rule_name = "rel_ax",
            .span = .{ .start = 17, .end = 23 },
            .detail = .{ .dep_violation = .{
                .first_arg_idx = 0,
                .second_arg_idx = 1,
                .first_arg_name = "x",
                .second_arg_name = "y",
                .first_deps = 1,
                .second_deps = 1,
                .first_bound = true,
                .second_bound = true,
                .first_rule_bound = true,
                .second_rule_bound = true,
                .first_binding_text = "z",
                .second_binding_text = "z",
            } },
        },
        .@"utf-16",
    );

    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        lsp_diag.message,
        1,
        "dependency violation: bound variables x and y " ++
            "must be assigned distinct variables",
    ));
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        lsp_diag.message,
        1,
        "x was assigned: z",
    ));
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        lsp_diag.message,
        1,
        "y was assigned: z",
    ));
}

test "compiler dependency diagnostics explain one-sided violations" {
    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    const allocator = arena_state.allocator();

    const proof_text =
        \\gen_bad
        \\-------
        \\l1: $ rel z z $ by gen (x := $ z $, p := $ rel z z $) []
    ;

    const diag_context: DiagnosticContext = .{
        .proof = .{
            .uri = "file:///tmp/test.auf",
            .text = proof_text,
            .version = 1,
        },
    };
    const lsp_diag = try compilerDiagnosticToLsp(
        allocator,
        diag_context,
        .{
            .kind = .generic,
            .err = error.DepViolation,
            .source = .proof,
            .phase = .theorem_application,
            .theorem_name = "gen_bad",
            .line_label = "l1",
            .rule_name = "gen",
            .span = .{ .start = 16, .end = 22 },
            .detail = .{ .dep_violation = .{
                .first_arg_idx = 0,
                .second_arg_idx = 1,
                .first_arg_name = "x",
                .second_arg_name = "p",
                .first_deps = 1,
                .second_deps = 1,
                .first_bound = true,
                .second_bound = false,
                .first_rule_bound = true,
                .second_rule_bound = false,
                .first_binding_text = "z",
                .second_binding_text = "rel z z",
            } },
        },
        .@"utf-16",
    );

    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        lsp_diag.message,
        1,
        "dependency violation: the rule does not allow p " ++
            "to mention the variable assigned to x",
    ));
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        lsp_diag.message,
        1,
        "x was assigned: z",
    ));
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        lsp_diag.message,
        1,
        "p was assigned: rel z z",
    ));
}
