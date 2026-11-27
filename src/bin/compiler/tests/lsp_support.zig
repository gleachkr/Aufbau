const std = @import("std");
const lsp = @import("lsp");
const mm0 = @import("mm0");
const lsp_server = @import("../lsp.zig");
const types = lsp.types.flat;
const CodeActionResult = lsp.ResultType("textDocument/codeAction");
const CodeActionItems = @typeInfo(CodeActionResult).optional.child;
const CodeActionItem = @typeInfo(CodeActionItems).pointer.child;
const Handler = lsp_server.Handler;

pub const TestTransport = struct {
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

    pub fn clearMessages(self: *TestTransport) void {
        self.message_count = 0;
    }

    pub fn containsMessage(self: *const TestTransport, needle: []const u8) bool {
        for (self.messages[0..self.message_count]) |message| {
            if (std.mem.containsAtLeast(u8, message, 1, needle)) {
                return true;
            }
        }
        return false;
    }

    /// Whether an empty diagnostics set was published for `uri`.
    pub fn publishedNone(transport: *const TestTransport, uri: []const u8) bool {
        for (transport.messages[0..transport.message_count]) |message| {
            if (!std.mem.containsAtLeast(u8, message, 1, uri)) continue;
            if (std.mem.containsAtLeast(u8, message, 1, "\"diagnostics\":[]")) {
                return true;
            }
        }
        return false;
    }

    /// Whether a message about `uri` holding `needle` was written.
    pub fn published(
        transport: *const TestTransport,
        uri: []const u8,
        needle: []const u8,
    ) bool {
        for (transport.messages[0..transport.message_count]) |message| {
            if (!std.mem.containsAtLeast(u8, message, 1, uri)) continue;
            if (std.mem.containsAtLeast(u8, message, 1, needle)) return true;
        }
        return false;
    }

    /// The ranges of the last diagnostics set the transport saw for `uri`.
    pub fn publishedRanges(
        transport: *const TestTransport,
        arena: std.mem.Allocator,
        uri: []const u8,
    ) ![]const types.Range {
        const Published = struct {
            params: struct {
                uri: []const u8,
                diagnostics: []const struct { range: types.Range },
            },
        };
        var ranges: ?[]const types.Range = null;
        for (transport.messages[0..transport.message_count]) |message| {
            if (!std.mem.containsAtLeast(u8, message, 1, "publishDiagnostics")) continue;
            const parsed = try std.json.parseFromSliceLeaky(
                Published,
                arena,
                message,
                .{ .ignore_unknown_fields = true },
            );
            if (!std.mem.eql(u8, parsed.params.uri, uri)) continue;
            const out = try arena.alloc(types.Range, parsed.params.diagnostics.len);
            for (parsed.params.diagnostics, out) |diagnostic, *range| range.* = diagnostic.range;
            ranges = out;
        }
        return ranges orelse error.ExpectedDiagnostics;
    }

    pub fn readJsonMessage(
        _: *lsp.Transport,
        _: std.Io,
        _: std.mem.Allocator,
    ) lsp.Transport.ReadError![]u8 {
        return error.EndOfStream;
    }

    pub fn writeJsonMessage(
        transport: *lsp.Transport,
        _: std.Io,
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

/// A handler with the transport it writes to and an arena for requests.
pub const Session = struct {
    transport: TestTransport,
    handler: Handler,
    arena_state: std.heap.ArenaAllocator,

    pub fn init(self: *Session) void {
        self.transport = .{};
        self.handler = Handler.init(
            std.testing.allocator,
            std.testing.io,
            &self.transport.transport,
        );
        self.arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    }

    pub fn deinit(self: *Session) void {
        self.handler.deinit();
        self.arena_state.deinit();
    }

    pub fn arena(self: *Session) std.mem.Allocator {
        return self.arena_state.allocator();
    }

    /// Open the document `uri` with `text`, as a client does.
    pub fn open(self: *Session, uri: []const u8, text: []const u8) !void {
        try self.handler.@"textDocument/didOpen"(self.arena(), .{ .textDocument = .{
            .uri = uri,
            .languageId = .{ .custom_value = "aufbau" },
            .version = 1,
            .text = text,
        } });
    }

    /// The code actions offered at the first `needle` of `text`, the text
    /// of the document `uri`.
    pub fn codeActions(
        self: *Session,
        uri: []const u8,
        text: []const u8,
        needle: []const u8,
    ) ![]const CodeActionItem {
        return expectCodeActionItems(try self.handler.@"textDocument/codeAction"(
            self.arena(),
            try codeActionParamsAt(uri, text, needle),
        ));
    }

    // What the handler keeps, read here and nowhere else in the tests.

    /// The text of the open document at `uri`.
    pub fn documentText(self: *const Session, uri: []const u8) []const u8 {
        return self.handler.docs.get(uri).?.text;
    }

    /// Where the search results kept for `proof_uri` lie; null when none
    /// are kept. Two requests answered from one search see one address.
    pub fn searchResults(self: *const Session, proof_uri: []const u8) ?[*]const Suggestion {
        const entry = self.handler.search_cache.getPtr(proof_uri) orelse return null;
        return entry.suggestions.ptr;
    }

    /// How many markers of `proof_uri` have a search outcome recorded.
    pub fn searchOutcomes(self: *const Session, proof_uri: []const u8) usize {
        const entry = self.handler.search_status.getPtr(proof_uri) orelse return 0;
        return entry.statuses.items.len;
    }

    /// The first search outcome recorded for `proof_uri`.
    pub fn searchOutcome(self: *const Session, proof_uri: []const u8) SearchStatus {
        return self.handler.search_status.getPtr(proof_uri).?.statuses.items[0].status;
    }

    /// Where the joined theory that requests on the root `mm0_uri` read lies.
    pub fn joinedTheory(self: *const Session, mm0_uri: []const u8) *const u8 {
        return &self.handler.nav_cache.get(mm0_uri).?.unit.mm0.joined.text[0];
    }

    /// The text of the theory file `file_uri` that requests on the root
    /// `mm0_uri` read.
    pub fn theoryFileText(self: *const Session, mm0_uri: []const u8, file_uri: []const u8) ![]const u8 {
        for (self.handler.nav_cache.get(mm0_uri).?.unit.mm0.files) |file| {
            if (std.mem.eql(u8, file.uri, file_uri)) return file.text;
        }
        return error.FileNotInUnit;
    }

    /// Leave documents that change pending, as the native server does.
    pub fn analyzeLater(self: *Session) void {
        self.handler.interrupt = .{ .context = self, .stopFn = neverStop };
    }

    pub fn neverStop(_: *anyopaque) bool {
        return false;
    }

    /// The roots with a navigation index.
    pub fn indexedRoots(self: *const Session) usize {
        return self.handler.nav_cache.count();
    }

    /// The proof checks so far: run, replayed from the memo, and kept in it.
    pub fn checks(self: *const Session) Checks {
        const memo = &self.handler.check_memo;
        return .{ .run = memo.misses, .replayed = memo.hits, .kept = memo.entries.count() };
    }

    const Suggestion = mm0.CompilerSupport.Search.SourceSuggestion;
    const SearchStatus = mm0.CompilerSupport.Search.SearchStatus;
    const Checks = struct { run: usize, replayed: usize, kept: usize };
};

pub fn testPosition(text: []const u8, needle: []const u8) !types.Position {
    const offset = std.mem.indexOf(u8, text, needle) orelse {
        return error.MissingNeedle;
    };
    return lsp.offsets.indexToPosition(text, offset, .@"utf-16");
}

pub fn testLastPosition(text: []const u8, needle: []const u8) !types.Position {
    const offset = std.mem.lastIndexOf(u8, text, needle) orelse {
        return error.MissingNeedle;
    };
    return lsp.offsets.indexToPosition(text, offset, .@"utf-16");
}

pub fn expectRangeText(
    text: []const u8,
    range: types.Range,
    expected: []const u8,
) !void {
    const loc = lsp.offsets.rangeToLoc(text, range, .@"utf-16");
    try std.testing.expectEqualStrings(expected, text[loc.start..loc.end]);
}

pub fn expectDefinitionLocation(
    result: lsp.ResultType("textDocument/definition"),
) !types.Location {
    const value = result orelse return error.ExpectedDefinition;
    return switch (value) {
        .definition => |definition| switch (definition) {
            .location => |location| location,
            else => error.ExpectedDefinitionLocation,
        },
        else => error.ExpectedDefinitionLocation,
    };
}

pub fn expectImplementationLocation(
    result: lsp.ResultType("textDocument/implementation"),
) !types.Location {
    const value = result orelse return error.ExpectedImplementation;
    return switch (value) {
        .definition => |definition| switch (definition) {
            .location => |location| location,
            else => error.ExpectedImplementationLocation,
        },
        else => error.ExpectedImplementationLocation,
    };
}

pub fn expectDocumentSymbols(
    result: lsp.ResultType("textDocument/documentSymbol"),
) ![]const types.DocumentSymbol {
    const value = result orelse return error.ExpectedDocumentSymbols;
    return switch (value) {
        .document_symbols => |symbols| symbols,
        else => error.ExpectedDocumentSymbols,
    };
}

pub fn expectCodeActionItems(
    result: CodeActionResult,
) ![]const CodeActionItem {
    return result orelse error.ExpectedCodeActions;
}

pub fn codeActionSingleEdit(
    action: types.CodeAction,
    uri: []const u8,
) ?types.TextEdit {
    const workspace_edit = action.edit orelse return null;
    const changes = workspace_edit.changes orelse return null;
    const edits = changes.map.get(uri) orelse return null;
    if (edits.len != 1) return null;
    return edits[0];
}

pub fn codeActionParamsAt(
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

pub const lsp_navigation_mm0_text =
    \\provable sort wff;
    \\term top: wff;
    \\axiom top_i: $ top $;
    \\axiom keep: $ top $ > $ top $;
    \\theorem main: $ top $ > $ top $;
;

pub const lsp_navigation_proof_text =
    \\main
    \\----
    \\l1: $ top $ by top_i []
    \\l2: $ top $ by keep [l1]
;

pub fn putLspNavigationDocuments(
    handler: *Handler,
    mm0_uri: []const u8,
    proof_uri: []const u8,
) !void {
    try handler.putDocument(mm0_uri, lsp_navigation_mm0_text, 1);
    try handler.putDocument(proof_uri, lsp_navigation_proof_text, 1);
}

pub const lsp_search_mm0_text =
    \\provable sort wff;
    \\term top: wff;
    \\axiom top_i: $ top $;
    \\axiom keep: $ top $ > $ top $;
    \\theorem main: $ top $ > $ top $;
;

pub const lsp_import_lib_text =
    \\provable sort wff;
    \\term top: wff;
    \\axiom top_i: $ top $;
;

pub const lsp_import_main_text =
    \\import "lib.mm0";
    \\theorem main: $ top $;
;

pub const lsp_import_proof_text =
    \\main
    \\----
    \\l1: $ top $ by top_i []
;
