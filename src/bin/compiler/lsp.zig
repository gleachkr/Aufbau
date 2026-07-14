const builtin = @import("builtin");
const build_options = @import("build_options");
const std = @import("std");
const lsp = @import("lsp");
const mm0 = @import("mm0");

const types = lsp.types;
const LspIndex = mm0.Frontend.LspIndex;
const Search = mm0.CompilerSupport.Search;
const lsp_diagnostics = @import("lsp_diagnostics");
const DiagnosticContext = lsp_diagnostics.DiagnosticContext;
const LSP_SERVER_NAME = lsp_diagnostics.SERVER_NAME;
const compilerDiagnosticsToLsp = lsp_diagnostics.compilerDiagnosticsToLsp;
const compilerSourceDiagnosticsToLsp =
    lsp_diagnostics.compilerSourceDiagnosticsToLsp;
const compilerDiagnosticToLsp = lsp_diagnostics.compilerDiagnosticToLsp;
const zeroRange = lsp_diagnostics.zeroRange;
const sourceRangeToLsp = lsp_diagnostics.sourceRangeToLsp;
const sourceRangesToLocations = lsp_diagnostics.sourceRangesToLocations;
const completionsToLsp = lsp_diagnostics.completionsToLsp;
const outlineSymbolsToLsp = lsp_diagnostics.outlineSymbolsToLsp;
const CodeActionResult = lsp.ResultType("textDocument/codeAction");
const CodeActionItems = @typeInfo(CodeActionResult).optional.child;
const CodeActionItem = @typeInfo(CodeActionItems).pointer.child;

const UnsupportedUriScheme = error{UnsupportedUriScheme};
const UnsupportedUriHost = error{UnsupportedUriHost};
const UnsupportedDocument = error{UnsupportedDocument};

const OpenDocument = struct {
    text: []u8,
    version: i32,
};

const LoadedText = struct {
    uri: []const u8,
    text: []const u8,
    version: ?i32,
    mtime: ?i128,
};

const NavigationDocumentState = struct {
    uri: []const u8,
    version: ?i32,
    mtime: ?i128,

    fn eql(
        self: NavigationDocumentState,
        other: NavigationDocumentState,
    ) bool {
        return std.mem.eql(u8, self.uri, other.uri) and
            self.version == other.version and
            self.mtime == other.mtime;
    }

    /// Return a copy whose `uri` is owned by `allocator` (version/mtime are
    /// plain values). Release it with `freeUri`.
    fn dupe(
        self: NavigationDocumentState,
        allocator: std.mem.Allocator,
    ) !NavigationDocumentState {
        return .{
            .uri = try allocator.dupe(u8, self.uri),
            .version = self.version,
            .mtime = self.mtime,
        };
    }

    fn freeUri(self: NavigationDocumentState, allocator: std.mem.Allocator) void {
        allocator.free(self.uri);
    }
};

/// Evict the entry stored under `key` (an owned URI string that aliases the
/// entry's own key), freeing both the value and its key. Shared by every
/// document-keyed cache in this file. `V` must expose `deinit(allocator)`.
fn removeCacheEntry(
    comptime V: type,
    map: *std.StringHashMapUnmanaged(V),
    allocator: std.mem.Allocator,
    key: []const u8,
) void {
    if (map.fetchRemove(key)) |removed| {
        var entry = removed.value;
        entry.deinit(allocator);
    }
}

/// Evict every entry whose `matches(value, uri)` predicate holds. The scan
/// restarts after each removal because removing invalidates the live iterator;
/// the caches hold a handful of entries, so this is not a hot path.
fn invalidateCacheContaining(
    comptime V: type,
    map: *std.StringHashMapUnmanaged(V),
    allocator: std.mem.Allocator,
    uri: []const u8,
    comptime matches: fn (V, []const u8) bool,
) void {
    while (true) {
        var it = map.iterator();
        var found: ?[]const u8 = null;
        while (it.next()) |entry| {
            if (matches(entry.value_ptr.*, uri)) {
                found = entry.key_ptr.*;
                break;
            }
        }
        const key = found orelse break;
        removeCacheEntry(V, map, allocator, key);
    }
}

const NavigationCacheKey = struct {
    mm0: NavigationDocumentState,
    proof: ?NavigationDocumentState,

    fn init(
        allocator: std.mem.Allocator,
        request: NavigationCacheRequest,
    ) !NavigationCacheKey {
        const mm0_state = try request.mm0.dupe(allocator);
        errdefer mm0_state.freeUri(allocator);

        const proof = if (request.proof) |proof_state|
            try proof_state.dupe(allocator)
        else
            null;

        return .{ .mm0 = mm0_state, .proof = proof };
    }

    fn deinit(self: *NavigationCacheKey, allocator: std.mem.Allocator) void {
        self.mm0.freeUri(allocator);
        if (self.proof) |proof| proof.freeUri(allocator);
        self.* = undefined;
    }

    fn eql(
        self: NavigationCacheKey,
        request: NavigationCacheRequest,
    ) bool {
        if (!self.mm0.eql(request.mm0)) return false;
        if (self.proof == null and request.proof == null) return true;
        if (self.proof == null or request.proof == null) return false;
        return self.proof.?.eql(request.proof.?);
    }
};

const NavigationCacheRequest = struct {
    mm0: NavigationDocumentState,
    proof: ?NavigationDocumentState,
};

const NavigationCacheEntry = struct {
    key: NavigationCacheKey,
    snapshot: LspIndex.Snapshot,

    fn deinit(
        self: *NavigationCacheEntry,
        allocator: std.mem.Allocator,
    ) void {
        self.snapshot.deinit();
        self.key.deinit(allocator);
        self.* = undefined;
    }
};

fn navEntryContainsUri(entry: NavigationCacheEntry, uri: []const u8) bool {
    if (std.mem.eql(u8, entry.key.mm0.uri, uri)) return true;
    if (entry.key.proof) |proof| {
        if (std.mem.eql(u8, proof.uri, uri)) return true;
    }
    return false;
}

const NavigationSnapshot = struct {
    snapshot: *const LspIndex.Snapshot,
    document: LspIndex.DocumentId,
};

// Proof-search results (`exact?`/`auto?`/`apply?` code-action suggestions) are
// expensive to compute and editors fire `textDocument/codeAction` repeatedly
// around the same proof step (lightbulb, quick-fix menu, cursor settle/drift).
// This caches the last result per proof document, keyed by both documents'
// states; a single result serves every cursor offset that resolves to the same
// placeholder (the search's `target_span`), so cursor movement within a step
// still hits. A document edit changes its version/mtime, so a stale key never
// matches.
//
// A SearchCacheKey is built borrowed (URIs point into the request arena) for a
// lookup, then `dupe`d into the handler allocator when its result is stored.
// `proof` is the edited document and is always present (unlike the navigation
// cache's optional proof), so no Request/Key split is needed.
const SearchCacheKey = struct {
    mm0: NavigationDocumentState,
    proof: NavigationDocumentState,

    fn dupe(self: SearchCacheKey, allocator: std.mem.Allocator) !SearchCacheKey {
        const mm0_state = try self.mm0.dupe(allocator);
        errdefer mm0_state.freeUri(allocator);
        const proof = try self.proof.dupe(allocator);
        return .{ .mm0 = mm0_state, .proof = proof };
    }

    fn deinit(self: *SearchCacheKey, allocator: std.mem.Allocator) void {
        self.mm0.freeUri(allocator);
        self.proof.freeUri(allocator);
        self.* = undefined;
    }

    fn eql(self: SearchCacheKey, other: SearchCacheKey) bool {
        return self.mm0.eql(other.mm0) and self.proof.eql(other.proof);
    }
};

fn searchEntryContainsUri(entry: SearchCacheEntry, uri: []const u8) bool {
    return std.mem.eql(u8, entry.key.mm0.uri, uri) or
        std.mem.eql(u8, entry.key.proof.uri, uri);
}

const SearchCacheEntry = struct {
    key: SearchCacheKey,
    // The placeholder span these suggestions resolve to: a lookup hits only when
    // the requested offset falls inside it (inclusive), so every offset within
    // one proof step reuses this result.
    target_span: Search.Span,
    // Owned by the handler allocator (deep copies of the arena-allocated search
    // output), so the slices stay valid across requests. An empty slice is a
    // cached "no suggestions" result, which is the most expensive search to repeat.
    suggestions: []Search.SourceSuggestion,

    fn matchesOffset(self: SearchCacheEntry, offset: usize) bool {
        return offset >= self.target_span.start and offset <= self.target_span.end;
    }

    fn deinit(self: *SearchCacheEntry, allocator: std.mem.Allocator) void {
        for (self.suggestions) |suggestion| {
            allocator.free(suggestion.title);
            allocator.free(suggestion.replacement);
        }
        allocator.free(self.suggestions);
        self.key.deinit(allocator);
        self.* = undefined;
    }
};

// The recorded outcome of one placeholder's search, backing that placeholder's
// status diagnostic (info on success, error on failure). Placeholders with no
// recorded outcome publish as a "not yet searched" warning.
const PlaceholderOutcome = struct {
    // The search's catchment span (`SourceSuggestions.target_span`): the whole
    // proof line for a top-level placeholder, the nested application for an
    // inline one. A placeholder is matched to its outcome by span containment.
    target_span: Search.Span,
    status: Search.SearchStatus,
    // Owned by the handler allocator. The first suggestion's replacement text
    // on success, empty otherwise.
    detail: []const u8,
};

// Per-proof-document search outcomes, accumulated across placeholders while
// both documents stay unchanged (unlike the search cache, which keeps only the
// most recent search's suggestions). Keyed by the same document-state pair as
// the search cache: any edit makes the key stale, degrading every recorded
// outcome back to the "not yet searched" warning even if the sweep in
// `invalidateCachesForUri` hasn't freed the entry (e.g. an unopened .mm0
// sibling changing on disk, which never fires a didChange).
const SearchStatusEntry = struct {
    key: SearchCacheKey,
    statuses: std.ArrayListUnmanaged(PlaceholderOutcome),

    fn deinit(self: *SearchStatusEntry, allocator: std.mem.Allocator) void {
        for (self.statuses.items) |outcome| {
            allocator.free(outcome.detail);
        }
        self.statuses.deinit(allocator);
        self.key.deinit(allocator);
        self.* = undefined;
    }
};

fn statusEntryContainsUri(entry: SearchStatusEntry, uri: []const u8) bool {
    return std.mem.eql(u8, entry.key.mm0.uri, uri) or
        std.mem.eql(u8, entry.key.proof.uri, uri);
}

// A placeholder is matched to a recorded outcome by containment in the
// outcome's catchment span (equal spans for a nested placeholder, the
// placeholder within its whole proof line for a top-level one).
fn outcomeForPlaceholder(
    outcomes: []const PlaceholderOutcome,
    span: Search.Span,
) ?*const PlaceholderOutcome {
    for (outcomes) |*outcome| {
        if (span.start >= outcome.target_span.start and
            span.end <= outcome.target_span.end)
        {
            return outcome;
        }
    }
    return null;
}

/// Filter static rule completions through the same conclusion probe as
/// `apply?`. Search locates the ordinary application at `offset` and treats it
/// as an apply target, preserving prior-line checking, local-lemma
/// availability, and inline expected-goal inference.
fn applicableRuleCompletions(
    arena: std.mem.Allocator,
    snapshot: *const LspIndex.Snapshot,
    proof_src: []const u8,
    offset: usize,
    completions: []const LspIndex.CompletionItem,
) ![]const LspIndex.CompletionItem {
    if (completions.len == 0) return completions;

    var suggestions = Search.suggestionsAtSourceOffset(
        arena,
        snapshot.mm0_text,
        proof_src,
        offset,
        .{
            .max_results = completions.len,
            .apply_at_offset = true,
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

    var filtered = std.ArrayListUnmanaged(LspIndex.CompletionItem){};
    for (completions) |item| {
        if (!searchOffersRule(suggestions.items, item.label)) continue;
        try filtered.append(arena, item);
    }
    return try filtered.toOwnedSlice(arena);
}

fn searchOffersRule(
    suggestions: []const Search.SourceSuggestion,
    rule_name: []const u8,
) bool {
    for (suggestions) |suggestion| {
        if (!std.mem.startsWith(u8, suggestion.replacement, rule_name)) {
            continue;
        }
        if (suggestion.replacement.len == rule_name.len) return true;
        if (suggestion.replacement[rule_name.len] == ' ') return true;
    }
    return false;
}

pub const Handler = struct {
    allocator: std.mem.Allocator,
    transport: *lsp.Transport,
    docs: std.StringHashMapUnmanaged(OpenDocument),
    nav_cache: std.StringHashMapUnmanaged(NavigationCacheEntry),
    search_cache: std.StringHashMapUnmanaged(SearchCacheEntry),
    search_status: std.StringHashMapUnmanaged(SearchStatusEntry),
    offset_encoding: lsp.offsets.Encoding,
    snippet_support: bool,

    pub fn init(
        allocator: std.mem.Allocator,
        transport: *lsp.Transport,
    ) Handler {
        return .{
            .allocator = allocator,
            .transport = transport,
            .docs = .empty,
            .nav_cache = .empty,
            .search_cache = .empty,
            .search_status = .empty,
            .offset_encoding = .@"utf-16",
            .snippet_support = false,
        };
    }

    pub fn deinit(self: *Handler) void {
        var it = self.docs.iterator();
        while (it.next()) |entry| {
            self.allocator.free(entry.key_ptr.*);
            self.allocator.free(entry.value_ptr.text);
        }
        self.docs.deinit(self.allocator);

        var cache_it = self.nav_cache.iterator();
        while (cache_it.next()) |entry| {
            entry.value_ptr.deinit(self.allocator);
        }
        self.nav_cache.deinit(self.allocator);

        var search_it = self.search_cache.iterator();
        while (search_it.next()) |entry| {
            entry.value_ptr.deinit(self.allocator);
        }
        self.search_cache.deinit(self.allocator);

        var status_it = self.search_status.iterator();
        while (status_it.next()) |entry| {
            entry.value_ptr.deinit(self.allocator);
        }
        self.search_status.deinit(self.allocator);
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

        self.snippet_support = clientSupportsSnippets(request.capabilities);

        const supports_hierarchical_document_symbols =
            clientSupportsHierarchicalDocumentSymbols(request.capabilities);

        const capabilities: types.ServerCapabilities = .{
            .positionEncoding = switch (self.offset_encoding) {
                .@"utf-8" => .@"utf-8",
                .@"utf-16" => .@"utf-16",
                .@"utf-32" => .@"utf-32",
            },
            .textDocumentSync = .{
                .TextDocumentSyncOptions = .{
                    .openClose = true,
                    .change = .Full,
                },
            },
            .hoverProvider = .{ .bool = true },
            .definitionProvider = .{ .bool = true },
            .implementationProvider = .{ .bool = true },
            .referencesProvider = .{ .bool = true },
            .completionProvider = .{
                .resolveProvider = false,
            },
            .codeActionProvider = .{ .bool = true },
            .documentSymbolProvider = if (supports_hierarchical_document_symbols)
                .{ .bool = true }
            else
                null,
        };

        if (builtin.mode == .Debug) {
            // The validator only understands static capabilities. Validate
            // against the superset of implemented handlers while returning
            // the client-specific capabilities above.
            var validation_capabilities = capabilities;
            validation_capabilities.documentSymbolProvider = .{ .bool = true };
            validation_capabilities.codeActionProvider = .{ .bool = true };
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
        self.invalidateCachesForUri(arena, params.textDocument.uri);
        try self.analyzeUri(arena, params.textDocument.uri);
    }

    pub fn @"textDocument/didChange"(
        self: *Handler,
        arena: std.mem.Allocator,
        params: types.DidChangeTextDocumentParams,
    ) !void {
        const doc = self.docs.getPtr(params.textDocument.uri) orelse return;

        var buffer = std.ArrayListUnmanaged(u8){};
        try buffer.appendSlice(arena, doc.text);

        for (params.contentChanges) |change| {
            switch (change) {
                .literal_0 => |partial| {
                    const loc = lsp.offsets.rangeToLoc(
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
                .literal_1 => |whole| {
                    buffer.clearRetainingCapacity();
                    try buffer.appendSlice(arena, whole.text);
                },
            }
        }

        const new_text = try self.allocator.dupe(u8, buffer.items);
        self.allocator.free(doc.text);
        doc.text = new_text;
        doc.version = params.textDocument.version;

        self.invalidateCachesForUri(arena, params.textDocument.uri);
        try self.analyzeUri(arena, params.textDocument.uri);
    }

    pub fn @"textDocument/didClose"(
        self: *Handler,
        arena: std.mem.Allocator,
        params: types.DidCloseTextDocumentParams,
    ) !void {
        const uri = params.textDocument.uri;
        const path = uriToPath(arena, uri) catch {
            try self.removeDocument(uri);
            try self.clearDiagnostics(arena, uri, null);
            return;
        };
        const kind = documentKind(path);

        self.invalidateCachesForUri(arena, uri);
        try self.removeDocument(uri);
        try self.clearDiagnostics(arena, uri, null);

        switch (kind) {
            .mm0 => {
                const proof_path = siblingPathForMm0(arena, path) catch return;
                const proof_uri = try pathToUri(arena, proof_path);
                if (self.docs.contains(proof_uri)) {
                    try self.analyzeUri(arena, proof_uri);
                }
            },
            .proof => {
                const mm0_path = siblingPathForProof(arena, path) catch return;
                const mm0_uri = try pathToUri(arena, mm0_path);
                if (self.docs.contains(mm0_uri)) {
                    try self.analyzeUri(arena, mm0_uri);
                } else {
                    try self.clearDiagnostics(arena, mm0_uri, null);
                }
            },
            .other => {},
        }
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
        const text = nav.snapshot.textForDocument(nav.document) orelse return null;
        const offset = lsp.offsets.positionToIndex(
            text,
            params.position,
            self.offset_encoding,
        );
        const hover = nav.snapshot.hoverAt(nav.document, offset) orelse return null;
        return .{
            .contents = .{
                .MarkupContent = .{
                    .kind = .markdown,
                    .value = hover.markdown,
                },
            },
            .range = sourceRangeToLsp(
                nav.snapshot,
                hover.range,
                self.offset_encoding,
            ),
        };
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
        const text = nav.snapshot.textForDocument(nav.document) orelse return null;
        const offset = lsp.offsets.positionToIndex(
            text,
            params.position,
            self.offset_encoding,
        );
        var completions = try nav.snapshot.completionsAt(
            arena,
            nav.document,
            offset,
            .{ .snippet_support = self.snippet_support },
        );
        if (nav.document == .proof and
            nav.snapshot.isProofRuleCompletionAt(offset))
        {
            completions = try applicableRuleCompletions(
                arena,
                nav.snapshot,
                text,
                offset,
                completions,
            );
        }
        const items = try completionsToLsp(
            arena,
            nav.snapshot,
            completions,
            self.offset_encoding,
        );
        return .{ .array_of_CompletionItem = items };
    }

    pub fn @"textDocument/codeAction"(
        self: *Handler,
        arena: std.mem.Allocator,
        params: types.CodeActionParams,
    ) !lsp.ResultType("textDocument/codeAction") {
        const path = uriToPath(arena, params.textDocument.uri) catch return null;
        if (documentKind(path) != .proof) return null;
        const proof_loaded = self.loadTextForUriPath(
            arena,
            params.textDocument.uri,
            path,
        ) catch return null;
        const mm0_path = siblingPathForProof(arena, path) catch return null;
        // The cache key only needs the sibling .mm0's state (version/mtime), not
        // its contents, so on a cache hit we avoid reading the (often large,
        // unopened) .mm0 from disk entirely — its text is loaded only on a miss.
        const mm0_state = self.documentStateForPath(arena, mm0_path) catch return null;
        const offset = lsp.offsets.positionToIndex(
            proof_loaded.text,
            params.range.start,
            self.offset_encoding,
        );

        const key: SearchCacheKey = .{
            .mm0 = mm0_state,
            .proof = navigationState(proof_loaded),
        };
        const suggestions = try self.suggestionsForKey(
            arena,
            key,
            offset,
            mm0_path,
            proof_loaded.text,
        ) orelse return null;
        if (suggestions.len == 0) return null;

        const actions = try arena.alloc(CodeActionItem, suggestions.len);
        for (suggestions, 0..) |suggestion, idx| {
            actions[idx] = .{ .CodeAction = try self.searchCodeAction(
                arena,
                params.textDocument.uri,
                proof_loaded.text,
                suggestion,
            ) };
        }
        return actions;
    }

    /// Return the search suggestions for `key` at `offset`, serving the per-proof
    /// cache when the document states match and the offset falls within the cached
    /// result's placeholder span, and recomputing otherwise. The .mm0 contents
    /// (`mm0_path`) are read only on a miss. The returned slice is owned by the
    /// cache entry (handler allocator) and stays valid until the entry is evicted,
    /// which never happens within one request. Returns null only when the search
    /// itself fails (a cached empty result is a non-null empty slice).
    ///
    /// A recomputed search also records its outcome in `search_status` and
    /// re-publishes the proof document's diagnostics, upgrading the target
    /// placeholder's "not yet searched" warning; a cache hit changes nothing,
    /// so it publishes nothing.
    fn suggestionsForKey(
        self: *Handler,
        arena: std.mem.Allocator,
        key: SearchCacheKey,
        offset: usize,
        mm0_path: []const u8,
        proof_src: []const u8,
    ) !?[]const Search.SourceSuggestion {
        if (self.search_cache.getPtr(key.proof.uri)) |entry| {
            if (entry.key.eql(key) and entry.matchesOffset(offset)) {
                return entry.suggestions;
            }
        }

        const mm0_loaded = self.loadTextPreferOpenDocument(arena, mm0_path) catch
            return null;
        const suggestions = Search.suggestionsAtSourceOffset(
            arena,
            mm0_loaded.text,
            proof_src,
            offset,
            // One best proof for the single-proof modes (`exact?`/`auto?`); this
            // also lets `exact?` short-circuit recursive generation once it has a
            // proof. `apply?` keeps the full `max_results` (it lists candidate
            // rules). Grant the generation permit; the keyword under the cursor
            // decides whether recursive generation actually runs.
            .{ .exact_result_limit = 1, .generate = .{ .enabled = true } },
        ) catch |err| switch (err) {
            error.OutOfMemory => return err,
            else => return null,
        };

        // No placeholder at this offset → nothing worth caching (the search
        // already short-circuited cheaply); just hand back the empty result.
        const target_span = suggestions.target_span orelse return suggestions.items;

        // Store under the .mm0 state from the read just performed, so the stored
        // key's mtime matches the contents actually searched (a file changed
        // between the cheap stat and this read self-corrects on the next lookup).
        const store_key: SearchCacheKey = .{
            .mm0 = navigationState(mm0_loaded),
            .proof = key.proof,
        };
        const stored = try self.storeSearchSuggestions(
            store_key,
            target_span,
            suggestions.items,
        );

        // A fresh search just concluded: record its outcome and re-publish the
        // proof document's diagnostics so this placeholder's "not yet searched"
        // warning upgrades to info (success) or error (failure) immediately.
        // Cache hits skip this — their outcome is already recorded.
        try self.recordSearchOutcome(
            store_key,
            target_span,
            suggestions.status,
            if (suggestions.items.len > 0) suggestions.items[0].replacement else "",
        );
        try self.analyzeUri(arena, store_key.proof.uri);
        return stored;
    }

    /// Record the outcome of a freshly-run placeholder search under the
    /// document-state `key`, updating the placeholder's previous outcome in
    /// place (same `target_span`) or appending a new one. A recorded list
    /// whose key no longer matches (either document changed) is dropped and
    /// restarted rather than mixed with outcomes from other document states.
    fn recordSearchOutcome(
        self: *Handler,
        key: SearchCacheKey,
        target_span: Search.Span,
        status: Search.SearchStatus,
        detail: []const u8,
    ) !void {
        const detail_owned = try self.allocator.dupe(u8, detail);
        errdefer self.allocator.free(detail_owned);
        const outcome: PlaceholderOutcome = .{
            .target_span = target_span,
            .status = status,
            .detail = detail_owned,
        };

        if (self.search_status.getPtr(key.proof.uri)) |entry| {
            if (entry.key.eql(key)) {
                for (entry.statuses.items) |*existing| {
                    if (existing.target_span.start == target_span.start and
                        existing.target_span.end == target_span.end)
                    {
                        self.allocator.free(existing.detail);
                        existing.* = outcome;
                        return;
                    }
                }
                try entry.statuses.append(self.allocator, outcome);
                return;
            }
            removeCacheEntry(
                SearchStatusEntry,
                &self.search_status,
                self.allocator,
                key.proof.uri,
            );
        }

        var owned_key = try key.dupe(self.allocator);
        errdefer owned_key.deinit(self.allocator);
        var statuses = std.ArrayListUnmanaged(PlaceholderOutcome){};
        errdefer statuses.deinit(self.allocator);
        try statuses.append(self.allocator, outcome);
        try self.search_status.put(self.allocator, owned_key.proof.uri, .{
            .key = owned_key,
            .statuses = statuses,
        });
    }

    /// Deep-copy `suggestions` (arena-owned) into the handler allocator and store
    /// them in the per-proof search cache, evicting any prior entry. Returns the
    /// stored slice.
    fn storeSearchSuggestions(
        self: *Handler,
        key: SearchCacheKey,
        target_span: Search.Span,
        suggestions: []const Search.SourceSuggestion,
    ) ![]const Search.SourceSuggestion {
        const owned = try self.allocator.alloc(
            Search.SourceSuggestion,
            suggestions.len,
        );
        var filled: usize = 0;
        errdefer {
            for (owned[0..filled]) |suggestion| {
                self.allocator.free(suggestion.title);
                self.allocator.free(suggestion.replacement);
            }
            self.allocator.free(owned);
        }
        for (suggestions, 0..) |suggestion, idx| {
            const title = try self.allocator.dupe(u8, suggestion.title);
            errdefer self.allocator.free(title);
            const replacement = try self.allocator.dupe(u8, suggestion.replacement);
            owned[idx] = .{
                .title = title,
                .replacement = replacement,
                .replace_span = suggestion.replace_span,
            };
            filled = idx + 1;
        }

        var owned_key = try key.dupe(self.allocator);
        errdefer owned_key.deinit(self.allocator);

        self.removeSearchCacheByProofUri(key.proof.uri);
        const cache_key = owned_key.proof.uri;
        try self.search_cache.put(self.allocator, cache_key, .{
            .key = owned_key,
            .target_span = target_span,
            .suggestions = owned,
        });
        return owned;
    }

    fn removeSearchCacheByProofUri(
        self: *Handler,
        proof_uri: []const u8,
    ) void {
        removeCacheEntry(
            SearchCacheEntry,
            &self.search_cache,
            self.allocator,
            proof_uri,
        );
    }

    fn invalidateSearchContainingUri(
        self: *Handler,
        uri: []const u8,
    ) void {
        invalidateCacheContaining(
            SearchCacheEntry,
            &self.search_cache,
            self.allocator,
            uri,
            searchEntryContainsUri,
        );
    }

    fn searchCodeAction(
        self: *Handler,
        arena: std.mem.Allocator,
        uri: []const u8,
        text: []const u8,
        suggestion: Search.SourceSuggestion,
    ) !types.CodeAction {
        const edits = try arena.alloc(types.TextEdit, 1);
        edits[0] = .{
            .range = lsp.offsets.locToRange(
                text,
                .{
                    .start = suggestion.replace_span.start,
                    .end = suggestion.replace_span.end,
                },
                self.offset_encoding,
            ),
            .newText = suggestion.replacement,
        };
        var changes: std.json.ArrayHashMap([]const types.TextEdit) = .{};
        try changes.map.put(arena, uri, edits);
        return .{
            .title = suggestion.title,
            .kind = .quickfix,
            .edit = .{ .changes = changes },
        };
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
            nav.snapshot,
            nav.snapshot.outline(nav.document),
            self.offset_encoding,
        );
        return .{ .array_of_DocumentSymbol = symbols };
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
        const text = nav.snapshot.textForDocument(nav.document) orelse return null;
        const offset = lsp.offsets.positionToIndex(
            text,
            params.position,
            self.offset_encoding,
        );
        const definition = nav.snapshot.definitionAt(
            nav.document,
            offset,
        ) orelse return null;
        return .{
            .Definition = .{
                .Location = .{
                    .uri = definition.uri,
                    .range = sourceRangeToLsp(
                        nav.snapshot,
                        definition.selection_range,
                        self.offset_encoding,
                    ),
                },
            },
        };
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
        const text = nav.snapshot.textForDocument(nav.document) orelse return null;
        const offset = lsp.offsets.positionToIndex(
            text,
            params.position,
            self.offset_encoding,
        );
        const implementation = nav.snapshot.implementationAt(
            nav.document,
            offset,
        ) orelse return null;
        return .{
            .Definition = .{
                .Location = .{
                    .uri = implementation.uri,
                    .range = sourceRangeToLsp(
                        nav.snapshot,
                        implementation.selection_range,
                        self.offset_encoding,
                    ),
                },
            },
        };
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
        const text = nav.snapshot.textForDocument(nav.document) orelse return null;
        const offset = lsp.offsets.positionToIndex(
            text,
            params.position,
            self.offset_encoding,
        );
        const ranges = try nav.snapshot.referencesAt(
            arena,
            nav.document,
            offset,
            params.context.includeDeclaration,
        );
        return try sourceRangesToLocations(
            arena,
            nav.snapshot,
            ranges,
            self.offset_encoding,
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

    fn analyzeUri(
        self: *Handler,
        arena: std.mem.Allocator,
        uri: []const u8,
    ) !void {
        const doc = self.docs.get(uri) orelse return;
        const path = uriToPath(arena, uri) catch |err| {
            try self.publishMessageDiagnostic(
                arena,
                uri,
                doc.version,
                doc.text,
                switch (err) {
                    error.InvalidFormat => "document URI is not a valid URI",
                    UnsupportedUriScheme.UnsupportedUriScheme => "document URI must use the file scheme",
                    UnsupportedUriHost.UnsupportedUriHost => "file URI host must be empty or localhost",
                    else => @errorName(err),
                },
            );
            return;
        };

        switch (documentKind(path)) {
            .mm0 => try self.analyzeMm0Document(
                arena,
                uri,
                doc.version,
                doc.text,
                path,
            ),
            .proof => try self.analyzeProofDocument(
                arena,
                uri,
                doc.version,
                doc.text,
                path,
            ),
            .other => try self.clearDiagnostics(arena, uri, doc.version),
        }
    }

    fn analyzeMm0Document(
        self: *Handler,
        arena: std.mem.Allocator,
        uri: []const u8,
        version: i32,
        text: []const u8,
        path: []const u8,
    ) !void {
        if (siblingPathForMm0(arena, path)) |proof_path| {
            const proof_uri = try pathToUri(arena, proof_path);
            if (self.docs.get(proof_uri)) |proof_doc| {
                try self.analyzeProofDocument(
                    arena,
                    proof_uri,
                    proof_doc.version,
                    proof_doc.text,
                    proof_path,
                );
                return;
            }
        } else |_| {}

        const diag_context: DiagnosticContext = .{
            .mm0 = .{
                .uri = uri,
                .text = text,
                .version = version,
            },
        };

        var compiler = mm0.Compiler.init(arena, text);
        compiler.analyzeMm0() catch |err| {
            if (compiler.diagnostics.last_diagnostic != null or
                compiler.primaryDiagnostics().len != 0 or
                compiler.warningDiagnostics().len != 0)
            {
                try self.publishCompilerSourceDiagnostics(
                    arena,
                    diag_context,
                    compiler.primaryDiagnostics(),
                    compiler.warningDiagnostics(),
                    compiler.diagnostics.last_diagnostic,
                    compiler.omittedPrimaryDiagnostic(.mm0),
                    .mm0,
                    &.{},
                );
            } else {
                try self.publishMessageDiagnostic(
                    arena,
                    uri,
                    version,
                    text,
                    @errorName(err),
                );
            }
            return;
        };
        try self.publishCompilerSourceDiagnostics(
            arena,
            diag_context,
            compiler.primaryDiagnostics(),
            compiler.warningDiagnostics(),
            null,
            compiler.omittedPrimaryDiagnostic(.mm0),
            .mm0,
            &.{},
        );
    }

    fn analyzeProofDocument(
        self: *Handler,
        arena: std.mem.Allocator,
        proof_uri: []const u8,
        proof_version: i32,
        proof_text: []const u8,
        proof_path: []const u8,
    ) !void {
        const mm0_path = siblingPathForProof(arena, proof_path) catch {
            try self.publishMessageDiagnostic(
                arena,
                proof_uri,
                proof_version,
                proof_text,
                "proof files must end in .auf",
            );
            return;
        };
        const mm0_loaded = self.loadTextPreferOpenDocument(arena, mm0_path) catch |err| {
            const message = switch (err) {
                error.FileNotFound => "could not find sibling .mm0 file for this proof",
                else => try std.fmt.allocPrint(
                    arena,
                    "could not read sibling .mm0 file: {s}",
                    .{@errorName(err)},
                ),
            };
            try self.publishMessageDiagnostic(
                arena,
                proof_uri,
                proof_version,
                proof_text,
                message,
            );
            const mm0_uri = try pathToUri(arena, mm0_path);
            try self.clearDiagnostics(arena, mm0_uri, null);
            return;
        };

        const diag_context: DiagnosticContext = .{
            .mm0 = .{
                .uri = mm0_loaded.uri,
                .text = mm0_loaded.text,
                .version = mm0_loaded.version,
            },
            .proof = .{
                .uri = proof_uri,
                .text = proof_text,
                .version = proof_version,
            },
        };

        // One status diagnostic per search placeholder (warning until searched,
        // then info/error from the recorded outcome), published together with
        // the compiler diagnostics: publishDiagnostics replaces the full set
        // per document, so they must go out in the same payload.
        const search_diagnostics = try self.searchStatusDiagnostics(
            arena,
            proof_uri,
            proof_version,
            proof_text,
            navigationState(mm0_loaded),
        );

        var compiler = mm0.Compiler.initWithProof(
            arena,
            mm0_loaded.text,
            proof_text,
        );
        compiler.allow_search_placeholders = true;
        compiler.analyze() catch |err| {
            if (compiler.diagnostics.last_diagnostic != null or
                compiler.primaryDiagnostics().len != 0 or
                compiler.warningDiagnostics().len != 0)
            {
                try self.publishProofAndMm0Diagnostics(
                    arena,
                    diag_context,
                    compiler.primaryDiagnostics(),
                    compiler.warningDiagnostics(),
                    compiler.diagnostics.last_diagnostic,
                    compiler.omittedPrimaryDiagnostic(.proof),
                    compiler.omittedPrimaryDiagnostic(.mm0),
                    search_diagnostics,
                );
            } else {
                try self.publishMessageDiagnostic(
                    arena,
                    proof_uri,
                    proof_version,
                    proof_text,
                    @errorName(err),
                );
                try self.clearDiagnostics(
                    arena,
                    mm0_loaded.uri,
                    mm0_loaded.version,
                );
            }
            return;
        };

        try self.publishProofAndMm0Diagnostics(
            arena,
            diag_context,
            compiler.primaryDiagnostics(),
            compiler.warningDiagnostics(),
            compiler.diagnostics.last_diagnostic,
            compiler.omittedPrimaryDiagnostic(.proof),
            compiler.omittedPrimaryDiagnostic(.mm0),
            search_diagnostics,
        );
    }

    /// Build one LSP diagnostic per search placeholder in the proof document:
    /// info for a recorded successful search, error for a recorded failure
    /// (with the reason), warning for a placeholder not searched since the
    /// documents last changed. Outcomes are keyed by both documents' states,
    /// so anything stale silently degrades to the warning. These are built
    /// directly as LSP diagnostics (not compiler diagnostics): search status
    /// is an editor-session concept the compile pipeline never produces.
    fn searchStatusDiagnostics(
        self: *Handler,
        arena: std.mem.Allocator,
        proof_uri: []const u8,
        proof_version: i32,
        proof_text: []const u8,
        mm0_state: NavigationDocumentState,
    ) ![]const types.Diagnostic {
        const placeholders = try Search.searchPlaceholders(arena, proof_text);
        if (placeholders.len == 0) return &.{};

        const current_key: SearchCacheKey = .{
            .mm0 = mm0_state,
            .proof = .{
                .uri = proof_uri,
                .version = proof_version,
                .mtime = null,
            },
        };
        var outcomes: []const PlaceholderOutcome = &.{};
        if (self.search_status.getPtr(proof_uri)) |entry| {
            if (entry.key.eql(current_key)) outcomes = entry.statuses.items;
        }

        const diagnostics = try arena.alloc(
            types.Diagnostic,
            placeholders.len,
        );
        for (placeholders, diagnostics) |placeholder, *diagnostic| {
            const keyword = placeholder.kind.keyword();
            var severity: types.DiagnosticSeverity = .Warning;
            var message: []const u8 = try std.fmt.allocPrint(
                arena,
                "{s} placeholder: search not yet run " ++
                    "(request code actions here to search)",
                .{keyword},
            );
            if (outcomeForPlaceholder(outcomes, placeholder.span)) |outcome| {
                switch (outcome.status) {
                    .found => {
                        severity = .Information;
                        message = try std.fmt.allocPrint(
                            arena,
                            "{s} search succeeded: {s}",
                            .{ keyword, outcome.detail },
                        );
                    },
                    .miss => {
                        severity = .Error;
                        message = try std.fmt.allocPrint(
                            arena,
                            "{s} search failed: no proof found",
                            .{keyword},
                        );
                    },
                    .budget_exhausted => {
                        severity = .Error;
                        message = try std.fmt.allocPrint(
                            arena,
                            "{s} search failed: budget exhausted before " ++
                                "the search completed (a proof may still exist)",
                            .{keyword},
                        );
                    },
                }
            }
            diagnostic.* = .{
                .range = lsp.offsets.locToRange(
                    proof_text,
                    .{
                        .start = placeholder.span.start,
                        .end = placeholder.span.end,
                    },
                    self.offset_encoding,
                ),
                .severity = severity,
                .source = LSP_SERVER_NAME,
                .message = message,
            };
        }
        return diagnostics;
    }

    fn loadTextPreferOpenDocument(
        self: *Handler,
        arena: std.mem.Allocator,
        path: []const u8,
    ) !LoadedText {
        const uri = try pathToUri(arena, path);
        return try self.loadTextForUriPath(arena, uri, path);
    }

    fn loadTextForUriPath(
        self: *Handler,
        arena: std.mem.Allocator,
        uri: []const u8,
        path: []const u8,
    ) !LoadedText {
        if (self.docs.get(uri)) |doc| {
            return .{
                .uri = uri,
                .text = doc.text,
                .version = doc.version,
                .mtime = null,
            };
        }

        const disk = try readFileWithMtimeAlloc(arena, path);
        return .{
            .uri = uri,
            .text = disk.text,
            .version = null,
            .mtime = disk.mtime,
        };
    }

    fn navigationState(loaded: LoadedText) NavigationDocumentState {
        return .{
            .uri = loaded.uri,
            .version = loaded.version,
            .mtime = loaded.mtime,
        };
    }

    /// The document state (uri/version/mtime) for `path` WITHOUT reading its
    /// contents: an open document contributes its version, a closed one its disk
    /// mtime via a cheap stat. Mirrors `loadTextForUriPath`'s state fields exactly,
    /// so a key built from this matches one built from a later full load of the
    /// unchanged file.
    fn documentStateForPath(
        self: *Handler,
        arena: std.mem.Allocator,
        path: []const u8,
    ) !NavigationDocumentState {
        const uri = try pathToUri(arena, path);
        if (self.docs.get(uri)) |doc| {
            return .{ .uri = uri, .version = doc.version, .mtime = null };
        }
        return .{ .uri = uri, .version = null, .mtime = try statMtimeAlloc(path) };
    }

    fn navigationSnapshotForUri(
        self: *Handler,
        arena: std.mem.Allocator,
        uri: []const u8,
    ) !?NavigationSnapshot {
        const path = uriToPath(arena, uri) catch return null;
        return switch (documentKind(path)) {
            .mm0 => try self.navigationSnapshotForMm0(arena, uri, path),
            .proof => try self.navigationSnapshotForProof(arena, uri, path),
            .other => null,
        };
    }

    fn navigationSnapshotForMm0(
        self: *Handler,
        arena: std.mem.Allocator,
        uri: []const u8,
        path: []const u8,
    ) !?NavigationSnapshot {
        const mm0_loaded = self.loadTextForUriPath(arena, uri, path) catch {
            return null;
        };
        var proof_state: ?NavigationDocumentState = null;
        var proof_uri: ?[]const u8 = null;
        var proof_text: ?[]const u8 = null;

        if (siblingPathForMm0(arena, path)) |proof_path| {
            const expected_uri = try pathToUri(arena, proof_path);
            proof_state = .{
                .uri = expected_uri,
                .version = null,
                .mtime = null,
            };
            if (self.loadTextForUriPath(
                arena,
                expected_uri,
                proof_path,
            )) |proof| {
                proof_state = navigationState(proof);
                proof_uri = proof.uri;
                proof_text = proof.text;
            } else |_| {}
        } else |_| {}

        return try self.navigationSnapshotForRequest(
            .{
                .mm0 = navigationState(mm0_loaded),
                .proof = proof_state,
            },
            .{
                .mm0_uri = mm0_loaded.uri,
                .mm0_text = mm0_loaded.text,
                .proof_uri = proof_uri,
                .proof_text = proof_text,
            },
            .mm0,
        );
    }

    fn navigationSnapshotForProof(
        self: *Handler,
        arena: std.mem.Allocator,
        uri: []const u8,
        path: []const u8,
    ) !?NavigationSnapshot {
        const proof_loaded = self.loadTextForUriPath(arena, uri, path) catch {
            return null;
        };
        const mm0_path = siblingPathForProof(arena, path) catch return null;
        const mm0_loaded = self.loadTextPreferOpenDocument(arena, mm0_path) catch {
            return null;
        };

        return try self.navigationSnapshotForRequest(
            .{
                .mm0 = navigationState(mm0_loaded),
                .proof = navigationState(proof_loaded),
            },
            .{
                .mm0_uri = mm0_loaded.uri,
                .mm0_text = mm0_loaded.text,
                .proof_uri = proof_loaded.uri,
                .proof_text = proof_loaded.text,
            },
            .proof,
        );
    }

    fn navigationSnapshotForRequest(
        self: *Handler,
        request: NavigationCacheRequest,
        input: LspIndex.SnapshotInput,
        document: LspIndex.DocumentId,
    ) !NavigationSnapshot {
        if (self.nav_cache.getPtr(request.mm0.uri)) |entry| {
            if (entry.key.eql(request)) {
                return .{
                    .snapshot = &entry.snapshot,
                    .document = document,
                };
            }
        }

        self.removeNavigationCacheByMm0Uri(request.mm0.uri);

        var snapshot = try LspIndex.Snapshot.build(self.allocator, input);
        errdefer snapshot.deinit();

        var key = try NavigationCacheKey.init(self.allocator, request);
        errdefer key.deinit(self.allocator);

        const cache_key = key.mm0.uri;
        try self.nav_cache.put(self.allocator, cache_key, .{
            .key = key,
            .snapshot = snapshot,
        });

        const entry = self.nav_cache.getPtr(cache_key).?;
        return .{
            .snapshot = &entry.snapshot,
            .document = document,
        };
    }

    fn removeNavigationCacheByMm0Uri(
        self: *Handler,
        mm0_uri: []const u8,
    ) void {
        removeCacheEntry(
            NavigationCacheEntry,
            &self.nav_cache,
            self.allocator,
            mm0_uri,
        );
    }

    /// Single invalidation chokepoint for every document-keyed cache, called from
    /// didOpen/didChange/didClose. New caches hook their sweep in here.
    fn invalidateCachesForUri(
        self: *Handler,
        arena: std.mem.Allocator,
        uri: []const u8,
    ) void {
        // A stale search-cache key never matches (its version/mtime differ), but
        // free the memory promptly on edit/close rather than waiting for the next
        // search on the same proof to evict it. Same for the recorded search
        // outcomes: dropping them returns the document's placeholders to the
        // "not yet searched" warning.
        self.invalidateSearchContainingUri(uri);
        invalidateCacheContaining(
            SearchStatusEntry,
            &self.search_status,
            self.allocator,
            uri,
            statusEntryContainsUri,
        );
        const path = uriToPath(arena, uri) catch {
            self.invalidateNavigationContainingUri(uri);
            return;
        };

        switch (documentKind(path)) {
            .mm0 => self.removeNavigationCacheByMm0Uri(uri),
            .proof => {
                if (siblingPathForProof(arena, path)) |mm0_path| {
                    if (pathToUri(arena, mm0_path)) |mm0_uri| {
                        self.removeNavigationCacheByMm0Uri(mm0_uri);
                    } else |_| {}
                } else |_| {}
            },
            .other => {},
        }
        self.invalidateNavigationContainingUri(uri);
    }

    fn invalidateNavigationContainingUri(
        self: *Handler,
        uri: []const u8,
    ) void {
        invalidateCacheContaining(
            NavigationCacheEntry,
            &self.nav_cache,
            self.allocator,
            uri,
            navEntryContainsUri,
        );
    }

    fn publishProofAndMm0Diagnostics(
        self: *Handler,
        arena: std.mem.Allocator,
        diag_context: DiagnosticContext,
        primary: []const mm0.CompilerDiagnostic,
        warnings: []const mm0.CompilerDiagnostic,
        extra: ?mm0.CompilerDiagnostic,
        proof_omitted: ?mm0.CompilerDiagnostic,
        mm0_omitted: ?mm0.CompilerDiagnostic,
        proof_extra_lsp: []const types.Diagnostic,
    ) !void {
        try self.publishCompilerSourceDiagnostics(
            arena,
            diag_context,
            primary,
            warnings,
            extra,
            proof_omitted,
            .proof,
            proof_extra_lsp,
        );
        try self.publishCompilerSourceDiagnostics(
            arena,
            diag_context,
            primary,
            warnings,
            extra,
            mm0_omitted,
            .mm0,
            &.{},
        );
    }

    fn publishCompilerDiagnostic(
        self: *Handler,
        arena: std.mem.Allocator,
        diag_context: DiagnosticContext,
        diag: mm0.CompilerDiagnostic,
    ) !void {
        const doc = diag_context.sourceDocument(diag.source) orelse return;
        const diagnostics = try arena.alloc(types.Diagnostic, 1);
        diagnostics[0] = try compilerDiagnosticToLsp(
            arena,
            diag_context,
            diag,
            self.offset_encoding,
        );
        try self.publishDiagnostics(
            arena,
            doc.uri,
            doc.version,
            diagnostics,
        );
    }

    fn publishCompilerWarnings(
        self: *Handler,
        arena: std.mem.Allocator,
        diag_context: DiagnosticContext,
        diags: []const mm0.CompilerDiagnostic,
        source: mm0.CompilerDiagnosticSource,
    ) !void {
        const doc = diag_context.sourceDocument(source) orelse return;
        const diagnostics = try compilerDiagnosticsToLsp(
            arena,
            diag_context,
            diags,
            source,
            self.offset_encoding,
        );
        if (diagnostics.len == 0) {
            try self.clearDiagnostics(arena, doc.uri, doc.version);
            return;
        }
        try self.publishDiagnostics(
            arena,
            doc.uri,
            doc.version,
            diagnostics,
        );
    }

    fn publishCompilerSourceDiagnostics(
        self: *Handler,
        arena: std.mem.Allocator,
        diag_context: DiagnosticContext,
        primary: []const mm0.CompilerDiagnostic,
        warnings: []const mm0.CompilerDiagnostic,
        extra: ?mm0.CompilerDiagnostic,
        omitted: ?mm0.CompilerDiagnostic,
        source: mm0.CompilerDiagnosticSource,
        extra_lsp: []const types.Diagnostic,
    ) !void {
        const doc = diag_context.sourceDocument(source) orelse return;
        const diagnostics = try compilerSourceDiagnosticsToLsp(
            arena,
            diag_context,
            primary,
            warnings,
            extra,
            omitted,
            source,
            self.offset_encoding,
        );
        const all = if (extra_lsp.len == 0) diagnostics else merged: {
            const merged = try arena.alloc(
                types.Diagnostic,
                diagnostics.len + extra_lsp.len,
            );
            @memcpy(merged[0..diagnostics.len], diagnostics);
            @memcpy(merged[diagnostics.len..], extra_lsp);
            break :merged merged;
        };
        if (all.len == 0) {
            try self.clearDiagnostics(arena, doc.uri, doc.version);
            return;
        }
        try self.publishDiagnostics(
            arena,
            doc.uri,
            doc.version,
            all,
        );
    }

    fn publishMessageDiagnostic(
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
            .message = message,
        };
        try self.publishDiagnostics(arena, uri, version, diagnostics);
    }

    fn clearDiagnostics(
        self: *Handler,
        arena: std.mem.Allocator,
        uri: []const u8,
        version: ?i32,
    ) !void {
        try self.publishDiagnostics(arena, uri, version, &.{});
    }

    fn publishDiagnostics(
        self: *Handler,
        arena: std.mem.Allocator,
        uri: []const u8,
        version: ?i32,
        diagnostics: []const types.Diagnostic,
    ) !void {
        try self.transport.writeNotification(
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
};

pub const DocumentKind = enum {
    mm0,
    proof,
    other,
};

pub fn run(allocator: std.mem.Allocator) !void {
    var read_buffer: [4096]u8 = undefined;
    var stdio_transport = lsp.Transport.Stdio.init(
        &read_buffer,
        .stdin(),
        .stdout(),
    );
    const transport: *lsp.Transport = &stdio_transport.transport;

    var handler = Handler.init(allocator, transport);
    defer handler.deinit();

    try lsp.basic_server.run(
        allocator,
        transport,
        &handler,
        std.log.err,
    );
}

pub fn uriToPath(
    allocator: std.mem.Allocator,
    uri_text: []const u8,
) ![]const u8 {
    const uri = try std.Uri.parse(uri_text);
    if (!std.mem.eql(u8, uri.scheme, "file")) {
        return UnsupportedUriScheme.UnsupportedUriScheme;
    }
    if (uri.host) |host| {
        const host_text = try host.toRawMaybeAlloc(allocator);
        if (host_text.len != 0 and
            !std.mem.eql(u8, host_text, "localhost"))
        {
            return UnsupportedUriHost.UnsupportedUriHost;
        }
    }
    return try uri.path.toRawMaybeAlloc(allocator);
}

pub fn pathToUri(
    allocator: std.mem.Allocator,
    path: []const u8,
) ![]const u8 {
    return try std.fmt.allocPrint(
        allocator,
        "file://{f}",
        .{std.fmt.alt(std.Uri.Component{ .raw = path }, .formatPath)},
    );
}

pub fn siblingPathForProof(
    allocator: std.mem.Allocator,
    proof_path: []const u8,
) ![]const u8 {
    if (!std.mem.endsWith(u8, proof_path, ".auf")) {
        return UnsupportedDocument.UnsupportedDocument;
    }
    return try std.fmt.allocPrint(
        allocator,
        "{s}.mm0",
        .{proof_path[0 .. proof_path.len - 4]},
    );
}

pub fn siblingPathForMm0(
    allocator: std.mem.Allocator,
    mm0_path: []const u8,
) ![]const u8 {
    if (!std.mem.endsWith(u8, mm0_path, ".mm0")) {
        return UnsupportedDocument.UnsupportedDocument;
    }
    return try std.fmt.allocPrint(
        allocator,
        "{s}.auf",
        .{mm0_path[0 .. mm0_path.len - 4]},
    );
}

pub fn documentKind(path: []const u8) DocumentKind {
    if (std.mem.endsWith(u8, path, ".mm0")) return .mm0;
    if (std.mem.endsWith(u8, path, ".auf")) return .proof;
    return .other;
}

const ReadFileWithMtime = struct {
    text: []u8,
    mtime: i128,
};

fn readFileWithMtimeAlloc(
    allocator: std.mem.Allocator,
    path: []const u8,
) !ReadFileWithMtime {
    if (builtin.os.tag == .freestanding) {
        return error.FileNotFound;
    } else {
        const file = if (std.fs.path.isAbsolute(path))
            try std.fs.openFileAbsolute(path, .{})
        else
            try std.fs.cwd().openFile(path, .{});
        defer file.close();

        const stat = try file.stat();
        return .{
            .text = try file.readToEndAlloc(
                allocator,
                std.math.maxInt(usize),
            ),
            .mtime = stat.mtime,
        };
    }
}

fn readFileAlloc(
    allocator: std.mem.Allocator,
    path: []const u8,
) ![]u8 {
    return (try readFileWithMtimeAlloc(allocator, path)).text;
}

/// The mtime of `path` without reading its contents — used to build a search
/// cache key cheaply on a hit. Reports the same mtime as `readFileWithMtimeAlloc`
/// for an unchanged file (both stat the same opened handle).
fn statMtimeAlloc(path: []const u8) !i128 {
    if (builtin.os.tag == .freestanding) {
        return error.FileNotFound;
    } else {
        const file = if (std.fs.path.isAbsolute(path))
            try std.fs.openFileAbsolute(path, .{})
        else
            try std.fs.cwd().openFile(path, .{});
        defer file.close();
        const stat = try file.stat();
        return stat.mtime;
    }
}

fn clientSupportsSnippets(capabilities: types.ClientCapabilities) bool {
    const text_document = capabilities.textDocument orelse return false;
    const completion = text_document.completion orelse return false;
    const item = completion.completionItem orelse return false;
    return item.snippetSupport orelse false;
}

fn clientSupportsHierarchicalDocumentSymbols(
    capabilities: types.ClientCapabilities,
) bool {
    const text_document = capabilities.textDocument orelse return false;
    const document_symbol = text_document.documentSymbol orelse return false;
    return document_symbol.hierarchicalDocumentSymbolSupport orelse false;
}
