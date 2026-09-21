const builtin = @import("builtin");
const build_options = @import("build_options");
const std = @import("std");
const lsp = @import("lsp");
const mm0 = @import("mm0");

const types = lsp.types;
const LspIndex = mm0.Frontend.LspIndex;
const Search = mm0.CompilerSupport.Search;
const Unpack = mm0.CompilerSupport.Unpack;
const Imports = mm0.Imports;
const lsp_diagnostics = @import("lsp_diagnostics");
const DiagnosticContext = lsp_diagnostics.DiagnosticContext;
const LocatedDiagnostic = lsp_diagnostics.LocatedDiagnostic;
const LSP_SERVER_NAME = lsp_diagnostics.SERVER_NAME;
const zeroRange = lsp_diagnostics.zeroRange;
const sourceRangesToLocations = lsp_diagnostics.sourceRangesToLocations;
const completionsToLsp = lsp_diagnostics.completionsToLsp;
const outlineSymbolsToLsp = lsp_diagnostics.outlineSymbolsToLsp;
const CodeActionResult = lsp.ResultType("textDocument/codeAction");

/// `Diagnostic.code` on everything `searchStatusDiagnostics` builds. These are
/// the only diagnostics the compile pipeline does not also produce, so a client
/// that runs its own compile (the browser editor does) needs a way to pick them
/// out of a `publishDiagnostics` set and merge just those.
const SEARCH_STATUS_CODE = "search-status";
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

/// One file of an analysis unit: an open document (with its version) or a
/// file read from disk (with its mtime), keyed by its path.
const UnitFile = struct {
    uri: []const u8,
    path: []const u8,
    text: []const u8,
    version: ?i32,
    mtime: ?i128,

    fn state(self: UnitFile) NavigationDocumentState {
        return .{ .uri = self.uri, .version = self.version, .mtime = self.mtime };
    }
};

/// A span of a joined text resolved to the file it was copied from.
const UnitLocation = struct {
    file: UnitFile,
    span: Search.Span,
};

/// One side of a unit (`.mm0` or `.auf`): its files, joined in post-order.
const UnitSide = struct {
    joined: Imports.Joined,
    /// Parallel to `joined.files`.
    files: []const UnitFile,
    /// Index of the root file in `files`.
    root: usize,

    fn rootFile(self: UnitSide) UnitFile {
        return self.files[self.root];
    }

    fn fileIndex(self: UnitSide, uri: []const u8) ?usize {
        for (self.files, 0..) |file, index| {
            if (std.mem.eql(u8, file.uri, uri)) return index;
        }
        return null;
    }

    /// The joined offset of a position in one file, or null inside an
    /// import/include statement (the joined text does not contain those).
    fn joinedOffset(self: UnitSide, file_index: usize, offset: usize) ?usize {
        return self.joined.map.joinedOffset(file_index, offset);
    }

    fn locate(self: UnitSide, span: Search.Span) ?UnitLocation {
        const hit = self.joined.map.locateSpan(.{
            .start = span.start,
            .end = span.end,
        }) orelse return null;
        return .{
            .file = self.files[hit.file_index],
            .span = .{ .start = hit.span.start, .end = hit.span.end },
        };
    }
};

/// An import/include that could not be followed: a diagnostic on the file
/// holding the statement.
const UnitFailure = struct {
    file: UnitFile,
    span: Search.Span,
    message: []const u8,
};

/// What one analysis or navigation request works on: the root `.mm0`
/// joined with its imports and, when the root has a proof file, the paired
/// `.auf` files joined with their includes — the same texts `abc compile`
/// sees. The compiler and the index run over the joined texts; spans map
/// back to files through `locate`, positions in a file map forward through
/// `UnitSide.joinedOffset`. A document without imports is passed through,
/// so both maps are the identity for it.
const Unit = struct {
    mm0: UnitSide,
    proof: ?UnitSide,
    failures: []const UnitFailure,

    const Found = struct {
        document: LspIndex.DocumentId,
        file_index: usize,
    };

    fn side(self: *const Unit, document: LspIndex.DocumentId) ?*const UnitSide {
        return switch (document) {
            .mm0 => &self.mm0,
            .proof => if (self.proof) |*proof| proof else null,
        };
    }

    fn find(self: *const Unit, uri: []const u8) ?Found {
        if (self.mm0.fileIndex(uri)) |index| {
            return .{ .document = .mm0, .file_index = index };
        }
        if (self.proof) |proof| {
            if (proof.fileIndex(uri)) |index| {
                return .{ .document = .proof, .file_index = index };
            }
        }
        return null;
    }

    fn isRootUri(self: *const Unit, uri: []const u8) bool {
        if (std.mem.eql(u8, self.mm0.rootFile().uri, uri)) return true;
        if (self.proof) |proof| {
            if (std.mem.eql(u8, proof.rootFile().uri, uri)) return true;
        }
        return false;
    }

    /// The document states of every file, `.mm0` side then proof side:
    /// the cache key for anything computed from the unit.
    fn states(
        self: *const Unit,
        allocator: std.mem.Allocator,
    ) ![]NavigationDocumentState {
        const proof_len = if (self.proof) |proof| proof.files.len else 0;
        const out = try allocator.alloc(
            NavigationDocumentState,
            self.mm0.files.len + proof_len,
        );
        var index: usize = 0;
        for (self.mm0.files) |file| {
            out[index] = file.state();
            index += 1;
        }
        if (self.proof) |proof| {
            for (proof.files) |file| {
                out[index] = file.state();
                index += 1;
            }
        }
        return out;
    }

    fn diagnosticContext(self: *const Unit) DiagnosticContext {
        return .{
            .mm0 = diagnosticDocument(self.mm0.rootFile()),
            .proof = if (self.proof) |proof|
                diagnosticDocument(proof.rootFile())
            else
                null,
            .locator = .{ .ctx = @ptrCast(self), .locateFn = locateSpan },
        };
    }

    fn rangeLocator(self: *const Unit) lsp_diagnostics.RangeLocator {
        return .{ .ctx = @ptrCast(self), .locateFn = locateRange };
    }

    fn diagnosticDocument(file: UnitFile) lsp_diagnostics.DiagnosticDocument {
        return .{ .uri = file.uri, .text = file.text, .version = file.version };
    }

    fn locateSpan(
        ctx: *const anyopaque,
        source: mm0.CompilerDiagnosticSource,
        span: lsp_diagnostics.Span,
    ) ?lsp_diagnostics.LocatedSpan {
        const self: *const Unit = @ptrCast(@alignCast(ctx));
        const document: LspIndex.DocumentId = switch (source) {
            .mm0 => .mm0,
            .proof => .proof,
        };
        const unit_side = self.side(document) orelse return null;
        const hit = unit_side.locate(.{
            .start = span.start,
            .end = span.end,
        }) orelse return null;
        return .{
            .uri = hit.file.uri,
            .text = hit.file.text,
            .version = hit.file.version,
            .span = .{ .start = hit.span.start, .end = hit.span.end },
        };
    }

    fn locateRange(
        ctx: *const anyopaque,
        range: LspIndex.SourceRange,
    ) ?lsp_diagnostics.LocatedRange {
        const self: *const Unit = @ptrCast(@alignCast(ctx));
        const unit_side = self.side(range.document) orelse return null;
        const hit = unit_side.locate(.{
            .start = range.start,
            .end = range.end,
        }) orelse return null;
        return .{
            .uri = hit.file.uri,
            .text = hit.file.text,
            .span = .{ .start = hit.span.start, .end = hit.span.end },
        };
    }
};

/// The states of every file a unit was built from, owned by the handler
/// allocator. Every cache below is keyed by one: an edit to any file of the
/// unit (a version bump for an open document, an mtime change on disk)
/// makes a stored key stale.
const UnitKey = struct {
    states: []NavigationDocumentState,

    fn init(
        allocator: std.mem.Allocator,
        states: []const NavigationDocumentState,
    ) !UnitKey {
        const owned = try allocator.alloc(NavigationDocumentState, states.len);
        var filled: usize = 0;
        errdefer {
            for (owned[0..filled]) |state| state.freeUri(allocator);
            allocator.free(owned);
        }
        for (states, 0..) |state, index| {
            owned[index] = try state.dupe(allocator);
            filled = index + 1;
        }
        return .{ .states = owned };
    }

    fn deinit(self: *UnitKey, allocator: std.mem.Allocator) void {
        for (self.states) |state| state.freeUri(allocator);
        allocator.free(self.states);
        self.* = undefined;
    }

    fn eql(self: UnitKey, states: []const NavigationDocumentState) bool {
        if (self.states.len != states.len) return false;
        for (self.states, states) |mine, other| {
            if (!mine.eql(other)) return false;
        }
        return true;
    }

    fn containsUri(self: UnitKey, uri: []const u8) bool {
        for (self.states) |state| {
            if (std.mem.eql(u8, state.uri, uri)) return true;
        }
        return false;
    }
};

const NavigationCacheEntry = struct {
    /// The root `.mm0` URI; aliases the map key.
    uri: []const u8,
    key: UnitKey,
    /// Backs `unit`: its joined texts and file records.
    unit_arena: std.heap.ArenaAllocator,
    unit: Unit,
    snapshot: LspIndex.Snapshot,

    fn deinit(
        self: *NavigationCacheEntry,
        allocator: std.mem.Allocator,
    ) void {
        self.snapshot.deinit();
        self.unit_arena.deinit();
        self.key.deinit(allocator);
        allocator.free(self.uri);
        self.* = undefined;
    }
};

fn navEntryContainsUri(entry: NavigationCacheEntry, uri: []const u8) bool {
    return entry.key.containsUri(uri);
}

/// A navigation request's view of its unit: the index over the joined
/// texts plus which file of the unit the request document is.
const NavigationSnapshot = struct {
    snapshot: *const LspIndex.Snapshot,
    unit: *const Unit,
    document: LspIndex.DocumentId,
    file_index: usize,

    fn side(self: NavigationSnapshot) *const UnitSide {
        return self.unit.side(self.document).?;
    }

    fn file(self: NavigationSnapshot) UnitFile {
        return self.side().files[self.file_index];
    }

    /// The joined offset of an editor position in the request document,
    /// or null when it sits inside an import/include statement.
    fn joinedPosition(
        self: NavigationSnapshot,
        position: types.Position,
        encoding: lsp.offsets.Encoding,
    ) ?usize {
        const offset = lsp.offsets.positionToIndex(
            self.file().text,
            position,
            encoding,
        );
        return self.side().joinedOffset(self.file_index, offset);
    }
};

/// What an analysis of one root touched: the other files it read (so the
/// root is re-analysed when one of them changes) and the closed files it
/// published diagnostics for (so those are cleared when they drop out).
const UnitRecord = struct {
    deps: []const []const u8,
    published: []const []const u8,

    fn deinit(self: *UnitRecord, allocator: std.mem.Allocator) void {
        freeUriList(allocator, self.deps);
        freeUriList(allocator, self.published);
        self.* = undefined;
    }
};

fn dupeUriList(
    allocator: std.mem.Allocator,
    uris: []const []const u8,
) ![]const []const u8 {
    const owned = try allocator.alloc([]const u8, uris.len);
    var filled: usize = 0;
    errdefer freeUriList(allocator, owned[0..filled]);
    for (uris, 0..) |uri, index| {
        owned[index] = try allocator.dupe(u8, uri);
        filled = index + 1;
    }
    return owned;
}

fn freeUriList(allocator: std.mem.Allocator, uris: []const []const u8) void {
    for (uris) |uri| allocator.free(uri);
    allocator.free(uris);
}

fn uriListContains(uris: []const []const u8, uri: []const u8) bool {
    for (uris) |candidate| {
        if (std.mem.eql(u8, candidate, uri)) return true;
    }
    return false;
}

// Proof-search results (`exact?`/`auto?`/`apply?` code-action suggestions) are
// expensive to compute and editors fire `textDocument/codeAction` repeatedly
// around the same proof step (lightbulb, quick-fix menu, cursor settle/drift).
// This caches the last result per proof document, keyed by the states of
// every file of the unit; a single result serves every cursor offset that
// resolves to the same placeholder (the search's `target_span`), so cursor
// movement within a step still hits. A document edit changes its
// version/mtime, so a stale key never matches.
const SearchCacheEntry = struct {
    /// The root proof URI; aliases the map key.
    uri: []const u8,
    key: UnitKey,
    // The placeholder span (in the joined proof text) these suggestions
    // resolve to: a lookup hits only when the requested offset falls inside
    // it (inclusive), so every offset within one proof step reuses this
    // result.
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
        allocator.free(self.uri);
        self.* = undefined;
    }
};

fn searchEntryContainsUri(entry: SearchCacheEntry, uri: []const u8) bool {
    return entry.key.containsUri(uri);
}

// The recorded outcome of one placeholder's search, backing that placeholder's
// status diagnostic (info on success, error on failure). Placeholders with no
// recorded outcome publish as a "not yet searched" warning.
const PlaceholderOutcome = struct {
    // The search's catchment span (`SourceSuggestions.target_span`, in the
    // joined proof text): the whole proof line for a top-level placeholder,
    // the nested application for an inline one. A placeholder is matched to
    // its outcome by span containment.
    target_span: Search.Span,
    status: Search.SearchStatus,
    // Owned by the handler allocator. The first suggestion's replacement text
    // on success, empty otherwise.
    detail: []const u8,
};

// Per-proof-document search outcomes, accumulated across placeholders while
// every file of the unit stays unchanged (unlike the search cache, which
// keeps only the most recent search's suggestions). Keyed like the search
// cache: any edit makes the key stale, degrading every recorded outcome back
// to the "not yet searched" warning even if the sweep in
// `invalidateCachesForUri` hasn't freed the entry (e.g. an unopened file
// changing on disk, which never fires a didChange).
const SearchStatusEntry = struct {
    /// The root proof URI; aliases the map key.
    uri: []const u8,
    key: UnitKey,
    statuses: std.ArrayListUnmanaged(PlaceholderOutcome),

    fn deinit(self: *SearchStatusEntry, allocator: std.mem.Allocator) void {
        for (self.statuses.items) |outcome| {
            allocator.free(outcome.detail);
        }
        self.statuses.deinit(allocator);
        self.key.deinit(allocator);
        allocator.free(self.uri);
        self.* = undefined;
    }
};

fn statusEntryContainsUri(entry: SearchStatusEntry, uri: []const u8) bool {
    return entry.key.containsUri(uri);
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
    // Every tactic is exempt from the filter below, so a list holding nothing
    // else cannot lose an entry — and the search that would decide it costs
    // tens of milliseconds on a large proof, once per keystroke. This is the
    // list you get while typing a placeholder, which is exactly when the
    // reader is typing fastest.
    if (allSearchTactics(completions)) return completions;

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
    /// What the last analysis of each root document read and published,
    /// keyed by the analysed URI (owned).
    units: std.StringHashMapUnmanaged(UnitRecord),
    /// Proof-block check outcomes shared by every analysis this handler
    /// runs, so an edit re-checks only what it can affect.
    check_memo: mm0.CheckMemo,
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
            .units = .empty,
            .check_memo = mm0.CheckMemo.init(allocator),
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

        var units_it = self.units.iterator();
        while (units_it.next()) |entry| {
            self.allocator.free(entry.key_ptr.*);
            entry.value_ptr.deinit(self.allocator);
        }
        self.units.deinit(self.allocator);
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
        try self.analyzeDependents(arena, params.textDocument.uri);
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
        try self.analyzeDependents(arena, params.textDocument.uri);
    }

    pub fn @"textDocument/didClose"(
        self: *Handler,
        arena: std.mem.Allocator,
        params: types.DidCloseTextDocumentParams,
    ) !void {
        const uri = params.textDocument.uri;
        self.invalidateCachesForUri(arena, uri);
        try self.removeDocument(uri);
        try self.clearDiagnostics(arena, uri, null);
        try self.forgetUnit(arena, uri);

        if (uriToPath(arena, uri)) |path| {
            switch (documentKind(path)) {
                .mm0 => if (siblingPathForMm0(arena, path)) |proof_path| {
                    const proof_uri = try pathToUri(arena, proof_path);
                    if (self.docs.contains(proof_uri)) {
                        try self.analyzeUri(arena, proof_uri);
                    }
                } else |_| {},
                .proof => if (siblingPathForProof(arena, path)) |mm0_path| {
                    const mm0_uri = try pathToUri(arena, mm0_path);
                    if (self.docs.contains(mm0_uri)) {
                        try self.analyzeUri(arena, mm0_uri);
                    } else {
                        try self.clearDiagnostics(arena, mm0_uri, null);
                    }
                } else |_| {},
                .other => {},
            }
        } else |_| {}

        // The file may still exist on disk, so roots that import or include
        // it re-analyse against that copy.
        try self.analyzeDependents(arena, uri);
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
        const hover = nav.snapshot.hoverAt(nav.document, offset) orelse return null;
        return .{
            .contents = .{
                .MarkupContent = .{
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
            nav.snapshot.isProofRuleCompletionAt(offset))
        {
            completions = try applicableRuleCompletions(
                arena,
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
        return .{ .CompletionList = .{
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

        var actions = std.ArrayListUnmanaged(CodeActionItem){};
        if (try self.suggestionsForUnit(arena, nav, offset)) |suggestions| {
            for (suggestions) |suggestion| {
                const action = try self.searchCodeAction(
                    arena,
                    nav,
                    suggestion,
                ) orelse continue;
                try actions.append(arena, .{ .CodeAction = action });
            }
        }
        if (try self.unpackCodeAction(arena, nav, offset)) |action| {
            try actions.append(arena, .{ .CodeAction = action });
        }
        if (actions.items.len == 0) return null;
        return try actions.toOwnedSlice(arena);
    }

    /// Offer the `unpack` rewrite when the cursor sits on a checked proof
    /// line containing inline rule applications. The parse-only `hasTargetAt`
    /// gate keeps the common case (no inline application under the cursor)
    /// free of the two compile passes the full rewrite performs.
    fn unpackCodeAction(
        self: *Handler,
        arena: std.mem.Allocator,
        nav: NavigationSnapshot,
        offset: usize,
    ) !?types.CodeAction {
        const proof_side = nav.side();
        const proof_text = proof_side.joined.text;
        if (!Unpack.hasTargetAt(arena, proof_text, offset)) return null;
        const suggestion = Unpack.unpackAtSourceOffset(
            arena,
            nav.unit.mm0.joined.text,
            proof_text,
            offset,
        ) catch |err| switch (err) {
            error.OutOfMemory => return err,
        } orelse return null;

        return try self.replacementCodeAction(
            arena,
            proof_side.*,
            suggestion.title,
            .@"refactor.rewrite",
            suggestion.replace_span,
            suggestion.replacement,
        );
    }

    /// A code action replacing `span` of the joined proof text with
    /// `replacement`, addressed to the file the span lies in.
    fn replacementCodeAction(
        self: *Handler,
        arena: std.mem.Allocator,
        proof_side: UnitSide,
        title: []const u8,
        kind: types.CodeActionKind,
        span: Search.Span,
        replacement: []const u8,
    ) !?types.CodeAction {
        const hit = proof_side.locate(span) orelse return null;
        const edits = try arena.alloc(types.TextEdit, 1);
        edits[0] = .{
            .range = lsp.offsets.locToRange(
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
        };
    }

    /// Return the search suggestions for the unit at `offset` (in the joined
    /// proof text), serving the per-proof cache when every file's state
    /// matches and the offset falls within the cached result's placeholder
    /// span, and recomputing otherwise. The returned slice is owned by the
    /// cache entry (handler allocator) and stays valid until the entry is
    /// evicted, which never happens within one request. Returns null only
    /// when the search itself fails (a cached empty result is a non-null
    /// empty slice).
    ///
    /// A recomputed search also records its outcome in `search_status` and
    /// re-publishes the proof document's diagnostics, upgrading the target
    /// placeholder's "not yet searched" warning; a cache hit changes nothing,
    /// so it publishes nothing.
    fn suggestionsForUnit(
        self: *Handler,
        arena: std.mem.Allocator,
        nav: NavigationSnapshot,
        offset: usize,
    ) !?[]const Search.SourceSuggestion {
        const proof_side = nav.side();
        const proof_uri = proof_side.rootFile().uri;
        const states = try nav.unit.states(arena);
        if (self.search_cache.getPtr(proof_uri)) |entry| {
            if (entry.key.eql(states) and entry.matchesOffset(offset)) {
                return entry.suggestions;
            }
        }

        const suggestions = Search.suggestionsAtSourceOffset(
            arena,
            nav.unit.mm0.joined.text,
            proof_side.joined.text,
            offset,
            // One best proof for the single-proof modes (`exact?`/`auto?`); this
            // also lets `exact?` short-circuit recursive generation once it has a
            // proof. `apply?` keeps the full `max_results` (it lists candidate
            // rules). Grant the generation permit; the keyword under the cursor
            // decides whether recursive generation actually runs. `status_detail`
            // asks for the human-readable failure elaboration the placeholder
            // diagnostics surface.
            .{
                .exact_result_limit = 1,
                .generate = .{ .enabled = true },
                .status_detail = true,
            },
        ) catch |err| switch (err) {
            error.OutOfMemory => return err,
            else => return null,
        };

        // No placeholder at this offset → nothing worth caching (the search
        // already short-circuited cheaply); just hand back the empty result.
        const target_span = suggestions.target_span orelse return suggestions.items;

        const stored = try self.storeSearchSuggestions(
            proof_uri,
            states,
            target_span,
            suggestions.items,
        );

        // A fresh search just concluded: record its outcome and re-publish the
        // proof document's diagnostics so this placeholder's "not yet searched"
        // warning upgrades to info (success) or error (failure) immediately.
        // Cache hits skip this — their outcome is already recorded.
        try self.recordSearchOutcome(
            proof_uri,
            states,
            target_span,
            suggestions.status,
            if (suggestions.items.len > 0)
                suggestions.items[0].replacement
            else
                suggestions.status_detail orelse "",
        );
        try self.analyzeUri(arena, proof_uri);
        return stored;
    }

    /// Record the outcome of a freshly-run placeholder search under the
    /// unit's document states, updating the placeholder's previous outcome
    /// in place (same `target_span`) or appending a new one. A recorded list
    /// whose key no longer matches (any file changed) is dropped and
    /// restarted rather than mixed with outcomes from other document states.
    fn recordSearchOutcome(
        self: *Handler,
        proof_uri: []const u8,
        states: []const NavigationDocumentState,
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

        if (self.search_status.getPtr(proof_uri)) |entry| {
            if (entry.key.eql(states)) {
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
                proof_uri,
            );
        }

        var owned_key = try UnitKey.init(self.allocator, states);
        errdefer owned_key.deinit(self.allocator);
        const owned_uri = try self.allocator.dupe(u8, proof_uri);
        errdefer self.allocator.free(owned_uri);
        var statuses = std.ArrayListUnmanaged(PlaceholderOutcome){};
        errdefer statuses.deinit(self.allocator);
        try statuses.append(self.allocator, outcome);
        try self.search_status.put(self.allocator, owned_uri, .{
            .uri = owned_uri,
            .key = owned_key,
            .statuses = statuses,
        });
    }

    /// Deep-copy `suggestions` (arena-owned) into the handler allocator and store
    /// them in the per-proof search cache, evicting any prior entry. Returns the
    /// stored slice.
    fn storeSearchSuggestions(
        self: *Handler,
        proof_uri: []const u8,
        states: []const NavigationDocumentState,
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

        var owned_key = try UnitKey.init(self.allocator, states);
        errdefer owned_key.deinit(self.allocator);
        const owned_uri = try self.allocator.dupe(u8, proof_uri);
        errdefer self.allocator.free(owned_uri);

        self.removeSearchCacheByProofUri(proof_uri);
        try self.search_cache.put(self.allocator, owned_uri, .{
            .uri = owned_uri,
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
        const offset = nav.joinedPosition(
            params.position,
            self.offset_encoding,
        ) orelse return null;
        const definition = nav.snapshot.definitionAt(
            nav.document,
            offset,
        ) orelse return null;
        const location = nav.unit.rangeLocator().toLocation(
            definition.selection_range,
            self.offset_encoding,
        ) orelse return null;
        return .{ .Definition = .{ .Location = location } };
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
            implementation.selection_range,
            self.offset_encoding,
        ) orelse return null;
        return .{ .Definition = .{ .Location = location } };
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
                    else => mm0.compilerErrorSummary(err),
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

    /// Re-analyse every open root whose last analysis read `uri` (as an
    /// import, an include, or a paired proof file of an import).
    fn analyzeDependents(
        self: *Handler,
        arena: std.mem.Allocator,
        uri: []const u8,
    ) !void {
        const roots = try self.dependentRoots(arena, uri);
        for (roots) |root| {
            if (std.mem.eql(u8, root, uri)) continue;
            if (!self.docs.contains(root)) continue;
            try self.analyzeUri(arena, root);
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

        const unit = try self.buildUnit(
            arena,
            .{ .uri = uri, .text = text, .version = version, .mtime = null },
            path,
            null,
            null,
        );

        var compiler = mm0.Compiler.init(arena, unit.mm0.joined.text);
        compiler.analyzeMm0() catch |err| {
            if (hasDiagnostics(&compiler)) {
                try self.publishUnitDiagnostics(
                    arena,
                    uri,
                    &unit,
                    compiler.primaryDiagnostics(),
                    compiler.warningDiagnostics(),
                    compiler.diagnostics.last_diagnostic,
                    null,
                    compiler.omittedPrimaryDiagnostic(.mm0),
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
        try self.publishUnitDiagnostics(
            arena,
            uri,
            &unit,
            compiler.primaryDiagnostics(),
            compiler.warningDiagnostics(),
            null,
            null,
            compiler.omittedPrimaryDiagnostic(.mm0),
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
            // A proof file without a theory of its own that some root
            // includes: that root's analysis reports on it.
            if (err == error.FileNotFound and self.isDependency(proof_uri)) return;
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

        const unit = try self.buildUnit(
            arena,
            mm0_loaded,
            mm0_path,
            .{
                .uri = proof_uri,
                .text = proof_text,
                .version = proof_version,
                .mtime = null,
            },
            proof_path,
        );
        const states = try unit.states(arena);

        // One status diagnostic per search placeholder (warning until searched,
        // then info/error from the recorded outcome), published together with
        // the compiler diagnostics: publishDiagnostics replaces the full set
        // per document, so they must go out in the same payload.
        const search_diagnostics = try self.searchStatusDiagnostics(
            arena,
            &unit,
            states,
        );

        var compiler = mm0.Compiler.initWithProof(
            arena,
            unit.mm0.joined.text,
            unit.proof.?.joined.text,
        );
        compiler.allow_search_placeholders = true;
        compiler.check_memo = &self.check_memo;
        compiler.analyze() catch |err| {
            if (hasDiagnostics(&compiler)) {
                try self.publishUnitDiagnostics(
                    arena,
                    proof_uri,
                    &unit,
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

        try self.publishUnitDiagnostics(
            arena,
            proof_uri,
            &unit,
            compiler.primaryDiagnostics(),
            compiler.warningDiagnostics(),
            null,
            compiler.omittedPrimaryDiagnostic(.proof),
            compiler.omittedPrimaryDiagnostic(.mm0),
            search_diagnostics,
        );
    }

    fn hasDiagnostics(compiler: *const mm0.Compiler) bool {
        return compiler.diagnostics.last_diagnostic != null or
            compiler.primaryDiagnostics().len != 0 or
            compiler.warningDiagnostics().len != 0;
    }

    fn searchStatusDiagnostics(
        self: *Handler,
        arena: std.mem.Allocator,
        unit: *const Unit,
        states: []const NavigationDocumentState,
    ) ![]const LocatedDiagnostic {
        const proof_side = unit.proof orelse return &.{};
        const proof_text = proof_side.joined.text;
        const placeholders = try Search.searchPlaceholders(arena, proof_text);
        if (placeholders.len == 0) return &.{};

        var outcomes: []const PlaceholderOutcome = &.{};
        if (self.search_status.getPtr(proof_side.rootFile().uri)) |entry| {
            if (entry.key.eql(states)) outcomes = entry.statuses.items;
        }

        var diagnostics = std.ArrayListUnmanaged(LocatedDiagnostic){};
        for (placeholders) |placeholder| {
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
                    .miss, .budget_exhausted => {
                        severity = .Error;
                        // The recorded detail elaborates the failure (which
                        // bound truncated the search, how far it got, what
                        // to tune); fall back to the generic wording for
                        // outcomes recorded without one.
                        const fallback: []const u8 =
                            if (outcome.status == .miss)
                                "no proof found"
                            else
                                "budget exhausted before the search " ++
                                    "completed (a proof may still exist)";
                        message = try std.fmt.allocPrint(
                            arena,
                            "{s} search failed: {s}",
                            .{
                                keyword,
                                if (outcome.detail.len > 0)
                                    outcome.detail
                                else
                                    fallback,
                            },
                        );
                    },
                }
            }
            try self.appendLocated(
                arena,
                &diagnostics,
                proof_side,
                placeholder.span,
                severity,
                message,
            );
            // Per-parameter validation (typo'd names, out-of-range values,
            // parameters on a non-auto? placeholder): one error diagnostic
            // per rejected entry, underlining the offending token. These
            // never block the search — invalid entries are simply not
            // applied — so the author sees the problem while the valid
            // parameters still work.
            const issues = try Search.tunables.validateSearchParams(
                arena,
                placeholder.kind.paramContext(),
                placeholder.params,
            );
            for (issues) |issue| {
                try self.appendLocated(
                    arena,
                    &diagnostics,
                    proof_side,
                    issue.span,
                    .Error,
                    issue.message,
                );
            }
        }
        return try diagnostics.toOwnedSlice(arena);
    }

    /// A search-status diagnostic for `span` of the joined proof text, on
    /// the file the span lies in.
    fn appendLocated(
        self: *Handler,
        arena: std.mem.Allocator,
        diagnostics: *std.ArrayListUnmanaged(LocatedDiagnostic),
        proof_side: UnitSide,
        span: Search.Span,
        severity: types.DiagnosticSeverity,
        message: []const u8,
    ) !void {
        const hit = proof_side.locate(span) orelse return;
        try diagnostics.append(arena, .{
            .uri = hit.file.uri,
            .version = hit.file.version,
            .diagnostic = .{
                .range = lsp.offsets.locToRange(
                    hit.file.text,
                    .{ .start = hit.span.start, .end = hit.span.end },
                    self.offset_encoding,
                ),
                .severity = severity,
                .source = LSP_SERVER_NAME,
                .code = .{ .string = SEARCH_STATUS_CODE },
                .message = message,
            },
        });
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

    /// The file at `path` as a unit file: an open document first (unsaved
    /// edits count), else the disk copy unless `open_only`. Null when there
    /// is neither. Text and names are copied into `arena`, so a unit never
    /// aliases the document store.
    fn resolveUnitFile(
        self: *Handler,
        arena: std.mem.Allocator,
        path: []const u8,
        open_only: bool,
    ) !?UnitFile {
        const uri = try pathToUri(arena, path);
        if (self.docs.get(uri)) |doc| {
            return .{
                .uri = uri,
                .path = try arena.dupe(u8, path),
                .text = try arena.dupe(u8, doc.text),
                .version = doc.version,
                .mtime = null,
            };
        }
        if (open_only) return null;
        const disk = readFileWithMtimeAlloc(arena, path) catch |err| {
            // On wasm there is no disk; the read reports FileNotFound.
            if (err == error.OutOfMemory) return error.OutOfMemory;
            return null;
        };
        return .{
            .uri = uri,
            .path = try arena.dupe(u8, path),
            .text = disk.text,
            .version = null,
            .mtime = disk.mtime,
        };
    }

    /// Does `path` name an open document or a readable file?
    fn pathExists(self: *Handler, arena: std.mem.Allocator, path: []const u8) bool {
        const uri = pathToUri(arena, path) catch return false;
        if (self.docs.contains(uri)) return true;
        _ = statMtimeAlloc(path) catch return false;
        return true;
    }

    /// Does the open document at `uri` report its own diagnostics (a `.mm0`
    /// file, or a `.auf` file with a sibling theory)? A root's analysis
    /// leaves such files alone; it publishes for closed files and for
    /// library proof files that have no analysis of their own.
    fn ownsDiagnostics(
        self: *Handler,
        arena: std.mem.Allocator,
        uri: []const u8,
    ) bool {
        if (!self.docs.contains(uri)) return false;
        const path = uriToPath(arena, uri) catch return true;
        return switch (documentKind(path)) {
            .mm0, .other => true,
            .proof => blk: {
                const mm0_path = siblingPathForProof(arena, path) catch
                    break :blk true;
                break :blk self.pathExists(arena, mm0_path);
            },
        };
    }

    /// Join a root `.mm0` with its imports and, when `proof` is given, the
    /// paired `.auf` files with their includes. A join that fails (a
    /// missing file, a cycle, a malformed statement) degrades that side to
    /// the root alone with its statements blanked, and records the failure
    /// as a diagnostic on the file holding the statement. Everything the
    /// unit references is allocated from `arena`.
    fn buildUnit(
        self: *Handler,
        arena: std.mem.Allocator,
        mm0_loaded: LoadedText,
        mm0_path: []const u8,
        proof_loaded: ?LoadedText,
        proof_path: ?[]const u8,
    ) !Unit {
        var loader = UnitLoader{ .handler = self, .arena = arena };
        var failures = std.ArrayListUnmanaged(UnitFailure){};

        const mm0_root = try unitFileFrom(arena, mm0_loaded, mm0_path);
        try loader.put(mm0_root);
        var failure: ?Imports.JoinFailure = null;
        const mm0_joined = Imports.join(
            arena,
            loader.resolver(),
            mm0_root.path,
            mm0_root.text,
            &failure,
        ) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            else => blk: {
                try recordJoinFailure(arena, &loader, &failures, failure);
                break :blk try Imports.single(
                    arena,
                    mm0_root.path,
                    try Imports.blankStatements(arena, .mm0, mm0_root.text),
                );
            },
        };
        const mm0_side: UnitSide = .{
            .joined = mm0_joined,
            .files = try loader.filesFor(mm0_joined),
            .root = indexOfKey(mm0_joined, mm0_root.path),
        };

        var proof_side: ?UnitSide = null;
        if (proof_loaded) |loaded| {
            const proof_root = try unitFileFrom(arena, loaded, proof_path.?);
            try loader.put(proof_root);
            // Every joined `.mm0` pairs with its `<stem>.auf` sibling when
            // one exists, in the same order; the root pairs with the given
            // proof file.
            var roots = std.ArrayListUnmanaged(Imports.File){};
            for (mm0_joined.files) |file| {
                if (std.mem.eql(u8, file.key, mm0_root.path)) {
                    try roots.append(arena, .{
                        .key = proof_root.path,
                        .text = proof_root.text,
                    });
                    continue;
                }
                const sibling = siblingPathForMm0(arena, file.key) catch continue;
                const paired = try loader.load(sibling, false) orelse continue;
                try roots.append(arena, .{ .key = paired.path, .text = paired.text });
            }
            failure = null;
            const proof_joined = Imports.joinAll(
                arena,
                loader.resolver(),
                .auf,
                roots.items,
                &failure,
            ) catch |err| switch (err) {
                error.OutOfMemory => return error.OutOfMemory,
                else => blk: {
                    try recordJoinFailure(arena, &loader, &failures, failure);
                    break :blk try Imports.single(
                        arena,
                        proof_root.path,
                        try Imports.blankStatements(arena, .auf, proof_root.text),
                    );
                },
            };
            proof_side = .{
                .joined = proof_joined,
                .files = try loader.filesFor(proof_joined),
                .root = indexOfKey(proof_joined, proof_root.path),
            };
        }

        return .{
            .mm0 = mm0_side,
            .proof = proof_side,
            .failures = try failures.toOwnedSlice(arena),
        };
    }

    fn unitFileFrom(
        arena: std.mem.Allocator,
        loaded: LoadedText,
        path: []const u8,
    ) !UnitFile {
        return .{
            .uri = try arena.dupe(u8, loaded.uri),
            .path = try arena.dupe(u8, path),
            .text = try arena.dupe(u8, loaded.text),
            .version = loaded.version,
            .mtime = loaded.mtime,
        };
    }

    fn indexOfKey(joined: Imports.Joined, key: []const u8) usize {
        for (joined.files, 0..) |file, index| {
            if (std.mem.eql(u8, file.key, key)) return index;
        }
        unreachable;
    }

    fn recordJoinFailure(
        arena: std.mem.Allocator,
        loader: *UnitLoader,
        failures: *std.ArrayListUnmanaged(UnitFailure),
        failure: ?Imports.JoinFailure,
    ) !void {
        const info = failure orelse return;
        const keyword = info.syntax.keyword();
        const message = switch (info.kind) {
            .cycle => try std.fmt.allocPrint(
                arena,
                "{s} cycle: '{s}' is already being {s}d",
                .{ keyword, info.spec, keyword },
            ),
            .unresolved => try std.fmt.allocPrint(
                arena,
                "unable to {s} '{s}': {s}",
                .{
                    keyword,
                    info.spec,
                    if (info.err) |err| @errorName(err) else "unresolved",
                },
            ),
            .malformed => try std.fmt.allocPrint(
                arena,
                "malformed {s} statement",
                .{keyword},
            ),
        };
        // The statement's file was loaded before its statements were
        // followed, so it is always on record.
        const file = loader.files.get(info.file_key) orelse return;
        try failures.append(arena, .{
            .file = file,
            .span = .{ .start = info.span.start, .end = info.span.end },
            .message = message,
        });
    }

    /// Publish the diagnostics of one analysis, each on the file it lies
    /// in. The roots always receive a set (an empty one clears them); other
    /// files receive theirs only when they do not report on themselves
    /// (`ownsDiagnostics`), and closed ones only when there is something to
    /// report. Records what the analysis read and published under
    /// `record_uri`.
    fn publishUnitDiagnostics(
        self: *Handler,
        arena: std.mem.Allocator,
        record_uri: []const u8,
        unit: *const Unit,
        primary: []const mm0.CompilerDiagnostic,
        warnings: []const mm0.CompilerDiagnostic,
        extra: ?mm0.CompilerDiagnostic,
        proof_omitted: ?mm0.CompilerDiagnostic,
        mm0_omitted: ?mm0.CompilerDiagnostic,
        extra_located: []const LocatedDiagnostic,
    ) !void {
        var all = std.ArrayListUnmanaged(LocatedDiagnostic){};
        try all.appendSlice(arena, try lsp_diagnostics.locateCompilerDiagnostics(
            arena,
            unit.diagnosticContext(),
            primary,
            warnings,
            extra,
            proof_omitted,
            mm0_omitted,
            self.offset_encoding,
        ));
        for (unit.failures) |failure| {
            try all.append(arena, .{
                .uri = failure.file.uri,
                .version = failure.file.version,
                .diagnostic = .{
                    .range = lsp.offsets.locToRange(
                        failure.file.text,
                        .{ .start = failure.span.start, .end = failure.span.end },
                        self.offset_encoding,
                    ),
                    .severity = .Error,
                    .source = LSP_SERVER_NAME,
                    .message = failure.message,
                },
            });
        }
        try all.appendSlice(arena, extra_located);

        // Proof root first, then the theory root, then everything else.
        var targets = std.ArrayListUnmanaged(UnitFile){};
        if (unit.proof) |proof| try targets.append(arena, proof.rootFile());
        try targets.append(arena, unit.mm0.rootFile());
        for (unit.mm0.files, 0..) |file, index| {
            if (index != unit.mm0.root) try targets.append(arena, file);
        }
        if (unit.proof) |proof| {
            for (proof.files, 0..) |file, index| {
                if (index != proof.root) try targets.append(arena, file);
            }
        }

        var deps = std.ArrayListUnmanaged([]const u8){};
        var published = std.ArrayListUnmanaged([]const u8){};
        for (targets.items, 0..) |target, position| {
            // A file reached twice (a proof file both paired and included)
            // publishes once.
            var seen = false;
            for (targets.items[0..position]) |earlier| {
                if (std.mem.eql(u8, earlier.uri, target.uri)) seen = true;
            }
            if (seen) continue;

            const is_root = unit.isRootUri(target.uri);
            if (!is_root) try deps.append(arena, target.uri);
            var diagnostics = std.ArrayListUnmanaged(types.Diagnostic){};
            for (all.items) |located| {
                if (!std.mem.eql(u8, located.uri, target.uri)) continue;
                try diagnostics.append(arena, located.diagnostic);
            }
            if (is_root) {
                try self.publishDiagnostics(
                    arena,
                    target.uri,
                    target.version,
                    diagnostics.items,
                );
                continue;
            }
            // A closed file is left alone when it has nothing to report; an
            // open library file always receives the root's view, which also
            // clears the note its own analysis left ("no sibling theory").
            if (diagnostics.items.len == 0 and !self.docs.contains(target.uri)) {
                continue;
            }
            if (self.ownsDiagnostics(arena, target.uri)) continue;
            try self.publishDiagnostics(
                arena,
                target.uri,
                target.version,
                diagnostics.items,
            );
            try published.append(arena, target.uri);
        }

        try self.storeUnitRecord(arena, record_uri, deps.items, published.items);
    }

    /// Replace the record for `root_uri`, clearing diagnostics on files the
    /// previous analysis published for but this one did not.
    fn storeUnitRecord(
        self: *Handler,
        arena: std.mem.Allocator,
        root_uri: []const u8,
        deps: []const []const u8,
        published: []const []const u8,
    ) !void {
        const owned_deps = try dupeUriList(self.allocator, deps);
        errdefer freeUriList(self.allocator, owned_deps);
        const owned_published = try dupeUriList(self.allocator, published);
        errdefer freeUriList(self.allocator, owned_published);

        const gop = try self.units.getOrPut(self.allocator, root_uri);
        if (gop.found_existing) {
            for (gop.value_ptr.published) |old| {
                if (uriListContains(published, old)) continue;
                try self.clearDiagnostics(arena, old, null);
            }
            gop.value_ptr.deinit(self.allocator);
        } else {
            errdefer _ = self.units.remove(root_uri);
            gop.key_ptr.* = try self.allocator.dupe(u8, root_uri);
        }
        gop.value_ptr.* = .{ .deps = owned_deps, .published = owned_published };
    }

    /// Drop the record for `root_uri`, clearing what it published.
    fn forgetUnit(
        self: *Handler,
        arena: std.mem.Allocator,
        root_uri: []const u8,
    ) !void {
        const removed = self.units.fetchRemove(root_uri) orelse return;
        var record = removed.value;
        defer {
            record.deinit(self.allocator);
            self.allocator.free(removed.key);
        }
        for (record.published) |uri| {
            try self.clearDiagnostics(arena, uri, null);
        }
    }

    /// Is `uri` read by some root's analysis?
    fn isDependency(self: *Handler, uri: []const u8) bool {
        var it = self.units.iterator();
        while (it.next()) |entry| {
            if (uriListContains(entry.value_ptr.deps, uri)) return true;
        }
        return false;
    }

    /// The roots whose analyses read `uri`, copied into `arena` (analysing
    /// them rewrites the records).
    fn dependentRoots(
        self: *Handler,
        arena: std.mem.Allocator,
        uri: []const u8,
    ) ![]const []const u8 {
        var roots = std.ArrayListUnmanaged([]const u8){};
        var it = self.units.iterator();
        while (it.next()) |entry| {
            if (!uriListContains(entry.value_ptr.deps, uri)) continue;
            try roots.append(arena, try arena.dupe(u8, entry.key_ptr.*));
        }
        return roots.items;
    }

    /// The root `.mm0` (and its proof file, when there is one) a request on
    /// `uri` navigates: the document itself for a `.mm0`, its sibling for a
    /// `.auf`. Null when the root cannot be loaded.
    fn rootDocumentsForUri(
        self: *Handler,
        arena: std.mem.Allocator,
        uri: []const u8,
    ) !?RootDocuments {
        const path = uriToPath(arena, uri) catch return null;
        switch (documentKind(path)) {
            .mm0 => {
                const mm0_loaded = self.loadTextForUriPath(arena, uri, path) catch
                    return null;
                var docs: RootDocuments = .{
                    .mm0 = mm0_loaded,
                    .mm0_path = path,
                    .proof = null,
                    .proof_path = null,
                };
                if (siblingPathForMm0(arena, path)) |proof_path| {
                    const proof_uri = try pathToUri(arena, proof_path);
                    if (self.loadTextForUriPath(arena, proof_uri, proof_path)) |proof| {
                        docs.proof = proof;
                        docs.proof_path = proof_path;
                    } else |_| {}
                } else |_| {}
                return docs;
            },
            .proof => {
                const proof_loaded = self.loadTextForUriPath(arena, uri, path) catch
                    return null;
                const mm0_path = siblingPathForProof(arena, path) catch return null;
                const mm0_loaded = self.loadTextPreferOpenDocument(arena, mm0_path) catch
                    return null;
                return .{
                    .mm0 = mm0_loaded,
                    .mm0_path = mm0_path,
                    .proof = proof_loaded,
                    .proof_path = path,
                };
            },
            .other => return null,
        }
    }

    fn navigationSnapshotForUri(
        self: *Handler,
        arena: std.mem.Allocator,
        uri: []const u8,
    ) !?NavigationSnapshot {
        if (try self.rootDocumentsForUri(arena, uri)) |docs| {
            return try self.navigationSnapshotForRoot(arena, uri, docs);
        }
        // A library proof file without a theory of its own navigates
        // through a root that includes it.
        const roots = try self.dependentRoots(arena, uri);
        for (roots) |root| {
            if (std.mem.eql(u8, root, uri)) continue;
            const docs = try self.rootDocumentsForUri(arena, root) orelse continue;
            return try self.navigationSnapshotForRoot(arena, uri, docs);
        }
        return null;
    }

    /// The cached index over the unit rooted at `docs`, rebuilt when any
    /// file of the unit changed, viewed from `request_uri`.
    fn navigationSnapshotForRoot(
        self: *Handler,
        arena: std.mem.Allocator,
        request_uri: []const u8,
        docs: RootDocuments,
    ) !?NavigationSnapshot {
        var unit_arena = std.heap.ArenaAllocator.init(self.allocator);
        var keep_arena = false;
        defer if (!keep_arena) unit_arena.deinit();

        const unit = try self.buildUnit(
            unit_arena.allocator(),
            docs.mm0,
            docs.mm0_path,
            docs.proof,
            docs.proof_path,
        );
        const states = try unit.states(arena);
        const mm0_uri = docs.mm0.uri;

        const entry: *NavigationCacheEntry = blk: {
            if (self.nav_cache.getPtr(mm0_uri)) |entry| {
                if (entry.key.eql(states)) break :blk entry;
            }
            self.removeNavigationCacheByMm0Uri(mm0_uri);

            var snapshot = try LspIndex.Snapshot.build(self.allocator, .{
                .mm0_uri = mm0_uri,
                .mm0_text = unit.mm0.joined.text,
                .proof_uri = if (unit.proof) |proof| proof.rootFile().uri else null,
                .proof_text = if (unit.proof) |proof| proof.joined.text else null,
                .check_memo = &self.check_memo,
            });
            errdefer snapshot.deinit();
            var key = try UnitKey.init(self.allocator, states);
            errdefer key.deinit(self.allocator);
            const owned_uri = try self.allocator.dupe(u8, mm0_uri);
            errdefer self.allocator.free(owned_uri);
            try self.nav_cache.put(self.allocator, owned_uri, .{
                .uri = owned_uri,
                .key = key,
                .unit_arena = unit_arena,
                .unit = unit,
                .snapshot = snapshot,
            });
            keep_arena = true;
            break :blk self.nav_cache.getPtr(owned_uri).?;
        };

        const found = entry.unit.find(request_uri) orelse return null;
        return .{
            .snapshot = &entry.snapshot,
            .unit = &entry.unit,
            .document = found.document,
            .file_index = found.file_index,
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
        // "not yet searched" warning. Every key lists all files of its unit,
        // so an edited import or include sweeps the roots that read it too.
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

const RootDocuments = struct {
    mm0: LoadedText,
    mm0_path: []const u8,
    proof: ?LoadedText,
    proof_path: ?[]const u8,
};

/// Resolves imports and includes for `Handler.buildUnit`: a spec is joined
/// to the importing file's directory and normalised lexically, then looked
/// up as an open document or read from disk. Every file loaded is kept
/// under its path so the unit can list them afterwards.
const UnitLoader = struct {
    handler: *Handler,
    arena: std.mem.Allocator,
    files: std.StringHashMapUnmanaged(UnitFile) = .empty,

    fn resolver(self: *UnitLoader) Imports.Resolver {
        return .{ .ctx = @ptrCast(self), .resolveFn = resolveFn };
    }

    fn put(self: *UnitLoader, file: UnitFile) !void {
        try self.files.put(self.arena, file.path, file);
    }

    fn load(self: *UnitLoader, path: []const u8, open_only: bool) !?UnitFile {
        if (self.files.get(path)) |file| return file;
        const file = try self.handler.resolveUnitFile(
            self.arena,
            path,
            open_only,
        ) orelse return null;
        try self.put(file);
        return file;
    }

    /// The unit files behind a join, parallel to `joined.files`.
    fn filesFor(self: *UnitLoader, joined: Imports.Joined) ![]const UnitFile {
        const out = try self.arena.alloc(UnitFile, joined.files.len);
        for (joined.files, 0..) |file, index| {
            out[index] = self.files.get(file.key).?;
        }
        return out;
    }

    fn resolveFn(
        ctx: *anyopaque,
        allocator: std.mem.Allocator,
        from_key: []const u8,
        spec: []const u8,
    ) anyerror!Imports.Resolved {
        const self: *UnitLoader = @ptrCast(@alignCast(ctx));
        const path = try resolveSpecPath(allocator, from_key, spec);
        const file = try self.load(path, false) orelse return error.FileNotFound;
        return .{ .key = file.path, .text = file.text };
    }
};

/// The path an import/include spec names, relative to the importing file's
/// directory, with `.` and `..` segments collapsed. Purely lexical: open
/// documents have no file behind them, and the same form keys both.
pub fn resolveSpecPath(
    allocator: std.mem.Allocator,
    from_path: []const u8,
    spec: []const u8,
) ![]const u8 {
    const base = if (std.fs.path.isAbsolutePosix(spec))
        ""
    else
        std.fs.path.dirnamePosix(from_path) orelse "";
    const absolute = std.fs.path.isAbsolutePosix(spec) or
        std.fs.path.isAbsolutePosix(base);

    var parts = std.ArrayListUnmanaged([]const u8){};
    defer parts.deinit(allocator);
    const sources = [_][]const u8{ base, spec };
    for (sources) |source| {
        var it = std.mem.splitScalar(u8, source, '/');
        while (it.next()) |part| {
            if (part.len == 0 or std.mem.eql(u8, part, ".")) continue;
            if (std.mem.eql(u8, part, "..")) {
                if (parts.items.len != 0 and
                    !std.mem.eql(u8, parts.items[parts.items.len - 1], ".."))
                {
                    _ = parts.pop();
                    continue;
                }
                if (absolute) continue;
            }
            try parts.append(allocator, part);
        }
    }

    var out = std.ArrayListUnmanaged(u8){};
    if (absolute) try out.append(allocator, '/');
    for (parts.items, 0..) |part, index| {
        if (index != 0) try out.append(allocator, '/');
        try out.appendSlice(allocator, part);
    }
    if (out.items.len == 0) try out.append(allocator, '.');
    return try out.toOwnedSlice(allocator);
}

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
