//! When the language server checks a document and what it does with the
//! result: the queue of documents whose diagnostics are out of date, the
//! analysis of one, and the progress it shows. `Handler` names these as
//! its own methods.

const std = @import("std");
const lsp = @import("lsp");
const mm0 = @import("mm0");
const protocol = @import("./protocol.zig");
const handler_mod = @import("../lsp.zig");
const uri_names = @import("./uris.zig");
const unit_mod = @import("./unit.zig");
const unit_state = @import("./unit_state.zig");

const types = lsp.types.flat;
const ArenaAllocator = mm0.ArenaAllocator;
const Handler = handler_mod.Handler;
const HoleInferenceSink = mm0.CompilerSupport.Context.HoleInferenceSink;
const LocatedDiagnostic = protocol.LocatedDiagnostic;
const LSP_SERVER_NAME = protocol.SERVER_NAME;
const Search = mm0.CompilerSupport.Search;
const Unit = unit_mod.Unit;
const UnitRoots = uri_names.UnitRoots;
const UnitSide = unit_mod.UnitSide;
const UnitState = unit_state.UnitState;
const documentKind = uri_names.documentKind;
const outcomeForPlaceholder = unit_state.outcomeForPlaceholder;
const pathToUri = uri_names.pathToUri;
const siblingPathForMm0 = uri_names.siblingPathForMm0;
const siblingPathForProof = uri_names.siblingPathForProof;
const uriToPath = uri_names.uriToPath;
const zeroRange = protocol.zeroRange;
const publish = @import("./publish.zig");

/// `Diagnostic.code` on everything `searchStatusDiagnostics` builds. These are
/// the only diagnostics the compile pipeline does not also produce, so a client
/// that runs its own compile (the browser editor does) needs a way to pick them
/// out of a `publishDiagnostics` set and merge just those.
const SEARCH_STATUS_CODE = "search-status";

/// A root whose diagnostics are out of date (`Handler.pending`).
pub const PendingAnalysis = struct {
    /// The proofs of its open files are checked and their diagnostics
    /// published (`Handler.analyzeProofDocument`): the check of the rest is
    /// left.
    own_checked: bool = false,
    /// When its analysis first ran (`std.Io.Clock.awake`).
    started: ?i96 = null,
    /// The progress shown for its check, once that has run long enough.
    progress: ?ShownProgress = null,
};

pub const ShownProgress = struct {
    token: i32,
    /// The last percentage sent.
    percentage: u32,
};

/// What `Handler.analyzeUri` got through.
pub const AnalysisOutcome = enum {
    /// The whole unit: its diagnostics are up to date.
    checked,
    /// The proofs of the open files only, whose diagnostics are published.
    own_checked,
};

fn analyzeUri(
    self: *Handler,
    arena: std.mem.Allocator,
    uri: []const u8,
    pending: *PendingAnalysis,
) !AnalysisOutcome {
    const doc = self.docs.get(uri) orelse return .checked;
    const path = uriToPath(arena, uri) catch |err| {
        try self.publishMessageDiagnostic(
            arena,
            uri,
            doc.version,
            doc.text,
            switch (err) {
                error.InvalidFormat => try mm0.allocDiagnosticMessage(
                    arena,
                    "document_uri_invalid",
                    .{},
                ),
                error.UnsupportedUriScheme => try mm0.allocDiagnosticMessage(
                    arena,
                    "document_uri_scheme",
                    .{},
                ),
                error.UnsupportedUriHost => try mm0.allocDiagnosticMessage(
                    arena,
                    "document_uri_host",
                    .{},
                ),
                else => mm0.compilerErrorSummary(err),
            },
        );
        return .checked;
    };

    switch (documentKind(path)) {
        .mm0 => return analyzeMm0Document(
            self,
            arena,
            uri,
            doc.version,
            doc.text,
            path,
            pending,
        ),
        .proof => return analyzeProofDocument(
            self,
            arena,
            uri,
            doc.version,
            doc.text,
            path,
            pending,
        ),
        .other => {
            try self.clearDiagnostics(arena, uri, doc.version);
            return .checked;
        },
    }
}

/// Re-analyse every open root whose last analysis read `uri` (as an
/// import, an include, or a paired proof file of an import).
pub fn analyzeDependentsSoon(
    self: *Handler,
    arena: std.mem.Allocator,
    uri: []const u8,
) !void {
    // `uri`'s own analysis is marked by its caller.
    const own = try analysisUri(self, arena, uri);
    const roots = try self.dependentRoots(arena, uri);
    for (roots) |root| {
        if (!self.docs.contains(root)) continue;
        if (std.mem.eql(u8, try analysisUri(self, arena, root), own)) continue;
        try self.analyzeSoon(arena, root);
    }
}

/// Mark `uri`'s diagnostics out of date. A serial host has them brought
/// up to date at once; a queued one asks for that when no input is
/// waiting.
pub fn analyzeSoon(
    self: *Handler,
    arena: std.mem.Allocator,
    uri: []const u8,
) !void {
    const key = try analysisUri(self, arena, uri);
    // A change starts its check over, behind those still pending.
    try self.dropPending(key);
    const owned = try self.allocator.dupe(u8, key);
    errdefer self.allocator.free(owned);
    try self.pending.put(self.allocator, owned, .{});
    // A proof file's analysis covers its `.mm0`.
    if (try siblingMm0Uri(self, arena, key)) |mm0_uri| try self.dropPending(mm0_uri);
    if (self.host == .serial) try self.analyzePending();
}

/// The URI whose analysis covers `uri`: a `.mm0` whose proof file is
/// open is analysed through it (`analyzeMm0Document`).
fn analysisUri(
    self: *Handler,
    arena: std.mem.Allocator,
    uri: []const u8,
) ![]const u8 {
    const path = uriToPath(arena, uri) catch return uri;
    if (documentKind(path) != .mm0) return uri;
    const proof_path = siblingPathForMm0(arena, path) catch return uri;
    const proof_uri = try pathToUri(arena, proof_path);
    return if (self.docs.contains(proof_uri)) proof_uri else uri;
}

/// The `.mm0` beside proof file `uri`; null for any other document.
fn siblingMm0Uri(
    _: *Handler,
    arena: std.mem.Allocator,
    uri: []const u8,
) !?[]const u8 {
    const path = uriToPath(arena, uri) catch return null;
    if (documentKind(path) != .proof) return null;
    const mm0_path = siblingPathForProof(arena, path) catch return null;
    return try pathToUri(arena, mm0_path);
}

pub fn hasPendingAnalysis(self: *const Handler) bool {
    return self.pending.count() != 0;
}

/// Analyse the pending documents in the order they changed: first the
/// proofs of the open files of each, then the rest of each. One the
/// interrupt stops stays pending, with those after it.
pub fn analyzePending(self: *Handler) !void {
    while (nextPending(self)) |index| try analyzePendingAt(self, index);
}

fn nextPending(self: *const Handler) ?usize {
    if (self.pending.count() == 0) return null;
    for (self.pending.values(), 0..) |entry, index| {
        if (!entry.own_checked) return index;
    }
    return 0;
}

fn analyzePendingAt(self: *Handler, index: usize) !void {
    var arena_state = ArenaAllocator.init(self.allocator);
    defer arena_state.deinit();
    const entry = &self.pending.values()[index];
    if (showsProgress(self) and entry.started == null) entry.started = now(self);
    const outcome = analyzeUri(
        self,
        arena_state.allocator(),
        self.pending.keys()[index],
        entry,
    ) catch |err| {
        if (err != error.AnalysisInterrupted) try removePendingAt(self, index);
        return err;
    };
    switch (outcome) {
        .own_checked => entry.own_checked = true,
        .checked => try removePendingAt(self, index),
    }
}

/// Whether checks show their progress: the client shows what the server
/// starts, and the host lets it see the output as it is written.
fn showsProgress(self: *const Handler) bool {
    return self.progress_support and self.host == .queued;
}

fn now(self: *const Handler) i96 {
    return std.Io.Clock.awake.now(self.io).nanoseconds;
}

pub fn dropPending(self: *Handler, uri: []const u8) !void {
    try removePendingAt(self, self.pending.getIndex(uri) orelse return);
}

fn removePendingAt(self: *Handler, index: usize) !void {
    const pending = self.pending.values()[index];
    self.allocator.free(self.pending.keys()[index]);
    self.pending.orderedRemoveAt(index);
    try endProgress(self, pending);
}

fn analyzeMm0Document(
    self: *Handler,
    arena: std.mem.Allocator,
    uri: []const u8,
    version: i32,
    text: []const u8,
    path: []const u8,
    pending: *PendingAnalysis,
) !AnalysisOutcome {
    if (siblingPathForMm0(arena, path)) |proof_path| {
        const proof_uri = try pathToUri(arena, proof_path);
        if (self.docs.get(proof_uri)) |proof_doc| {
            return analyzeProofDocument(
                self,
                arena,
                proof_uri,
                proof_doc.version,
                proof_doc.text,
                proof_path,
                pending,
            );
        }
    } else |_| {}

    const unit = try unit_mod.join(self.sources(), arena, uri, path, null, null);
    defer unit.release(&self.texts);

    var compiler = mm0.Compiler.init(arena, unit.mm0.joined.text);
    compiler.analyzeMm0() catch |err| {
        if (hasDiagnostics(&compiler)) {
            try self.publishUnitDiagnostics(
                arena,
                uri,
                &unit,
                .checked,
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
        return .checked;
    };
    try self.publishUnitDiagnostics(
        arena,
        uri,
        &unit,
        .checked,
        compiler.primaryDiagnostics(),
        compiler.warningDiagnostics(),
        null,
        null,
        compiler.omittedPrimaryDiagnostic(.mm0),
        &.{},
    );
    return .checked;
}

fn analyzeProofDocument(
    self: *Handler,
    arena: std.mem.Allocator,
    proof_uri: []const u8,
    proof_version: i32,
    proof_text: []const u8,
    proof_path: []const u8,
    pending: *PendingAnalysis,
) !AnalysisOutcome {
    const mm0_path = siblingPathForProof(arena, proof_path) catch {
        try self.publishMessageDiagnostic(
            arena,
            proof_uri,
            proof_version,
            proof_text,
            try mm0.allocDiagnosticMessage(
                arena,
                "proof_document_extension",
                .{},
            ),
        );
        return .checked;
    };
    const roots: UnitRoots = .{
        .mm0_uri = try pathToUri(arena, mm0_path),
        .mm0_path = mm0_path,
        .proof_uri = proof_uri,
        .proof_path = proof_path,
    };
    // A request may have joined the same files already, say the one that
    // stopped this analysis; if not, the next request reads this join.
    const state = self.unitFor(roots) catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
        else => {
            try publishTheoryUnreadable(
                self,
                arena,
                roots,
                proof_version,
                proof_text,
                err,
            );
            return .checked;
        },
    };
    const unit: *const Unit = &state.unit;
    try self.recordUnitFiles(arena, proof_uri, unit);

    // One status diagnostic per search placeholder (warning until searched,
    // then info/error from the recorded outcome), published together with
    // the compiler diagnostics: publishDiagnostics replaces the full set
    // per document, so they must go out in the same payload.
    const search_diagnostics = try searchStatusDiagnostics(self, arena, state);

    // The handler's allocator, not the request's arena: the analysis
    // frees each theorem's work once it is checked, which an arena
    // could not take back. What outlives it is the diagnostics, which
    // the compiler holds in storage of its own, and the holes.
    var compiler = mm0.Compiler.initWithProof(
        self.allocator,
        unit.mm0.joined.text,
        unit.proof.?.joined.text,
    );
    compiler.allow_search_placeholders = true;
    var holes = HoleInferenceSink{
        .allocator = self.allocator,
    };
    var holes_owned = true;
    defer if (holes_owned) holes.deinit();
    compiler.hole_inference_sink = &holes;
    compiler.editor.memo = self.checkMemoFor(roots.mm0_uri);
    compiler.editor.interrupt = self.host.interrupt();
    // The editor shows the open files, so a queued host has their
    // proofs checked first and their diagnostics published, then the
    // rest.
    const own_first = self.host == .queued;
    const own: []const mm0.CompilerDiagnosticSpan =
        if (own_first) try ownProofSpans(self, arena, unit) else &.{};
    var scope: mm0.CheckScope = .{ .spans = own };
    if (own_first and !pending.own_checked) compiler.editor.scope = &scope;
    var progress: CheckProgress = .{
        .handler = self,
        .pending = pending,
        .side = &unit.proof.?,
        .own = own,
        .own_pass = compiler.editor.scope != null,
    };
    if (showsProgress(self)) compiler.editor.progress = progress.hook();
    const analyzed = compiler.analyze();
    if (progress.failure) |err| return err;
    // A stopped analysis saw part of the unit: what it found is neither
    // published nor kept.
    if (analyzed) |_| {} else |err| {
        if (err == error.AnalysisInterrupted) return err;
    }
    // A check of the open files' proofs alone publishes on those files
    // only. Its holes are all a request can ask about: requests are
    // about open files.
    const outcome: AnalysisOutcome = if (scope.skipped != 0) .own_checked else .checked;
    holes_owned = false;
    state.keepHoles(holes);
    analyzed catch |err| {
        if (hasDiagnostics(&compiler)) {
            try self.publishUnitDiagnostics(
                arena,
                proof_uri,
                unit,
                outcome,
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
                roots.mm0_uri,
                unit.mm0.rootFile().version,
            );
        }
        return outcome;
    };

    try self.publishUnitDiagnostics(
        arena,
        proof_uri,
        unit,
        outcome,
        compiler.primaryDiagnostics(),
        compiler.warningDiagnostics(),
        null,
        compiler.omittedPrimaryDiagnostic(.proof),
        compiler.omittedPrimaryDiagnostic(.mm0),
        search_diagnostics,
    );
    return outcome;
}

/// The spans of `unit`'s joined proof text that come from the files
/// its analysis reports on and the editor shows: the root, and the open
/// library files without a theory of their own (`ownsDiagnostics`).
fn ownProofSpans(
    self: *Handler,
    arena: std.mem.Allocator,
    unit: *const Unit,
) ![]const mm0.CompilerDiagnosticSpan {
    const side = unit.proof.?;
    var spans = std.ArrayListUnmanaged(mm0.CompilerDiagnosticSpan).empty;
    for (side.joined.map.segments) |segment| {
        // Separators the join inserted hold no proofs.
        const index = segment.file_index orelse continue;
        const file = side.files[index];
        if (index != side.root and
            (!self.docs.contains(file.uri) or self.ownsDiagnostics(arena, file.uri)))
        {
            continue;
        }
        const start = segment.joined_start;
        const end = start + segment.len;
        if (spans.items.len != 0 and spans.items[spans.items.len - 1].end == start) {
            spans.items[spans.items.len - 1].end = end;
        } else {
            try spans.append(arena, .{ .start = start, .end = end });
        }
    }
    return spans.items;
}

/// Show `progress`'s check at the proof starting at `offset`, once the
/// check has run `progress_delay_ns`: begun with the client's
/// `window/workDoneProgress/create`, then reported as the percentage
/// rises. The client handles messages in order, so the token is used
/// without waiting for its answer, which the input queue would hold
/// until the check stops.
fn showProgress(self: *Handler, progress: *const CheckProgress, offset: usize) !void {
    const pending = progress.pending;
    const percentage = progress.percentage(offset);
    const message = std.fs.path.basename(progress.fileAt(offset));
    if (pending.progress) |*shown| {
        if (percentage <= shown.percentage) return;
        shown.percentage = percentage;
        try writeProgress(self, shown.token, types.WorkDoneProgressReport{
            .message = message,
            .percentage = percentage,
        });
        return;
    }
    const started = pending.started orelse return;
    if (now(self) - started < self.progress_delay_ns) return;
    self.last_progress_token += 1;
    const token = self.last_progress_token;
    self.last_request_id += 1;
    try self.transport.writeRequest(
        self.io,
        self.allocator,
        .{ .number = self.last_request_id },
        "window/workDoneProgress/create",
        types.WorkDoneProgressCreateParams,
        .{ .token = .{ .integer = token } },
        .{ .emit_null_optional_fields = false },
    );
    pending.progress = .{ .token = token, .percentage = percentage };
    try writeProgress(self, token, types.WorkDoneProgressBegin{
        .title = "Checking proofs",
        .message = message,
        .percentage = percentage,
    });
}

/// End the progress shown for `pending`, if any.
fn endProgress(self: *Handler, pending: PendingAnalysis) !void {
    const shown = pending.progress orelse return;
    try writeProgress(self, shown.token, types.WorkDoneProgressEnd{});
}

fn writeProgress(self: *Handler, token: i32, value: anytype) !void {
    try self.transport.writeNotification(
        self.io,
        self.allocator,
        "$/progress",
        struct { token: types.ProgressToken, value: @TypeOf(value) },
        .{ .token = .{ .integer = token }, .value = value },
        .{ .emit_null_optional_fields = false },
    );
}

/// Report that the theory of the proof file at `roots` cannot be loaded.
fn publishTheoryUnreadable(
    self: *Handler,
    arena: std.mem.Allocator,
    roots: UnitRoots,
    proof_version: i32,
    proof_text: []const u8,
    err: anyerror,
) !void {
    // A proof file without a theory of its own that some root
    // includes: that root's analysis reports on it.
    if (err == error.FileNotFound and self.isDependency(roots.proof_uri)) return;
    const message = switch (err) {
        error.FileNotFound => try mm0.allocDiagnosticMessage(
            arena,
            "proof_document_no_theory",
            .{},
        ),
        else => try mm0.allocDiagnosticMessage(
            arena,
            "proof_document_theory_unreadable",
            .{@errorName(err)},
        ),
    };
    try self.publishMessageDiagnostic(
        arena,
        roots.proof_uri,
        proof_version,
        proof_text,
        message,
    );
    try self.clearDiagnostics(arena, roots.mm0_uri, null);
}

pub fn hasDiagnostics(compiler: *const mm0.Compiler) bool {
    return compiler.diagnostics.last_diagnostic != null or
        compiler.primaryDiagnostics().len != 0 or
        compiler.warningDiagnostics().len != 0;
}

fn searchStatusDiagnostics(
    self: *Handler,
    arena: std.mem.Allocator,
    state: *const UnitState,
) ![]const LocatedDiagnostic {
    const proof_side = state.unit.proof orelse return &.{};
    // The memo knows where the bodies it checked end, so the scan
    // parses only the bodies that spell a placeholder and those it does
    // not know.
    const notices = try Search.placeholderNotices(
        arena,
        proof_side.joined.text,
        self.check_memo.knownBodies(),
    );
    if (notices.len == 0) return &.{};
    var converter = protocol.RangeConverter{
        .arena = arena,
        .encoding = self.offset_encoding,
    };

    const outcomes = state.outcomes.items;

    var diagnostics = std.ArrayListUnmanaged(LocatedDiagnostic).empty;
    for (notices) |notice| {
        // A rejected parameter is an error; it never blocks the search,
        // which simply does not apply it.
        var severity = protocol.diagnosticSeverityToLsp(notice.severity());
        var message = notice.message;
        const recorded = if (notice.kind == .placeholder)
            outcomeForPlaceholder(outcomes, notice.span)
        else
            null;
        if (recorded) |outcome| {
            const keyword = notice.placeholder.kind.keyword();
            switch (outcome.status) {
                .found => {
                    severity = .Information;
                    message = try mm0.allocDiagnosticMessage(
                        arena,
                        "search_succeeded",
                        .{ keyword, outcome.detail },
                    );
                },
                .miss, .budget_exhausted => {
                    severity = .Error;
                    // The recorded detail elaborates the failure (which
                    // bound truncated the search, how far it got, what
                    // to tune); fall back to the generic wording for
                    // outcomes recorded without one.
                    const detail = if (outcome.detail.len > 0)
                        outcome.detail
                    else if (outcome.status == .miss)
                        try mm0.allocDiagnosticMessage(
                            arena,
                            "search_no_proof",
                            .{},
                        )
                    else
                        try mm0.allocDiagnosticMessage(
                            arena,
                            "search_budget_exhausted",
                            .{},
                        );
                    message = try mm0.allocDiagnosticMessage(
                        arena,
                        "search_failed",
                        .{ keyword, detail },
                    );
                },
            }
        }
        try appendLocated(
            arena,
            &diagnostics,
            &converter,
            proof_side,
            notice.span,
            severity,
            message,
        );
    }
    return try diagnostics.toOwnedSlice(arena);
}

/// A search-status diagnostic for `span` of the joined proof text, on
/// the file the span lies in.
pub fn appendLocated(
    arena: std.mem.Allocator,
    diagnostics: *std.ArrayListUnmanaged(LocatedDiagnostic),
    converter: *protocol.RangeConverter,
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
            .range = try converter.range(hit.file.text, .{
                .start = hit.span.start,
                .end = hit.span.end,
            }),
            .severity = severity,
            .source = LSP_SERVER_NAME,
            .code = .{ .string = SEARCH_STATUS_CODE },
            .message = .{ .string = message },
        },
    });
}

/// The progress of one check of a unit's proofs (`Handler.showProgress`),
/// told where each proof the check runs starts. The percentage counts the
/// proof text done: in the check of the open files' proofs alone (`own`),
/// their bytes up to the proof; in the check of the rest, all of theirs and
/// the others' up to it. So it rises across both.
const CheckProgress = struct {
    handler: *Handler,
    pending: *PendingAnalysis,
    side: *const UnitSide,
    own: []const mm0.CompilerDiagnosticSpan,
    own_pass: bool,
    /// Why a report could not be sent: the analysis returns it once done.
    failure: ?anyerror = null,

    fn hook(self: *CheckProgress) mm0.AnalysisProgress {
        return .{ .context = self, .checkingFn = checking };
    }

    fn checking(context: *anyopaque, offset: usize) void {
        const self: *CheckProgress = @ptrCast(@alignCast(context));
        if (self.failure != null) return;
        showProgress(self.handler, self, offset) catch |err| {
            self.failure = err;
        };
    }

    fn percentage(self: *const CheckProgress, offset: usize) u32 {
        const total = self.side.joined.text.len;
        if (total == 0) return 0;
        var own_total: usize = 0;
        var own_before: usize = 0;
        for (self.own) |span| {
            own_total += span.end - span.start;
            own_before += @min(span.end, @max(span.start, offset)) - span.start;
        }
        const done = if (self.own_pass) own_before else own_total + (offset - own_before);
        return @intCast(@min(100, done * 100 / total));
    }

    fn fileAt(self: *const CheckProgress, offset: usize) []const u8 {
        const location = self.side.locate(.{ .start = offset, .end = offset }) orelse
            return self.side.rootFile().path;
        return location.file.path;
    }
};
