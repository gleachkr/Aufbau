//! Fuzz target: language-server sessions, in process.
//!
//! The session runs lsp-kit's own server loop (as `abc lsp` and the browser
//! do) over a transport that writes the client's half on demand: initialize
//! with a random position encoding, open a proof case's `.mm0` and `.auf`
//! (maybe edited, maybe split at a statement into a `lib` pair that the
//! `case` pair imports, so analysis crosses an import), then edits (insertions, deletions, whole-document
//! replacements, typing a token one character at a time), requests at
//! random or real positions, closing and reopening, applying an edit a code
//! action returned, and malformed messages. The server must not panic,
//! leak or hang, every message it sends must be JSON, a well-formed request
//! must not fail, and every range it returns must lie inside its document
//! on a code-point boundary of the negotiated encoding. A rename must
//! replace one name, and leave the analysis's diagnostics as they were.
const std = @import("std");
const lsp = @import("lsp");
const server = @import("lsp_server");
const mm0 = @import("mm0");
const harness = @import("harness.zig");
const mutate = @import("mutate.zig");

const Encoding = lsp.offsets.Encoding;
const Position = lsp.offsets.Position;
const Smith = std.testing.Smith;
/// Serializes as `{}`; an empty `.{}` is a tuple and serializes as `[]`.
const Empty = struct {};

/// At most this many client events after the documents open.
const max_events = 32;

const case_mm0 = "file:///fuzz/case.mm0";
const case_auf = "file:///fuzz/case.auf";
const lib_mm0 = "file:///fuzz/lib.mm0";
const lib_auf = "file:///fuzz/lib.auf";

/// A document of the session and the text it was first opened with.
const Document = struct { uri: []const u8, source: []const u8 };

const Event = enum(u8) {
    insert,
    delete,
    replace_document,
    type_token,
    hover,
    completion,
    definition,
    implementation,
    references,
    document_highlight,
    prepare_rename,
    rename,
    document_symbol,
    code_action,
    apply_code_action,
    close,
    reopen,
    malformed,
};

const Malformed = enum(u8) { garbage, truncated, wrong_params, unknown_method, response };

const Session = struct {
    transport: lsp.Transport = .{ .vtable = &vtable },
    gpa: std.mem.Allocator,
    smith: *Smith,
    input: harness.Input,
    seed: harness.Seed,
    handler: *server.Handler,
    encoding: Encoding = .@"utf-16",
    stage: enum { initialize, initialized, open, events, shutdown, exit, done } = .initialize,
    events: usize = 0,
    next_id: i64 = 1,
    /// The request whose response comes next, when it was well formed.
    pending: ?struct { id: i64, method: []const u8, uri: []const u8 } = null,
    /// A token being typed one character per change.
    typing: ?struct { uri: []const u8, index: usize, rest: []const u8 } = null,
    /// The new name of the rename request whose response comes next.
    rename_to: []const u8 = "",
    /// The document text the last code action's edit would produce.
    action_result: ?struct { uri: []const u8, text: []u8 } = null,
    /// The session's documents; set when they first open.
    docs: []const Document = &.{},
    /// Messages to send before the next event: the documents still to open.
    queued: std.ArrayList([]u8) = .empty,
    /// Every client message, written out when replaying.
    log: std.ArrayList(u8) = .empty,
    /// The documents' texts.
    text_arena: std.heap.ArenaAllocator,

    const vtable: lsp.Transport.VTable = .{
        .readJsonMessage = readJsonMessage,
        .writeJsonMessage = writeJsonMessage,
    };

    fn deinit(self: *Session) void {
        self.text_arena.deinit();
        if (self.action_result) |result| self.gpa.free(result.text);
        for (self.queued.items) |message| self.gpa.free(message);
        self.queued.deinit(self.gpa);
        self.log.deinit(self.gpa);
    }

    fn readJsonMessage(transport: *lsp.Transport, _: std.Io, allocator: std.mem.Allocator) lsp.Transport.ReadError![]u8 {
        const self: *Session = @fieldParentPtr("transport", transport);
        self.pending = null;
        const message = try self.nextMessage(allocator);
        try self.log.appendSlice(self.gpa, message);
        try self.log.append(self.gpa, '\n');
        self.input.dump("session.jsonl", self.log.items);
        return message;
    }

    fn nextMessage(self: *Session, allocator: std.mem.Allocator) ![]u8 {
        switch (self.stage) {
            .initialize => {
                self.stage = .initialized;
                self.encoding = self.smith.value(Encoding);
                return self.request(allocator, "initialize", null, .{
                    .capabilities = .{
                        .general = .{ .positionEncodings = &[_][]const u8{@tagName(self.encoding)} },
                        .textDocument = .{
                            .documentSymbol = .{ .hierarchicalDocumentSymbolSupport = self.smith.value(bool) },
                            .completion = .{ .completionItem = .{ .snippetSupport = self.smith.value(bool) } },
                        },
                    },
                });
            },
            .initialized => {
                self.stage = .open;
                return notification(allocator, "initialized", Empty{});
            },
            .open => {
                self.stage = .events;
                self.docs = try self.documents();
                // Open them in a random order, maybe leaving one out.
                var order: [4]usize = .{ 0, 1, 2, 3 };
                const count = self.docs.len;
                var k = count;
                while (k > 1) : (k -= 1) std.mem.swap(usize, &order[k - 1], &order[self.smith.index(k)]);
                const opened = if (self.smith.value(bool)) count else count - 1;
                for (order[1..opened]) |i| try self.queued.append(self.gpa, try open(allocator, self.docs[i].uri, self.docs[i].source));
                return open(allocator, self.docs[order[0]].uri, self.docs[order[0]].source);
            },
            .events => {
                if (self.queued.items.len != 0) return self.queued.orderedRemove(0);
                if (self.typing != null) return self.typeNext(allocator);
                if (self.events == max_events or self.smith.eos()) {
                    self.stage = .shutdown;
                    return self.nextMessage(allocator);
                }
                self.events += 1;
                return self.event(allocator);
            },
            .shutdown => {
                self.stage = .exit;
                return self.request(allocator, "shutdown", null, null);
            },
            .exit => {
                self.stage = .done;
                return notification(allocator, "exit", null);
            },
            .done => return error.EndOfStream,
        }
    }

    /// The seed's documents, maybe edited: its own pair, or that pair
    /// split at a statement into a `lib` pair the `case` pair imports.
    fn documents(self: *Session) ![]const Document {
        const split = if (self.smith.value(bool)) try splitSeed(self.arena(), self.smith, self.seed) else null;
        const parts: []const Document = if (split) |pair| &pair else &.{
            .{ .uri = case_mm0, .source = self.seed.mm0 },
            .{ .uri = case_auf, .source = self.seed.auf },
        };
        const out = try self.arena().alloc(Document, parts.len);
        for (out, parts) |*doc, part| {
            const other = if (std.mem.endsWith(u8, part.uri, ".mm0")) self.seed.auf else self.seed.mm0;
            doc.* = .{ .uri = part.uri, .source = try self.editedSeed(part.source, other) };
        }
        return out;
    }

    fn arena(self: *Session) std.mem.Allocator {
        return self.text_arena.allocator();
    }

    fn editedSeed(self: *Session, text: []const u8, other: []const u8) ![]const u8 {
        if (self.smith.value(bool)) return mutate.mutate(self.arena(), self.smith, text, other);
        return text;
    }

    fn event(self: *Session, allocator: std.mem.Allocator) ![]u8 {
        const doc = self.docs[self.smith.index(self.docs.len)];
        const uri = doc.uri;
        const text = self.documentText(uri) orelse "";
        switch (self.smith.value(Event)) {
            .insert => {
                const at = self.pickPosition(text);
                const token = mutate.dictionary[self.smith.index(mutate.dictionary.len)];
                return change(allocator, uri, .{ .start = at, .end = at }, token);
            },
            .delete => {
                const a = self.pickPosition(text);
                const b = self.pickPosition(text);
                const ordered = if (a.line < b.line or (a.line == b.line and a.character <= b.character))
                    [2]Position{ a, b }
                else
                    [2]Position{ b, a };
                return change(allocator, uri, .{ .start = ordered[0], .end = ordered[1] }, "");
            },
            .replace_document => {
                const new_text = try mutate.mutate(self.gpa, self.smith, text, "");
                defer self.gpa.free(new_text);
                return replace(allocator, uri, new_text);
            },
            .type_token => {
                self.typing = .{
                    .uri = uri,
                    .index = self.pickIndex(text),
                    .rest = mutate.dictionary[self.smith.index(mutate.dictionary.len)],
                };
                return self.typeNext(allocator);
            },
            inline .hover, .completion, .definition, .implementation => |kind| {
                const method = switch (kind) {
                    .hover => "textDocument/hover",
                    .completion => "textDocument/completion",
                    .definition => "textDocument/definition",
                    .implementation => "textDocument/implementation",
                    else => unreachable,
                };
                return self.request(allocator, method, uri, .{
                    .textDocument = .{ .uri = uri },
                    .position = self.pickPosition(text),
                });
            },
            .references => return self.request(allocator, "textDocument/references", uri, .{
                .textDocument = .{ .uri = uri },
                .position = self.pickPosition(text),
                .context = .{ .includeDeclaration = self.smith.value(bool) },
            }),
            inline .document_highlight, .prepare_rename => |kind| {
                const method = switch (kind) {
                    .document_highlight => "textDocument/documentHighlight",
                    .prepare_rename => "textDocument/prepareRename",
                    else => unreachable,
                };
                return self.request(allocator, method, uri, .{
                    .textDocument = .{ .uri = uri },
                    .position = self.pickPosition(text),
                });
            },
            .rename => {
                self.rename_to = try self.freshName();
                return self.request(allocator, "textDocument/rename", uri, .{
                    .textDocument = .{ .uri = uri },
                    .position = self.pickPosition(text),
                    .newName = self.rename_to,
                });
            },
            .document_symbol => return self.request(allocator, "textDocument/documentSymbol", uri, .{
                .textDocument = .{ .uri = uri },
            }),
            .code_action => {
                const start = self.pickPosition(text);
                return self.request(allocator, "textDocument/codeAction", uri, .{
                    .textDocument = .{ .uri = uri },
                    .range = .{ .start = start, .end = if (self.smith.value(bool)) start else self.pickPosition(text) },
                    .context = .{ .diagnostics = &[_]u32{} },
                });
            },
            .apply_code_action => {
                const result = self.action_result orelse return self.request(allocator, "textDocument/documentSymbol", uri, .{
                    .textDocument = .{ .uri = uri },
                });
                defer {
                    self.gpa.free(result.text);
                    self.action_result = null;
                }
                return replace(allocator, result.uri, result.text);
            },
            .close => return notification(allocator, "textDocument/didClose", .{
                .textDocument = .{ .uri = uri },
            }),
            .reopen => return open(allocator, uri, doc.source),
            .malformed => return self.malformed(allocator, uri),
        }
    }

    fn malformed(self: *Session, allocator: std.mem.Allocator, uri: []const u8) ![]u8 {
        switch (self.smith.value(Malformed)) {
            .garbage => {
                var buffer: [64]u8 = undefined;
                const len = self.smith.slice(&buffer);
                return allocator.dupe(u8, buffer[0..len]);
            },
            .truncated => {
                const whole = try self.request(allocator, "textDocument/hover", uri, .{
                    .textDocument = .{ .uri = uri },
                    .position = .{ .line = 0, .character = 0 },
                });
                self.pending = null;
                return allocator.realloc(whole, self.smith.index(whole.len));
            },
            .wrong_params => {
                const message = try self.request(allocator, "textDocument/hover", uri, .{
                    .textDocument = .{ .uri = uri },
                    .position = "nowhere",
                });
                self.pending = null;
                return message;
            },
            .unknown_method => {
                const message = try self.request(allocator, "textDocument/fuzz", uri, Empty{});
                self.pending = null;
                return message;
            },
            .response => return std.json.Stringify.valueAlloc(allocator, .{
                .jsonrpc = "2.0",
                .id = 9999,
                .result = null,
            }, .{}),
        }
    }

    /// A name no open document contains, so a rename to it can neither
    /// clash nor resolve something unresolved.
    fn freshName(self: *Session) ![]const u8 {
        var name = try std.fmt.allocPrint(self.arena(), "fz{d}", .{self.next_id});
        while (self.anyDocumentContains(name)) {
            name = try std.fmt.allocPrint(self.arena(), "{s}x", .{name});
        }
        return name;
    }

    fn anyDocumentContains(self: *Session, needle: []const u8) bool {
        for (self.docs) |doc| {
            const text = self.documentText(doc.uri) orelse continue;
            if (std.mem.indexOf(u8, text, needle) != null) return true;
        }
        return false;
    }

    fn typeNext(self: *Session, allocator: std.mem.Allocator) ![]u8 {
        const typing = &self.typing.?;
        const text = self.documentText(typing.uri) orelse "";
        const index = @min(typing.index, text.len);
        const at: Position = if (std.unicode.utf8ValidateSlice(text))
            lsp.offsets.indexToPosition(text, index, self.encoding)
        else
            .{ .line = 0, .character = @intCast(@min(index, std.math.maxInt(u32))) };
        const char = typing.rest[0..1];
        typing.index = index + 1;
        typing.rest = typing.rest[1..];
        const uri = typing.uri;
        if (typing.rest.len == 0) self.typing = null;
        return change(allocator, uri, .{ .start = at, .end = at }, char);
    }

    fn request(self: *Session, allocator: std.mem.Allocator, method: []const u8, uri: ?[]const u8, params: anytype) ![]u8 {
        const id = self.next_id;
        self.next_id += 1;
        self.pending = .{ .id = id, .method = method, .uri = uri orelse "" };
        return std.json.Stringify.valueAlloc(allocator, .{
            .jsonrpc = "2.0",
            .id = id,
            .method = method,
            .params = params,
        }, .{ .emit_null_optional_fields = false });
    }

    fn documentText(self: *Session, uri: []const u8) ?[]const u8 {
        const doc = self.handler.docs.get(uri) orelse return null;
        return doc.text;
    }

    /// A byte offset on a code-point boundary of `text`.
    fn pickIndex(self: *Session, text: []const u8) usize {
        var at = self.smith.index(text.len + 1);
        while (at > 0 and at < text.len and text[at] & 0xC0 == 0x80) at -= 1;
        return at;
    }

    /// A position on a code-point boundary of `text`, or an arbitrary one
    /// up to a line past its end (the server must clamp it).
    fn pickPosition(self: *Session, text: []const u8) Position {
        // lsp-kit's conversions assume valid UTF-8; byte edits can break it.
        if (self.smith.value(bool) and std.unicode.utf8ValidateSlice(text))
            return lsp.offsets.indexToPosition(text, self.pickIndex(text), self.encoding);
        const lines: u32 = @intCast(std.mem.count(u8, text, "\n") + 1);
        return .{
            .line = self.smith.valueRangeAtMost(u32, 0, lines + 1),
            .character = self.smith.valueRangeAtMost(u32, 0, 200),
        };
    }

    fn writeJsonMessage(transport: *lsp.Transport, _: std.Io, message: []const u8) lsp.Transport.WriteError!void {
        const self: *Session = @fieldParentPtr("transport", transport);
        self.check(message) catch |err| switch (err) {
            error.OutOfMemory => @panic("out of memory checking a server message"),
        };
    }

    fn check(self: *Session, message: []const u8) error{OutOfMemory}!void {
        var parsed = std.json.parseFromSlice(std.json.Value, self.gpa, message, .{}) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            else => fail("the server sent a message that is not JSON: {s}", .{message}),
        };
        defer parsed.deinit();
        const root = parsed.value.object;

        var context: []const u8 = "";
        if (root.get("method")) |method| {
            if (std.mem.eql(u8, method.string, "textDocument/publishDiagnostics"))
                context = root.get("params").?.object.get("uri").?.string;
        } else if (self.pending) |pending| {
            if (root.get("id")) |id| if (id == .integer and id.integer == pending.id) {
                if (root.get("error")) |err|
                    fail("well-formed {s} request failed: {f}", .{ pending.method, std.json.fmt(err, .{}) });
                context = pending.uri;
            };
        }
        self.checkRanges(parsed.value, context);
        if (self.pending) |pending| if (root.get("result")) |result| {
            if (std.mem.eql(u8, pending.method, "textDocument/codeAction")) try self.keepActionEdit(result);
            if (std.mem.eql(u8, pending.method, "textDocument/rename")) try self.checkRename(result);
        };
    }

    /// A rename replaces occurrences of one name, and the unit's analysis
    /// after it reports the same diagnostics as before. Checked when the
    /// unit is the two case documents, without an import.
    fn checkRename(self: *Session, result: std.json.Value) !void {
        if (result != .object or self.docs.len != 2) return;
        const changes = (result.object.get("changes") orelse return).object;
        const mm0_text = self.documentText(case_mm0) orelse return;
        const auf_text = self.documentText(case_auf);
        for ([_]?[]const u8{ mm0_text, auf_text }) |text| {
            if (text) |t| if (!std.unicode.utf8ValidateSlice(t)) return;
        }

        var renamed: [2]?[]u8 = .{ null, null };
        defer for (renamed) |text| if (text) |t| self.gpa.free(t);
        var old_name: ?[]const u8 = null;
        var it = changes.iterator();
        while (it.next()) |entry| {
            const uri = entry.key_ptr.*;
            const index: usize = if (std.mem.eql(u8, uri, case_mm0))
                0
            else if (std.mem.eql(u8, uri, case_auf))
                1
            else
                fail("rename edits {s}, outside the unit", .{uri});
            const text = (if (index == 0) mm0_text else auf_text) orelse
                fail("rename edits {s}, which is not open", .{uri});
            renamed[index] = try self.applyRename(text, entry.value_ptr.array.items, &old_name);
        }

        const before = try diagnosticKeys(self.gpa, mm0_text, auf_text);
        defer self.gpa.free(before);
        const after = try diagnosticKeys(
            self.gpa,
            renamed[0] orelse mm0_text,
            if (renamed[1]) |text| text else auf_text,
        );
        defer self.gpa.free(after);
        if (!std.mem.eql(u64, before, after)) fail(
            "renaming `{s}` to `{s}` changed the diagnostics: {d} before, {d} after",
            .{ old_name orelse "", self.rename_to, before.len, after.len },
        );
    }

    /// `text` with the edits of a rename applied; every edit must replace
    /// the same name.
    fn applyRename(self: *Session, text: []const u8, edits: []const std.json.Value, old_name: *?[]const u8) ![]u8 {
        const Span = struct { start: usize, end: usize };
        const spans = try self.gpa.alloc(Span, edits.len);
        defer self.gpa.free(spans);
        for (edits, spans) |edit, *span| {
            const range = edit.object.get("range").?.object;
            span.* = .{
                .start = lsp.offsets.positionToIndex(text, jsonPosition(range.get("start").?), self.encoding),
                .end = lsp.offsets.positionToIndex(text, jsonPosition(range.get("end").?), self.encoding),
            };
            if (!std.mem.eql(u8, edit.object.get("newText").?.string, self.rename_to))
                fail("rename edit writes `{s}`, not `{s}`", .{ edit.object.get("newText").?.string, self.rename_to });
            const name = text[span.start..span.end];
            const expected = old_name.* orelse name;
            old_name.* = expected;
            if (!std.mem.eql(u8, name, expected)) fail("rename replaces both `{s}` and `{s}`", .{ expected, name });
        }
        std.mem.sort(Span, spans, {}, struct {
            fn lessThan(_: void, a: Span, b: Span) bool {
                return a.start < b.start;
            }
        }.lessThan);
        var out: std.ArrayList(u8) = .empty;
        errdefer out.deinit(self.gpa);
        var pos: usize = 0;
        for (spans) |span| {
            if (span.start < pos) fail("rename edits overlap", .{});
            try out.appendSlice(self.gpa, text[pos..span.start]);
            try out.appendSlice(self.gpa, self.rename_to);
            pos = span.end;
        }
        try out.appendSlice(self.gpa, text[pos..]);
        return out.toOwnedSlice(self.gpa);
    }

    /// Walk `value` checking every range against the document of the
    /// nearest enclosing `uri` (or `changes` key).
    fn checkRanges(self: *Session, value: std.json.Value, context: []const u8) void {
        switch (value) {
            .array => |array| for (array.items) |item| self.checkRanges(item, context),
            .object => |object| {
                var uri = context;
                if (object.get("uri")) |u| if (u == .string) {
                    uri = u.string;
                };
                if (object.get("textDocument")) |doc| if (doc == .object) if (doc.object.get("uri")) |u| if (u == .string) {
                    uri = u.string;
                };
                if (object.get("start")) |start| if (object.get("end")) |end| {
                    self.checkRange(start, end, uri);
                    return;
                };
                if (object.get("changes")) |changes| if (changes == .object) {
                    var it = changes.object.iterator();
                    while (it.next()) |entry| self.checkRanges(entry.value_ptr.*, entry.key_ptr.*);
                };
                var it = object.iterator();
                while (it.next()) |entry| {
                    if (std.mem.eql(u8, entry.key_ptr.*, "changes")) continue;
                    self.checkRanges(entry.value_ptr.*, uri);
                }
            },
            else => {},
        }
    }

    fn checkRange(self: *Session, start: std.json.Value, end: std.json.Value, uri: []const u8) void {
        const text = self.documentText(uri) orelse return;
        if (!std.unicode.utf8ValidateSlice(text)) return;
        const a = self.checkPosition(start, text, uri);
        const b = self.checkPosition(end, text, uri);
        if (a.line > b.line or (a.line == b.line and a.character > b.character))
            fail("range in {s} ends before it starts", .{uri});
    }

    fn checkPosition(self: *Session, value: std.json.Value, text: []const u8, uri: []const u8) Position {
        const line = value.object.get("line").?.integer;
        const character = value.object.get("character").?.integer;
        if (line < 0 or character < 0 or line > std.math.maxInt(u32) or character > std.math.maxInt(u32))
            fail("position {d}:{d} in {s} out of range", .{ line, character, uri });
        const pos: Position = .{ .line = @intCast(line), .character = @intCast(character) };
        const back = lsp.offsets.indexToPosition(text, lsp.offsets.positionToIndex(text, pos, self.encoding), self.encoding);
        if (back.line != pos.line or back.character != pos.character)
            fail("position {d}:{d} is not in {s} ({t}); nearest is {d}:{d}", .{ line, character, uri, self.encoding, back.line, back.character });
        return pos;
    }

    /// Remember the document the first returned edit would produce.
    fn keepActionEdit(self: *Session, result: std.json.Value) !void {
        if (result != .array or result.array.items.len == 0) return;
        const action = result.array.items[self.smith.index(result.array.items.len)];
        if (action != .object) return;
        const edit = action.object.get("edit") orelse return;
        const changes = (edit.object.get("changes") orelse return).object;
        var it = changes.iterator();
        const entry = it.next() orelse return;
        const uri = for (self.docs) |doc| {
            if (std.mem.eql(u8, doc.uri, entry.key_ptr.*)) break doc.uri;
        } else return;
        const text = self.documentText(uri) orelse return;
        if (!std.unicode.utf8ValidateSlice(text)) return;
        var out: std.ArrayList(u8) = .empty;
        errdefer out.deinit(self.gpa);
        // Apply from the last edit back so earlier offsets stay put.
        try out.appendSlice(self.gpa, text);
        const edits = entry.value_ptr.array.items;
        var i = edits.len;
        while (i > 0) {
            i -= 1;
            const range = edits[i].object.get("range").?.object;
            const start = lsp.offsets.positionToIndex(out.items, jsonPosition(range.get("start").?), self.encoding);
            const end = lsp.offsets.positionToIndex(out.items, jsonPosition(range.get("end").?), self.encoding);
            if (start > end) return out.deinit(self.gpa);
            try out.replaceRange(self.gpa, start, end - start, edits[i].object.get("newText").?.string);
        }
        if (self.action_result) |old| self.gpa.free(old.text);
        self.action_result = .{ .uri = uri, .text = try out.toOwnedSlice(self.gpa) };
    }
};

/// The analysis's diagnostics as sorted keys of kind, error, severity and
/// document: what a rename must not change (their messages name names).
fn diagnosticKeys(gpa: std.mem.Allocator, mm0_text: []const u8, auf_text: ?[]const u8) ![]u64 {
    var compiler = if (auf_text) |auf| mm0.Compiler.initWithProof(gpa, mm0_text, auf) else mm0.Compiler.init(gpa, mm0_text);
    compiler.analyze() catch |err| if (err == error.OutOfMemory) return error.OutOfMemory;
    var keys: std.ArrayList(u64) = .empty;
    errdefer keys.deinit(gpa);
    for ([_][]const mm0.CompilerDiagnostic{ compiler.primaryDiagnostics(), compiler.warningDiagnostics() }) |diags| {
        for (diags) |diag| {
            try keys.append(gpa, @as(u64, @backingInt(diag.kind)) << 32 |
                @as(u64, @intFromError(diag.err)) << 8 |
                @as(u64, @backingInt(diag.severity)) << 1 |
                @backingInt(diag.source));
        }
    }
    std.mem.sort(u64, keys.items, {}, std.sort.asc(u64));
    return keys.toOwnedSlice(gpa);
}

fn jsonPosition(value: std.json.Value) Position {
    return .{
        .line = @intCast(value.object.get("line").?.integer),
        .character = @intCast(value.object.get("character").?.integer),
    };
}

/// `seed` split after a statement chosen by `smith`: the statements up to
/// it become `lib.mm0` with the proofs of its theorems in `lib.auf`, and
/// the rest `case.mm0`, importing `lib.mm0`, with the other proofs. Null
/// when the seed has no statement to split after or its proofs do not
/// parse.
fn splitSeed(arena: std.mem.Allocator, smith: *Smith, seed: harness.Seed) !?[4]Document {
    // Statement ends: `;` outside math strings and comments.
    var ends: std.ArrayList(usize) = .empty;
    var in_math = false;
    var i: usize = 0;
    while (i < seed.mm0.len) : (i += 1) {
        const c = seed.mm0[i];
        if (!in_math and c == '-' and i + 1 < seed.mm0.len and seed.mm0[i + 1] == '-') {
            i = std.mem.indexOfScalarPos(u8, seed.mm0, i, '\n') orelse seed.mm0.len;
        } else if (c == '$') {
            in_math = !in_math;
        } else if (c == ';' and !in_math) {
            try ends.append(arena, i + 1);
        }
    }
    if (ends.items.len < 2) return null;
    const cut = ends.items[smith.index(ends.items.len - 1)];
    const lib_text = seed.mm0[0..cut];

    var lib_proofs: std.ArrayList(u8) = .empty;
    var case_proofs: std.ArrayList(u8) = .empty;
    var copied: usize = 0;
    var parser = mm0.ProofScript.Parser.init(arena, seed.auf);
    while (parser.nextItem() catch return null) |item| switch (item) {
        .block => |block| if (declares(lib_text, block.name)) {
            try case_proofs.appendSlice(arena, seed.auf[copied..block.span.start]);
            try lib_proofs.appendSlice(arena, seed.auf[block.span.start..block.span.end]);
            try lib_proofs.appendSlice(arena, "\n\n");
            copied = block.span.end;
        },
        .def, .notation => {},
    };
    try case_proofs.appendSlice(arena, seed.auf[copied..]);
    return .{
        .{ .uri = lib_mm0, .source = lib_text },
        .{ .uri = lib_auf, .source = lib_proofs.items },
        .{ .uri = case_mm0, .source = try std.mem.concat(arena, u8, &.{ "import \"lib.mm0\";\n", seed.mm0[cut..] }) },
        .{ .uri = case_auf, .source = case_proofs.items },
    };
}

/// Whether `mm0_text` declares a theorem named `name`.
fn declares(mm0_text: []const u8, name: []const u8) bool {
    var rest = mm0_text;
    while (std.mem.indexOf(u8, rest, "theorem ")) |at| {
        rest = std.mem.trimStart(u8, rest[at + "theorem ".len ..], " \t\n");
        if (std.mem.startsWith(u8, rest, name) and rest.len > name.len) {
            const next = rest[name.len];
            if (std.ascii.isWhitespace(next) or next == '(' or next == ':') return true;
        }
    }
    return false;
}

fn change(allocator: std.mem.Allocator, uri: []const u8, range: lsp.offsets.Range, new_text: []const u8) ![]u8 {
    return notification(allocator, "textDocument/didChange", .{
        .textDocument = .{ .uri = uri, .version = 1 },
        .contentChanges = &.{.{ .range = range, .text = new_text }},
    });
}

fn replace(allocator: std.mem.Allocator, uri: []const u8, new_text: []const u8) ![]u8 {
    return notification(allocator, "textDocument/didChange", .{
        .textDocument = .{ .uri = uri, .version = 1 },
        .contentChanges = &.{.{ .text = new_text }},
    });
}

fn notification(allocator: std.mem.Allocator, method: []const u8, params: anytype) ![]u8 {
    return std.json.Stringify.valueAlloc(allocator, .{
        .jsonrpc = "2.0",
        .method = method,
        .params = params,
    }, .{ .emit_null_optional_fields = false });
}

fn open(allocator: std.mem.Allocator, uri: []const u8, text: []const u8) ![]u8 {
    return notification(allocator, "textDocument/didOpen", .{
        .textDocument = .{
            .uri = uri,
            .languageId = if (std.mem.endsWith(u8, uri, ".mm0")) "metamath-zero" else "aufbau",
            .version = 0,
            .text = text,
        },
    });
}

fn fail(comptime format: []const u8, args: anytype) noreturn {
    std.debug.print(format ++ "\n", args);
    @panic("lsp oracle failed");
}

fn session(seeds: []const harness.Seed, input: harness.Input) !void {
    var handler: server.Handler = undefined;
    var state: Session = .{
        .text_arena = .init(input.gpa),
        .gpa = input.gpa,
        .smith = input.smith,
        .input = input,
        .seed = seeds[input.smith.index(seeds.len)],
        .handler = &handler,
    };
    defer state.deinit();
    handler = server.Handler.init(input.gpa, std.testing.io, &state.transport);
    defer handler.deinit();
    lsp.basic_server.run(std.testing.io, input.gpa, &state.transport, &handler, null) catch |err| switch (err) {
        error.EndOfStream => {},
        else => return err,
    };
}

test "fuzz language server sessions" {
    try harness.run("lsp", .{ .time_limit_s = 30 }, try harness.seeds(), session);
}
