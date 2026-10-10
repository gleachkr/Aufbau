//! Fuzz target: language-server sessions, in process.
//!
//! The session runs lsp-kit's own server loop (as `abc lsp` and the browser
//! do) over a transport that writes the client's half on demand: initialize
//! with a random position encoding, open a proof case's `.mm0` and `.auf`
//! (maybe edited), then edits (insertions, deletions, whole-document
//! replacements, typing a token one character at a time), requests at
//! random or real positions, closing and reopening, applying an edit a code
//! action returned, and malformed messages. The server must not panic,
//! leak or hang, every message it sends must be JSON, a well-formed request
//! must not fail, and every range it returns must lie inside its document
//! on a code-point boundary of the negotiated encoding.
const std = @import("std");
const lsp = @import("lsp");
const server = @import("lsp_server");
const harness = @import("harness.zig");
const mutate = @import("mutate.zig");

const Encoding = lsp.offsets.Encoding;
const Position = lsp.offsets.Position;
const Smith = std.testing.Smith;
/// Serializes as `{}`; an empty `.{}` is a tuple and serializes as `[]`.
const Empty = struct {};

/// At most this many client events after the documents open.
const max_events = 32;

const uris = [_][]const u8{ "file:///fuzz/case.mm0", "file:///fuzz/case.auf" };

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
    /// The document text the last code action's edit would produce.
    action_result: ?struct { uri: []const u8, text: []u8 } = null,
    /// The second document to open, sent right after the first.
    queued: ?[]u8 = null,
    /// Every client message, written out when replaying.
    log: std.ArrayList(u8) = .empty,

    const vtable: lsp.Transport.VTable = .{
        .readJsonMessage = readJsonMessage,
        .writeJsonMessage = writeJsonMessage,
    };

    fn deinit(self: *Session) void {
        if (self.action_result) |result| self.gpa.free(result.text);
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
                // Open the proof file first or second, or not at all.
                const auf = try self.editedSeed(self.seed.auf, self.seed.mm0);
                defer self.gpa.free(auf);
                const mm0 = try self.editedSeed(self.seed.mm0, self.seed.auf);
                defer self.gpa.free(mm0);
                return switch (self.smith.valueRangeAtMost(u8, 0, 2)) {
                    0 => self.openThenQueue(allocator, uris[0], mm0, uris[1], auf),
                    1 => self.openThenQueue(allocator, uris[1], auf, uris[0], mm0),
                    else => open(allocator, uris[0], mm0),
                };
            },
            .events => {
                if (self.queued) |queued| {
                    self.queued = null;
                    return queued;
                }
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

    fn openThenQueue(self: *Session, allocator: std.mem.Allocator, first_uri: []const u8, first: []const u8, second_uri: []const u8, second: []const u8) ![]u8 {
        self.queued = try open(allocator, second_uri, second);
        return open(allocator, first_uri, first);
    }

    fn editedSeed(self: *Session, text: []const u8, other: []const u8) ![]u8 {
        if (self.smith.value(bool)) return mutate.mutate(self.gpa, self.smith, text, other);
        return self.gpa.dupe(u8, text);
    }

    fn event(self: *Session, allocator: std.mem.Allocator) ![]u8 {
        const uri = uris[self.smith.index(uris.len)];
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
            .reopen => {
                const source = if (uri.ptr == uris[0].ptr) self.seed.mm0 else self.seed.auf;
                return open(allocator, uri, source);
            },
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

    fn typeNext(self: *Session, allocator: std.mem.Allocator) ![]u8 {
        const typing = &self.typing.?;
        const text = self.documentText(typing.uri) orelse "";
        const index = @min(typing.index, text.len);
        const at = lsp.offsets.indexToPosition(text, index, self.encoding);
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
        if (self.smith.value(bool)) return lsp.offsets.indexToPosition(text, self.pickIndex(text), self.encoding);
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
        if (self.pending) |pending| if (std.mem.eql(u8, pending.method, "textDocument/codeAction")) {
            if (root.get("result")) |result| try self.keepActionEdit(result);
        };
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
        const uri = for (uris) |known| {
            if (std.mem.eql(u8, known, entry.key_ptr.*)) break known;
        } else return;
        const text = self.documentText(uri) orelse return;
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

fn jsonPosition(value: std.json.Value) Position {
    return .{
        .line = @intCast(value.object.get("line").?.integer),
        .character = @intCast(value.object.get("character").?.integer),
    };
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
    try harness.run("lsp", try harness.seeds(), session);
}
