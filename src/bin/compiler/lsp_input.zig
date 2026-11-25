//! The native language server's input: stdin read ahead into a queue, so
//! that the handler's analyses can wait for a quiet moment and stop once
//! newer input makes their result moot.
//!
//! lsp-kit's `basic_server.run` reads one message, handles it, and reads the
//! next. `Input` is the transport it reads from. A message it returns has
//! already been taken off the queue; when the queue is empty and the handler
//! has analyses pending, the read runs them before it blocks on stdin. While
//! an analysis runs, its `AnalysisInterrupt` drains whatever stdin holds
//! into the queue and stops it when the queue holds a message that changes a
//! document or ends the session, or a request to answer. The document stays
//! pending, and the next analysis replays what this one checked.
//!
//! The handler asks the same of the queue while it answers a request: there
//! it means that the client has cancelled that request.
//!
//! A request whose `$/cancelRequest` is queued when it is read off the queue
//! is answered `RequestCancelled` here and never reaches the handler.

const std = @import("std");
const lsp = @import("lsp");
const mm0 = @import("mm0");
const Handler = @import("./lsp.zig").Handler;

const Id = lsp.JsonRPCMessage.ID;

pub const Input = struct {
    transport: lsp.Transport = .{ .vtable = &vtable },
    stdio: lsp.Transport.Stdio,
    allocator: std.mem.Allocator,
    io: std.Io,
    /// Set by `attach`: its pending analyses run when nothing is queued.
    handler: ?*Handler = null,
    /// Messages read and not yet handed to the server loop, oldest first.
    queue: std.ArrayListUnmanaged(Queued) = .empty,
    /// The request the server loop is handling: set when it is read off
    /// the queue, cleared by the next read (owned).
    current: ?Id = null,
    /// Why stdin stopped, once it has; returned when the queue runs dry.
    read_error: ?lsp.Transport.ReadError = null,

    const vtable: lsp.Transport.VTable = .{
        .readJsonMessage = readJsonMessage,
        .writeJsonMessage = writeJsonMessage,
    };

    const Queued = struct {
        json: []u8,
        /// The id of a request (owned).
        request: ?Id,
        /// The request a `$/cancelRequest` names (owned). It follows that
        /// request, so while it is queued the request is still unanswered.
        cancels: ?Id,
        /// A document change, `shutdown` or `exit`.
        changes: bool,
    };

    pub fn init(
        allocator: std.mem.Allocator,
        io: std.Io,
        read_buffer: []u8,
        read_from: std.Io.File,
        write_to: std.Io.File,
    ) Input {
        return .{
            .stdio = lsp.Transport.Stdio.init(read_buffer, read_from, write_to),
            .allocator = allocator,
            .io = io,
        };
    }

    pub fn deinit(self: *Input) void {
        for (self.queue.items) |item| self.freeQueued(item);
        self.queue.deinit(self.allocator);
        if (self.current) |id| self.freeId(id);
        self.* = undefined;
    }

    /// Run `handler`'s pending analyses when nothing is queued, and give
    /// them the interrupt that stops them (`Handler.interrupt`).
    pub fn attach(self: *Input, handler: *Handler) void {
        self.handler = handler;
        handler.interrupt = .{ .context = self, .stopFn = stopRequested };
    }

    fn readJsonMessage(
        transport: *lsp.Transport,
        io: std.Io,
        allocator: std.mem.Allocator,
    ) lsp.Transport.ReadError![]u8 {
        _ = io;
        _ = allocator;
        const self: *Input = @fieldParentPtr("transport", transport);
        if (self.current) |id| self.freeId(id);
        self.current = null;
        while (true) {
            while (self.queue.items.len != 0) {
                const item = self.queue.orderedRemove(0);
                if (item.cancels) |id| self.freeId(id);
                if (item.request) |id| {
                    if (self.isCancelled(id)) {
                        self.answerCancelled(id);
                        self.freeQueued(item);
                        continue;
                    }
                    self.current = id;
                }
                return item.json;
            }
            if (self.read_error) |err| return err;
            if (self.handler) |handler| if (handler.hasPendingAnalysis()) {
                handler.analyzePending() catch |err| switch (err) {
                    error.AnalysisInterrupted => {},
                    else => std.log.err("Failed to analyse: {}", .{err}),
                };
                continue;
            };
            try self.readMessage();
        }
    }

    fn writeJsonMessage(
        transport: *lsp.Transport,
        io: std.Io,
        json_message: []const u8,
    ) lsp.Transport.WriteError!void {
        const self: *Input = @fieldParentPtr("transport", transport);
        return self.stdio.transport.writeJsonMessage(io, json_message);
    }

    /// The `AnalysisInterrupt` the handler polls.
    fn stopRequested(context: *anyopaque) bool {
        const self: *Input = @ptrCast(@alignCast(context));
        self.readWaiting();
        if (self.read_error != null) return true;
        if (self.current) |id| return self.isCancelled(id);
        for (self.queue.items) |item| {
            if (item.changes) return true;
            if (item.request) |id| if (!self.isCancelled(id)) return true;
        }
        return false;
    }

    /// Queue every message stdin already holds, without waiting for more.
    fn readWaiting(self: *Input) void {
        while (self.read_error == null and self.inputWaiting()) {
            self.readMessage() catch |err| {
                self.read_error = err;
            };
        }
    }

    fn inputWaiting(self: *Input) bool {
        if (self.stdio.reader.bufferedLen() != 0) return true;
        var fds = [_]std.posix.pollfd{.{
            .fd = self.stdio.read_from.handle,
            .events = std.posix.POLL.IN,
            .revents = 0,
        }};
        // A failed poll reads as input, so the blocking read reports it.
        const ready = std.posix.poll(&fds, 0) catch return true;
        return ready != 0;
    }

    /// Read one message (waiting for it) and queue it.
    fn readMessage(self: *Input) lsp.Transport.ReadError!void {
        const json = try self.stdio.transport.readJsonMessage(
            self.io,
            self.allocator,
        );
        var item: Queued = .{
            .json = json,
            .request = null,
            .cancels = null,
            .changes = false,
        };
        errdefer self.freeQueued(item);
        try self.classify(&item);
        try self.queue.append(self.allocator, item);
    }

    const Head = struct {
        id: ?Id = null,
        method: ?[]const u8 = null,
        params: ?struct { id: ?Id = null } = null,
    };

    /// Read what the queue needs to know of `item`: its request id, and
    /// whether it cancels a request or changes a document. A message that
    /// does not parse is left for the server loop to report.
    fn classify(self: *Input, item: *Queued) !void {
        var arena = std.heap.ArenaAllocator.init(self.allocator);
        defer arena.deinit();
        const head = std.json.parseFromSliceLeaky(
            Head,
            arena.allocator(),
            item.json,
            .{ .ignore_unknown_fields = true, .max_value_len = null },
        ) catch return;
        const method = head.method orelse return;
        item.changes = isChange(method);
        if (head.id) |id| {
            item.request = try self.dupeId(id);
            return;
        }
        if (!std.mem.eql(u8, method, "$/cancelRequest")) return;
        const params = head.params orelse return;
        item.cancels = try self.dupeId(params.id orelse return);
    }

    fn isChange(method: []const u8) bool {
        const changes = [_][]const u8{
            "textDocument/didOpen",
            "textDocument/didChange",
            "textDocument/didClose",
            "shutdown",
            "exit",
        };
        for (changes) |name| {
            if (std.mem.eql(u8, method, name)) return true;
        }
        return false;
    }

    fn isCancelled(self: *const Input, id: Id) bool {
        for (self.queue.items) |item| {
            const cancels = item.cancels orelse continue;
            if (cancels.eql(id)) return true;
        }
        return false;
    }

    fn answerCancelled(self: *Input, id: Id) void {
        self.stdio.transport.writeErrorResponse(
            self.io,
            self.allocator,
            id,
            .{
                .code = @fromBackingInt(@intCast(@backingInt(lsp.types.LSPErrorCodes.RequestCancelled))),
                .message = "RequestCancelled",
            },
            .{ .emit_null_optional_fields = false },
        ) catch |err| std.log.err("Failed to answer a cancelled request: {}", .{err});
    }

    fn dupeId(self: *Input, id: Id) !Id {
        return switch (id) {
            .number => id,
            .string => |text| .{ .string = try self.allocator.dupe(u8, text) },
        };
    }

    fn freeId(self: *Input, id: Id) void {
        switch (id) {
            .number => {},
            .string => |text| self.allocator.free(text),
        }
    }

    fn freeQueued(self: *Input, item: Queued) void {
        self.allocator.free(item.json);
        if (item.request) |id| self.freeId(id);
        if (item.cancels) |id| self.freeId(id);
    }
};
