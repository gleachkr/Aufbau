const std = @import("std");
const lsp = @import("lsp");
const mm0 = @import("mm0");
const lsp_server = @import("../lsp.zig");
const Handler = lsp_server.Handler;
const pathToUri = lsp_server.pathToUri;
const Input = @import("../lsp_input.zig").Input;
const queued_hole_value = "Inferred expression:\n\n```mm0\n$ top $\n```";

const queued_mm0_text = "--| @hole _wff\n" ++
    \\provable sort wff;
    \\term top: wff;
    \\axiom top_i: $ top $;
    \\term bot: wff;
    \\axiom bot_i: $ bot $;
    \\theorem main: $ top $;
;

/// Three lemmas and the theorem they come before, proved by one holey line
/// each, the theorem's by `last_rule`.
fn queuedProofText(comptime last_rule: []const u8) []const u8 {
    return
    \\lemma a: $ top $
    \\----
    \\l1: $ _wff $ by top_i []
    \\
    \\lemma b: $ top $
    \\----
    \\l1: $ _wff $ by top_i []
    \\
    \\lemma c: $ top $
    \\----
    \\l1: $ _wff $ by top_i []
    \\
    \\main
    \\----
    \\
    ++ "l1: $ _wff $ by " ++ last_rule ++ " []\n";
}

/// The hole on the line of lemma `a`.
const queued_hole = .{ .line = 2, .character = 7 };

/// A client of the server over pipes. The server stops at the first poll
/// that finds a message, and runs its analyses as soon as it has read one,
/// so what is sent before `start` decides where each analysis stops.
const StdioClient = struct {
    mm0_uri: []const u8 = "file:///tmp/lsp-queue/main.mm0",
    proof_uri: []const u8 = "file:///tmp/lsp-queue/main.auf",
    /// Another file whose diagnostics are reported (`Event.library_published`).
    library_uri: ?[]const u8 = null,
    /// Whether the server shows its checks' progress (`initializeWithProgress`).
    progress: bool = false,
    /// How long a check runs before its progress shows.
    progress_delay_ns: i96 = 0,
    /// The last percentage the progress reported, and how many reports came.
    percentage: i64 = -1,
    reports: usize = 0,

    arena_state: std.heap.ArenaAllocator,
    to_server: [2]std.Io.File,
    from_server: [2]std.Io.File,
    read_buffer: [4096]u8 = undefined,
    stdio: lsp.Transport.Stdio = undefined,
    server: ?std.Thread = null,

    fn init(self: *StdioClient) !void {
        self.* = .{
            .arena_state = std.heap.ArenaAllocator.init(std.heap.page_allocator),
            .to_server = try pipe(),
            .from_server = try pipe(),
        };
        self.stdio = .init(&self.read_buffer, self.from_server[0], self.to_server[1]);
    }

    fn pipe() ![2]std.Io.File {
        const fds = try std.Io.Threaded.pipe2(.{});
        return .{
            .{ .handle = fds[0], .flags = .{ .nonblocking = false } },
            .{ .handle = fds[1], .flags = .{ .nonblocking = false } },
        };
    }

    /// Ends a server still running: its stdin ends.
    fn deinit(self: *StdioClient) void {
        const io = std.testing.io;
        self.to_server[1].close(io);
        if (self.server) |thread| thread.join();
        self.to_server[0].close(io);
        for (self.from_server) |end| end.close(io);
        self.arena_state.deinit();
    }

    fn start(self: *StdioClient) !void {
        self.server = try std.Thread.spawn(
            .{},
            serve,
            .{ self.to_server[0], self.from_server[1], self.progress_delay_ns },
        );
    }

    fn serve(read_from: std.Io.File, write_to: std.Io.File, progress_delay_ns: i96) void {
        const allocator = std.testing.allocator;
        const io = std.testing.io;
        var read_buffer: [4096]u8 = undefined;
        var input = Input.init(allocator, io, &read_buffer, read_from, write_to);
        defer input.deinit();
        var handler = Handler.init(allocator, io, &input.transport);
        defer handler.deinit();
        handler.progress_delay_ns = progress_delay_ns;
        input.attach(&handler);
        lsp.basic_server.run(io, allocator, &input.transport, &handler, null) catch {};
    }

    /// Say that the client shows progress the server starts; the server
    /// shows a check's once it has run `progress_delay_ns`.
    fn initializeWithProgress(self: *StdioClient) !void {
        self.progress = true;
        try self.send(.{ .jsonrpc = "2.0", .id = 0, .method = "initialize", .params = .{
            .capabilities = .{ .window = .{ .workDoneProgress = true } },
        } });
        try self.send(.{ .jsonrpc = "2.0", .method = "initialized", .params = struct {}{} });
    }

    fn send(self: *StdioClient, message: anytype) !void {
        try self.write(try self.frame(message));
    }

    /// `message` as it goes over the pipe.
    fn frame(self: *StdioClient, message: anytype) ![]const u8 {
        const arena = self.arena_state.allocator();
        const json = try std.json.Stringify.valueAlloc(arena, message, .{});
        return std.fmt.allocPrint(
            arena,
            "Content-Length: {d}\r\n\r\n{s}",
            .{ json.len, json },
        );
    }

    fn write(self: *StdioClient, bytes: []const u8) !void {
        try self.to_server[1].writeStreamingAll(std.testing.io, bytes);
    }

    fn open(self: *StdioClient, uri: []const u8, text: []const u8) !void {
        try self.send(.{ .jsonrpc = "2.0", .method = "textDocument/didOpen", .params = .{
            .textDocument = .{ .uri = uri, .languageId = "aufbau", .version = 1, .text = text },
        } });
    }

    fn openBoth(self: *StdioClient) !void {
        try self.open(self.mm0_uri, queued_mm0_text);
        try self.open(self.proof_uri, queuedProofText("top_i"));
    }

    fn change(self: *StdioClient, version: i32, text: []const u8) !void {
        try self.write(try self.changeFrame(version, text));
    }

    fn changeFrame(self: *StdioClient, version: i32, text: []const u8) ![]const u8 {
        return self.frame(.{ .jsonrpc = "2.0", .method = "textDocument/didChange", .params = .{
            .textDocument = .{ .uri = self.proof_uri, .version = version },
            .contentChanges = .{.{ .text = text }},
        } });
    }

    fn hoverHole(self: *StdioClient, id: i64) !void {
        try self.write(try self.hoverFrame(id, self.proof_uri));
    }

    fn hoverFrame(self: *StdioClient, id: i64, uri: []const u8) ![]const u8 {
        return self.frame(.{ .jsonrpc = "2.0", .id = id, .method = "textDocument/hover", .params = .{
            .textDocument = .{ .uri = uri },
            .position = queued_hole,
        } });
    }

    fn outline(self: *StdioClient, id: i64) !void {
        try self.send(.{
            .jsonrpc = "2.0",
            .id = id,
            .method = "textDocument/documentSymbol",
            .params = .{ .textDocument = .{ .uri = self.proof_uri } },
        });
    }

    fn cancel(self: *StdioClient, id: i64) !void {
        try self.send(.{
            .jsonrpc = "2.0",
            .method = "$/cancelRequest",
            .params = .{ .id = id },
        });
    }

    const Event = union(enum) {
        /// The proof file's diagnostics: how many, for which version.
        published: struct { version: i64, count: usize },
        /// How many diagnostics the library file has.
        library_published: usize,
        /// A progress made or ended (its reports are checked to rise).
        progress: enum { create, end },
        /// A progress begun, at this percentage.
        progress_begin: i64,
        /// A request answered, with the value of a hole hover.
        answered: struct { id: i64, value: ?[]const u8 = null },
        failed: struct { id: i64, code: i64 },
    };

    /// The next message about the proof file.
    fn next(self: *StdioClient) !Event {
        const arena = self.arena_state.allocator();
        while (true) {
            if (self.stdio.reader.bufferedLen() == 0) {
                var fds = [_]std.posix.pollfd{.{
                    .fd = self.from_server[0].handle,
                    .events = std.posix.POLL.IN,
                    .revents = 0,
                }};
                if (try std.posix.poll(&fds, 20_000) == 0) return error.ServerIsQuiet;
            }
            const json = try self.stdio.transport.readJsonMessage(std.testing.io, arena);
            const message = try std.json.parseFromSliceLeaky(std.json.Value, arena, json, .{});
            const object = message.object;
            if (object.get("method")) |method| {
                if (self.progress) if (try self.progressEvent(method.string, object)) |event| {
                    return event;
                };
                if (!std.mem.eql(u8, method.string, "textDocument/publishDiagnostics")) continue;
                const params = object.get("params").?.object;
                const uri = params.get("uri").?.string;
                if (self.library_uri) |library| if (std.mem.eql(u8, uri, library)) {
                    return .{ .library_published = params.get("diagnostics").?.array.items.len };
                };
                if (!std.mem.eql(u8, uri, self.proof_uri)) continue;
                return .{ .published = .{
                    .version = params.get("version").?.integer,
                    .count = params.get("diagnostics").?.array.items.len,
                } };
            }
            const id = object.get("id").?.integer;
            if (object.get("error")) |failure| {
                return .{ .failed = .{ .id = id, .code = failure.object.get("code").?.integer } };
            }
            const result = object.get("result").?;
            if (result != .object) return .{ .answered = .{ .id = id } };
            const contents = result.object.get("contents") orelse
                return .{ .answered = .{ .id = id } };
            return .{ .answered = .{
                .id = id,
                .value = contents.object.get("value").?.string,
            } };
        }
    }

    /// The progress event `method` is, if any; a report is checked to rise
    /// from the last percentage and is no event.
    fn progressEvent(
        self: *StdioClient,
        method: []const u8,
        object: std.json.ObjectMap,
    ) !?Event {
        if (std.mem.eql(u8, method, "window/workDoneProgress/create")) {
            self.percentage = -1;
            return .{ .progress = .create };
        }
        if (!std.mem.eql(u8, method, "$/progress")) return null;
        const value = object.get("params").?.object.get("value").?.object;
        const kind = value.get("kind").?.string;
        if (std.mem.eql(u8, kind, "end")) return .{ .progress = .end };
        const percentage = value.get("percentage").?.integer;
        try std.testing.expect(percentage > self.percentage);
        self.percentage = percentage;
        if (std.mem.eql(u8, kind, "begin")) return .{ .progress_begin = percentage };
        self.reports += 1;
        return null;
    }

    fn expect(self: *StdioClient, expected: []const Event) !void {
        for (expected) |event| try std.testing.expectEqualDeep(event, try self.next());
    }

    /// Expect no further message about the proof file.
    fn expectEnd(self: *StdioClient) !void {
        try self.send(.{ .jsonrpc = "2.0", .id = 99, .method = "shutdown" });
        try self.expect(&.{.{ .answered = .{ .id = 99 } }});
    }
};

test "LSP over stdio analyses queued edits once" {
    var client: StdioClient = undefined;
    try client.init();
    defer client.deinit();
    try client.openBoth();
    try client.change(2, queuedProofText("nope"));
    try client.change(3, queuedProofText("top_i"));
    try client.start();
    // Neither the opened text nor the broken edit is published: their
    // analyses were stopped.
    try client.expect(&.{.{ .published = .{ .version = 3, .count = 0 } }});
    try client.change(4, queuedProofText("nope"));
    try client.expect(&.{.{ .published = .{ .version = 4, .count = 1 } }});
    try client.expectEnd();
}

test "LSP over stdio answers requests before an analysis ends" {
    var client: StdioClient = undefined;
    try client.init();
    defer client.deinit();
    try client.openBoth();
    try client.hoverHole(1);
    try client.cancel(1);
    try client.outline(2);
    try client.start();
    try client.expect(&.{
        .{ .failed = .{ .id = 1, .code = -32800 } },
        .{ .answered = .{ .id = 2 } },
        .{ .published = .{ .version = 1, .count = 0 } },
    });
    try client.expectEnd();
}

test "LSP over stdio shows a hole's value before the analysis ends" {
    var client: StdioClient = undefined;
    try client.init();
    defer client.deinit();
    try client.openBoth();
    try client.hoverHole(1);
    try client.change(2, queuedProofText("nope"));
    try client.start();
    try client.expect(&.{
        .{ .answered = .{ .id = 1, .value = queued_hole_value } },
        .{ .published = .{ .version = 2, .count = 1 } },
    });
    try client.hoverHole(2);
    try client.expect(&.{.{ .answered = .{ .id = 2, .value = queued_hole_value } }});
    try client.expectEnd();
}

test "LSP over stdio shows the hole values of the text a hover is about" {
    var client: StdioClient = undefined;
    try client.init();
    defer client.deinit();
    try client.openBoth();
    try client.start();
    try client.expect(&.{.{ .published = .{ .version = 1, .count = 0 } }});
    // In one write, so that the hover is there when the analysis of the edit
    // first looks: the value then known is the old text's.
    const edited = try std.mem.replaceOwned(
        u8,
        client.arena_state.allocator(),
        queuedProofText("top_i"),
        "lemma a: $ top $\n----\nl1: $ _wff $ by top_i",
        "lemma a: $ bot $\n----\nl1: $ _wff $ by bot_i",
    );
    try client.write(try std.mem.concat(client.arena_state.allocator(), u8, &.{
        try client.changeFrame(2, edited),
        try client.hoverFrame(1, client.proof_uri),
    }));
    try client.expect(&.{
        .{ .answered = .{ .id = 1, .value = "Inferred expression:\n\n```mm0\n$ bot $\n```" } },
        .{ .published = .{ .version = 2, .count = 0 } },
    });
    try client.expectEnd();
}

test "LSP over stdio answers about a library file while its root is checked" {
    var client: StdioClient = undefined;
    try client.init();
    defer client.deinit();
    const lib_uri = "file:///tmp/lsp-queue/lib.auf";
    try client.open(lib_uri,
        \\lemma z: $ top $
        \\----
        \\l1: $ _wff $ by top_i []
        \\
    );
    try client.open(client.mm0_uri, queued_mm0_text);
    try client.open(client.proof_uri, "include \"lib.auf\";\n" ++ comptime queuedProofText("top_i"));
    try client.write(try client.hoverFrame(1, lib_uri));
    try client.start();
    try client.expect(&.{
        .{ .answered = .{ .id = 1, .value = queued_hole_value } },
        .{ .published = .{ .version = 1, .count = 0 } },
    });
    try client.expectEnd();
}

/// A directory with a library proof file in it, `lib.auf`: a proof that
/// fails, and a block no theorem claims, which the walk reports whether or
/// not the proofs are checked.
const LibraryDir = struct {
    tmp: std.testing.TmpDir,
    dir: []const u8,

    fn init(self: *LibraryDir, arena: std.mem.Allocator) !void {
        const io = std.testing.io;
        self.tmp = std.testing.tmpDir(.{});
        try self.tmp.dir.writeFile(io, .{
            .sub_path = "lib.auf",
            .data = "lemma z: $ top $\n----\nl1: $ top $ by nope []\n\n" ++
                "ghost\n----\nl1: $ top $ by top_i []\n",
        });
        self.dir = try self.tmp.dir.realPathFileAlloc(io, ".", arena);
    }

    fn uri(self: *const LibraryDir, arena: std.mem.Allocator, name: []const u8) ![]const u8 {
        return pathToUri(arena, try std.fs.path.join(arena, &.{ self.dir, name }));
    }
};

test "LSP over stdio publishes the open file's diagnostics before its libraries'" {
    var client: StdioClient = undefined;
    try client.init();
    defer client.deinit();
    const arena = client.arena_state.allocator();
    var library: LibraryDir = undefined;
    try library.init(arena);
    defer library.tmp.cleanup();
    client.mm0_uri = try library.uri(arena, "main.mm0");
    client.proof_uri = try library.uri(arena, "main.auf");
    client.library_uri = try library.uri(arena, "lib.auf");
    try client.initializeWithProgress();
    try client.open(client.mm0_uri, queued_mm0_text);
    try client.open(client.proof_uri, "include \"lib.auf\";\n" ++ comptime queuedProofText("nope"));
    try client.start();
    const checks = [_]StdioClient.Event{
        .{ .progress = .create },
        .{ .progress_begin = 0 },
        // The open file's proofs alone, then all of them, with the progress
        // rising across both.
        .{ .published = .{ .version = 1, .count = 1 } },
        .{ .published = .{ .version = 1, .count = 1 } },
        .{ .library_published = 2 },
        .{ .progress = .end },
    };
    try client.expect(&.{.{ .answered = .{ .id = 0 } }});
    try client.expect(&checks);
    try std.testing.expect(client.reports != 0);
    // A theory edit every check sees: the library's errors stand until its
    // proofs are checked again.
    try client.send(.{ .jsonrpc = "2.0", .method = "textDocument/didChange", .params = .{
        .textDocument = .{ .uri = client.mm0_uri, .version = 2 },
        .contentChanges = .{.{ .text = "sort extra;\n" ++ queued_mm0_text }},
    } });
    try client.expect(&checks);
    try client.expectEnd();
}

test "LSP over stdio checks the open files of every root before their libraries" {
    var client: StdioClient = undefined;
    try client.init();
    defer client.deinit();
    const arena = client.arena_state.allocator();
    var library: LibraryDir = undefined;
    try library.init(arena);
    defer library.tmp.cleanup();
    for ([_][]const u8{ "main.mm0", "other.mm0" }) |name| {
        try library.tmp.dir.writeFile(std.testing.io, .{ .sub_path = name, .data = queued_mm0_text });
    }
    client.proof_uri = try library.uri(arena, "main.auf");
    // The other root's diagnostics.
    client.library_uri = try library.uri(arena, "other.auf");
    try client.open(client.proof_uri, "include \"lib.auf\";\n" ++ comptime queuedProofText("nope"));
    // Stops the first check, so both roots are pending.
    try client.open(client.library_uri.?, "include \"lib.auf\";\n" ++ comptime queuedProofText("top_i"));
    try client.start();
    try client.expect(&.{
        .{ .published = .{ .version = 1, .count = 1 } },
        .{ .library_published = 0 },
        .{ .published = .{ .version = 1, .count = 1 } },
        .{ .library_published = 0 },
    });
    try client.expectEnd();
}

test "LSP over stdio shows a check's progress through the requests that stop it" {
    var client: StdioClient = undefined;
    try client.init();
    defer client.deinit();
    try client.initializeWithProgress();
    try client.openBoth();
    try client.hoverHole(1);
    try client.start();
    try client.expect(&.{
        .{ .answered = .{ .id = 0 } },
        .{ .progress = .create },
        .{ .progress_begin = 0 },
        .{ .answered = .{ .id = 1, .value = queued_hole_value } },
        .{ .published = .{ .version = 1, .count = 0 } },
        .{ .progress = .end },
    });
    try client.expectEnd();
}

test "LSP over stdio shows no progress for a check shorter than the delay" {
    var client: StdioClient = undefined;
    try client.init();
    defer client.deinit();
    client.progress_delay_ns = std.time.ns_per_hour;
    try client.initializeWithProgress();
    try client.openBoth();
    try client.start();
    try client.expect(&.{
        .{ .answered = .{ .id = 0 } },
        .{ .published = .{ .version = 1, .count = 0 } },
    });
    try client.expectEnd();
}

test "LSP over stdio ends a check's progress at an edit" {
    var client: StdioClient = undefined;
    try client.init();
    defer client.deinit();
    try client.initializeWithProgress();
    try client.openBoth();
    try client.change(2, queuedProofText("nope"));
    try client.start();
    try client.expect(&.{
        .{ .answered = .{ .id = 0 } },
        .{ .progress = .create },
        .{ .progress_begin = 0 },
        .{ .progress = .end },
        // The stopped check checked lemma a: the new one starts at b.
        .{ .progress = .create },
        .{ .progress_begin = 26 },
        .{ .published = .{ .version = 2, .count = 1 } },
        .{ .progress = .end },
    });
    try client.expectEnd();
}

test "LSP input stops an analysis for a request, but not for a cancelled one" {
    var client: StdioClient = undefined;
    try client.init();
    defer client.deinit();

    var read_buffer: [4096]u8 = undefined;
    var input = Input.init(
        std.testing.allocator,
        std.testing.io,
        &read_buffer,
        client.to_server[0],
        client.from_server[1],
    );
    defer input.deinit();
    var handler = Handler.init(std.testing.allocator, std.testing.io, &input.transport);
    defer handler.deinit();
    input.attach(&handler);
    const interrupt = handler.interrupt.?;

    try std.testing.expect(!interrupt.stopRequested());
    try client.hoverHole(1);
    try client.cancel(1);
    try std.testing.expect(!interrupt.stopRequested());
    try client.hoverHole(2);
    try std.testing.expect(interrupt.stopRequested());
    // While the server loop handles a request, only its cancellation counts.
    input.current = .{ .number = 3 };
    try std.testing.expect(!interrupt.stopRequested());
    try client.cancel(3);
    try std.testing.expect(interrupt.stopRequested());
}
