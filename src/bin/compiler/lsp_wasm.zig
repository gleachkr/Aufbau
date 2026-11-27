const std = @import("std");
const lsp = @import("lsp");
const mm0 = @import("mm0");
const compiler_lsp = @import("./lsp.zig");

const host = @import("./wasm_host.zig");
const allocator = host.allocator;
const ptrToConstSlice = host.ptrToConstSlice;
const slicePtr = host.slicePtr;

// The host's `alloc`, `free` and `set_locale` are this module's exports too.
comptime {
    _ = &host.alloc;
    _ = &host.free;
    _ = &host.set_locale;
}

var result_lsp: []u8 = &.{};
var lsp_handler: compiler_lsp.Handler = undefined;
var lsp_handler_initialized = false;
var browser_transport: BrowserTransport = .{};

pub export fn process_lsp_message(message_ptr: u32, message_len: u32) u32 {
    clearLspResult();
    if (!lsp_handler_initialized) {
        lsp_handler = compiler_lsp.Handler.init(
            allocator,
            browser_io,
            &browser_transport.transport,
            .serial,
        );
        lsp_handler_initialized = true;
    }

    browser_transport.reset(ptrToConstSlice(message_ptr, message_len));
    lsp.basic_server.run(
        browser_io,
        allocator,
        &browser_transport.transport,
        &lsp_handler,
        null,
    ) catch |err| switch (err) {
        error.EndOfStream => {},
        else => {
            writeLspError(err) catch clearLspResult();
            return 0;
        },
    };

    result_lsp = allocator.dupe(u8, browser_transport.output.items) catch {
        clearLspResult();
        return 0;
    };
    return 1;
}

pub export fn reset_lsp_server() void {
    clearLspResult();
    browser_transport.deinit();
    if (lsp_handler_initialized) {
        lsp_handler.deinit();
        lsp_handler_initialized = false;
    }
}

pub export fn result_lsp_ptr() u32 {
    return slicePtr(result_lsp);
}

pub export fn result_lsp_len() u32 {
    return @intCast(result_lsp.len);
}

fn clearLspResult() void {
    if (result_lsp.len != 0) allocator.free(result_lsp);
    result_lsp = &.{};
}

/// The browser host does no I/O of its own: messages arrive and leave
/// through `BrowserTransport`, and the handler's disk reads get
/// FileNotFound from `std.Io.failing`.
const browser_io = std.Io.failing;

/// Freestanding has no working directory for `std.Io.Dir.cwd()` to name; the
/// handler's reads go through `browser_io`, which never looks at the handle.
pub fn std_options_cwd() std.Io.Dir {
    return .{ .handle = {} };
}

const BrowserTransport = struct {
    transport: lsp.Transport = .{ .vtable = &vtable },
    input: []const u8 = &.{},
    consumed: bool = true,
    output: std.ArrayListUnmanaged(u8) = .empty,

    const vtable: lsp.Transport.VTable = .{
        .readJsonMessage = readJsonMessage,
        .writeJsonMessage = writeJsonMessage,
    };

    fn reset(self: *BrowserTransport, input: []const u8) void {
        self.input = input;
        self.consumed = false;
        self.output.clearRetainingCapacity();
    }

    fn deinit(self: *BrowserTransport) void {
        self.output.deinit(allocator);
        self.* = .{};
    }

    fn readJsonMessage(
        transport: *lsp.Transport,
        io: std.Io,
        arena: std.mem.Allocator,
    ) lsp.Transport.ReadError![]u8 {
        _ = io;
        const self: *BrowserTransport = @fieldParentPtr(
            "transport",
            transport,
        );
        if (self.consumed) return error.EndOfStream;
        self.consumed = true;
        return try arena.dupe(u8, self.input);
    }

    fn writeJsonMessage(
        transport: *lsp.Transport,
        io: std.Io,
        json_message: []const u8,
    ) lsp.Transport.WriteError!void {
        _ = io;
        const self: *BrowserTransport = @fieldParentPtr(
            "transport",
            transport,
        );
        // `WriteError` has no `OutOfMemory`; the nearest member is reported
        // and `process_lsp_message` turns it into a JSON-RPC error.
        self.output.appendSlice(allocator, json_message) catch
            return error.SystemResources;
        self.output.append(allocator, '\n') catch
            return error.SystemResources;
    }
};

fn writeLspError(err: anyerror) !void {
    var out: std.Io.Writer.Allocating = .init(allocator);
    errdefer out.deinit();
    try std.json.Stringify.value(.{
        .jsonrpc = "2.0",
        .@"error" = .{ .code = -32603, .message = @errorName(err) },
    }, .{}, &out.writer);
    try out.writer.writeByte('\n');
    result_lsp = try out.toOwnedSlice();
}
