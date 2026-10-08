const std = @import("std");

pub const types = @import("types");
pub const offsets = @import("offsets");

pub const JsonRPCMessage = union(enum) {
    request: Request,
    notification: Notification,
    response: Response,

    pub const ID = union(enum) {
        number: i64,
        string: []const u8,

        pub fn jsonStringify(self: ID, stream: anytype) !void {
            switch (self) {
                .number => |value| try stream.write(value),
                .string => |value| try stream.write(value),
            }
        }
    };

    pub const Request = struct {
        id: ID,
        method: []const u8,
        params: ?std.json.Value,
    };

    pub const Notification = struct {
        method: []const u8,
        params: ?std.json.Value,
    };

    pub const Response = struct {
        id: ?ID,
        result_or_error: union(enum) {
            result: ?std.json.Value,
            @"error": Error,
        },

        pub const Error = struct {
            code: Code,
            message: []const u8,
            data: ?std.json.Value = null,

            pub const Code = enum(i64) {
                parse_error = -32700,
                invalid_request = -32600,
                method_not_found = -32601,
                invalid_params = -32602,
                internal_error = -32603,
                _,

                pub fn jsonStringify(code: Code, stream: anytype) !void {
                    try stream.write(@intFromEnum(code));
                }
            };
        };
    };
};

pub const Transport = struct {
    vtable: *const VTable,

    pub const VTable = struct {
        readJsonMessage: *const fn (
            transport: *Transport,
            allocator: std.mem.Allocator,
        ) ReadError![]u8,
        writeJsonMessage: *const fn (
            transport: *Transport,
            json_message: []const u8,
        ) WriteError!void,
    };

    pub const ReadError = error{EndOfStream} || std.mem.Allocator.Error;
    pub const WriteError = error{};

    pub fn readJsonMessage(
        transport: *Transport,
        allocator: std.mem.Allocator,
    ) ReadError![]u8 {
        return try transport.vtable.readJsonMessage(transport, allocator);
    }

    pub fn writeJsonMessage(
        transport: *Transport,
        json_message: []const u8,
    ) WriteError!void {
        return try transport.vtable.writeJsonMessage(transport, json_message);
    }

    pub fn writeNotification(
        transport: *Transport,
        allocator: std.mem.Allocator,
        method: []const u8,
        comptime Params: type,
        params: Params,
        options: std.json.Stringify.Options,
    ) std.mem.Allocator.Error!void {
        const message = TypedJsonRPCNotification(Params){
            .method = method,
            .params = params,
        };
        const json_message = try std.json.Stringify.valueAlloc(
            allocator,
            message,
            options,
        );
        defer allocator.free(json_message);
        try transport.writeJsonMessage(json_message);
    }

    pub fn writeResponse(
        transport: *Transport,
        allocator: std.mem.Allocator,
        id: ?JsonRPCMessage.ID,
        comptime Result: type,
        result: Result,
        options: std.json.Stringify.Options,
    ) std.mem.Allocator.Error!void {
        const message = TypedJsonRPCResponse(Result){
            .id = id,
            .result_or_error = .{ .result = result },
        };
        const json_message = try std.json.Stringify.valueAlloc(
            allocator,
            message,
            options,
        );
        defer allocator.free(json_message);
        try transport.writeJsonMessage(json_message);
    }

    pub fn writeErrorResponse(
        transport: *Transport,
        allocator: std.mem.Allocator,
        id: ?JsonRPCMessage.ID,
        err: JsonRPCMessage.Response.Error,
        options: std.json.Stringify.Options,
    ) std.mem.Allocator.Error!void {
        const message = TypedJsonRPCResponse(void){
            .id = id,
            .result_or_error = .{ .@"error" = err },
        };
        const json_message = try std.json.Stringify.valueAlloc(
            allocator,
            message,
            options,
        );
        defer allocator.free(json_message);
        try transport.writeJsonMessage(json_message);
    }
};

pub fn TypedJsonRPCNotification(comptime Params: type) type {
    return struct {
        comptime jsonrpc: []const u8 = "2.0",
        method: []const u8,
        params: ?Params,

        pub fn jsonStringify(self: @This(), stream: anytype) !void {
            try stream.beginObject();
            try stream.objectField("jsonrpc");
            try stream.write("2.0");
            try stream.objectField("method");
            try stream.write(self.method);
            if (self.params) |params| {
                try stream.objectField("params");
                if (Params == void) {
                    try stream.write(null);
                } else {
                    try stream.write(params);
                }
            }
            try stream.endObject();
        }
    };
}

pub fn TypedJsonRPCResponse(comptime Result: type) type {
    return struct {
        id: ?JsonRPCMessage.ID,
        result_or_error: union(enum) {
            result: Result,
            @"error": JsonRPCMessage.Response.Error,
        },

        pub fn jsonStringify(self: @This(), stream: anytype) !void {
            try stream.beginObject();
            try stream.objectField("jsonrpc");
            try stream.write("2.0");
            try stream.objectField("id");
            try stream.write(self.id);
            switch (self.result_or_error) {
                .result => |result| {
                    try stream.objectField("result");
                    if (Result == void or Result == ?void) {
                        try stream.write(null);
                    } else {
                        try stream.write(result);
                    }
                },
                .@"error" => |err| {
                    try stream.objectField("error");
                    try stream.write(err);
                },
            }
            try stream.endObject();
        }
    };
}

pub fn ResultType(comptime method: []const u8) type {
    if (types.getRequestMetadata(method)) |meta| return meta.Result;
    @compileError("unsupported LSP result type: " ++ method);
}

pub const basic_server = struct {
    pub fn validateServerCapabilities(
        comptime Handler: type,
        capabilities: types.ServerCapabilities,
    ) void {
        _ = Handler;
        _ = capabilities;
    }

    pub fn run(
        allocator: std.mem.Allocator,
        transport: *Transport,
        handler: anytype,
        logger: anytype,
    ) !void {
        _ = logger;
        while (true) {
            var arena_state: std.heap.ArenaAllocator = .init(allocator);
            defer arena_state.deinit();
            const arena = arena_state.allocator();

            const json_message = transport.readJsonMessage(arena) catch |err| {
                return err;
            };
            try handleOne(arena, transport, handler, json_message);
        }
    }
};

fn handleOne(
    arena: std.mem.Allocator,
    transport: *Transport,
    handler: anytype,
    json_message: []const u8,
) !void {
    const parsed = std.json.parseFromSlice(
        std.json.Value,
        arena,
        json_message,
        .{},
    ) catch |err| {
        try transport.writeErrorResponse(
            arena,
            null,
            .{ .code = .parse_error, .message = @errorName(err) },
            .{ .emit_null_optional_fields = false },
        );
        return;
    };
    const root = parsed.value;
    if (root != .object) {
        try writeInvalidRequest(arena, transport, null, "expected object");
        return;
    }

    const object = root.object;
    const maybe_method = object.get("method");
    if (maybe_method) |method_value| {
        if (method_value != .string) {
            try writeInvalidRequest(arena, transport, null, "invalid method");
            return;
        }
        const method = method_value.string;
        const params = object.get("params");
        if (object.get("id")) |id_value| {
            const id = parseId(id_value) orelse {
                try writeInvalidRequest(arena, transport, null, "invalid id");
                return;
            };
            try handleRequest(arena, transport, handler, id, method, params);
        } else {
            handleNotification(arena, handler, method, params);
        }
        return;
    }

    if (object.get("id")) |id_value| {
        _ = parseId(id_value);
        return;
    }
    try writeInvalidRequest(arena, transport, null, "missing method");
}

/// Calls the handler method named `method`, as lsp_kit's server does: the
/// methods are the handler's own declarations, and a request that fails
/// is answered with an error under its id, so the client's promise
/// settles and the messages written before it are kept.
fn handleRequest(
    arena: std.mem.Allocator,
    transport: *Transport,
    handler: anytype,
    id: JsonRPCMessage.ID,
    method: []const u8,
    params: ?std.json.Value,
) !void {
    const Handler = @TypeOf(handler.*);
    inline for (types.request_metadata) |meta| {
        if (comptime @hasDecl(Handler, meta.method)) {
            if (std.mem.eql(u8, method, meta.method)) {
                const parsed = parseParams(meta.Params orelse void, arena, params) catch |err| {
                    return writeError(arena, transport, id, .invalid_params, err);
                };
                const returned = @field(Handler, meta.method)(handler, arena, parsed);
                const result = if (@typeInfo(@TypeOf(returned)) == .error_union)
                    returned catch |err| {
                        return writeError(arena, transport, id, .internal_error, err);
                    }
                else
                    returned;
                return transport.writeResponse(
                    arena,
                    id,
                    meta.Result,
                    result,
                    .{ .emit_null_optional_fields = false },
                );
            }
        }
    }
    try transport.writeErrorResponse(
        arena,
        id,
        .{ .code = .method_not_found, .message = method },
        .{ .emit_null_optional_fields = false },
    );
}

/// A notification has no reply: one that fails is dropped, as lsp_kit's
/// server drops it.
fn handleNotification(
    arena: std.mem.Allocator,
    handler: anytype,
    method: []const u8,
    params: ?std.json.Value,
) void {
    const Handler = @TypeOf(handler.*);
    inline for (types.notification_metadata) |meta| {
        if (comptime @hasDecl(Handler, meta.method)) {
            if (std.mem.eql(u8, method, meta.method)) {
                const parsed = parseParams(meta.Params orelse void, arena, params) catch return;
                const returned = @field(Handler, meta.method)(handler, arena, parsed);
                if (@typeInfo(@TypeOf(returned)) == .error_union) {
                    returned catch {};
                }
                return;
            }
        }
    }
}

fn writeError(
    arena: std.mem.Allocator,
    transport: *Transport,
    id: JsonRPCMessage.ID,
    code: JsonRPCMessage.Response.Error.Code,
    err: anyerror,
) !void {
    try transport.writeErrorResponse(
        arena,
        id,
        .{ .code = code, .message = @errorName(err) },
        .{ .emit_null_optional_fields = false },
    );
}

fn parseParams(
    comptime Params: type,
    arena: std.mem.Allocator,
    params: ?std.json.Value,
) !Params {
    if (Params == void) return {};
    const value = params orelse return error.MissingField;
    return try std.json.parseFromValueLeaky(
        Params,
        arena,
        value,
        .{ .ignore_unknown_fields = true },
    );
}

fn parseId(value: std.json.Value) ?JsonRPCMessage.ID {
    return switch (value) {
        .integer => |number| .{ .number = number },
        .string => |string| .{ .string = string },
        else => null,
    };
}

fn writeInvalidRequest(
    arena: std.mem.Allocator,
    transport: *Transport,
    id: ?JsonRPCMessage.ID,
    message: []const u8,
) !void {
    try transport.writeErrorResponse(
        arena,
        id,
        .{ .code = .invalid_request, .message = message },
        .{ .emit_null_optional_fields = false },
    );
}
