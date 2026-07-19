//! JSON string-emission helpers shared by the wasm compiler's result writer.
//!
//! These live in their own module (rather than inline in `wasm.zig`) so they
//! can be exercised by native unit tests — `wasm.zig` itself pins
//! `std.heap.wasm_allocator` at module scope and only compiles for wasm32.

const std = @import("std");

/// Write `value` as a JSON string literal, escaping every character JSON
/// requires so the result is always valid JSON — including source-derived
/// values (notation tokens, identifiers) that may contain quotes, backslashes,
/// or control bytes.
pub fn writeString(writer: anytype, value: []const u8) !void {
    try writer.writeByte('"');
    for (value) |ch| switch (ch) {
        '"' => try writer.writeAll("\\\""),
        '\\' => try writer.writeAll("\\\\"),
        '\n' => try writer.writeAll("\\n"),
        '\r' => try writer.writeAll("\\r"),
        '\t' => try writer.writeAll("\\t"),
        else => if (ch < 0x20) {
            try writer.print("\\u{x:0>4}", .{ch});
        } else {
            try writer.writeByte(ch);
        },
    };
    try writer.writeByte('"');
}

/// `null` or an escaped JSON string.
pub fn writeOptionalString(writer: anytype, value: ?[]const u8) !void {
    if (value) |actual| {
        try writeString(writer, actual);
    } else {
        try writer.writeAll("null");
    }
}

/// `"name":"value"` with `value` escaped. Field names are always controlled
/// literals at the call sites, so they are emitted directly.
pub fn writeStringField(
    writer: anytype,
    name: []const u8,
    value: []const u8,
) !void {
    try writer.print("\"{s}\":", .{name});
    try writeString(writer, value);
}

/// `"name":null` or `"name":"value"` with `value` escaped.
pub fn writeOptionalStringField(
    writer: anytype,
    name: []const u8,
    value: ?[]const u8,
) !void {
    try writer.print("\"{s}\":", .{name});
    try writeOptionalString(writer, value);
}
