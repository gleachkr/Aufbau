const std = @import("std");
const json_out = @import("../json_out.zig");

comptime {
    _ = @import("./lsp_tests.zig");
}

// Regression: a diagnostic echoes an offending source token verbatim into its
// `detail.token` field. When that token contains a JSON-special character
// (e.g. the backslash in `t\p`), an unescaped emitter produced a buffer like
// `"token":"t\p"` — `\p` is an invalid JSON escape, so the npm package's
// `JSON.parse(resultBuffer)` threw `SyntaxError: Bad escaped character` and
// `compile()` blew up on entirely legitimate (if erroneous) input.
test "wasm result JSON escapes source tokens with backslashes" {
    const allocator = std.testing.allocator;

    var out: std.io.Writer.Allocating = .init(allocator);
    defer out.deinit();

    try out.writer.writeByte('{');
    try json_out.writeStringField(&out.writer, "kind", "unknown_math_token");
    try out.writer.writeByte(',');
    // The reported offending token: `t\p`.
    try json_out.writeStringField(&out.writer, "token", "t\\p");
    try out.writer.writeByte('}');

    // The whole point: the buffer must be parseable JSON (this is exactly what
    // `readJsonResult` does with `JSON.parse`).
    var parsed = try std.json.parseFromSlice(
        std.json.Value,
        allocator,
        out.written(),
        .{},
    );
    defer parsed.deinit();

    const token = parsed.value.object.get("token").?;
    try std.testing.expectEqualStrings("t\\p", token.string);
}

test "wasm result JSON escapes quotes, control bytes, and optional fields" {
    const allocator = std.testing.allocator;

    var out: std.io.Writer.Allocating = .init(allocator);
    defer out.deinit();

    // A quote, a backslash, a newline, and a raw control byte all in one token.
    const nasty = "a\"b\\c\nd\x01e";

    try out.writer.writeByte('{');
    try json_out.writeStringField(&out.writer, "token", nasty);
    try out.writer.writeByte(',');
    try json_out.writeOptionalStringField(&out.writer, "rule", nasty);
    try out.writer.writeByte(',');
    try json_out.writeOptionalStringField(&out.writer, "name", null);
    try out.writer.writeByte('}');

    var parsed = try std.json.parseFromSlice(
        std.json.Value,
        allocator,
        out.written(),
        .{},
    );
    defer parsed.deinit();

    try std.testing.expectEqualStrings(
        nasty,
        parsed.value.object.get("token").?.string,
    );
    try std.testing.expectEqualStrings(
        nasty,
        parsed.value.object.get("rule").?.string,
    );
    try std.testing.expect(parsed.value.object.get("name").? == .null);
}
