//! Guards for the shared `.mm0` statement walk (task #262). Three loops
//! stream the `.mm0` file — the compile path, the editor analysis, and the
//! search fixture — and each once carried its own copy of the per-gap
//! obligations, which drifted (the fixture never mirrored coercions). They
//! now advance through `pipeline/common.zig`; this pins that the copies do
//! not come back.

const std = @import("std");

const statement_walks = [_][]const u8{
    "src/frontend/compiler/pipeline/run.zig",
    "src/frontend/compiler/pipeline/analyze.zig",
    "src/frontend/compiler/search/fixture.zig",
};

const common_path = "src/frontend/compiler/pipeline/common.zig";

fn readSource(allocator: std.mem.Allocator, path: []const u8) ![]u8 {
    return std.fs.cwd().readFileAlloc(allocator, path, 1 << 22);
}

fn contains(haystack: []const u8, needle: []const u8) bool {
    return std.mem.indexOf(u8, haystack, needle) != null;
}

test "every statement walk advances and registers through the shared helpers" {
    const allocator = std.testing.allocator;
    for (statement_walks) |path| {
        const src = try readSource(allocator, path);
        defer allocator.free(src);
        try std.testing.expect(contains(src, ".nextPublicStatement("));
        // The gap obligations the helper discharges are called nowhere else.
        try std.testing.expect(!contains(src, "syncCoercionsFromParser("));
        try std.testing.expect(!contains(src, "warnDroppedAnnotations("));
        try std.testing.expect(!contains(src, "rejectLocalTermNotation("));
        // Declarations enter the env through the registration helpers.
        try std.testing.expect(!contains(src, ".addStmt("));
        try std.testing.expect(!contains(src, "Metadata.process"));
    }

    const common = try readSource(allocator, common_path);
    defer allocator.free(common);
    try std.testing.expect(contains(common, "syncCoercionsFromParser("));
    try std.testing.expect(contains(common, "pub fn nextPublicStatement("));
    try std.testing.expect(contains(common, "pub fn registerSort("));
    try std.testing.expect(contains(common, "pub fn registerTerm("));
    try std.testing.expect(contains(common, "pub fn registerAssertion("));
}
