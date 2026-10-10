//! mm0-c, the reference C verifier, as a second opinion on a pair.
//!
//! Used only when `mm0-c` is on PATH (the dev shell and CI have it).
const std = @import("std");

const io = std.testing.io;

pub const Verdict = enum { accept, reject };

var checked = false;
var found = false;
/// Where the binary goes for mm0-c to read; one per process.
var scratch: ?std.testing.TmpDir = null;
var scratch_path: [64]u8 = undefined;
var scratch_path_len: usize = 0;

/// Whether `mm0-c` runs at all; checked once per process.
pub fn present() bool {
    if (checked) return found;
    checked = true;
    const result = std.process.run(std.heap.page_allocator, io, .{
        .argv = &.{"mm0-c"},
        .stdout_limit = .limited(8 * 1024),
        .stderr_limit = .limited(8 * 1024),
    }) catch return false;
    std.heap.page_allocator.free(result.stdout);
    std.heap.page_allocator.free(result.stderr);
    // With no arguments mm0-c prints its usage and exits 1.
    found = result.term == .exited;
    return found;
}

/// mm0-c's verdict on `mmb` against `mm0_src`. Exit 0 accepts; anything
/// else, including admitted `sorry` statements (exit 3), rejects.
pub fn verdict(mm0_src: []const u8, mmb: []const u8) !Verdict {
    const path = try scratchFile();
    try std.Io.Dir.cwd().writeFile(io, .{ .sub_path = path, .data = mmb });

    var child = try std.process.spawn(io, .{
        .argv = &.{ "mm0-c", path },
        .stdin = .pipe,
        .stdout = .ignore,
        .stderr = .ignore,
    });
    defer child.kill(io);
    child.stdin.?.writeStreamingAll(io, mm0_src) catch {};
    child.stdin.?.close(io);
    child.stdin = null;
    return switch (try child.wait(io)) {
        .exited => |code| if (code == 0) .accept else .reject,
        else => .reject,
    };
}

fn scratchFile() ![]const u8 {
    if (scratch == null) {
        scratch = std.testing.tmpDir(.{});
        scratch_path_len = (try std.fmt.bufPrint(
            &scratch_path,
            ".zig-cache/tmp/{s}/case.mmb",
            .{&scratch.?.sub_path},
        )).len;
    }
    return scratch_path[0..scratch_path_len];
}
