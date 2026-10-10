//! Fuzz target: the trusted kernel on malformed input.
//!
//! A base pair is a proof case's `.mm0` with the binary this compiler makes
//! for it, or the upstream tutorial pair from tests/mmb_mutants/ (built by
//! mm0-rs, so laid out differently). The binary gets raw or structured
//! edits (mmb_mutate.zig), the spec gets token edits, or both. The
//! verifier, MMB parser, MM0 parser and cross-checker must reject bad input
//! with an error, never a panic, leak or hang. When mm0-c is on PATH it is
//! the oracle for acceptance: a changed pair this verifier accepts must
//! pass mm0-c too.
const std = @import("std");
const mm0 = @import("mm0");
const harness = @import("harness.zig");
const mm0c = @import("mm0c.zig");
const mutateSource = @import("mutate.zig").mutate;
const mmb_mutate = @import("mmb_mutate.zig");

const Base = struct { mm0: []const u8, mmb: []const u8 };

var tutorial: ?Base = null;

const Edit = enum { raw, structure, spec, structure_and_spec };

fn kernel(seeds: []const harness.Seed, input: harness.Input) !void {
    const gpa = input.gpa;
    const smith = input.smith;
    const base = (try pickBase(seeds, smith.index(seeds.len + 1))) orelse return;
    const edit = smith.value(Edit);

    const mm0_src = switch (edit) {
        .spec, .structure_and_spec => try mutateSource(gpa, smith, base.mm0, ""),
        .raw, .structure => try gpa.dupe(u8, base.mm0),
    };
    defer gpa.free(mm0_src);
    const mmb = switch (edit) {
        .raw => try mmb_mutate.mutateBytes(gpa, smith, base.mmb),
        .structure, .structure_and_spec => try mmb_mutate.mutateStructure(gpa, smith, base.mmb),
        .spec => try gpa.dupe(u8, base.mmb),
    };
    defer gpa.free(mmb);
    input.dump("case.mm0", mm0_src);
    input.dump("case.mmb", mmb);

    mm0.verifyPair(gpa, mm0_src, mmb) catch |err| switch (err) {
        error.OutOfMemory => return err,
        else => return,
    };
    const unchanged = std.mem.eql(u8, mm0_src, base.mm0) and std.mem.eql(u8, mmb, base.mmb);
    if (unchanged or !mm0c.present()) return;
    if (try mm0c.verdict(mm0_src, mmb) == .reject) {
        std.debug.print("this verifier accepts a pair that mm0-c rejects\n", .{});
        @panic("kernel oracle failed");
    }
}

/// Base `index` (the last index is the tutorial), or null when that seed
/// does not compile cleanly.
fn pickBase(seeds: []const harness.Seed, index: usize) !?Base {
    if (index == seeds.len) return try loadTutorial();
    const mmb = (try harness.compiledSeed(seeds, index)) orelse return null;
    return .{ .mm0 = seeds[index].mm0, .mmb = mmb };
}

fn loadTutorial() !Base {
    if (tutorial) |base| return base;
    const io = std.testing.io;
    const dir = std.Io.Dir.cwd();
    const gpa = std.heap.page_allocator;
    tutorial = .{
        .mm0 = try dir.readFileAlloc(io, "tests/mmb_mutants/tutorial.mm0", gpa, .unlimited),
        .mmb = try dir.readFileAlloc(io, "tests/mmb_mutants/tutorial.mmb", gpa, .unlimited),
    };
    return tutorial.?;
}

test "fuzz trusted kernel" {
    try harness.run("kernel", try harness.seeds(), kernel);
}
