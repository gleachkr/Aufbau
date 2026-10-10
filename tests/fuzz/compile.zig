//! Fuzz target: compile a mutated proof case, then verify what compiled.
//!
//! One side of a seed (its `.mm0` or its `.auf`) gets token edits. The
//! compiler may reject the result with diagnostics, but it must not panic,
//! leak, hang or run away with memory, and whatever it does compile must
//! pass the trusted verifier.
const std = @import("std");
const mm0 = @import("mm0");
const harness = @import("harness.zig");
const mutate = @import("mutate.zig").mutate;

fn compileThenVerify(seeds: []const harness.Seed, input: harness.Input) !void {
    const gpa = input.gpa;
    const smith = input.smith;
    const seed = seeds[smith.index(seeds.len)];
    const edit_mm0 = smith.value(bool);
    const mm0_src = if (edit_mm0) try mutate(gpa, smith, seed.mm0) else try gpa.dupe(u8, seed.mm0);
    defer gpa.free(mm0_src);
    const auf_src = if (edit_mm0) try gpa.dupe(u8, seed.auf) else try mutate(gpa, smith, seed.auf);
    defer gpa.free(auf_src);
    input.dump("case.mm0", mm0_src);
    input.dump("case.auf", auf_src);

    var compiler = mm0.Compiler.initWithProof(gpa, mm0_src, auf_src);
    const mmb = compiler.compileMmb(gpa) catch |err| switch (err) {
        error.OutOfMemory => return err,
        else => return,
    };
    defer gpa.free(mmb);
    mm0.verifyPair(gpa, mm0_src, mmb) catch |err| switch (err) {
        // `by sorry!` lines compile with a warning and verify as admitted.
        error.SorryUsed => {},
        else => {
            std.debug.print("seed {s}: the compiled proof fails to verify: {t}\n", .{ seed.stem, err });
            @panic("compiled output fails to verify");
        },
    };
}

test "fuzz compile then verify" {
    try harness.run("compile", try harness.seeds(), compileThenVerify);
}
