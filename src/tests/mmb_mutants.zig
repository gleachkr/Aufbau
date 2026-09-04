const std = @import("std");
const mm0 = @import("../lib.zig");

// Hand-mutated MMB files under tests/mmb_mutants/. Each mutant is the
// upstream tutorial (third_party/mm0/examples/tutorial/03-mm1-intro.mmb)
// with a few bytes changed, paired with a hand-written .mm0 spec covering
// its public declarations. mm0-c is the oracle for every expected verdict.

fn readMutantFile(
    allocator: std.mem.Allocator,
    name: []const u8,
) ![]align(@alignOf(mm0.Arg)) u8 {
    const path = try std.fmt.allocPrint(
        allocator,
        "tests/mmb_mutants/{s}",
        .{name},
    );
    defer allocator.free(path);
    return try std.fs.cwd().readFileAllocOptions(
        allocator,
        path,
        std.math.maxInt(usize),
        null,
        std.mem.Alignment.of(mm0.Arg),
        null,
    );
}

fn verifyMutant(mmb_name: []const u8) !void {
    const allocator = std.testing.allocator;
    const spec = try readMutantFile(allocator, "tutorial.mm0");
    defer allocator.free(spec);
    const mmb = try readMutantFile(allocator, mmb_name);
    defer allocator.free(mmb);
    try mm0.verifyPair(allocator, spec, mmb);
}

test "mmb mutants: unmodified tutorial verifies" {
    try verifyMutant("tutorial.mmb");
}

test "mmb mutants: a proof of the wrong conclusion is rejected" {
    // a1i's body returns its hypothesis |- b for the declared a -> b: the
    // statement's unify stream demands an `imp` application and finds a
    // variable (mm0-c: "unify failure at term").
    try std.testing.expectError(
        error.ExpectedTermApp,
        verifyMutant("wrong_conclusion.mmb"),
    );
}

test "mmb mutants: a proof that cites its own theorem is rejected" {
    // a1i's body ends with `Thm 6`, a1i's own index (mm0-c: "theorem out
    // of range"). A statement becomes available only after it verifies.
    try std.testing.expectError(
        error.ForwardTheoremRef,
        verifyMutant("circular_proof.mmb"),
    );
}
