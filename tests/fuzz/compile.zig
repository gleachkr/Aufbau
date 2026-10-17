//! Fuzz target: compile a mutated proof case, then verify what compiled.
//!
//! The `.mm0`, the `.auf` or both get edits (see mutate.zig). The compiler
//! may reject the result with diagnostics, but it must not panic, leak,
//! hang or run away with memory, and:
//!
//! - whatever compiles passes the trusted verifier, except for the
//!   statements its `by sorry!` warnings admit, which the verifier must
//!   count exactly;
//! - a failed compile has a diagnostic for its error;
//! - the editor's analysis agrees: it reports an error exactly when the
//!   compile fails.
const std = @import("std");
const mm0 = @import("mm0");
const harness = @import("harness.zig");
const mutate = @import("mutate.zig").mutate;

const Side = enum { mm0, auf, both };

fn compileThenVerify(seeds: []const harness.Seed, input: harness.Input) !void {
    const gpa = input.gpa;
    const smith = input.smith;
    const seed = seeds[smith.index(seeds.len)];
    const side = smith.value(Side);
    const mm0_src = if (side != .auf)
        try mutate(gpa, smith, seed.mm0, seed.auf)
    else
        try gpa.dupe(u8, seed.mm0);
    defer gpa.free(mm0_src);
    const auf_src = if (side != .mm0)
        try mutate(gpa, smith, seed.auf, seed.mm0)
    else
        try gpa.dupe(u8, seed.auf);
    defer gpa.free(auf_src);
    input.dump("case.mm0", mm0_src);
    input.dump("case.auf", auf_src);
    _ = try checkPair(gpa, seed.stem, mm0_src, auf_src);
}

/// Whether the pair compiled, after checking it against the oracles above.
/// `name` labels a failure.
pub fn checkPair(gpa: std.mem.Allocator, name: []const u8, mm0_src: []const u8, auf_src: []const u8) !bool {
    const analysis_error = try analyzeError(gpa, mm0_src, auf_src);

    var compiler = mm0.Compiler.initWithProof(gpa, mm0_src, auf_src);
    const mmb = compiler.compileMmb(gpa) catch |err| {
        if (err == error.OutOfMemory) return err;
        // What the CLI prints: without a matching diagnostic it can only
        // name the error, with no location.
        const reported = if (compiler.getDiagnostic()) |diag| diag.err == err else false;
        if (!reported)
            fail(name, "compile fails with {t} but has no diagnostic for it", .{err});
        if (analysis_error == null)
            fail(name, "compile fails with {t} but analysis reports nothing", .{err});
        return false;
    };
    defer gpa.free(mmb);
    if (analysis_error) |err|
        fail(name, "compile succeeds but analysis reports {t}", .{err});

    var sorry_lines: usize = 0;
    for (compiler.warningDiagnostics()) |diag| {
        if (diag.err == error.SorryLine) sorry_lines += 1;
    }
    var session = mm0.VerificationSession.init(gpa, mm0_src, mmb) catch |err| {
        if (err == error.OutOfMemory) return err;
        fail(name, "the compiled proof fails to load: {t}", .{err});
    };
    defer session.deinit();
    if (session.verify()) |_| {
        if (sorry_lines != 0)
            fail(name, "{d} sorry lines, but the proof verifies", .{sorry_lines});
    } else |err| switch (err) {
        error.OutOfMemory => return err,
        error.SorryUsed => if (session.verifier.sorry_count != sorry_lines)
            fail(name, "{d} sorry lines, but the verifier admits {d} statements", .{
                sorry_lines,
                session.verifier.sorry_count,
            }),
        else => fail(name, "the compiled proof fails to verify: {t}", .{err}),
    }
    return true;
}

/// The first error the editor's analysis reports, if any.
fn analyzeError(gpa: std.mem.Allocator, mm0_src: []const u8, auf_src: []const u8) !?anyerror {
    var compiler = mm0.Compiler.initWithProof(gpa, mm0_src, auf_src);
    compiler.analyze() catch |err| {
        if (err == error.OutOfMemory) return err;
        return @as(?anyerror, err);
    };
    const diags = compiler.primaryDiagnostics();
    if (diags.len == 0) return null;
    return @as(?anyerror, diags[0].err);
}

fn fail(name: []const u8, comptime format: []const u8, args: anytype) noreturn {
    std.debug.print("{s}: " ++ format ++ "\n", .{name} ++ args);
    @panic("compile oracle failed");
}

test "fuzz compile then verify" {
    try harness.run("compile", .{}, try harness.seeds(), compileThenVerify);
}
