const std = @import("std");
const mm0 = @import("../lib.zig");

// Malformed MMB files, one row per verdict. Each row patches bytes of the
// upstream tutorial (third_party/mm0/examples/tutorial/03-mm1-intro.mmb,
// checked in as tests/mmb_mutants/tutorial.mmb) or names a hand-mutated copy,
// optionally rewrites the .mm0 spec, and names the error this verifier must
// report. mm0-c is the oracle: `mm0c` is the message it gives for the same
// pair, and when `mm0-c` is on PATH (as in CI) every row is run through it
// too.
//
// Offsets in the tutorial: header fields at 4 (version), 5 (num_sorts),
// 8 (num_terms), 12 (num_thms) and 24 (p_proof); the sort table at 40;
// term 0 (`imp`) has its binders at 0x50; term 2 (`and`, a local def) has
// its binders at 0x78 and return slot at 0x88; theorem 6 (`a1i`, a local
// theorem) has its binders at 0x1f0. Statements: `wff` 0x340, `imp` 0x342,
// `ax_1` 0x346, `id` 0x37f, `and` 0x3b6, `or_right` 0x3ca, `or_left` 0x524
// (its proof ends `Conv Cong Refl Ref 5 Unfold Refl` at 0x53a).

const Patch = struct {
    at: usize,
    bytes: []const u8,
};

const SpecEdit = struct {
    find: []const u8,
    replace: []const u8,
};

const Mutant = struct {
    name: []const u8,
    base: []const u8 = "tutorial.mmb",
    patches: []const Patch = &.{},
    /// Keep only this many bytes of the file.
    truncate: ?usize = null,
    spec_edits: []const SpecEdit = &.{},
    spec_suffix: []const u8 = "",
    expected: anyerror,
    /// The line mm0-c prints for the same pair.
    mm0c: []const u8,
};

fn arg(sort: u7, bound: bool, deps: u55) [8]u8 {
    const value = mm0.Arg{
        .deps = deps,
        .reserved = 0,
        .sort = sort,
        .bound = bound,
    };
    return @bitCast(value);
}

fn le32(value: u32) [4]u8 {
    var bytes: [4]u8 = undefined;
    std.mem.writeInt(u32, &bytes, value, .little);
    return bytes;
}

const strict_wff: SpecEdit = .{
    .find = "provable sort wff;",
    .replace = "strict provable sort wff;",
};

const mutants = [_]Mutant{
    // Header and tables.
    .{
        .name = "header shorter than the fixed fields",
        .truncate = 20,
        .expected = error.ShortMmb,
        .mm0c = "header not long enough",
    },
    .{
        .name = "wrong magic",
        .patches = &.{.{ .at = 0, .bytes = &.{0} }},
        .expected = error.BadMagic,
        .mm0c = "Not a MM0B file",
    },
    .{
        .name = "wrong version",
        .patches = &.{.{ .at = 4, .bytes = &.{2} }},
        .expected = error.BadVersion,
        .mm0c = "Wrong version",
    },
    .{
        .name = "129 sorts",
        .patches = &.{.{ .at = 5, .bytes = &.{129} }},
        .expected = error.TooManySorts,
        .mm0c = "Too many sorts",
    },
    .{
        // 255 sorts once overflowed the u8 header-end sum.
        .name = "255 sorts",
        .patches = &.{.{ .at = 5, .bytes = &.{255} }},
        .expected = error.TooManySorts,
        .mm0c = "Too many sorts",
    },
    .{
        .name = "term table past the end of the file",
        .patches = &.{.{ .at = 8, .bytes = &le32(0x10000) }},
        .expected = error.ShortTermTable,
        .mm0c = "Term table out of range",
    },
    .{
        .name = "theorem table past the end of the file",
        .patches = &.{.{ .at = 12, .bytes = &le32(0x10000) }},
        .expected = error.ShortTheoremTable,
        .mm0c = "Theorem table out of range",
    },
    .{
        .name = "proof stream past the end of the file",
        .patches = &.{.{ .at = 24, .bytes = &le32(0x100000) }},
        .expected = error.SuspectHeader,
        .mm0c = "Proof section out of range",
    },

    // Statements.
    .{
        .name = "sort statement with a body",
        .patches = &.{.{ .at = 0x341, .bytes = &.{3} }},
        .expected = error.NonEmptySortStatement,
        .mm0c = "Next statement incorrect",
    },
    .{
        .name = "stream ends before the last theorem",
        .patches = &.{.{ .at = 0x524, .bytes = &.{0} }},
        .expected = error.TheoremCountMismatch,
        .mm0c = "not all theorems proved",
    },
    .{
        .name = "stream has more theorems than the table",
        .patches = &.{.{ .at = 12, .bytes = &le32(14) }},
        .expected = error.TheoremCountMismatch,
        .mm0c = "Step theorem overflow",
    },
    .{
        .name = "unknown statement command",
        .patches = &.{.{ .at = 0x524, .bytes = &.{0x4f} }},
        .expected = error.UnknownStatement,
        .mm0c = "bad statement command",
    },
    .{
        .name = "term in a pure sort",
        .patches = &.{.{ .at = 40, .bytes = &.{0x05} }},
        .spec_edits = &.{.{
            .find = "provable sort wff;",
            .replace = "pure provable sort wff;",
        }},
        .expected = error.PureSort,
        .mm0c = "term in pure sort",
    },
    .{
        // The spec declares more than the stream proves: the extra axiom
        // would otherwise be accepted unproved.
        .name = "spec statement after the last proof",
        .spec_suffix = "axiom bogus (a: wff): $ a $;\n",
        .expected = error.MM0StatementNotProved,
        .mm0c = "expecting an axiom",
    },
    .{
        .name = "junk after the last spec statement",
        .spec_suffix = "garbage !!! @@@\n",
        .expected = error.UnexpectedKeyword,
        .mm0c = "invalid command keyword",
    },

    // Binders (mm0-c's `load_args`). Local statements have no spec to
    // cross-check against, so only these checks stand between a bad binder
    // table and the proof.
    .{
        .name = "bound binder whose deps are not its own bit",
        .patches = &.{.{ .at = 0x78, .bytes = &arg(0, true, 0) }},
        .expected = error.BadBinderDeps,
        .mm0c = "bad binder deps",
    },
    .{
        .name = "regular binder depending on an undeclared bound variable",
        .patches = &.{.{ .at = 0x78, .bytes = &arg(0, false, 1) }},
        .expected = error.BadBinderDeps,
        .mm0c = "bad binder deps",
    },
    .{
        .name = "theorem binder depending on an undeclared bound variable",
        .patches = &.{.{ .at = 0x1f0, .bytes = &arg(0, false, 1) }},
        .expected = error.BadBinderDeps,
        .mm0c = "bad binder deps",
    },
    .{
        .name = "bound return slot",
        .patches = &.{.{ .at = 0x88, .bytes = &arg(0, true, 1) }},
        .expected = error.BadReturnType,
        .mm0c = "bad return type",
    },
    .{
        .name = "return slot depending on an undeclared bound variable",
        .patches = &.{.{ .at = 0x88, .bytes = &arg(0, false, 1) }},
        .expected = error.BadBinderDeps,
        .mm0c = "bad binder deps",
    },
    .{
        .name = "local def with a bound binder in a strict sort",
        .patches = &.{
            .{ .at = 40, .bytes = &.{0x06} },
            .{ .at = 0x78, .bytes = &arg(0, true, 1) },
        },
        .spec_edits = &.{strict_wff},
        .expected = error.StrictSort,
        .mm0c = "bound variable in strict sort",
    },
    .{
        // A plain term has no proof, but its binders are still checked.
        .name = "term with a bound binder in a strict sort",
        .patches = &.{
            .{ .at = 40, .bytes = &.{0x06} },
            .{ .at = 0x50, .bytes = &arg(0, true, 1) },
        },
        .spec_edits = &.{ strict_wff, .{
            .find = "term imp: wff > wff > wff;",
            .replace = "term imp {a: wff} (b: wff): wff;",
        } },
        .expected = error.StrictSort,
        .mm0c = "bound variable in strict sort",
    },

    // Proof streams.
    .{
        .name = "axiom leaves two expressions on the stack",
        .patches = &.{.{ .at = 0x34d, .bytes = &.{0x12} }},
        .expected = error.StackNotEmpty,
        .mm0c = "stack has != one element",
    },
    .{
        .name = "theorem ends on an expression",
        .patches = &.{.{ .at = 0x3b3, .bytes = &.{0x52} }},
        .expected = error.ExpectedProof,
        .mm0c = "stack has != one element",
    },
    .{
        .name = "def cites a theorem",
        .patches = &.{.{ .at = 0x3bb, .bytes = &.{0x54} }},
        .expected = error.ThmNotAllowed,
        .mm0c = "invalid opcode in def",
    },
    .{
        .name = "def uses Hyp",
        .patches = &.{.{ .at = 0x3bd, .bytes = &.{0x16} }},
        .expected = error.HypNotAllowed,
        .mm0c = "invalid opcode in def",
    },
    .{
        .name = "def uses Sorry",
        .patches = &.{.{ .at = 0x3bd, .bytes = &.{0x20} }},
        .expected = error.SorryNotAllowed,
        .mm0c = "invalid opcode in def",
    },
    .{
        .name = "def cites itself",
        .patches = &.{.{ .at = 0x3bc, .bytes = &.{2} }},
        .expected = error.ForwardTermRef,
        .mm0c = "term out of range",
    },
    .{
        .name = "a proof of the wrong conclusion",
        .base = "wrong_conclusion.mmb",
        .expected = error.ExpectedTermApp,
        .mm0c = "store type error",
    },
    .{
        // a1i's body ends with `Thm 6`, a1i's own index. A statement
        // becomes available only after it verifies.
        .name = "theorem cites itself",
        .base = "circular_proof.mmb",
        .expected = error.ForwardTheoremRef,
        .mm0c = "theorem out of range",
    },
    .{
        .name = "dummy of an undeclared sort",
        .patches = &.{.{ .at = 0x3cc, .bytes = &.{0x53} }},
        .expected = error.InvalidSort,
        .mm0c = "bad dummy sort",
    },
    .{
        .name = "Ref past the heap",
        .patches = &.{.{ .at = 0x53e, .bytes = &.{6} }},
        .expected = error.HeapOutOfBounds,
        .mm0c = "bad ref step",
    },

    // Conversion proofs, all in or_left.
    .{
        .name = "Refl on an obligation whose sides differ",
        .patches = &.{.{ .at = 0x53b, .bytes = &.{0x18} }},
        .expected = error.ReflMismatch,
        .mm0c = "Refl unify failure",
    },
    .{
        .name = "Symm where Refl closes the obligation",
        .patches = &.{.{ .at = 0x53c, .bytes = &.{0x19} }},
        .expected = error.ExpectedTermApp,
        .mm0c = "store type error",
    },
    .{
        .name = "ConvSave where Refl closes the obligation",
        .patches = &.{.{ .at = 0x53c, .bytes = &.{0x1e} }},
        .expected = error.ExpectedConv,
        .mm0c = "bad stack slot",
    },
    .{
        .name = "ConvCut in place of Conv",
        .patches = &.{.{ .at = 0x53a, .bytes = &.{0x1c} }},
        .expected = error.ExpectedConvObligation,
        .mm0c = "bad stack slot",
    },
    .{
        .name = "Unfold against another term's expansion",
        .patches = &.{.{ .at = 0x53e, .bytes = &.{4} }},
        .expected = error.TermMismatch,
        .mm0c = "unify failure at term",
    },
    .{
        .name = "Refl in place of Unfold",
        .patches = &.{.{ .at = 0x53f, .bytes = &.{0x18} }},
        .expected = error.ExpectedConvObligation,
        .mm0c = "bad stack slot",
    },
};

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

fn buildSpec(allocator: std.mem.Allocator, mutant: Mutant) ![]u8 {
    var spec = try std.fs.cwd().readFileAlloc(
        allocator,
        "tests/mmb_mutants/tutorial.mm0",
        std.math.maxInt(usize),
    );
    for (mutant.spec_edits) |edit| {
        const next = try std.mem.replaceOwned(u8, allocator, spec, edit.find, edit.replace);
        if (std.mem.eql(u8, next, spec)) return error.SpecEditMissed;
        allocator.free(spec);
        spec = next;
    }
    const full = try std.mem.concat(allocator, u8, &.{ spec, mutant.spec_suffix });
    allocator.free(spec);
    return full;
}

fn buildMmb(
    allocator: std.mem.Allocator,
    mutant: Mutant,
) ![]align(@alignOf(mm0.Arg)) u8 {
    const mmb = try readMutantFile(allocator, mutant.base);
    for (mutant.patches) |patch| {
        @memcpy(mmb[patch.at..][0..patch.bytes.len], patch.bytes);
    }
    if (mutant.truncate) |len| {
        return try allocator.realloc(mmb, len);
    }
    return mmb;
}

/// Runs mm0-c on the pair and returns its stderr, or null when mm0-c is not
/// installed.
fn runMm0c(
    allocator: std.mem.Allocator,
    dir: std.testing.TmpDir,
    mmb: []const u8,
    spec: []const u8,
) !?struct { term: std.process.Child.Term, stderr: []u8 } {
    try dir.dir.writeFile(.{ .sub_path = "mutant.mmb", .data = mmb });
    const mmb_path = try dir.dir.realpathAlloc(allocator, "mutant.mmb");
    defer allocator.free(mmb_path);

    var child = std.process.Child.init(&.{ "mm0-c", mmb_path }, allocator);
    child.stdin_behavior = .Pipe;
    child.stdout_behavior = .Pipe;
    child.stderr_behavior = .Pipe;
    child.spawn() catch |err| switch (err) {
        error.FileNotFound => return null,
        else => return err,
    };
    // The spec fits in the pipe buffer, so writing it before reading
    // mm0-c's output cannot deadlock. mm0-c rejects a bad header without
    // reading the spec at all, and may exit before the write.
    child.stdin.?.writeAll(spec) catch |err| switch (err) {
        error.BrokenPipe => {},
        else => return err,
    };
    child.stdin.?.close();
    child.stdin = null;

    var stdout: std.ArrayListUnmanaged(u8) = .{};
    defer stdout.deinit(allocator);
    var stderr: std.ArrayListUnmanaged(u8) = .{};
    errdefer stderr.deinit(allocator);
    try child.collectOutput(allocator, &stdout, &stderr, 1 << 20);
    const term = try child.wait();
    return .{ .term = term, .stderr = try stderr.toOwnedSlice(allocator) };
}

test "mmb mutants: unmodified tutorial verifies" {
    const allocator = std.testing.allocator;
    const spec = try readMutantFile(allocator, "tutorial.mm0");
    defer allocator.free(spec);
    const mmb = try readMutantFile(allocator, "tutorial.mmb");
    defer allocator.free(mmb);
    try mm0.verifyPair(allocator, spec, mmb);
}

test "mmb mutants: each mutant is rejected as mm0-c rejects it" {
    const allocator = std.testing.allocator;
    var dir = std.testing.tmpDir(.{});
    defer dir.cleanup();

    var failures: usize = 0;
    for (mutants) |mutant| {
        const spec = try buildSpec(allocator, mutant);
        defer allocator.free(spec);
        const mmb = try buildMmb(allocator, mutant);
        defer allocator.free(mmb);

        if (mm0.verifyPair(allocator, spec, mmb)) |_| {
            std.debug.print("{s}: verified, expected {s}\n", .{
                mutant.name,
                @errorName(mutant.expected),
            });
            failures += 1;
        } else |err| if (err != mutant.expected) {
            std.debug.print("{s}: {s}, expected {s}\n", .{
                mutant.name,
                @errorName(err),
                @errorName(mutant.expected),
            });
            failures += 1;
        }

        const oracle = try runMm0c(allocator, dir, mmb, spec) orelse continue;
        defer allocator.free(oracle.stderr);
        const rejected = switch (oracle.term) {
            .Exited => |code| code != 0,
            else => true,
        };
        if (!rejected or std.mem.indexOf(u8, oracle.stderr, mutant.mm0c) == null) {
            std.debug.print("{s}: mm0-c did not report \"{s}\":\n{s}\n", .{
                mutant.name,
                mutant.mm0c,
                oracle.stderr,
            });
            failures += 1;
        }
    }
    try std.testing.expectEqual(@as(usize, 0), failures);
}
