//! A compile's memory follows its largest proof, not the sum of its proofs
//! (#634): each theorem and lemma is checked in an arena reset once its MMB
//! records are out. So does an analysis: the one that explains a failed
//! compile, which checks every proof again, and an editor's, which keeps a
//! check memo. The tests compile the same proof repeated a few times and
//! many times, as theorems and as lemmas, and compare peak live bytes.

const helpers = @import("./helpers.zig");
const std = helpers.std;
const Compiler = helpers.Compiler;

/// Counts live bytes through a child allocator and keeps their peak.
const PeakAllocator = struct {
    child: std.mem.Allocator,
    live: usize = 0,
    peak: usize = 0,

    fn allocator(self: *PeakAllocator) std.mem.Allocator {
        return .{ .ptr = self, .vtable = &.{
            .alloc = alloc,
            .resize = resize,
            .remap = remap,
            .free = free,
        } };
    }

    fn grow(self: *PeakAllocator, old_len: usize, new_len: usize) void {
        self.live = self.live - old_len + new_len;
        self.peak = @max(self.peak, self.live);
    }

    fn alloc(ctx: *anyopaque, len: usize, alignment: std.mem.Alignment, ret_addr: usize) ?[*]u8 {
        const self: *PeakAllocator = @ptrCast(@alignCast(ctx));
        const ptr = self.child.rawAlloc(len, alignment, ret_addr) orelse return null;
        self.grow(0, len);
        return ptr;
    }

    fn resize(ctx: *anyopaque, memory: []u8, alignment: std.mem.Alignment, new_len: usize, ret_addr: usize) bool {
        const self: *PeakAllocator = @ptrCast(@alignCast(ctx));
        if (!self.child.rawResize(memory, alignment, new_len, ret_addr)) return false;
        self.grow(memory.len, new_len);
        return true;
    }

    fn remap(ctx: *anyopaque, memory: []u8, alignment: std.mem.Alignment, new_len: usize, ret_addr: usize) ?[*]u8 {
        const self: *PeakAllocator = @ptrCast(@alignCast(ctx));
        const ptr = self.child.rawRemap(memory, alignment, new_len, ret_addr) orelse return null;
        self.grow(memory.len, new_len);
        return ptr;
    }

    fn free(ctx: *anyopaque, memory: []u8, alignment: std.mem.Alignment, ret_addr: usize) void {
        const self: *PeakAllocator = @ptrCast(@alignCast(ctx));
        self.child.rawFree(memory, alignment, ret_addr);
        self.live -= memory.len;
    }
};

const theory =
    \\delimiter $ ( ) $;
    \\provable sort wff;
    \\term imp (a b: wff): wff; infixr imp: $->$ prec 25;
    \\axiom ax_1 (a b: wff): $ a -> b -> a $;
    \\axiom ax_2 (a b c: wff): $ (a -> b -> c) -> (a -> b) -> a -> c $;
    \\axiom ax_mp (a b: wff): $ a -> b $ > $ a $ > $ b $;
    \\
;

const Kind = enum { theorem, lemma };

const Run = enum {
    compile,
    /// The last proof cites an unknown rule, so the compile fails and its
    /// failure is analyzed as the command line does.
    failed_compile,
    /// An analysis with a check memo and a hole sink, as the language
    /// server runs it.
    editor_analysis,
};

/// The peak live bytes of `run` over `count` copies of `a → a`, each proved
/// in five lines after five lines about a long implication chain `x`, so
/// the proof is large while the statement every later proof keeps is small.
fn runPeak(kind: Kind, run: Run, count: usize) !usize {
    const gpa = std.testing.allocator;
    var x: std.ArrayListUnmanaged(u8) = .empty;
    defer x.deinit(gpa);
    try x.append(gpa, '(');
    for (0..200) |_| try x.appendSlice(gpa, "a -> ");
    try x.appendSlice(gpa, "a)");
    const X = x.items;

    var mm0: std.ArrayListUnmanaged(u8) = .empty;
    defer mm0.deinit(gpa);
    var auf: std.ArrayListUnmanaged(u8) = .empty;
    defer auf.deinit(gpa);
    try mm0.appendSlice(gpa, theory);
    for (0..count) |idx| {
        const statement = try std.fmt.allocPrint(gpa, "t{d} (a: wff): $ a -> a $", .{idx});
        defer gpa.free(statement);
        switch (kind) {
            .theorem => {
                try mm0.print(gpa, "theorem {s};\n", .{statement});
                try auf.print(gpa, "t{d}\n---\n", .{idx});
            },
            .lemma => try auf.print(gpa, "lemma {s}\n---\n", .{statement}),
        }
        const fails = run == .failed_compile and idx + 1 == count;
        for ([_][]const u8{ "x", "y" }, [_][]const u8{ X, "a" }) |label, f| try auf.print(gpa,
            \\{0s}1: $ {1s} -> ({1s} -> {1s}) -> {1s} $ by ax_1
            \\{0s}2: $ ({1s} -> ({1s} -> {1s}) -> {1s}) -> ({1s} -> {1s} -> {1s}) -> {1s} -> {1s} $ by ax_2
            \\{0s}3: $ ({1s} -> {1s} -> {1s}) -> {1s} -> {1s} $ by ax_mp [{0s}2, {0s}1]
            \\{0s}4: $ {1s} -> {1s} -> {1s} $ by ax_1
            \\{0s}5: $ {1s} -> {1s} $ by {2s} [{0s}3, {0s}4]
            \\
        , .{ label, f, if (fails) "ax_unknown" else "ax_mp" });
        try auf.append(gpa, '\n');
    }

    var peak = PeakAllocator{ .child = gpa };
    const allocator = peak.allocator();
    var compiler = Compiler.initWithProof(allocator, mm0.items, auf.items);
    switch (run) {
        .compile => allocator.free(try compiler.compileMmb(allocator)),
        .failed_compile => {
            if (compiler.compileMmb(allocator)) |mmb| {
                allocator.free(mmb);
                return error.TestUnexpectedResult;
            } else |_| {}
            var analysis = compiler.failureAnalysis();
            try std.testing.expect(analysis.analyzeCompileFailure(&compiler));
        },
        .editor_analysis => {
            var memo = helpers.mm0.CheckMemo.init(allocator);
            defer memo.deinit();
            var holes = helpers.mm0.CompilerSupport.Context.HoleInferenceSink{
                .allocator = allocator,
            };
            defer holes.deinit();
            compiler.editor.memo = &memo;
            compiler.hole_inference_sink = &holes;
            try compiler.analyze();
            // Every block went through the memo, so its path is the one
            // measured.
            try std.testing.expectEqual(@as(usize, count), memo.misses);
        },
    }
    return peak.peak;
}

fn expectBoundedByLargestProof(kind: Kind, run: Run) !void {
    const few = try runPeak(kind, run, 4);
    const many = try runPeak(kind, run, 32);
    // Eight times the proofs; held memory would grow about eightfold.
    // What remains per proof is its MMB records and its parsed block.
    if (many >= 2 * few) {
        std.debug.print("peak live bytes: 4 proofs {d}, 32 proofs {d}\n", .{ few, many });
        return error.TestUnexpectedResult;
    }
}

test "a compile frees each theorem's work once its records are out" {
    try expectBoundedByLargestProof(.theorem, .compile);
}

test "a compile frees each lemma's work once its records are out" {
    try expectBoundedByLargestProof(.lemma, .compile);
}

test "a failed compile's analysis frees each theorem's work once it is checked" {
    try expectBoundedByLargestProof(.theorem, .failed_compile);
}

test "a failed compile's analysis frees each lemma's work once it is checked" {
    try expectBoundedByLargestProof(.lemma, .failed_compile);
}

test "an editor's analysis frees each theorem's work, check memo and all" {
    try expectBoundedByLargestProof(.theorem, .editor_analysis);
}

test "an editor's analysis frees each lemma's work, check memo and all" {
    try expectBoundedByLargestProof(.lemma, .editor_analysis);
}
