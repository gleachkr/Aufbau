//! Fuzz target: the search's work allocator
//! (src/frontend/reclaiming_allocator.zig).
//!
//! The input is a script of allocator calls: allocations of sizes on both
//! sides of the small/large boundary at alignments up to 4096, and frees,
//! resizes and remaps of live blocks. Each live block holds a pattern
//! seeded by its own number, so a block that overlaps another, or loses
//! bytes when it moves, fails the check. `deinit` must return every block
//! the script left live, which the harness's leak-checked allocator sees.
//!
//! A plain test run feeds a fuzz target only the empty input, which makes
//! an empty script, so a second test runs the same model on a fixed
//! pseudo-random script.
const std = @import("std");
const mm0 = @import("mm0");
const harness = @import("harness.zig");

const ReclaimingAllocator = mm0.ReclaimingAllocator;
const Alignment = std.mem.Alignment;

const max_small: u32 = ReclaimingAllocator.max_small;
/// Longest script; each step touches at most a few hundred KiB.
const max_ops = 4096;
/// Most blocks live at once.
const max_live = 256;

const alignments = [_]Alignment{ .@"1", .@"2", .@"4", .@"8", .@"16", .@"32", .@"64", .fromByteUnits(4096) };

const Op = struct {
    kind: Kind,
    /// Which live block a free, resize or remap applies to, modulo the
    /// number live.
    slot: u8,
    /// Length of an allocation, or the new length of a resize or remap.
    len: u32,
    /// Alignment of an allocation.
    alignment: Alignment,

    const Kind = enum { alloc, free, resize, remap };
};

/// Builds the script from `choose`, which is the fuzzer's `Smith` or
/// `Prng` below.
fn script(gpa: std.mem.Allocator, choose: anytype) ![]Op {
    var ops: std.ArrayList(Op) = .empty;
    errdefer ops.deinit(gpa);
    while (ops.items.len < max_ops and !choose.eos()) {
        try ops.append(gpa, .{
            .kind = @fromBackingInt(@intCast(choose.index(4))),
            .slot = @intCast(choose.index(max_live)),
            // Mostly small, with a share on each side of the boundary.
            .len = switch (choose.index(8)) {
                0...3 => choose.valueRangeAtMost(u32, 1, 64),
                4, 5 => choose.valueRangeAtMost(u32, 1, 4096),
                6 => choose.valueRangeAtMost(u32, max_small - 32, max_small + 32),
                else => choose.valueRangeAtMost(u32, max_small + 1, 3 * max_small),
            },
            .alignment = alignments[choose.index(alignments.len)],
        });
    }
    return ops.toOwnedSlice(gpa);
}

fn describe(gpa: std.mem.Allocator, ops: []const Op) ![]u8 {
    var out: std.Io.Writer.Allocating = .init(gpa);
    errdefer out.deinit();
    for (ops) |op| switch (op.kind) {
        .alloc => try out.writer.print("alloc len={d} align={d}\n", .{ op.len, op.alignment.toByteUnits() }),
        .free => try out.writer.print("free slot={d}\n", .{op.slot}),
        .resize, .remap => try out.writer.print("{t} slot={d} len={d}\n", .{ op.kind, op.slot, op.len }),
    };
    return out.toOwnedSlice();
}

const Live = struct {
    ptr: [*]u8,
    len: usize,
    alignment: Alignment,
    seed: u8,

    fn byte(live: Live, i: usize) u8 {
        return live.seed *% 31 +% @as(u8, @truncate(i));
    }

    fn fill(live: Live, from: usize) void {
        for (from..live.len) |i| live.ptr[i] = live.byte(i);
    }

    fn check(live: Live, len: usize) void {
        if (!live.alignment.check(@intFromPtr(live.ptr)))
            @panic("reclaiming allocator: block lost its alignment");
        for (0..len) |i| if (live.ptr[i] != live.byte(i))
            @panic("reclaiming allocator: block contents changed");
    }

    fn slice(live: Live) []u8 {
        return live.ptr[0..live.len];
    }
};

/// Runs `ops` against a fresh allocator over `gpa`, checking every live
/// block's contents and alignment before and after each call that
/// touches it. Leaves half the blocks for `deinit`.
fn run(gpa: std.mem.Allocator, ops: []const Op) !void {
    var reclaiming = ReclaimingAllocator.init(gpa);
    defer reclaiming.deinit();
    const a = reclaiming.allocator();

    var live: [max_live]Live = undefined;
    var count: usize = 0;
    var next_seed: u8 = 0;
    for (ops) |op| {
        if (op.kind == .alloc or count == 0) {
            if (count == max_live) continue;
            const ptr = a.rawAlloc(op.len, op.alignment, @returnAddress()) orelse return error.OutOfMemory;
            live[count] = .{ .ptr = ptr, .len = op.len, .alignment = op.alignment, .seed = next_seed };
            next_seed +%= 1;
            live[count].fill(0);
            live[count].check(op.len);
            count += 1;
            continue;
        }
        const index = op.slot % count;
        const block = &live[index];
        block.check(block.len);
        const old_len = block.len;
        switch (op.kind) {
            .alloc => unreachable,
            .free => {
                a.rawFree(block.slice(), block.alignment, @returnAddress());
                count -= 1;
                live[index] = live[count];
                continue;
            },
            .resize => {
                if (!a.rawResize(block.slice(), block.alignment, op.len, @returnAddress())) continue;
            },
            .remap => {
                block.ptr = a.rawRemap(block.slice(), block.alignment, op.len, @returnAddress()) orelse continue;
            },
        }
        block.len = op.len;
        block.check(@min(old_len, block.len));
        block.fill(@min(old_len, block.len));
    }
    for (live[0..count]) |block| block.check(block.len);
    for (live[0 .. count / 2]) |block| a.rawFree(block.slice(), block.alignment, @returnAddress());
}

fn allocator(_: void, input: harness.Input) !void {
    const ops = try script(input.gpa, input.smith);
    defer input.gpa.free(ops);
    if (input.replay_dir != null) {
        const text = try describe(input.gpa, ops);
        defer input.gpa.free(text);
        input.dump("ops.txt", text);
    }
    try run(input.gpa, ops);
}

test "fuzz the reclaiming allocator" {
    try harness.run("allocator", .{}, {}, allocator);
}

/// `Smith`'s choice methods over a seeded PRNG, ending after `left` steps.
const Prng = struct {
    random: std.Random,
    left: usize,

    pub fn eos(self: *Prng) bool {
        if (self.left == 0) return true;
        self.left -= 1;
        return false;
    }

    pub fn index(self: *Prng, len: usize) usize {
        return self.random.uintLessThan(usize, len);
    }

    pub fn valueRangeAtMost(self: *Prng, comptime T: type, at_least: T, at_most: T) T {
        return self.random.intRangeAtMost(T, at_least, at_most);
    }
};

test "reclaiming allocator keeps contents across a fixed random script" {
    var prng = std.Random.DefaultPrng.init(0x5eed_a110c);
    var choose: Prng = .{ .random = prng.random(), .left = max_ops };
    const ops = try script(std.testing.allocator, &choose);
    defer std.testing.allocator.free(ops);
    try run(std.testing.allocator, ops);
}
