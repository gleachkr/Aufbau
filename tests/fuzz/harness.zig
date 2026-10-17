//! What every fuzz target shares: a per-input time limit and memory cap,
//! the proof-case seeds, and replay of a saved crash.
//!
//! A target is a function from an `Input` to `void`; `run` hands it to
//! `std.testing.fuzz`. The fuzzer already fails an input that panics, leaks
//! or writes after free. The harness adds the two failures it cannot see:
//! an input that runs too long and one that holds too much memory. Both
//! panic, so the fuzzer saves the input like any other crash.
//!
//! The saved input is the byte stream the target's `Smith` read, so it only
//! means something to the target (and the harness version) that wrote it.
//! `zig build fuzz -Dfuzz-replay=<file>` (which sets `FUZZ_REPLAY`) re-runs
//! it once through each target instead of fuzzing, and the target writes
//! what it generated (`Input.dump`) into `<file>.<target>/`, ready to turn
//! into a plain regression fixture.
const std = @import("std");
const mm0 = @import("mm0");

const Smith = std.testing.Smith;

pub const Options = struct {
    /// Longest one input may run before the watchdog panics. The fuzz build
    /// runs about ten times slower than ReleaseFast, and CI slower again
    /// than a workstation, so this is generous on purpose; a target that
    /// runs proof search on the larger proof cases asks for more.
    time_limit_s: u32 = 10,
};

/// Most live bytes one input may hold.
const memory_cap: usize = 1 << 30;

pub const Input = struct {
    smith: *Smith,
    /// The fuzzer's per-input leak-checked allocator, under `memory_cap`.
    gpa: std.mem.Allocator,
    /// Where `dump` writes while replaying; null while fuzzing.
    replay_dir: ?std.Io.Dir,

    /// Record a generated input under `name` when replaying a crash.
    pub fn dump(self: Input, name: []const u8, bytes: []const u8) void {
        const dir = self.replay_dir orelse return;
        dir.writeFile(std.testing.io, .{ .sub_path = name, .data = bytes }) catch |err|
            std.debug.print("fuzz replay: cannot write {s}: {t}\n", .{ name, err });
    }
};

/// Fuzz `testOne` as the target `name`, or replay `FUZZ_REPLAY` through it.
pub fn run(
    comptime name: []const u8,
    comptime options: Options,
    context: anytype,
    comptime testOne: fn (@TypeOf(context), Input) anyerror!void,
) !void {
    const Context = @TypeOf(context);
    const one = struct {
        fn one(ctx: Context, smith: *Smith) anyerror!void {
            return runOne(ctx, smith, null, options, testOne);
        }
    }.one;

    const replay = std.testing.environ.getAlloc(std.testing.allocator, "FUZZ_REPLAY") catch |err| switch (err) {
        error.EnvironmentVariableMissing => return std.testing.fuzz(context, one, .{}),
        else => return err,
    };
    defer std.testing.allocator.free(replay);

    const io = std.testing.io;
    const bytes = try std.Io.Dir.cwd().readFileAlloc(io, replay, std.testing.allocator, .unlimited);
    defer std.testing.allocator.free(bytes);
    const out_path = try std.fmt.allocPrint(std.testing.allocator, "{s}.{s}", .{ replay, name });
    defer std.testing.allocator.free(out_path);
    var out = try std.Io.Dir.cwd().createDirPathOpen(io, out_path, .{});
    defer out.close(io);
    std.debug.print("fuzz replay: {s} through {s}, generated inputs in {s}/\n", .{ replay, name, out_path });

    var smith: Smith = .{ .in = bytes };
    try runOne(context, &smith, out, options, testOne);
}

fn runOne(
    context: anytype,
    smith: *Smith,
    replay_dir: ?std.Io.Dir,
    comptime options: Options,
    comptime testOne: fn (@TypeOf(context), Input) anyerror!void,
) anyerror!void {
    startWatchdog();
    input_deadline.store(now() + @as(i64, options.time_limit_s) * std.time.ns_per_s, .release);
    defer input_deadline.store(0, .release);

    var capped: Capped = .{ .child = std.testing.allocator };
    return testOne(context, .{
        .smith = smith,
        .gpa = capped.allocator(),
        .replay_dir = replay_dir,
    });
}

// ---- watchdog ----

/// When the running input becomes overdue (awake clock, ns); 0 between
/// inputs.
var input_deadline: std.atomic.Value(i64) = .init(0);
/// Inputs run one at a time on the test thread, so a plain flag will do.
var watchdog_started = false;

fn startWatchdog() void {
    if (watchdog_started) return;
    watchdog_started = true;
    const thread = std.Thread.spawn(.{}, watchdog, .{}) catch
        @panic("fuzz harness: cannot start the watchdog thread");
    thread.detach();
}

fn now() i64 {
    return @intCast(std.Io.Timestamp.now(std.testing.io, .awake).nanoseconds);
}

fn watchdog() void {
    while (true) {
        std.testing.io.sleep(.fromMilliseconds(250), .awake) catch {};
        const deadline = input_deadline.load(.acquire);
        if (deadline != 0 and now() > deadline)
            @panic("fuzz input exceeded the time limit");
    }
}

// ---- memory cap ----

/// Counts live bytes through to `child` and panics past `memory_cap`.
const Capped = struct {
    child: std.mem.Allocator,
    live: usize = 0,

    fn allocator(self: *Capped) std.mem.Allocator {
        return .{ .ptr = self, .vtable = &.{
            .alloc = alloc,
            .resize = resize,
            .remap = remap,
            .free = free,
        } };
    }

    fn grow(self: *Capped, old: usize, new: usize) void {
        self.live = self.live - old + new;
        if (self.live > memory_cap) @panic("fuzz input exceeded the memory cap");
    }

    fn alloc(ctx: *anyopaque, len: usize, alignment: std.mem.Alignment, ra: usize) ?[*]u8 {
        const self: *Capped = @ptrCast(@alignCast(ctx));
        const ptr = self.child.rawAlloc(len, alignment, ra) orelse return null;
        self.grow(0, len);
        return ptr;
    }

    fn resize(ctx: *anyopaque, memory: []u8, alignment: std.mem.Alignment, new_len: usize, ra: usize) bool {
        const self: *Capped = @ptrCast(@alignCast(ctx));
        if (!self.child.rawResize(memory, alignment, new_len, ra)) return false;
        self.grow(memory.len, new_len);
        return true;
    }

    fn remap(ctx: *anyopaque, memory: []u8, alignment: std.mem.Alignment, new_len: usize, ra: usize) ?[*]u8 {
        const self: *Capped = @ptrCast(@alignCast(ctx));
        const ptr = self.child.rawRemap(memory, alignment, new_len, ra) orelse return null;
        self.grow(memory.len, new_len);
        return ptr;
    }

    fn free(ctx: *anyopaque, memory: []u8, alignment: std.mem.Alignment, ra: usize) void {
        const self: *Capped = @ptrCast(@alignCast(ctx));
        self.child.rawFree(memory, alignment, ra);
        self.live -= memory.len;
    }
};

// ---- seeds ----

/// One proof case, its `import`s and `include`s joined into single texts.
pub const Seed = struct {
    stem: []const u8,
    mm0: []const u8,
    /// Empty when the case has no proof file.
    auf: []const u8,
};

var seed_arena: std.heap.ArenaAllocator = .init(std.heap.page_allocator);
var loaded_seeds: ?[]const Seed = null;

/// The proof-case seeds, loaded on first use and kept for the process: the
/// fuzzer calls a test again for every batch of inputs.
pub fn seeds() ![]const Seed {
    if (loaded_seeds) |loaded| return loaded;
    loaded_seeds = try loadSeeds(seed_arena.allocator());
    return loaded_seeds.?;
}

/// Each seed's compiled binary, made the first time an input asks for it
/// and kept for the process, like the seeds.
const Compiled = union(enum) { untried, failed, mmb: []const u8 };
var compiled: []Compiled = &.{};

/// The binary this compiler makes for `seeds[index]`, or null when the
/// seed does not compile or verify cleanly (`by sorry!` included).
pub fn compiledSeed(all: []const Seed, index: usize) !?[]const u8 {
    if (compiled.len == 0) {
        compiled = try std.heap.page_allocator.alloc(Compiled, all.len);
        @memset(compiled, .untried);
    }
    if (compiled[index] == .untried) {
        // Outside the per-input allocator: the binary outlives the input.
        const gpa = std.heap.smp_allocator;
        const seed = all[index];
        var compiler = mm0.Compiler.initWithProof(gpa, seed.mm0, seed.auf);
        compiled[index] = if (compiler.compileMmb(gpa)) |mmb| verified: {
            mm0.verifyPair(gpa, seed.mm0, mmb) catch |err| {
                gpa.free(mmb);
                if (err == error.OutOfMemory) return err;
                break :verified .failed;
            };
            break :verified .{ .mmb = mmb };
        } else |err| switch (err) {
            error.OutOfMemory => return err,
            else => .failed,
        };
    }
    return switch (compiled[index]) {
        .untried => unreachable,
        .failed => null,
        .mmb => |mmb| mmb,
    };
}

/// Every case under tests/proof_cases that joins, sorted by stem so a
/// saved input picks the same seed on every machine. Lives in `arena`.
fn loadSeeds(arena: std.mem.Allocator) ![]const Seed {
    const io = std.testing.io;
    var dir = try std.Io.Dir.cwd().openDir(io, "tests/proof_cases", .{ .iterate = true });
    defer dir.close(io);
    var out: std.ArrayList(Seed) = .empty;
    var it = dir.iterate();
    while (try it.next(io)) |entry| {
        if (entry.kind != .file or !std.mem.endsWith(u8, entry.name, ".mm0")) continue;
        const stem = try arena.dupe(u8, entry.name[0 .. entry.name.len - ".mm0".len]);
        const path = try std.fmt.allocPrint(arena, "tests/proof_cases/{s}", .{entry.name});
        var failure: ?mm0.Imports.LoadFailure = null;
        // The fail_import_* / fail_include_* cases do not join; skip them.
        const pair = mm0.Imports.loadPair(io, arena, path, null, &failure) catch continue;
        try out.append(arena, .{
            .stem = stem,
            .mm0 = pair.mm0.text,
            .auf = if (pair.proof) |proof| proof.text else "",
        });
    }
    std.mem.sort(Seed, out.items, {}, struct {
        fn lessThan(_: void, a: Seed, b: Seed) bool {
            return std.mem.lessThan(u8, a.stem, b.stem);
        }
    }.lessThan);
    return out.items;
}

test "seeds load and include joined multi-file cases" {
    const all = try seeds();
    try std.testing.expect(all.len > 300);
    for (all) |seed| {
        if (!std.mem.eql(u8, seed.stem, "pass_import_diamond")) continue;
        try std.testing.expect(!mm0.Imports.hasImports(seed.mm0, .mm0));
        return;
    }
    return error.TestExpectedSeed;
}

test "capped allocator counts live bytes" {
    var capped: Capped = .{ .child = std.testing.allocator };
    const gpa = capped.allocator();
    const a = try gpa.alloc(u8, 100);
    const b = try gpa.realloc(a, 300);
    try std.testing.expectEqual(@as(usize, 300), capped.live);
    gpa.free(b);
    try std.testing.expectEqual(@as(usize, 0), capped.live);
}
