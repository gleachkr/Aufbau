//! An allocator that reuses what is freed and frees, at `deinit`, whatever
//! is still live.
//!
//! The search works through one allocator per call (`search/source.zig`).
//! A bump arena there leaks nothing past the call, but it reuses nothing
//! during it: every candidate clone, child-search scope and scratch map the
//! search frees stays allocated until the call returns, so memory grows with
//! the work done (about 85 MB per billion ticks on Pelletier problems).
//!
//! Small blocks are rounded up to a power-of-two size class and cut from a
//! bump arena; a freed block goes on its class's free list and is handed out
//! again by the next request of that class. There is no per-block header:
//! `free` and `resize` get the block's length, which names its class (a
//! `resize` never moves a block to another class). Large or over-aligned
//! blocks come from the child allocator with a header that keeps them on an
//! intrusive list. `deinit` releases the arena and every large block still
//! on the list, so anything a caller never freed is reclaimed, as the arena
//! did. Single-threaded, like the frontend arena.
//!
//! Free lists never hand memory back to the arena, and a block never moves
//! to another class, so each class keeps its peak footprint reserved until
//! `deinit`.
//!
//! The bump arena ignored a double free, a free through the wrong allocator
//! or a free with the wrong length; here each would put a block on the wrong
//! free list, or on one twice. Safe builds therefore keep a set of the blocks
//! handed out, with their classes, and panic on any free, resize or remap of
//! a block that is not in it at that class. Fast builds do not check.

const std = @import("std");
const ArenaAllocator = @import("./arena_allocator.zig").ArenaAllocator;

const Allocator = std.mem.Allocator;
const Alignment = std.mem.Alignment;

pub const ReclaimingAllocator = struct {
    child_allocator: Allocator,
    /// Backs every small block, used or free.
    small: ArenaAllocator,
    /// Free small blocks, one list per size class.
    free_lists: [class_count]?*FreeBlock = @splat(null),
    /// Most recent live large block first.
    head: ?*Header = null,
    /// Safe builds only: the address of every block handed out, with its
    /// class (`large_class` for a large block).
    live: LiveSet = if (std.debug.runtime_safety) .empty else {},

    /// Size classes run from `min_block` to `max_small` bytes in powers of
    /// two; anything bigger, or aligned beyond `small_alignment`, is large.
    const min_block_log2 = 4;
    const max_small_log2 = 16;
    const min_block: usize = 1 << min_block_log2;
    pub const max_small: usize = 1 << max_small_log2;
    const class_count = max_small_log2 - min_block_log2 + 1;
    const small_alignment: Alignment = .@"16";
    const large_class: u8 = class_count;

    const LiveSet = if (std.debug.runtime_safety) std.AutoHashMapUnmanaged(usize, u8) else void;

    const FreeBlock = struct { next: ?*FreeBlock };

    const Header = struct {
        prev: ?*Header,
        next: ?*Header,
        /// Length the caller sees, kept current across `resize`.
        len: usize,
        /// Bytes from the start of the child allocation to the caller's
        /// pointer; the header occupies the last `@sizeOf(Header)` of them.
        prefix: u32,
        alignment: Alignment,
    };
    const header_alignment: Alignment = .of(Header);

    pub fn init(child_allocator: Allocator) ReclaimingAllocator {
        return .{ .child_allocator = child_allocator, .small = .init(child_allocator) };
    }

    /// Frees every block still live.
    pub fn deinit(self: *ReclaimingAllocator) void {
        self.small.deinit();
        var it = self.head;
        while (it) |header| {
            it = header.next;
            self.child_allocator.rawFree(childSlice(header), childAlignment(header.alignment), @returnAddress());
        }
        if (std.debug.runtime_safety) self.live.deinit(self.child_allocator);
        self.* = undefined;
    }

    pub fn allocator(self: *ReclaimingAllocator) Allocator {
        return .{
            .ptr = self,
            .vtable = &.{
                .alloc = alloc,
                .resize = resize,
                .remap = remap,
                .free = free,
            },
        };
    }

    fn isSmall(len: usize, alignment: Alignment) bool {
        return len <= max_small and alignment.compare(.lte, small_alignment);
    }

    fn classOf(len: usize) usize {
        if (len <= min_block) return 0;
        return std.math.log2_int_ceil(usize, len) - min_block_log2;
    }

    fn classSize(class: usize) usize {
        return min_block << @intCast(class);
    }

    /// Makes room to record one more live block; false when that fails.
    fn reserveLive(self: *ReclaimingAllocator) bool {
        if (!std.debug.runtime_safety) return true;
        self.live.ensureUnusedCapacity(self.child_allocator, 1) catch return false;
        return true;
    }

    fn addLive(self: *ReclaimingAllocator, memory: [*]u8, class: u8) void {
        if (std.debug.runtime_safety) self.live.putAssumeCapacityNoClobber(@intFromPtr(memory), class);
    }

    fn removeLive(self: *ReclaimingAllocator, memory: [*]u8) void {
        if (std.debug.runtime_safety) _ = self.live.remove(@intFromPtr(memory));
    }

    /// Safe builds: panics unless `memory` is a live block whose length and
    /// alignment name the class it was handed out at.
    fn checkLive(self: *ReclaimingAllocator, memory: []u8, alignment: Alignment) void {
        if (!std.debug.runtime_safety) return;
        const class = self.live.get(@intFromPtr(memory.ptr)) orelse
            @panic("ReclaimingAllocator: free or resize of memory it did not hand out, or already freed");
        const small = isSmall(memory.len, alignment);
        const expected: u8 = if (small) @intCast(classOf(memory.len)) else large_class;
        if (class != expected or (!small and headerOf(memory.ptr).len != memory.len))
            @panic("ReclaimingAllocator: free or resize with the wrong length or alignment");
    }

    fn allocSmall(self: *ReclaimingAllocator, n: usize, ret_addr: usize) ?[*]u8 {
        const class = classOf(n);
        if (!self.reserveLive()) return null;
        const block: [*]u8 = if (self.free_lists[class]) |free_block| block: {
            self.free_lists[class] = free_block.next;
            break :block @ptrCast(free_block);
        } else self.small.allocator().rawAlloc(classSize(class), small_alignment, ret_addr) orelse
            return null;
        self.addLive(block, @intCast(class));
        return block;
    }

    fn freeSmall(self: *ReclaimingAllocator, memory: []u8) void {
        const class = classOf(memory.len);
        const block: *FreeBlock = @ptrCast(@alignCast(memory.ptr));
        block.next = self.free_lists[class];
        self.free_lists[class] = block;
    }

    fn childAlignment(alignment: Alignment) Alignment {
        return alignment.max(header_alignment);
    }

    fn prefixFor(alignment: Alignment) usize {
        return childAlignment(alignment).forward(@sizeOf(Header));
    }

    fn headerOf(memory: [*]u8) *Header {
        return @ptrCast(@alignCast(memory - @sizeOf(Header)));
    }

    fn childSlice(header: *Header) []u8 {
        const user: [*]u8 = @as([*]u8, @ptrCast(header)) + @sizeOf(Header);
        return (user - header.prefix)[0 .. header.prefix + header.len];
    }

    fn alloc(ctx: *anyopaque, n: usize, alignment: Alignment, ret_addr: usize) ?[*]u8 {
        const self: *ReclaimingAllocator = @ptrCast(@alignCast(ctx));
        if (isSmall(n, alignment)) return self.allocSmall(n, ret_addr);
        const prefix = prefixFor(alignment);
        const total = std.math.add(usize, prefix, n) catch return null;
        if (!self.reserveLive()) return null;
        const base = self.child_allocator.rawAlloc(total, childAlignment(alignment), ret_addr) orelse
            return null;
        const user = base + prefix;
        const header = headerOf(user);
        header.* = .{
            .prev = null,
            .next = self.head,
            .len = n,
            .prefix = @intCast(prefix),
            .alignment = alignment,
        };
        if (self.head) |old| old.prev = header;
        self.head = header;
        self.addLive(user, large_class);
        return user;
    }

    fn resize(ctx: *anyopaque, memory: []u8, alignment: Alignment, new_len: usize, ret_addr: usize) bool {
        const self: *ReclaimingAllocator = @ptrCast(@alignCast(ctx));
        self.checkLive(memory, alignment);
        const small = isSmall(memory.len, alignment);
        if (small != isSmall(new_len, alignment)) return false;
        if (small) return classOf(memory.len) == classOf(new_len);
        const header = headerOf(memory.ptr);
        const total = std.math.add(usize, header.prefix, new_len) catch return false;
        if (!self.child_allocator.rawResize(childSlice(header), childAlignment(header.alignment), total, ret_addr))
            return false;
        header.len = new_len;
        return true;
    }

    fn remap(ctx: *anyopaque, memory: []u8, alignment: Alignment, new_len: usize, ret_addr: usize) ?[*]u8 {
        // A small block never moves, so only a large one remaps past what
        // `resize` allows.
        if (isSmall(memory.len, alignment) or isSmall(new_len, alignment))
            return if (resize(ctx, memory, alignment, new_len, ret_addr)) memory.ptr else null;
        const self: *ReclaimingAllocator = @ptrCast(@alignCast(ctx));
        self.checkLive(memory, alignment);
        const header = headerOf(memory.ptr);
        const prefix = header.prefix;
        const total = std.math.add(usize, prefix, new_len) catch return null;
        if (!self.reserveLive()) return null;
        const base = self.child_allocator.rawRemap(childSlice(header), childAlignment(header.alignment), total, ret_addr) orelse
            return null;
        const user = base + prefix;
        // The header moved with the block; point its neighbours at it.
        const moved = headerOf(user);
        moved.len = new_len;
        if (moved.prev) |prev| prev.next = moved else self.head = moved;
        if (moved.next) |next| next.prev = moved;
        self.removeLive(memory.ptr);
        self.addLive(user, large_class);
        return user;
    }

    fn free(ctx: *anyopaque, memory: []u8, alignment: Alignment, ret_addr: usize) void {
        const self: *ReclaimingAllocator = @ptrCast(@alignCast(ctx));
        self.checkLive(memory, alignment);
        self.removeLive(memory.ptr);
        if (isSmall(memory.len, alignment)) return self.freeSmall(memory);
        const header = headerOf(memory.ptr);
        if (header.prev) |prev| prev.next = header.next else self.head = header.next;
        if (header.next) |next| next.prev = header.prev;
        self.child_allocator.rawFree(childSlice(header), childAlignment(header.alignment), ret_addr);
    }
};

test "reclaiming allocator reuses freed blocks and reclaims the rest at deinit" {
    // `std.testing.allocator` fails the test on a leak or a bad free, so it
    // checks that deinit returns every block, small or large.
    var reclaiming = ReclaimingAllocator.init(std.testing.allocator);
    defer reclaiming.deinit();
    const a = reclaiming.allocator();

    // A freed small block is the next one handed out in its class.
    const first = try a.alloc(u8, 100);
    a.free(first);
    const again = try a.alloc(u8, 120);
    try std.testing.expectEqual(first.ptr, again.ptr);

    var kept: [64][]u8 = undefined;
    for (&kept, 0..) |*slot, i| {
        // Sizes on both sides of the small/large boundary.
        const size = 1 + (i * 4099) % 140_000;
        const freed = try a.alignedAlloc(u8, .@"64", size);
        try std.testing.expect(std.mem.isAligned(@intFromPtr(freed.ptr), 64));
        @memset(freed, 0xff);
        a.free(freed);
        slot.* = try a.alloc(u8, size);
        @memset(slot.*, @truncate(i));
    }
    // Free from the middle and both ends of the large list; leave the rest.
    a.free(kept[0]);
    a.free(kept[31]);
    a.free(kept[63]);
    for (kept[1..31], 1..) |slice, i| {
        for (slice) |byte| try std.testing.expectEqual(@as(u8, @truncate(i)), byte);
    }
}

test "reclaiming allocator resizes within a class and remaps large blocks" {
    var reclaiming = ReclaimingAllocator.init(std.testing.allocator);
    defer reclaiming.deinit();
    const a = reclaiming.allocator();

    const buf = try a.alloc(u8, 100);
    try std.testing.expect(a.resize(buf, 128));
    try std.testing.expect(!a.resize(buf, 129));

    // Lists growing side by side remap large blocks that sit in the middle
    // of the live list; the neighbours must follow, or deinit walks freed
    // memory.
    var lists: [3]std.ArrayListUnmanaged(u32) = @splat(.empty);
    defer for (&lists) |*list| list.deinit(a);
    for (0..100_000) |i| {
        for (&lists) |*list| try list.append(a, @intCast(i));
    }
    for (lists) |list| {
        for (list.items, 0..) |value, i| try std.testing.expectEqual(@as(u32, @intCast(i)), value);
    }
    const leftover = try a.alloc(u8, 1 << 20);
    _ = a.remap(leftover, 4 << 20);
}
