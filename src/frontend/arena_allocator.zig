//! A single-threaded arena: bump allocation out of a list of growing
//! chunks, freed all at once.
//!
//! Zig 0.17's `std.heap.ArenaAllocator` is lock-free and thread-safe: every
//! allocation pays an atomic add and usually a compare-and-swap. The compiler
//! and its search run on one thread and allocate small nodes at a high rate,
//! so the frontend uses this arena instead (#445; on the search depth bench
//! the atomics cost about 7% of cycles). Same interface subset as the std
//! arena: `init`, `deinit`, `allocator`, `reset`, `child_allocator`.
//!
//! Like the std arena, `free` and `resize` act only on the most recent
//! allocation; anything else is reclaimed when the arena is reset or freed,
//! or rewound to a `mark` taken before it (a stack of allocations).

const std = @import("std");

const Allocator = std.mem.Allocator;
const Alignment = std.mem.Alignment;

pub const ArenaAllocator = struct {
    child_allocator: Allocator,
    /// Most recent chunk first; allocation bumps `end_index` in it.
    chunks: ?*Chunk = null,
    end_index: usize = 0,
    /// Chunks a `rewind` emptied, smallest first, for the next ones needed.
    spare: ?*Chunk = null,

    /// A chunk's header; its buffer follows it in the same allocation.
    const Chunk = struct {
        next: ?*Chunk,
        /// Length of the whole allocation, header included.
        len: usize,

        fn buffer(chunk: *Chunk) []u8 {
            return @as([*]u8, @ptrCast(chunk))[@sizeOf(Chunk)..chunk.len];
        }

        fn allocation(chunk: *Chunk) []u8 {
            return @as([*]u8, @ptrCast(chunk))[0..chunk.len];
        }
    };
    const chunk_alignment: Alignment = .of(Chunk);

    pub fn init(child_allocator: Allocator) ArenaAllocator {
        return .{ .child_allocator = child_allocator };
    }

    pub fn deinit(self: ArenaAllocator) void {
        self.freeList(self.chunks);
        self.freeList(self.spare);
    }

    fn freeList(self: ArenaAllocator, first: ?*Chunk) void {
        var it = first;
        while (it) |chunk| {
            it = chunk.next;
            self.child_allocator.rawFree(chunk.allocation(), chunk_alignment, @returnAddress());
        }
    }

    /// The arena's extent, to `rewind` to.
    pub const Mark = struct {
        chunk: ?*Chunk,
        end_index: usize,
    };

    pub fn mark(self: *const ArenaAllocator) Mark {
        return .{ .chunk = self.chunks, .end_index = self.end_index };
    }

    /// Forgets every allocation made since `to` was taken. Marks are a
    /// stack: `to` must not predate a mark already rewound to, nor a reset.
    /// The chunks emptied are kept for the allocations that follow.
    pub fn rewind(self: *ArenaAllocator, to: Mark) void {
        while (self.chunks != to.chunk) {
            const chunk = self.chunks.?;
            self.chunks = chunk.next;
            chunk.next = self.spare;
            self.spare = chunk;
        }
        self.end_index = to.end_index;
    }

    pub fn allocator(self: *ArenaAllocator) Allocator {
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

    pub const ResetMode = enum {
        /// Return every chunk to the child allocator.
        free_all,
        /// Keep the most recent (largest) chunk for the next round.
        retain_capacity,
    };

    /// Forgets every allocation. Always succeeds; the result mirrors the std
    /// arena's signature.
    pub fn reset(self: *ArenaAllocator, mode: ResetMode) bool {
        const keep: ?*Chunk = switch (mode) {
            .free_all => null,
            .retain_capacity => self.chunks,
        };
        self.freeList(if (keep) |chunk| chunk.next else self.chunks);
        self.freeList(self.spare);
        self.spare = null;
        if (keep) |chunk| chunk.next = null;
        self.chunks = keep;
        self.end_index = 0;
        return true;
    }

    /// Prepends a chunk with room for `minimum` bytes: the first spare chunk
    /// that has it, after freeing the smaller ones before it, or a new one
    /// growing geometrically from the previous chunk's size.
    fn addChunk(self: *ArenaAllocator, prev_len: usize, minimum: usize) ?*Chunk {
        while (self.spare) |chunk| {
            self.spare = chunk.next;
            if (chunk.buffer().len >= minimum) {
                chunk.next = self.chunks;
                self.chunks = chunk;
                self.end_index = 0;
                return chunk;
            }
            self.child_allocator.rawFree(chunk.allocation(), chunk_alignment, @returnAddress());
        }
        const big_enough = prev_len + minimum + @sizeOf(Chunk) + 16;
        const len = big_enough + big_enough / 2;
        const ptr = self.child_allocator.rawAlloc(len, chunk_alignment, @returnAddress()) orelse
            return null;
        const chunk: *Chunk = @ptrCast(@alignCast(ptr));
        chunk.* = .{ .next = self.chunks, .len = len };
        self.chunks = chunk;
        self.end_index = 0;
        return chunk;
    }

    fn alloc(ctx: *anyopaque, n: usize, alignment: Alignment, ret_addr: usize) ?[*]u8 {
        _ = ret_addr;
        const self: *ArenaAllocator = @ptrCast(@alignCast(ctx));
        const align_bytes = alignment.toByteUnits();
        var chunk = self.chunks orelse
            (self.addChunk(0, n + align_bytes) orelse return null);
        while (true) {
            const buf = chunk.buffer();
            const addr = @intFromPtr(buf.ptr) + self.end_index;
            const start = self.end_index + (alignment.forward(addr) - addr);
            const end = start + n;
            if (end <= buf.len) {
                self.end_index = end;
                return buf.ptr + start;
            }
            const grown = @sizeOf(Chunk) + end;
            if (self.child_allocator.rawResize(chunk.allocation(), chunk_alignment, grown, @returnAddress())) {
                chunk.len = grown;
            } else {
                chunk = self.addChunk(buf.len, n + align_bytes) orelse return null;
            }
        }
    }

    /// Whether `memory` is the most recent allocation, the only one that can
    /// shrink back into the chunk or grow in place.
    fn isLast(self: *const ArenaAllocator, memory: []u8) bool {
        const chunk = self.chunks orelse return false;
        const buf = chunk.buffer();
        return @intFromPtr(buf.ptr) + self.end_index == @intFromPtr(memory.ptr) + memory.len;
    }

    fn resize(ctx: *anyopaque, memory: []u8, alignment: Alignment, new_len: usize, ret_addr: usize) bool {
        _ = alignment;
        _ = ret_addr;
        const self: *ArenaAllocator = @ptrCast(@alignCast(ctx));
        if (!self.isLast(memory)) return new_len <= memory.len;
        if (new_len <= memory.len) {
            self.end_index -= memory.len - new_len;
            return true;
        }
        const room = self.chunks.?.buffer().len - self.end_index;
        if (room < new_len - memory.len) return false;
        self.end_index += new_len - memory.len;
        return true;
    }

    fn remap(ctx: *anyopaque, memory: []u8, alignment: Alignment, new_len: usize, ret_addr: usize) ?[*]u8 {
        return if (resize(ctx, memory, alignment, new_len, ret_addr)) memory.ptr else null;
    }

    fn free(ctx: *anyopaque, memory: []u8, alignment: Alignment, ret_addr: usize) void {
        _ = alignment;
        _ = ret_addr;
        const self: *ArenaAllocator = @ptrCast(@alignCast(ctx));
        if (self.isLast(memory)) self.end_index -= memory.len;
    }
};

test "arena allocations stay aligned, distinct and reusable after reset" {
    var arena = ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();

    var round: usize = 0;
    while (round < 3) : (round += 1) {
        var total: usize = 0;
        var i: usize = 0;
        while (total < 20_000) : (i += 1) {
            const size = 1 + (i * 37) % 300;
            const slice = try a.alignedAlloc(u8, .@"32", size);
            try std.testing.expect(std.mem.isAligned(@intFromPtr(slice.ptr), 32));
            @memset(slice, @truncate(i));
            total += size;
        }
        _ = arena.reset(if (round == 1) .free_all else .retain_capacity);
    }
}

test "arena frees and resizes only its most recent allocation" {
    var arena = ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();

    const first = try a.alloc(u8, 16);
    const second = try a.alloc(u8, 16);
    try std.testing.expect(!a.resize(first, 32));
    try std.testing.expect(a.resize(first, 8));
    try std.testing.expect(a.resize(second, 24));
    const grown = second.ptr[0..24];
    a.free(grown);
    const third = try a.alloc(u8, 4);
    try std.testing.expectEqual(second.ptr, third.ptr);
}

test "arena rewinds to a mark and reuses the chunks it emptied" {
    var arena = ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();

    const kept = try a.alloc(u8, 16);
    @memset(kept, 7);
    const outer = arena.mark();
    var round: usize = 0;
    var first: ?[*]u8 = null;
    while (round < 3) : (round += 1) {
        const at = try a.alloc(u8, 8);
        if (first) |ptr| try std.testing.expectEqual(ptr, at.ptr) else first = at.ptr;
        const inner = arena.mark();
        // Enough to need new chunks, which the next round takes again.
        var total: usize = 0;
        while (total < 50_000) : (total += 500) @memset(try a.alloc(u8, 500), 1);
        arena.rewind(inner);
        try std.testing.expectEqual(inner.end_index, arena.end_index);
        arena.rewind(outer);
    }
    for (kept) |byte| try std.testing.expectEqual(7, byte);
    // A request larger than every spare chunk frees them or grows in place.
    @memset(try a.alloc(u8, 1 << 20), 2);
    _ = arena.reset(.retain_capacity);
    try std.testing.expect(arena.spare == null);
}
