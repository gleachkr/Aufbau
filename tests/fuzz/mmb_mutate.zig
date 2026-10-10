//! Mutation of MMB binaries, driven by a `Smith`.
//!
//! Raw edits (a byte, a word, a cut, a copy) find the parser's bounds
//! checks. Structured edits aim at what the parser hands the verifier:
//! they walk the header, the sort, term and theorem tables, the proof
//! stream and every unify stream, and rewrite one field or one command (its
//! opcode, its operand, or the whole command dropped or repeated).
const std = @import("std");
const mm0 = @import("mm0");
const Smith = std.testing.Smith;

/// At most this many edits per mutation.
const max_edits = 8;

const RawOp = enum(u8) { byte, word, cut, copy, truncate };

/// `bytes` with up to `max_edits` raw edits. The caller owns the result.
pub fn mutateBytes(gpa: std.mem.Allocator, smith: *Smith, bytes: []const u8) ![]u8 {
    var out: std.ArrayList(u8) = .fromOwnedSlice(try gpa.dupe(u8, bytes));
    errdefer out.deinit(gpa);
    var edits: usize = 0;
    while (edits < max_edits and out.items.len != 0 and !smith.eos()) : (edits += 1) {
        const at = smith.index(out.items.len);
        switch (smith.value(RawOp)) {
            .byte => out.items[at] = smith.value(u8),
            .word => {
                const start = at & ~@as(usize, 3);
                if (start + 4 <= out.items.len)
                    writeValue(out.items[start..][0..4], interesting(smith, out.items.len, readValue(out.items[start..][0..4])));
            },
            .cut => {
                const n = @min(smith.valueRangeAtMost(u8, 1, 16), out.items.len - at);
                out.replaceRangeAssumeCapacity(at, n, &.{});
            },
            .copy => {
                const from = smith.index(out.items.len);
                const n = @min(smith.valueRangeAtMost(u8, 1, 16), out.items.len - from);
                const copy = try gpa.dupe(u8, out.items[from .. from + n]);
                defer gpa.free(copy);
                try out.insertSlice(gpa, at, copy);
            },
            .truncate => out.shrinkRetainingCapacity(at),
        }
    }
    return out.toOwnedSlice(gpa);
}

const StructOp = enum(u8) { opcode, operand, drop, repeat };

/// `bytes` with up to `max_edits` structured edits. Falls back to leaving
/// the file alone when its header is too broken to walk. The caller owns
/// the result.
pub fn mutateStructure(gpa: std.mem.Allocator, smith: *Smith, bytes: []const u8) ![]u8 {
    var out: std.ArrayList(u8) = .fromOwnedSlice(try gpa.dupe(u8, bytes));
    errdefer out.deinit(gpa);
    var sites: std.ArrayList(Site) = .empty;
    defer sites.deinit(gpa);

    var edits: usize = 0;
    while (edits < max_edits and !smith.eos()) : (edits += 1) {
        sites.clearRetainingCapacity();
        try collectSites(gpa, out.items, &sites);
        if (sites.items.len == 0) break;
        const site = sites.items[smith.index(sites.items.len)];
        const op = smith.value(StructOp);
        switch (site.kind) {
            .field => {
                const field = out.items[site.pos..][0..site.width];
                writeValue(field, interesting(smith, out.items.len, readValue(field)));
            },
            .command => switch (op) {
                .opcode => {
                    const first = &out.items[site.pos];
                    const new_op = if (smith.value(bool))
                        known_ops[smith.index(known_ops.len)]
                    else
                        smith.value(u6);
                    first.* = (first.* & 0xC0) | new_op;
                },
                .operand => if (site.width > 1) {
                    const operand = out.items[site.pos + 1 .. site.pos + site.width];
                    writeValue(operand, interesting(smith, out.items.len, readValue(operand)));
                },
                .drop => out.replaceRangeAssumeCapacity(site.pos, site.width, &.{}),
                .repeat => {
                    const copy = try gpa.dupe(u8, out.items[site.pos .. site.pos + site.width]);
                    defer gpa.free(copy);
                    try out.insertSlice(gpa, site.pos, copy);
                },
            },
        }
    }
    return out.toOwnedSlice(gpa);
}

/// Every statement, proof and unify opcode the verifier knows.
const known_ops = [_]u6{
    0x00, 0x02, 0x04, 0x05, 0x06, 0x0D, 0x0E, // statements
    0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x1A, 0x1B, 0x1C, 0x1E, 0x1F, 0x20, // proofs
    0x30, 0x31, 0x32, 0x33, 0x36, // unify
};

const Site = struct {
    pos: usize,
    width: usize,
    kind: enum { field, command },
};

const header_fields = [_][2]usize{
    .{ 4, 1 }, // version
    .{ 5, 1 }, // num_sorts
    .{ 8, 4 }, // num_terms
    .{ 12, 4 }, // num_thms
    .{ 16, 4 }, // p_terms
    .{ 20, 4 }, // p_thms
    .{ 24, 4 }, // p_proof
    .{ 32, 8 }, // p_index
};

/// The editable places of `bytes`, as far as its header lets us walk.
fn collectSites(gpa: std.mem.Allocator, bytes: []const u8, sites: *std.ArrayList(Site)) !void {
    const header_len = @sizeOf(mm0.Header);
    if (bytes.len < header_len) return;
    for (header_fields) |field| try sites.append(gpa, .{ .pos = field[0], .width = field[1], .kind = .field });

    const num_sorts = bytes[5];
    for (0..@min(num_sorts, bytes.len - header_len)) |i|
        try sites.append(gpa, .{ .pos = header_len + i, .width = 1, .kind = .field });

    // Terms: num_args (u16), ret_sort (u8), p_data (u32); a def (high bit
    // of ret_sort) has a unify stream after its arguments and return.
    const num_terms = read(u32, bytes, 8);
    const p_terms = read(u32, bytes, 16);
    for (0..@min(num_terms, 1 << 16)) |i| {
        const entry = p_terms +| 8 * i;
        if (entry + 8 > bytes.len) break;
        try sites.append(gpa, .{ .pos = entry, .width = 2, .kind = .field });
        try sites.append(gpa, .{ .pos = entry + 2, .width = 1, .kind = .field });
        try sites.append(gpa, .{ .pos = entry + 4, .width = 4, .kind = .field });
        if (bytes[entry + 2] & 0x80 != 0) {
            const num_args = read(u16, bytes, entry);
            try collectStream(gpa, bytes, read(u32, bytes, entry + 4) +| 8 * (num_args + 1), bytes.len, sites);
        }
    }

    // Theorems: num_args (u16), p_data (u32); a unify stream after the
    // arguments.
    const num_thms = read(u32, bytes, 12);
    const p_thms = read(u32, bytes, 20);
    for (0..@min(num_thms, 1 << 16)) |i| {
        const entry = p_thms +| 8 * i;
        if (entry + 8 > bytes.len) break;
        try sites.append(gpa, .{ .pos = entry, .width = 2, .kind = .field });
        try sites.append(gpa, .{ .pos = entry + 4, .width = 4, .kind = .field });
        const num_args = read(u16, bytes, entry);
        try collectStream(gpa, bytes, read(u32, bytes, entry + 4) +| 8 * @as(usize, num_args), bytes.len, sites);
    }

    // Statements: each command's operand is the statement's length, and
    // its proof commands follow up to an End.
    var pos: usize = read(u32, bytes, 24);
    var statements: usize = 0;
    while (pos < bytes.len and statements < 1 << 16) : (statements += 1) {
        const cmd = mm0.Proof.Cmd.read(bytes, pos, bytes.len) catch break;
        try sites.append(gpa, .{ .pos = pos, .width = cmd.size, .kind = .command });
        if (cmd.op == 0 or cmd.data == 0) break;
        const next = pos +| cmd.data;
        try collectStream(gpa, bytes, pos + cmd.size, @min(next, bytes.len), sites);
        pos = next;
    }
}

/// Commands from `start` up to an End or `limit`.
fn collectStream(gpa: std.mem.Allocator, bytes: []const u8, start: usize, limit: usize, sites: *std.ArrayList(Site)) !void {
    var pos = start;
    var count: usize = 0;
    while (pos < limit and count < 1 << 16) : (count += 1) {
        const cmd = mm0.Proof.Cmd.read(bytes, pos, limit) catch return;
        try sites.append(gpa, .{ .pos = pos, .width = cmd.size, .kind = .command });
        if (cmd.op == 0) return;
        pos += cmd.size;
    }
}

fn read(comptime T: type, bytes: []const u8, pos: usize) usize {
    if (pos + @sizeOf(T) > bytes.len) return 0;
    return std.mem.readInt(T, bytes[pos..][0..@sizeOf(T)], .little);
}

fn readValue(field: []const u8) u64 {
    var value: u64 = 0;
    for (field, 0..) |byte, i| value |= @as(u64, byte) << @intCast(8 * i);
    return value;
}

fn writeValue(field: []u8, value: u64) void {
    for (field, 0..) |*byte, i| byte.* = @truncate(value >> @intCast(8 * i));
}

/// A value likely to sit on a boundary: small numbers, the old value
/// nudged by one, the file length, or the extremes of a field.
fn interesting(smith: *Smith, file_len: usize, old: u64) u64 {
    return switch (smith.valueRangeAtMost(u8, 0, 8)) {
        0 => 0,
        1 => 1,
        2 => old +% 1,
        3 => old -% 1,
        4 => file_len,
        5 => file_len -| 1,
        6 => 0x7FFF_FFFF,
        7 => std.math.maxInt(u64),
        else => smith.value(u64),
    };
}

test "structured edits find sites in a real binary" {
    const io = std.testing.io;
    const bytes = try std.Io.Dir.cwd().readFileAlloc(io, "tests/mmb_mutants/tutorial.mmb", std.testing.allocator, .unlimited);
    defer std.testing.allocator.free(bytes);
    var sites: std.ArrayList(Site) = .empty;
    defer sites.deinit(std.testing.allocator);
    try collectSites(std.testing.allocator, bytes, &sites);
    var commands: usize = 0;
    for (sites.items) |site| {
        try std.testing.expect(site.pos + site.width <= bytes.len);
        if (site.kind == .command) commands += 1;
    }
    try std.testing.expect(commands > 50);
}
