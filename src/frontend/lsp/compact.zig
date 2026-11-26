//! Copies what a snapshot keeps out of the arena it was built in, so that
//! what building left there (the parses, the copies a growing list leaves
//! behind) goes with that arena. A slice of one of the indexed texts stays
//! a slice of it; anything else is copied, each string once however many
//! records share it.
const std = @import("std");
const model = @import("model.zig");

const Allocator = std.mem.Allocator;
const NameTable = model.NameTable;

pub const Compactor = struct {
    /// Where the copies go.
    arena: Allocator,
    /// Backs `strings`.
    allocator: Allocator,
    /// The indexed texts, which outlive the copies.
    texts: []const []const u8,
    /// The copy of each string copied so far, by its address and length.
    strings: std.AutoHashMapUnmanaged([2]usize, []const u8) = .empty,

    pub fn deinit(self: *Compactor) void {
        self.strings.deinit(self.allocator);
        self.* = undefined;
    }

    /// `value` with everything it points to copied. A type this cannot copy
    /// faithfully (a hash map, a many-item pointer) does not compile.
    pub fn copy(self: *Compactor, comptime T: type, value: T) Allocator.Error!T {
        if (comptime !pointsOut(T)) return value;
        switch (@typeInfo(T)) {
            .optional => |optional| {
                return if (value) |child| try self.copy(optional.child, child) else null;
            },
            .array => |array| {
                var out: T = undefined;
                for (&out, value) |*slot, item| slot.* = try self.copy(array.child, item);
                return out;
            },
            .@"struct" => |info| {
                var out: T = undefined;
                inline for (info.field_names, info.field_types) |name, Field| {
                    @field(out, name) = try self.copy(Field, @field(value, name));
                }
                return out;
            },
            .@"union" => |info| {
                if (info.tag_type == null) @compileError("cannot copy untagged " ++ @typeName(T));
                switch (value) {
                    inline else => |payload, tag| return @unionInit(
                        T,
                        @tagName(tag),
                        try self.copy(@TypeOf(payload), payload),
                    ),
                }
            },
            .pointer => |pointer| switch (pointer.size) {
                .one => {
                    const out = try self.arena.create(pointer.child);
                    out.* = try self.copy(pointer.child, value.*);
                    return out;
                },
                .slice => {
                    if (pointer.sentinel_ptr != null or !pointer.attrs.@"const") {
                        @compileError("cannot copy " ++ @typeName(T));
                    }
                    if (pointer.child == u8) return self.string(value);
                    if (value.len == 0) return &.{};
                    const out = try self.arena.alloc(pointer.child, value.len);
                    for (out, value) |*slot, item| slot.* = try self.copy(pointer.child, item);
                    return out;
                },
                else => @compileError("cannot copy " ++ @typeName(T)),
            },
            else => @compileError("cannot copy " ++ @typeName(T)),
        }
    }

    /// Whether a `T` can point outside itself, so that copying it means
    /// copying what it points to.
    fn pointsOut(comptime T: type) bool {
        return switch (@typeInfo(T)) {
            .bool, .int, .float, .@"enum", .void, .error_set => false,
            .optional => |optional| pointsOut(optional.child),
            .array => |array| pointsOut(array.child),
            .@"struct" => |info| for (info.field_types) |Field| {
                if (pointsOut(Field)) break true;
            } else false,
            .@"union" => |info| for (info.field_types) |Field| {
                if (pointsOut(Field)) break true;
            } else false,
            else => true,
        };
    }

    fn string(self: *Compactor, value: []const u8) Allocator.Error![]const u8 {
        if (value.len == 0) return "";
        const start = @intFromPtr(value.ptr);
        for (self.texts) |text| {
            const text_start = @intFromPtr(text.ptr);
            if (start >= text_start and start + value.len <= text_start + text.len) return value;
        }
        const slot = try self.strings.getOrPut(self.allocator, .{ start, value.len });
        if (!slot.found_existing) slot.value_ptr.* = try self.arena.dupe(u8, value);
        return slot.value_ptr.*;
    }

    pub fn nameTable(self: *Compactor, table: NameTable) Allocator.Error!NameTable {
        return .{
            .latest = try self.stringMap(NameTable.Entry, table.latest),
            .replaced = .fromOwnedSlice(try self.arena.dupe(NameTable.Entry, table.replaced.items)),
        };
    }

    pub fn stringMap(
        self: *Compactor,
        comptime V: type,
        map: std.StringHashMapUnmanaged(V),
    ) Allocator.Error!std.StringHashMapUnmanaged(V) {
        var out: std.StringHashMapUnmanaged(V) = .empty;
        try out.ensureTotalCapacity(self.arena, map.count());
        var it = map.iterator();
        while (it.next()) |entry| {
            out.putAssumeCapacityNoClobber(
                try self.string(entry.key_ptr.*),
                try self.copy(V, entry.value_ptr.*),
            );
        }
        return out;
    }
};
