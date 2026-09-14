const std = @import("std");

pub fn cloneMap(
    allocator: std.mem.Allocator,
    map: anytype,
) !@TypeOf(map) {
    var clone: @TypeOf(map) = .{};
    errdefer clone.deinit(allocator);

    var it = map.iterator();
    while (it.next()) |entry| {
        try clone.put(allocator, entry.key_ptr.*, entry.value_ptr.*);
    }
    return clone;
}

pub fn cloneManagedMap(
    allocator: std.mem.Allocator,
    src: anytype,
) !@TypeOf(src.*) {
    var clone = @TypeOf(src.*).init(allocator);
    errdefer clone.deinit();

    var it = src.iterator();
    while (it.next()) |entry| {
        try clone.put(entry.key_ptr.*, entry.value_ptr.*);
    }
    return clone;
}

/// Like `cloneManagedMap` for a map whose values are `ArrayListUnmanaged`s:
/// each list is copied, so appends to either map's lists never reach the
/// other's. (`cloneManagedMap` would copy the list headers by value and
/// leave both maps sharing one backing buffer.)
pub fn cloneManagedListMap(
    allocator: std.mem.Allocator,
    src: anytype,
) !@TypeOf(src.*) {
    var clone = @TypeOf(src.*).init(allocator);
    errdefer clone.deinit();

    var it = src.iterator();
    while (it.next()) |entry| {
        try clone.put(entry.key_ptr.*, try entry.value_ptr.clone(allocator));
    }
    return clone;
}
