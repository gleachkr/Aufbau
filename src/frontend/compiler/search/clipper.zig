const std = @import("std");

pub const SortId = u32;
pub const TermId = u32;
pub const Arity = u32;
pub const ChildIndex = u32;
pub const PathId = u32;
pub const ItemId = usize;

const bits_per_word = @bitSizeOf(u64);
const invalid_path: PathId = std.math.maxInt(PathId);

// Synthetic child index under which every member of an ACUI region is routed,
// erasing member position so the per-token BitSets union across members. Never
// collides with a real argument index.
const acui_slot: ChildIndex = std.math.maxInt(ChildIndex);

pub const Token = struct {
    term_id: TermId,
    arity: Arity,
};

pub const ConcreteNode = struct {
    token: Token,
    sort: SortId,
    children: []const ShapeNode = &.{},
};

// An ACUI region: its members, flattened, unit dropped, position erased. A
// variable member is a `.wildcard` (it becomes covering for the slot subtree).
// A plain non-combiner term of an ACUI sort is a one-member region; `emp` is a
// zero-member region.
pub const AcuiNode = struct {
    sort: SortId,
    members: []const ShapeNode = &.{},
};

pub const ShapeNode = union(enum) {
    concrete: ConcreteNode,
    wildcard: SortId,
    hole: SortId,
    acui: AcuiNode,

    fn sort(self: ShapeNode) SortId {
        return switch (self) {
            .concrete => |node| node.sort,
            .wildcard => |sort_id| sort_id,
            .hole => |sort_id| sort_id,
            .acui => |node| node.sort,
        };
    }
};

pub const BitSet = struct {
    words: std.ArrayListUnmanaged(u64) = .{},

    pub fn deinit(self: *BitSet, allocator: std.mem.Allocator) void {
        self.words.deinit(allocator);
    }

    pub fn clone(
        self: *const BitSet,
        allocator: std.mem.Allocator,
    ) !BitSet {
        var result = BitSet{};
        errdefer result.deinit(allocator);
        try result.words.appendSlice(allocator, self.words.items);
        return result;
    }

    pub fn full(
        allocator: std.mem.Allocator,
        bit_count: usize,
    ) !BitSet {
        var result = BitSet{};
        errdefer result.deinit(allocator);
        const word_count = wordCount(bit_count);
        try result.words.appendNTimes(allocator, 0, word_count);
        @memset(result.words.items, std.math.maxInt(u64));
        result.clearUnusedBits(bit_count);
        return result;
    }

    pub fn set(
        self: *BitSet,
        allocator: std.mem.Allocator,
        bit: usize,
    ) !void {
        const index = wordIndex(bit);
        if (index >= self.words.items.len) {
            try self.words.appendNTimes(
                allocator,
                0,
                index + 1 - self.words.items.len,
            );
        }
        self.words.items[index] |= bitMask(bit);
    }

    pub fn get(self: *const BitSet, bit: usize) bool {
        const index = wordIndex(bit);
        if (index >= self.words.items.len) return false;
        return (self.words.items[index] & bitMask(bit)) != 0;
    }

    pub fn unionWith(
        self: *BitSet,
        allocator: std.mem.Allocator,
        other: *const BitSet,
    ) !void {
        if (other.words.items.len > self.words.items.len) {
            try self.words.appendNTimes(
                allocator,
                0,
                other.words.items.len - self.words.items.len,
            );
        }
        for (other.words.items, 0..) |word, index| {
            self.words.items[index] |= word;
        }
    }

    /// `self &= (a | b)`, treating words past either operand's length as
    /// zero. Fused, allocation-free form of `clone(a)` + `unionWith(b)` +
    /// `intersectWith` for the query hot path.
    pub fn intersectWithUnionOf(
        self: *BitSet,
        a: *const BitSet,
        b: *const BitSet,
    ) void {
        for (self.words.items, 0..) |*word, index| {
            const a_word = if (index < a.words.items.len)
                a.words.items[index]
            else
                0;
            const b_word = if (index < b.words.items.len)
                b.words.items[index]
            else
                0;
            word.* &= a_word | b_word;
        }
    }

    pub fn intersectWith(self: *BitSet, other: *const BitSet) void {
        const shared_len = @min(self.words.items.len, other.words.items.len);
        for (self.words.items[0..shared_len], 0..) |*word, index| {
            word.* &= other.words.items[index];
        }
        if (shared_len < self.words.items.len) {
            @memset(self.words.items[shared_len..], 0);
        }
    }

    pub fn isEmpty(self: *const BitSet) bool {
        for (self.words.items) |word| {
            if (word != 0) return false;
        }
        return true;
    }

    pub fn collect(
        self: *const BitSet,
        allocator: std.mem.Allocator,
        bit_count: usize,
    ) ![]ItemId {
        var result = std.ArrayListUnmanaged(ItemId){};
        errdefer result.deinit(allocator);
        var bit: usize = 0;
        while (bit < bit_count) : (bit += 1) {
            if (self.get(bit)) try result.append(allocator, bit);
        }
        return result.toOwnedSlice(allocator);
    }

    fn clearUnusedBits(self: *BitSet, bit_count: usize) void {
        if (bit_count == 0 or self.words.items.len == 0) return;
        const used_bits = bit_count % bits_per_word;
        if (used_bits == 0) return;
        const mask = (@as(u64, 1) << @intCast(used_bits)) - 1;
        self.words.items[self.words.items.len - 1] &= mask;
    }
};

fn wordCount(bit_count: usize) usize {
    return (bit_count + bits_per_word - 1) / bits_per_word;
}

fn wordIndex(bit: usize) usize {
    return bit / bits_per_word;
}

fn bitMask(bit: usize) u64 {
    return @as(u64, 1) << @intCast(bit % bits_per_word);
}

const PathStep = struct {
    parent: PathId,
    child: ChildIndex,
};

const PathNode = struct {
    parent: PathId,
    child: ChildIndex,
};

const PathCell = struct {
    concrete_by_token: std.AutoHashMapUnmanaged(Token, BitSet) = .empty,
    new_wild_by_sort: std.AutoHashMapUnmanaged(SortId, BitSet) = .empty,
    present_by_sort: std.AutoHashMapUnmanaged(SortId, BitSet) = .empty,

    fn deinit(self: *PathCell, allocator: std.mem.Allocator) void {
        deinitBitSetMap(Token, &self.concrete_by_token, allocator);
        deinitBitSetMap(SortId, &self.new_wild_by_sort, allocator);
        deinitBitSetMap(SortId, &self.present_by_sort, allocator);
    }
};

fn deinitBitSetMap(
    comptime K: type,
    map: *std.AutoHashMapUnmanaged(K, BitSet),
    allocator: std.mem.Allocator,
) void {
    var values = map.valueIterator();
    while (values.next()) |bits| {
        bits.deinit(allocator);
    }
    map.deinit(allocator);
}

const PathInterner = struct {
    nodes: std.ArrayListUnmanaged(PathNode) = .{},
    children: std.AutoHashMapUnmanaged(PathStep, PathId) = .empty,

    fn init(allocator: std.mem.Allocator) !PathInterner {
        var result = PathInterner{};
        errdefer result.deinit(allocator);
        try result.nodes.append(allocator, .{
            .parent = invalid_path,
            .child = 0,
        });
        return result;
    }

    fn deinit(self: *PathInterner, allocator: std.mem.Allocator) void {
        self.children.deinit(allocator);
        self.nodes.deinit(allocator);
    }

    fn internPath(
        self: *PathInterner,
        allocator: std.mem.Allocator,
        path: []const ChildIndex,
    ) !PathId {
        var current: PathId = 0;
        for (path) |child| {
            current = try self.internChild(allocator, current, child);
        }
        return current;
    }

    fn internChild(
        self: *PathInterner,
        allocator: std.mem.Allocator,
        parent: PathId,
        child: ChildIndex,
    ) !PathId {
        const step = PathStep{ .parent = parent, .child = child };
        const gop = try self.children.getOrPut(allocator, step);
        if (gop.found_existing) return gop.value_ptr.*;
        const id: PathId = @intCast(self.nodes.items.len);
        try self.nodes.append(allocator, .{ .parent = parent, .child = child });
        gop.value_ptr.* = id;
        return id;
    }

    fn lookupPath(
        self: *const PathInterner,
        path: []const ChildIndex,
    ) ?PathId {
        var current: PathId = 0;
        for (path) |child| {
            current = self.lookupChild(current, child) orelse return null;
        }
        return current;
    }

    fn lookupChild(
        self: *const PathInterner,
        parent: PathId,
        child: ChildIndex,
    ) ?PathId {
        return self.children.get(.{ .parent = parent, .child = child });
    }
};

const ActiveWildcards = struct {
    covering: BitSet = .{},

    fn deinit(self: *ActiveWildcards, allocator: std.mem.Allocator) void {
        self.covering.deinit(allocator);
    }

    fn clone(
        self: *const ActiveWildcards,
        allocator: std.mem.Allocator,
    ) !ActiveWildcards {
        return .{ .covering = try self.covering.clone(allocator) };
    }

    fn add(
        self: *ActiveWildcards,
        allocator: std.mem.Allocator,
        bits: *const BitSet,
    ) !void {
        try self.covering.unionWith(allocator, bits);
    }
};

pub const Index = struct {
    allocator: std.mem.Allocator,
    paths: PathInterner,
    cells: std.ArrayListUnmanaged(PathCell) = .{},
    item_count: usize = 0,

    pub fn init(allocator: std.mem.Allocator) !Index {
        var result = Index{
            .allocator = allocator,
            .paths = try PathInterner.init(allocator),
        };
        errdefer result.deinit();
        try result.cells.append(allocator, .{});
        return result;
    }

    pub fn deinit(self: *Index) void {
        for (self.cells.items) |*cell| {
            cell.deinit(self.allocator);
        }
        self.cells.deinit(self.allocator);
        self.paths.deinit(self.allocator);
    }

    pub fn addItem(self: *Index) ItemId {
        const item = self.item_count;
        self.item_count += 1;
        return item;
    }

    pub fn insertConcrete(
        self: *Index,
        path: []const ChildIndex,
        token: Token,
        sort: SortId,
        item: ItemId,
    ) !void {
        try self.requireItem(item);
        const path_id = try self.internPath(path);
        var cell = &self.cells.items[path_id];
        try putBit(Token, &cell.concrete_by_token, self.allocator, token, item);
        try putBit(SortId, &cell.present_by_sort, self.allocator, sort, item);
    }

    pub fn insertStoredWildcard(
        self: *Index,
        path: []const ChildIndex,
        sort: SortId,
        item: ItemId,
    ) !void {
        try self.requireItem(item);
        const path_id = try self.internPath(path);
        var cell = &self.cells.items[path_id];
        try putBit(SortId, &cell.new_wild_by_sort, self.allocator, sort, item);
        try putBit(SortId, &cell.present_by_sort, self.allocator, sort, item);
    }

    // Mark an item present at `path` without making it covering: a wildcard /
    // hole query here matches it, but a descent (e.g. into an ACUI member slot)
    // still discriminates. Used for the ACUI region node itself.
    pub fn insertPresent(
        self: *Index,
        path: []const ChildIndex,
        sort: SortId,
        item: ItemId,
    ) !void {
        try self.requireItem(item);
        const path_id = try self.internPath(path);
        var cell = &self.cells.items[path_id];
        try putBit(SortId, &cell.present_by_sort, self.allocator, sort, item);
    }

    pub fn insertShape(
        self: *Index,
        item: ItemId,
        shape: ShapeNode,
    ) !void {
        var path = std.ArrayListUnmanaged(ChildIndex){};
        defer path.deinit(self.allocator);
        try self.insertShapeAt(item, shape, &path);
    }

    pub fn query(self: *const Index, shape: ShapeNode) !BitSet {
        var live = try BitSet.full(self.allocator, self.item_count);
        errdefer live.deinit(self.allocator);
        var active = ActiveWildcards{};
        defer active.deinit(self.allocator);
        const path_id = self.paths.lookupPath(&.{}) orelse return live;
        try self.queryAt(shape, path_id, &live, &active);
        return live;
    }

    pub fn collect(
        self: *const Index,
        bits: *const BitSet,
    ) ![]ItemId {
        return bits.collect(self.allocator, self.item_count);
    }

    fn insertShapeAt(
        self: *Index,
        item: ItemId,
        shape: ShapeNode,
        path: *std.ArrayListUnmanaged(ChildIndex),
    ) !void {
        switch (shape) {
            .concrete => |node| {
                try self.insertConcrete(path.items, node.token, node.sort, item);
                for (node.children, 0..) |child, index| {
                    try path.append(self.allocator, @intCast(index));
                    try self.insertShapeAt(item, child, path);
                    _ = path.pop();
                }
            },
            .wildcard => |sort_id| {
                try self.insertStoredWildcard(path.items, sort_id, item);
            },
            .hole => |sort_id| {
                try self.insertStoredWildcard(path.items, sort_id, item);
            },
            .acui => |node| {
                // Mark the region present at its own path so a wildcard / hole
                // query here (a bare context variable, `G ⊩ ...`) still matches,
                // without making it covering for the member sub-queries.
                try self.insertPresent(path.items, node.sort, item);
                // Route every member through the shared slot child; the per-token
                // BitSets union across members. A variable member lands in
                // new_wild_by_sort at the slot -> covering for the slot subtree
                // (not for Y, so it does not blanket sibling positions).
                try path.append(self.allocator, acui_slot);
                for (node.members) |member| {
                    try self.insertShapeAt(item, member, path);
                }
                _ = path.pop();
                // Zero members (emp) inserts nothing; emp only matches emp, and a
                // non-empty goal culls it for lack of a slot bucket.
            },
        }
    }

    fn queryAt(
        self: *const Index,
        shape: ShapeNode,
        path_id: PathId,
        live: *BitSet,
        active: *const ActiveWildcards,
    ) anyerror!void {
        // Clone the active wildcard set only when this cell actually widens
        // it; most cells add nothing for the query's sort, and the
        // unconditional per-node clone dominated query cost.
        const cell = &self.cells.items[path_id];
        if (cell.new_wild_by_sort.get(shape.sort())) |wild_bits| {
            var branch = try active.clone(self.allocator);
            defer branch.deinit(self.allocator);
            try branch.add(self.allocator, &wild_bits);
            return self.queryAtActive(shape, path_id, live, &branch);
        }
        return self.queryAtActive(shape, path_id, live, active);
    }

    // The node logic of `queryAt`, after the cell's new wildcards (if any)
    // have been folded into `active`.
    fn queryAtActive(
        self: *const Index,
        shape: ShapeNode,
        path_id: PathId,
        live: *BitSet,
        active: *const ActiveWildcards,
    ) anyerror!void {
        const cell = &self.cells.items[path_id];
        switch (shape) {
            .concrete => |node| {
                const token_bits =
                    cell.concrete_by_token.get(node.token) orelse BitSet{};
                live.intersectWithUnionOf(&token_bits, &active.covering);
                if (live.isEmpty()) return;

                for (node.children, 0..) |child, index| {
                    const child_id = self.paths.lookupChild(
                        path_id,
                        @intCast(index),
                    ) orelse {
                        if (!active.covering.isEmpty()) continue;
                        live.intersectWith(&BitSet{});
                        return;
                    };
                    try self.queryAt(child, child_id, live, active);
                    if (live.isEmpty()) return;
                }
            },
            .hole, .wildcard => |sort_id| {
                const present_bits =
                    cell.present_by_sort.get(sort_id) orelse BitSet{};
                live.intersectWithUnionOf(&present_bits, &active.covering);
            },
            .acui => |node| {
                // Empty region (emp) imposes no requirement.
                if (node.members.len == 0) return;

                const slot_id = self.paths.lookupChild(path_id, acui_slot) orelse {
                    // No stored item has members at this region; only items
                    // covered by an ancestor wildcard can still match.
                    live.intersectWith(&active.covering);
                    return;
                };

                // Several members collapse onto the same slot cell, so each
                // imposes an independent requirement: a fresh full sub-query per
                // member, AND-ed into `live`. A variable member imposes nothing.
                for (node.members) |member| {
                    switch (member) {
                        .wildcard => continue,
                        else => {},
                    }
                    var member_live = try BitSet.full(self.allocator, self.item_count);
                    defer member_live.deinit(self.allocator);
                    try self.queryAt(member, slot_id, &member_live, active);
                    live.intersectWith(&member_live);
                    if (live.isEmpty()) return;
                }
            },
        }
    }

    fn internPath(
        self: *Index,
        path: []const ChildIndex,
    ) !PathId {
        const before = self.paths.nodes.items.len;
        const path_id = try self.paths.internPath(self.allocator, path);
        while (self.cells.items.len < self.paths.nodes.items.len) {
            errdefer self.cells.shrinkRetainingCapacity(before);
            try self.cells.append(self.allocator, .{});
        }
        return path_id;
    }

    fn requireItem(self: *const Index, item: ItemId) !void {
        if (item >= self.item_count) return error.UnknownClipperItem;
    }
};

fn putBit(
    comptime K: type,
    map: *std.AutoHashMapUnmanaged(K, BitSet),
    allocator: std.mem.Allocator,
    key: K,
    item: ItemId,
) !void {
    const gop = try map.getOrPut(allocator, key);
    if (!gop.found_existing) gop.value_ptr.* = .{};
    try gop.value_ptr.set(allocator, item);
}

const s_wff: SortId = 1;
const s_obj: SortId = 2;
const s_set: SortId = 3;
const t_f: Token = .{ .term_id = 10, .arity = 1 };
const t_g: Token = .{ .term_id = 11, .arity = 1 };
const t_a: Token = .{ .term_id = 12, .arity = 0 };
const t_b: Token = .{ .term_id = 13, .arity = 0 };
const t_eq: Token = .{ .term_id = 14, .arity = 2 };
const t_p: Token = .{ .term_id = 15, .arity = 1 };

fn concrete(token: Token, sort_id: SortId, children: []const ShapeNode) ShapeNode {
    return .{ .concrete = .{
        .token = token,
        .sort = sort_id,
        .children = children,
    } };
}

fn expectItems(
    index: *const Index,
    query_shape: ShapeNode,
    expected: []const ItemId,
) !void {
    var bits = try index.query(query_shape);
    defer bits.deinit(index.allocator);
    const actual = try index.collect(&bits);
    defer index.allocator.free(actual);
    try std.testing.expectEqualSlices(ItemId, expected, actual);
}

test "clipper concrete lookup uses rigid tokens at paths" {
    var index = try Index.init(std.testing.allocator);
    defer index.deinit();
    const f_a_children = [_]ShapeNode{concrete(t_a, s_obj, &.{})};
    const g_a_children = [_]ShapeNode{concrete(t_a, s_obj, &.{})};
    const f_b_children = [_]ShapeNode{concrete(t_b, s_obj, &.{})};

    const item_f_a = index.addItem();
    const item_g_a = index.addItem();
    try index.insertShape(item_f_a, concrete(t_f, s_obj, &f_a_children));
    try index.insertShape(item_g_a, concrete(t_g, s_obj, &g_a_children));

    try expectItems(&index, concrete(t_f, s_obj, &f_a_children), &.{item_f_a});
    try expectItems(&index, concrete(t_f, s_obj, &f_b_children), &.{});
}

test "clipper stored wildcard covers deep query trees branch-locally" {
    var index = try Index.init(std.testing.allocator);
    defer index.deinit();
    const wildcard_item = index.addItem();
    const rigid_item = index.addItem();
    try index.insertShape(wildcard_item, .{ .wildcard = s_wff });
    const p_a_children = [_]ShapeNode{concrete(t_a, s_obj, &.{})};
    try index.insertShape(rigid_item, concrete(t_p, s_wff, &p_a_children));

    const p_b_children = [_]ShapeNode{concrete(t_b, s_obj, &.{})};
    try expectItems(
        &index,
        concrete(t_p, s_wff, &p_b_children),
        &.{wildcard_item},
    );
}

test "clipper goal holes are query wildcards" {
    var index = try Index.init(std.testing.allocator);
    defer index.deinit();
    const item = index.addItem();
    const p_a_children = [_]ShapeNode{concrete(t_a, s_obj, &.{})};
    const p_hole_children = [_]ShapeNode{.{ .hole = s_obj }};
    try index.insertShape(item, concrete(t_p, s_wff, &p_a_children));

    try expectItems(&index, concrete(t_p, s_wff, &p_hole_children), &.{item});
}

test "clipper sort-mismatched wildcards do not match" {
    var index = try Index.init(std.testing.allocator);
    defer index.deinit();
    const item = index.addItem();
    try index.insertShape(item, .{ .wildcard = s_set });
    const p_a_children = [_]ShapeNode{concrete(t_a, s_obj, &.{})};

    try expectItems(&index, concrete(t_p, s_wff, &p_a_children), &.{});
    try expectItems(&index, .{ .hole = s_wff }, &.{});
}

test "clipper deliberately allows repeated-binder false positives" {
    var index = try Index.init(std.testing.allocator);
    defer index.deinit();
    const repeated_binder_rule = index.addItem();
    const eq_same_children = [_]ShapeNode{
        .{ .wildcard = s_obj },
        .{ .wildcard = s_obj },
    };
    try index.insertShape(
        repeated_binder_rule,
        concrete(t_eq, s_wff, &eq_same_children),
    );

    const eq_distinct_children = [_]ShapeNode{
        concrete(t_a, s_obj, &.{}),
        concrete(t_b, s_obj, &.{}),
    };

    // This is a candidate-generation false positive.  A later unification
    // check must reject the candidate if both wildcard positions represent
    // the same binder and cannot consistently be assigned to `a` and `b`.
    try expectItems(
        &index,
        concrete(t_eq, s_wff, &eq_distinct_children),
        &.{repeated_binder_rule},
    );
}

test "clipper acui slot filters by member, variable members cover" {
    var index = try Index.init(std.testing.allocator);
    defer index.deinit();

    const a_leaf = [_]ShapeNode{concrete(t_a, s_obj, &.{})};
    const b_leaf = [_]ShapeNode{concrete(t_b, s_obj, &.{})};
    const wild_obj = [_]ShapeNode{.{ .wildcard = s_obj }};

    const f_a = concrete(t_f, s_wff, &a_leaf);
    const g_b = concrete(t_g, s_wff, &b_leaf);
    const p_b = concrete(t_p, s_wff, &b_leaf);

    // item 0: region { f(a), p(b) } — has a p-headed member
    const has_p_members = [_]ShapeNode{ f_a, p_b };
    // item 1: region { f(a), g(b) } — no p-headed member
    const no_p_members = [_]ShapeNode{ f_a, g_b };
    // item 2: region { *wff, f(a) } — variable member -> covering at the slot
    const var_members = [_]ShapeNode{ .{ .wildcard = s_wff }, f_a };

    const has_p = index.addItem();
    const no_p = index.addItem();
    const var_member = index.addItem();
    try index.insertShape(has_p, .{ .acui = .{ .sort = s_wff, .members = &has_p_members } });
    try index.insertShape(no_p, .{ .acui = .{ .sort = s_wff, .members = &no_p_members } });
    try index.insertShape(var_member, .{ .acui = .{ .sort = s_wff, .members = &var_members } });

    // query region { p(*obj), *wff }: a distinctive p-member plus a context var.
    // The wildcard member imposes nothing; the p-member culls `no_p`; the
    // variable-member item survives via slot covering.
    const query_p = [_]ShapeNode{
        concrete(t_p, s_wff, &wild_obj),
        .{ .wildcard = s_wff },
    };
    try expectItems(
        &index,
        .{ .acui = .{ .sort = s_wff, .members = &query_p } },
        &.{ has_p, var_member },
    );

    // Symmetric check: requiring a g-member keeps `no_p` and the covering item.
    const query_g = [_]ShapeNode{concrete(t_g, s_wff, &wild_obj)};
    try expectItems(
        &index,
        .{ .acui = .{ .sort = s_wff, .members = &query_g } },
        &.{ no_p, var_member },
    );

    // An absent member culls everything except the covering item.
    const query_absent = [_]ShapeNode{concrete(t_eq, s_wff, &.{})};
    try expectItems(
        &index,
        .{ .acui = .{ .sort = s_wff, .members = &query_absent } },
        &.{var_member},
    );

    // A bare wildcard query (a context variable `G`) matches every region,
    // since each is marked present at its own path.
    try expectItems(&index, .{ .wildcard = s_wff }, &.{ has_p, no_p, var_member });
}
