//! Failure-memo keys for goals that hold witness variables
//! (`docs/design_notes/shared_witness.md` C2).
//!
//! A goal holding wvars has no proof within a depth for the same reasons
//! as any goal that differs from it only in which wvars it holds, provided
//! the wvars stand under the same constraints. The key is the goal written
//! out with each wvar numbered in order of first occurrence (a subterm
//! without wvars is its canonical id, a bag's members are sorted by how
//! they are written), followed by each wvar's constraints:
//! - a γ wvar: whether it is a cut wvar, the variables it may not hold
//!   (its capture list and the variables eigenvariables of its level or
//!   above became) and which of the goal's eigenvariables are older than
//!   it;
//! - an eigenvariable: the variables it may not become, among those the
//!   goal or a fact mentions, since no other variable can meet it.
//!
//! Equal keys mean goals equal up to renaming their wvars, so a failure
//! recorded under one key holds for every goal with that key. Bag members
//! are visited in an order blind to which wvar a leaf is, so goals that
//! differ only in naming usually get the same key; when two members tie,
//! their `ExprId` order decides, and two renamings of one goal may then
//! get different keys, which costs a memo hit but never soundness.

const std = @import("std");
const ExprId = @import("../../../expr.zig").ExprId;
const Terms = @import("./terms.zig").Terms;
const terms_mod = @import("./terms.zig");
const WVars = @import("./wvars.zig").WVars;

pub const Error = terms_mod.Error;

pub const Keys = struct {
    allocator: std.mem.Allocator,
    /// Owns the variable lists; lives for the run.
    arena: std.mem.Allocator,
    terms: *Terms,
    wvars: *WVars,
    /// The variables the facts mention, sorted.
    fact_vars: []const ExprId,
    /// Per expression, a hash of its shape with every wvar leaf alike.
    shapes: std.AutoHashMapUnmanaged(ExprId, u64) = .empty,
    /// Per expression, the variables it mentions, sorted.
    var_sets: std.AutoHashMapUnmanaged(ExprId, []const ExprId) = .empty,
    // Scratch for one key.
    order: std.ArrayListUnmanaged(u32) = .empty,
    visited: std.AutoHashMapUnmanaged(ExprId, void) = .empty,
    bytes: std.ArrayListUnmanaged(u8) = .empty,

    pub fn deinit(self: *Keys) void {
        self.shapes.deinit(self.allocator);
        self.var_sets.deinit(self.allocator);
        self.order.deinit(self.allocator);
        self.visited.deinit(self.allocator);
        self.bytes.deinit(self.allocator);
        self.* = undefined;
    }

    /// The key of the resolved, canonical `goal`, which holds a wvar. It
    /// is valid until the next call.
    pub fn key(self: *Keys, goal: ExprId) Error![]const u8 {
        self.order.clearRetainingCapacity();
        self.visited.clearRetainingCapacity();
        self.bytes.clearRetainingCapacity();
        try self.collect(goal);
        try self.write(goal, &self.bytes);
        try self.put(@intCast(self.order.items.len));

        const goal_vars = try self.variables(goal);
        var list = std.ArrayListUnmanaged(ExprId).empty;
        defer list.deinit(self.allocator);
        for (self.order.items) |idx| {
            const wvar = self.wvars.vars.items[idx];
            list.clearRetainingCapacity();
            if (wvar.introduced_at) |at| {
                try self.bytes.append(self.allocator, 'e');
                const mentioned = try self.variables(try self.wvars.deref(at, null));
                for ([_][]const ExprId{ goal_vars, self.fact_vars }) |reachable| {
                    for (reachable) |variable| {
                        if (std.mem.indexOfScalar(ExprId, mentioned, variable) != null or
                            std.mem.indexOfScalar(ExprId, wvar.capture, variable) != null or
                            self.wvars.eigens.contains(variable))
                        {
                            try list.append(self.allocator, variable);
                        }
                    }
                }
                try self.putSet(list.items);
            } else {
                try self.bytes.append(self.allocator, if (wvar.cut) 'c' else 'g');
                try list.appendSlice(self.allocator, wvar.capture);
                var it = self.wvars.eigens.iterator();
                while (it.next()) |entry| {
                    if (entry.value_ptr.* >= wvar.level) try list.append(self.allocator, entry.key_ptr.*);
                }
                try self.putSet(list.items);
                for (self.order.items, 0..) |other, pos| {
                    const eigen = self.wvars.vars.items[other];
                    if (eigen.introduced_at != null and eigen.level < wvar.level) try self.put(@intCast(pos));
                }
                try self.put(std.math.maxInt(u32));
            }
        }
        return self.bytes.items;
    }

    fn put(self: *Keys, value: u32) Error!void {
        try putTo(self.allocator, &self.bytes, value);
    }

    /// `variables` sorted, without repeats, then a terminator.
    fn putSet(self: *Keys, variables_: []ExprId) Error!void {
        std.mem.sort(ExprId, variables_, {}, std.sort.asc(ExprId));
        var last: ?ExprId = null;
        for (variables_) |variable| {
            if (last == variable) continue;
            last = variable;
            try self.put(variable);
        }
        try self.put(std.math.maxInt(u32));
    }

    /// Record `expr`'s wvars in order of first occurrence, visiting bag
    /// members in shape order.
    fn collect(self: *Keys, expr: ExprId) Error!void {
        if (!try self.wvars.holdsWVar(expr)) return;
        if ((try self.visited.getOrPut(self.allocator, expr)).found_existing) return;
        switch (self.terms.theorem.interner.node(expr).*) {
            .variable => {},
            .placeholder => if (self.wvars.of(expr)) |idx| try self.order.append(self.allocator, idx),
            .app => |app| {
                if (self.terms.bagFor(app.term_id)) |combiner| {
                    const members = combiner.flatten(self.terms.theorem, expr) orelse return error.Unsupported;
                    const sorted = try self.allocator.dupe(ExprId, members.slice());
                    defer self.allocator.free(sorted);
                    const shapes = try self.allocator.alloc(u64, sorted.len);
                    defer self.allocator.free(shapes);
                    for (sorted, shapes) |member, *out| out.* = try self.shape(member);
                    const Order = struct {
                        shapes: []u64,
                        members: []ExprId,
                        pub fn lessThan(ctx: @This(), a: usize, b: usize) bool {
                            if (ctx.shapes[a] != ctx.shapes[b]) return ctx.shapes[a] < ctx.shapes[b];
                            return ctx.members[a] < ctx.members[b];
                        }
                        pub fn swap(ctx: @This(), a: usize, b: usize) void {
                            std.mem.swap(u64, &ctx.shapes[a], &ctx.shapes[b]);
                            std.mem.swap(ExprId, &ctx.members[a], &ctx.members[b]);
                        }
                    };
                    std.sort.pdqContext(0, sorted.len, Order{ .shapes = shapes, .members = sorted });
                    for (sorted) |member| try self.collect(member);
                    return;
                }
                for (app.args) |arg| try self.collect(arg);
            },
        }
    }

    /// Append `expr` to `out` with each wvar written as its position in
    /// `order`.
    fn write(self: *Keys, expr: ExprId, out: *std.ArrayListUnmanaged(u8)) Error!void {
        if (!try self.wvars.holdsWVar(expr)) {
            try putTo(self.allocator, out, 'g');
            return putTo(self.allocator, out, expr);
        }
        switch (self.terms.theorem.interner.node(expr).*) {
            .variable => unreachable,
            .placeholder => {
                const idx = self.wvars.of(expr).?;
                try putTo(self.allocator, out, 'w');
                try putTo(self.allocator, out, @intCast(std.mem.indexOfScalar(u32, self.order.items, idx).?));
            },
            .app => |app| {
                try putTo(self.allocator, out, 'a');
                try putTo(self.allocator, out, app.term_id);
                const combiner = self.terms.bagFor(app.term_id) orelse {
                    for (app.args) |arg| try self.write(arg, out);
                    return;
                };
                const members = combiner.flatten(self.terms.theorem, expr) orelse return error.Unsupported;
                const written = try self.allocator.alloc([]u8, members.len);
                var done: usize = 0;
                defer {
                    for (written[0..done]) |bytes| self.allocator.free(bytes);
                    self.allocator.free(written);
                }
                for (members.slice()) |member| {
                    var bytes = std.ArrayListUnmanaged(u8).empty;
                    errdefer bytes.deinit(self.allocator);
                    try self.write(member, &bytes);
                    written[done] = try bytes.toOwnedSlice(self.allocator);
                    done += 1;
                }
                std.mem.sort([]u8, written, {}, struct {
                    fn lessThan(_: void, a: []u8, b: []u8) bool {
                        return std.mem.order(u8, a, b) == .lt;
                    }
                }.lessThan);
                try putTo(self.allocator, out, @intCast(written.len));
                for (written) |bytes| try out.appendSlice(self.allocator, bytes);
            },
        }
    }

    /// A hash of `expr` that every wvar leaf of one sort shares. Valid for
    /// resolved expressions, the only kind asked about.
    fn shape(self: *Keys, expr: ExprId) Error!u64 {
        if (self.shapes.get(expr)) |known| return known;
        var hasher = std.hash.Wyhash.init(0);
        switch (self.terms.theorem.interner.node(expr).*) {
            .variable => {
                hasher.update("v");
                hasher.update(std.mem.asBytes(&expr));
            },
            .placeholder => if (self.wvars.of(expr)) |idx| {
                hasher.update(if (self.wvars.isEigen(idx)) "e" else "w");
                hasher.update(self.wvars.vars.items[idx].sort_name);
            } else {
                hasher.update("p");
                hasher.update(std.mem.asBytes(&expr));
            },
            .app => |app| {
                hasher.update("a");
                hasher.update(std.mem.asBytes(&app.term_id));
                if (self.terms.bagFor(app.term_id)) |combiner| {
                    const members = combiner.flatten(self.terms.theorem, expr) orelse return error.Unsupported;
                    const shapes = try self.allocator.alloc(u64, members.len);
                    defer self.allocator.free(shapes);
                    for (members.slice(), shapes) |member, *out| out.* = try self.shape(member);
                    std.mem.sort(u64, shapes, {}, std.sort.asc(u64));
                    hasher.update(std.mem.sliceAsBytes(shapes));
                } else {
                    for (app.args) |arg| {
                        const arg_shape = try self.shape(arg);
                        hasher.update(std.mem.asBytes(&arg_shape));
                    }
                }
            },
        }
        const result = hasher.final();
        try self.shapes.put(self.allocator, expr, result);
        return result;
    }

    /// The variables `expr` mentions, bound ones included, sorted. Valid
    /// for resolved expressions.
    pub fn variables(self: *Keys, expr: ExprId) Error![]const ExprId {
        if (self.var_sets.get(expr)) |known| return known;
        const result: []const ExprId = switch (self.terms.theorem.interner.node(expr).*) {
            .variable => try self.arena.dupe(ExprId, &.{expr}),
            .placeholder => &.{},
            .app => |app| blk: {
                var merged = std.ArrayListUnmanaged(ExprId).empty;
                defer merged.deinit(self.allocator);
                for (app.args) |arg| {
                    for (try self.variables(arg)) |variable| {
                        if (std.mem.indexOfScalar(ExprId, merged.items, variable) == null) {
                            try merged.append(self.allocator, variable);
                        }
                    }
                }
                std.mem.sort(ExprId, merged.items, {}, std.sort.asc(ExprId));
                break :blk try self.arena.dupe(ExprId, merged.items);
            },
        };
        try self.var_sets.put(self.allocator, expr, result);
        return result;
    }
};

fn putTo(allocator: std.mem.Allocator, out: *std.ArrayListUnmanaged(u8), value: u32) Error!void {
    try out.appendSlice(allocator, std.mem.asBytes(&value));
}
