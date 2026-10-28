//! Witness variables and eigenvariables for the search core
//! (`docs/design_notes/shared_witness.md` D1, D3, D5).
//!
//! A witness variable (wvar) is a `.meta` placeholder leaf minted in the
//! run's theorem. Its assignment lives here, never in the interner, and
//! every binding goes on one log that the search undoes as it backtracks.
//! A γ wvar stands for a binder a rule's conclusion does not fix and is
//! closed by unification.
//!
//! An eigenvariable (δ) is a wvar too, so its name is chosen only once the
//! proof needs one: a pool fact may state the goal for one particular
//! variable, and MM0 has no alpha-equivalence to rename it. It may become
//! a variable its introduction goal does not mention, and nothing else;
//! leftovers are named at close-out. Its level is the number of
//! eigenvariables introduced before it; a γ wvar's level is the number
//! introduced before it was minted. A γ wvar may hold an eigenvariable, or
//! the variable one became, only of a lower level (W6), which keeps every
//! eigenvariable out of the instances that existed before it. A
//! definition's dummy is an eigenvariable introduced at the unfolding that
//! holds it (`Terms.unfold`).
//!
//! A wvar also carries the variables bound inside the formula it was swapped
//! into: holding one of those would capture it.
//!
//! A cut wvar stands for a binder of a cut rule (`imp_trans`'s `q`); the
//! prover lets only a closure or a rule match that binds it work on a goal
//! that holds it unbound.

const std = @import("std");
const ExprModule = @import("../../../expr.zig");
const ExprId = ExprModule.ExprId;
const PlaceholderId = ExprModule.PlaceholderId;
const TheoremContext = ExprModule.TheoremContext;
const Context = @import("../types.zig").Context;

pub const Error = error{ OutOfMemory, TooManyTheoremExprs };

pub const WVar = struct {
    /// Its placeholder leaf.
    expr: ExprId,
    sort_name: []const u8,
    level: u32,
    /// Variables it may not hold.
    capture: []const ExprId,
    /// For an eigenvariable, the goal it was introduced at.
    introduced_at: ?ExprId = null,
    cut: bool = false,
    value: ?ExprId = null,
};

const Entry = union(enum) {
    bound: u32,
    /// A wvar inside a binding took the bound wvar's constraints.
    narrowed: struct { wvar: u32, level: u32, capture: []const ExprId },
    /// `variable` became an eigenvariable; `prev` is the level it had.
    named: struct { variable: ExprId, prev: ?u32 },
};

pub const WVars = struct {
    allocator: std.mem.Allocator,
    /// Owns capture lists; lives for the run.
    arena: std.mem.Allocator,
    context: *const Context,
    theorem: *TheoremContext,
    vars: std.ArrayListUnmanaged(WVar) = .empty,
    by_placeholder: std.AutoHashMapUnmanaged(PlaceholderId, u32) = .empty,
    log: std.ArrayListUnmanaged(Entry) = .empty,
    eigen_count: u32 = 0,
    /// The level of each variable an eigenvariable became.
    eigens: std.AutoHashMapUnmanaged(ExprId, u32) = .empty,
    /// Whether an expression has a wvar leaf.
    holds: std.AutoHashMapUnmanaged(ExprId, bool) = .empty,

    pub fn deinit(self: *WVars) void {
        self.vars.deinit(self.allocator);
        self.by_placeholder.deinit(self.allocator);
        self.log.deinit(self.allocator);
        self.eigens.deinit(self.allocator);
        self.holds.deinit(self.allocator);
        self.* = undefined;
    }

    /// The number of wvars minted so far; a wvar's index is below it.
    pub fn count(self: *const WVars) u32 {
        return @intCast(self.vars.items.len);
    }

    pub fn mark(self: *const WVars) usize {
        return self.log.items.len;
    }

    /// Undo every binding and introduction made since `to`.
    pub fn rollback(self: *WVars, to: usize) void {
        while (self.log.items.len > to) {
            switch (self.log.pop().?) {
                .bound => |idx| self.vars.items[idx].value = null,
                .narrowed => |old| {
                    self.vars.items[old.wvar].level = old.level;
                    self.vars.items[old.wvar].capture = old.capture;
                },
                .named => |old| if (old.prev) |level| {
                    self.eigens.getPtr(old.variable).?.* = level;
                } else {
                    _ = self.eigens.remove(old.variable);
                },
            }
        }
    }

    /// Whether a wvar with index below `older_than` was bound or narrowed
    /// since the log mark `since`.
    pub fn constrainedOlderSince(self: *const WVars, since: usize, older_than: u32) bool {
        for (self.log.items[since..]) |entry| switch (entry) {
            .bound => |idx| if (idx < older_than) return true,
            .narrowed => |old| if (old.wvar < older_than) return true,
            .named => {},
        };
        return false;
    }

    /// Append to `out` what the steps logged since `since` did to the wvars
    /// with index below `older_than`: each binding (with the younger wvars
    /// it holds numbered by first occurrence), narrowing, and naming of an
    /// eigenvariable, with levels above `level_cap` read as `level_cap`.
    /// Two runs that leave the same signature leave those wvars, and every
    /// later goal that can see only them, in the same state.
    pub fn signature(
        self: *WVars,
        allocator: std.mem.Allocator,
        since: usize,
        older_than: u32,
        level_cap: u32,
        out: *std.ArrayListUnmanaged(u8),
    ) Error!void {
        var young = std.ArrayListUnmanaged(u32).empty;
        defer young.deinit(allocator);
        for (self.log.items[since..]) |entry| switch (entry) {
            .bound => |idx| if (idx < older_than) {
                try putWord(allocator, out, 'b');
                try putWord(allocator, out, idx);
                try self.serialize(allocator, self.vars.items[idx].value.?, older_than, level_cap, &young, out);
            },
            .narrowed => |old| if (old.wvar < older_than) {
                const wvar = self.vars.items[old.wvar];
                try putWord(allocator, out, 'n');
                try putWord(allocator, out, old.wvar);
                try putWord(allocator, out, @min(wvar.level, level_cap));
                for (wvar.capture) |variable| try putWord(allocator, out, variable);
                try putWord(allocator, out, std.math.maxInt(u32));
            },
            .named => |named| {
                try putWord(allocator, out, 'v');
                try putWord(allocator, out, named.variable);
                try putWord(allocator, out, @min(self.eigens.get(named.variable).?, level_cap));
            },
        };
    }

    fn serialize(
        self: *WVars,
        allocator: std.mem.Allocator,
        expr: ExprId,
        older_than: u32,
        level_cap: u32,
        young: *std.ArrayListUnmanaged(u32),
        out: *std.ArrayListUnmanaged(u8),
    ) Error!void {
        const at = self.resolve(expr);
        if (!try self.holdsWVar(at)) {
            try putWord(allocator, out, 'g');
            return putWord(allocator, out, at);
        }
        switch (self.theorem.interner.node(at).*) {
            .variable => unreachable,
            .placeholder => {
                const idx = self.of(at).?;
                if (idx < older_than) {
                    try putWord(allocator, out, 'o');
                    return putWord(allocator, out, idx);
                }
                const pos = std.mem.indexOfScalar(u32, young.items, idx) orelse blk: {
                    try young.append(allocator, idx);
                    break :blk young.items.len - 1;
                };
                const wvar = self.vars.items[idx];
                try putWord(allocator, out, if (wvar.introduced_at != null) 'e' else if (wvar.cut) 'c' else 'y');
                try putWord(allocator, out, @intCast(pos));
                try putWord(allocator, out, @min(wvar.level, level_cap));
                for (wvar.capture) |variable| try putWord(allocator, out, variable);
                try putWord(allocator, out, std.math.maxInt(u32));
            },
            .app => |app| {
                try putWord(allocator, out, 'a');
                try putWord(allocator, out, app.term_id);
                for (app.args) |arg| try self.serialize(allocator, arg, older_than, level_cap, young, out);
            },
        }
    }

    /// A new γ wvar, or cut wvar when `cut`.
    pub fn mint(self: *WVars, sort_name: []const u8, capture: []const ExprId, cut: bool) Error!ExprId {
        return self.add(.{
            .expr = undefined,
            .sort_name = sort_name,
            .level = self.eigen_count,
            .capture = capture,
            .cut = cut,
        });
    }

    /// A new eigenvariable introduced at `goal`.
    pub fn introduce(self: *WVars, sort_name: []const u8, goal: ExprId) Error!ExprId {
        const expr = try self.add(.{
            .expr = undefined,
            .sort_name = sort_name,
            .level = self.eigen_count,
            .capture = &.{},
            .introduced_at = goal,
        });
        self.eigen_count += 1;
        return expr;
    }

    fn add(self: *WVars, wvar: WVar) Error!ExprId {
        const expr = self.theorem.addMetaPlaceholderResolved(wvar.sort_name) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            else => return error.TooManyTheoremExprs,
        };
        const pid = self.theorem.interner.node(expr).placeholder;
        try self.by_placeholder.put(self.allocator, pid, self.count());
        var entry = wvar;
        entry.expr = expr;
        try self.vars.append(self.allocator, entry);
        return expr;
    }

    pub fn isEigen(self: *const WVars, idx: u32) bool {
        return self.vars.items[idx].introduced_at != null;
    }

    /// The wvar `expr` is, if it is one.
    pub fn of(self: *const WVars, expr: ExprId) ?u32 {
        return switch (self.theorem.interner.node(expr).*) {
            .placeholder => |pid| self.by_placeholder.get(pid),
            else => null,
        };
    }

    /// `expr` with bound wvars at its head followed.
    pub fn resolve(self: *const WVars, expr: ExprId) ExprId {
        var at = expr;
        while (self.of(at)) |idx| at = self.vars.items[idx].value orelse return at;
        return at;
    }

    pub fn holdsWVar(self: *WVars, expr: ExprId) Error!bool {
        if (self.holds.get(expr)) |known| return known;
        const result = switch (self.theorem.interner.node(expr).*) {
            .variable => false,
            .placeholder => self.of(expr) != null,
            .app => |app| blk: {
                for (app.args) |arg| {
                    if (try self.holdsWVar(arg)) break :blk true;
                }
                break :blk false;
            },
        };
        try self.holds.put(self.allocator, expr, result);
        return result;
    }

    /// `expr` with every bound wvar replaced by its value, and each unbound
    /// one by `names`' entry when it has one.
    pub fn deref(self: *WVars, expr: ExprId, names: ?*const std.AutoHashMapUnmanaged(u32, ExprId)) Error!ExprId {
        if (!try self.holdsWVar(expr)) return expr;
        switch (self.theorem.interner.node(expr).*) {
            .variable => return expr,
            .placeholder => {
                const idx = self.of(expr).?;
                if (self.vars.items[idx].value) |value| return self.deref(value, names);
                if (names) |map| if (map.get(idx)) |name| return name;
                return expr;
            },
            .app => |app| {
                const args = try self.allocator.alloc(ExprId, app.args.len);
                defer self.allocator.free(args);
                var changed = false;
                for (app.args, args) |arg, *out| {
                    out.* = try self.deref(arg, names);
                    if (out.* != arg) changed = true;
                }
                if (!changed) return expr;
                return self.theorem.interner.internApp(app.term_id, args);
            },
        }
    }

    /// The unbound wvars of `expr`, after following bindings, once each.
    pub fn collectUnbound(
        self: *WVars,
        allocator: std.mem.Allocator,
        expr: ExprId,
        out: *std.ArrayListUnmanaged(u32),
    ) Error!void {
        if (!try self.holdsWVar(expr)) return;
        switch (self.theorem.interner.node(expr).*) {
            .variable => {},
            .placeholder => {
                const idx = self.of(expr).?;
                if (self.vars.items[idx].value) |value| return self.collectUnbound(allocator, value, out);
                if (std.mem.indexOfScalar(u32, out.items, idx) == null) try out.append(allocator, idx);
            },
            .app => |app| for (app.args) |arg| try self.collectUnbound(allocator, arg, out),
        }
    }

    /// Whether the variable `variable` occurs in `expr` (bound occurrences
    /// included), following bindings.
    pub fn mentions(self: *WVars, expr: ExprId, variable: ExprId) bool {
        const at = self.resolve(expr);
        if (at == variable) return true;
        return switch (self.theorem.interner.node(at).*) {
            .variable, .placeholder => false,
            .app => |app| for (app.args) |arg| {
                if (self.mentions(arg, variable)) break true;
            } else false,
        };
    }

    /// Whether wvar `idx` may hold, or as an eigenvariable become, the
    /// variable `variable`. An eigenvariable becomes only a bound variable.
    pub fn admits(self: *WVars, idx: u32, variable: ExprId) bool {
        const wvar = self.vars.items[idx];
        if (std.mem.indexOfScalar(ExprId, wvar.capture, variable) != null) return false;
        if (wvar.introduced_at) |goal| {
            const info = (self.theorem.currentLeafInfo(variable) catch null) orelse return false;
            if (!info.bound) return false;
            return !self.eigens.contains(variable) and !self.mentions(goal, variable);
        }
        const level = self.eigens.get(variable) orelse return true;
        return level < wvar.level;
    }

    /// Bind unbound wvar `idx` to `value`, unless that breaks its sort,
    /// occurs, capture or level constraint. Wvars inside `value` take on
    /// `idx`'s constraints, so binding them later cannot break them either.
    /// An eigenvariable binds only to a variable it admits; facing a γ wvar
    /// it binds that one instead. Returns false, logging nothing, when the
    /// binding is refused.
    pub fn bind(self: *WVars, idx: u32, value: ExprId) Error!bool {
        std.debug.assert(self.vars.items[idx].value == null);
        const wvar = self.vars.items[idx];
        if (!std.mem.eql(u8, self.sortOf(value) orelse return false, wvar.sort_name)) return false;
        if (wvar.introduced_at != null) return self.bindEigen(idx, self.resolve(value));
        const start = self.mark();
        errdefer self.rollback(start);
        if (!try self.constrain(idx, value)) {
            self.rollback(start);
            return false;
        }
        try self.log.append(self.allocator, .{ .bound = idx });
        self.vars.items[idx].value = value;
        return true;
    }

    fn bindEigen(self: *WVars, idx: u32, value: ExprId) Error!bool {
        switch (self.theorem.interner.node(value).*) {
            .variable => {},
            .placeholder => {
                const other = self.of(value) orelse return false;
                if (self.vars.items[other].introduced_at != null) return false;
                return self.bind(other, self.vars.items[idx].expr);
            },
            .app => return false,
        }
        if (!self.admits(idx, value)) return false;
        try self.eigens.ensureUnusedCapacity(self.allocator, 1);
        try self.log.ensureUnusedCapacity(self.allocator, 2);
        self.log.appendAssumeCapacity(.{ .named = .{ .variable = value, .prev = null } });
        self.eigens.putAssumeCapacity(value, self.vars.items[idx].level);
        self.log.appendAssumeCapacity(.{ .bound = idx });
        self.vars.items[idx].value = value;
        return true;
    }

    fn constrain(self: *WVars, idx: u32, expr: ExprId) Error!bool {
        const at = self.resolve(expr);
        switch (self.theorem.interner.node(at).*) {
            .variable => return self.admits(idx, at),
            .placeholder => {
                const other = self.of(at) orelse return true;
                if (other == idx) return false;
                const wvar = self.vars.items[idx];
                const target = &self.vars.items[other];
                if (target.introduced_at != null) {
                    // An eigenvariable inside: it must be older, and its
                    // name must stay clear of what `idx` would capture.
                    if (target.level >= wvar.level) return false;
                    if (wvar.capture.len == 0) return true;
                    try self.log.append(self.allocator, .{ .narrowed = .{
                        .wvar = other,
                        .level = target.level,
                        .capture = target.capture,
                    } });
                    target.capture = try std.mem.concat(self.arena, ExprId, &.{ target.capture, wvar.capture });
                    return true;
                }
                if (target.level <= wvar.level and wvar.capture.len == 0) return true;
                try self.log.append(self.allocator, .{ .narrowed = .{
                    .wvar = other,
                    .level = target.level,
                    .capture = target.capture,
                } });
                target.level = @min(target.level, wvar.level);
                if (wvar.capture.len != 0) {
                    target.capture = try std.mem.concat(self.arena, ExprId, &.{ target.capture, wvar.capture });
                }
                return true;
            },
            .app => |app| {
                for (app.args) |arg| {
                    if (!try self.constrain(idx, arg)) return false;
                }
                return true;
            },
        }
    }

    pub fn sortOf(self: *const WVars, expr: ExprId) ?[]const u8 {
        const at = self.resolve(expr);
        if (self.of(at)) |idx| return self.vars.items[idx].sort_name;
        return switch (self.theorem.interner.node(at).*) {
            .app => |app| self.context.env.terms.items[app.term_id].ret_sort_name,
            else => {
                const info = (self.theorem.currentLeafInfo(at) catch null) orelse return null;
                return info.sort_name;
            },
        };
    }

    /// At close-out: record that the unbound eigenvariable `idx` is named
    /// `variable`, so a γ wvar named later admits it only above its level.
    /// Two eigenvariables may share a name; the higher level counts.
    pub fn nameEigen(self: *WVars, idx: u32, variable: ExprId) Error!void {
        const level = self.vars.items[idx].level;
        const prev = self.eigens.get(variable);
        try self.log.append(self.allocator, .{ .named = .{ .variable = variable, .prev = prev } });
        try self.eigens.put(self.allocator, variable, @max(level, prev orelse 0));
    }
};

fn putWord(allocator: std.mem.Allocator, out: *std.ArrayListUnmanaged(u8), word: u32) Error!void {
    try out.appendSlice(allocator, std.mem.asBytes(&word));
}
