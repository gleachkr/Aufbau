//! Witness variables and eigenvariables for the search core
//! (`docs/design_notes/shared_witness.md` D1, D3).
//!
//! A witness variable (wvar) is a `.meta` placeholder leaf minted in the
//! run's theorem for a binder a rule's conclusion does not fix (γ). Its
//! assignment lives here, never in the interner, and every binding goes on
//! one log that the search undoes as it backtracks.
//!
//! An eigenvariable (δ) is a `@vars` pool variable fresh for the goal it is
//! introduced at. Its level is the number of eigenvariables introduced
//! before it; a wvar's level is the number introduced before it was minted.
//! A wvar may hold an eigenvariable only of a lower level (W6), which keeps
//! every eigenvariable out of the instances that existed before it. A
//! variable may be introduced again once the goal no longer mentions it;
//! its new, higher level then counts.
//!
//! A wvar also carries the variables bound inside the formula it was swapped
//! into: holding one of those would capture it.

const std = @import("std");
const ExprModule = @import("../../../expr.zig");
const ExprId = ExprModule.ExprId;
const PlaceholderId = ExprModule.PlaceholderId;
const TheoremContext = ExprModule.TheoremContext;
const Context = @import("../types.zig").Context;

pub const Error = error{ OutOfMemory, TooManyTheoremExprs };

pub const WVar = struct {
    sort_name: []const u8,
    level: u32,
    /// Variables it may not hold.
    capture: []const ExprId,
    value: ?ExprId = null,
};

const Entry = union(enum) {
    bound: u32,
    /// A wvar inside a binding took the bound wvar's constraints.
    narrowed: struct { wvar: u32, level: u32, capture: []const ExprId },
    /// `variable` was introduced as an eigenvariable; `prev` is the level of
    /// its previous introduction.
    introduced: struct { variable: ExprId, prev: ?u32 },
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
    /// Bindings and introductions ever made, undone ones included.
    steps: usize = 0,
    eigen_count: u32 = 0,
    /// Each live eigenvariable's level.
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
                .introduced => |old| if (old.prev) |level| {
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
            .introduced => {},
        };
        return false;
    }

    pub fn mint(self: *WVars, sort_name: []const u8, capture: []const ExprId) Error!ExprId {
        const expr = self.theorem.addMetaPlaceholderResolved(sort_name) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            else => return error.TooManyTheoremExprs,
        };
        const pid = self.theorem.interner.node(expr).placeholder;
        try self.by_placeholder.put(self.allocator, pid, self.count());
        try self.vars.append(self.allocator, .{
            .sort_name = sort_name,
            .level = self.eigen_count,
            .capture = capture,
        });
        return expr;
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

    /// Whether wvar `idx` may hold the variable `variable`.
    pub fn admits(self: *const WVars, idx: u32, variable: ExprId) bool {
        const wvar = self.vars.items[idx];
        if (std.mem.indexOfScalar(ExprId, wvar.capture, variable) != null) return false;
        const level = self.eigens.get(variable) orelse return true;
        return level < wvar.level;
    }

    /// Bind unbound wvar `idx` to `value`, unless that breaks its sort,
    /// occurs, capture or level constraint. Wvars inside `value` take on
    /// `idx`'s constraints, so binding them later cannot break them either.
    /// Returns false, logging nothing, when the binding is refused.
    pub fn bind(self: *WVars, idx: u32, value: ExprId) Error!bool {
        std.debug.assert(self.vars.items[idx].value == null);
        const wvar = self.vars.items[idx];
        if (!std.mem.eql(u8, self.sortOf(value) orelse return false, wvar.sort_name)) return false;
        const start = self.mark();
        errdefer self.rollback(start);
        if (!try self.constrain(idx, value)) {
            self.rollback(start);
            return false;
        }
        try self.log.append(self.allocator, .{ .bound = idx });
        self.vars.items[idx].value = value;
        self.steps += 1;
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

    fn sortOf(self: *const WVars, expr: ExprId) ?[]const u8 {
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

    /// Record `variable` as an eigenvariable introduced now.
    pub fn introduce(self: *WVars, variable: ExprId) Error!void {
        try self.eigens.ensureUnusedCapacity(self.allocator, 1);
        try self.log.append(self.allocator, .{ .introduced = .{
            .variable = variable,
            .prev = self.eigens.get(variable),
        } });
        self.eigens.putAssumeCapacity(variable, self.eigen_count);
        self.eigen_count += 1;
        self.steps += 1;
    }

    /// Whether `variable` has a live introduction as an eigenvariable.
    pub fn introduced(self: *const WVars, variable: ExprId) bool {
        return self.eigens.contains(variable);
    }
};
