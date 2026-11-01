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
//! proof needs one: a fact may state the goal for one particular
//! variable, and MM0 has no alpha-equivalence to rename it. It may become
//! a variable its introduction goal does not mention, and nothing else;
//! leftovers are named at close-out. Its level is the number of
//! eigenvariables introduced before it; a γ wvar's level is the number
//! introduced before it was minted. A γ wvar may hold an eigenvariable, or
//! the variable one became, only of a lower level (W6), which keeps every
//! eigenvariable out of the instances that existed before it. A
//! definition's dummy is an eigenvariable introduced at the unfolding that
//! holds it (`Terms.unfold`). Two eigenvariables unify as one fresh
//! variable: the younger is bound to the older, and close-out names the
//! older clear of what either must not occur in.
//!
//! A bound name is an eigenvariable for a bound binder a narrowing leaves
//! unbound (`Terms` `Matcher.invent`): the step may pick any variable its
//! dependency condition allows, so the name is kept out of only what its
//! steps bar it from. Narrowing puts it into an older wvar, so W6, which
//! keeps an eigenvariable out of what existed before it, does not apply;
//! instead the name's level is the lowest of the wvars holding it, and it
//! merges with an eigenvariable only below that level.
//!
//! A wvar also carries the variables bound inside the formula it was swapped
//! into: holding one of those, or a theorem variable that depends on one,
//! would capture it.
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
    /// For an eigenvariable a rule introduces, the rule's arguments that
    /// do not depend on it, which it may not occur in; null when it may
    /// occur nowhere in its introduction goal. A later step whose bound
    /// binder it is adds its own such arguments (`bar`).
    fresh_in: ?[]const ExprId = null,
    /// A bound name (see the module doc). Its introduction goal is its own
    /// leaf, and `fresh_in` starts empty.
    name: bool = false,
    cut: bool = false,
    value: ?ExprId = null,
};

const Entry = union(enum) {
    bound: u32,
    /// A wvar inside a binding took the bound wvar's constraints.
    narrowed: struct { wvar: u32, level: u32, capture: []const ExprId },
    /// `variable` became an eigenvariable; `prev` is the level it had.
    named: struct { variable: ExprId, prev: ?u32 },
    /// An eigenvariable was barred from more expressions; `prev` is the
    /// list it had.
    barred: struct { wvar: u32, prev: ?[]const ExprId },
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
                .barred => |old| self.vars.items[old.wvar].fresh_in = old.prev,
            }
        }
    }

    /// Whether a wvar with index below `older_than` was bound or narrowed
    /// since the log mark `since`. Barring one (`bar`) does not count: a
    /// bar only refuses what would break the barring step's dependency
    /// condition.
    pub fn constrainedOlderSince(self: *const WVars, since: usize, older_than: u32) bool {
        for (self.log.items[since..]) |entry| switch (entry) {
            .bound => |idx| if (idx < older_than) return true,
            .narrowed => |old| if (old.wvar < older_than) return true,
            .barred, .named => {},
        };
        return false;
    }

    /// Append to `out` what the steps logged since `since` did to the wvars
    /// with index below `older_than`: each binding (with the younger wvars
    /// it holds numbered by first occurrence), narrowing, and naming of an
    /// eigenvariable, with levels above `level_cap` read as `level_cap`, and
    /// then the eigenvariables barred, in index order, each with the leaves
    /// of what it was barred from since `since`.
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
        // Each eigenvariable barred, with the length its list had at `since`.
        var barred = std.AutoArrayHashMapUnmanaged(u32, usize).empty;
        defer barred.deinit(allocator);
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
            .barred => |old| if (old.wvar < older_than) {
                const gop = try barred.getOrPut(allocator, old.wvar);
                // Unbarred, the list was the introduction goal alone.
                if (!gop.found_existing) gop.value_ptr.* = if (old.prev) |prev| prev.len else 1;
            },
        };
        const Asc = struct {
            keys: []const u32,
            pub fn lessThan(ctx: @This(), a: usize, b: usize) bool {
                return ctx.keys[a] < ctx.keys[b];
            }
        };
        barred.sort(Asc{ .keys = barred.keys() });
        // A bar keeps the eigenvariable out of what its expressions' leaves
        // become, so the leaves of what it was barred from since `since`
        // are all that matters, whatever order or repeats the bars came in.
        var leaves = std.ArrayListUnmanaged(ExprId).empty;
        defer leaves.deinit(allocator);
        for (barred.keys(), barred.values()) |idx, start| {
            leaves.clearRetainingCapacity();
            for (self.vars.items[idx].fresh_in.?[start..]) |expr| try self.collectLeaves(allocator, expr, &leaves);
            std.mem.sort(ExprId, leaves.items, {}, std.sort.asc(ExprId));
            try putWord(allocator, out, 'f');
            try putWord(allocator, out, idx);
            for (leaves.items) |leaf| try self.serialize(allocator, leaf, older_than, level_cap, &young, out);
            try putWord(allocator, out, std.math.maxInt(u32));
        }
    }

    /// The variables and unbound wvars of `expr`, after following
    /// bindings, added to `out` once each.
    fn collectLeaves(self: *WVars, allocator: std.mem.Allocator, expr: ExprId, out: *std.ArrayListUnmanaged(ExprId)) Error!void {
        const at = self.resolve(expr);
        switch (self.theorem.interner.node(at).*) {
            .variable, .placeholder => if (std.mem.indexOfScalar(ExprId, out.items, at) == null) try out.append(allocator, at),
            .app => |app| for (app.args) |arg| try self.collectLeaves(allocator, arg, out),
        }
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
                try putWord(allocator, out, if (wvar.name) 'm' else if (wvar.introduced_at != null) 'e' else if (wvar.cut) 'c' else 'y');
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

    /// A new eigenvariable introduced at `goal`, kept out of the whole goal,
    /// or only out of `fresh_in` when that is given.
    pub fn introduce(self: *WVars, sort_name: []const u8, goal: ExprId, fresh_in: ?[]const ExprId) Error!ExprId {
        const expr = try self.add(.{
            .expr = undefined,
            .sort_name = sort_name,
            .level = self.eigen_count,
            .capture = &.{},
            .introduced_at = goal,
            .fresh_in = fresh_in,
        });
        self.eigen_count += 1;
        return expr;
    }

    /// A new bound name (`WVar.name`), which no wvar holds yet.
    pub fn introduceName(self: *WVars, sort_name: []const u8) Error!ExprId {
        const expr = try self.add(.{
            .expr = undefined,
            .sort_name = sort_name,
            .level = std.math.maxInt(u32),
            .capture = &.{},
            .introduced_at = undefined,
            .fresh_in = &.{},
            .name = true,
        });
        self.vars.items[self.count() - 1].introduced_at = expr;
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
    /// included), following bindings, or a theorem variable `expr` holds
    /// depends on it: substituting `expr` for a binder that does not
    /// depend on `variable` breaks MM0's dependency condition either way.
    pub fn mentions(self: *WVars, expr: ExprId, variable: ExprId) bool {
        const at = self.resolve(expr);
        if (at == variable) return true;
        return switch (self.theorem.interner.node(at).*) {
            .variable => self.dependsOn(at, variable),
            .placeholder => false,
            .app => |app| for (app.args) |arg| {
                if (self.mentions(arg, variable)) break true;
            } else false,
        };
    }

    /// Whether the variable leaf `leaf` is declared to depend on the bound
    /// variable `variable` (`p : wff x` on `x`).
    pub fn dependsOn(self: *const WVars, leaf: ExprId, variable: ExprId) bool {
        if (self.theorem.interner.node(variable).* != .variable) return false;
        const info = (self.theorem.currentLeafInfo(leaf) catch null) orelse return false;
        if (info.bound or info.deps == 0) return false;
        const bound = (self.theorem.currentLeafInfo(variable) catch null) orelse return false;
        return bound.bound and info.deps & bound.deps != 0;
    }

    /// The bound variables `expr` holds, after following bindings, once
    /// each.
    pub fn collectBound(
        self: *WVars,
        allocator: std.mem.Allocator,
        expr: ExprId,
        out: *std.ArrayListUnmanaged(ExprId),
    ) Error!void {
        const at = self.resolve(expr);
        switch (self.theorem.interner.node(at).*) {
            .variable => if (self.isBound(at) and std.mem.indexOfScalar(ExprId, out.items, at) == null) {
                try out.append(allocator, at);
            },
            .placeholder => {},
            .app => |app| for (app.args) |arg| try self.collectBound(allocator, arg, out),
        }
    }

    /// Add `variables` to what the unbound wvar `idx` may not hold.
    pub fn narrowCapture(self: *WVars, idx: u32, variables: []const ExprId) Error!void {
        if (variables.len == 0) return;
        const wvar = &self.vars.items[idx];
        const capture = try std.mem.concat(self.arena, ExprId, &.{ wvar.capture, variables });
        try self.log.append(self.allocator, .{ .narrowed = .{
            .wvar = idx,
            .level = wvar.level,
            .capture = wvar.capture,
        } });
        wvar.capture = capture;
    }

    /// Whether `variable` is a bound variable, the only kind an
    /// eigenvariable may become.
    pub fn isBound(self: *const WVars, variable: ExprId) bool {
        const info = (self.theorem.currentLeafInfo(variable) catch null) orelse return false;
        return info.bound;
    }

    /// Whether wvar `idx` may hold, or as an eigenvariable become, the
    /// variable `variable`. An eigenvariable becomes only a bound variable.
    /// A variable that depends on one the wvar may not hold is refused
    /// with it.
    pub fn admits(self: *WVars, idx: u32, variable: ExprId) bool {
        const wvar = self.vars.items[idx];
        for (wvar.capture) |captured| {
            if (self.mentions(variable, captured)) return false;
        }
        if (wvar.introduced_at) |goal| {
            if (!self.isBound(variable) or self.eigens.contains(variable)) return false;
            for (wvar.fresh_in orelse &.{goal}) |expr| {
                if (self.mentions(expr, variable)) return false;
            }
            return true;
        }
        if (self.eigens.get(variable)) |level| return level < wvar.level;
        var it = self.eigens.iterator();
        while (it.next()) |entry| {
            if (entry.value_ptr.* >= wvar.level and self.dependsOn(variable, entry.key_ptr.*)) return false;
        }
        return true;
    }

    /// Bind unbound wvar `idx` to `value`, unless that breaks its sort,
    /// occurs, capture or level constraint. Wvars inside `value` take on
    /// `idx`'s constraints, so binding them later cannot break them either.
    /// An eigenvariable binds only to a variable it admits or another
    /// eigenvariable (`merge`); facing a γ wvar it binds that one instead.
    /// Returns false, logging nothing, when the binding is refused.
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
                if (self.vars.items[other].introduced_at != null) return self.merge(idx, other);
                return self.bind(other, self.vars.items[idx].expr);
            },
            .app => return false,
        }
        if (!self.admits(idx, value)) return false;
        // A bound name's variable stays open to every wvar.
        if (self.vars.items[idx].name) {
            try self.log.append(self.allocator, .{ .bound = idx });
            self.vars.items[idx].value = value;
            return true;
        }
        try self.eigens.ensureUnusedCapacity(self.allocator, 1);
        try self.log.ensureUnusedCapacity(self.allocator, 2);
        self.log.appendAssumeCapacity(.{ .named = .{ .variable = value, .prev = null } });
        self.eigens.putAssumeCapacity(value, self.vars.items[idx].level);
        self.log.appendAssumeCapacity(.{ .bound = idx });
        self.vars.items[idx].value = value;
        return true;
    }

    /// Unify the unbound eigenvariables `idx` and `other` as one fresh
    /// variable: the younger is bound to the older, which then stands for
    /// both, so a goal that existed before the younger one constrains
    /// nothing older, and takes on what the younger must stay out of. A
    /// bound name is bound to an eigenvariable instead, which every wvar
    /// holding the name must be younger than. Refused when one occurs
    /// where the other may not.
    fn merge(self: *WVars, idx: u32, other: u32) Error!bool {
        if (idx == other) return false;
        const is_name = self.vars.items[idx].name;
        const gone_idx, const kept_idx = if (is_name != self.vars.items[other].name)
            (if (is_name) .{ idx, other } else .{ other, idx })
        else if (idx > other) .{ idx, other } else .{ other, idx };
        const gone = self.vars.items[gone_idx];
        const kept = self.vars.items[kept_idx];
        if (gone.name and !kept.name and gone.level <= kept.level) return false;
        for ([2][2]u32{ .{ gone_idx, kept_idx }, .{ kept_idx, gone_idx } }) |pair| {
            const wvar = self.vars.items[pair[0]];
            for (wvar.fresh_in orelse &.{wvar.introduced_at.?}) |expr| {
                if (self.mentions(expr, self.vars.items[pair[1]].expr)) return false;
            }
        }
        try self.extendFreshIn(kept_idx, gone.fresh_in orelse &.{gone.introduced_at.?});
        // The kept name is held by what held the other too.
        if (kept.name and gone.level < kept.level) {
            try self.log.append(self.allocator, .{ .narrowed = .{ .wvar = kept_idx, .level = kept.level, .capture = kept.capture } });
            self.vars.items[kept_idx].level = gone.level;
        }
        try self.log.append(self.allocator, .{ .bound = gone_idx });
        self.vars.items[gone_idx].value = kept.expr;
        return true;
    }

    /// Bar the unbound eigenvariable `idx` from `exprs` too: a step fixed a
    /// bound binder to it, and these are the step's arguments that do not
    /// depend on the binder. False, logging nothing, when one holds it.
    pub fn bar(self: *WVars, idx: u32, exprs: []const ExprId) Error!bool {
        const wvar = self.vars.items[idx];
        std.debug.assert(wvar.introduced_at != null and wvar.value == null);
        for (exprs) |expr| {
            if (self.mentions(expr, wvar.expr)) return false;
        }
        try self.extendFreshIn(idx, exprs);
        return true;
    }

    fn extendFreshIn(self: *WVars, idx: u32, exprs: []const ExprId) Error!void {
        if (exprs.len == 0) return;
        const wvar = &self.vars.items[idx];
        const own = wvar.fresh_in orelse &.{wvar.introduced_at.?};
        const list = try std.mem.concat(self.arena, ExprId, &.{ own, exprs });
        try self.log.append(self.allocator, .{ .barred = .{ .wvar = idx, .prev = wvar.fresh_in } });
        wvar.fresh_in = list;
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
                // A bound name inside is narrowed like a γ wvar.
                if (target.introduced_at != null and !target.name) {
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
