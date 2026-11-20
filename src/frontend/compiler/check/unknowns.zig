//! Named unknowns (`?a`) in the line walk.
//!
//! A named unknown is a hole with an identity that spans the lines of one
//! proof (`--| @unknown ?` on its sort). The walk keeps that identity: the
//! first line whose check fills a name binds it, every later occurrence is
//! written as that value before its line is checked, and a later line that
//! fills it differently is an error there.
//!
//! A line is bound only once its check is final, so a `@fallback` attempt
//! or an ACUI retry that fills a name and is then abandoned binds nothing.

const std = @import("std");
const ExprModule = @import("../../../trusted/expressions.zig");
const Expr = ExprModule.Expr;
const ExprId = @import("../../expr.zig").ExprId;
const PlaceholderId = @import("../../expr.zig").PlaceholderId;
const VarId = @import("../../expr.zig").VarId;
const TheoremContext = @import("../../expr.zig").TheoremContext;
const GlobalEnv = @import("../../env.zig").GlobalEnv;
const MM0Parser = @import("../../parse_recovery.zig").MM0Parser;
const RewriteRegistry = @import("../../rewrite_registry.zig").RewriteRegistry;
const Canonicalizer = @import("../../normalizer.zig").Canonicalizer;
const Holes = @import("../holes.zig");

pub const Unknowns = struct {
    /// Each bound name's value.
    bound: std.StringHashMapUnmanaged(ExprId) = .empty,
    /// The shape the pre-pass forced on a name it did not solve, with its
    /// open parts as placeholders. Only shown, never written into a line.
    partial: std.StringHashMapUnmanaged(ExprId) = .empty,
    /// The name each open placeholder in a `partial` value stands for.
    open: std.AutoHashMapUnmanaged(PlaceholderId, []const u8) = .empty,
    /// Theorem variables by id, to write a value back as surface syntax.
    var_surfaces: std.AutoHashMapUnmanaged(u64, *const Expr) = .empty,
    var_surfaces_seen: usize = 0,

    pub fn deinit(self: *Unknowns, allocator: std.mem.Allocator) void {
        self.bound.deinit(allocator);
        self.partial.deinit(allocator);
        self.open.deinit(allocator);
        self.var_surfaces.deinit(allocator);
        self.* = undefined;
    }

    pub const Known = struct {
        value: ExprId,
        /// False while `value` still holds placeholders.
        complete: bool,
    };

    /// What is known of `name` now: its value, or its partial shape with
    /// the open names the walk has bound since written in.
    pub fn known(self: *const Unknowns, theorem: *TheoremContext, name: []const u8) !?Known {
        if (self.bound.get(name)) |value| return .{ .value = value, .complete = true };
        const shape = self.partial.get(name) orelse return null;
        var complete = true;
        const value = try self.fillOpen(theorem, shape, &complete);
        return .{ .value = value, .complete = complete };
    }

    fn fillOpen(self: *const Unknowns, theorem: *TheoremContext, id: ExprId, complete: *bool) !ExprId {
        switch (theorem.interner.node(id).*) {
            .variable => return id,
            .placeholder => |pid| {
                if (self.open.get(pid)) |name| if (self.bound.get(name)) |value| return value;
                complete.* = false;
                return id;
            },
            .app => |app| {
                const args = try theorem.allocator.alloc(ExprId, app.args.len);
                defer theorem.allocator.free(args);
                var changed = false;
                for (app.args, args) |arg, *out| {
                    out.* = try self.fillOpen(theorem, arg, complete);
                    if (out.* != arg) changed = true;
                }
                if (!changed) return id;
                return try theorem.interner.internApp(app.term_id, args);
            },
        }
    }

    /// `surface` with every bound name written as its value: the same
    /// pointer when it names nothing bound. A value that cannot be written
    /// as surface syntax (it holds a placeholder) leaves its name a hole;
    /// `record` then checks the line's fill against it.
    pub fn substitute(
        self: *Unknowns,
        allocator: std.mem.Allocator,
        theorem: *const TheoremContext,
        parser: *const MM0Parser,
        surface: *const Expr,
    ) !*const Expr {
        if (self.bound.count() == 0 or !hasNamed(surface)) return surface;
        try self.refreshVarSurfaces(allocator, theorem);
        return try self.substituteExpr(allocator, theorem, parser, surface);
    }

    fn substituteExpr(
        self: *Unknowns,
        allocator: std.mem.Allocator,
        theorem: *const TheoremContext,
        parser: *const MM0Parser,
        expr: *const Expr,
    ) !*const Expr {
        switch (expr.*) {
            .variable => return expr,
            .hole => |hole| {
                const name = hole.name orelse return expr;
                const value = self.bound.get(name) orelse return expr;
                return (try self.surfaceOf(allocator, theorem, parser, value)) orelse expr;
            },
            .term => |term| {
                const args = try allocator.alloc(*const Expr, term.args.len);
                var changed = false;
                var deps: u55 = 0;
                for (term.args, args) |arg, *out| {
                    out.* = try self.substituteExpr(allocator, theorem, parser, arg);
                    if (out.* != arg) changed = true;
                    deps |= out.*.deps();
                }
                if (!changed) {
                    allocator.free(args);
                    return expr;
                }
                const node = try allocator.create(Expr);
                node.* = .{ .term = .{
                    .sort = term.sort,
                    .deps = deps,
                    .id = term.id,
                    .args = args,
                } };
                return node;
            },
        }
    }

    /// `id` as surface syntax, or null when it holds a placeholder. Nodes
    /// are not freed: `allocator` is the walk's arena.
    fn surfaceOf(
        self: *Unknowns,
        allocator: std.mem.Allocator,
        theorem: *const TheoremContext,
        parser: *const MM0Parser,
        id: ExprId,
    ) !?*const Expr {
        switch (theorem.interner.node(id).*) {
            .variable => |var_id| return self.var_surfaces.get(var_id.hashKey()),
            .placeholder => return null,
            .app => |app| {
                const term = parser.core.terms.items[app.term_id];
                const args = try allocator.alloc(*const Expr, app.args.len);
                var deps: u55 = 0;
                for (app.args, args) |arg, *out| {
                    out.* = (try self.surfaceOf(allocator, theorem, parser, arg)) orelse {
                        allocator.free(args);
                        return null;
                    };
                    deps |= out.*.deps();
                }
                const node = try allocator.create(Expr);
                node.* = .{ .term = .{
                    .sort = term.ret_sort,
                    .deps = deps,
                    .id = app.term_id,
                    .args = args,
                } };
                return node;
            },
        }
    }

    fn refreshVarSurfaces(
        self: *Unknowns,
        allocator: std.mem.Allocator,
        theorem: *const TheoremContext,
    ) !void {
        if (theorem.parser_vars.count() == self.var_surfaces_seen) return;
        self.var_surfaces.clearRetainingCapacity();
        var it = theorem.parser_vars.iterator();
        while (it.next()) |entry| {
            try self.var_surfaces.put(allocator, entry.value_ptr.hashKey(), entry.key_ptr.*);
        }
        self.var_surfaces_seen = theorem.parser_vars.count();
    }

    /// Bind the names `surface` holds from `checked`, the statement its
    /// line checked as. Null when every fill agrees with every earlier one;
    /// otherwise the first name filled differently, and nothing is bound.
    /// A fill the walk cannot read back (the line checked through a
    /// rewrite that changed its shape) binds nothing: the line stands.
    pub fn record(
        self: *Unknowns,
        allocator: std.mem.Allocator,
        parser: *MM0Parser,
        theorem: *TheoremContext,
        env: *const GlobalEnv,
        registry: *RewriteRegistry,
        surface: *const Expr,
        checked: ExprId,
    ) !?[]const u8 {
        if (!hasNamed(surface)) return null;
        var canonicalizer = Canonicalizer.init(allocator, theorem, registry, env, {});
        defer canonicalizer.deinit();
        const fill = (try Holes.fillThroughDefs(parser, theorem, env, surface, checked)) orelse
            (if (registry.hasStructuralCombiners())
                try Holes.materializeSurfaceModuloAcui(
                    parser,
                    theorem,
                    env,
                    registry,
                    &canonicalizer,
                    surface,
                    checked,
                )
            else
                null) orelse return null;

        var fills: std.StringArrayHashMapUnmanaged(ExprId) = .empty;
        defer fills.deinit(allocator);
        const clash = readFills(allocator, theorem, &canonicalizer, surface, fill, &fills) catch |err| switch (err) {
            error.NamedUnknownUnread => return null,
            else => return err,
        };
        if (clash) |name| return name;
        for (fills.keys(), fills.values()) |name, value| {
            const bound = self.bound.get(name) orelse continue;
            if (!try sameValue(&canonicalizer, bound, value)) return name;
        }
        for (fills.keys(), fills.values()) |name, value| {
            const entry = try self.bound.getOrPut(allocator, name);
            if (!entry.found_existing) entry.value_ptr.* = value;
        }
        return null;
    }
};

/// Walk `surface` and its `fill` (which has the surface's shape) together,
/// recording each name's value. Returns the first name filled twice
/// differently on this line.
fn readFills(
    allocator: std.mem.Allocator,
    theorem: *TheoremContext,
    canonicalizer: *Canonicalizer,
    surface: *const Expr,
    fill: ExprId,
    out: *std.StringArrayHashMapUnmanaged(ExprId),
) !?[]const u8 {
    switch (surface.*) {
        .variable => return null,
        .hole => |hole| {
            const name = hole.name orelse return null;
            const entry = try out.getOrPut(allocator, name);
            if (!entry.found_existing) {
                entry.value_ptr.* = fill;
                return null;
            }
            return if (try sameValue(canonicalizer, entry.value_ptr.*, fill)) null else name;
        },
        .term => |term| {
            if (!hasNamed(surface)) return null;
            const app = switch (theorem.interner.node(fill).*) {
                .app => |app| app,
                else => return error.NamedUnknownUnread,
            };
            if (app.term_id != term.id or app.args.len != term.args.len) {
                return error.NamedUnknownUnread;
            }
            for (term.args, app.args) |arg, value| {
                if (try readFills(allocator, theorem, canonicalizer, arg, value, out)) |name| {
                    return name;
                }
            }
            return null;
        },
    }
}

fn sameValue(canonicalizer: *Canonicalizer, lhs: ExprId, rhs: ExprId) !bool {
    if (lhs == rhs) return true;
    return (try canonicalizer.canonicalize(lhs)) == (try canonicalizer.canonicalize(rhs));
}

/// Whether `expr` holds a named unknown.
pub fn hasNamed(expr: *const Expr) bool {
    return switch (expr.*) {
        .variable => false,
        .hole => |hole| hole.name != null,
        .term => |term| for (term.args) |arg| {
            if (hasNamed(arg)) break true;
        } else false,
    };
}
