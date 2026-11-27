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
const SurfaceExpr = @import("../../surface_expr.zig");

pub const Unknowns = struct {
    /// Each bound name's value.
    bound: std.StringHashMapUnmanaged(ExprId) = .empty,
    /// The shape the pre-pass forced on a name it did not solve, with its
    /// open parts as placeholders. `substitute` writes it into a line with
    /// those parts as holes.
    partial: std.StringHashMapUnmanaged(ExprId) = .empty,
    /// The statements the pre-pass read, by the address of their text:
    /// the walk takes them from here instead of reading them again.
    statements: std.AutoHashMapUnmanaged(usize, Holes.ParsedAssertion) = .empty,
    /// The name each open placeholder in a `partial` value stands for.
    open: std.AutoHashMapUnmanaged(PlaceholderId, []const u8) = .empty,
    /// Theorem variables by id, to write a value back as surface syntax.
    var_surfaces: std.AutoHashMapUnmanaged(u64, *const Expr) = .empty,
    var_surfaces_seen: usize = 0,
    /// Set when the pre-pass found that the lines give the names values
    /// that disagree; it then solved none of them.
    clash: ?Clash = null,

    pub const Clash = struct {
        /// The line on which the pre-pass found the clash, solving the
        /// lines in order.
        line: []const u8,
        /// The two terms that cannot be equal, when the clash is between
        /// two terms; their open parts are placeholders.
        terms: ?[2]ExprId,
    };

    pub fn deinit(self: *Unknowns, allocator: std.mem.Allocator) void {
        self.bound.deinit(allocator);
        self.partial.deinit(allocator);
        self.statements.deinit(allocator);
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

    /// `surface` with what is known of each name written in: a solved name
    /// as its value, a partly solved one as its shape. Every other hole is
    /// a fresh placeholder, one per name; `names` maps each placeholder
    /// that stands for a name (these, and the open parts of the shapes) to
    /// it. Null when nothing is known of any name in `surface`, or a hole's
    /// sort is unknown.
    pub fn writeKnown(
        self: *const Unknowns,
        allocator: std.mem.Allocator,
        theorem: *TheoremContext,
        env: *const GlobalEnv,
        surface: *const Expr,
        names: *std.AutoHashMapUnmanaged(PlaceholderId, []const u8),
    ) !?ExprId {
        var minted: std.StringHashMapUnmanaged(ExprId) = .empty;
        defer minted.deinit(allocator);
        var any_known = false;
        const goal = (try self.writeKnownExpr(
            allocator,
            theorem,
            env,
            surface,
            names,
            &minted,
            &any_known,
        )) orelse return null;
        if (!any_known) return null;
        var it = self.open.iterator();
        while (it.next()) |entry| {
            const slot = try names.getOrPut(allocator, entry.key_ptr.*);
            if (!slot.found_existing) slot.value_ptr.* = entry.value_ptr.*;
        }
        return goal;
    }

    fn writeKnownExpr(
        self: *const Unknowns,
        allocator: std.mem.Allocator,
        theorem: *TheoremContext,
        env: *const GlobalEnv,
        expr: *const Expr,
        names: *std.AutoHashMapUnmanaged(PlaceholderId, []const u8),
        minted: *std.StringHashMapUnmanaged(ExprId),
        any_known: *bool,
    ) !?ExprId {
        if (!SurfaceExpr.containsHole(expr)) return try theorem.internParsedExpr(expr);
        switch (expr.*) {
            .variable => unreachable,
            .hole => |hole| {
                if (hole.name) |name| {
                    if (try self.known(theorem, name)) |known_value| {
                        any_known.* = true;
                        return known_value.value;
                    }
                    if (minted.get(name)) |id| return id;
                }
                const sort_name = SurfaceExpr.sortNameById(env, hole.sort) orelse return null;
                const id = try theorem.addLineHolePlaceholder(sort_name);
                if (hole.name) |name| {
                    try minted.put(allocator, name, id);
                    try names.put(allocator, theorem.interner.node(id).placeholder, name);
                }
                return id;
            },
            .term => |term| {
                const args = try allocator.alloc(ExprId, term.args.len);
                defer allocator.free(args);
                for (term.args, args) |arg, *out| {
                    out.* = (try self.writeKnownExpr(
                        allocator,
                        theorem,
                        env,
                        arg,
                        names,
                        minted,
                        any_known,
                    )) orelse return null;
                }
                return try theorem.interner.internApp(term.id, args);
            },
        }
    }

    /// `surface` with what is known of each name written in: a bound name
    /// as its value, and a name the pre-pass forced a shape on as that
    /// shape, its open parts holes (named where they stand for a name).
    /// The same pointer when nothing is known of any name in `surface`. A
    /// bound value that cannot be written as surface syntax (it holds a
    /// placeholder) leaves its name a hole; `record` then checks the
    /// line's fill against it. A line with a shape written in no longer
    /// shows its name: `record` reads the names off the line as written
    /// by the user (`writesShape`).
    pub fn substitute(
        self: *Unknowns,
        allocator: std.mem.Allocator,
        theorem: *TheoremContext,
        parser: *const MM0Parser,
        surface: *const Expr,
    ) !*const Expr {
        if (self.bound.count() == 0 and self.partial.count() == 0) return surface;
        if (!hasNamed(surface)) return surface;
        try self.refreshVarSurfaces(allocator, theorem);
        return try self.substituteExpr(allocator, theorem, parser, surface);
    }

    /// `surface` interned with each named hole written as its value: the
    /// line it states once every name in it is bound. Null when a hole is
    /// left: an anonymous one, a name with no value, or one whose value
    /// holds a placeholder. The values go in as they are interned, so a
    /// value shared between lines is never spelled out.
    pub fn internBound(
        self: *const Unknowns,
        theorem: *TheoremContext,
        surface: *const Expr,
    ) !?ExprId {
        if (self.bound.count() == 0) return null;
        switch (surface.*) {
            .variable => return try theorem.internParsedExpr(surface),
            .hole => |hole| {
                const value = self.bound.get(hole.name orelse return null) orelse return null;
                return if (theorem.containsPlaceholder(value)) null else value;
            },
            .term => |term| {
                const args = try theorem.allocator.alloc(ExprId, term.args.len);
                defer theorem.allocator.free(args);
                for (term.args, args) |arg, *out| {
                    out.* = (try self.internBound(theorem, arg)) orelse return null;
                }
                return try theorem.interner.internApp(term.id, args);
            },
        }
    }

    /// Whether `substitute` writes a shape into `surface`: a name in it is
    /// not bound but has a shape from the pre-pass.
    pub fn writesShape(self: *const Unknowns, surface: *const Expr) bool {
        if (self.partial.count() == 0) return false;
        return switch (surface.*) {
            .variable => false,
            .hole => |hole| if (hole.name) |name|
                !self.bound.contains(name) and self.partial.contains(name)
            else
                false,
            .term => |term| for (term.args) |arg| {
                if (self.writesShape(arg)) break true;
            } else false,
        };
    }

    fn substituteExpr(
        self: *Unknowns,
        allocator: std.mem.Allocator,
        theorem: *TheoremContext,
        parser: *const MM0Parser,
        expr: *const Expr,
    ) !*const Expr {
        switch (expr.*) {
            .variable => return expr,
            .hole => |hole| {
                const name = hole.name orelse return expr;
                if (self.bound.get(name)) |value| {
                    return (try self.surfaceOf(allocator, theorem, parser, value, false)) orelse expr;
                }
                if (!self.partial.contains(name)) return expr;
                const shape = (try self.known(theorem, name)).?;
                return (try self.surfaceOf(allocator, theorem, parser, shape.value, true)) orelse expr;
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

    /// `id` as surface syntax. A placeholder is a hole when `holes` (named
    /// for the open name it stands for, else anonymous), and otherwise
    /// makes the whole null. Nodes are not freed: `allocator` is the walk's
    /// arena.
    fn surfaceOf(
        self: *Unknowns,
        allocator: std.mem.Allocator,
        theorem: *const TheoremContext,
        parser: *const MM0Parser,
        id: ExprId,
        holes: bool,
    ) !?*const Expr {
        switch (theorem.interner.node(id).*) {
            .variable => |var_id| return self.var_surfaces.get(var_id.hashKey()),
            .placeholder => |pid| {
                if (!holes) return null;
                const info = theorem.placeholderInfo(pid) orelse return null;
                const sort = parser.core.sort_names.get(info.sort_name) orelse return null;
                const name = self.open.get(pid);
                const node = try allocator.create(Expr);
                node.* = .{ .hole = .{
                    .sort = @intCast(sort),
                    .name = name,
                    .token = name orelse parser.core.sort_hole_tokens.get(info.sort_name) orelse "_",
                } };
                return node;
            },
            .app => |app| {
                const term = parser.core.terms.items[app.term_id];
                const args = try allocator.alloc(*const Expr, app.args.len);
                var deps: u55 = 0;
                for (app.args, args) |arg, *out| {
                    out.* = (try self.surfaceOf(allocator, theorem, parser, arg, holes)) orelse {
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
        return switch (try self.readLine(allocator, parser, theorem, env, registry, &canonicalizer, surface, checked)) {
            .no_fill, .fits => null,
            .clash => |name| name,
        };
    }

    pub const BindingFit = union(enum) {
        fits,
        /// The binder's value does not have the written shape.
        mismatch,
        /// The value fills this name differently from an earlier fill.
        conflict: []const u8,
    };

    /// An explicit binding written with holes, `surface`, against `value`,
    /// the binder's value once its line checked: whether it fits, and if so
    /// the names it fills bound, as `record` binds a statement's.
    pub fn recordBinding(
        self: *Unknowns,
        allocator: std.mem.Allocator,
        parser: *MM0Parser,
        theorem: *TheoremContext,
        env: *const GlobalEnv,
        registry: *RewriteRegistry,
        surface: *const Expr,
        value: ExprId,
    ) !BindingFit {
        var canonicalizer = Canonicalizer.init(allocator, theorem, registry, env, {});
        defer canonicalizer.deinit();
        return switch (try self.readLine(allocator, parser, theorem, env, registry, &canonicalizer, surface, value)) {
            .no_fill => .mismatch,
            .fits => .fits,
            .clash => |name| .{ .conflict = name },
        };
    }

    const LineReading = union(enum) {
        /// `surface` does not fit the checked expression.
        no_fill,
        /// The names are bound: the fill agrees with every earlier one.
        /// Also when the fill cannot be read back, which binds nothing.
        fits,
        /// The first name filled differently; nothing is bound.
        clash: []const u8,
    };

    /// Bind the names `surface` holds from `checked`. The positional fill
    /// comes first. When it fills a name two ways, or there is none, the
    /// fill modulo ACUI that keeps each name to one value may still fit;
    /// failing that, the fill modulo ACUI with every hole on its own says
    /// which name clashes. `error.NamedUnknownPairingLimit` when the search
    /// for a fill that keeps names alike gave up.
    fn readLine(
        self: *Unknowns,
        allocator: std.mem.Allocator,
        parser: *MM0Parser,
        theorem: *TheoremContext,
        env: *const GlobalEnv,
        registry: *RewriteRegistry,
        canonicalizer: *Canonicalizer,
        surface: *const Expr,
        checked: ExprId,
    ) !LineReading {
        var fills: std.StringArrayHashMapUnmanaged(ExprId) = .empty;
        defer fills.deinit(allocator);
        var reading: LineReading = .no_fill;
        if (try Holes.fillThroughDefs(parser, theorem, env, surface, checked)) |fill| {
            reading = try self.readFill(allocator, theorem, canonicalizer, surface, fill, &fills);
            // An empty reading of a line with names is a fill not read back.
            if (reading == .fits and fills.count() != 0) return try self.bindAll(allocator, &fills);
        }
        if (!registry.hasStructuralCombiners()) return try self.settle(allocator, reading, &fills);
        if (hasNamed(surface)) {
            var names: Holes.NameFills = .{ .bound = &self.bound };
            defer names.deinit(allocator);
            if (try fillModuloAcui(parser, theorem, env, registry, canonicalizer, surface, checked, &names)) |fill| {
                var alike: std.StringArrayHashMapUnmanaged(ExprId) = .empty;
                defer alike.deinit(allocator);
                if (try self.readFill(allocator, theorem, canonicalizer, surface, fill, &alike) == .fits and
                    alike.count() != 0)
                {
                    return try self.bindAll(allocator, &alike);
                }
            }
            if (names.limit_hit) return error.NamedUnknownPairingLimit;
        }
        if (reading == .no_fill) {
            if (try fillModuloAcui(parser, theorem, env, registry, canonicalizer, surface, checked, null)) |fill| {
                reading = try self.readFill(allocator, theorem, canonicalizer, surface, fill, &fills);
            }
        }
        return try self.settle(allocator, reading, &fills);
    }

    /// `reading` of the fill `fills` was read from, its names bound when
    /// it fits.
    fn settle(
        self: *Unknowns,
        allocator: std.mem.Allocator,
        reading: LineReading,
        fills: *const std.StringArrayHashMapUnmanaged(ExprId),
    ) !LineReading {
        if (reading != .fits) return reading;
        return try self.bindAll(allocator, fills);
    }

    fn bindAll(
        self: *Unknowns,
        allocator: std.mem.Allocator,
        fills: *const std.StringArrayHashMapUnmanaged(ExprId),
    ) !LineReading {
        for (fills.keys(), fills.values()) |name, value| {
            const entry = try self.bound.getOrPut(allocator, name);
            if (!entry.found_existing) entry.value_ptr.* = value;
        }
        return .fits;
    }

    /// Read the names `surface` holds off `fill`, which has its shape, into
    /// `fills`, and check them against each other and the bound names.
    /// `.fits` with `fills` empty when `fill` cannot be read back.
    fn readFill(
        self: *const Unknowns,
        allocator: std.mem.Allocator,
        theorem: *TheoremContext,
        canonicalizer: *Canonicalizer,
        surface: *const Expr,
        fill: ExprId,
        fills: *std.StringArrayHashMapUnmanaged(ExprId),
    ) !LineReading {
        const clash = readFills(allocator, theorem, canonicalizer, surface, fill, fills) catch |err| switch (err) {
            error.NamedUnknownUnread => {
                fills.clearRetainingCapacity();
                return .fits;
            },
            else => return err,
        };
        if (clash) |name| return .{ .clash = name };
        for (fills.keys(), fills.values()) |name, value| {
            const bound = self.bound.get(name) orelse continue;
            if (!try sameValue(canonicalizer, bound, value)) return .{ .clash = name };
        }
        return .fits;
    }
};

/// `surface` filled from `checked` modulo the ACUI combiners
/// (`Holes.materializeSurfaceModuloAcui`), when the fill is `checked`
/// modulo them.
fn fillModuloAcui(
    parser: *MM0Parser,
    theorem: *TheoremContext,
    env: *const GlobalEnv,
    registry: *RewriteRegistry,
    canonicalizer: *Canonicalizer,
    surface: *const Expr,
    checked: ExprId,
    names: ?*Holes.NameFills,
) !?ExprId {
    const fill = (try Holes.materializeSurfaceModuloAcui(
        parser,
        theorem,
        env,
        registry,
        canonicalizer,
        surface,
        checked,
        names,
    )) orelse return null;
    return if (try sameValue(canonicalizer, fill, checked)) fill else null;
}

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
pub const hasNamed = SurfaceExpr.containsNamedHole;
