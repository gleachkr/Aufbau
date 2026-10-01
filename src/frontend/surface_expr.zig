const std = @import("std");

const ExprModule = @import("../trusted/expressions.zig");
const Expr = ExprModule.Expr;
const SourceSpan = ExprModule.SourceSpan;
const MM0Parser = @import("parse_recovery.zig").MM0Parser;
const ExprId = @import("./expr.zig").ExprId;
const TheoremContext = @import("./expr.zig").TheoremContext;
const GlobalEnv = @import("./env.zig").GlobalEnv;
const RewriteRegistry = @import("./rewrite_registry.zig").RewriteRegistry;

pub fn containsHole(expr: *const Expr) bool {
    return switch (expr.*) {
        .hole => true,
        .variable => false,
        .term => |term| blk: {
            for (term.args) |arg| {
                if (containsHole(arg)) break :blk true;
            }
            break :blk false;
        },
    };
}

pub fn firstHoleSourceSpan(expr: *const Expr) ?SourceSpan {
    return switch (expr.*) {
        .hole => |hole| hole.token_span,
        .variable => null,
        .term => |term| blk: {
            for (term.args) |arg| {
                if (firstHoleSourceSpan(arg)) |span| break :blk span;
            }
            break :blk null;
        },
    };
}

pub fn sortNameById(env: *const GlobalEnv, sort_id: u7) ?[]const u8 {
    var it = env.sort_names.iterator();
    while (it.next()) |entry| {
        if (entry.value_ptr.* == sort_id) return entry.key_ptr.*;
    }
    return null;
}

pub fn parserSortName(parser: *const MM0Parser, sort: u7) []const u8 {
    var iter = parser.core.sort_names.iterator();
    while (iter.next()) |entry| {
        if (entry.value_ptr.* == sort) return entry.key_ptr.*;
    }
    return "?";
}

pub fn exprIdSortName(
    theorem: *const TheoremContext,
    env: *const GlobalEnv,
    expr_id: ExprId,
) ![]const u8 {
    return switch (theorem.interner.node(expr_id).*) {
        .app => |app| blk: {
            if (app.term_id >= env.terms.items.len) return error.UnknownTerm;
            break :blk env.terms.items[app.term_id].ret_sort_name;
        },
        .variable, .placeholder => theorem.currentLeafSortName(expr_id) orelse {
            return error.UnknownSort;
        },
    };
}

pub fn exprIdSort(
    parser: *MM0Parser,
    theorem: *const TheoremContext,
    env: *const GlobalEnv,
    expr_id: ExprId,
) !u7 {
    const name = try exprIdSortName(theorem, env, expr_id);
    return @intCast(parser.core.sort_names.get(name) orelse {
        return error.UnknownSort;
    });
}

pub fn containsStructuralHole(
    env: *const GlobalEnv,
    registry: *RewriteRegistry,
    expr: *const Expr,
) !bool {
    return switch (expr.*) {
        .hole => |hole| blk: {
            const sort_name = sortNameById(env, hole.sort) orelse {
                break :blk false;
            };
            break :blk (try registry.resolveStructuralCombinerForSort(
                env,
                sort_name,
            )) != null;
        },
        .variable => false,
        .term => |term| blk: {
            for (term.args) |arg| {
                if (try containsStructuralHole(env, registry, arg)) {
                    break :blk true;
                }
            }
            break :blk false;
        },
    };
}

/// Intern a holey surface into `theorem`, with `mint(context, theorem,
/// sort_name)` in place of each hole. Null when a hole's sort is unknown or
/// `mint` declines it. A hole-free subtree is interned as parsed.
pub fn internHoley(
    theorem: *TheoremContext,
    env: *const GlobalEnv,
    expr: *const Expr,
    context: anytype,
    comptime mint: fn (@TypeOf(context), *TheoremContext, []const u8) anyerror!?ExprId,
) anyerror!?ExprId {
    if (!containsHole(expr)) return try theorem.internParsedExpr(expr);
    switch (expr.*) {
        .hole => |hole| {
            const sort_name = sortNameById(env, hole.sort) orelse return null;
            return try mint(context, theorem, sort_name);
        },
        .variable => unreachable,
        .term => |term| {
            const args = try theorem.allocator.alloc(ExprId, term.args.len);
            defer theorem.allocator.free(args);
            for (term.args, 0..) |arg, idx| {
                args[idx] = (try internHoley(theorem, env, arg, context, mint)) orelse
                    return null;
            }
            return try theorem.interner.internApp(term.id, args);
        },
    }
}

/// Intern a holey surface with each hole replaced by its sort's structural
/// unit. Null when a hole's sort has no structural combiner.
pub fn lowerStructuralHolesToUnits(
    theorem: *TheoremContext,
    env: *const GlobalEnv,
    registry: *RewriteRegistry,
    expr: *const Expr,
) !?ExprId {
    const Units = struct {
        env: *const GlobalEnv,
        registry: *RewriteRegistry,

        fn mint(self: @This(), t: *TheoremContext, sort_name: []const u8) anyerror!?ExprId {
            const acui = try self.registry.resolveStructuralCombinerForSort(
                self.env,
                sort_name,
            ) orelse return null;
            return try t.interner.internApp(acui.unit_term_id, &.{});
        }
    };
    return internHoley(theorem, env, expr, Units{ .env = env, .registry = registry }, Units.mint);
}
