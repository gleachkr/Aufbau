const std = @import("std");
const TheoremContext = @import("../expr.zig").TheoremContext;
const ExprId = @import("../expr.zig").ExprId;
const Expr = @import("../../trusted/expressions.zig").Expr;
const MM0Parser = @import("../parse_recovery.zig").MM0Parser;
const Sort = @import("../../trusted/sorts.zig").Sort;
const Idents = @import("../idents.zig");

const annotationMatchesTag = Idents.annotationMatchesTag;
const isAsciiWhitespace = Idents.isAsciiWhitespace;

const NameExprMap = std.StringHashMap(*const Expr);

pub const SortVarDecl = struct {
    sort_name: []const u8,
    sort_id: u8,
};

pub const SortVarPool = struct {
    sort_name: []const u8,
    sort_id: u8,
    tokens: std.ArrayListUnmanaged([]const u8) = .{},

    pub fn deinit(
        self: *SortVarPool,
        allocator: std.mem.Allocator,
    ) void {
        self.tokens.deinit(allocator);
    }
};

pub const SortVarRegistry = struct {
    allocator: std.mem.Allocator,
    tokens: std.StringHashMap(SortVarDecl),
    pools: std.StringHashMap(SortVarPool),

    pub fn init(allocator: std.mem.Allocator) SortVarRegistry {
        return .{
            .allocator = allocator,
            .tokens = std.StringHashMap(SortVarDecl).init(allocator),
            .pools = std.StringHashMap(SortVarPool).init(allocator),
        };
    }

    pub fn deinit(self: *SortVarRegistry) void {
        var pool_iter = self.pools.valueIterator();
        while (pool_iter.next()) |pool| {
            pool.deinit(self.allocator);
        }
        self.pools.deinit();
        self.tokens.deinit();
    }

    pub fn count(self: *const SortVarRegistry) usize {
        return self.tokens.count();
    }

    pub fn getTokenDecl(
        self: *const SortVarRegistry,
        token: []const u8,
    ) ?SortVarDecl {
        return self.tokens.get(token);
    }

    pub fn getPool(
        self: *const SortVarRegistry,
        sort_name: []const u8,
    ) ?SortVarPool {
        return self.pools.get(sort_name);
    }

    fn append(
        self: *SortVarRegistry,
        token: []const u8,
        decl: SortVarDecl,
    ) !void {
        try self.tokens.put(token, decl);
        const gop = try self.pools.getOrPut(decl.sort_name);
        if (!gop.found_existing) {
            gop.value_ptr.* = .{
                .sort_name = decl.sort_name,
                .sort_id = decl.sort_id,
            };
        }
        try gop.value_ptr.tokens.append(self.allocator, token);
    }
};

/// One `@vars` pool variable, as `theorem_vars` binds its token.
pub const PoolVar = struct {
    token: []const u8,
    expr: ExprId,
    /// Its dependency bits; 0 when the token is not bound to a variable.
    deps: u55,

    /// True for a variable sharing no dependency bit with `taken`: it is
    /// none of the variables `taken` collects.
    pub fn avoids(self: PoolVar, taken: u55) bool {
        return self.deps != 0 and self.deps & taken == 0;
    }
};

/// The pool variables of one sort, in sorted token order, each as
/// `theorem_vars` binds it (search pre-materializes them as dummies of its
/// work theorem). A token `theorem_vars` does not bind is skipped.
pub const PoolVars = struct {
    allocator: std.mem.Allocator,
    tokens: []const []const u8,
    index: usize = 0,
    theorem: *TheoremContext,
    theorem_vars: *const NameExprMap,

    pub fn init(
        allocator: std.mem.Allocator,
        sort_vars: *const SortVarRegistry,
        sort_name: []const u8,
        theorem: *TheoremContext,
        theorem_vars: *const NameExprMap,
    ) !PoolVars {
        const pool = sort_vars.getPool(sort_name);
        const tokens = try allocator.dupe([]const u8, if (pool) |p| p.tokens.items else &.{});
        std.mem.sort([]const u8, tokens, {}, struct {
            fn lt(_: void, a: []const u8, b: []const u8) bool {
                return std.mem.order(u8, a, b) == .lt;
            }
        }.lt);
        return .{
            .allocator = allocator,
            .tokens = tokens,
            .theorem = theorem,
            .theorem_vars = theorem_vars,
        };
    }

    pub fn deinit(self: *PoolVars) void {
        self.allocator.free(self.tokens);
    }

    pub fn next(self: *PoolVars) !?PoolVar {
        while (self.index < self.tokens.len) {
            const token = self.tokens[self.index];
            self.index += 1;
            const parser_var = self.theorem_vars.get(token) orelse continue;
            const expr = self.theorem.internParsedExpr(parser_var) catch |err| switch (err) {
                error.OutOfMemory => return err,
                else => continue,
            };
            const info = self.theorem.currentLeafInfo(expr) catch null;
            return .{
                .token = token,
                .expr = expr,
                .deps = if (info) |leaf| leaf.deps else 0,
            };
        }
        return null;
    }

    /// The next pool variable that avoids `taken` (`PoolVar.avoids`), or,
    /// with `taken` null, the next one whatever its bits.
    pub fn nextAvoiding(self: *PoolVars, taken: ?u55) !?PoolVar {
        while (try self.next()) |pool_var| {
            const mask = taken orelse return pool_var;
            if (pool_var.avoids(mask)) return pool_var;
        }
        return null;
    }
};

pub fn processSortVarAnnotations(
    parser: *const MM0Parser,
    sort_name: []const u8,
    sort_modifiers: Sort,
    annotations: []const []const u8,
    sort_vars: *SortVarRegistry,
) !void {
    const vars_tag = "@vars";

    for (annotations) |ann| {
        if (!annotationMatchesTag(ann, vars_tag)) continue;

        if (sort_modifiers.strict) return error.VarsStrictSort;
        if (sort_modifiers.free) return error.VarsFreeSort;

        const sort_id = parser.core.sort_names.get(sort_name) orelse {
            return error.UnknownSort;
        };

        const tail = std.mem.trim(u8, ann[vars_tag.len..], " \t\r\n");
        if (tail.len == 0) return error.InvalidVarsAnnotation;

        var iter = std.mem.tokenizeAny(u8, tail, " \t\r\n");
        while (iter.next()) |token| {
            try validateTokenHasNoSyntaxCollision(parser, token);
            if (sort_vars.getTokenDecl(token) != null) {
                return error.DuplicateVarsToken;
            }
            try sort_vars.append(token, .{
                .sort_name = sort_name,
                .sort_id = sort_id,
            });
        }
    }
}

pub fn validateSortVarCollisions(
    parser: *const MM0Parser,
    sort_vars: *const SortVarRegistry,
) !void {
    var iter = sort_vars.tokens.iterator();
    while (iter.next()) |entry| {
        try validateTokenHasNoSyntaxCollision(parser, entry.key_ptr.*);
    }
}

pub fn ensureMathTextVars(
    parser: *const MM0Parser,
    theorem: *TheoremContext,
    theorem_vars: *NameExprMap,
    sort_vars: *const SortVarRegistry,
    math: []const u8,
) !void {
    var pos: usize = 0;
    while (nextMathToken(
        math,
        &pos,
        parser.core.left_delims,
        parser.core.right_delims,
    )) |token| {
        if (theorem_vars.contains(token)) {
            if (parser.isRegisteredHoleToken(token)) {
                return error.HoleTokenNameCollision;
            }
            continue;
        }
        if (hasSyntaxCollision(parser, token)) continue;
        if (sort_vars.count() == 0) continue;

        if (sort_vars.getTokenDecl(token)) |decl| {
            if (parser.isRegisteredHoleToken(token)) {
                return error.HoleTokenNameCollision;
            }
            try theorem.ensureNamedDummyParserVar(
                parser.core.allocator,
                theorem_vars,
                token,
                decl.sort_name,
                decl.sort_id,
            );
        }
    }
}

fn validateTokenHasNoSyntaxCollision(
    parser: *const MM0Parser,
    token: []const u8,
) !void {
    if (parser.isRegisteredHoleToken(token)) {
        return error.HoleTokenNameCollision;
    }
    if (hasSyntaxCollision(parser, token)) return error.VarsTokenCollision;
}

fn hasSyntaxCollision(parser: *const MM0Parser, token: []const u8) bool {
    return parser.core.term_names.contains(token) or
        parser.core.formula_markers.contains(token) or
        parser.core.prefix_notations.contains(token) or
        parser.core.infix_notations.contains(token);
}

fn nextMathToken(
    src: []const u8,
    pos: *usize,
    left_delims: [256]bool,
    right_delims: [256]bool,
) ?[]const u8 {
    while (pos.* < src.len) {
        const ch = src[pos.*];
        if (isAsciiWhitespace(ch)) {
            pos.* += 1;
        } else break;
    }
    if (pos.* >= src.len) return null;

    const start = pos.*;
    while (pos.* < src.len) {
        const ch = src[pos.*];
        pos.* += 1;
        if (left_delims[ch]) break;
        if (pos.* >= src.len) break;

        const next_ch = src[pos.*];
        if (isAsciiWhitespace(next_ch) or right_delims[next_ch]) break;
    }

    return src[start..pos.*];
}
