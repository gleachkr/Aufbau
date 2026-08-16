const std = @import("std");
const ArgInfo = @import("parse_recovery.zig").ArgInfo;
const AssertionKind = @import("parse_recovery.zig").AssertionKind;
const AssertionStmt = @import("parse_recovery.zig").AssertionStmt;
const Expr = @import("../trusted/expressions.zig").Expr;
const MM0Stmt = @import("parse_recovery.zig").MM0Stmt;
const SortStmt = @import("parse_recovery.zig").SortStmt;
const TermStmt = @import("parse_recovery.zig").TermStmt;
const TemplateExpr = @import("./rules.zig").TemplateExpr;

pub const TermDecl = struct {
    name: []const u8,
    args: []const ArgInfo,
    arg_names: []const ?[]const u8,
    dummy_args: []const ArgInfo,
    dummy_names: []const ?[]const u8,
    ret_sort_name: []const u8,
    /// Result-type dependencies, indexed over the bound args in declaration
    /// order (same convention as the MMB return Arg).
    ret_deps: u55 = 0,
    is_def: bool,
    body: ?TemplateExpr,
    // In recovery mode we sometimes keep a placeholder here for a parsed
    // term that failed semantic validation. The parser bakes term ids into
    // later expressions, so the `terms` array must stay aligned with parser
    // order even when the frontend decides that a term is unusable.
    available: bool = true,
};

/// A declared coercion edge, mirrored from the trusted parser. The parser
/// consumes `coercion` statements silently (they are notation-layer), so the
/// frontend re-derives src/dst from the coercion term's own signature.
pub const CoercionDecl = struct {
    term_id: u32,
    src_sort: []const u8,
    dst_sort: []const u8,
};

pub const RuleDecl = struct {
    name: []const u8,
    args: []const ArgInfo,
    arg_names: []const ?[]const u8,
    hyps: []const TemplateExpr,
    concl: TemplateExpr,
    kind: AssertionKind,
    is_local: bool,
};

pub const GlobalEnv = struct {
    allocator: std.mem.Allocator,
    sort_names: std.StringHashMap(u8),
    term_names: std.StringHashMap(u32),
    rule_names: std.StringHashMap(u32),
    terms: std.ArrayListUnmanaged(TermDecl) = .{},
    rules: std.ArrayListUnmanaged(RuleDecl) = .{},
    coercions: std.ArrayListUnmanaged(CoercionDecl) = .{},
    coercion_term_ids: std.AutoHashMapUnmanaged(u32, void) = .{},

    pub fn init(allocator: std.mem.Allocator) GlobalEnv {
        return .{
            .allocator = allocator,
            .sort_names = std.StringHashMap(u8).init(allocator),
            .term_names = std.StringHashMap(u32).init(allocator),
            .rule_names = std.StringHashMap(u32).init(allocator),
        };
    }

    pub fn addStmt(self: *GlobalEnv, stmt: MM0Stmt) !void {
        switch (stmt) {
            .sort => |sort| try self.addSort(sort),
            .term => |term| try self.addTerm(term),
            .assertion => |rule| try self.addRule(rule),
        }
    }

    pub fn addSort(self: *GlobalEnv, stmt: SortStmt) !void {
        const sort_id = std.math.cast(u8, self.sort_names.count()) orelse {
            return error.TooManySorts;
        };
        try self.sort_names.put(stmt.name, sort_id);
    }

    pub fn addTerm(self: *GlobalEnv, stmt: TermStmt) !void {
        const term_id = std.math.cast(u32, self.terms.items.len) orelse {
            return error.TooManyCompilerTerms;
        };
        try self.terms.append(self.allocator, try self.buildTermDecl(stmt));
        try self.term_names.put(stmt.name, term_id);
    }

    pub fn appendInvalidTerm(self: *GlobalEnv, name: []const u8) !void {
        // Reserve the parser-assigned term id, but do not expose the name in
        // `term_names`. Later parsed expressions may still mention this id,
        // and recovery code will reject those references via `available`.
        try self.terms.append(self.allocator, invalidTermDecl(name));
    }

    pub fn invalidateLastTerm(self: *GlobalEnv, name: []const u8) void {
        std.debug.assert(self.terms.items.len != 0);
        _ = self.term_names.remove(name);
        // Keep the slot so parser term ids remain stable, but replace the
        // declaration with an unavailable placeholder so semantic lookups do
        // not treat the broken term as part of the surviving environment.
        self.terms.items[self.terms.items.len - 1] = invalidTermDecl(name);
    }

    pub fn hasAvailableTerm(self: *const GlobalEnv, term_id: u32) bool {
        return term_id < self.terms.items.len and
            self.terms.items[term_id].available;
    }

    pub fn addRule(self: *GlobalEnv, stmt: AssertionStmt) !void {
        if (self.rule_names.contains(stmt.name)) {
            return error.DuplicateRuleName;
        }
        const rule_id = std.math.cast(u32, self.rules.items.len) orelse {
            return error.TooManyCompilerRules;
        };
        const hyps = try self.allocator.alloc(TemplateExpr, stmt.hyps.len);
        for (stmt.hyps, 0..) |hyp, idx| {
            hyps[idx] = try TemplateExpr.fromExpr(
                self.allocator,
                hyp,
                stmt.arg_exprs,
            );
        }
        const concl = try TemplateExpr.fromExpr(
            self.allocator,
            stmt.concl,
            stmt.arg_exprs,
        );
        try self.rules.append(self.allocator, .{
            .name = stmt.name,
            .args = stmt.args,
            .arg_names = stmt.arg_names,
            .hyps = hyps,
            .concl = concl,
            .kind = stmt.kind,
            .is_local = stmt.is_local,
        });
        try self.rule_names.put(stmt.name, rule_id);
    }

    pub fn rollbackRulesToLen(
        self: *GlobalEnv,
        previous_len: usize,
        name: []const u8,
    ) void {
        if (self.rules.items.len > previous_len) {
            self.rules.items.len = previous_len;
        }
        if (self.rule_names.get(name)) |rule_id| {
            if (rule_id >= previous_len) {
                _ = self.rule_names.remove(name);
            }
        }
    }

    pub fn removeLastRule(self: *GlobalEnv, name: []const u8) void {
        const rule_id = self.rule_names.get(name) orelse return;
        std.debug.assert(self.rules.items.len != 0);
        const last_idx = self.rules.items.len - 1;
        std.debug.assert(rule_id == last_idx);
        _ = self.rule_names.remove(name);
        self.rules.items.len = last_idx;
    }

    /// Mirror the parser's coercion registrations. Called after each parsed
    /// statement; the parser has already validated the declaration (unary
    /// term, unique routes), so unseen ids are simply appended. Terms that
    /// recovery invalidated are skipped via the signature guard.
    pub fn syncCoercionsFromParser(self: *GlobalEnv, parser: anytype) !void {
        var it = parser.coercionTermIds().keyIterator();
        while (it.next()) |term_id| try self.addCoercion(term_id.*);
    }

    pub fn addCoercion(self: *GlobalEnv, term_id: u32) !void {
        if (self.coercion_term_ids.contains(term_id)) return;
        if (term_id >= self.terms.items.len) return;
        const term = &self.terms.items[term_id];
        if (!term.available or term.args.len != 1) return;
        try self.coercion_term_ids.put(self.allocator, term_id, {});
        try self.coercions.append(self.allocator, .{
            .term_id = term_id,
            .src_sort = term.args[0].sort_name,
            .dst_sort = term.ret_sort_name,
        });
    }

    pub fn isCoercionTerm(self: *const GlobalEnv, term_id: u32) bool {
        return self.coercion_term_ids.contains(term_id);
    }

    /// Whether `src` reaches `dst` through the declared coercion graph
    /// (reflexively). The parser guarantees unique routes, hence no cycles;
    /// the fuel bound is a backstop, not a semantic limit.
    pub fn coercionPathExists(
        self: *const GlobalEnv,
        src: []const u8,
        dst: []const u8,
    ) bool {
        return self.coercionPathFuel(src, dst, self.coercions.items.len + 1);
    }

    fn coercionPathFuel(
        self: *const GlobalEnv,
        src: []const u8,
        dst: []const u8,
        fuel: usize,
    ) bool {
        if (std.mem.eql(u8, src, dst)) return true;
        if (fuel == 0) return false;
        for (self.coercions.items) |edge| {
            if (!std.mem.eql(u8, edge.src_sort, src)) continue;
            if (self.coercionPathFuel(edge.dst_sort, dst, fuel - 1)) {
                return true;
            }
        }
        return false;
    }

    /// Whether some sort is coercion-reachable from both `a` and `b`
    /// (reflexively). This is the enrollment condition for cross-sort
    /// derived bindings.
    pub fn sortsShareCoercionTarget(
        self: *const GlobalEnv,
        a: []const u8,
        b: []const u8,
    ) bool {
        if (self.coercionPathExists(a, b)) return true;
        if (self.coercionPathExists(b, a)) return true;
        // A strictly-common target must be the destination of some edge.
        for (self.coercions.items) |edge| {
            if (self.coercionPathExists(a, edge.dst_sort) and
                self.coercionPathExists(b, edge.dst_sort))
            {
                return true;
            }
        }
        return false;
    }

    /// Append the coercion term ids along the unique route `src` → `dst` to
    /// `out` (source-side first; empty when the sorts are equal). Returns
    /// false when no route exists, leaving `out` unchanged.
    pub fn coercionRoute(
        self: *const GlobalEnv,
        src: []const u8,
        dst: []const u8,
        allocator: std.mem.Allocator,
        out: *std.ArrayListUnmanaged(u32),
    ) !bool {
        const start_len = out.items.len;
        if (try self.coercionRouteFuel(
            src,
            dst,
            allocator,
            out,
            self.coercions.items.len + 1,
        )) return true;
        out.items.len = start_len;
        return false;
    }

    fn coercionRouteFuel(
        self: *const GlobalEnv,
        src: []const u8,
        dst: []const u8,
        allocator: std.mem.Allocator,
        out: *std.ArrayListUnmanaged(u32),
        fuel: usize,
    ) !bool {
        if (std.mem.eql(u8, src, dst)) return true;
        if (fuel == 0) return false;
        for (self.coercions.items) |edge| {
            if (!std.mem.eql(u8, edge.src_sort, src)) continue;
            try out.append(allocator, edge.term_id);
            if (try self.coercionRouteFuel(
                edge.dst_sort,
                dst,
                allocator,
                out,
                fuel - 1,
            )) return true;
            out.items.len -= 1;
        }
        return false;
    }

    pub fn getRuleId(self: *const GlobalEnv, name: []const u8) ?u32 {
        return self.rule_names.get(name);
    }

    pub fn getRule(self: *const GlobalEnv, name: []const u8) ?*const RuleDecl {
        const rule_id = self.getRuleId(name) orelse return null;
        return &self.rules.items[rule_id];
    }

    fn buildTermDecl(self: *GlobalEnv, stmt: TermStmt) !TermDecl {
        const body = if (stmt.body) |expr| blk: {
            if (stmt.dummy_exprs.len > 0) {
                const all_exprs = try self.allocator.alloc(
                    *const Expr,
                    stmt.arg_exprs.len + stmt.dummy_exprs.len,
                );
                @memcpy(all_exprs[0..stmt.arg_exprs.len], stmt.arg_exprs);
                @memcpy(all_exprs[stmt.arg_exprs.len..], stmt.dummy_exprs);
                break :blk try TemplateExpr.fromExpr(
                    self.allocator,
                    expr,
                    all_exprs,
                );
            } else {
                break :blk try TemplateExpr.fromExpr(
                    self.allocator,
                    expr,
                    stmt.arg_exprs,
                );
            }
        } else null;
        return .{
            .name = stmt.name,
            .args = stmt.args,
            .arg_names = stmt.arg_names,
            .dummy_args = stmt.dummy_args,
            .dummy_names = stmt.dummy_names,
            .ret_sort_name = stmt.ret_sort_name,
            .ret_deps = stmt.ret_deps,
            .is_def = stmt.is_def,
            .body = body,
        };
    }
};

fn invalidTermDecl(name: []const u8) TermDecl {
    // This sentinel is intentionally minimal. It exists only to occupy the
    // parser's term-id slot after recovery has discarded the declaration.
    return .{
        .name = name,
        .args = &.{},
        .arg_names = &.{},
        .dummy_args = &.{},
        .dummy_names = &.{},
        .ret_sort_name = "",
        .is_def = false,
        .body = null,
        .available = false,
    };
}
