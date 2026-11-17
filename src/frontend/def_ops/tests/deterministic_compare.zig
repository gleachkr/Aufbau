//! `compareTransparent` decides by unfolding only the later def: rows that
//! unfolding reconciles get a plan, rows it cannot reconcile get none, and a
//! failing comparison of terms that share positions does work linear in the
//! sharing, not in the tree.

const std = @import("std");

const DefOps = @import("../../def_ops.zig");
const FrontendEnv = @import("../../env.zig");
const FrontendExpr = @import("../../expr.zig");
const Expr = @import("../../../trusted/expressions.zig").Expr;
const MM0Parser = @import("../../parse_recovery.zig").MM0Parser;
const ExprId = FrontendExpr.ExprId;

/// Successor numerals, tagged pairs, a def that binds a dummy, a projection,
/// two defs that name their argument twice, an ACUI combiner and a
/// `@rewrite` head.
const theory =
    \\delimiter $ ( ) $;
    \\provable sort wff;
    \\sort V;
    \\sort R;
    \\term eq (a b: R): wff;
    \\term zero: R;
    \\term s (a: R): R;
    \\term pr (a b: R): R;
    \\term vr (x: V): R;
    \\term ab {x: V} (p: R x): R;
    \\--| @acui add_assoc add_comm zero _
    \\term add (a b: R): R;
    \\term rw (a b: R): R;
    \\def one: R = $ s zero $;
    \\def two: R = $ s one $;
    \\def three: R = $ s two $;
    \\def tag2 (a: R): R = $ pr two a $;
    \\def tag3 (a: R): R = $ pr three a $;
    \\def sng (a: R) (.x: V): R = $ ab x (pr (vr x) a) $;
    \\def cst (a b: R): R = $ a $;
    \\def bag (a b: R): R = $ add a b $;
    \\def dbl (a: R): R = $ pr a a $;
    \\def dbl2 (a: R): R = $ pr a a $;
    \\--| @relation R eq eq_refl eq_trans eq_symm _
    \\axiom eq_refl (a: R): $ eq a a $;
    \\axiom eq_trans (a b c: R): $ eq a b $ > $ eq b c $ > $ eq a c $;
    \\axiom eq_symm (a b: R): $ eq a b $ > $ eq b a $;
    \\axiom add_assoc (a b c: R): $ eq (add (add a b) c) (add a (add b c)) $;
    \\axiom add_comm (a b: R): $ eq (add a b) (add b a) $;
    \\--| @rewrite
    \\axiom rw_red (a b: R): $ eq (rw a b) a $;
    \\theorem t (x y z: R): $ eq x y $;
;

const Case = struct {
    arena: std.heap.ArenaAllocator,
    parser: MM0Parser,
    env: FrontendEnv.GlobalEnv,
    theorem: FrontendExpr.TheoremContext,
    vars: std.StringHashMap(*const Expr),

    fn init(self: *Case) !void {
        self.arena = std.heap.ArenaAllocator.init(std.testing.allocator);
        const allocator = self.arena.allocator();
        self.parser = MM0Parser.init(theory, allocator);
        self.env = FrontendEnv.GlobalEnv.init(allocator);
        self.theorem = FrontendExpr.TheoremContext.init(allocator);
        self.vars = std.StringHashMap(*const Expr).init(allocator);
        while (try self.parser.next()) |stmt| {
            try self.env.addStmt(stmt);
            const assertion = switch (stmt) {
                .assertion => |value| value,
                else => continue,
            };
            if (assertion.kind != .theorem) continue;
            try self.theorem.seedAssertion(assertion);
            for (assertion.arg_names, assertion.arg_exprs) |name, arg| {
                try self.vars.put(name orelse continue, arg);
            }
        }
    }

    fn deinit(self: *Case) void {
        self.vars.deinit();
        self.theorem.deinit();
        self.arena.deinit();
    }

    fn expr(self: *Case, text: []const u8) !ExprId {
        const parsed = try self.parser.parseMathText(text, &self.vars);
        return try self.theorem.internParsedExpr(parsed);
    }

    fn term(self: *Case, name: []const u8) !u32 {
        return self.env.term_names.get(name) orelse error.MissingTerm;
    }
};

test "compareTransparent plans exactly the pairs unfolding reconciles" {
    var case: Case = undefined;
    try case.init();
    defer case.deinit();
    var def_ops = DefOps.Context.init(case.arena.allocator(), &case.theorem, &case.env);
    defer def_ops.deinit();

    const Row = struct { lhs: []const u8, rhs: []const u8, plan: bool };
    const rows = [_]Row{
        // Successor numerals: unfolding the later def first meets `zero`
        // against `s zero`.
        .{ .lhs = "two", .rhs = "three", .plan = false },
        .{ .lhs = "two", .rhs = "s one", .plan = true },
        .{ .lhs = "three", .rhs = "s (s (s zero))", .plan = true },
        // Two defs that unfold to the same head, apart in an argument it
        // forces.
        .{ .lhs = "tag2 x", .rhs = "tag3 x", .plan = false },
        .{ .lhs = "tag2 x", .rhs = "tag2 y", .plan = false },
        .{ .lhs = "tag2 x", .rhs = "pr two x", .plan = true },
        // Through a body that binds a dummy.
        .{ .lhs = "sng x", .rhs = "sng y", .plan = false },
        // `cst` drops its second argument, and unfolds to its first.
        .{ .lhs = "cst x y", .rhs = "cst x z", .plan = true },
        .{ .lhs = "cst x y", .rhs = "x", .plan = true },
        .{ .lhs = "cst x y", .rhs = "z", .plan = false },
        // A variable against a rigid head, and two rigid heads.
        .{ .lhs = "s x", .rhs = "x", .plan = false },
        .{ .lhs = "pr x y", .rhs = "s x", .plan = false },
        // Unfolding alone does not rearrange an ACUI bag or reduce a
        // `@rewrite` redex: those are the normalizer's.
        .{ .lhs = "add x y", .rhs = "add y x", .plan = false },
        .{ .lhs = "bag x y", .rhs = "bag y x", .plan = false },
        .{ .lhs = "rw x y", .rhs = "x", .plan = false },
    };
    for (rows) |row| {
        const lhs = try case.expr(row.lhs);
        const rhs = try case.expr(row.rhs);
        for ([_][2]ExprId{ .{ lhs, rhs }, .{ rhs, lhs } }) |pair| {
            const got = (try def_ops.compareTransparent(pair[0], pair[1])) != null;
            std.testing.expectEqual(row.plan, got) catch |err| {
                std.debug.print("compareTransparent({s}, {s})\n", .{ row.lhs, row.rhs });
                return err;
            };
        }
    }
}

test "compareTransparent rejects a mismatch under shared positions in linear work" {
    // `dbl` and `dbl2` both name their argument twice: read as trees, 40
    // levels hold 2^40 positions. The later def unfolds at each level and
    // the first argument's mismatch decides, so the work is per level.
    var case: Case = undefined;
    try case.init();
    defer case.deinit();
    var def_ops = DefOps.Context.init(case.arena.allocator(), &case.theorem, &case.env);
    defer def_ops.deinit();

    const dbl = try case.term("dbl");
    const dbl2 = try case.term("dbl2");
    var lhs = try case.expr("x");
    var rhs = try case.expr("y");
    for (0..40) |_| {
        lhs = try case.theorem.interner.internApp(dbl, &.{lhs});
        rhs = try case.theorem.interner.internApp(dbl2, &.{rhs});
    }
    const before = FrontendExpr.work_ticks + FrontendExpr.work_ticks_sym;
    try std.testing.expect((try def_ops.compareTransparent(lhs, rhs)) == null);
    const work = FrontendExpr.work_ticks + FrontendExpr.work_ticks_sym - before;
    std.testing.expect(work < 10_000) catch |err| {
        std.debug.print("work {d}\n", .{work});
        return err;
    };
}

test "an opened def binds a rule binder on either side" {
    // `two` against `s X`: `two` is the later def, so it opens to
    // `s one` with the pattern on the right, and `one` meets `X` there.
    // The binder takes the opened term as it is, as it does on the left.
    var case: Case = undefined;
    try case.init();
    defer case.deinit();
    var def_ops = DefOps.Context.init(case.arena.allocator(), &case.theorem, &case.env);
    defer def_ops.deinit();
    const Testing = DefOps.Testing;

    const binder = try Testing.allocSymbolic(&def_ops, .{ .binder = 0 });
    const pattern = try Testing.allocSymbolic(&def_ops, .{ .app = .{
        .term_id = try case.term("s"),
        .args = &.{binder},
    } });
    const fixed = struct {
        fn of(ctx: *DefOps.Context, c: *Case, text: []const u8) !*const Testing.SymbolicExpr {
            return try Testing.allocSymbolic(ctx, .{ .fixed = try c.expr(text) });
        }
    }.of;

    var state = try Testing.MatchSession.init(case.arena.allocator(), 1);
    defer state.deinit(case.arena.allocator());
    try std.testing.expect(try Testing.matchSymbolicToSymbolic(
        &def_ops,
        try fixed(&def_ops, &case, "two"),
        pattern,
        &state,
    ));
    // `X` holds `one`: it meets `s zero` and not `zero`.
    try std.testing.expect(try Testing.matchSymbolicToSymbolic(
        &def_ops,
        binder,
        try fixed(&def_ops, &case, "s zero"),
        &state,
    ));
    try std.testing.expect(!try Testing.matchSymbolicToSymbolic(
        &def_ops,
        binder,
        try fixed(&def_ops, &case, "zero"),
        &state,
    ));
}
