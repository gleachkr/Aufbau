//! Tests for the directed-rewrite big-step normalizer (task #196).

const std = @import("std");
const DefOps = @import("../../def_ops.zig");
const Fixtures = @import("./fixtures.zig");
const ExprId = @import("../../expr.zig").ExprId;
const Context = DefOps.Context;
const Testing = DefOps.Testing;
const MatchSession = Testing.MatchSession;
const SymbolicExpr = Testing.SymbolicExpr;
const RewriteFixture = Fixtures.RewriteFixture;

test "big-step normalization opens nested fixed subtrees" {
    var fixture = try RewriteFixture.init();
    defer fixture.deinit();

    var ctx = Context.initWithRegistry(
        fixture.arena.allocator(),
        &fixture.theorem,
        &fixture.env,
        &fixture.registry,
    );
    defer ctx.deinit();

    // mor_eq has no rewrite rules; the only redex sits inside a nested
    // .fixed child — the shape rule-rhs instantiation and def expansion
    // produce (subst entries are fixed representatives).
    const mor_eq_term_id = fixture.env.term_names.get("mor_eq") orelse {
        return error.MissingTerm;
    };
    const g = fixture.theorem.theorem_vars.items[1];
    const eq_args = try fixture.arena.allocator().alloc(
        *const SymbolicExpr,
        2,
    );
    eq_args[0] = try Testing.allocSymbolic(
        &ctx,
        .{ .fixed = fixture.comp_expr },
    );
    eq_args[1] = try Testing.allocSymbolic(&ctx, .{ .fixed = g });
    const symbolic = try Testing.allocSymbolic(&ctx, .{ .app = .{
        .term_id = mor_eq_term_id,
        .args = eq_args,
    } });

    var state = try MatchSession.init(fixture.arena.allocator(), 0);
    defer state.deinit(fixture.arena.allocator());

    // Before the .fixed opening pass this returned null — a false "no
    // reduction" on exactly the mixed symbolic/concrete shape above.
    const reduced = (try Testing.bigStepSymbolic(
        &ctx,
        symbolic,
        &state,
    )) orelse return error.BigStepMissedNestedFixed;

    // (g o f) o alpha reduces to g o (f o alpha) under comp_assoc; the
    // normal form matches the expected expression structurally.
    const f = fixture.theorem.theorem_vars.items[0];
    const alpha = fixture.theorem.theorem_vars.items[2];
    const foa = try fixture.theorem.interner.internApp(
        fixture.comp_term_id,
        &[_]ExprId{ f, alpha },
    );
    const nf = try fixture.theorem.interner.internApp(
        fixture.comp_term_id,
        &[_]ExprId{ g, foa },
    );
    const expected = try fixture.theorem.interner.internApp(
        mor_eq_term_id,
        &[_]ExprId{ nf, g },
    );
    try std.testing.expect(try Testing.matchSymbolicToExprModuloRewrites(
        &ctx,
        reduced,
        expected,
        &state,
    ));

    // Matching modulo rewrites must reach that normal form from mor_eq,
    // although mor_eq itself has no rewrite rules: the redex sits in its
    // child. Cover symbolic and fixed roots.
    const concrete = try fixture.theorem.interner.internApp(
        mor_eq_term_id,
        &.{ fixture.comp_expr, g },
    );
    const fixed = try Testing.allocSymbolic(&ctx, .{ .fixed = concrete });
    for ([_]*const SymbolicExpr{ symbolic, fixed }) |original| {
        var search_state = try MatchSession.init(
            fixture.arena.allocator(),
            0,
        );
        defer search_state.deinit(fixture.arena.allocator());
        try std.testing.expect(try Testing.matchSymbolicToExprModuloRewrites(
            &ctx,
            original,
            expected,
            &search_state,
        ));
    }
}

test "normalization that takes all the fuel still reaches its normal form" {
    // Right-associating a left comb of n leaves takes (n-1)(n-2)/2
    // `comp_assoc` steps: 28 for 9 leaves and 36 for 10, so
    // `L9 ~ L10` uses exactly the 64 units of fuel. Its last step leaves
    // `comp` apps where no rule fires: that is a normal form, not a fuel
    // stop. `L10 ~ L10` needs 72 and is cut off.
    var fixture = try RewriteFixture.init();
    defer fixture.deinit();

    var ctx = Context.initWithRegistry(
        fixture.arena.allocator(),
        &fixture.theorem,
        &fixture.env,
        &fixture.registry,
    );
    defer ctx.deinit();

    const mor_eq_term_id = fixture.env.term_names.get("mor_eq") orelse {
        return error.MissingTerm;
    };
    // f, g, alpha in turn: no two neighbours are equal, so `dup_left`
    // never fires.
    const leaves = fixture.theorem.theorem_vars.items[0..3];
    const comb = struct {
        fn left(fx: *RewriteFixture, ls: []const ExprId, n: usize) !ExprId {
            var acc = ls[0];
            for (1..n) |i| {
                acc = try fx.theorem.interner.internApp(
                    fx.comp_term_id,
                    &[_]ExprId{ acc, ls[i % ls.len] },
                );
            }
            return acc;
        }
    }.left;

    const Row = struct { lhs: usize, rhs: usize, exhausted: bool };
    for ([_]Row{
        .{ .lhs = 9, .rhs = 10, .exhausted = false },
        .{ .lhs = 10, .rhs = 10, .exhausted = true },
    }) |row| {
        const expr = try fixture.theorem.interner.internApp(
            mor_eq_term_id,
            &[_]ExprId{
                try comb(&fixture, leaves, row.lhs),
                try comb(&fixture, leaves, row.rhs),
            },
        );
        var state = try MatchSession.init(fixture.arena.allocator(), 0);
        defer state.deinit(fixture.arena.allocator());
        _ = try Testing.bigStepSymbolic(
            &ctx,
            try Testing.allocSymbolic(&ctx, .{ .fixed = expr }),
            &state,
        ) orelse return error.NoReduction;
        try std.testing.expectEqual(row.exhausted, state.rewrite_fuel_exhausted);
    }
}
