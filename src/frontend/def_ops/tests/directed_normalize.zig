//! Tests for the directed-rewrite big-step normalizer (task #196).

const std = @import("std");
const DefOps = @import("../../def_ops.zig");
const Fixtures = @import("./fixtures.zig");
const ExprId = @import("../../expr.zig").ExprId;
const Context = DefOps.Context;
const Testing = DefOps.Testing;
const MatchSession = Testing.MatchSession;
const SymbolicExpr = Testing.SymbolicExpr;
const SemanticStepFixture = Fixtures.SemanticStepFixture;

test "big-step normalization opens nested fixed subtrees" {
    var fixture = try SemanticStepFixture.init();
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

    // (g o f) o alpha reduces to g o (f o alpha) under comp_assoc; budget 0
    // permits no further semantic steps, so this is a structural match of
    // the normal form.
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
    try std.testing.expect(try Testing.matchSymbolicToExprSemantic(
        &ctx,
        reduced,
        expected,
        &state,
        0,
    ));
}
