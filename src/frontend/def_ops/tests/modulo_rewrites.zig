const std = @import("std");
const DefOps = @import("../../def_ops.zig");
const Fixtures = @import("./fixtures.zig");
const ExprId = @import("../../expr.zig").ExprId;
const Context = DefOps.Context;
const Testing = DefOps.Testing;
const MatchSession = Testing.MatchSession;
const SymbolicExpr = Testing.SymbolicExpr;
const RewriteFixture = Fixtures.RewriteFixture;

test "matching modulo rewrites refuses hidden dummies bound to theorem args" {
    // The target pins mono's hidden dummies to the plain theorem args
    // `g`/`alpha`. Hidden dummies are bound variables (MMB `UDummy`), so a
    // non-bound witness would lower to an unfolding the verifier rejects —
    // the match must fail, and the failure must roll the session's witness
    // state back.
    var fixture = try RewriteFixture.init();
    defer fixture.deinit();

    var ctx = Context.initWithRegistry(
        fixture.arena.allocator(),
        &fixture.theorem,
        &fixture.env,
        &fixture.registry,
    );
    defer ctx.deinit();

    const mono_args = try fixture.arena.allocator().alloc(
        *const SymbolicExpr,
        1,
    );
    mono_args[0] = try Testing.allocSymbolic(&ctx, .{ .fixed = fixture.comp_expr });
    const symbolic_mono = try Testing.allocSymbolic(&ctx, .{ .app = .{
        .term_id = fixture.mono_term_id,
        .args = mono_args,
    } });

    var state = try MatchSession.init(fixture.arena.allocator(), 0);
    defer state.deinit(fixture.arena.allocator());

    try std.testing.expect(
        !try Testing.matchSymbolicToExprModuloRewrites(
            &ctx,
            symbolic_mono,
            fixture.rewrite_target_expr,
            &state,
        ),
    );
    try std.testing.expectEqual(@as(usize, 0), state.witnesses.count());
    try std.testing.expectEqual(@as(u32, 0), fixture.theorem.next_dummy_id);
    try std.testing.expectEqual(@as(u32, 0), fixture.theorem.next_dummy_dep);
}

test "failed match modulo rewrites restores state" {
    var fixture = try RewriteFixture.init();
    defer fixture.deinit();

    var ctx = Context.initWithRegistry(
        fixture.arena.allocator(),
        &fixture.theorem,
        &fixture.env,
        &fixture.registry,
    );
    defer ctx.deinit();

    const mono_args = try fixture.arena.allocator().alloc(
        *const SymbolicExpr,
        1,
    );
    mono_args[0] = try Testing.allocSymbolic(&ctx, .{ .fixed = fixture.comp_expr });
    const symbolic_mono = try Testing.allocSymbolic(&ctx, .{ .app = .{
        .term_id = fixture.mono_term_id,
        .args = mono_args,
    } });

    var state = try MatchSession.init(fixture.arena.allocator(), 0);
    defer state.deinit(fixture.arena.allocator());
    const start_dummy_info_len = state.symbolic_dummy_infos.items.len;
    const start_witness_count = state.witnesses.count();

    try std.testing.expect(!try Testing.matchSymbolicToExprModuloRewrites(
        &ctx,
        symbolic_mono,
        fixture.rewrite_target_expr,
        &state,
    ));
    try std.testing.expectEqual(
        start_dummy_info_len,
        state.symbolic_dummy_infos.items.len,
    );
    try std.testing.expectEqual(start_witness_count, state.witnesses.count());
    try std.testing.expectEqual(@as(u32, 0), fixture.theorem.next_dummy_id);
    try std.testing.expectEqual(@as(u32, 0), fixture.theorem.next_dummy_dep);
}

test "def exposure refuses witnesses that capture def arguments" {
    // The old target here required mono's hidden dummy `a` to be witnessed
    // by `g`, which occurs in the def's own argument instantiation `g o f` —
    // an unfolding MMB `UDummy` disjointness forbids (and `g` is not bound
    // besides). unfoldDefToward must return null rather than mint
    // an unverifiable witness.
    var fixture = try RewriteFixture.init();
    defer fixture.deinit();

    var ctx = Context.initWithRegistry(
        fixture.arena.allocator(),
        &fixture.theorem,
        &fixture.env,
        &fixture.registry,
    );
    defer ctx.deinit();

    try std.testing.expectEqual(
        @as(?ExprId, null),
        try ctx.unfoldDefToward(
            fixture.mono_expr,
            fixture.rewrite_target_expr,
            true,
            null,
        ),
    );
}

test "def exposure reads witnesses off a target in rewrite normal form" {
    // Legal variant of the exposure: the hidden dummies are witnessed by
    // fresh theorem dummies (bound, distinct, absent from the def's args —
    // the same shape the @vars pool provides in production). The target's
    // rhs is one comp_assoc step away from the unfolded body, so the dummies
    // are read off the body's normal form; the returned witness is the
    // pre-rewrite body instantiation.
    var fixture = try RewriteFixture.init();
    defer fixture.deinit();

    var ctx = Context.initWithRegistry(
        fixture.arena.allocator(),
        &fixture.theorem,
        &fixture.env,
        &fixture.registry,
    );
    defer ctx.deinit();

    const u = try fixture.theorem.addDummyVarResolved(
        "mor",
        fixture.mor_sort_id,
    );
    const v = try fixture.theorem.addDummyVarResolved(
        "mor",
        fixture.mor_sort_id,
    );

    const f = fixture.theorem.theorem_vars.items[0];
    const g = fixture.theorem.theorem_vars.items[1];
    const gof = try fixture.theorem.interner.internApp(
        fixture.comp_term_id,
        &[_]ExprId{ g, f },
    );
    const lhs_inner = try fixture.theorem.interner.internApp(
        fixture.comp_term_id,
        &[_]ExprId{ gof, u },
    );
    const lhs = try fixture.theorem.interner.internApp(
        fixture.comp_term_id,
        &[_]ExprId{ lhs_inner, v },
    );
    const mor_eq_term_id =
        fixture.env.term_names.get("mor_eq") orelse return error.MissingTerm;
    // Target rhs equals the target lhs; the unfolded body's rhs
    // `(g o f) o (u o v)` reaches it through one comp_assoc application on
    // the target side.
    const target = try fixture.theorem.interner.internApp(
        mor_eq_term_id,
        &[_]ExprId{ lhs, lhs },
    );

    const witness = try ctx.unfoldDefToward(
        fixture.mono_expr,
        target,
        true,
        null,
    ) orelse return error.MissingWitness;

    const rhs_inner = try fixture.theorem.interner.internApp(
        fixture.comp_term_id,
        &[_]ExprId{ u, v },
    );
    const rhs = try fixture.theorem.interner.internApp(
        fixture.comp_term_id,
        &[_]ExprId{ gof, rhs_inner },
    );
    const expected = try fixture.theorem.interner.internApp(
        mor_eq_term_id,
        &[_]ExprId{ lhs, rhs },
    );

    try std.testing.expectEqual(expected, witness);
}
