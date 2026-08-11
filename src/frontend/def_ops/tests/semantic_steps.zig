const std = @import("std");
const DefOps = @import("../../def_ops.zig");
const Fixtures = @import("./fixtures.zig");
const RewriteRule = @import("../../rewrite_registry.zig").RewriteRule;
const ExprId = @import("../../expr.zig").ExprId;
const Context = DefOps.Context;
const Testing = DefOps.Testing;
const MatchSession = Testing.MatchSession;
const SymbolicExpr = Testing.SymbolicExpr;
const SemanticStepCandidate = DefOps.SemanticStepCandidate;
const SemanticStepFixture = Fixtures.SemanticStepFixture;
const SemanticAcuiExposureFixture = Fixtures.SemanticAcuiExposureFixture;
const SemanticWrappedAcuiDefFixture =
    Fixtures.SemanticWrappedAcuiDefFixture;
const SemanticQuantifiedAcuiDefFixture =
    Fixtures.SemanticQuantifiedAcuiDefFixture;
const allocNoneSeeds = Fixtures.allocNoneSeeds;
const hasConcreteUnfold = Fixtures.hasConcreteUnfold;
const hasSymbolicUnfold = Fixtures.hasSymbolicUnfold;
const hasRewriteRule = Fixtures.hasRewriteRule;
const hasAcuiHead = Fixtures.hasAcuiHead;
const hasNormalizeBigStep = Fixtures.hasNormalizeBigStep;

test "semantic step enumeration finds root def rewrite and acui moves" {
    var fixture = try SemanticStepFixture.init();
    defer fixture.deinit();

    var ctx = Context.initWithRegistry(
        fixture.arena.allocator(),
        &fixture.theorem,
        &fixture.env,
        &fixture.registry,
    );
    defer ctx.deinit();

    var mono_steps = std.ArrayListUnmanaged(SemanticStepCandidate){};
    defer mono_steps.deinit(fixture.arena.allocator());
    try Testing.collectSemanticStepCandidatesExpr(
        &ctx,
        fixture.mono_expr,
        &mono_steps,
    );
    try std.testing.expect(
        hasConcreteUnfold(
            mono_steps.items,
            fixture.mono_expr,
            fixture.mono_term_id,
        ),
    );
    try std.testing.expect(!hasRewriteRule(
        mono_steps.items,
        fixture.comp_assoc_rule_id,
        fixture.comp_term_id,
    ));
    try std.testing.expect(!hasAcuiHead(
        mono_steps.items,
        fixture.join_term_id,
    ));
    // The big-step is offered only where the head has rewrite rules.
    try std.testing.expect(!hasNormalizeBigStep(mono_steps.items));

    var comp_steps = std.ArrayListUnmanaged(SemanticStepCandidate){};
    defer comp_steps.deinit(fixture.arena.allocator());
    try Testing.collectSemanticStepCandidatesExpr(
        &ctx,
        fixture.comp_expr,
        &comp_steps,
    );
    try std.testing.expect(hasRewriteRule(
        comp_steps.items,
        fixture.comp_assoc_rule_id,
        fixture.comp_term_id,
    ));
    try std.testing.expect(!hasConcreteUnfold(
        comp_steps.items,
        fixture.comp_expr,
        fixture.comp_term_id,
    ));
    try std.testing.expect(!hasAcuiHead(
        comp_steps.items,
        fixture.join_term_id,
    ));
    // Big-step offered for the rewritable head, ordered after the per-rule
    // single steps so it fires only when they failed at this node.
    try std.testing.expect(hasNormalizeBigStep(comp_steps.items));
    try std.testing.expect(
        comp_steps.items[comp_steps.items.len - 1] == .normalize_rewrites,
    );

    var ctx_steps = std.ArrayListUnmanaged(SemanticStepCandidate){};
    defer ctx_steps.deinit(fixture.arena.allocator());
    try Testing.collectSemanticStepCandidatesExpr(
        &ctx,
        fixture.ctx_expr,
        &ctx_steps,
    );
    try std.testing.expect(hasAcuiHead(
        ctx_steps.items,
        fixture.join_term_id,
    ));
    try std.testing.expect(!hasRewriteRule(
        ctx_steps.items,
        fixture.comp_assoc_rule_id,
        fixture.comp_term_id,
    ));
}

test "semantic step enumeration is registry-gated" {
    var fixture = try SemanticStepFixture.init();
    defer fixture.deinit();

    var ctx = Context.init(
        fixture.arena.allocator(),
        &fixture.theorem,
        &fixture.env,
    );
    defer ctx.deinit();

    var mono_steps = std.ArrayListUnmanaged(SemanticStepCandidate){};
    defer mono_steps.deinit(fixture.arena.allocator());
    try Testing.collectSemanticStepCandidatesExpr(
        &ctx,
        fixture.mono_expr,
        &mono_steps,
    );
    try std.testing.expect(
        hasConcreteUnfold(
            mono_steps.items,
            fixture.mono_expr,
            fixture.mono_term_id,
        ),
    );

    var comp_steps = std.ArrayListUnmanaged(SemanticStepCandidate){};
    defer comp_steps.deinit(fixture.arena.allocator());
    try Testing.collectSemanticStepCandidatesExpr(
        &ctx,
        fixture.comp_expr,
        &comp_steps,
    );
    try std.testing.expectEqual(@as(usize, 0), comp_steps.items.len);

    var ctx_steps = std.ArrayListUnmanaged(SemanticStepCandidate){};
    defer ctx_steps.deinit(fixture.arena.allocator());
    try Testing.collectSemanticStepCandidatesExpr(
        &ctx,
        fixture.ctx_expr,
        &ctx_steps,
    );
    try std.testing.expectEqual(@as(usize, 0), ctx_steps.items.len);
}

test "semantic step enumeration handles symbolic roots" {
    var fixture = try SemanticStepFixture.init();
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

    var symbolic_steps = std.ArrayListUnmanaged(SemanticStepCandidate){};
    defer symbolic_steps.deinit(fixture.arena.allocator());
    try Testing.collectSemanticStepCandidatesSymbolic(
        &ctx,
        symbolic_mono,
        &symbolic_steps,
    );
    try std.testing.expect(
        hasSymbolicUnfold(symbolic_steps.items, fixture.mono_term_id),
    );

    const fixed_comp = try Testing.allocSymbolic(
        &ctx,
        .{ .fixed = fixture.comp_expr },
    );
    var fixed_steps = std.ArrayListUnmanaged(SemanticStepCandidate){};
    defer fixed_steps.deinit(fixture.arena.allocator());
    try Testing.collectSemanticStepCandidatesSymbolic(
        &ctx,
        fixed_comp,
        &fixed_steps,
    );
    try std.testing.expect(hasRewriteRule(
        fixed_steps.items,
        fixture.comp_assoc_rule_id,
        fixture.comp_term_id,
    ));
}

test "semantic step enumeration ignores placeholder roots" {
    var fixture = try SemanticStepFixture.init();
    defer fixture.deinit();

    var ctx = Context.initWithRegistry(
        fixture.arena.allocator(),
        &fixture.theorem,
        &fixture.env,
        &fixture.registry,
    );
    defer ctx.deinit();

    const placeholder = try fixture.theorem.addPlaceholderResolved(
        "mor",
    );

    var expr_steps = std.ArrayListUnmanaged(SemanticStepCandidate){};
    defer expr_steps.deinit(fixture.arena.allocator());
    try Testing.collectSemanticStepCandidatesExpr(
        &ctx,
        placeholder,
        &expr_steps,
    );
    try std.testing.expectEqual(@as(usize, 0), expr_steps.items.len);

    const fixed_placeholder = try Testing.allocSymbolic(
        &ctx,
        .{ .fixed = placeholder },
    );
    var symbolic_steps = std.ArrayListUnmanaged(SemanticStepCandidate){};
    defer symbolic_steps.deinit(fixture.arena.allocator());
    try Testing.collectSemanticStepCandidatesSymbolic(
        &ctx,
        fixed_placeholder,
        &symbolic_steps,
    );
    try std.testing.expectEqual(@as(usize, 0), symbolic_steps.items.len);
}

test "semantic search refuses unfold binding hidden dummies to theorem args" {
    // The target pins mono's hidden dummies to the plain theorem args
    // `g`/`alpha`. Hidden dummies are bound variables (MMB `UDummy`), so a
    // non-bound witness would lower to an unfolding the verifier rejects —
    // the semantic search must refuse the match, and the refusal must roll
    // the session's witness state back.
    var fixture = try SemanticStepFixture.init();
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
        !try Testing.matchSymbolicToExprSemantic(
            &ctx,
            symbolic_mono,
            fixture.semantic_target_expr,
            &state,
            1,
        ),
    );
    try std.testing.expectEqual(@as(usize, 0), state.witnesses.count());
    try std.testing.expectEqual(@as(u32, 0), fixture.theorem.next_dummy_id);
    try std.testing.expectEqual(@as(u32, 0), fixture.theorem.next_dummy_dep);
}

test "semantic search budget failure restores state" {
    var fixture = try SemanticStepFixture.init();
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

    try std.testing.expect(!try Testing.matchSymbolicToExprSemantic(
        &ctx,
        symbolic_mono,
        fixture.semantic_target_expr,
        &state,
        0,
    ));
    try std.testing.expectEqual(
        start_dummy_info_len,
        state.symbolic_dummy_infos.items.len,
    );
    try std.testing.expectEqual(start_witness_count, state.witnesses.count());
    try std.testing.expectEqual(@as(u32, 0), fixture.theorem.next_dummy_id);
    try std.testing.expectEqual(@as(u32, 0), fixture.theorem.next_dummy_dep);
}

test "semantic def exposure refuses witnesses that capture def arguments" {
    // The old target here required mono's hidden dummy `a` to be witnessed
    // by `g`, which occurs in the def's own argument instantiation `g o f` —
    // an unfolding MMB `UDummy` disjointness forbids (and `g` is not bound
    // besides). instantiateDefTowardExpr must return null rather than mint
    // an unverifiable witness.
    var fixture = try SemanticStepFixture.init();
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
        try ctx.instantiateDefTowardExpr(
            fixture.mono_expr,
            fixture.semantic_target_expr,
        ),
    );
}

test "semantic def exposure materializes witness toward rewrite target" {
    // Legal variant of the exposure: the hidden dummies are witnessed by
    // fresh theorem dummies (bound, distinct, absent from the def's args —
    // the same shape the @vars pool provides in production). The target's
    // rhs is one comp_assoc step away from the unfolded body, so only the
    // semantic tier can close it; the returned witness is the pre-rewrite
    // body instantiation.
    var fixture = try SemanticStepFixture.init();
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

    const witness = try ctx.instantiateDefTowardExpr(
        fixture.mono_expr,
        target,
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
