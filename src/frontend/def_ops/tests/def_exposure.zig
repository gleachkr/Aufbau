const std = @import("std");
const DefOps = @import("../../def_ops.zig");
const Fixtures = @import("./fixtures.zig");
const ExprId = @import("../../expr.zig").ExprId;
const Context = DefOps.Context;
const Testing = DefOps.Testing;
const AcuiExposureFixture = Fixtures.AcuiExposureFixture;
const WrappedAcuiDefFixture = Fixtures.WrappedAcuiDefFixture;
const QuantifiedAcuiDefFixture = Fixtures.QuantifiedAcuiDefFixture;

test "ACUI leaf exposure rewrites before matching the leaf" {
    var fixture = try AcuiExposureFixture.init(true, true);
    defer fixture.deinit();

    var ctx = Context.initWithRegistry(
        fixture.arena.allocator(),
        &fixture.theorem,
        &fixture.env,
        &fixture.registry,
    );
    defer ctx.deinit();

    const witness = try ctx.instantiateDefTowardAcuiItem(
        fixture.pre_ctx_expr,
        fixture.bound_item_expr,
        fixture.join_term_id,
        true,
    ) orelse return error.MissingWitness;

    try std.testing.expectEqual(fixture.expected_bound_witness, witness);
}

test "ACUI leaf exposure compares the body as it stands without rewriting" {
    // A bag compared without rewriting holds `box (hyp (u = x))` as it is:
    // `box_flat` must not turn the def's body into `emp , hyp (u = x)`
    // first, or the literal member is missed.
    var fixture = try AcuiExposureFixture.init(true, true);
    defer fixture.deinit();

    var ctx = Context.initWithRegistry(
        fixture.arena.allocator(),
        &fixture.theorem,
        &fixture.env,
        &fixture.registry,
    );
    defer ctx.deinit();

    const witness = try ctx.instantiateDefTowardAcuiItem(
        fixture.pre_ctx_expr,
        fixture.expected_bound_witness,
        fixture.join_term_id,
        false,
    ) orelse return error.MissingWitness;
    try std.testing.expectEqual(fixture.expected_bound_witness, witness);

    // Modulo rewriting the body is compared at its normal form, whose
    // members are `emp` and `hyp (u = x)`.
    try std.testing.expect(try ctx.instantiateDefTowardAcuiItem(
        fixture.pre_ctx_expr,
        fixture.bound_item_expr,
        fixture.join_term_id,
        true,
    ) != null);
}

test "ACUI exposure treats parenthesized dot-binders as bound" {
    // `(.x: obj)` and `{.x: obj}` both declare a bound hidden dummy (the
    // parser treats every dot-binder as bound, matching MMB `UDummy`
    // semantics), so a non-bound theorem arg can never witness it and the
    // exposure must refuse rather than fabricate an unsound unfolding.
    var fixture = try AcuiExposureFixture.init(false, false);
    defer fixture.deinit();

    var ctx = Context.initWithRegistry(
        fixture.arena.allocator(),
        &fixture.theorem,
        &fixture.env,
        &fixture.registry,
    );
    defer ctx.deinit();

    const witness = try ctx.instantiateDefTowardAcuiItem(
        fixture.pre_ctx_expr,
        fixture.free_item_expr,
        fixture.join_term_id,
        true,
    );

    try std.testing.expectEqual(@as(?ExprId, null), witness);
}

test "ACUI exposure keeps bound hidden witnesses strict" {
    var fixture = try AcuiExposureFixture.init(true, false);
    defer fixture.deinit();

    var ctx = Context.initWithRegistry(
        fixture.arena.allocator(),
        &fixture.theorem,
        &fixture.env,
        &fixture.registry,
    );
    defer ctx.deinit();

    const witness = try ctx.instantiateDefTowardAcuiItem(
        fixture.pre_ctx_expr,
        fixture.free_item_expr,
        fixture.join_term_id,
        true,
    );

    try std.testing.expectEqual(@as(?ExprId, null), witness);
}

test "def exposure matches wrapped ACUI witness" {
    var fixture = try WrappedAcuiDefFixture.init(false, true, true);
    defer fixture.deinit();

    var ctx = Context.initWithRegistry(
        fixture.arena.allocator(),
        &fixture.theorem,
        &fixture.env,
        &fixture.registry,
    );
    defer ctx.deinit();

    const start_dummy_id = fixture.theorem.next_dummy_id;
    const start_dummy_dep = fixture.theorem.next_dummy_dep;

    const witness = try ctx.unfoldDefToward(
        fixture.pre_ctx_expr,
        fixture.target_expr,
        true,
        null,
    ) orelse return error.MissingWitness;

    try std.testing.expectEqual(fixture.expected_witness, witness);
    try std.testing.expectEqual(start_dummy_id, fixture.theorem.next_dummy_id);
    try std.testing.expectEqual(
        start_dummy_dep,
        fixture.theorem.next_dummy_dep,
    );
}

test "def exposure matches wrapped full ACUI witness" {
    var fixture = try WrappedAcuiDefFixture.init(true, true, true);
    defer fixture.deinit();

    var ctx = Context.initWithRegistry(
        fixture.arena.allocator(),
        &fixture.theorem,
        &fixture.env,
        &fixture.registry,
    );
    defer ctx.deinit();

    const start_dummy_id = fixture.theorem.next_dummy_id;
    const start_dummy_dep = fixture.theorem.next_dummy_dep;

    const witness = try ctx.unfoldDefToward(
        fixture.pre_ctx_expr,
        fixture.target_expr,
        true,
        null,
    ) orelse return error.MissingWitness;

    try std.testing.expectEqual(fixture.expected_witness, witness);
    try std.testing.expectEqual(start_dummy_id, fixture.theorem.next_dummy_id);
    try std.testing.expectEqual(
        start_dummy_dep,
        fixture.theorem.next_dummy_dep,
    );
}

test "def exposure matches quantified wrapped ACUI witness" {
    var fixture = try QuantifiedAcuiDefFixture.init(false);
    defer fixture.deinit();

    var ctx = Context.initWithRegistry(
        fixture.arena.allocator(),
        &fixture.theorem,
        &fixture.env,
        &fixture.registry,
    );
    defer ctx.deinit();

    const start_dummy_id = fixture.theorem.next_dummy_id;
    const start_dummy_dep = fixture.theorem.next_dummy_dep;

    const witness = try ctx.unfoldDefToward(
        fixture.pre_ctx_expr,
        fixture.target_expr,
        true,
        null,
    ) orelse return error.MissingWitness;

    try std.testing.expectEqual(fixture.expected_witness, witness);
    try std.testing.expectEqual(start_dummy_id, fixture.theorem.next_dummy_id);
    try std.testing.expectEqual(
        start_dummy_dep,
        fixture.theorem.next_dummy_dep,
    );
}

test "def exposure matches quantified wrapped full ACUI witness" {
    var fixture = try QuantifiedAcuiDefFixture.init(true);
    defer fixture.deinit();

    var ctx = Context.initWithRegistry(
        fixture.arena.allocator(),
        &fixture.theorem,
        &fixture.env,
        &fixture.registry,
    );
    defer ctx.deinit();

    const start_dummy_id = fixture.theorem.next_dummy_id;
    const start_dummy_dep = fixture.theorem.next_dummy_dep;

    const witness = try ctx.unfoldDefToward(
        fixture.pre_ctx_expr,
        fixture.target_expr,
        true,
        null,
    ) orelse return error.MissingWitness;

    try std.testing.expectEqual(fixture.expected_witness, witness);
    try std.testing.expectEqual(start_dummy_id, fixture.theorem.next_dummy_id);
    try std.testing.expectEqual(
        start_dummy_dep,
        fixture.theorem.next_dummy_dep,
    );
}

test "def exposure keeps wrapped bound witnesses unresolved" {
    var fixture = try WrappedAcuiDefFixture.init(false, true, false);
    defer fixture.deinit();

    var ctx = Context.initWithRegistry(
        fixture.arena.allocator(),
        &fixture.theorem,
        &fixture.env,
        &fixture.registry,
    );
    defer ctx.deinit();

    const start_dummy_id = fixture.theorem.next_dummy_id;
    const start_dummy_dep = fixture.theorem.next_dummy_dep;

    const witness = try ctx.unfoldDefToward(
        fixture.pre_ctx_expr,
        fixture.target_expr,
        true,
        null,
    );

    try std.testing.expectEqual(@as(?ExprId, null), witness);
    try std.testing.expectEqual(start_dummy_id, fixture.theorem.next_dummy_id);
    try std.testing.expectEqual(
        start_dummy_dep,
        fixture.theorem.next_dummy_dep,
    );
}

const RecordingProvider = struct {
    expr_id: ExprId,
    calls: usize = 0,

    fn provider(self: *RecordingProvider) DefOps.HiddenWitnessProvider {
        return .{
            .context = self,
            .provideFn = provide,
        };
    }

    fn provide(
        raw_context: *anyopaque,
        allocator: std.mem.Allocator,
        roots: []const DefOps.UnresolvedDummyRoot,
        extra_used_deps: u55,
    ) anyerror!?[]DefOps.MaterializedDummyAssignment {
        _ = extra_used_deps;
        const self: *RecordingProvider =
            @ptrCast(@alignCast(raw_context));
        self.calls += 1;
        const assignments = try allocator.alloc(
            DefOps.MaterializedDummyAssignment,
            roots.len,
        );
        for (roots, 0..) |root, idx| {
            assignments[idx] = .{
                .root_slot = root.root_slot,
                .expr_id = self.expr_id,
            };
        }
        return assignments;
    }
};

test "provider materializes a hidden witness the match leaves open" {
    // Matching pre_ctx's expansion against pre_ctx2's aligns the two hidden
    // dummies without pinning either to a concrete witness, so the match
    // succeeds with an unresolved root — the shape that consults the
    // hidden-witness provider (the @vars pool in production). The provided
    // materialization is not remembered: a query without the provider keeps
    // returning null, and each query with it asks the provider again.
    var fixture = try WrappedAcuiDefFixture.init(false, true, false);
    defer fixture.deinit();

    var ctx = Context.initWithRegistry(
        fixture.arena.allocator(),
        &fixture.theorem,
        &fixture.env,
        &fixture.registry,
    );
    defer ctx.deinit();

    var provider_state = RecordingProvider{
        .expr_id = fixture.theorem.theorem_vars.items[0],
    };
    try std.testing.expectEqual(
        @as(?ExprId, null),
        try ctx.unfoldDefToward(
            fixture.pre_ctx_expr,
            fixture.pre_ctx2_expr,
            true,
            null,
        ),
    );
    try std.testing.expectEqual(@as(usize, 0), provider_state.calls);

    const witness = try ctx.unfoldDefToward(
        fixture.pre_ctx_expr,
        fixture.pre_ctx2_expr,
        true,
        provider_state.provider(),
    ) orelse return error.MissingWitness;
    try std.testing.expectEqual(fixture.expected_witness, witness);
    try std.testing.expectEqual(@as(usize, 1), provider_state.calls);

    try std.testing.expectEqual(
        @as(?ExprId, null),
        try ctx.unfoldDefToward(
            fixture.pre_ctx_expr,
            fixture.pre_ctx2_expr,
            true,
            null,
        ),
    );
    _ = try ctx.unfoldDefToward(
        fixture.pre_ctx_expr,
        fixture.pre_ctx2_expr,
        true,
        provider_state.provider(),
    );
    try std.testing.expectEqual(@as(usize, 2), provider_state.calls);
}
