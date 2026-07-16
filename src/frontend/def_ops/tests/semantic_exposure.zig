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

test "semantic ACUI leaf exposure rewrites before matching the leaf" {
    var fixture = try SemanticAcuiExposureFixture.init(true, true);
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
    ) orelse return error.MissingWitness;

    try std.testing.expectEqual(fixture.expected_bound_witness, witness);
}

test "semantic ACUI exposure allows theorem args for non-bound hidden witnesses" {
    var fixture = try SemanticAcuiExposureFixture.init(false, false);
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
    );

    try std.testing.expectEqual(fixture.expected_free_witness, witness);
}

test "semantic ACUI exposure keeps bound hidden witnesses strict" {
    var fixture = try SemanticAcuiExposureFixture.init(true, false);
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
    );

    try std.testing.expectEqual(@as(?ExprId, null), witness);
}

test "semantic def exposure matches wrapped ACUI witness" {
    var fixture = try SemanticWrappedAcuiDefFixture.init(false, true, true);
    defer fixture.deinit();

    var ctx = Context.initWithRegistry(
        fixture.arena.allocator(),
        &fixture.theorem,
        &fixture.env,
        &fixture.registry,
    );
    defer ctx.deinit();

    const witness = try ctx.instantiateDefTowardExpr(
        fixture.pre_ctx_expr,
        fixture.target_expr,
    ) orelse return error.MissingWitness;

    try std.testing.expectEqual(fixture.expected_witness, witness);
    try std.testing.expectEqual(@as(u32, 0), fixture.theorem.next_dummy_id);
    try std.testing.expectEqual(@as(u32, 0), fixture.theorem.next_dummy_dep);
}

test "semantic def exposure matches wrapped full ACUI witness" {
    var fixture = try SemanticWrappedAcuiDefFixture.init(true, true, true);
    defer fixture.deinit();

    var ctx = Context.initWithRegistry(
        fixture.arena.allocator(),
        &fixture.theorem,
        &fixture.env,
        &fixture.registry,
    );
    defer ctx.deinit();

    const witness = try ctx.instantiateDefTowardExpr(
        fixture.pre_ctx_expr,
        fixture.target_expr,
    ) orelse return error.MissingWitness;

    try std.testing.expectEqual(fixture.expected_witness, witness);
    try std.testing.expectEqual(@as(u32, 0), fixture.theorem.next_dummy_id);
    try std.testing.expectEqual(@as(u32, 0), fixture.theorem.next_dummy_dep);
}

test "semantic def exposure matches quantified wrapped ACUI witness" {
    var fixture = try SemanticQuantifiedAcuiDefFixture.init(false);
    defer fixture.deinit();

    var ctx = Context.initWithRegistry(
        fixture.arena.allocator(),
        &fixture.theorem,
        &fixture.env,
        &fixture.registry,
    );
    defer ctx.deinit();

    const witness = try ctx.instantiateDefTowardExpr(
        fixture.pre_ctx_expr,
        fixture.target_expr,
    ) orelse return error.MissingWitness;

    try std.testing.expectEqual(fixture.expected_witness, witness);
    try std.testing.expectEqual(@as(u32, 0), fixture.theorem.next_dummy_id);
    try std.testing.expectEqual(@as(u32, 0), fixture.theorem.next_dummy_dep);
}

test "semantic def exposure matches quantified wrapped full ACUI witness" {
    var fixture = try SemanticQuantifiedAcuiDefFixture.init(true);
    defer fixture.deinit();

    var ctx = Context.initWithRegistry(
        fixture.arena.allocator(),
        &fixture.theorem,
        &fixture.env,
        &fixture.registry,
    );
    defer ctx.deinit();

    const witness = try ctx.instantiateDefTowardExpr(
        fixture.pre_ctx_expr,
        fixture.target_expr,
    ) orelse return error.MissingWitness;

    try std.testing.expectEqual(fixture.expected_witness, witness);
    try std.testing.expectEqual(@as(u32, 0), fixture.theorem.next_dummy_id);
    try std.testing.expectEqual(@as(u32, 0), fixture.theorem.next_dummy_dep);
}

test "semantic def exposure keeps wrapped bound witnesses unresolved" {
    var fixture = try SemanticWrappedAcuiDefFixture.init(false, true, false);
    defer fixture.deinit();

    var ctx = Context.initWithRegistry(
        fixture.arena.allocator(),
        &fixture.theorem,
        &fixture.env,
        &fixture.registry,
    );
    defer ctx.deinit();

    const witness = try ctx.instantiateDefTowardExpr(
        fixture.pre_ctx_expr,
        fixture.target_expr,
    );

    try std.testing.expectEqual(@as(?ExprId, null), witness);
    try std.testing.expectEqual(@as(u32, 0), fixture.theorem.next_dummy_id);
    try std.testing.expectEqual(@as(u32, 0), fixture.theorem.next_dummy_dep);
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

test "provider materializes semantic hidden witness without caching it" {
    var fixture = try SemanticWrappedAcuiDefFixture.init(false, true, false);
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
        try ctx.instantiateDefTowardExpr(
            fixture.pre_ctx_expr,
            fixture.target_expr,
        ),
    );
    try std.testing.expectEqual(@as(usize, 0), provider_state.calls);
    const cache_count = fixture.theorem.instantiate_def_cache.count();

    const witness = try ctx.instantiateDefTowardExprWithProvider(
        fixture.pre_ctx_expr,
        fixture.target_expr,
        provider_state.provider(),
    ) orelse return error.MissingWitness;
    try std.testing.expectEqual(fixture.expected_witness, witness);
    try std.testing.expectEqual(@as(usize, 1), provider_state.calls);
    try std.testing.expectEqual(
        cache_count,
        fixture.theorem.instantiate_def_cache.count(),
    );

    try std.testing.expectEqual(
        @as(?ExprId, null),
        try ctx.instantiateDefTowardExpr(
            fixture.pre_ctx_expr,
            fixture.target_expr,
        ),
    );
    _ = try ctx.instantiateDefTowardExprWithProvider(
        fixture.pre_ctx_expr,
        fixture.target_expr,
        provider_state.provider(),
    );
    try std.testing.expectEqual(@as(usize, 2), provider_state.calls);
}
