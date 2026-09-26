const helpers = @import("./helpers.zig");
const std = helpers.std;
const types = helpers.types;
const source = helpers.source;
const ProofScript = helpers.ProofScript;
const apply = helpers.apply;
const exact = helpers.exact;
const tunables = helpers.tunables;
const tunable_chain_mm0 = helpers.tunable_chain_mm0;

fn testParam(name: []const u8, value: u64) ProofScript.SearchParam {
    const zero = ProofScript.Span{ .start = 0, .end = 0 };
    return .{
        .name = name,
        .name_span = zero,
        .value = value,
        .value_span = zero,
        .span = zero,
    };
}

test "search tunables apply valid params and skip invalid ones" {
    var gen = types.GenerateOptions{};
    const defaults = types.GenerateOptions{};
    tunables.applySearchParams(&gen, &.{
        testParam("depth", 8),
        testParam("fuel", 8192),
        testParam("nodes", 0), // below range: skipped
        testParam("unknown", 3), // unknown: skipped
        testParam("budget", 12),
    });
    try std.testing.expectEqual(@as(usize, 8), gen.max_depth);
    try std.testing.expectEqual(@as(usize, 8192), gen.fuel);
    try std.testing.expectEqual(defaults.max_nodes, gen.max_nodes);
    try std.testing.expectEqual(
        @as(?u64, 12 * tunables.ticks_per_budget_unit),
        gen.global_budget,
    );

    // `budget: 0` disables the per-call cap entirely.
    tunables.applySearchParams(&gen, &.{testParam("budget", 0)});
    try std.testing.expectEqual(@as(?u64, null), gen.global_budget);
}

test "search tunables validate names, values, and placeholder kind" {
    const allocator = std.testing.allocator;

    const issues = try tunables.validateSearchParams(allocator, .auto, &.{
        testParam("depth", 8), // valid: no issue
        testParam("depht", 8), // typo
        testParam("nodes", 0), // out of range
    });
    defer {
        for (issues) |issue| allocator.free(issue.message);
        allocator.free(issues);
    }
    try std.testing.expectEqual(@as(usize, 2), issues.len);
    try std.testing.expect(
        std.mem.indexOf(
            u8,
            issues[0].message,
            "unknown auto? parameter 'depht'",
        ) != null,
    );
    try std.testing.expect(
        std.mem.indexOf(
            u8,
            issues[0].message,
            "depth, nodes, fuel, budget",
        ) != null,
    );
    try std.testing.expect(
        std.mem.indexOf(u8, issues[1].message, "'nodes' must be between") != null,
    );

    // Any parameter on an exact?/apply? placeholder is rejected.
    const not_auto = try tunables.validateSearchParams(allocator, .exact, &.{
        testParam("depth", 8),
    });
    defer {
        for (not_auto) |issue| allocator.free(issue.message);
        allocator.free(not_auto);
    }
    try std.testing.expectEqual(@as(usize, 1), not_auto.len);
    try std.testing.expect(
        std.mem.indexOf(
            u8,
            not_auto[0].message,
            "only apply to auto? and conversion?",
        ) != null,
    );

    // conversion? accepts its own parameter set.
    const conv = try tunables.validateSearchParams(allocator, .conversion, &.{
        testParam("iters", 32), // valid: no issue
        testParam("depth", 8), // auto?-only name
    });
    defer {
        for (conv) |issue| allocator.free(issue.message);
        allocator.free(conv);
    }
    try std.testing.expectEqual(@as(usize, 1), conv.len);
    try std.testing.expect(
        std.mem.indexOf(
            u8,
            conv[0].message,
            "unknown conversion? parameter 'depth'",
        ) != null,
    );
    try std.testing.expect(
        std.mem.indexOf(u8, conv[0].message, "iters, nodes") != null,
    );
}

fn tunableChainSuggestions(
    arena: *std.heap.ArenaAllocator,
    proof_src: []const u8,
    options: types.SourceSuggestionOptions,
) !types.SourceSuggestions {
    const offset = std.mem.indexOf(u8, proof_src, "auto?") orelse
        std.mem.indexOf(u8, proof_src, "exact?") orelse
        return error.MissingNeedle;
    return source.suggestionsAtSourceOffset(
        arena.allocator(),
        tunable_chain_mm0,
        proof_src,
        offset,
        options,
    );
}

test "auto? per-call depth parameter narrows one search" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    // Default depth finds the two-level chain.
    var found = try tunableChainSuggestions(&arena,
        \\t
        \\----
        \\l1: $ R $ by auto?
    , .{ .generate = .{ .enabled = true } });
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);

    // `(depth: 1)` cuts generation below the chain: the same goal misses,
    // and the detail names the effective depth and suggests raising it.
    var narrowed = try tunableChainSuggestions(&arena,
        \\t
        \\----
        \\l1: $ R $ by auto? (depth: 1)
    , .{ .generate = .{ .enabled = true }, .status_detail = true });
    defer narrowed.deinit();
    try std.testing.expectEqual(@as(usize, 0), narrowed.items.len);
    try std.testing.expectEqual(types.SearchStatus.miss, narrowed.status);
    const detail = narrowed.status_detail orelse
        return error.MissingStatusDetail;
    try std.testing.expect(
        std.mem.indexOf(u8, detail, "no proof found within depth 1") != null,
    );
    try std.testing.expect(
        std.mem.indexOf(u8, detail, "auto? (depth: 3)") != null,
    );
}

test "auto? miss detail reports the exhausted space" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var miss = try tunableChainSuggestions(&arena,
        \\ts
        \\----
        \\l1: $ S $ by auto?
    , .{ .generate = .{ .enabled = true }, .status_detail = true });
    defer miss.deinit();
    try std.testing.expectEqual(types.SearchStatus.miss, miss.status);
    const detail = miss.status_detail orelse return error.MissingStatusDetail;
    try std.testing.expect(
        std.mem.indexOf(u8, detail, "no proof found within depth 6") != null,
    );

    // The detail is opt-in: the same miss without the flag carries none
    // (the bench/programmatic path stays untouched).
    var plain = try tunableChainSuggestions(&arena,
        \\ts
        \\----
        \\l1: $ S $ by auto?
    , .{ .generate = .{ .enabled = true } });
    defer plain.deinit();
    try std.testing.expectEqual(types.SearchStatus.miss, plain.status);
    try std.testing.expectEqual(@as(?[]const u8, null), plain.status_detail);
}

test "exact? miss detail reports pool coverage and suggests auto?" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var miss = try tunableChainSuggestions(&arena,
        \\ts
        \\----
        \\l1: $ S $ by exact?
    , .{ .status_detail = true });
    defer miss.deinit();
    try std.testing.expectEqual(types.SearchStatus.miss, miss.status);
    const detail = miss.status_detail orelse return error.MissingStatusDetail;
    try std.testing.expect(
        std.mem.indexOf(
            u8,
            detail,
            "no rule application closes this goal",
        ) != null,
    );
    try std.testing.expect(
        std.mem.indexOf(u8, detail, "auto? can additionally synthesize") != null,
    );
}

test "auto? fuel exhaustion is reported as truncation with a fuel hint" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    // `fuel: 1` starves every phase before the two-level chain assembles;
    // the miss must surface as truncation (not a definitive miss), name the
    // fuel bound, and suggest raising it.
    var starved = try tunableChainSuggestions(&arena,
        \\t
        \\----
        \\l1: $ R $ by auto? (fuel: 1)
    , .{ .generate = .{ .enabled = true }, .status_detail = true });
    defer starved.deinit();
    try std.testing.expectEqual(
        types.SearchStatus.budget_exhausted,
        starved.status,
    );
    const detail = starved.status_detail orelse
        return error.MissingStatusDetail;
    try std.testing.expect(
        std.mem.indexOf(u8, detail, "ran out of fuel") != null,
    );
    try std.testing.expect(
        std.mem.indexOf(u8, detail, "auto? (fuel: 2)") != null,
    );
}

test "auto? node-cap truncation is reported as truncation with a nodes hint" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    // `nodes: 1` lets each pass expand a single subgoal, too few for the
    // two-level chain. No budget or fuel runs out, so before the node cap was
    // reported the miss read as an exhausted search space.
    var capped = try tunableChainSuggestions(&arena,
        \\t
        \\----
        \\l1: $ R $ by auto? (nodes: 1)
    , .{ .generate = .{ .enabled = true }, .status_detail = true });
    defer capped.deinit();
    try std.testing.expectEqual(
        types.SearchStatus.budget_exhausted,
        capped.status,
    );
    const detail = capped.status_detail orelse
        return error.MissingStatusDetail;
    try std.testing.expect(
        std.mem.indexOf(u8, detail, "limit of 1 subgoals per pass") != null,
    );
    try std.testing.expect(
        std.mem.indexOf(u8, detail, "auto? (nodes: 2)") != null,
    );
    try std.testing.expect(
        std.mem.indexOf(u8, detail, "search space was exhausted") == null,
    );
}

test "auto? budget truncation does not claim node-capped depths were searched" {
    // Depth 3 was node-capped, so `gen_core_depth_done` stops at 2 and the
    // budget message must not say every depth up to the limit was searched.
    const gen = types.GenerateOptions{
        .global_budget = 6 * tunables.ticks_per_budget_unit,
    };
    const counters = types.SearchCounters{
        .gen_budget_exhausted = true,
        .gen_node_capped_passes = 1,
        .gen_last_phase = 1,
        .gen_last_depth = 4,
        .gen_core_depth_done = 2,
    };
    const detail = (try source.buildStatusDetail(
        std.testing.allocator,
        "auto?",
        true,
        .budget_exhausted,
        &counters,
        gen,
    )).?;
    defer std.testing.allocator.free(detail);
    try std.testing.expect(std.mem.indexOf(u8, detail, "every depth up to") == null);
    try std.testing.expect(std.mem.indexOf(u8, detail, "auto? (budget: 12)") != null);
}

test "auto? budget truncation past every core depth suggests more depth" {
    // `add_suc_right`'s shape: the core phases searched depths 1–6 clean,
    // then the budget died in the constrained-MP tail, which restarts at
    // depth 1. The detail must lead with depth, and must not present the
    // tail's depth as how far the search got.
    const gen = types.GenerateOptions{
        .global_budget = 6 * tunables.ticks_per_budget_unit,
    };
    const counters = types.SearchCounters{
        .gen_budget_exhausted = true,
        .gen_last_phase = 5,
        .gen_last_depth = 2,
        .gen_core_depth_done = 6,
    };
    const detail = (try source.buildStatusDetail(
        std.testing.allocator,
        "auto?",
        true,
        .budget_exhausted,
        &counters,
        gen,
    )).?;
    defer std.testing.allocator.free(detail);
    try std.testing.expect(std.mem.indexOf(
        u8,
        detail,
        "every depth up to 6 was searched",
    ) != null);
    try std.testing.expect(std.mem.indexOf(
        u8,
        detail,
        "constrained modus ponens (a retry pass) at depth 2 of 6",
    ) != null);
    try std.testing.expect(std.mem.indexOf(u8, detail, "auto? (depth: 8)") != null);
    try std.testing.expect(std.mem.indexOf(u8, detail, "auto? (budget: 12)") != null);
}

test "auto? budget truncation before the depth limit suggests only budget" {
    // The budget died in the core at depth 4 with depth 3 the deepest clean
    // one: more depth cannot help, so the detail keeps the budget advice.
    const gen = types.GenerateOptions{
        .global_budget = 6 * tunables.ticks_per_budget_unit,
    };
    const counters = types.SearchCounters{
        .gen_budget_exhausted = true,
        .gen_last_phase = 1,
        .gen_last_depth = 4,
        .gen_core_depth_done = 3,
    };
    const detail = (try source.buildStatusDetail(
        std.testing.allocator,
        "auto?",
        true,
        .budget_exhausted,
        &counters,
        gen,
    )).?;
    defer std.testing.allocator.free(detail);
    try std.testing.expect(std.mem.indexOf(
        u8,
        detail,
        "stopped by the per-call work budget (~6s of work) during " ++
            "non-splitting generation at depth 4 of 6",
    ) != null);
    try std.testing.expect(std.mem.indexOf(u8, detail, "auto? (budget: 12)") != null);
    try std.testing.expect(std.mem.indexOf(u8, detail, "depth: 8") == null);
}

test "searchPlaceholders carries parsed search params" {
    const proof_src =
        \\t
        \\----
        \\l1: $ R $ by auto? (depth: 8)
    ;
    const placeholders = try source.searchPlaceholders(
        std.testing.allocator,
        proof_src,
    );
    defer {
        for (placeholders) |placeholder| {
            std.testing.allocator.free(placeholder.params);
        }
        std.testing.allocator.free(placeholders);
    }
    try std.testing.expectEqual(@as(usize, 1), placeholders.len);
    try std.testing.expectEqual(@as(usize, 1), placeholders[0].params.len);
    try std.testing.expectEqualStrings(
        "depth",
        placeholders[0].params[0].name,
    );
    try std.testing.expectEqual(@as(u64, 8), placeholders[0].params[0].value);
}

// --- conversion? end-to-end ---------------------------------------------
