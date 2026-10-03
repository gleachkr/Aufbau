const helpers = @import("./helpers.zig");
const std = helpers.std;
const types = helpers.types;
const source = helpers.source;
const ProofScript = helpers.ProofScript;
const apply = helpers.apply;
const exact = helpers.exact;
const tunables = helpers.tunables;
const miss_mod = helpers.miss;
const generate = helpers.generate;
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
    // Raising depth spends more of the shared budget, so the budget grows
    // with it (the default ~6.3s rounds up to 7 units).
    try std.testing.expect(
        std.mem.indexOf(u8, detail, "Try 'auto? (depth: 3, budget: 14)'") != null,
    );
    // The retry edit rewrites the placeholder's own parameters.
    const retry = narrowed.retry orelse return error.MissingRetry;
    try std.testing.expectEqualStrings("Retry with depth: 3, budget: 14", retry.title);
    try std.testing.expectEqualStrings("auto? (depth: 3, budget: 14)", retry.replacement);
}

test "auto? retry keeps the parameters it does not raise" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    const proof_src =
        \\t
        \\----
        \\l1: $ R $ by auto? (fuel: 4096, depth: 1)
    ;
    var narrowed = try tunableChainSuggestions(
        &arena,
        proof_src,
        .{ .generate = .{ .enabled = true }, .status_detail = true },
    );
    defer narrowed.deinit();
    try std.testing.expectEqual(types.SearchStatus.miss, narrowed.status);
    const retry = narrowed.retry orelse return error.MissingRetry;
    try std.testing.expectEqualStrings(
        "auto? (fuel: 4096, depth: 3, budget: 14)",
        retry.replacement,
    );
    // The edit covers the keyword through the closing parenthesis.
    try std.testing.expectEqualStrings(
        "auto? (fuel: 4096, depth: 1)",
        proof_src[retry.replace_span.start..retry.replace_span.end],
    );
}

test "auto? miss detail reports the exhausted space" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var counters = types.SearchCounters{};
    var miss = try tunableChainSuggestions(&arena,
        \\ts
        \\----
        \\l1: $ S $ by auto? (depth: 3)
    , .{
        .generate = .{ .enabled = true },
        .status_detail = true,
        .counters = &counters,
    });
    defer miss.deinit();
    try std.testing.expectEqual(types.SearchStatus.miss, miss.status);
    const detail = miss.status_detail orelse return error.MissingStatusDetail;
    try std.testing.expect(
        std.mem.indexOf(u8, detail, "no proof found within depth 3") != null,
    );
    // The core searched every depth in full, and nothing cut it short.
    try std.testing.expectEqual(@as(usize, 3), counters.gen_core_depth_done);
    try std.testing.expectEqual(@as(usize, 0), counters.gen_node_capped_passes);
    try std.testing.expect(!counters.gen_budget_exhausted);

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
    // exact? takes no parameters, so there is nothing to retry with.
    try std.testing.expectEqual(@as(?types.SourceSuggestion, null), miss.retry);
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
    // Fuel doubles, and the budget grows with it.
    try std.testing.expect(std.mem.indexOf(u8, detail, "fuel: 2") != null);
    try std.testing.expect(std.mem.indexOf(u8, detail, "budget: 14)'") != null);
    const retry = starved.retry orelse return error.MissingRetry;
    try std.testing.expect(std.mem.indexOf(u8, retry.replacement, "fuel: 2") != null);
}

test "auto? node-cap truncation is reported as truncation with a nodes hint" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    // `nodes: 1` lets each pass expand a single subgoal, too few for the
    // two-level chain. No budget or fuel runs out, so before the node cap was
    // reported the miss read as an exhausted search space.
    var counters = types.SearchCounters{};
    var capped = try tunableChainSuggestions(&arena,
        \\t
        \\----
        \\l1: $ R $ by auto? (nodes: 1)
    , .{
        .generate = .{ .enabled = true },
        .status_detail = true,
        .counters = &counters,
    });
    defer capped.deinit();
    try std.testing.expectEqual(
        types.SearchStatus.budget_exhausted,
        capped.status,
    );
    // Depth 1 expands a single subgoal, so the cap first stops a pass at
    // depth 2. Only depth 1 counts as searched in full, and no budget ran
    // out.
    try std.testing.expect(counters.gen_node_capped_passes > 0);
    try std.testing.expectEqual(@as(usize, 1), counters.gen_core_depth_done);
    try std.testing.expect(!counters.gen_budget_exhausted);
    const detail = capped.status_detail orelse
        return error.MissingStatusDetail;
    try std.testing.expect(
        std.mem.indexOf(u8, detail, "limit of 1 subgoals per pass") != null,
    );
    try std.testing.expect(std.mem.indexOf(u8, detail, "nodes: 2") != null);
    try std.testing.expect(std.mem.indexOf(u8, detail, "budget: 14)'") != null);
    try std.testing.expect(
        std.mem.indexOf(u8, detail, "search space was exhausted") == null,
    );
}

fn budgetDetail(counters: types.SearchCounters) ![]const u8 {
    const gen = types.GenerateOptions{
        .max_depth = 6,
        .global_budget = 6 * tunables.ticks_per_budget_unit,
    };
    return (try source.buildStatusDetail(
        std.testing.allocator,
        "auto?",
        true,
        .budget_exhausted,
        &counters,
        gen,
    )) orelse error.MissingStatusDetail;
}

test "auto? budget truncation names every limit that was hit" {
    // The budget ran out in the core at depth 4, after node caps and a
    // retired phase. Each limit is named, and each one that was hit is
    // raised together with the budget; depth is not, since the core never
    // got near the depth limit.
    const detail = try budgetDetail(.{
        .gen_budget_exhausted = true,
        .phase_fuel_exhausted = true,
        .gen_node_capped_passes = 3,
        .gen_last_phase = 1,
        .gen_last_depth = 4,
        .gen_core_depth_done = 2,
    });
    defer std.testing.allocator.free(detail);
    const where = try std.fmt.allocPrint(
        std.testing.allocator,
        "ran out during {s} at depth 4 of 6",
        .{generate.phaseName(1)},
    );
    defer std.testing.allocator.free(where);
    try std.testing.expect(std.mem.indexOf(u8, detail, where) != null);
    try std.testing.expect(std.mem.indexOf(
        u8,
        detail,
        "the per-call work budget (~6s of work)",
    ) != null);
    try std.testing.expect(std.mem.indexOf(
        u8,
        detail,
        "the limit of 256 subgoals per pass was reached in 3 passes",
    ) != null);
    try std.testing.expect(std.mem.indexOf(u8, detail, "ran out of fuel (4096") != null);
    try std.testing.expect(std.mem.indexOf(
        u8,
        detail,
        "try 'auto? (nodes: 512, fuel: 8192, budget: 12)'",
    ) != null);
    try std.testing.expect(std.mem.indexOf(u8, detail, "depth: 8") == null);
}

test "auto? budget truncation past every core depth suggests more depth" {
    // `add_suc_right`'s shape: the core searched depths 1–6 in full, then
    // the budget ran out in the constrained-MP tail, where a pass also hit
    // the node cap.
    const detail = try budgetDetail(.{
        .gen_budget_exhausted = true,
        .gen_node_capped_passes = 1,
        .gen_last_phase = 5,
        .gen_last_depth = 2,
        .gen_core_depth_done = 6,
    });
    defer std.testing.allocator.free(detail);
    try std.testing.expect(std.mem.indexOf(
        u8,
        detail,
        "Every depth below 6 was searched",
    ) != null);
    try std.testing.expect(std.mem.indexOf(
        u8,
        detail,
        "try 'auto? (depth: 8, nodes: 512, budget: 12)'",
    ) != null);
}

test "auto? budget truncation before the depth limit suggests only budget" {
    const detail = try budgetDetail(.{
        .gen_budget_exhausted = true,
        .gen_last_phase = 1,
        .gen_last_depth = 4,
        .gen_core_depth_done = 3,
    });
    defer std.testing.allocator.free(detail);
    try std.testing.expect(std.mem.indexOf(u8, detail, "try 'auto? (budget: 12)'") != null);
    try std.testing.expect(std.mem.indexOf(u8, detail, "depth: 8") == null);
}

test "miss retry is null when no parameter can help" {
    const gen = types.GenerateOptions{};
    // The stack guard protects the process stack; no parameter raises it.
    try std.testing.expectEqual(@as(?miss_mod.Retry, null), miss_mod.retryFor(
        miss_mod.MissReport.of(&.{ .stack_guard_exhausted = true, .gen_last_phase = 1 }),
        gen,
    ));
    // Generation never ran (an exact?-style miss).
    try std.testing.expectEqual(@as(?miss_mod.Retry, null), miss_mod.retryFor(
        miss_mod.MissReport.of(&.{ .gen_budget_exhausted = true }),
        gen,
    ));
    // A clean miss already at the depth maximum.
    try std.testing.expectEqual(@as(?miss_mod.Retry, null), miss_mod.retryFor(
        miss_mod.MissReport.of(&.{ .gen_last_phase = 5, .gen_core_depth_done = 64 }),
        .{ .max_depth = tunables.max_depth_value },
    ));
    // Only forward saturation was cut short, and no auto? parameter
    // bounds it.
    try std.testing.expectEqual(@as(?miss_mod.Retry, null), miss_mod.retryFor(
        miss_mod.MissReport.of(&.{ .forward_saturation_exhausted = true, .gen_last_phase = 5 }),
        gen,
    ));
}

test "miss retry leaves an uncapped budget uncapped" {
    const retry = miss_mod.retryFor(
        miss_mod.MissReport.of(&.{ .gen_node_capped_passes = 1, .gen_last_phase = 5 }),
        .{ .global_budget = null },
    ) orelse return error.MissingRetry;
    try std.testing.expectEqual(miss_mod.Retry{ .nodes = 512 }, retry);
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
