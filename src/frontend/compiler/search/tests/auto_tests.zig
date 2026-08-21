const helpers = @import("./helpers.zig");
const std = helpers.std;
const types = helpers.types;
const source = helpers.source;
const prune = helpers.prune;
const def_match = helpers.def_match;
const acui = helpers.acui;
const TemplateExpr = helpers.TemplateExpr;
const ExprId = helpers.ExprId;
const TheoremContext = helpers.TheoremContext;
const CompilerContext = helpers.CompilerContext;
const Check = helpers.Check;
const DiagnosticSink = helpers.DiagnosticSink;
const Goal = helpers.Goal;
const Context = helpers.Context;
const apply = helpers.apply;
const exact = helpers.exact;
const tryCandidate = helpers.tryCandidate;
const fixtureFor = helpers.fixtureFor;
const parseGoal = helpers.parseGoal;
const readProofCase = helpers.readProofCase;
const expectTimingCounter = helpers.expectTimingCounter;
const ContextHarness = helpers.ContextHarness;
const auto_chain_mm0 = helpers.auto_chain_mm0;
const auto_inline_mm0 = helpers.auto_inline_mm0;
const GeneratedConclusionHookCtx = helpers.GeneratedConclusionHookCtx;

fn autoChainSuggestions(
    arena: *std.heap.ArenaAllocator,
    proof_src: []const u8,
    needle: []const u8,
    options: types.SourceSuggestionOptions,
) !types.SourceSuggestions {
    const offset = std.mem.indexOf(u8, proof_src, needle) orelse
        return error.MissingNeedle;
    return source.suggestionsAtSourceOffset(
        arena.allocator(),
        auto_chain_mm0,
        proof_src,
        offset,
        options,
    );
}

test "auto generates a depth-1 inline chain" {
    const proof_src =
        \\t
        \\----
        \\l1: $ Q $ by auto?
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    var suggestions = try autoChainSuggestions(&arena, proof_src, "auto?", .{
        .counters = &counters,
        .generate = .{ .enabled = true },
    });
    defer suggestions.deinit();

    var found = false;
    for (suggestions.items) |item| {
        if (std.mem.eql(u8, item.replacement, "pq [p []]")) found = true;
    }
    try std.testing.expect(found);
    try std.testing.expect(counters.generated_chain_attempts > 0);
}

fn autoInlineSuggestions(
    arena: *std.heap.ArenaAllocator,
    proof_src: []const u8,
    needle: []const u8,
    options: types.SourceSuggestionOptions,
) !types.SourceSuggestions {
    const offset = std.mem.indexOf(u8, proof_src, needle) orelse
        return error.MissingNeedle;
    return source.suggestionsAtSourceOffset(
        arena.allocator(),
        auto_inline_mm0,
        proof_src,
        offset,
        options,
    );
}

test "auto generates a depth-1 chain inside a slot" {
    // The `auto?` fills `qr`'s only hypothesis (goal `Q`). No single rule proves
    // `Q` over the empty pool, so the slot must generate `pq [p []]`, yielding a
    // whole line of `qr [pq [p []]]`.
    const proof_src =
        \\t
        \\----
        \\l1: $ R $ by qr [auto?]
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    var suggestions = try autoInlineSuggestions(&arena, proof_src, "auto?", .{
        .counters = &counters,
        .generate = .{ .enabled = true },
    });
    defer suggestions.deinit();

    var found = false;
    for (suggestions.items) |item| {
        if (std.mem.eql(u8, item.replacement, "pq [p []]")) found = true;
    }
    try std.testing.expect(found);
    // The slot span is what gets replaced, not the whole line.
    try std.testing.expect(suggestions.target_span != null);
    const auto_offset = std.mem.indexOf(u8, proof_src, "auto?").?;
    try std.testing.expect(suggestions.target_span.?.start <= auto_offset);
    try std.testing.expect(suggestions.target_span.?.end >= auto_offset);
    // Generation actually fired (this is not a plain direct match).
    try std.testing.expect(counters.generated_chain_attempts > 0);
}

test "inline auto still resolves a slot from a direct ref without generating" {
    // Here the slot goal `P` is provable directly by `p` (a single rule), so the
    // direct exact pass supplies it; generation must not be required.
    const proof_src =
        \\t
        \\----
        \\l1: $ Q $ by pq [auto?]
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    var suggestions = try autoInlineSuggestions(&arena, proof_src, "auto?", .{
        .counters = &counters,
        .generate = .{ .enabled = true },
    });
    defer suggestions.deinit();

    // The direct exact pass renders a no-ref rule as `p` (brackets are only
    // emitted for non-empty ref lists); the generation pass, which also runs,
    // renders the same axiom as `p []`. Either way the slot resolves; the point
    // is that a directly-provable slot does not depend on generation.
    var found_direct = false;
    for (suggestions.items) |item| {
        if (std.mem.eql(u8, item.replacement, "p")) found_direct = true;
    }
    try std.testing.expect(found_direct);
}

test "inline auto reports a miss on an unprovable slot" {
    // `sq`'s only hypothesis is `S`, and no rule concludes `S`, so the slot goal
    // has no proof at all — both the direct exact pass and the generated pass
    // come up empty and the search is a definitive inline miss.
    const proof_src =
        \\t
        \\----
        \\l1: $ Q $ by sq [auto?]
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    var suggestions = try autoInlineSuggestions(&arena, proof_src, "auto?", .{
        .counters = &counters,
        .generate = .{ .enabled = true },
    });
    defer suggestions.deinit();

    try std.testing.expectEqual(@as(usize, 0), suggestions.items.len);
}

test "inline auto generates a longer chain in a slot" {
    // Outer rule `rx` needs a proof of `R` in its slot. `R` is only reachable by
    // a two-level chain `qr [pq [p]]`, so the slot must recurse twice, producing
    // a strictly longer inline application than the depth-1 case.
    const proof_src =
        \\tX
        \\----
        \\l1: $ X $ by rx [auto?]
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    var suggestions = try autoInlineSuggestions(&arena, proof_src, "auto?", .{
        .counters = &counters,
        .generate = .{ .enabled = true },
    });
    defer suggestions.deinit();

    var found = false;
    for (suggestions.items) |item| {
        if (std.mem.eql(u8, item.replacement, "qr [pq [p []]]")) found = true;
    }
    try std.testing.expect(found);
    try std.testing.expect(counters.generated_chain_attempts > 0);
}

test "inline auto grounds an existential meta inside a slot" {
    // The slot goal `R` (concrete) is provable by `r2 (a: wff): a > Q > R`, whose
    // first argument `a` is NOT pinned by the conclusion. Generation opens `a` as
    // an existential meta and grounds it from the theorem hypothesis `#1` (= P),
    // then fills the concrete sibling `Q` with `pq [#1]` — exercising the same
    // metavar-grounding path `auto_open_mm0` covers at top level, now in a slot.
    const proof_src =
        \\tPX
        \\----
        \\l1: $ X $ by rx [auto?]
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    var suggestions = try autoInlineSuggestions(&arena, proof_src, "auto?", .{
        .counters = &counters,
        .generate = .{ .enabled = true },
    });
    defer suggestions.deinit();

    var found = false;
    for (suggestions.items) |item| {
        if (std.mem.eql(u8, item.replacement, "r2 [#1, pq [#1]]")) found = true;
    }
    try std.testing.expect(found);
}

// Real Zermelo natural-deduction theory: `,` (the sequent context) is a full
// `@acui` combiner, so `and_intro`'s conclusion context `G , H` splits
// ambiguously against a single-member goal context. See the ACUI-combiner guard
// in `expectedRefForApplication`. Read from disk (unit tests run at repo root);
// the full congruence/@relation machinery it carries is what makes the ordinary
// exact search resolve these sequent goals, so a hand-trimmed fixture won't do.
fn andCommSlotSuggestions(
    arena: *std.heap.ArenaAllocator,
    proof_src: []const u8,
) !types.SourceSuggestions {
    const mm0 = try std.fs.cwd().readFileAlloc(
        arena.allocator(),
        "tests/proof_cases/zermelo.mm0",
        std.math.maxInt(usize),
    );
    const offset = std.mem.indexOf(u8, proof_src, "exact?").?;
    return source.suggestionsAtSourceOffset(
        arena.allocator(),
        mm0,
        proof_src,
        offset,
        .{},
    );
}

fn expectSlotReplacement(
    suggestions: types.SourceSuggestions,
    wanted: []const u8,
) !void {
    for (suggestions.items) |item| {
        if (std.mem.eql(u8, item.replacement, wanted)) return;
    }
    return error.MissingExpectedSuggestion;
}

test "inline exact resolves either and_intro premise slot (ACUI context split)" {
    // `and_intro`'s conclusion context `G , H` matches the goal's single context
    // `p ∧ q` ambiguously. The probe commits one canonical ACUI split — whole
    // context to the last operand, `emp` to earlier ones — which used to leave a
    // *first*-premise slot goal as `emp ⊢ q`, matching nothing. Both slot
    // orderings must resolve symmetrically now.
    const first_slot =
        \\nd_and_comm
        \\----
        \\l1: $ p ∧ q ⊢ p ∧ q $ by ax
        \\l2: $ p ∧ q ⊢ p $ by and_elim_l [l1]
        \\l3: $ p ∧ q ⊢ q $ by and_elim_r [l1]
        \\l4: $ p ∧ q ⊢ q ∧ p $ by and_intro [exact?, l2]
    ;
    const second_slot =
        \\nd_and_comm
        \\----
        \\l1: $ p ∧ q ⊢ p ∧ q $ by ax
        \\l2: $ p ∧ q ⊢ p $ by and_elim_l [l1]
        \\l3: $ p ∧ q ⊢ q $ by and_elim_r [l1]
        \\l4: $ p ∧ q ⊢ q ∧ p $ by and_intro [l3, exact?]
    ;

    var arena_a = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_a.deinit();
    var first = try andCommSlotSuggestions(&arena_a, first_slot);
    defer first.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, first.status);
    try expectSlotReplacement(first, "l3");

    var arena_b = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_b.deinit();
    var second = try andCommSlotSuggestions(&arena_b, second_slot);
    defer second.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, second.status);
    try expectSlotReplacement(second, "l2");
}

fn expectGeneratedConclusionGate(wrong_conclusion: bool) !usize {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    var fixture = try fixtureFor(allocator, auto_chain_mm0, "t");
    var sink = DiagnosticSink.init(auto_chain_mm0, "");
    var compiler = CompilerContext.init(auto_chain_mm0, "", .none, &sink);
    var theorem = TheoremContext.init(allocator);
    defer theorem.deinit();
    try theorem.seedAssertion(fixture.assertion);
    var theorem_vars = try Check.buildTheoremVarMap(
        allocator,
        fixture.assertion,
    );
    defer theorem_vars.deinit();
    var harness = ContextHarness.init(allocator);
    defer harness.deinit();
    const context = harness.context(&fixture);
    const goal = try parseGoal(&fixture, &theorem, &theorem_vars, "Q");
    const wrong_expr = try parseGoal(&fixture, &theorem, &theorem_vars, "Q");
    var hook_ctx = GeneratedConclusionHookCtx{
        .wrong_conclusion = wrong_conclusion,
        .wrong_expr = switch (wrong_expr) {
            .concrete => |expr| expr,
            else => return error.ExpectedConcreteGoal,
        },
    };
    const hook = types.GenerationHook{
        .ctx = &hook_ctx,
        .solveFn = GeneratedConclusionHookCtx.solve,
        .allow_split = false,
    };
    var results = try exact(
        &compiler,
        &context,
        goal,
        &theorem,
        &theorem_vars,
        .{ .max_results = 1, .generator = &hook },
    );
    defer results.deinit();
    try std.testing.expect(hook_ctx.calls > 0);
    return results.candidates.len;
}

test "generated child conclusion is checked against the target" {
    try std.testing.expectEqual(
        @as(usize, 1),
        try expectGeneratedConclusionGate(false),
    );
    try std.testing.expectEqual(
        @as(usize, 0),
        try expectGeneratedConclusionGate(true),
    );
}

test "exact does not generate the chain" {
    const proof_src =
        \\t
        \\----
        \\l1: $ Q $ by exact?
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var suggestions = try autoChainSuggestions(&arena, proof_src, "exact?", .{
        .generate = .{ .enabled = true },
    });
    defer suggestions.deinit();
    // `exact?` never generates, even with the permit set.
    try std.testing.expectEqual(@as(usize, 0), suggestions.items.len);
}

test "auto without the generation permit does not generate" {
    const proof_src =
        \\t
        \\----
        \\l1: $ Q $ by auto?
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var suggestions = try autoChainSuggestions(&arena, proof_src, "auto?", .{});
    defer suggestions.deinit();
    try std.testing.expectEqual(@as(usize, 0), suggestions.items.len);
}

// Open-hypothesis grounding. `r2`'s first hypothesis `a` is not
// pinned by its conclusion `R`, so it must be grounded from a ref (#1 = P) by the
// backtracker; once it is, the sibling hypothesis `Q` is concrete and gets a
// generated sub-proof (`pq [#1]`). Step 1 (pinned-only) could not do this.
const auto_open_mm0 =
    \\delimiter $ ( ) $;
    \\provable sort wff;
    \\term P: wff;
    \\term Q: wff;
    \\term R: wff;
    \\axiom p: $ P $;
    \\axiom pq: $ P $ > $ Q $;
    \\axiom r2 (a: wff): $ a $ > $ Q $ > $ R $;
    \\theorem t: $ P $ > $ R $;
;

test "auto grounds an open hypothesis from a ref and generates a sibling" {
    const proof_src =
        \\t
        \\----
        \\l1: $ R $ by auto?
    ;
    const offset = std.mem.indexOf(u8, proof_src, "auto?").?;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var suggestions = try source.suggestionsAtSourceOffset(
        arena.allocator(),
        auto_open_mm0,
        proof_src,
        offset,
        .{ .generate = .{ .enabled = true } },
    );
    defer suggestions.deinit();

    var found = false;
    for (suggestions.items) |item| {
        if (std.mem.eql(u8, item.replacement, "r2 [#1, pq [#1]]")) found = true;
    }
    try std.testing.expect(found);
}

// Iterative deepening. `R` needs a two-level chain
// `qr [pq [p]]` (depth 1 finds nothing because `pq`'s `P` can't be closed by a
// leaf search), so the driver must escalate from depth 1 to depth 2.
const auto_depth2_mm0 =
    \\delimiter $ ( ) $;
    \\provable sort wff;
    \\term P: wff;
    \\term Q: wff;
    \\term R: wff;
    \\axiom p: $ P $;
    \\axiom pq: $ P $ > $ Q $;
    \\axiom qr: $ Q $ > $ R $;
    \\theorem t: $ R $;
;

test "auto escalates depth to find a two-level chain" {
    const proof_src =
        \\t
        \\----
        \\l1: $ R $ by auto?
    ;
    const offset = std.mem.indexOf(u8, proof_src, "auto?").?;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var suggestions = try source.suggestionsAtSourceOffset(
        arena.allocator(),
        auto_depth2_mm0,
        proof_src,
        offset,
        .{ .generate = .{ .enabled = true } },
    );
    defer suggestions.deinit();

    var found = false;
    for (suggestions.items) |item| {
        if (std.mem.eql(u8, item.replacement, "qr [pq [p []]]")) found = true;
    }
    try std.testing.expect(found);
}

test "auto depth cap stops escalation" {
    const proof_src =
        \\t
        \\----
        \\l1: $ R $ by auto?
    ;
    const offset = std.mem.indexOf(u8, proof_src, "auto?").?;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // With the depth capped at 1, the two-level chain is unreachable.
    var suggestions = try source.suggestionsAtSourceOffset(
        arena.allocator(),
        auto_depth2_mm0,
        proof_src,
        offset,
        .{ .generate = .{ .enabled = true, .max_depth = 1 } },
    );
    defer suggestions.deinit();
    try std.testing.expectEqual(@as(usize, 0), suggestions.items.len);
}

test "auto global fuel floor stops the search and reports exhaustion" {
    const proof_src =
        \\t
        \\----
        \\l1: $ R $ by auto?
    ;
    const offset = std.mem.indexOf(u8, proof_src, "auto?").?;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    // The two-level chain `qr [pq [p]]` needs several validations; a fuel of 1
    // is spent on the first `tryCandidate`, so the next one trips the floor.
    var suggestions = try source.suggestionsAtSourceOffset(
        arena.allocator(),
        auto_depth2_mm0,
        proof_src,
        offset,
        .{ .counters = &counters, .generate = .{ .enabled = true, .fuel = 1 } },
    );
    defer suggestions.deinit();
    // Budget exhaustion is reported distinctly, and surfaces no suggestion.
    try std.testing.expectEqual(@as(usize, 0), suggestions.items.len);
    try std.testing.expect(counters.recursive_budget_exhausted);
    try std.testing.expectEqual(
        types.SearchStatus.budget_exhausted,
        suggestions.status,
    );
}

test "auto stack guard stops the search and reports exhaustion" {
    const proof_src =
        \\t
        \\----
        \\l1: $ R $ by auto?
    ;
    const offset = std.mem.indexOf(u8, proof_src, "auto?").?;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    // A 1-byte guard trips at the first recursive sub-solve: the honest-miss
    // degradation path a real overflow-threatening descent would take.
    var suggestions = try source.suggestionsAtSourceOffset(
        arena.allocator(),
        auto_depth2_mm0,
        proof_src,
        offset,
        .{
            .counters = &counters,
            .generate = .{ .enabled = true, .stack_guard_bytes = 1 },
        },
    );
    defer suggestions.deinit();
    // The guard is reported like a budget exhaustion, never a hard error.
    try std.testing.expectEqual(@as(usize, 0), suggestions.items.len);
    try std.testing.expect(counters.stack_guard_exhausted);
    try std.testing.expectEqual(
        types.SearchStatus.budget_exhausted,
        suggestions.status,
    );
}

test "auto with ample fuel finds the chain without tripping the floor" {
    const proof_src =
        \\t
        \\----
        \\l1: $ R $ by auto?
    ;
    const offset = std.mem.indexOf(u8, proof_src, "auto?").?;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    var suggestions = try source.suggestionsAtSourceOffset(
        arena.allocator(),
        auto_depth2_mm0,
        proof_src,
        offset,
        .{ .counters = &counters, .generate = .{ .enabled = true } },
    );
    defer suggestions.deinit();

    var found = false;
    for (suggestions.items) |item| {
        if (std.mem.eql(u8, item.replacement, "qr [pq [p []]]")) found = true;
    }
    try std.testing.expect(found);
    // The default fuel floor is generous; a normal proof never trips it.
    try std.testing.expect(!counters.recursive_budget_exhausted);
    // Same for the default call-stack guard.
    try std.testing.expect(!counters.stack_guard_exhausted);
    try std.testing.expectEqual(types.SearchStatus.found, suggestions.status);
}

test "exact does not ground-and-generate the open-hyp chain" {
    const proof_src =
        \\t
        \\----
        \\l1: $ R $ by exact?
    ;
    const offset = std.mem.indexOf(u8, proof_src, "exact?").?;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var suggestions = try source.suggestionsAtSourceOffset(
        arena.allocator(),
        auto_open_mm0,
        proof_src,
        offset,
        .{ .generate = .{ .enabled = true } },
    );
    defer suggestions.deinit();
    try std.testing.expectEqual(@as(usize, 0), suggestions.items.len);
}

test "source exact completes inline application from parent expected goal" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term P: wff;
        \\term Q: wff;
        \\axiom p: $ P $;
        \\axiom use: $ P $ > $ Q $;
        \\theorem t: $ Q $;
    ;
    const proof_src =
        \\t
        \\------
        \\l1: $ Q $ by use [exact?]
    ;
    const offset = std.mem.indexOf(u8, proof_src, "exact?") orelse {
        return error.MissingNeedle;
    };
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var suggestions = try source.suggestionsAtSourceOffset(
        arena.allocator(),
        mm0_src,
        proof_src,
        offset,
        .{},
    );
    defer suggestions.deinit();

    try std.testing.expect(suggestions.items.len > 0);
    try std.testing.expectEqualStrings("p", suggestions.items[0].replacement);
}

test "source exact inside inline application can resolve to direct ref" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term P: wff;
        \\axiom id (p: wff): $ p $ > $ p $;
        \\theorem t: $ P $ > $ P $;
    ;
    const proof_src =
        \\t
        \\------
        \\l1: $ P $ by id [exact?]
    ;
    const offset = std.mem.indexOf(u8, proof_src, "exact?") orelse {
        return error.MissingNeedle;
    };
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    var suggestions = try source.suggestionsAtSourceOffset(
        arena.allocator(),
        mm0_src,
        proof_src,
        offset,
        .{ .counters = &counters },
    );
    defer suggestions.deinit();

    try std.testing.expect(suggestions.items.len > 0);
    try std.testing.expectEqualStrings(
        "#1",
        suggestions.items[0].replacement,
    );
    try expectTimingCounter(counters.ref_index_build_ns);
    try expectTimingCounter(counters.ref_lookup_ns);
}

test "source apply completes inline application with unresolved subrefs" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term P: wff;
        \\term Q: wff;
        \\axiom id (p: wff): $ p $ > $ p $;
        \\axiom use: $ P $ > $ Q $;
        \\theorem t: $ P $ > $ Q $;
    ;
    const proof_src =
        \\t
        \\------
        \\l1: $ Q $ by use [apply?]
    ;
    const offset = std.mem.indexOf(u8, proof_src, "apply?") orelse {
        return error.MissingNeedle;
    };
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var suggestions = try source.suggestionsAtSourceOffset(
        arena.allocator(),
        mm0_src,
        proof_src,
        offset,
        .{},
    );
    defer suggestions.deinit();

    try std.testing.expect(suggestions.items.len > 0);
    try std.testing.expectEqualStrings(
        "id [ref1]",
        suggestions.items[0].replacement,
    );
}

test "source exact inside inline application requires useful parent goal" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term P: wff;
        \\term Q: wff;
        \\term R: wff;
        \\term imp (p q: wff): wff;
        \\infixr imp: $->$ prec 25;
        \\axiom mp (p q: wff): $ p $ > $ p -> q $ > $ q $;
        \\axiom q_imp (p: wff): $ p -> Q $;
        \\theorem t: $ Q $;
    ;
    const proof_src =
        \\t
        \\------
        \\l1: $ Q $ by mp [exact?, exact?]
    ;
    const offset = std.mem.indexOf(u8, proof_src, "exact?") orelse {
        return error.MissingNeedle;
    };
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var suggestions = try source.suggestionsAtSourceOffset(
        arena.allocator(),
        mm0_src,
        proof_src,
        offset,
        .{},
    );
    defer suggestions.deinit();

    try std.testing.expectEqual(@as(usize, 0), suggestions.items.len);
}

test "source exact nested inline edit is local" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term P: wff;
        \\term Q: wff;
        \\term R: wff;
        \\axiom id (p: wff): $ p $ > $ p $;
        \\axiom use: $ P $ > $ P $ > $ R $;
        \\theorem t: $ P $ > $ R $;
    ;
    const proof_src =
        \\t
        \\------
        \\l1: $ R $ by use [id [exact?], #1]
    ;
    const offset = std.mem.indexOf(u8, proof_src, "exact?") orelse {
        return error.MissingNeedle;
    };
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var suggestions = try source.suggestionsAtSourceOffset(
        arena.allocator(),
        mm0_src,
        proof_src,
        offset,
        .{},
    );
    defer suggestions.deinit();

    try std.testing.expect(suggestions.items.len > 0);
    try std.testing.expectEqualStrings(
        "#1",
        suggestions.items[0].replacement,
    );
    const expected_span = std.mem.indexOf(u8, proof_src, "exact?") orelse {
        return error.MissingNeedle;
    };
    try std.testing.expectEqual(
        expected_span,
        suggestions.items[0].replace_span.start,
    );
    try std.testing.expectEqual(
        expected_span + "exact?".len,
        suggestions.items[0].replace_span.end,
    );
}

test "source exact inside inline ex elim uses sibling and goal" {
    const mm0_src =
        \\delimiter $ ( ) , $;
        \\strict provable sort wff;
        \\sort set;
        \\sort ctx;
        \\term ctx_eq (G H: ctx): wff;
        \\term emp: ctx;
        \\notation emp: ctx = ($_$:max);
        \\--| @acui ctx_assoc ctx_comm emp ctx_idem
        \\term join (G H: ctx): ctx;
        \\infixl join: $,$ prec 5;
        \\term hyp (p: wff): ctx;
        \\coercion hyp: wff > ctx;
        \\term nd (G: ctx) (p: wff): wff;
        \\infixl nd: $⊢$ prec 0;
        \\term ex {x: set} (p: wff x): wff;
        \\prefix ex: $∃$ prec 41;
        \\term P (x: set): wff;
        \\term Q: wff;
        \\axiom ctx_refl (G: ctx): $ ctx_eq G G $;
        \\axiom ctx_trans (G H K: ctx):
        \\  $ ctx_eq G H $ > $ ctx_eq H K $ > $ ctx_eq G K $;
        \\axiom ctx_sym (G H: ctx): $ ctx_eq G H $ > $ ctx_eq H G $;
        \\axiom ctx_assoc (G H K: ctx):
        \\  $ ctx_eq ((G , H) , K) (G , (H , K)) $;
        \\axiom ctx_comm (G H: ctx): $ ctx_eq (G , H) (H , G) $;
        \\axiom ctx_idem (G: ctx): $ ctx_eq (G , G) G $;
        \\axiom make_q (H: ctx) {x: set}: $ H , P x ⊢ Q $;
        \\axiom ex_elim {x: set} (G H: ctx x) (p: wff x) (c: wff):
        \\  $ G ⊢ ∃ x p $ > $ H , p ⊢ c $ > $ G , H ⊢ c $;
        \\theorem t (G H: ctx) {x: set}:
        \\  $ G ⊢ ∃ x (P x) $ > $ G , H ⊢ Q $;
    ;
    const proof_src =
        \\t
        \\------
        \\l1: $ H , P x ⊢ Q $ by make_q
        \\l2: $ G , H ⊢ Q $ by ex_elim [#1, exact?]
    ;
    const offset = std.mem.indexOf(u8, proof_src, "exact?") orelse {
        return error.MissingNeedle;
    };
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var suggestions = try source.suggestionsAtSourceOffset(
        arena.allocator(),
        mm0_src,
        proof_src,
        offset,
        .{},
    );
    defer suggestions.deinit();

    try std.testing.expect(suggestions.items.len > 0);
    try std.testing.expectEqualStrings(
        "l1",
        suggestions.items[0].replacement,
    );
}

test "source exact inside inline ex elim uses later sibling" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    const mm0_src = try readProofCase(allocator, "zermelo", "mm0");
    const proof_src =
        \\nd_exists_elim_const
        \\--------------------
        \\l1: $ ∃ x p ⊢ ∃ x p $ by ax
        \\l2: $ p → q ⊢ p → q $ by ax
        \\l3: $ p ⊢ p $ by ax
        \\l4: $ p → q , p ⊢ q $ by imp_elim [l2, l3]
        \\l5: $ ∃ x p , p → q ⊢ q $ by ex_elim [exact?, l4]
        \\l6: $ ∃ x p ⊢ (p → q) → q $ by imp_intro [l5]
        \\l7: $ _ ⊢ (∃ x p) → ((p → q) → q) $ by imp_intro [l6]
    ;
    const offset = std.mem.indexOf(u8, proof_src, "exact?") orelse {
        return error.MissingNeedle;
    };
    var counters = types.SearchCounters{};
    var suggestions = try source.suggestionsAtSourceOffset(
        allocator,
        mm0_src,
        proof_src,
        offset,
        .{ .counters = &counters },
    );
    defer suggestions.deinit();

    for (suggestions.items) |item| {
        if (std.mem.eql(u8, item.replacement, "l1")) {
            try expectTimingCounter(counters.ref_lookup_ns);
            return;
        }
    }
    return error.ExpectedInlineExactSuggestion;
}

test "extractHypPartialBindings keeps an ACUI binder open for an eigenvariable sibling" {
    // Regression for the `ex_elim` eigenvariable / commutative-ACUI-context
    // interaction (zermelo `cb_branch_fg_injective_mixed l16`). The body
    // hypothesis template `H , p` (= `join(H, hyp(p))`, `H` a bare context
    // binder, `p` the eigenvariable wff) is extracted against a ref whose join
    // is associated so the eigenvariable member `hyp(P s)` sits inside the first
    // positional arg and the trailing arg is a bare (non-`hyp`) context term.
    //
    // The old positional walk pinned `H` to the ref's first arg — swallowing the
    // `hyp(P s)` member — which left `p` unpinnable (no remaining `hyp`-shaped
    // member) and carried the eigenvariable into the rule's context binder.
    // Under a commutative ACUI head the positional walk is now skipped, so the
    // member extractor pins `p` to the unique `hyp` member and leaves the bare
    // binder `H` open for the validator's ACUI weakening.
    const mm0_src =
        \\delimiter $ ( ) , $;
        \\strict provable sort wff;
        \\sort set;
        \\sort ctx;
        \\term ctx_eq (G H: ctx): wff;
        \\term emp: ctx;
        \\notation emp: ctx = ($_$:max);
        \\--| @acui ctx_assoc ctx_comm emp ctx_idem
        \\term join (G H: ctx): ctx;
        \\infixl join: $,$ prec 5;
        \\term hyp (p: wff): ctx;
        \\coercion hyp: wff > ctx;
        \\term ca: ctx;
        \\term cb: ctx;
        \\term s0: set;
        \\term P (x: set): wff;
        \\axiom ctx_assoc (G H K: ctx):
        \\  $ ctx_eq ((G , H) , K) (G , (H , K)) $;
        \\axiom ctx_comm (G H: ctx): $ ctx_eq (G , H) (H , G) $;
        \\axiom ctx_idem (G: ctx): $ ctx_eq (G , G) G $;
        \\theorem t (G: ctx): $ ctx_eq G G $;
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();

    var fixture = try fixtureFor(allocator, mm0_src, "t");
    var harness = ContextHarness.init(allocator);
    defer harness.deinit();
    const context = harness.context(&fixture);

    const ti_join = fixture.env.term_names.get("join").?;
    const ti_hyp = fixture.env.term_names.get("hyp").?;
    const ti_ca = fixture.env.term_names.get("ca").?;
    const ti_cb = fixture.env.term_names.get("cb").?;
    const ti_s0 = fixture.env.term_names.get("s0").?;
    const ti_P = fixture.env.term_names.get("P").?;

    var theorem = TheoremContext.init(allocator);
    defer theorem.deinit();
    const s0 = try theorem.interner.internApp(ti_s0, &.{});
    const px = try theorem.interner.internApp(ti_P, &.{s0});
    const hyp_px = try theorem.interner.internApp(ti_hyp, &.{px});
    const ca = try theorem.interner.internApp(ti_ca, &.{});
    const cb = try theorem.interner.internApp(ti_cb, &.{});
    // Ref: `join(join(ca, hyp(P s)), cb)` — eigenvariable member buried in the
    // first positional arg, trailing arg a bare (non-`hyp`) context term.
    const inner = try theorem.interner.internApp(ti_join, &.{ ca, hyp_px });
    const ref = try theorem.interner.internApp(ti_join, &.{ inner, cb });

    // Template `join(binder0, hyp(binder1))`: binder0 = bare context `H`,
    // binder1 = the eigenvariable wff `p`.
    const hyp_p_args = [_]TemplateExpr{.{ .binder = 1 }};
    const hyp_p = TemplateExpr{ .app = .{ .term_id = ti_hyp, .args = &hyp_p_args } };
    const join_args = [_]TemplateExpr{ .{ .binder = 0 }, hyp_p };
    const template = TemplateExpr{ .app = .{ .term_id = ti_join, .args = &join_args } };

    var bindings = [_]?ExprId{ null, null };
    def_match.extractHypPartialBindings(
        &context,
        &theorem,
        template,
        ref,
        &bindings,
    );

    // `p` (binder 1) is pinned to the unique `hyp` member; the bare context
    // binder `H` (binder 0) stays open rather than swallowing it.
    try std.testing.expectEqual(@as(?ExprId, px), bindings[1]);
    try std.testing.expectEqual(@as(?ExprId, null), bindings[0]);
}

test "canonicalizeAcui respects the registered combiner subset" {
    // The success/failure memo keys (`generate.zig` `canonicalKey`) collapse
    // ACUI-equal subgoals via `canonicalizeAcui`. It must collapse only the laws
    // the *registered subset* declares: over-collision would let a sub-proof be
    // reused for a genuinely-unequal goal (an unsound memo hit). Three combiners
    // exercise the distinguishing subset cells: `join` is full ACUI; `bag` is ACU
    // (commutative but NOT idempotent — sort, but keep duplicates); `seq` is AU
    // (NOT commutative, not idempotent — keep order and duplicates).
    const mm0_src =
        \\delimiter $ ( ) , $;
        \\strict provable sort wff;
        \\sort ctx;
        \\term ctx_eq (G H: ctx): wff;
        \\infixl ctx_eq: $=$ prec 10;
        \\term emp: ctx;
        \\term bemp: ctx;
        \\term semp: ctx;
        \\--| @acui ctx_assoc ctx_comm emp ctx_idem
        \\term join (G H: ctx): ctx;
        \\--| @acui bag_assoc bag_comm bemp _
        \\term bag (G H: ctx): ctx;
        \\--| @acui seq_assoc _ semp _
        \\term seq (G H: ctx): ctx;
        \\term ca: ctx;
        \\term cb: ctx;
        \\term cc: ctx;
        \\axiom ctx_assoc (G H K: ctx): $ G = G $;
        \\axiom ctx_comm (G H: ctx): $ G = G $;
        \\axiom ctx_idem (G: ctx): $ G = G $;
        \\axiom bag_assoc (G H K: ctx): $ G = G $;
        \\axiom bag_comm (G H: ctx): $ G = G $;
        \\axiom seq_assoc (G H K: ctx): $ G = G $;
        \\theorem t (G: ctx): $ G = G $;
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();

    var fixture = try fixtureFor(allocator, mm0_src, "t");
    var harness = ContextHarness.init(allocator);
    defer harness.deinit();
    const context = harness.context(&fixture);

    const ti_join = fixture.env.term_names.get("join").?;
    const ti_bag = fixture.env.term_names.get("bag").?;
    const ti_seq = fixture.env.term_names.get("seq").?;
    const ti_emp = fixture.env.term_names.get("emp").?;
    const ti_bemp = fixture.env.term_names.get("bemp").?;
    const ti_semp = fixture.env.term_names.get("semp").?;
    const ti_ca = fixture.env.term_names.get("ca").?;
    const ti_cb = fixture.env.term_names.get("cb").?;
    const ti_cc = fixture.env.term_names.get("cc").?;

    var theorem = TheoremContext.init(allocator);
    defer theorem.deinit();
    const ca = try theorem.interner.internApp(ti_ca, &.{});
    const cb = try theorem.interner.internApp(ti_cb, &.{});
    const cc = try theorem.interner.internApp(ti_cc, &.{});
    const emp = try theorem.interner.internApp(ti_emp, &.{});
    const bemp = try theorem.interner.internApp(ti_bemp, &.{});
    const semp = try theorem.interner.internApp(ti_semp, &.{});

    const j = struct {
        fn mk(t: *TheoremContext, head: u32, x: ExprId, y: ExprId) !ExprId {
            return t.interner.internApp(head, &.{ x, y });
        }
    }.mk;
    const canon = struct {
        fn f(c: *const Context, t: *TheoremContext, e: ExprId) !ExprId {
            return acui.canonicalizeAcui(c, t, e);
        }
    }.f;

    // A bare atom canonicalizes to itself.
    try std.testing.expectEqual(ca, try canon(&context, &theorem, ca));

    // --- join: full ACUI ---
    // C: order-variant regions collide.
    try std.testing.expectEqual(
        try canon(&context, &theorem, try j(&theorem, ti_join, ca, cb)),
        try canon(&context, &theorem, try j(&theorem, ti_join, cb, ca)),
    );
    // A: re-association collides.
    try std.testing.expectEqual(
        try canon(&context, &theorem, try j(&theorem, ti_join, try j(&theorem, ti_join, ca, cb), cc)),
        try canon(&context, &theorem, try j(&theorem, ti_join, ca, try j(&theorem, ti_join, cb, cc))),
    );
    // U: a unit member drops.
    try std.testing.expectEqual(ca, try canon(&context, &theorem, try j(&theorem, ti_join, ca, emp)));
    // I: a duplicate member collapses.
    try std.testing.expectEqual(ca, try canon(&context, &theorem, try j(&theorem, ti_join, ca, ca)));

    // --- bag: ACU (commutative, NOT idempotent) ---
    // C: order-variants collide.
    try std.testing.expectEqual(
        try canon(&context, &theorem, try j(&theorem, ti_bag, ca, cb)),
        try canon(&context, &theorem, try j(&theorem, ti_bag, cb, ca)),
    );
    // NOT idempotent: a duplicate must be KEPT (sorting must not imply dedup).
    try std.testing.expect(
        (try canon(&context, &theorem, try j(&theorem, ti_bag, ca, ca))) != ca,
    );
    // U still holds.
    try std.testing.expectEqual(ca, try canon(&context, &theorem, try j(&theorem, ti_bag, ca, bemp)));

    // --- seq: AU only (the soundness-critical negatives) ---
    // NOT commutative: order-variants must stay DISTINCT.
    try std.testing.expect(
        (try canon(&context, &theorem, try j(&theorem, ti_seq, ca, cb))) !=
            (try canon(&context, &theorem, try j(&theorem, ti_seq, cb, ca))),
    );
    // NOT idempotent: a duplicate must NOT collapse.
    try std.testing.expect(
        (try canon(&context, &theorem, try j(&theorem, ti_seq, ca, ca))) != ca,
    );
    // A still holds: re-association collides.
    try std.testing.expectEqual(
        try canon(&context, &theorem, try j(&theorem, ti_seq, try j(&theorem, ti_seq, ca, cb), cc)),
        try canon(&context, &theorem, try j(&theorem, ti_seq, ca, try j(&theorem, ti_seq, cb, cc))),
    );
    // U still holds: the unit member drops.
    try std.testing.expectEqual(ca, try canon(&context, &theorem, try j(&theorem, ti_seq, ca, semp)));
}

test "source exact inside inline or_elim uses sibling branch" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    const mm0_src = try readProofCase(allocator, "zermelo", "mm0");
    const proof_src =
        \\nd_or_comm
        \\----------
        \\l1: $ p ∨ q ⊢ p ∨ q $ by ax
        \\l2: $ p ⊢ p $ by ax
        \\l3: $ p ⊢ q ∨ p $ by or_intro_r [l2]
        \\l4: $ q ⊢ q $ by ax
        \\l5: $ q ⊢ q ∨ p $ by or_intro_l [l4]
        \\l6: $ p ∨ q ⊢ q ∨ p $ by or_elim [l1, exact?, l5]
        \\l7: $ _ ⊢ (p ∨ q) → (q ∨ p) $ by imp_intro [l6]
    ;
    const offset = std.mem.indexOf(u8, proof_src, "exact?") orelse {
        return error.MissingNeedle;
    };
    var suggestions = try source.suggestionsAtSourceOffset(
        allocator,
        mm0_src,
        proof_src,
        offset,
        .{},
    );
    defer suggestions.deinit();

    for (suggestions.items) |item| {
        if (std.mem.eql(u8, item.replacement, "l3")) return;
    }
    return error.ExpectedInlineExactSuggestion;
}

test "source exact inline search supports view candidates" {
    const mm0_src =
        \\delimiter $ ( ) [ / ] $;
        \\provable sort wff;
        \\--| @vars x y z t
        \\sort nat;
        \\term ex {x: nat} (p: wff x): wff;
        \\prefix ex: $E$ prec 41;
        \\term sb_f {x: nat} (t: nat x) (p: wff x): wff;
        \\notation sb_f {x: nat} (t: nat x) (p: wff x): wff =
        \\  ($[$:41) x ($/$:0) t ($]$:0) p;
        \\term sb_s {x: nat} (t: nat x) (a: nat x): nat;
        \\notation sb_s {x: nat} (t: nat x) (a: nat x): nat =
        \\  ($subst$:41) x ($/$:0) t a;
        \\term P (a: nat): wff;
        \\term c: nat;
        \\term Goal: wff;
        \\term iff (a b: wff): wff;
        \\infixr iff: $<->$ prec 20;
        \\term nat_eq (a b: nat): wff;
        \\infixl nat_eq: $==$ prec 35;
        \\--| @relation wff iff iff_refl iff_trans iff_sym iff_mp
        \\axiom iff_refl (a: wff): $ a <-> a $;
        \\axiom iff_trans (a b c: wff):
        \\  $ a <-> b $ > $ b <-> c $ > $ a <-> c $;
        \\axiom iff_sym (a b: wff): $ a <-> b $ > $ b <-> a $;
        \\axiom iff_mp (a b: wff): $ a <-> b $ > $ a $ > $ b $;
        \\--| @relation nat nat_eq eq_refl eq_trans eq_sym _
        \\axiom eq_refl (a: nat): $ a == a $;
        \\axiom eq_trans (a b c: nat): $ a == b $ > $ b == c $ > $ a == c $;
        \\axiom eq_sym (a b: nat): $ a == b $ > $ b == a $;
        \\--| @congr
        \\axiom P_congr (a b: nat): $ a == b $ > $ P a <-> P b $;
        \\--| @rewrite
        \\axiom sb_f_P {x: nat} (t a: nat x):
        \\  $ [x/t] (P a) <-> P (subst x / t a) $;
        \\--| @rewrite
        \\axiom sb_s_var {x: nat} (t: nat x): $ subst x / t x == t $;
        \\axiom have_Pc: $ P c $;
        \\--| @view {x: nat} (t: nat x) (p: wff x) (q: wff): $ q $ > $ E x p $
        \\--| @recover t q p x
        \\axiom ex_intro {x: nat} (t: nat x) (p: wff x):
        \\  $ [x/t] p $ > $ E x p $;
        \\axiom use_exists {x: nat}: $ E x (P x) $ > $ Goal $;
        \\theorem prove_goal {x: nat}: $ Goal $;
    ;
    const proof_src =
        \\prove_goal
        \\----------
        \\l1: $ P c $ by have_Pc
        \\l2: $ Goal $ by use_exists (x := $ x $) [exact?]
    ;
    const offset = std.mem.indexOf(u8, proof_src, "exact?") orelse {
        return error.MissingNeedle;
    };
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var suggestions = try source.suggestionsAtSourceOffset(
        arena.allocator(),
        mm0_src,
        proof_src,
        offset,
        .{},
    );
    defer suggestions.deinit();

    for (suggestions.items) |item| {
        if (std.mem.eql(u8, item.replacement, "ex_intro [l1]")) return;
    }
    return error.ExpectedSourceSuggestion;
}

// Guard for the `recoverGuardRejects` soundness fix: a `@recover` whose target
// is already pinned (here `t` from the conclusion match) must NOT be used as a
// pruning guard. `myrule` mirrors `sep_intro_imp2`: its `@recover t q p x` names
// the shared implication antecedent `q` as the source, which is NOT the
// substituted motive, so walking `q` against the motive pattern `p` "provably
// fails". Before the fix the search pruned both valid refs and never assembled
// `myrule [l1, l2]`; `applyRecover` skips the (target-resolved) law during real
// validation, so the prune was unsound.
test "exact search keeps view candidate when a pinned-target recover diverges" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\--| @vars x y z
        \\sort set;
        \\term imp (a b: wff): wff;
        \\term Mem (t A: set): wff;
        \\term Sep {x: set} (A: set) (p: wff x): set;
        \\term Phi: wff;
        \\term Psi: wff;
        \\term AA: set;
        \\term TT: set;
        \\axiom ref1: $ imp Psi (Mem TT AA) $;
        \\axiom ref2: $ imp Psi Phi $;
        \\--| @view {x: set} (t A: set) (p: wff x) (q r s: wff): $ imp q r $ > $ imp q s $ > $ imp q (Mem t (Sep x A p)) $
        \\--| @recover t q p x
        \\axiom myrule {x: set} (t A: set) (p: wff x) (q: wff):
        \\  $ imp q (Mem t A) $ > $ imp q p $ > $ imp q (Mem t (Sep x A p)) $;
        \\theorem prove_goal {x: set}: $ imp Psi (Mem TT (Sep x AA Phi)) $;
    ;
    const proof_src =
        \\prove_goal
        \\----------
        \\l1: $ imp Psi (Mem TT AA) $ by ref1
        \\l2: $ imp Psi Phi $ by ref2
        \\l3: $ imp Psi (Mem TT (Sep x AA Phi)) $ by exact?
    ;
    const offset = std.mem.indexOf(u8, proof_src, "exact?") orelse {
        return error.MissingNeedle;
    };
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var suggestions = try source.suggestionsAtSourceOffset(
        arena.allocator(),
        mm0_src,
        proof_src,
        offset,
        .{},
    );
    defer suggestions.deinit();

    for (suggestions.items) |item| {
        if (std.mem.eql(u8, item.replacement, "myrule [l1, l2]")) return;
    }
    return error.ExpectedSourceSuggestion;
}

test "recover member injection skips pinned-target laws" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\sort ctx;
        \\sort set;
        \\term ctx_eq (G H: ctx): wff;
        \\term emp: ctx;
        \\--| @acui ctx_assoc ctx_comm emp ctx_idem
        \\term join (G H: ctx): ctx;
        \\term hyp (p: wff): ctx;
        \\term nd (G: ctx) (p: wff): wff;
        \\term Mem (t A: set): wff;
        \\term Sep {x: set} (A: set) (p: wff x): set;
        \\term Phi: wff;
        \\term Psi: wff;
        \\term AA: set;
        \\term TT: set;
        \\axiom ctx_refl (G: ctx): $ ctx_eq G G $;
        \\axiom ctx_trans (G H K: ctx):
        \\  $ ctx_eq G H $ > $ ctx_eq H K $ > $ ctx_eq G K $;
        \\axiom ctx_sym (G H: ctx): $ ctx_eq G H $ > $ ctx_eq H G $;
        \\axiom ctx_assoc (G H K: ctx):
        \\  $ ctx_eq (join (join G H) K) (join G (join H K)) $;
        \\axiom ctx_comm (G H: ctx): $ ctx_eq (join G H) (join H G) $;
        \\axiom ctx_idem (G: ctx): $ ctx_eq (join G G) G $;
        \\axiom ref1: $ nd (join emp (hyp Psi)) (Mem TT AA) $;
        \\axiom ref2: $ nd (join emp (hyp Psi)) Phi $;
        \\--| @view {x: set} (t A: set) (p: wff x) (q r s: wff): $ nd (join emp (hyp q)) r $ > $ nd (join emp (hyp q)) s $ > $ nd emp (Mem t (Sep x A p)) $
        \\--| @recover t q p x
        \\axiom myrule {x: set} (t A: set) (p: wff x) (q: wff):
        \\  $ nd (join emp (hyp q)) (Mem t A) $ >
        \\  $ nd (join emp (hyp q)) p $ >
        \\  $ nd emp (Mem t (Sep x A p)) $;
        \\theorem prove_goal {x: set}: $ nd emp (Mem TT (Sep x AA Phi)) $;
    ;
    const proof_src =
        \\prove_goal
        \\----------
        \\l1: $ nd (join emp (hyp Psi)) (Mem TT AA) $ by ref1
        \\l2: $ nd (join emp (hyp Psi)) Phi $ by ref2
        \\l3: $ nd emp (Mem TT (Sep x AA Phi)) $ by exact?
    ;
    const offset = std.mem.indexOf(u8, proof_src, "exact?") orelse {
        return error.MissingNeedle;
    };
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var suggestions = try source.suggestionsAtSourceOffset(
        arena.allocator(),
        mm0_src,
        proof_src,
        offset,
        .{},
    );
    defer suggestions.deinit();

    for (suggestions.items) |item| {
        if (std.mem.eql(u8, item.replacement, "myrule [l1, l2]")) return;
    }
    return error.ExpectedSourceSuggestion;
}
