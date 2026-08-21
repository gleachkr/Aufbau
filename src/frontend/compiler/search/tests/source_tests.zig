const helpers = @import("./helpers.zig");
const std = helpers.std;
const types = helpers.types;
const source = helpers.source;
const backtrack = helpers.backtrack;
const prune = helpers.prune;
const plausible = helpers.plausible;
const seed = helpers.seed;
const acui = helpers.acui;
const ExprId = helpers.ExprId;
const TheoremContext = helpers.TheoremContext;
const Check = helpers.Check;
const apply = helpers.apply;
const exact = helpers.exact;
const tryCandidate = helpers.tryCandidate;
const fixtureFor = helpers.fixtureFor;
const parseGoal = helpers.parseGoal;
const expectTimingCounter = helpers.expectTimingCounter;
const ContextHarness = helpers.ContextHarness;
const expectApplyContains = helpers.expectApplyContains;
const expectInlineSearch = helpers.expectInlineSearch;

test "search candidate matches exactly" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term P: wff;
        \\axiom p: $ P $;
        \\theorem t: $ P $;
    ;
    const proof_src =
        \\t
        \\------
        \\l1: $ P $ by p
    ;
    try expectInlineSearch(mm0_src, proof_src, "t", 0);
}

test "apply search finds exact zero-hypothesis candidates" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term P: wff;
        \\term Q: wff;
        \\axiom p: $ P $;
        \\axiom q: $ Q $;
        \\theorem t: $ P $;
    ;
    try expectApplyContains(mm0_src, "t", "P", "p", 0, 0);
}

test "source search records search counters" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term P: wff;
        \\axiom p: $ P $;
        \\axiom id (p: wff): $ p $ > $ p $;
        \\theorem t: $ P $ > $ P $;
    ;
    const proof_src =
        \\t
        \\----
        \\l1: $ P $ by exact?
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

    try std.testing.expectEqual(@as(usize, 2), suggestions.items.len);
    try std.testing.expectEqual(@as(usize, 0), counters.conclusion_probes);
    try std.testing.expectEqual(@as(usize, 1), counters.ref_pool_size);
    try std.testing.expect(counters.full_try_candidate_calls > 0);
    try std.testing.expect(counters.accepted_candidates > 0);
    try expectTimingCounter(counters.cold_setup_ns);
    try expectTimingCounter(counters.warm_search_ns);
}

test "source suggestions can apply at an ordinary rule offset" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term P: wff;
        \\term Q: wff;
        \\axiom p: $ P $;
        \\axiom q: $ Q $;
        \\axiom keep (a: wff): $ a $ > $ a $;
        \\theorem t: $ P $;
    ;
    const proof_src =
        \\t
        \\----
        \\l1: $ P $ by ke
    ;
    const rule_start = std.mem.indexOf(u8, proof_src, "ke") orelse {
        return error.MissingNeedle;
    };
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var suggestions = try source.suggestionsAtSourceOffset(
        arena.allocator(),
        mm0_src,
        proof_src,
        rule_start + "ke".len,
        .{ .apply_at_offset = true },
    );
    defer suggestions.deinit();

    try std.testing.expect(suggestions.target_span != null);
    var found_p = false;
    var found_keep = false;
    for (suggestions.items) |item| {
        try std.testing.expectEqualStrings(
            "ke",
            proof_src[item.replace_span.start..item.replace_span.end],
        );
        if (std.mem.eql(u8, item.replacement, "p")) found_p = true;
        if (std.mem.startsWith(u8, item.replacement, "keep ")) {
            found_keep = true;
        }
        try std.testing.expect(!std.mem.startsWith(
            u8,
            item.replacement,
            "q",
        ));
    }
    try std.testing.expect(found_p);
    try std.testing.expect(found_keep);
}

test "source suggestions report found and miss status" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term P: wff;
        \\term Q: wff;
        \\axiom p: $ P $;
        \\theorem t: $ P $;
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    // Provable goal, no caller counters: the local counters block still
    // derives the status.
    const found_src =
        \\t
        \\----
        \\l1: $ P $ by exact?
    ;
    var found = try source.suggestionsAtSourceOffset(
        arena.allocator(),
        mm0_src,
        found_src,
        std.mem.indexOf(u8, found_src, "exact?").?,
        .{},
    );
    defer found.deinit();
    try std.testing.expect(found.items.len > 0);
    try std.testing.expectEqual(types.SearchStatus.found, found.status);

    // No rule concludes `Q`: the search runs to completion empty-handed.
    const miss_src =
        \\t
        \\----
        \\l1: $ Q $ by exact?
    ;
    var miss = try source.suggestionsAtSourceOffset(
        arena.allocator(),
        mm0_src,
        miss_src,
        std.mem.indexOf(u8, miss_src, "exact?").?,
        .{},
    );
    defer miss.deinit();
    try std.testing.expectEqual(@as(usize, 0), miss.items.len);
    try std.testing.expectEqual(types.SearchStatus.miss, miss.status);
    try std.testing.expect(miss.target_span != null);
}

// #156: a broken sibling line must not cost the block its search actions.
// The lenient parse keeps the block; the incomplete line contributes nothing
// to the checked context (same as a placeholder), and the target still
// searches.
test "source suggestions survive a broken sibling line" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term P: wff;
        \\term Q: wff;
        \\axiom p: $ P $;
        \\axiom q: $ Q $;
        \\theorem t: $ Q $;
    ;
    const proof_src =
        \\t
        \\----
        \\l1: $ P $ by p []
        \\l2: $ P $ by [#1]
        \\l3: $ Q $ by exact?
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var suggestions = try source.suggestionsAtSourceOffset(
        arena.allocator(),
        mm0_src,
        proof_src,
        std.mem.indexOf(u8, proof_src, "exact?").?,
        .{},
    );
    defer suggestions.deinit();
    try std.testing.expect(suggestions.items.len > 0);
    try std.testing.expectEqual(types.SearchStatus.found, suggestions.status);
}

// Same story one block earlier: a local lemma before the target holds the
// broken line. The lenient proof stream and the placeholder-tolerant fixture
// compiler keep the fixture build alive.
test "source suggestions survive a broken line in a preceding local lemma" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term P: wff;
        \\term Q: wff;
        \\axiom p: $ P $;
        \\axiom q: $ Q $;
        \\theorem t: $ Q $;
    ;
    const proof_src =
        \\lemma h: $ P $
        \\----
        \\h1: $ P $ by [#1]
        \\
        \\t
        \\----
        \\l1: $ Q $ by exact?
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var suggestions = try source.suggestionsAtSourceOffset(
        arena.allocator(),
        mm0_src,
        proof_src,
        std.mem.indexOf(u8, proof_src, "exact?").?,
        .{},
    );
    defer suggestions.deinit();
    try std.testing.expect(suggestions.items.len > 0);
    try std.testing.expectEqual(types.SearchStatus.found, suggestions.status);
}

test "searchPlaceholders survives a broken sibling line" {
    const proof_src =
        \\t
        \\----
        \\l1: $ P $ by [#1]
        \\l2: $ Q $ by auto?
    ;
    const placeholders = try source.searchPlaceholders(
        std.testing.allocator,
        proof_src,
    );
    defer std.testing.allocator.free(placeholders);

    try std.testing.expectEqual(@as(usize, 1), placeholders.len);
    try std.testing.expectEqual(
        source.SearchPlaceholder.Kind.auto,
        placeholders[0].kind,
    );
}

// A trailing local lemma has no public anchor block; its search scope is the
// whole mm0 (mirrors `drainTrailingLocalProofItems` on the compile path).
test "source suggestions work in a trailing local lemma" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term P: wff;
        \\axiom p: $ P $;
        \\theorem t: $ P $;
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    // Lemmas-only proof source: no public block at all.
    const solo_src =
        \\lemma l: $ P $
        \\----
        \\l1: $ P $ by exact?
    ;
    var solo = try source.suggestionsAtSourceOffset(
        arena.allocator(),
        mm0_src,
        solo_src,
        std.mem.indexOf(u8, solo_src, "exact?").?,
        .{},
    );
    defer solo.deinit();
    try std.testing.expect(solo.items.len > 0);
    try std.testing.expectEqual(types.SearchStatus.found, solo.status);

    // A lemma after the last public block (trailing, not anchored).
    const trailing_src =
        \\t
        \\----
        \\l1: $ P $ by p []
        \\
        \\lemma l: $ P $
        \\----
        \\l1: $ P $ by exact?
    ;
    var trailing = try source.suggestionsAtSourceOffset(
        arena.allocator(),
        mm0_src,
        trailing_src,
        std.mem.indexOf(u8, trailing_src, "exact?").?,
        .{},
    );
    defer trailing.deinit();
    try std.testing.expect(trailing.items.len > 0);
    try std.testing.expectEqual(types.SearchStatus.found, trailing.status);
}

// Minimal one-sided ACUI sequent theory exercising the unbound-repeated-binder
// branch of `closedAcuiTemplateMismatch` (repeatedBinderMemberMismatch): the
// `ax`-style closing rule `⊢ a , (~ a) , d` repeats the wff binder `a` across two
// ACUI succedent members with no rigid anchor, so nothing binds `a` before
// validation. A goal with no complementary literal pair can never close by `ax`,
// and the prune must reject it (cheaply, before `tryCandidate`) — while a goal
// that does have the pair must still be found.
const one_sided_ax_mm0 =
    \\delimiter $ ( ) $;
    \\provable sort wff;
    \\sort ctx;
    \\term ctx_eq (g h: ctx): wff;
    \\term emp: ctx;
    \\--| @acui ctx_assoc ctx_comm emp ctx_idem
    \\term join (g h: ctx): ctx;
    \\infixl join: $,$ prec 5;
    \\term hyp (a: wff): ctx;
    \\coercion hyp: wff > ctx;
    \\term seq (d: ctx): wff;
    \\prefix seq: $|-$ prec 1;
    \\term lnot (a: wff): wff;
    \\prefix lnot: $~$ prec 40;
    \\term P: wff;
    \\term Q: wff;
    \\term R: wff;
    \\--| @relation ctx ctx_eq ctx_refl ctx_trans ctx_sym _
    \\axiom ctx_refl (g: ctx): $ ctx_eq g g $;
    \\axiom ctx_trans (g h i: ctx): $ ctx_eq g h $ > $ ctx_eq h i $ > $ ctx_eq g i $;
    \\axiom ctx_sym (g h: ctx): $ ctx_eq g h $ > $ ctx_eq h g $;
    \\axiom ctx_assoc (g h i: ctx): $ ctx_eq ( ( g , h ) , i ) ( g , ( h , i ) ) $;
    \\axiom ctx_comm (g h: ctx): $ ctx_eq ( g , h ) ( h , g ) $;
    \\axiom ctx_idem (g: ctx): $ ctx_eq ( g , g ) g $;
    \\axiom ax (d: ctx) (a: wff): $ |- a , ( ~ a ) , d $;
    \\term lor (a b: wff): wff;
    \\infixl lor: $v$ prec 20;
    \\axiom ror (d: ctx) (a b: wff): $ |- a , b , d $ > $ |- ( a v b ) , d $;
    \\theorem good: $ |- P , ( ~ P ) , R $;
    \\theorem bad: $ |- P , ( ~ Q ) , R $;
    \\theorem orgood: $ |- ( P v Q ) , R $;
;

// Directly exercises the unbound-repeated-binder branch through the public
// `finalConclusionPlausible`, with `ax`'s binders left unbound (the open-backward
// state the seed can't pin). A goal WITH a complementary pair must stay plausible
// (never drop a winnable candidate); a goal WITHOUT one must be refuted (pruned)
// and must bump `final_conclusion_prunes`. This isolates the branch regardless of
// whether a full search happens to reach it.
test "repeated-binder prune refutes a doomed ax and spares a valid one" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();

    var fixture = try fixtureFor(allocator, one_sided_ax_mm0, "good");
    var theorem = TheoremContext.init(allocator);
    defer theorem.deinit();
    try theorem.seedAssertion(fixture.assertion);
    var theorem_vars = try Check.buildTheoremVarMap(allocator, fixture.assertion);
    defer theorem_vars.deinit();
    var harness = ContextHarness.init(allocator);
    defer harness.deinit();
    const context = harness.context(&fixture);

    // Both goals interned into `theorem` before the candidate clone below, so the
    // clone (which preserves ExprIds) resolves either.
    const good_goal = try parseGoal(&fixture, &theorem, &theorem_vars, "|- P , ( ~ P ) , R");
    const bad_goal = try parseGoal(&fixture, &theorem, &theorem_vars, "|- P , ( ~ Q ) , R");

    var ax_id: ?u32 = null;
    for (context.env.rules.items, 0..) |rule, i| {
        if (std.mem.eql(u8, rule.name, "ax")) ax_id = @intCast(i);
    }
    const rid = ax_id orelse return error.MissingAxRule;

    // All of `ax`'s binders (`d`, `a`) left unbound — the open state.
    const nbind = context.env.rules.items[rid].args.len;
    const bindings = try allocator.alloc(?ExprId, nbind);
    @memset(bindings, null);

    var candidate = types.ApplyCandidate{
        .allocator = allocator,
        .rule_id = rid,
        .rule_name = "ax",
        .declaration_order = 0,
        .theorem = try theorem.clone(),
        .bindings = try allocator.alloc(?ExprId, 0),
        .conclusion = good_goal.concrete,
        .unresolved_hyps = try allocator.alloc(types.UnresolvedHypothesis, 0),
    };
    defer candidate.deinit();

    // `finalConclusionPlausible` returns whether the candidate could still match;
    // `false` is the prune (its caller, `validateSelectedRefs`, is what bumps the
    // `final_conclusion_prunes` counter — not exercised here).
    // Complementary pair present → the branch finds a consistent `a := P` and must
    // NOT prune.
    try std.testing.expect(plausible.finalConclusionPlausible(
        &context,
        &candidate,
        good_goal,
        bindings,
        null,
    ));
    // No complementary pair → no value of `a` covers both `a` and `~ a`, so the
    // branch refutes it before any `tryCandidate`.
    try std.testing.expect(!plausible.finalConclusionPlausible(
        &context,
        &candidate,
        bad_goal,
        bindings,
        null,
    ));
}

// Directly exercises the hyp-vs-ref member-consistency check with `ror`'s
// binders left unbound (the loose-candidate state a one-sided ACUI conclusion
// forces: seeding never descends the region, so the premise slot is a wildcard
// sequent that would otherwise pair with every pool line through a full
// `tryCandidate`). The valid premise must stay plausible; a ref carrying a
// member no assignment derives (direction 1) and a ref missing a member the
// rest binder must carry (direction 3) must both be refuted.
test "hyp-ref member prune refutes doomed premise refs and spares the valid one" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();

    var fixture = try fixtureFor(allocator, one_sided_ax_mm0, "orgood");
    var theorem = TheoremContext.init(allocator);
    defer theorem.deinit();
    try theorem.seedAssertion(fixture.assertion);
    var theorem_vars = try Check.buildTheoremVarMap(allocator, fixture.assertion);
    defer theorem_vars.deinit();
    var harness = ContextHarness.init(allocator);
    defer harness.deinit();
    const context = harness.context(&fixture);

    const goal = try parseGoal(&fixture, &theorem, &theorem_vars, "|- ( P v Q ) , R");
    const good_ref = try parseGoal(&fixture, &theorem, &theorem_vars, "|- P , Q , R");
    const missing_ref = try parseGoal(&fixture, &theorem, &theorem_vars, "|- P , Q");
    const alien_ref = try parseGoal(&fixture, &theorem, &theorem_vars, "|- P , ( ~ P ) , R");

    var ror_id: ?u32 = null;
    for (context.env.rules.items, 0..) |rule, i| {
        if (std.mem.eql(u8, rule.name, "ror")) ror_id = @intCast(i);
    }
    const rid = ror_id orelse return error.MissingRorRule;

    // All of `ror`'s binders (`d`, `a`, `b`) unbound — the loose state.
    const nbind = context.env.rules.items[rid].args.len;
    const bindings = try allocator.alloc(?ExprId, nbind);
    @memset(bindings, null);

    // The true premise `⊢ P , Q , R` is consistent under `a v b := P v Q`.
    try std.testing.expect(plausible.hypRefMembersPlausible(
        &context,
        &theorem,
        rid,
        goal,
        bindings,
        &[_]?ExprId{good_ref.concrete},
    ));
    // `⊢ P , ( ~ P ) , R` holds a member (`~ P`) no assignment derives.
    try std.testing.expect(!plausible.hypRefMembersPlausible(
        &context,
        &theorem,
        rid,
        goal,
        bindings,
        &[_]?ExprId{alien_ref.concrete},
    ));
    // `⊢ P , Q` is missing `R`, which the rest binder `d` must carry.
    try std.testing.expect(!plausible.hypRefMembersPlausible(
        &context,
        &theorem,
        rid,
        goal,
        bindings,
        &[_]?ExprId{missing_ref.concrete},
    ));
    // A generated (non-pool) slot gives the check nothing to judge — abstain.
    try std.testing.expect(plausible.hypRefMembersPlausible(
        &context,
        &theorem,
        rid,
        goal,
        bindings,
        &[_]?ExprId{null},
    ));
}

// Generation-order witness classes (`witnessClass`): a rule not enrolled in
// `@auto backward` is class 0; an enrolled rule whose every hypothesis binder
// is conclusion-determined is class 1; an enrolled rule with a premise-only
// binder — a witness backward application must defer as an existential meta
// (tait's `rex`, or `mp`'s antecedent) — is class 2. The 1-vs-2 split is what
// orders a one-sided calculus (where EVERY rule is enrolled, so the
// annotation alone distinguishes nothing) so the invertible ladder runs
// before the witness contraction cascade.
const witness_class_mm0 =
    \\delimiter $ ( ) $;
    \\provable sort wff;
    \\term im (a b: wff): wff;
    \\infixr im: $->$ prec 25;
    \\term an (a b: wff): wff;
    \\infixl an: $&$ prec 20;
    \\term P: wff;
    \\axiom ax_id (a: wff): $ a -> a $;
    \\--| @auto backward
    \\axiom andi (a b: wff): $ a $ > $ b $ > $ ( a & b ) $;
    \\--| @auto backward
    \\axiom mp (a b: wff): $ ( a -> b ) $ > $ a $ > $ b $;
    \\theorem t: $ P -> P $;
;

test "witnessClass splits un-enrolled, conclusion-determined, and witness rules" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();

    var fixture = try fixtureFor(allocator, witness_class_mm0, "t");
    var harness = ContextHarness.init(allocator);
    defer harness.deinit();
    const context = harness.context(&fixture);

    var by_name = [_]struct { name: []const u8, class: u8 }{
        .{ .name = "ax_id", .class = 0 }, // not enrolled
        .{ .name = "andi", .class = 1 }, // enrolled, binders in conclusion
        .{ .name = "mp", .class = 2 }, // enrolled, `a` is premise-only
    };
    for (&by_name) |expected| {
        var rule_id: ?u32 = null;
        for (context.env.rules.items, 0..) |rule, i| {
            if (std.mem.eql(u8, rule.name, expected.name)) rule_id = @intCast(i);
        }
        const rid = rule_id orelse return error.MissingRule;
        try std.testing.expectEqual(
            expected.class,
            backtrack.witnessClass(&context, rid),
        );
    }
}

test "searchPlaceholders enumerates top-level and nested placeholders" {
    const proof_src =
        \\t
        \\----
        \\l1: $ P $ by exact?
        \\l2: $ Q $ by keep [auto?]
        \\l3: $ R $ by apply?
    ;
    const placeholders = try source.searchPlaceholders(
        std.testing.allocator,
        proof_src,
    );
    defer std.testing.allocator.free(placeholders);

    try std.testing.expectEqual(@as(usize, 3), placeholders.len);
    try std.testing.expectEqual(
        source.SearchPlaceholder.Kind.exact,
        placeholders[0].kind,
    );
    try std.testing.expectEqual(
        source.SearchPlaceholder.Kind.auto,
        placeholders[1].kind,
    );
    try std.testing.expectEqual(
        source.SearchPlaceholder.Kind.apply,
        placeholders[2].kind,
    );
    // Each span covers the placeholder application text itself.
    const auto_offset = std.mem.indexOf(u8, proof_src, "auto?").?;
    try std.testing.expectEqual(auto_offset, placeholders[1].span.start);
    try std.testing.expectEqualStrings(
        "exact?",
        proof_src[placeholders[0].span.start..placeholders[0].span.end],
    );
}
