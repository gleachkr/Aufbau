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
const Canonicalizer = @import("../../../canonicalizer.zig").Canonicalizer;
const TheoremContext = helpers.TheoremContext;
const Check = helpers.Check;
const apply = helpers.apply;
const exact = helpers.exact;
const fixtureFor = helpers.fixtureFor;
const parseGoal = helpers.parseGoal;
const expectTimingCounter = helpers.expectTimingCounter;
const ContextHarness = helpers.ContextHarness;
const expectApplyContains = helpers.expectApplyContains;
const expectInlineSearch = helpers.expectInlineSearch;
const suggestionsAtNeedle = helpers.suggestionsAtNeedle;
const expectOffered = helpers.expectOffered;

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
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    var suggestions = try suggestionsAtNeedle(
        &arena,
        mm0_src,
        proof_src,
        "exact?",
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
    var found = try suggestionsAtNeedle(
        &arena,
        mm0_src,
        found_src,
        "exact?",
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
    var miss = try suggestionsAtNeedle(
        &arena,
        mm0_src,
        miss_src,
        "exact?",
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
    var suggestions = try suggestionsAtNeedle(
        &arena,
        mm0_src,
        proof_src,
        "exact?",
        .{},
    );
    defer suggestions.deinit();
    try std.testing.expect(suggestions.items.len > 0);
    try std.testing.expectEqual(types.SearchStatus.found, suggestions.status);
}

// An earlier placeholder line is admitted like `sorry!` when its assertion
// is concrete, so a later search can cite it. A holey one is unfinished; a
// line citing it is admitted on its own concrete assertion.
test "source suggestions cite earlier placeholder lines" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\--| @hole HOLE
        \\provable sort wff;
        \\term P: wff;
        \\term Q: wff;
        \\term R: wff;
        \\axiom pq: $ P $ > $ Q $;
        \\axiom qr: $ Q $ > $ R $;
        \\theorem t: $ R $;
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    const concrete_src =
        \\t
        \\---
        \\l1: $ Q $ by apply?
        \\l2: $ R $ by exact?
    ;
    var concrete = try suggestionsAtNeedle(
        &arena,
        mm0_src,
        concrete_src,
        "exact?",
        .{},
    );
    defer concrete.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, concrete.status);
    try expectOffered(concrete.items, &.{"qr [l1]"});

    const holey_src =
        \\t
        \\---
        \\l1: $ HOLE $ by apply?
        \\l2: $ Q $ by pq [l1]
        \\l3: $ R $ by exact?
    ;
    var holey = try suggestionsAtNeedle(
        &arena,
        mm0_src,
        holey_src,
        "exact?",
        .{},
    );
    defer holey.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, holey.status);
    try expectOffered(holey.items, &.{"qr [l2]"});
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
    var suggestions = try suggestionsAtNeedle(
        &arena,
        mm0_src,
        proof_src,
        "exact?",
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

test "placeholderNotices warns per placeholder and rejects bad parameters" {
    const proof_src =
        \\t
        \\----
        \\l1: $ P $ by exact?
        \\l2: $ Q $ by auto? (depht: 8, depth: 2)
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const notices = try source.placeholderNotices(arena.allocator(), proof_src);

    try std.testing.expectEqual(@as(usize, 3), notices.len);
    try std.testing.expectEqual(.placeholder, notices[0].kind);
    try std.testing.expectEqualStrings(
        "exact? placeholder: search not yet run " ++
            "(request code actions here to search)",
        notices[0].message,
    );
    try std.testing.expectEqual(.placeholder, notices[1].kind);
    try std.testing.expectEqual(
        source.SearchPlaceholder.Kind.auto,
        notices[1].placeholder.kind,
    );
    // Only the misspelt name is rejected, on its own span.
    try std.testing.expectEqual(.parameter, notices[2].kind);
    try std.testing.expectEqualStrings(
        "depht",
        proof_src[notices[2].span.start..notices[2].span.end],
    );
}

// Local def and notation items are not blocks. The editor-facing walkers must
// step over them rather than stop (enumeration) or fail (targeting) there.
test "searchPlaceholders enumerates past local def and notation items" {
    const proof_src =
        \\def limp (a b: wff): wff = $ a -> b $
        \\infixr limp: $=>$ prec 25;
        \\
        \\t
        \\----
        \\l1: $ Q $ by auto?
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

test "source suggestions target a line after local def and notation items" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term imp (a b: wff): wff;
        \\infixr imp: $->$ prec 25;
        \\term P: wff;
        \\term Q: wff;
        \\axiom p: $ P $;
        \\axiom q: $ Q $;
        \\theorem t: $ Q $;
    ;
    const proof_src =
        \\def limp (a b: wff): wff = $ a -> b $
        \\infixr limp: $=>$ prec 25;
        \\
        \\t
        \\----
        \\l1: $ Q $ by exact?
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var suggestions = try suggestionsAtNeedle(
        &arena,
        mm0_src,
        proof_src,
        "exact?",
        .{},
    );
    defer suggestions.deinit();
    try std.testing.expect(suggestions.items.len > 0);
    try std.testing.expectEqual(types.SearchStatus.found, suggestions.status);
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
    var solo = try suggestionsAtNeedle(
        &arena,
        mm0_src,
        solo_src,
        "exact?",
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
    var trailing = try suggestionsAtNeedle(
        &arena,
        mm0_src,
        trailing_src,
        "exact?",
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
        .{},
        null,
    ));
    // No complementary pair → no value of `a` covers both `a` and `~ a`, so the
    // branch refutes it before any `tryCandidate`.
    try std.testing.expect(!plausible.finalConclusionPlausible(
        &context,
        &candidate,
        bad_goal,
        bindings,
        .{},
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

// Three rules share the shape `P (f y x) x` and differ only in the head `f`:
// a primitive `h`, a def `K` that drops its second argument, and a `@rewrite`
// head `k2` that reduces to its first. Against `P (f a b) c` the re-pin may pin
// `x := b` only through `h`: `K a b ≡ K a c` and `k2 a b ≡ k2 a c`, so there
// `x := c` is still possible and pinning `x := b` would refute it.
const repin_heads_mm0 =
    \\delimiter $ ( ) $;
    \\provable sort wff;
    \\sort obj;
    \\term bi (a b: wff): wff;
    \\infixl bi: $<->$ prec 5;
    \\--| @relation wff bi biid bitr bisym mpbi
    \\axiom biid (a: wff): $ a <-> a $;
    \\axiom bitr (a b c: wff): $ a <-> b $ > $ b <-> c $ > $ a <-> c $;
    \\axiom bisym (a b: wff): $ a <-> b $ > $ b <-> a $;
    \\axiom mpbi (a b: wff): $ a <-> b $ > $ a $ > $ b $;
    \\term oeq (a b: obj): wff;
    \\infixl oeq: $==$ prec 10;
    \\--| @relation obj oeq oeq_refl oeq_trans oeq_sym _
    \\axiom oeq_refl (a: obj): $ a == a $;
    \\axiom oeq_trans (a b c: obj): $ a == b $ > $ b == c $ > $ a == c $;
    \\axiom oeq_sym (a b: obj): $ a == b $ > $ b == a $;
    \\term P (a b: obj): wff;
    \\--| @congr
    \\axiom P_congr (a b c d: obj): $ a == b $ > $ c == d $ > $ P a c <-> P b d $;
    \\term h (a b: obj): obj;
    \\def K (a b: obj): obj = $ a $;
    \\term k2 (a b: obj): obj;
    \\--| @congr
    \\axiom k2_congr (a b c d: obj): $ a == b $ > $ c == d $ > $ k2 a c == k2 b d $;
    \\--| @rewrite
    \\axiom k2_drop (a b: obj): $ k2 a b == a $;
    \\axiom r_h (y x: obj): $ P (h y x) x $;
    \\axiom r_K (y x: obj): $ P (K y x) x $;
    \\axiom r_k2 (y x: obj): $ P (k2 y x) x $;
    \\term R (a: obj): wff;
    \\term Q (a: obj): wff;
    \\axiom r3 (y x: obj): $ R y $ > $ Q x $ > $ P (k2 y x) x $;
    \\axiom r3K (y x: obj): $ R y $ > $ Q x $ > $ P (K y x) x $;
    \\theorem t (a b c: obj): $ P (k2 a b) c $;
    \\theorem t3 (a b c: obj): $ R a $ > $ Q c $ > $ P (k2 a b) c $;
    \\theorem t3K (a b c: obj): $ R a $ > $ Q c $ > $ P (K a b) c $;
;

test "re-pin descends only into arguments the head determines" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();

    var fixture = try fixtureFor(allocator, repin_heads_mm0, "t");
    var theorem = TheoremContext.init(allocator);
    defer theorem.deinit();
    try theorem.seedAssertion(fixture.assertion);
    var theorem_vars = try Check.buildTheoremVarMap(allocator, fixture.assertion);
    defer theorem_vars.deinit();
    var harness = ContextHarness.init(allocator);
    defer harness.deinit();
    const context = harness.context(&fixture);

    const cases = [_]struct { rule: []const u8, goal: []const u8, plausible: bool }{
        .{ .rule = "r_h", .goal = "P (h a b) c", .plausible = false },
        .{ .rule = "r_K", .goal = "P (K a b) c", .plausible = true },
        .{ .rule = "r_k2", .goal = "P (k2 a b) c", .plausible = true },
    };
    var goals: [cases.len]types.Goal = undefined;
    for (cases, &goals) |case, *goal| {
        goal.* = try parseGoal(&fixture, &theorem, &theorem_vars, case.goal);
    }
    var failed = false;
    for (cases, goals) |case, goal| {
        const rid = context.env.getRuleId(case.rule) orelse
            return error.MissingRule;
        // Both binders unbound: the seed nulls `x` on its conflicting
        // occurrences, and `y` is left for the re-pin to fill.
        const bindings = try allocator.alloc(?ExprId, 2);
        @memset(bindings, null);
        var candidate = types.ApplyCandidate{
            .allocator = allocator,
            .rule_id = rid,
            .rule_name = case.rule,
            .declaration_order = 0,
            .theorem = try theorem.clone(),
            .bindings = try allocator.alloc(?ExprId, 0),
            .conclusion = goal.concrete,
            .unresolved_hyps = try allocator.alloc(types.UnresolvedHypothesis, 0),
        };
        defer candidate.deinit();
        const actual = plausible.finalConclusionPlausible(
            &context,
            &candidate,
            goal,
            bindings,
            .{ .repin_prune_enabled = true },
            null,
        );
        if (actual != case.plausible) {
            std.debug.print("rule {s}: expected plausible={}\n", .{ case.rule, case.plausible });
            failed = true;
        }
    }
    try std.testing.expect(!failed);
}

test "folded-body check compares only determined args of a same-head @rewrite" {
    // `y := k2 a b` against the goal's `k2 a c`: both reduce to `a`, so the
    // differing second argument is no mismatch.
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    const mm0_src = repin_heads_mm0 ++
        \\axiom r_y (y x: obj): $ P y x $;
        \\theorem t_y (a b c: obj): $ P (k2 a c) c $;
    ;

    var fixture = try fixtureFor(allocator, mm0_src, "t_y");
    var theorem = TheoremContext.init(allocator);
    defer theorem.deinit();
    try theorem.seedAssertion(fixture.assertion);
    var theorem_vars = try Check.buildTheoremVarMap(allocator, fixture.assertion);
    defer theorem_vars.deinit();
    var harness = ContextHarness.init(allocator);
    defer harness.deinit();
    const context = harness.context(&fixture);

    const goal = try parseGoal(&fixture, &theorem, &theorem_vars, "P (k2 a c) c");
    const other = try parseGoal(&fixture, &theorem, &theorem_vars, "P (k2 a b) c");
    const y_value = theorem.interner.node(other.concrete).app.args[0];
    const rule_id = fixture.env.getRuleId("r_y") orelse return error.MissingRule;
    const bindings = try allocator.dupe(?ExprId, &.{ y_value, null });
    var candidate = types.ApplyCandidate{
        .allocator = allocator,
        .rule_id = rule_id,
        .rule_name = "r_y",
        .declaration_order = 0,
        .theorem = try theorem.clone(),
        .bindings = try allocator.alloc(?ExprId, 0),
        .conclusion = goal.concrete,
        .unresolved_hyps = try allocator.alloc(types.UnresolvedHypothesis, 0),
    };
    defer candidate.deinit();
    try std.testing.expect(plausible.finalConclusionPlausible(
        &context,
        &candidate,
        goal,
        bindings,
        .{ .repin_prune_enabled = true },
        null,
    ));
}

test "a stuck @rewrite redex clashes with a rigid conclusion head" {
    // `sb_irrel` fires only when `p` does not depend on `x`. With `p: wff x`
    // the redex `sb x t p` is in normal form, so it can never become an `an`;
    // with `q: wff` it reduces to `q`, which an instance of `an a b` may be.
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\sort obj;
        \\term bi (a b: wff): wff;
        \\infixl bi: $<->$ prec 5;
        \\--| @relation wff bi biid bitr bisym mpbi
        \\axiom biid (a: wff): $ a <-> a $;
        \\axiom bitr (a b c: wff): $ a <-> b $ > $ b <-> c $ > $ a <-> c $;
        \\axiom bisym (a b: wff): $ a <-> b $ > $ b <-> a $;
        \\axiom mpbi (a b: wff): $ a <-> b $ > $ a $ > $ b $;
        \\term an (a b: wff): wff;
        \\term sb {x: obj} (t: obj) (p: wff x): wff;
        \\--| @rewrite
        \\axiom sb_irrel {x: obj} (t: obj) (p: wff): $ sb x t p <-> p $;
        \\axiom r_an (a b: wff): $ an a b $;
        \\theorem t {x: obj} (t: obj) (p: wff x) (q: wff): $ sb x t p $;
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();

    var fixture = try fixtureFor(allocator, mm0_src, "t");
    var theorem = TheoremContext.init(allocator);
    defer theorem.deinit();
    try theorem.seedAssertion(fixture.assertion);
    var theorem_vars = try Check.buildTheoremVarMap(allocator, fixture.assertion);
    defer theorem_vars.deinit();
    var harness = ContextHarness.init(allocator);
    defer harness.deinit();
    const context = harness.context(&fixture);

    const stuck = (try parseGoal(&fixture, &theorem, &theorem_vars, "sb x t p")).concrete;
    const reducible = (try parseGoal(&fixture, &theorem, &theorem_vars, "sb x t q")).concrete;
    try std.testing.expect(helpers.def_match.stuckRedex(&context, &theorem, stuck));
    try std.testing.expect(!helpers.def_match.stuckRedex(&context, &theorem, reducible));

    const rule_id = fixture.env.getRuleId("r_an") orelse return error.MissingRule;
    const concl = fixture.env.rules.items[rule_id].concl;
    const unbound = [_]?ExprId{ null, null };
    try std.testing.expect(helpers.def_match.templateDefiniteMismatch(
        &context,
        &theorem,
        concl,
        stuck,
        &unbound,
    ));
    try std.testing.expect(!helpers.def_match.templateDefiniteMismatch(
        &context,
        &theorem,
        concl,
        reducible,
        &unbound,
    ));
}

test "a @rewrite head that is also a def or an ACUI combiner is never stuck" {
    // The canonicalizer fires no rewrite on either term, yet the checker
    // changes both: it unfolds `sbd x t p` to `an p p`, an instance of
    // `an a b`, and its normalizer rewrites `join (hyp q) (hyp r)` by
    // `join_hyp`, which the canonicalizer never tries on an ACUI head.
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\sort obj;
        \\sort ctx;
        \\term bi (a b: wff): wff;
        \\infixl bi: $<->$ prec 5;
        \\--| @relation wff bi biid bitr bisym mpbi
        \\axiom biid (a: wff): $ a <-> a $;
        \\axiom bitr (a b c: wff): $ a <-> b $ > $ b <-> c $ > $ a <-> c $;
        \\axiom bisym (a b: wff): $ a <-> b $ > $ b <-> a $;
        \\axiom mpbi (a b: wff): $ a <-> b $ > $ a $ > $ b $;
        \\term an (a b: wff): wff;
        \\def sbd {x: obj} (t: obj) (p: wff x): wff = $ an p p $;
        \\--| @rewrite
        \\axiom sbd_irrel {x: obj} (t: obj) (p: wff): $ sbd x t p <-> p $;
        \\axiom r_an (a b: wff): $ an a b $;
        \\term ctx_eq (g h: ctx): wff;
        \\term emp: ctx;
        \\--| @acui ctx_assoc ctx_comm emp ctx_idem
        \\term join (g h: ctx): ctx;
        \\term hyp (a: wff): ctx;
        \\--| @relation ctx ctx_eq ctx_refl ctx_trans ctx_sym _
        \\axiom ctx_refl (g: ctx): $ ctx_eq g g $;
        \\axiom ctx_trans (g h i: ctx): $ ctx_eq g h $ > $ ctx_eq h i $ > $ ctx_eq g i $;
        \\axiom ctx_sym (g h: ctx): $ ctx_eq g h $ > $ ctx_eq h g $;
        \\axiom ctx_assoc (g h i: ctx): $ ctx_eq (join (join g h) i) (join g (join h i)) $;
        \\axiom ctx_comm (g h: ctx): $ ctx_eq (join g h) (join h g) $;
        \\axiom ctx_idem (g: ctx): $ ctx_eq (join g g) g $;
        \\--| @rewrite
        \\axiom join_hyp (a b: wff): $ ctx_eq (join (hyp a) (hyp b)) (hyp (an a b)) $;
        \\theorem t {x: obj} (t: obj) (p: wff x) (q r: wff) (g: ctx): $ sbd x t p $;
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();

    var fixture = try fixtureFor(allocator, mm0_src, "t");
    var theorem = TheoremContext.init(allocator);
    defer theorem.deinit();
    try theorem.seedAssertion(fixture.assertion);
    var theorem_vars = try Check.buildTheoremVarMap(allocator, fixture.assertion);
    defer theorem_vars.deinit();
    var harness = ContextHarness.init(allocator);
    defer harness.deinit();
    const context = harness.context(&fixture);

    const def_redex = (try parseGoal(&fixture, &theorem, &theorem_vars, "sbd x t p")).concrete;
    const bag_eq = (try parseGoal(&fixture, &theorem, &theorem_vars, "ctx_eq (join (hyp q) (hyp r)) g")).concrete;
    // Put the bag in canonical order first, so only the head's class can make
    // it not stuck.
    var canon = Canonicalizer.init(allocator, &theorem, context.registry, context.env);
    defer canon.cache.deinit();
    const raw_bag = theorem.interner.node(bag_eq).app.args[0];
    const bag = try canon.canonicalize(raw_bag);
    try std.testing.expectEqual(
        theorem.interner.node(raw_bag).app.term_id,
        theorem.interner.node(bag).app.term_id,
    );
    try std.testing.expect(!helpers.def_match.stuckRedex(&context, &theorem, def_redex));
    try std.testing.expect(!helpers.def_match.stuckRedex(&context, &theorem, bag));

    const rule_id = fixture.env.getRuleId("r_an") orelse return error.MissingRule;
    const unbound = [_]?ExprId{ null, null };
    try std.testing.expect(!helpers.def_match.templateDefiniteMismatch(
        &context,
        &theorem,
        fixture.env.rules.items[rule_id].concl,
        def_redex,
        &unbound,
    ));
}

// End to end: a rule that repeats `x` proves `P (_ a b) c` with `x := c`
// when the head drops its second argument, so the conclusion prunes must not
// force `x := b` from the goal.
// - `k2` is a `@rewrite` head: normalization reduces both `k2` sides to `a`,
//   so the hypothesis-free `r_k2` and `r3` (whose `x` comes from `Q c`) both
//   prove `P (k2 a b) c`.
// - `K` is an erasing def: `K a b ≡ K a c` once `K` unfolds, so
//   `r3K [#1, #2]` proves `P (K a b) c` (the checker accepts it).
test "search keeps a rule whose repeated binder sits under an erasing head" {
    const cases = [_]struct { proof: []const u8, offered: []const []const u8 }{
        .{
            .proof =
            \\t3
            \\----
            \\l1: $ P (k2 a b) c $ by exact?
            ,
            .offered = &.{ "r_k2", "r3 [#1, #2]" },
        },
        .{
            .proof =
            \\t3K
            \\-----
            \\l1: $ P (K a b) c $ by exact?
            ,
            .offered = &.{"r3K [#1, #2]"},
        },
    };
    for (cases) |case| {
        var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
        defer arena.deinit();
        var found = try suggestionsAtNeedle(
            &arena,
            repin_heads_mm0,
            case.proof,
            "exact?",
            .{},
        );
        defer found.deinit();
        try expectOffered(found.items, case.offered);
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

fn suggestionStartingWith(
    suggestions: []const types.SourceSuggestion,
    prefix: []const u8,
) ?types.SourceSuggestion {
    for (suggestions) |item| {
        if (std.mem.startsWith(u8, item.replacement, prefix)) return item;
    }
    return null;
}

// #262: the search fixture walks the `.mm0` through the same helper as the
// compile and analyze paths, so it mirrors the parser's coercions into its
// env. `ex_intro`'s @recover crosses sorts (a `tm` hole recovered from a
// `name` instance), which enrolls only when the env knows `name > tm`;
// without the mirror the fixture rejected the axiom's annotations and every
// search in the theory failed before it started. The search's own recover
// pre-filter then has to read a coercion chain around the hole as the
// recovery site it is, or `ex_intro` is never tried.
test "source search sees coercions: a cross-sort @recover rule is searchable" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    const mm0_src = try helpers.readProofCase(
        allocator,
        "pass_ex_elim_infer_two_sort",
        "mm0",
    );

    // The fixture's env carries the theory's three coercions.
    var fixture = try fixtureFor(allocator, mm0_src, "ex_open");
    try std.testing.expectEqual(@as(usize, 3), fixture.env.coercions.items.len);
    try std.testing.expect(fixture.env.getRuleId("ex_intro") != null);

    const proof_src =
        \\ex_open
        \\-------
        \\
        \\l1: $ ∃ x (F x) ⊢ ∃ x (F x) $ by ax
        \\l2: $ F b ⊢ F b $ by ax
        \\l3: $ F b ⊢ ∃ x (F x) $ by exact?
        \\l4: $ ∃ x (F x) ⊢ ∃ x (F x) $ by ex_elim [l1, l3]
    ;
    var suggestions = try suggestionsAtNeedle(
        &arena,
        mm0_src,
        proof_src,
        "exact?",
        .{},
    );
    defer suggestions.deinit();

    const suggestion = suggestionStartingWith(suggestions.items, "ex_intro") orelse {
        return error.MissingSuggestion;
    };
    try std.testing.expectEqualStrings("ex_intro [l2]", suggestion.replacement);
    // What the search offers is exactly what the compile path accepts.
    try helpers.expectConversionCompiles(&arena, mm0_src, proof_src, suggestion);
}

// #262: the fixture recovers the way the analysis does, so a broken
// declaration or local item earlier in the file no longer silences the
// search of every theorem after it. The four failures here take the four
// recovery routes: an `.mm0` parse error, rejected annotations, a duplicate
// rule, and a lemma whose proof does not check.
test "source search survives broken statements before the target" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term P: wff;
        \\term Q: wff;
        \\axiom p: $ P $;
        \\axiom bad_parse: $ R $;
        \\--| @fallback missing
        \\axiom bad_annotation: $ Q $;
        \\axiom dup: $ Q $;
        \\axiom dup: $ Q $;
        \\theorem t: $ P $;
    ;
    const proof_src =
        \\lemma wrong: $ Q $
        \\------------------
        \\l1: $ Q $ by p
        \\
        \\t
        \\----
        \\l1: $ P $ by exact?
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var suggestions = try suggestionsAtNeedle(
        &arena,
        mm0_src,
        proof_src,
        "exact?",
        .{},
    );
    defer suggestions.deinit();

    try std.testing.expect(suggestions.target_span != null);
    const suggestion = suggestionStartingWith(suggestions.items, "p") orelse {
        return error.MissingSuggestion;
    };
    try std.testing.expectEqualStrings("p", suggestion.replacement);
    // The dropped declarations left no rule behind for the search to cite.
    try std.testing.expect(suggestionStartingWith(suggestions.items, "dup") == null);
    try std.testing.expect(suggestionStartingWith(suggestions.items, "wrong") == null);
}

// The target itself must be intact: a theorem that names a declaration the
// walk dropped is what the analysis marks invalid without checking.
test "source search declines a target that depends on a dropped declaration" {
    // `bad`'s body depends on a dummy its result type does not declare:
    // the parser accepts it, definition validation rejects it.
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\sort obj;
        \\term P (a: obj): wff;
        \\def bad {.x: obj}: obj = $ x $;
        \\axiom p (a: obj): $ P a $;
        \\theorem t: $ P bad $;
    ;
    const proof_src =
        \\t
        \\----
        \\l1: $ P bad $ by exact?
    ;
    const offset = std.mem.indexOf(u8, proof_src, "exact?") orelse {
        return error.MissingNeedle;
    };
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    try std.testing.expectError(
        error.UnavailableDependency,
        source.suggestionsAtSourceOffset(
            arena.allocator(),
            mm0_src,
            proof_src,
            offset,
            .{},
        ),
    );
}

// ---------------------------------------------------------------------------
// Binding trimming through the `BindingOracle` (#374). Each case is an nd_fol
// line whose bare suggestion fails, so trimming needs the oracle, and needs
// the named part of it; `suggestionsAtNeedle` fails any suggestion that comes
// back untrimmed.
// ---------------------------------------------------------------------------

fn expectNdFolTrim(proof_src: []const u8, expected: []const u8) !void {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const mm0_src = try std.fs.cwd().readFileAlloc(
        arena.allocator(),
        "tests/search_bench_cases/nd_fol.mm0",
        std.math.maxInt(usize),
    );
    var suggestions = try suggestionsAtNeedle(&arena, mm0_src, proof_src, "auto?", .{
        .max_results = 3,
        .exact_result_limit = 1,
        .generate = .{ .enabled = true },
    });
    defer suggestions.deinit();
    try expectOffered(suggestions.items, &.{expected});
}

test "trimming supplies an inline sub-proof the binders its hint lacks" {
    // `weak [l2]` gets no hint from a bare `all_left`; the retry supplies the
    // `t` its premise leaves open.
    try expectNdFolTrim(
        \\vac_all_or
        \\----------
        \\l1: $ (∀ x (s0 ∨ s0)) , s0 ⊢ s0 $ by ax
        \\l2: $ (∀ x (s0 ∨ s0)) , (s0 ∨ s0) ⊢ s0 $ by or_left [l1, l1]
        \\l4: $ ∅ ⊢ (∀ x (s0 ∨ s0)) → s0 $ by auto?
    ,
        "imp_intro [all_left (t := $ u $) [weak [l2]]]",
    );
}

test "trimming forces the binders an inline sub-proof proved past" {
    // Under a bare `not_left`, `ex_intro [ax []]` checks against a weak hint
    // and proves something other than `not_left`'s premise; `not_left`'s
    // binders are then supplied before inference, and `ex_intro`'s `p`,
    // forced along with them, is dropped again.
    try expectNdFolTrim(
        \\not_ex_to_all_not
        \\-----------------
        \\l6: $ ∅ ⊢ (¬ ∃ x P x) → ∀ y (¬ P y) $ by auto?
    ,
        "imp_intro [all_intro [not_intro [not_left (g := $ P y $, a := $ ∃ x P x $) " ++
            "[ex_intro (t := $ y $) [ax []]]]]]",
    );
}

test "trimming accepts an inferred binder equal to the search's up to ACUI" {
    try expectNdFolTrim(
        \\drinker
        \\-------
        \\l1: $ ¬ ∃ x (P x → ∀ y P y) , P C , ¬ P y , P y , ¬ ∀ y P y ⊢ P y $ by ax
        \\l2: $ ¬ ∃ x (P x → ∀ y P y) , P C , ¬ P y , P y , ¬ ∀ y P y ⊢ ⊥ $ by not_left [l1]
        \\l3: $ ¬ ∃ x (P x → ∀ y P y) , P C , ¬ P y , P y ⊢ ∀ y P y $ by raa [l2]
        \\l4: $ ¬ ∃ x (P x → ∀ y P y) , P C , ¬ P y ⊢ P y → ∀ y P y $ by imp_intro [l3]
        \\l5: $ ¬ ∃ x (P x → ∀ y P y) , P C , ¬ P y ⊢ ∃ x (P x → ∀ y P y) $ by ex_intro [l4]
        \\l6: $ ¬ ∃ x (P x → ∀ y P y) , P C , ¬ P y ⊢ ⊥ $ by not_left [l5]
        \\l7: $ ¬ ∃ x (P x → ∀ y P y) , P C ⊢ P y $ by raa [l6]
        \\l12: $ ∅ ⊢ ∃ x (P x → ∀ y P y) $ by auto?
    ,
        "raa [not_left [ex_intro [imp_intro [all_intro (x := $ y $) [l7]]]]]",
    );
}

test "trimming checks again with the kept bindings stated" {
    // The first oracle check keeps a set the line rejects once the kept
    // bindings are stated (a stated binder changes the hint an inline
    // sub-proof gets); the second check, with them stated, keeps `t`.
    try expectNdFolTrim(
        \\drinker
        \\-------
        \\l1: $ ¬ ∃ x (P x → ∀ y P y) , P C , ¬ P y , P y , ¬ ∀ y P y ⊢ P y $ by ax
        \\l2: $ ¬ ∃ x (P x → ∀ y P y) , P C , ¬ P y , P y , ¬ ∀ y P y ⊢ ⊥ $ by not_left [l1]
        \\l3: $ ¬ ∃ x (P x → ∀ y P y) , P C , ¬ P y , P y ⊢ ∀ y P y $ by raa [l2]
        \\l4: $ ¬ ∃ x (P x → ∀ y P y) , P C , ¬ P y ⊢ P y → ∀ y P y $ by imp_intro [l3]
        \\l12: $ ∅ ⊢ ∃ x (P x → ∀ y P y) $ by auto?
    ,
        "raa [not_left [ex_intro (t := $ C $) [imp_intro (g := $ ¬ ∃ x (P x → ∀ y P y) $, " ++
            "a := $ P C $, b := $ ∀ y P y $) [all_intro (x := $ y $) [raa " ++
            "(g := $ ¬ ∃ x (P x → ∀ y P y) , P C $, a := $ P y $) [not_left " ++
            "(g := $ P C , ¬ P y $, a := $ ∃ x (P x → ∀ y P y) $) [ex_intro [l4]]]]]]]]",
    );
}
