const helpers = @import("./helpers.zig");
const std = helpers.std;
const types = helpers.types;
const source = helpers.source;
const def_match = helpers.def_match;
const session_mod = helpers.session_mod;
const TheoremContext = helpers.TheoremContext;
const ProofScript = helpers.ProofScript;
const CompilerContext = helpers.CompilerContext;
const CheckedIr = helpers.CheckedIr;
const Check = helpers.Check;
const DiagnosticSink = helpers.DiagnosticSink;
const ProofParser = helpers.ProofParser;
const Goal = helpers.Goal;
const apply = helpers.apply;
const applyWithSession = helpers.applyWithSession;
const exact = helpers.exact;
const tryCandidate = helpers.tryCandidate;
const fixtureFor = helpers.fixtureFor;
const parseGoal = helpers.parseGoal;
const runSearchLine = helpers.runSearchLine;
const readProofCase = helpers.readProofCase;
const expectTimingCounter = helpers.expectTimingCounter;
const ContextHarness = helpers.ContextHarness;
const expectCaseLineSearch = helpers.expectCaseLineSearch;
const expectApplyContains = helpers.expectApplyContains;
const expectApplyNotContains = helpers.expectApplyNotContains;
const expectRuleIsUnavailableAtSearchPoint = helpers.expectRuleIsUnavailableAtSearchPoint;
const expectApplyRuleOrder = helpers.expectApplyRuleOrder;
const expectExactRuleOrderWithPrefix = helpers.expectExactRuleOrderWithPrefix;
const expectExactRuleOrder = helpers.expectExactRuleOrder;
const expectFirstExactRefs = helpers.expectFirstExactRefs;

test "apply rule index filters nonmatching rules before validation" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term P: wff;
        \\term Q: wff;
        \\term R: wff;
        \\axiom p: $ P $;
        \\axiom q: $ Q $;
        \\axiom r: $ R $;
        \\theorem t: $ P $;
    ;
    const proof_src =
        \\t
        \\------
        \\l1: $ P $ by apply?
    ;
    const offset = std.mem.indexOf(u8, proof_src, "apply?") orelse {
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

    try std.testing.expectEqual(@as(usize, 1), suggestions.items.len);
    try std.testing.expectEqual(@as(usize, 1), counters.conclusion_probes);
    try std.testing.expectEqual(
        @as(usize, 1),
        counters.candidate_rules_before_conclusion_validation,
    );
    try expectTimingCounter(counters.rule_index_build_ns);
    try expectTimingCounter(counters.rule_lookup_ns);
}

test "search session reuses rule index across apply calls" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term P: wff;
        \\term Q: wff;
        \\axiom p: $ P $;
        \\axiom q: $ Q $;
        \\theorem t: $ P $;
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    var fixture = try fixtureFor(allocator, mm0_src, "t");
    var sink = DiagnosticSink.init(mm0_src, "");
    var compiler = CompilerContext.init(mm0_src, "", .none, &sink);
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
    var session = session_mod.SearchSession.init(&context, .{});
    defer session.deinit();

    var first_counters = types.SearchCounters{};
    var first_results = try applyWithSession(
        &compiler,
        &session,
        try parseGoal(&fixture, &theorem, &theorem_vars, "P"),
        &theorem,
        &theorem_vars,
        .{ .counters = &first_counters },
    );
    defer first_results.deinit();

    var second_counters = types.SearchCounters{};
    var second_results = try applyWithSession(
        &compiler,
        &session,
        try parseGoal(&fixture, &theorem, &theorem_vars, "Q"),
        &theorem,
        &theorem_vars,
        .{ .counters = &second_counters },
    );
    defer second_results.deinit();

    try expectTimingCounter(first_counters.rule_index_build_ns);
    try std.testing.expectEqual(
        @as(u64, 0),
        second_counters.rule_index_build_ns,
    );
    try std.testing.expectEqual(@as(usize, 1), first_results.candidates.len);
    try std.testing.expectEqual(@as(usize, 1), second_results.candidates.len);
    try std.testing.expectEqualStrings("p", first_results.candidates[0].rule_name);
    try std.testing.expectEqualStrings("q", second_results.candidates[0].rule_name);
}

test "apply search returns unresolved hypotheses" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term P: wff;
        \\axiom id (p: wff): $ p $ > $ p $;
        \\theorem t: $ P $;
    ;
    try expectApplyContains(mm0_src, "t", "P", "id", 1, 0);
}

test "apply search allows hyp-only unresolved binders" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term P: wff;
        \\term Q: wff;
        \\term imp (p q: wff): wff;
        \\infixr imp: $->$ prec 25;
        \\axiom mp (p q: wff): $ p $ > $ p -> q $ > $ q $;
        \\theorem t: $ Q $;
    ;
    try expectApplyContains(mm0_src, "t", "Q", "mp", 2, 2);
}

test "apply search matches through transparent defs" {
    const mm0_src = try readProofCase(
        std.testing.allocator,
        "pass_def_transport",
        "mm0",
    );
    defer std.testing.allocator.free(mm0_src);
    try expectApplyContains(
        mm0_src,
        "concl_transport",
        "id a",
        "ax_expanded",
        0,
        0,
    );
}

test "apply search uses view for normalized searchable shape" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\sort mor;
        \\term iff (a b: wff): wff;
        \\infixr iff: $<->$ prec 20;
        \\term mor_eq (f g: mor): wff;
        \\infixl mor_eq: $~$ prec 15;
        \\term comp (f g: mor): mor;
        \\infixl comp: $o$ prec 35;
        \\term F: mor;
        \\term G: mor;
        \\term H: mor;
        \\--| @relation wff iff iff_refl iff_trans iff_sym iff_mp
        \\axiom iff_refl (a: wff): $ a <-> a $;
        \\axiom iff_trans (a b c: wff):
        \\  $ a <-> b $ > $ b <-> c $ > $ a <-> c $;
        \\axiom iff_sym (a b: wff): $ a <-> b $ > $ b <-> a $;
        \\axiom iff_mp (a b: wff): $ a <-> b $ > $ a $ > $ b $;
        \\--| @relation mor mor_eq mor_refl mor_trans mor_sym _
        \\axiom mor_refl (f: mor): $ f ~ f $;
        \\axiom mor_trans (f g h: mor):
        \\  $ f ~ g $ > $ g ~ h $ > $ f ~ h $;
        \\axiom mor_sym (f g: mor): $ f ~ g $ > $ g ~ f $;
        \\--| @congr
        \\axiom mor_eq_congr (f1 f2 g1 g2: mor):
        \\  $ f1 ~ f2 $ > $ g1 ~ g2 $ > $ (f1 ~ g1) <-> (f2 ~ g2) $;
        \\--| @congr
        \\axiom comp_congr (f1 f2 g1 g2: mor):
        \\  $ f1 ~ f2 $ > $ g1 ~ g2 $ > $ f1 o g1 ~ f2 o g2 $;
        \\--| @rewrite
        \\axiom comp_assoc (f g h: mor): $ (f o g) o h ~ f o (g o h) $;
        \\--| @view : $ F o (G o H) ~ F o (G o H) $
        \\axiom assoc_refl: $ ((F o G) o H) ~ ((F o G) o H) $;
        \\def assoc_norm: wff = $ F o (G o H) ~ F o (G o H) $;
        \\theorem normalize_goal: $ assoc_norm $;
    ;
    try expectApplyContains(
        mm0_src,
        "normalize_goal",
        "assoc_norm",
        "assoc_refl",
        0,
        0,
    );
}

test "apply search matches through view and recover" {
    const mm0_src = try readProofCase(
        std.testing.allocator,
        "pass_recover_basic",
        "mm0",
    );
    defer std.testing.allocator.free(mm0_src);
    try expectApplyContains(
        mm0_src,
        "inst_use",
        "A. x (P x) -> P u",
        "ax_inst",
        0,
        0,
    );
}

test "apply search does not return future rules" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term P: wff;
        \\term Q: wff;
        \\axiom p: $ P $;
        \\theorem t: $ Q $;
        \\axiom future_q: $ Q $;
    ;
    try expectRuleIsUnavailableAtSearchPoint(mm0_src, "t", "future_q");
    try expectApplyNotContains(mm0_src, "t", "Q", "future_q");
}

test "apply search max_results preserves ranked declaration order" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term P: wff;
        \\axiom p1: $ P $;
        \\axiom p2: $ P $;
        \\axiom p3: $ P $;
        \\theorem t: $ P $;
    ;
    try expectApplyRuleOrder(
        mm0_src,
        "t",
        "P",
        2,
        &[_][]const u8{ "p1", "p2" },
    );
}

test "apply search rejects partial dependency violations" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\sort obj;
        \\provable sort wff;
        \\term rel {x y: obj}: wff;
        \\axiom rel_bad {x y: obj} (p: wff): $ p $ > $ rel x y $;
        \\theorem t {z: obj}: $ rel z z $;
    ;
    try expectApplyNotContains(mm0_src, "t", "rel z z", "rel_bad");
}

test "apply search keeps view candidates with unresolved hypotheses" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term P: wff;
        \\term raw (a: wff): wff;
        \\def shown (a: wff): wff = $ raw a $;
        \\--| @view (a b: wff): $ b $ > $ shown a $
        \\axiom view_use (a b: wff): $ b $ > $ raw a $;
        \\theorem t: $ shown P $;
    ;
    try expectApplyContains(
        mm0_src,
        "t",
        "shown P",
        "view_use",
        1,
        1,
    );
}

test "apply search rejects freshness-invalid candidates" {
    const mm0_src =
        \\--| @vars x
        \\provable sort wff;
        \\term top: wff;
        \\--| @fresh a
        \\--| @fresh b
        \\axiom use_fresh_pair {a b: wff}: $ top $;
        \\theorem t: $ top $;
    ;
    try expectApplyNotContains(mm0_src, "t", "top", "use_fresh_pair");
}

test "apply search does not use checked proof lines as refs" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term P: wff;
        \\term Q: wff;
        \\term imp (p q: wff): wff;
        \\infixr imp: $->$ prec 25;
        \\axiom p: $ P $;
        \\axiom mp (p q: wff): $ p $ > $ p -> q $ > $ q $;
        \\theorem t: $ Q $;
    ;
    const proof_src =
        \\t
        \\------
        \\l1: $ P $ by p
    ;
    var fixture = try fixtureFor(allocator, mm0_src, "t");
    var sink = DiagnosticSink.init(mm0_src, proof_src);
    var compiler = CompilerContext.init(mm0_src, proof_src, .none, &sink);
    var proof_parser = ProofParser.init(allocator, proof_src);
    const block = (try proof_parser.nextBlock()) orelse return error.MissingBlock;
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

    var line_result = try runSearchLine(
        allocator,
        &compiler,
        &fixture,
        &harness.labels,
        &harness.checked,
        &theorem,
        &theorem_vars,
        &harness.diag_scratch,
        &harness.cache,
        block.lines[0],
        true,
    );
    defer line_result.deinit();
    try harness.labels.put(block.lines[0].label, line_result.line_idx);

    const context = harness.context(&fixture);
    const goal = try parseGoal(&fixture, &theorem, &theorem_vars, "Q");
    var results = try apply(
        &compiler,
        &context,
        goal,
        &theorem,
        &theorem_vars,
        .{},
    );
    defer results.deinit();

    for (results.candidates) |candidate| {
        if (!std.mem.eql(u8, candidate.rule_name, "mp")) continue;
        var null_count: usize = 0;
        for (candidate.unresolved_hyps) |hyp| {
            if (hyp.expected == null) null_count += 1;
        }
        try std.testing.expectEqual(@as(usize, 2), null_count);
        try std.testing.expectEqual(@as(usize, 1), harness.checked.items.len);
        return;
    }
    return error.ExpectedApplyCandidate;
}

test "exact search finds zero-hypothesis proof" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term P: wff;
        \\axiom p: $ P $;
        \\theorem t: $ P $;
    ;
    try expectExactRuleOrder(mm0_src, "t", "P", &[_][]const u8{"p"});
}

test "exact ref index filters multi-hyp reference tuples" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term P: wff;
        \\term Q: wff;
        \\term R: wff;
        \\term S: wff;
        \\term T: wff;
        \\axiom use: $ P $ > $ Q $ > $ T $;
        \\theorem t: $ R $ > $ S $ > $ P $ > $ Q $ > $ T $;
    ;
    const proof_src =
        \\t
        \\------
        \\l1: $ T $ by exact?
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

    try std.testing.expectEqual(@as(usize, 1), suggestions.items.len);
    try std.testing.expectEqual(@as(usize, 4), counters.ref_pool_size);
    try std.testing.expectEqual(
        @as(usize, 2),
        counters.per_hyp_filtered_ref_list_total,
    );
    try std.testing.expectEqual(
        @as(usize, 1),
        counters.ref_tuple_count_after_filtering,
    );
    try std.testing.expectEqual(@as(usize, 1), counters.full_try_candidate_calls);
    try expectTimingCounter(counters.ref_index_build_ns);
    try expectTimingCounter(counters.ref_lookup_ns);
}

test "exact search propagates sibling hyp bindings while filtering refs" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term P: wff;
        \\term Q: wff;
        \\term R: wff;
        \\term S: wff;
        \\term Goal: wff;
        \\term imp (p q: wff): wff;
        \\infixr imp: $->$ prec 25;
        \\axiom mp (p q: wff): $ p $ > $ p -> q $ > $ q $;
        \\theorem t:
        \\  $ P $ > $ Q $ > $ R $ > $ S $ > $ P -> Goal $ > $ Goal $;
    ;
    const proof_src =
        \\t
        \\------
        \\l1: $ Goal $ by exact?
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

    try std.testing.expectEqual(@as(usize, 1), suggestions.items.len);
    try std.testing.expectEqual(@as(usize, 5), counters.ref_pool_size);
    try std.testing.expectEqual(
        @as(usize, 1),
        counters.ref_tuple_count_after_filtering,
    );
    try std.testing.expectEqual(@as(usize, 1), counters.full_try_candidate_calls);
}

test "exact search uses one theorem hypothesis" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term P: wff;
        \\axiom id (p: wff): $ p $ > $ p $;
        \\theorem t: $ P $ > $ P $;
    ;
    try expectFirstExactRefs(
        mm0_src,
        "",
        "t",
        "P",
        0,
        "id",
        &[_]ProofScript.Ref{.{ .hyp = .{
            .index = 1,
            .span = .{ .start = 0, .end = 0 },
        } }},
    );
}

test "exact search uses one previous line" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term P: wff;
        \\term Q: wff;
        \\term imp (p q: wff): wff;
        \\infixr imp: $->$ prec 25;
        \\axiom p: $ P $;
        \\axiom mp (p q: wff): $ p $ > $ p -> q $ > $ q $;
        \\theorem t: $ P -> Q $ > $ Q $;
    ;
    const proof_src =
        \\t
        \\------
        \\l1: $ P $ by p
    ;
    try expectFirstExactRefs(
        mm0_src,
        proof_src,
        "t",
        "Q",
        1,
        "mp",
        &[_]ProofScript.Ref{
            .{ .line = .{
                .label = "l1",
                .span = .{ .start = 0, .end = 0 },
            } },
            .{ .hyp = .{
                .index = 1,
                .span = .{ .start = 0, .end = 0 },
            } },
        },
    );
}

test "exact search uses multiple theorem hypotheses" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term P: wff;
        \\term Q: wff;
        \\term imp (p q: wff): wff;
        \\infixr imp: $->$ prec 25;
        \\axiom mp (p q: wff): $ p $ > $ p -> q $ > $ q $;
        \\theorem t: $ P $ > $ P -> Q $ > $ Q $;
    ;
    try expectFirstExactRefs(
        mm0_src,
        "",
        "t",
        "Q",
        0,
        "mp",
        &[_]ProofScript.Ref{
            .{ .hyp = .{
                .index = 1,
                .span = .{ .start = 0, .end = 0 },
            } },
            .{ .hyp = .{
                .index = 2,
                .span = .{ .start = 0, .end = 0 },
            } },
        },
    );
}

test "exact search matches refs through transparent defs" {
    const mm0_src = try readProofCase(
        std.testing.allocator,
        "pass_def_transport",
        "mm0",
    );
    defer std.testing.allocator.free(mm0_src);
    const proof_src =
        \\hyp_transport
        \\-------------
        \\l1: $ a -> a $ by ax_expanded (a := $ a $) []
    ;
    try expectFirstExactRefs(
        mm0_src,
        proof_src,
        "hyp_transport",
        "a",
        1,
        "use_id",
        &[_]ProofScript.Ref{.{ .line = .{
            .label = "l1",
            .span = .{ .start = 0, .end = 0 },
        } }},
    );
}

test "exact ref index reaches a reducible-headed hypothesis through normalization" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\sort mor;
        \\term iff (a b: wff): wff;
        \\infixr iff: $<->$ prec 20;
        \\term mor_eq (f g: mor): wff;
        \\infixl mor_eq: $~$ prec 15;
        \\term comp (f g: mor): mor;
        \\infixl comp: $o$ prec 35;
        \\term F: mor;
        \\term G: mor;
        \\term H: mor;
        \\term P: wff;
        \\--| @relation wff iff iff_refl iff_trans iff_sym iff_mp
        \\axiom iff_refl (a: wff): $ a <-> a $;
        \\axiom iff_trans (a b c: wff):
        \\  $ a <-> b $ > $ b <-> c $ > $ a <-> c $;
        \\axiom iff_sym (a b: wff): $ a <-> b $ > $ b <-> a $;
        \\axiom iff_mp (a b: wff): $ a <-> b $ > $ a $ > $ b $;
        \\--| @relation mor mor_eq mor_refl mor_trans mor_sym _
        \\axiom mor_refl (f: mor): $ f ~ f $;
        \\axiom mor_trans (f g h: mor):
        \\  $ f ~ g $ > $ g ~ h $ > $ f ~ h $;
        \\axiom mor_sym (f g: mor): $ f ~ g $ > $ g ~ f $;
        \\--| @congr
        \\axiom mor_eq_congr (f1 f2 g1 g2: mor):
        \\  $ f1 ~ f2 $ > $ g1 ~ g2 $ > $ (f1 ~ g1) <-> (f2 ~ g2) $;
        \\--| @congr
        \\axiom comp_congr (f1 f2 g1 g2: mor):
        \\  $ f1 ~ f2 $ > $ g1 ~ g2 $ > $ f1 o g1 ~ f2 o g2 $;
        \\--| @rewrite
        \\axiom comp_assoc (f g h: mor): $ (f o g) o h ~ f o (g o h) $;
        \\axiom assoc_refl: $ ((F o G) o H) ~ ((F o G) o H) $;
        \\axiom use_norm:
        \\  $ F o (G o H) ~ F o (G o H) $ > $ P $;
        \\theorem t: $ P $;
    ;
    const proof_src =
        \\t
        \\------
        \\l1: $ ((F o G) o H) ~ ((F o G) o H) $ by assoc_refl
    ;
    // `use_norm`'s hypothesis `F o (G o H) ~ F o (G o H)` carries a
    // `@rewrite`-reducible head (`comp`, via `comp_assoc`), so its shape cannot
    // be a reliable index key: the pool ref l1 `((F o G) o H) ~ ((F o G) o H)`
    // is `comp_assoc`-equal but written in a different association. A reducible
    // head shapes to a covering wildcard (shape.zig) and the hyp matcher
    // classifies the pair `.unknown` (semantic.zig / def_match.zig)
    // rather than `.mismatch`, so the candidate reaches `tryCandidate`, which
    // normalizes and validates it. This is the substitution-head path that
    // view-less eliminators (`J_elim`, `nat_ind_*`) rely on; the validated
    // `use_norm` candidate below confirms the recovered proof is genuine.
    try expectExactRuleOrderWithPrefix(
        mm0_src,
        proof_src,
        "t",
        "P",
        1,
        null,
        &[_][]const u8{"use_norm"},
    );
}

test "exact search handles successful fallback applications" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term P: wff;
        \\term Q: wff;
        \\term R: wff;
        \\axiom have_p: $ P $;
        \\axiom fallback_use: $ P $ > $ Q $;
        \\--| @fallback fallback_use
        \\axiom bad_use: $ R $ > $ Q $;
        \\theorem t: $ Q $;
    ;
    const proof_src =
        \\t
        \\------
        \\l1: $ P $ by have_p
    ;
    try expectExactRuleOrderWithPrefix(
        mm0_src,
        proof_src,
        "t",
        "Q",
        1,
        null,
        &[_][]const u8{"fallback_use"},
    );
}

test "exact search returns no result when a hypothesis is unavailable" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term P: wff;
        \\axiom id (p: wff): $ p $ > $ p $;
        \\theorem t: $ P $;
    ;
    try expectExactRuleOrder(mm0_src, "t", "P", &[_][]const u8{});
}

test "exact search does not use later proof lines" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term P: wff;
        \\term Q: wff;
        \\term imp (p q: wff): wff;
        \\infixr imp: $->$ prec 25;
        \\axiom p: $ P $;
        \\axiom mp (p q: wff): $ p $ > $ p -> q $ > $ q $;
        \\theorem t: $ P -> Q $ > $ Q $;
    ;
    const proof_src =
        \\t
        \\------
        \\l1: $ P $ by p
    ;
    try expectExactRuleOrderWithPrefix(
        mm0_src,
        proof_src,
        "t",
        "Q",
        0,
        null,
        &[_][]const u8{},
    );
}

test "exact search orders refs deterministically" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term P: wff;
        \\axiom id (p: wff): $ p $ > $ p $;
        \\theorem t: $ P $ > $ P $ > $ P $;
    ;
    try expectFirstExactRefs(
        mm0_src,
        "",
        "t",
        "P",
        0,
        "id",
        &[_]ProofScript.Ref{.{ .hyp = .{
            .index = 1,
            .span = .{ .start = 0, .end = 0 },
        } }},
    );
}

test "exact search orders successful rules deterministically" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term P: wff;
        \\axiom p1: $ P $;
        \\axiom p2: $ P $;
        \\axiom p3: $ P $;
        \\theorem t: $ P $;
    ;
    try expectExactRuleOrder(
        mm0_src,
        "t",
        "P",
        &[_][]const u8{ "p1", "p2", "p3" },
    );
}

test "exact search max_results preserves ranked declaration order" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term P: wff;
        \\axiom p1: $ P $;
        \\axiom p2: $ P $;
        \\axiom p3: $ P $;
        \\theorem t: $ P $;
    ;
    try expectExactRuleOrderWithPrefix(
        mm0_src,
        "",
        "t",
        "P",
        0,
        2,
        &[_][]const u8{ "p1", "p2" },
    );
}

test "exact search leaves checked prefix unchanged on failure" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term P: wff;
        \\term Q: wff;
        \\axiom p: $ P $;
        \\axiom id (a: wff): $ a $ > $ a $;
        \\theorem t: $ P $ > $ Q $;
    ;
    const proof_src =
        \\t
        \\------
        \\l1: $ P $ by p
    ;
    try expectExactRuleOrderWithPrefix(
        mm0_src,
        proof_src,
        "t",
        "Q",
        1,
        null,
        &[_][]const u8{},
    );
}

test "exact search orders transparent refs by pool order" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term P: wff;
        \\def id (p: wff): wff = $ p $;
        \\axiom use_p: $ P $ > $ P $;
        \\theorem t: $ id P $ > $ P $ > $ P $;
    ;
    try expectFirstExactRefs(
        mm0_src,
        "",
        "t",
        "P",
        0,
        "use_p",
        &[_]ProofScript.Ref{.{ .hyp = .{
            .index = 1,
            .span = .{ .start = 0, .end = 0 },
        } }},
    );
}

test "apply candidate can compile after user supplies refs" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term P: wff;
        \\term Q: wff;
        \\term imp (p q: wff): wff;
        \\infixr imp: $->$ prec 25;
        \\axiom mp (p q: wff): $ p $ > $ p -> q $ > $ q $;
        \\theorem t: $ P $ > $ P -> Q $ > $ Q $;
    ;
    const proof_src =
        \\t
        \\------
        \\l1: $ Q $ by mp [#1, #2]
    ;
    var fixture = try fixtureFor(allocator, mm0_src, "t");
    var sink = DiagnosticSink.init(mm0_src, proof_src);
    var compiler = CompilerContext.init(mm0_src, proof_src, .none, &sink);
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
    var results = try apply(
        &compiler,
        &context,
        goal,
        &theorem,
        &theorem_vars,
        .{},
    );
    defer results.deinit();
    var found_mp = false;
    for (results.candidates) |candidate| {
        found_mp = found_mp or std.mem.eql(u8, candidate.rule_name, "mp");
    }
    try std.testing.expect(found_mp);

    var proof_parser = ProofParser.init(allocator, proof_src);
    const block = (try proof_parser.nextBlock()) orelse return error.MissingBlock;
    var result = try runSearchLine(
        allocator,
        &compiler,
        &fixture,
        &harness.labels,
        &harness.checked,
        &theorem,
        &theorem_vars,
        &harness.diag_scratch,
        &harness.cache,
        block.lines[0],
        false,
    );
    defer result.deinit();
    try std.testing.expect(result.checked_lines.len > 0);
    try CheckedIr.validateLines(&result.theorem.?, result.checked_lines);
}

test "search candidate failure leaves no checked lines" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();

    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term P: wff;
        \\term Q: wff;
        \\axiom p: $ P $;
        \\theorem t: $ Q $;
    ;
    const proof_src =
        \\t
        \\------
        \\l1: $ Q $ by p
    ;
    var fixture = try fixtureFor(allocator, mm0_src, "t");
    var sink = DiagnosticSink.init(mm0_src, proof_src);
    var compiler = CompilerContext.init(mm0_src, proof_src, .none, &sink);
    var proof_parser = ProofParser.init(allocator, proof_src);
    const block = (try proof_parser.nextBlock()) orelse return error.MissingBlock;
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
    const line = block.lines[0];
    const context = harness.context(&fixture);
    const goal = try parseGoal(
        &fixture,
        &theorem,
        &theorem_vars,
        line.assertion.text,
    );
    const interner_count = theorem.interner.count();
    const vars_len = theorem.theorem_vars.items.len;
    const dummies_len = theorem.theorem_dummies.items.len;
    const placeholders_len = theorem.theorem_placeholders.items.len;
    const theorem_vars_count = theorem_vars.count();

    try std.testing.expectError(
        error.ConclusionMismatch,
        tryCandidate(
            &compiler,
            &context,
            line.application,
            goal,
            &theorem,
            &theorem_vars,
            .{
                .line_label = line.label,
                .assertion_span = line.assertion.span,
                .diagnostic_span = line.span,
            },
        ),
    );
    try std.testing.expectEqual(interner_count, theorem.interner.count());
    try std.testing.expectEqual(vars_len, theorem.theorem_vars.items.len);
    try std.testing.expectEqual(dummies_len, theorem.theorem_dummies.items.len);
    try std.testing.expectEqual(
        placeholders_len,
        theorem.theorem_placeholders.items.len,
    );
    try std.testing.expectEqual(theorem_vars_count, theorem_vars.count());
    try std.testing.expectEqual(@as(usize, 0), harness.checked.items.len);
    try std.testing.expectEqual(@as(usize, 0), harness.diag_scratch.entries.items.len);
    try std.testing.expect(compiler.getDiagnostic() == null);
}

test "search candidate uses transparent definition conversion" {
    try expectCaseLineSearch("pass_def_transport", "hyp_transport", 1);
}

test "search candidate uses normalization and transport" {
    try expectCaseLineSearch(
        "pass_normalize_def_transport_concl",
        "normalize_def_transport_concl",
        0,
    );
}

test "search candidate uses view inference" {
    try expectCaseLineSearch("pass_view_basic", "imp_refl", 3);
}

test "search candidate uses view recover" {
    try expectCaseLineSearch("pass_recover_basic", "inst_use", 0);
}

test "search candidate rejects boundness failures" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\sort nat;
        \\term all {x: nat} (p: wff x): wff;
        \\prefix all: $A.$ prec 41;
        \\axiom ax_gen {x: nat} (p: wff x): $ p $ > $ A. x p $;
        \\theorem gen_bad (n: nat) (q: wff): $ q $ > $ q $;
    ;
    const proof_src =
        \\gen_bad
        \\-------
        \\l1: $ q $ by ax_gen (x := $ n $, p := $ q $) [#1]
    ;
    var fixture = try fixtureFor(allocator, mm0_src, "gen_bad");
    var sink = DiagnosticSink.init(mm0_src, proof_src);
    var compiler = CompilerContext.init(mm0_src, proof_src, .none, &sink);
    var proof_parser = ProofParser.init(allocator, proof_src);
    const block = (try proof_parser.nextBlock()) orelse return error.MissingBlock;
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

    const err = runSearchLine(
        allocator,
        &compiler,
        &fixture,
        &harness.labels,
        &harness.checked,
        &theorem,
        &theorem_vars,
        &harness.diag_scratch,
        &harness.cache,
        block.lines[0],
        false,
    );
    try std.testing.expectError(error.BoundnessMismatch, err);
    try std.testing.expectEqual(@as(usize, 0), harness.checked.items.len);
    try std.testing.expectEqual(@as(usize, 0), harness.diag_scratch.entries.items.len);
    try std.testing.expect(compiler.getDiagnostic() == null);
}

test "apply search accepts visible holey goals" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\--| @hole _wff
        \\provable sort wff;
        \\term imp (a b: wff): wff;
        \\infixr imp: $->$ prec 25;
        \\axiom ax_keep (a b: wff): $ a $ > $ a -> b -> a $;
        \\theorem t (a b: wff): $ a -> b -> a $;
    ;
    try expectApplyContains(
        mm0_src,
        "t",
        "a -> _wff -> a",
        "ax_keep",
        1,
        0,
    );
}

test "apply search accepts term-position holes" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\--| @hole _wff
        \\provable sort wff;
        \\--| @hole _set
        \\sort set;
        \\term P (x: set): wff;
        \\term u: set;
        \\axiom pred_any (x: set): $ P x $;
        \\theorem t: $ P u $;
    ;
    try expectApplyContains(
        mm0_src,
        "t",
        "P _set",
        "pred_any",
        0,
        0,
    );
}

test "exact search accepts visible holey goals" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\--| @hole _wff
        \\provable sort wff;
        \\term imp (a b: wff): wff;
        \\infixr imp: $->$ prec 25;
        \\axiom ax_keep (a b: wff):
        \\  $ a $ > $ b $ > $ a -> b -> a $;
        \\theorem t (a b: wff): $ a $ > $ b $ > $ a -> b -> a $;
    ;
    try expectFirstExactRefs(
        mm0_src,
        "",
        "t",
        "a -> _wff -> a",
        0,
        "ax_keep",
        &[_]ProofScript.Ref{
            .{ .hyp = .{
                .index = 1,
                .span = .{ .start = 0, .end = 0 },
            } },
            .{ .hyp = .{
                .index = 1,
                .span = .{ .start = 0, .end = 0 },
            } },
        },
    );
}

test "apply search supports ACUI context holes" {
    const mm0_src = try readProofCase(
        std.testing.allocator,
        "pass_hole_acui_min_ctx",
        "mm0",
    );
    defer std.testing.allocator.free(mm0_src);
    try expectApplyContains(
        mm0_src,
        "hole_acui_min_ctx",
        "nd _ctx (imp p _wff)",
        "imp_intro",
        1,
        1,
    );
}

test "exact search supports ACUI context holes" {
    const mm0_src = try readProofCase(
        std.testing.allocator,
        "pass_hole_acui_min_ctx",
        "mm0",
    );
    defer std.testing.allocator.free(mm0_src);
    try expectFirstExactRefs(
        mm0_src,
        "",
        "hole_acui_min_ctx",
        "nd _ctx (imp p _wff)",
        0,
        "imp_intro",
        &[_]ProofScript.Ref{.{ .hyp = .{
            .index = 1,
            .span = .{ .start = 0, .end = 0 },
        } }},
    );
}
