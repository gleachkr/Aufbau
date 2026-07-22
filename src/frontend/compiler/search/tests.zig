const std = @import("std");
const build_options = @import("build_options");
const types = @import("./types.zig");
const source = @import("./source.zig");
const fixture_mod = @import("./fixture.zig");
const apply_mod = @import("./apply.zig");
const backtrack = @import("./backward/backtrack.zig");
const prune = @import("./backward/prune.zig");
const plausible = @import("./backward/plausible.zig");
const abstract_prune = @import("./abstract_prune.zig");
const context_prune = @import("./context_prune.zig");
const seed = @import("./backward/seed.zig");
const def_match = @import("./backward/def_match.zig");
const acui = @import("./backward/acui.zig");
const Witness = @import("./backward/witness.zig");
const MetaStore = @import("../inference/meta_store.zig").MetaStore;
const TemplateExpr = @import("../../rules.zig").TemplateExpr;
const candidate_mod = @import("./candidate.zig");
const session_mod = @import("./session.zig");
const expr_mod = @import("../../expr.zig");
const ExprId = expr_mod.ExprId;
const TheoremContext = expr_mod.TheoremContext;
const ProofScript = @import("../../proof_script.zig");
const CompilerDiag = @import("../diag.zig");
const CompilerContext = @import("../context.zig").CompilerContext;
const CheckedIr = @import("../checked_ir.zig");
const CheckedLine = CheckedIr.CheckedLine;
const Inference = @import("../inference.zig");
const Check = @import("../check.zig");
const DiagnosticSink = @import("../diagnostic_sink.zig").DiagnosticSink;
const ProofParser = ProofScript.Parser;
const Goal = types.Goal;
const Context = types.Context;
const AttemptResult = types.AttemptResult;
const NameExprMap = types.NameExprMap;
const LabelIndexMap = types.LabelIndexMap;
const apply = apply_mod.apply;
const applyWithSession = apply_mod.applyWithSession;
const exact = backtrack.exact;
const tryCandidate = candidate_mod.tryCandidate;
const fixtureFor = fixture_mod.fixtureFor;
const fixtureForFullEnv = fixture_mod.fixtureForFullEnv;
const parseGoal = fixture_mod.parseGoal;
const runSearchLine = fixture_mod.runSearchLine;
const readProofCase = fixture_mod.readProofCase;

fn expectTimingCounter(value: u64) !void {
    if (build_options.enable_search_timers) {
        try std.testing.expect(value > 0);
    } else {
        try std.testing.expectEqual(@as(u64, 0), value);
    }
}

/// Owns the four per-test `Context` collaborators every search test wires
/// identically (label index, checked lines, diag scratch, unify cache);
/// `context()` assembles the search `Context` over a fixture. `deinit` also
/// deinits any lines pushed into `checked`, so tests that run search lines
/// need no extra teardown.
const ContextHarness = struct {
    allocator: std.mem.Allocator,
    labels: LabelIndexMap,
    checked: std.ArrayListUnmanaged(CheckedLine) = .{},
    diag_scratch: CompilerDiag.Scratch,
    cache: Inference.RuleUnifyCache,

    fn init(allocator: std.mem.Allocator) ContextHarness {
        return .{
            .allocator = allocator,
            .labels = LabelIndexMap.init(allocator),
            .diag_scratch = CompilerDiag.Scratch.init(allocator),
            .cache = Inference.RuleUnifyCache.init(allocator),
        };
    }

    fn deinit(self: *ContextHarness) void {
        self.labels.deinit();
        CheckedIr.deinitLines(self.allocator, self.checked.items);
        self.checked.deinit(self.allocator);
        self.diag_scratch.deinit();
        self.cache.deinit();
    }

    fn context(self: *ContextHarness, fixture: *fixture_mod.Fixture) Context {
        return .{
            .allocator = self.allocator,
            .parser = &fixture.parser,
            .env = &fixture.env,
            .registry = &fixture.registry,
            .rule_catalog = &fixture.rule_catalog,
            .fresh_bindings = &fixture.fresh_bindings,
            .freshen_bindings = &fixture.freshen_bindings,
            .views = &fixture.views,
            .sort_vars = &fixture.sort_vars,
            .assertion = fixture.assertion,
            .labels = &self.labels,
            .checked = &self.checked,
            .diag_scratch = &self.diag_scratch,
            .rule_unify_cache = &self.cache,
            .available_rule_count = fixture.available_rule_count,
        };
    }
};

fn expectCaseLineSearch(
    stem: []const u8,
    theorem_name: []const u8,
    line_index: usize,
) !void {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    const mm0_src = try readProofCase(allocator, stem, "mm0");
    defer allocator.free(mm0_src);
    const proof_src = try readProofCase(allocator, stem, "auf");
    defer allocator.free(proof_src);

    var fixture = try fixtureFor(allocator, mm0_src, theorem_name);
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

    for (block.lines[0..line_index]) |line| {
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
            line,
            true,
        );
        defer result.deinit();
        try harness.labels.put(line.label, result.line_idx);
    }

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
        block.lines[line_index],
        false,
    );
    defer result.deinit();
    try std.testing.expect(result.checked_lines.len > 0);
    try CheckedIr.validateLines(&result.theorem.?, result.checked_lines);
    try std.testing.expectEqual(line_index, harness.checked.items.len);
}

fn expectApplyContains(
    mm0_src: []const u8,
    theorem_name: []const u8,
    goal_text: []const u8,
    rule_name: []const u8,
    unresolved_count: ?usize,
    null_expected_count: ?usize,
) !void {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    var fixture = try fixtureFor(allocator, mm0_src, theorem_name);
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
    const goal = try parseGoal(
        &fixture,
        &theorem,
        &theorem_vars,
        goal_text,
    );
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
        if (!std.mem.eql(u8, candidate.rule_name, rule_name)) continue;
        if (unresolved_count) |expected_count| {
            try std.testing.expectEqual(
                expected_count,
                candidate.unresolved_hyps.len,
            );
        }
        if (null_expected_count) |expected_count| {
            var actual_count: usize = 0;
            for (candidate.unresolved_hyps) |hyp| {
                if (hyp.expected == null) actual_count += 1;
            }
            try std.testing.expectEqual(expected_count, actual_count);
        }
        try std.testing.expectEqual(@as(usize, 0), harness.checked.items.len);
        return;
    }
    return error.ExpectedApplyCandidate;
}

fn expectApplyNotContains(
    mm0_src: []const u8,
    theorem_name: []const u8,
    goal_text: []const u8,
    rule_name: []const u8,
) !void {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    var fixture = try fixtureForFullEnv(allocator, mm0_src, theorem_name);
    const excluded_rule_id = fixture.env.getRuleId(rule_name) orelse {
        return error.ExpectedExcludedRuleInEnv;
    };
    _ = excluded_rule_id;
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
    const goal = try parseGoal(
        &fixture,
        &theorem,
        &theorem_vars,
        goal_text,
    );
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
        if (std.mem.eql(u8, candidate.rule_name, rule_name)) {
            return error.UnexpectedApplyCandidate;
        }
    }
    try std.testing.expectEqual(@as(usize, 0), harness.checked.items.len);
}

fn expectRuleIsUnavailableAtSearchPoint(
    mm0_src: []const u8,
    theorem_name: []const u8,
    rule_name: []const u8,
) !void {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    var fixture = try fixtureForFullEnv(allocator, mm0_src, theorem_name);
    const rule_id = fixture.env.getRuleId(rule_name) orelse {
        return error.ExpectedExcludedRuleInEnv;
    };
    try std.testing.expect(
        @as(usize, @intCast(rule_id)) >= fixture.available_rule_count,
    );
}

fn expectApplyRuleOrder(
    mm0_src: []const u8,
    theorem_name: []const u8,
    goal_text: []const u8,
    max_results: ?usize,
    expected_names: []const []const u8,
) !void {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    var fixture = try fixtureFor(allocator, mm0_src, theorem_name);
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
    const goal = try parseGoal(
        &fixture,
        &theorem,
        &theorem_vars,
        goal_text,
    );
    var results = try apply(
        &compiler,
        &context,
        goal,
        &theorem,
        &theorem_vars,
        .{ .max_results = max_results },
    );
    defer results.deinit();

    try std.testing.expectEqual(expected_names.len, results.candidates.len);
    for (expected_names, results.candidates) |expected, actual| {
        try std.testing.expectEqualStrings(expected, actual.rule_name);
    }
    try std.testing.expectEqual(@as(usize, 0), harness.checked.items.len);
}

fn expectExactRuleOrderWithPrefix(
    mm0_src: []const u8,
    proof_src: []const u8,
    theorem_name: []const u8,
    goal_text: []const u8,
    prefix_count: usize,
    max_results: ?usize,
    expected_names: []const []const u8,
) !void {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    var fixture = try fixtureFor(allocator, mm0_src, theorem_name);
    var sink = DiagnosticSink.init(mm0_src, proof_src);
    var compiler = CompilerContext.init(mm0_src, proof_src, .none, &sink);
    var proof_parser = ProofParser.init(allocator, proof_src);
    const block = if (proof_src.len == 0)
        null
    else
        try proof_parser.nextBlock();

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

    if (prefix_count > 0) {
        const actual_block = block orelse return error.MissingBlock;
        for (actual_block.lines[0..prefix_count]) |line| {
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
                line,
                true,
            );
            defer result.deinit();
            try harness.labels.put(line.label, result.line_idx);
        }
    }

    const checked_before = harness.checked.items.len;

    const context = harness.context(&fixture);
    const goal = try parseGoal(&fixture, &theorem, &theorem_vars, goal_text);
    var results = try exact(
        &compiler,
        &context,
        goal,
        &theorem,
        &theorem_vars,
        .{ .max_results = max_results },
    );
    defer results.deinit();
    try std.testing.expectEqual(checked_before, harness.checked.items.len);

    try std.testing.expectEqual(
        expected_names.len,
        results.candidates.len,
    );
    for (expected_names, 0..) |expected, idx| {
        try std.testing.expectEqualStrings(
            expected,
            results.candidates[idx].rule_name,
        );
        var attempt_theorem = try theorem.clone();
        defer attempt_theorem.deinit();
        var attempt_vars = try Check.cloneNameExprMap(
            allocator,
            &theorem_vars,
        );
        defer attempt_vars.deinit();
        var attempt = try tryCandidate(
            &compiler,
            &context,
            results.candidates[idx].application,
            goal,
            &attempt_theorem,
            &attempt_vars,
            .{},
        );
        defer attempt.deinit();
        try CheckedIr.validateLines(
            &attempt.theorem.?,
            attempt.checked_lines,
        );
    }
}

fn expectExactRuleOrder(
    mm0_src: []const u8,
    theorem_name: []const u8,
    goal_text: []const u8,
    expected_names: []const []const u8,
) !void {
    try expectExactRuleOrderWithPrefix(
        mm0_src,
        "",
        theorem_name,
        goal_text,
        0,
        null,
        expected_names,
    );
}

fn expectInlineSearch(
    mm0_src: []const u8,
    proof_src: []const u8,
    theorem_name: []const u8,
    line_index: usize,
) !void {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    var fixture = try fixtureFor(allocator, mm0_src, theorem_name);
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
        block.lines[line_index],
        false,
    );
    defer result.deinit();
    try std.testing.expect(result.checked_lines.len > 0);
    try std.testing.expectEqual(@as(usize, 0), harness.checked.items.len);
}

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

// `auto?` recursive generation. Goal `Q` is not provable by any
// single rule over the (empty) ref pool — `pq` needs a proof of `P` — but it is
// provable by `pq [p]`, one level of generated inline application.
const auto_chain_mm0 =
    \\delimiter $ ( ) $;
    \\provable sort wff;
    \\term P: wff;
    \\term Q: wff;
    \\axiom p: $ P $;
    \\axiom pq: $ P $ > $ Q $;
    \\theorem t: $ Q $;
;

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

// Inline `auto?` generation. Outer rule `qr` needs a proof of `Q` in its slot;
// `Q` is not provable by any single rule over the (empty) ref pool, but is
// provable by `pq [p]` — so an `auto?` in the slot must recursively generate,
// exactly as a top-level `auto?` does. `p2` gives a direct-ref alternative for
// the regression case; `S` is deliberately unreachable for the negative case.
const auto_inline_mm0 =
    \\delimiter $ ( ) $;
    \\provable sort wff;
    \\term P: wff;
    \\term Q: wff;
    \\term R: wff;
    \\term S: wff;
    \\term X: wff;
    \\axiom p: $ P $;
    \\axiom pq: $ P $ > $ Q $;
    \\axiom qr: $ Q $ > $ R $;
    \\axiom sq: $ S $ > $ Q $;
    \\axiom rx: $ R $ > $ X $;
    \\axiom r2 (a: wff): $ a $ > $ Q $ > $ R $;
    \\theorem t: $ R $;
    \\theorem tX: $ X $;
    \\theorem tPX: $ P $ > $ X $;
;

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

const GeneratedConclusionHookCtx = struct {
    wrong_conclusion: bool,
    wrong_expr: ExprId,
    calls: usize = 0,

    fn solve(
        ctx: *anyopaque,
        target: ExprId,
        target_theorem: *TheoremContext,
        eager_step: bool,
    ) anyerror!?types.GeneratedProof {
        _ = target_theorem;
        _ = eager_step;
        const self: *@This() = @ptrCast(@alignCast(ctx));
        self.calls += 1;
        const zero = ProofScript.Span{ .start = 0, .end = 0 };
        return .{
            .application = .{
                .rule_name = "p",
                .rule_span = zero,
                .refs_span = null,
                .refs = &.{},
                .span = zero,
            },
            .conclusion = if (self.wrong_conclusion) self.wrong_expr else target,
        };
    }
};

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

fn expectFirstExactRefs(
    mm0_src: []const u8,
    proof_src: []const u8,
    theorem_name: []const u8,
    goal_text: []const u8,
    prefix_count: usize,
    expected_rule: []const u8,
    expected_refs: []const ProofScript.Ref,
) !void {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    var fixture = try fixtureFor(allocator, mm0_src, theorem_name);
    var sink = DiagnosticSink.init(mm0_src, proof_src);
    var compiler = CompilerContext.init(mm0_src, proof_src, .none, &sink);
    var proof_parser = ProofParser.init(allocator, proof_src);
    const block = if (proof_src.len == 0)
        null
    else
        try proof_parser.nextBlock();
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

    if (prefix_count > 0) {
        const actual_block = block orelse return error.MissingBlock;
        for (actual_block.lines[0..prefix_count]) |line| {
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
                line,
                true,
            );
            defer result.deinit();
            try harness.labels.put(line.label, result.line_idx);
        }
    }

    const checked_before = harness.checked.items.len;

    const context = harness.context(&fixture);
    const goal = try parseGoal(&fixture, &theorem, &theorem_vars, goal_text);
    var results = try exact(
        &compiler,
        &context,
        goal,
        &theorem,
        &theorem_vars,
        .{},
    );
    defer results.deinit();
    try std.testing.expectEqual(checked_before, harness.checked.items.len);
    try std.testing.expect(results.candidates.len > 0);
    const candidate = results.candidates[0];
    try std.testing.expectEqualStrings(expected_rule, candidate.rule_name);
    try std.testing.expectEqual(expected_refs.len, candidate.refs.len);
    for (expected_refs, candidate.refs) |expected, actual| {
        switch (expected) {
            .hyp => |expected_hyp| switch (actual) {
                .hyp => |actual_hyp| try std.testing.expectEqual(
                    expected_hyp.index,
                    actual_hyp.index,
                ),
                else => return error.ExpectedHypRef,
            },
            .line => |expected_line| switch (actual) {
                .line => |actual_line| try std.testing.expectEqualStrings(
                    expected_line.label,
                    actual_line.label,
                ),
                else => return error.ExpectedLineRef,
            },
            .application => return error.UnexpectedInlineRef,
        }
    }
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

test "conclusion seed unfolds transparent template head" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\strict provable sort wff;
        \\sort type;
        \\term bool: type;
        \\sort term;
        \\term eqc (A: type) (t u: term): term;
        \\def bic (p q: term): term = $ eqc bool p q $;
        \\term thm (p: term): wff;
        \\
        \\axiom ded (p q: term):
        \\  $ thm p $ > $ thm q $ > $ thm (bic p q) $;
        \\theorem t (a b: term): $ thm (eqc bool a b) $;
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    var fixture = try fixtureFor(allocator, mm0_src, "t");
    var theorem = TheoremContext.init(allocator);
    defer theorem.deinit();
    try theorem.seedAssertion(fixture.assertion);
    var harness = ContextHarness.init(allocator);
    defer harness.deinit();
    const context = harness.context(&fixture);
    const goal_expr = try theorem.internParsedExpr(fixture.assertion.concl);
    const goal: Goal = .{ .concrete = goal_expr };
    const rule_id = fixture.env.getRuleId("ded") orelse return error.MissingRule;
    var candidate = try seed.makeExactRuleCandidate(
        allocator,
        &context,
        goal,
        &theorem,
        rule_id,
    );
    defer candidate.deinit();

    const rule = &fixture.env.rules.items[@intCast(rule_id)];
    const p_idx = blk: {
        for (rule.arg_names, 0..) |maybe_name, idx| {
            const name = maybe_name orelse continue;
            if (std.mem.eql(u8, name, "p")) break :blk idx;
        }
        return error.MissingArg;
    };
    const q_idx = blk: {
        for (rule.arg_names, 0..) |maybe_name, idx| {
            const name = maybe_name orelse continue;
            if (std.mem.eql(u8, name, "q")) break :blk idx;
        }
        return error.MissingArg;
    };
    const a_expr = theorem.theorem_vars.items[0];
    const b_expr = theorem.theorem_vars.items[1];

    try std.testing.expectEqual(@as(?ExprId, a_expr), candidate.bindings[p_idx]);
    try std.testing.expectEqual(@as(?ExprId, b_expr), candidate.bindings[q_idx]);
}

fn ruleArgIndex(rule: anytype, name: []const u8) !usize {
    for (rule.arg_names, 0..) |maybe_name, idx| {
        const arg_name = maybe_name orelse continue;
        if (std.mem.eql(u8, arg_name, name)) return idx;
    }
    return error.MissingArg;
}

test "multiHypBinderMask flags binders occurring in more than one hypothesis" {
    // arg0 in hyp0 & hyp1 (multi); arg1 in hyp0 only (single); arg2 in hyp0 &
    // hyp1 (multi); arg3 in hyp1 only (single).
    const hyp0_args = [_]TemplateExpr{
        .{ .binder = 0 },
        .{ .binder = 1 },
        .{ .binder = 2 },
    };
    const hyp1_args = [_]TemplateExpr{
        .{ .binder = 0 },
        .{ .binder = 2 },
        .{ .binder = 3 },
    };
    const hyps = [_]TemplateExpr{
        .{ .app = .{ .term_id = 0, .args = &hyp0_args } },
        .{ .app = .{ .term_id = 0, .args = &hyp1_args } },
    };
    const mask = seed.multiHypBinderMask(&hyps);
    try std.testing.expect(!mask.overflow);
    try std.testing.expectEqual(@as(u64, 0b0101), mask.mask); // bits 0 and 2
}

// Regression for the eliminator-reconciliation seed partition (code review):
// a def-unfold dummy threaded across >1 hypothesis is kept as a reconciliation
// meta; a single-hypothesis dummy is scrubbed to null; and a BARE meta leaf is
// scrubbed even in a multi-hypothesis slot (it constrains nothing — it must not
// ride forward as an unresolved, non-reconciliation pin).
test "partitionSeedBindings: keep multi-hyp dummy as reconciliation meta, scrub single-hyp and bare meta" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    var theorem = TheoremContext.init(allocator);
    defer theorem.deinit();

    // arg0: hyp0 & hyp1 (multi). arg1: hyp0 only (single). arg2: hyp0 & hyp1 (multi).
    const hyp0_args = [_]TemplateExpr{
        .{ .binder = 0 },
        .{ .binder = 1 },
        .{ .binder = 2 },
    };
    const hyp1_args = [_]TemplateExpr{
        .{ .binder = 0 },
        .{ .binder = 2 },
    };
    const hyps = [_]TemplateExpr{
        .{ .app = .{ .term_id = 0, .args = &hyp0_args } },
        .{ .app = .{ .term_id = 0, .args = &hyp1_args } },
    };

    const d0 = try theorem.addPlaceholderResolved("tm"); // standard dummy, multi → keep
    const d1 = try theorem.addPlaceholderResolved("tm"); // standard dummy, single → scrub
    const m2 = try theorem.addMetaPlaceholderResolved("tm"); // bare meta, multi → scrub
    var bindings = [_]?ExprId{ d0, d1, m2 };

    try seed.partitionSeedBindings(allocator, &theorem, &hyps, &bindings);

    // arg0 kept and converted to a reconciliation meta.
    try std.testing.expect(bindings[0] != null);
    const pid0 = switch (theorem.interner.node(bindings[0].?).*) {
        .placeholder => |id| id,
        else => return error.ExpectedPlaceholder,
    };
    try std.testing.expect(theorem.placeholderClass(pid0) == .meta);
    try std.testing.expect(theorem.placeholderInfo(pid0).?.reconciliation_meta);
    try std.testing.expect(theorem.hasReconciliationMetas());

    // arg1 (single-hyp dummy) scrubbed; arg2 (bare meta) scrubbed despite multi.
    try std.testing.expectEqual(@as(?ExprId, null), bindings[1]);
    try std.testing.expectEqual(@as(?ExprId, null), bindings[2]);
}

// A two-sided sequent calculus with an ACUI context, a two-premise
// left-implication rule (`lim`, principal `im a b` selected from the
// antecedent), and a one-premise left-conjunction rule (`lan`). Each fan-out
// test appends its own `theorem t` line whose conclusion is the search goal.
const fanout_seq_prefix =
    \\delimiter $ ( ) $;
    \\provable sort wff;
    \\sort ctx;
    \\term im (a b: wff): wff;
    \\term an (a b: wff): wff;
    \\term ctx_eq (g h: ctx): wff;
    \\term emp: ctx;
    \\--| @acui ctx_assoc ctx_comm emp ctx_idem
    \\term join (g h: ctx): ctx;
    \\term hyp (a: wff): ctx;
    \\term seq (g d: ctx): wff;
    \\term P: wff;
    \\term Q: wff;
    \\term R: wff;
    \\term S: wff;
    \\
    \\--| @relation ctx ctx_eq ctx_refl ctx_trans ctx_sym _
    \\axiom ctx_refl (g: ctx): $ ctx_eq g g $;
    \\axiom ctx_trans (g h i: ctx):
    \\  $ ctx_eq g h $ > $ ctx_eq h i $ > $ ctx_eq g i $;
    \\axiom ctx_sym (g h: ctx): $ ctx_eq g h $ > $ ctx_eq h g $;
    \\axiom ctx_assoc (g h i: ctx):
    \\  $ ctx_eq (join (join g h) i) (join g (join h i)) $;
    \\axiom ctx_comm (g h: ctx): $ ctx_eq (join g h) (join h g) $;
    \\axiom ctx_idem (g: ctx): $ ctx_eq (join g g) g $;
    \\axiom ctx_unit (g: ctx): $ ctx_eq (join emp g) g $;
    \\
    \\axiom lim (g d: ctx) (a b: wff):
    \\  $ seq g (join (hyp a) d) $ >
    \\  $ seq (join g (hyp b)) d $ >
    \\  $ seq (join g (hyp (im a b))) d $;
    \\axiom lan (g d: ctx) (a b: wff):
    \\  $ seq (join (join g (hyp a)) (hyp b)) d $ >
    \\  $ seq (join g (hyp (an a b))) d $;
    \\
;

// Build a `Context` over `fanout_seq_prefix ++ theorem_line`, take theorem `t`'s
// conclusion as the search goal, and append `rule_name`'s candidates to `list`.
// Everything allocates through `allocator` (an arena), so the caller's arena
// owns all of it; `holder.*` must outlive the candidates' use.
const FanoutHolder = struct {
    fixture: fixture_mod.Fixture = undefined,
    theorem: TheoremContext = undefined,
    harness: ContextHarness = undefined,
};

fn collectFanoutCandidates(
    allocator: std.mem.Allocator,
    holder: *FanoutHolder,
    mm0_src: []const u8,
    rule_name: []const u8,
    list: *std.ArrayListUnmanaged(types.ApplyCandidate),
) !void {
    holder.fixture = try fixtureFor(allocator, mm0_src, "t");
    holder.theorem = TheoremContext.init(allocator);
    try holder.theorem.seedAssertion(holder.fixture.assertion);
    holder.harness = ContextHarness.init(allocator);
    const context = holder.harness.context(&holder.fixture);
    const goal_expr = try holder.theorem.internParsedExpr(holder.fixture.assertion.concl);
    const goal: Goal = .{ .concrete = goal_expr };
    const rule_id = holder.fixture.env.getRuleId(rule_name) orelse
        return error.MissingRule;
    try seed.appendRuleCandidates(
        list,
        allocator,
        &context,
        goal,
        &holder.theorem,
        rule_id,
    );
}

test "principal fan-out: ambiguous two-premise principal yields one candidate per member" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    var holder: FanoutHolder = .{};
    var list = std.ArrayListUnmanaged(types.ApplyCandidate){};
    // Antecedent holds two implication members, so `lim`'s principal `(im a b)`
    // is shape-compatible with both — the case the plain seed abstains on.
    try collectFanoutCandidates(
        allocator,
        &holder,
        fanout_seq_prefix ++
            "theorem t: $ seq (join (join (hyp (im P Q)) (hyp (im R S))) (hyp Q)) (hyp Q) $;",
        "lim",
        &list,
    );

    try std.testing.expectEqual(@as(usize, 2), list.items.len);
    const rule = &holder.fixture.env.rules.items[
        @intCast(holder.fixture.env.getRuleId("lim").?)
    ];
    const a_idx = try ruleArgIndex(rule, "a");
    const b_idx = try ruleArgIndex(rule, "b");
    // Every variant pins both principal binders...
    for (list.items) |cand| {
        try std.testing.expect(cand.bindings[a_idx] != null);
        try std.testing.expect(cand.bindings[b_idx] != null);
    }
    // ...and the two variants pin DISTINCT principals (one per member).
    try std.testing.expect(
        list.items[0].bindings[a_idx].? != list.items[1].bindings[a_idx].?,
    );
}

test "principal fan-out: single matching member keeps one candidate" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    var holder: FanoutHolder = .{};
    var list = std.ArrayListUnmanaged(types.ApplyCandidate){};
    // Only one implication member ⇒ the seed pins it uniquely; no fan-out.
    try collectFanoutCandidates(
        allocator,
        &holder,
        fanout_seq_prefix ++
            "theorem t: $ seq (join (hyp (im P Q)) (hyp Q)) (hyp Q) $;",
        "lim",
        &list,
    );
    try std.testing.expectEqual(@as(usize, 1), list.items.len);
}

test "principal fan-out: one-premise rule is not fanned out" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    var holder: FanoutHolder = .{};
    var list = std.ArrayListUnmanaged(types.ApplyCandidate){};
    // Two conjunction members would make `lan`'s principal ambiguous, but `lan`
    // has a single premise: its loose backtrack is linear, so the premises≥2
    // gate keeps it a single candidate (the spurious-overhead guard the
    // budget-edge `drinker` case needs).
    try collectFanoutCandidates(
        allocator,
        &holder,
        fanout_seq_prefix ++
            "theorem t: $ seq (join (join (hyp (an P Q)) (hyp (an R S))) (hyp Q)) (hyp Q) $;",
        "lan",
        &list,
    );
    try std.testing.expectEqual(@as(usize, 1), list.items.len);
}

test "ACUI conclusion member prune scans below semantic container" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\sort ctx;
        \\term iff (a b: wff): wff;
        \\infixr iff: $<->$ prec 20;
        \\term ctx_eq (g h: ctx): wff;
        \\term emp: ctx;
        \\--| @acui ctx_assoc ctx_comm emp ctx_idem
        \\term join (g h: ctx): ctx;
        \\term hyp (a: wff): ctx;
        \\term nd (g: ctx) (a: wff): wff;
        \\
        \\--| @relation wff iff iff_refl iff_trans iff_sym iff_mp
        \\axiom iff_refl (a: wff): $ a <-> a $;
        \\axiom iff_trans (a b c: wff):
        \\  $ a <-> b $ > $ b <-> c $ > $ a <-> c $;
        \\axiom iff_sym (a b: wff): $ a <-> b $ > $ b <-> a $;
        \\axiom iff_mp (a b: wff): $ a <-> b $ > $ a $ > $ b $;
        \\
        \\--| @relation ctx ctx_eq ctx_refl ctx_trans ctx_sym _
        \\axiom ctx_refl (g: ctx): $ ctx_eq g g $;
        \\axiom ctx_trans (g h i: ctx):
        \\  $ ctx_eq g h $ > $ ctx_eq h i $ > $ ctx_eq g i $;
        \\axiom ctx_sym (g h: ctx): $ ctx_eq g h $ > $ ctx_eq h g $;
        \\axiom ctx_assoc (g h i: ctx):
        \\  $ ctx_eq (join (join g h) i) (join g (join h i)) $;
        \\axiom ctx_comm (g h: ctx): $ ctx_eq (join g h) (join h g) $;
        \\axiom ctx_idem (g: ctx): $ ctx_eq (join g g) g $;
        \\axiom ctx_unit (g: ctx): $ ctx_eq (join emp g) g $;
        \\
        \\axiom use_assump (g: ctx) (p: wff):
        \\  $ nd (join g (hyp p)) p $;
        \\theorem t (a b c: wff):
        \\  $ nd (join (hyp a) (hyp b)) c $;
    ;
    const proof_src =
        \\t
        \\------
        \\l1: $ nd (join (hyp a) (hyp b)) c $ by exact?
    ;
    const offset = std.mem.indexOf(u8, proof_src, "exact?") orelse
        return error.MissingNeedle;
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

    try std.testing.expectEqual(@as(usize, 0), suggestions.items.len);
    try std.testing.expectEqual(
        @as(usize, 0),
        counters.full_try_candidate_calls,
    );
    try std.testing.expect(counters.conclusion_member_prunes > 0);
}

test "ACUI member prune allows transparent def matching variable member" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\sort ctx;
        \\term iff (a b: wff): wff;
        \\infixr iff: $<->$ prec 20;
        \\term ctx_eq (g h: ctx): wff;
        \\term emp: ctx;
        \\--| @acui ctx_assoc ctx_comm emp ctx_idem
        \\term join (g h: ctx): ctx;
        \\term holds (g: ctx): wff;
        \\term nd (g: ctx) (a: wff): wff;
        \\
        \\def idctx (g: ctx): ctx = $ g $;
        \\
        \\--| @relation wff iff iff_refl iff_trans iff_sym iff_mp
        \\axiom iff_refl (a: wff): $ a <-> a $;
        \\axiom iff_trans (a b c: wff):
        \\  $ a <-> b $ > $ b <-> c $ > $ a <-> c $;
        \\axiom iff_sym (a b: wff): $ a <-> b $ > $ b <-> a $;
        \\axiom iff_mp (a b: wff): $ a <-> b $ > $ a $ > $ b $;
        \\
        \\--| @relation ctx ctx_eq ctx_refl ctx_trans ctx_sym _
        \\axiom ctx_refl (g: ctx): $ ctx_eq g g $;
        \\axiom ctx_trans (g h i: ctx):
        \\  $ ctx_eq g h $ > $ ctx_eq h i $ > $ ctx_eq g i $;
        \\axiom ctx_sym (g h: ctx): $ ctx_eq g h $ > $ ctx_eq h g $;
        \\axiom ctx_assoc (g h i: ctx):
        \\  $ ctx_eq (join (join g h) i) (join g (join h i)) $;
        \\axiom ctx_comm (g h: ctx): $ ctx_eq (join g h) (join h g) $;
        \\axiom ctx_idem (g: ctx): $ ctx_eq (join g g) g $;
        \\axiom ctx_unit (g: ctx): $ ctx_eq (join emp g) g $;
        \\
        \\axiom use_idctx (g h: ctx):
        \\  $ nd (join h (idctx g)) (holds g) $;
        \\theorem t (G H: ctx):
        \\  $ nd (join H G) (holds G) $;
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    var fixture = try fixtureFor(allocator, mm0_src, "t");
    var theorem = TheoremContext.init(allocator);
    defer theorem.deinit();
    try theorem.seedAssertion(fixture.assertion);
    var harness = ContextHarness.init(allocator);
    defer harness.deinit();
    const context = harness.context(&fixture);
    const goal_expr = try theorem.internParsedExpr(fixture.assertion.concl);
    const goal: Goal = .{ .concrete = goal_expr };
    const rule_id = fixture.env.getRuleId("use_idctx") orelse
        return error.MissingRule;
    var candidate = try seed.makeExactRuleCandidate(
        allocator,
        &context,
        goal,
        &theorem,
        rule_id,
    );
    defer candidate.deinit();
    const rule = &fixture.env.rules.items[@intCast(rule_id)];

    try std.testing.expect(prune.acuiBoundMembersPlausible(
        &context,
        &candidate.theorem,
        rule.concl,
        goal_expr,
        candidate.bindings,
    ));
}

test "exprUnifiesModuloMeta treats search metas as wildcards but prunes rigid clashes" {
    // The carry-to-leaf witness predicate behind the ACUI plausibility prune:
    // a binding embedding an open `.meta` leaf (e.g. `rim`'s `P ?t`) must stay
    // unifiable with a concrete member (`P c`) so the witness can be pinned at
    // validation, while a genuinely different rigid skeleton still prunes. No
    // env is consulted, so raw term ids and vars suffice.
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    var theorem = TheoremContext.init(allocator);
    defer theorem.deinit();

    const term_p: u32 = 1;
    const term_q: u32 = 2;
    const c = try theorem.interner.internVar(.{ .theorem_var = 0 });
    const d = try theorem.interner.internVar(.{ .theorem_var = 1 });
    const meta = try theorem.addMetaPlaceholderResolved("wff");

    const p_meta = try theorem.interner.internApp(term_p, &.{meta});
    const p_c = try theorem.interner.internApp(term_p, &.{c});
    const p_d = try theorem.interner.internApp(term_p, &.{d});
    const q_c = try theorem.interner.internApp(term_q, &.{c});

    const unifies = prune.exprUnifiesModuloMeta;
    // Meta absorbs the difference — buried (either side) or bare.
    try std.testing.expect(unifies(&theorem, p_meta, p_c));
    try std.testing.expect(unifies(&theorem, p_c, p_meta));
    try std.testing.expect(unifies(&theorem, meta, p_c));
    // Identity always unifies.
    try std.testing.expect(unifies(&theorem, p_c, p_c));
    // Rigid skeleton clashes still prune: differing argument var, differing
    // head, and a head clash that an embedded meta must NOT paper over.
    try std.testing.expect(!unifies(&theorem, p_c, p_d));
    try std.testing.expect(!unifies(&theorem, p_c, q_c));
    try std.testing.expect(!unifies(&theorem, p_meta, q_c));
}

test "solveCorrespondenceAcui matches commutative regions member-wise" {
    // The member-wise read-back matcher: a child conclusion ACUI-equal to the
    // open target but reordered/reassociated must still solve the target's
    // metas, while genuinely different multisets and non-commutative subsets
    // must not. Regions are matched as multisets only under a COMMUTATIVE
    // registered combiner (`join`); `join2` declares `_` for commutativity and
    // must stay positional.
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\sort ctx;
        \\term P: wff;
        \\term Q: wff;
        \\term R: wff;
        \\term emp: ctx;
        \\--| @acui ctx_assoc ctx_comm emp _
        \\term join (g h: ctx): ctx;
        \\term emp2: ctx;
        \\--| @acui ctx2_assoc _ emp2 _
        \\term join2 (g h: ctx): ctx;
        \\term hyp (a: wff): ctx;
        \\term boxed (g: ctx): ctx;
        \\theorem t: $ P $;
    ;
    var fixture = try fixtureFor(allocator, mm0_src, "t");
    var sink = DiagnosticSink.init(mm0_src, "");
    var compiler = CompilerContext.init(mm0_src, "", .none, &sink);
    _ = &compiler;
    var theorem = TheoremContext.init(allocator);
    defer theorem.deinit();
    try theorem.seedAssertion(fixture.assertion);
    var harness = ContextHarness.init(allocator);
    defer harness.deinit();
    const context = harness.context(&fixture);

    const join_id = fixture.env.term_names.get("join").?;
    const join2_id = fixture.env.term_names.get("join2").?;
    const emp_id = fixture.env.term_names.get("emp").?;
    const hyp_id = fixture.env.term_names.get("hyp").?;
    const p_id = fixture.env.term_names.get("P").?;
    const q_id = fixture.env.term_names.get("Q").?;
    const r_id = fixture.env.term_names.get("R").?;
    const hp = try theorem.interner.internApp(
        hyp_id,
        &.{try theorem.interner.internApp(p_id, &.{})},
    );
    const hq = try theorem.interner.internApp(
        hyp_id,
        &.{try theorem.interner.internApp(q_id, &.{})},
    );
    const hr = try theorem.interner.internApp(
        hyp_id,
        &.{try theorem.interner.internApp(r_id, &.{})},
    );

    var store = MetaStore.init(allocator, &fixture.env);
    defer store.deinit();
    const solve = Witness.solveCorrespondenceAcui;

    // Pure reassociation + reorder, no metas: (hp,hq),hr vs hq,(hr,hp).
    const left_nested = try theorem.interner.internApp(
        join_id,
        &.{ try theorem.interner.internApp(join_id, &.{ hp, hq }), hr },
    );
    const rotated = try theorem.interner.internApp(
        join_id,
        &.{ hq, try theorem.interner.internApp(join_id, &.{ hr, hp }) },
    );
    try std.testing.expect(try solve(&context, &store, &theorem, rotated, left_nested));

    // A whole-member meta absorbs the reordered complement: hp,?m vs
    // hq,(hr,hp) forces ?m := hq,hr (right-fold of the leftover members).
    const meta = try store.mint(&theorem, "ctx", std.math.maxInt(u55), .existential);
    const pat_meta = try theorem.interner.internApp(join_id, &.{ hp, meta });
    const mark = store.mark();
    try std.testing.expect(try solve(&context, &store, &theorem, rotated, pat_meta));
    try std.testing.expectEqual(
        try theorem.interner.internApp(join_id, &.{ hq, hr }),
        try store.materialize(&theorem, meta),
    );
    store.rollbackTo(mark);

    // Nothing left over: the meta takes the combiner's unit.
    try std.testing.expect(try solve(&context, &store, &theorem, hp, pat_meta));
    try std.testing.expectEqual(
        try theorem.interner.internApp(emp_id, &.{}),
        try store.materialize(&theorem, meta),
    );
    store.rollbackTo(mark);

    // Genuinely different multisets still conflict.
    const pq = try theorem.interner.internApp(join_id, &.{ hp, hq });
    const pr = try theorem.interner.internApp(join_id, &.{ hp, hr });
    try std.testing.expect(!(try solve(&context, &store, &theorem, pr, pq)));

    // Non-commutative subset (`join2`, comm declared `_`): reordering is NOT
    // reconcilable — the matcher must stay positional and reject.
    const pq2 = try theorem.interner.internApp(join2_id, &.{ hp, hq });
    const qp2 = try theorem.interner.internApp(join2_id, &.{ hq, hp });
    try std.testing.expect(!(try solve(&context, &store, &theorem, qp2, pq2)));

    // Foreign unit: `join2`'s unit `emp2` inside a `join` region is a REAL
    // member (join(emp2, X) is not ACUI-equal to X under join's laws), so a
    // source carrying it cannot cancel against a pattern without it.
    const emp2_id = fixture.env.term_names.get("emp2").?;
    const emp2 = try theorem.interner.internApp(emp2_id, &.{});
    const p_with_foreign_unit = try theorem.interner.internApp(join_id, &.{ hp, emp2 });
    try std.testing.expect(!(try solve(&context, &store, &theorem, p_with_foreign_unit, hp)));

    // The meta may absorb a foreign unit, though — it is a member like any
    // other.
    try std.testing.expect(try solve(&context, &store, &theorem, p_with_foreign_unit, pat_meta));
    try std.testing.expectEqual(emp2, try store.materialize(&theorem, meta));
    store.rollbackTo(mark);

    // Repeated meta, bare AND nested inside a structured member of the same
    // region: pass 2 solves `?m := hp` through `boxed ?m`, and the
    // whole-member complement branch must CONSISTENCY-CHECK the already-solved
    // meta against the leftover (`hp`) instead of failing the blind re-assign.
    const boxed_id = fixture.env.term_names.get("boxed").?;
    const boxed_meta = try theorem.interner.internApp(boxed_id, &.{meta});
    const boxed_hp = try theorem.interner.internApp(boxed_id, &.{hp});
    const pat_nested = try theorem.interner.internApp(join_id, &.{ meta, boxed_meta });
    const src_nested = try theorem.interner.internApp(join_id, &.{ boxed_hp, hp });
    try std.testing.expect(try solve(&context, &store, &theorem, src_nested, pat_nested));
    try std.testing.expectEqual(hp, try store.materialize(&theorem, meta));
    store.rollbackTo(mark);

    // Two DISTINCT whole-member metas in one region: no forced partition —
    // the matcher must abstain rather than guess.
    const meta2 = try store.mint(&theorem, "ctx", std.math.maxInt(u55), .existential);
    const pat_two_metas = try theorem.interner.internApp(join_id, &.{ meta, meta2 });
    try std.testing.expect(!(try solve(&context, &store, &theorem, rotated, pat_two_metas)));
}

test "search candidate supports view recover with holey goals" {
    try expectCaseLineSearch(
        "pass_hole_view_recover_matrix",
        "view_recover_visible_formula",
        0,
    );
}

test "apply search may list broad whole-line hole candidates" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\--| @hole _wff
        \\provable sort wff;
        \\term P: wff;
        \\axiom p: $ P $;
        \\theorem t: $ P $;
    ;
    try expectApplyContains(mm0_src, "t", "_wff", "p", 0, 0);
}

test "exact search accepts broad whole-line holes with useful refs" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\--| @hole _wff
        \\provable sort wff;
        \\term P: wff;
        \\axiom id (p: wff): $ p $ > $ p $;
        \\theorem t: $ P $ > $ P $;
    ;
    try expectFirstExactRefs(
        mm0_src,
        "",
        "t",
        "_wff",
        0,
        "id",
        &[_]ProofScript.Ref{.{ .hyp = .{
            .index = 1,
            .span = .{ .start = 0, .end = 0 },
        } }},
    );
}

test "exact search suppresses broad whole-line holes without refs" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\--| @hole _wff
        \\provable sort wff;
        \\term P: wff;
        \\axiom p: $ P $;
        \\theorem t: $ P $;
    ;
    try expectExactRuleOrder(mm0_src, "t", "_wff", &[_][]const u8{});
}

test "hole sort mismatches do not poison later search candidates" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\--| @hole _wff
        \\provable sort wff;
        \\--| @hole _obj
        \\provable sort obj;
        \\term W: wff;
        \\term O: obj;
        \\axiom bad_wff: $ W $;
        \\axiom good_obj: $ O $;
        \\theorem t: $ O $;
    ;
    try expectApplyContains(mm0_src, "t", "_obj", "good_obj", 0, 0);
}

test "abstract pruner skips rigid-bad broad refs before validation" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term imp (a b: wff): wff;
        \\infixr imp: $->$ prec 25;
        \\term iff (a b: wff): wff;
        \\infixr iff: $<->$ prec 20;
        \\term top: wff;
        \\term sb (t x: wff) (r: wff x): wff;
        \\--| @relation wff iff iff_refl iff_trans iff_sym iff_mp
        \\axiom iff_refl (a: wff): $ a <-> a $;
        \\axiom iff_trans (a b c: wff): $ a <-> b $ > $ b <-> c $ > $ a <-> c $;
        \\axiom iff_sym (a b: wff): $ a <-> b $ > $ b <-> a $;
        \\axiom iff_mp (a b: wff): $ a <-> b $ > $ a $ > $ b $;
        \\--| @rewrite
        \\axiom sb_var (t x: wff): $ sb t x x <-> t $;
        \\--| @rewrite
        \\axiom sb_top (t x: wff): $ sb t x top <-> top $;
        \\--| @rewrite
        \\axiom sb_imp (t x: wff) (a b: wff x):
        \\  $ sb t x (a -> b) <-> (sb t x a -> sb t x b) $;
        \\--| @congr
        \\axiom imp_congr (a b c d: wff):
        \\  $ a <-> b $ > $ c <-> d $ > $ (a -> c) <-> (b -> d) $;
        \\--| @view (a b: wff) (r: wff a) (p q: wff): $ a <-> b $ > $ p $ > $ q $
        \\--| @abstract r p q a a b
        \\axiom ax_ctx (a b: wff) (r: wff a):
        \\  $ a <-> b $ > $ sb a a r $ > $ sb b a r $;
        \\theorem t (a b c: wff):
        \\  $ a <-> b $ > $ a -> top $ > $ c -> top $ >
        \\  $ b -> top $;
    ;
    const proof_src =
        \\t
        \\------
        \\l1: $ b -> top $ by exact?
    ;
    const offset = std.mem.indexOf(u8, proof_src, "exact?") orelse
        return error.MissingNeedle;
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

    var found = false;
    for (suggestions.items) |item| {
        if (std.mem.eql(u8, item.replacement, "ax_ctx [#1, #2]")) {
            found = true;
        }
    }
    try std.testing.expect(found);
    try std.testing.expect(counters.abstract_prunes > 0);
}

test "abstract pruner resolves def heads to rigid roots, abstains on reducible heads" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term imp (a b: wff): wff;
        \\infixr imp: $->$ prec 25;
        \\term iff (a b: wff): wff;
        \\infixr iff: $<->$ prec 20;
        \\term top: wff;
        \\term sb (t x: wff) (r: wff x): wff;
        \\def hold (p: wff): wff = $ p $;
        \\def wrapiff (a b: wff): wff = $ a <-> b $;
        \\def wrapimp (a b: wff): wff = $ a -> b $;
        \\term pair (x y: wff): wff;
        \\def box {.x: wff} (a: wff): wff = $ pair x (a -> top) $;
        \\--| @relation wff iff iff_refl iff_trans iff_sym iff_mp
        \\axiom iff_refl (a: wff): $ a <-> a $;
        \\axiom iff_trans (a b c: wff): $ a <-> b $ > $ b <-> c $ > $ a <-> c $;
        \\axiom iff_sym (a b: wff): $ a <-> b $ > $ b <-> a $;
        \\axiom iff_mp (a b: wff): $ a <-> b $ > $ a $ > $ b $;
        \\--| @rewrite
        \\axiom sb_var (t x: wff): $ sb t x x <-> t $;
        \\--| @rewrite
        \\axiom sb_top (t x: wff): $ sb t x top <-> top $;
        \\--| @rewrite
        \\axiom sb_imp (t x: wff) (a b: wff x):
        \\  $ sb t x (a -> b) <-> (sb t x a -> sb t x b) $;
        \\--| @congr
        \\axiom imp_congr (a b c d: wff):
        \\  $ a <-> b $ > $ c <-> d $ > $ (a -> c) <-> (b -> d) $;
        \\--| @view (a b: wff) (r: wff a) (p q: wff): $ a <-> b $ > $ p $ > $ q $
        \\--| @abstract r p q a a b
        \\axiom ax_ctx (a b: wff) (r: wff a):
        \\  $ a <-> b $ > $ sb a a r $ > $ sb b a r $;
        \\theorem t (a b c: wff):
        \\  $ a <-> b $ > $ a -> top $ > $ c -> top $ >
        \\  $ hold (c -> top) $ > $ b -> top $;
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    var fixture = try fixtureFor(allocator, mm0_src, "t");
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
    const rule_id = fixture.env.getRuleId("ax_ctx") orelse
        return error.MissingRule;
    const view = fixture.views.get(rule_id) orelse return error.MissingView;
    const goal_expr = try parseConcreteGoal(
        &fixture,
        &theorem,
        &theorem_vars,
        "b -> top",
    );
    const eq_expr = try parseConcreteGoal(
        &fixture,
        &theorem,
        &theorem_vars,
        "a <-> b",
    );
    const good_expr = try parseConcreteGoal(
        &fixture,
        &theorem,
        &theorem_vars,
        "a -> top",
    );
    const rigid_bad_expr = try parseConcreteGoal(
        &fixture,
        &theorem,
        &theorem_vars,
        "c -> top",
    );
    // A transparent-def-headed ref whose head resolves (through the def's body)
    // to a *rigid root* that clashes with the goal: `wrapiff c c` has head
    // `wrapiff`, a `def … = $ a <-> b $`, so its rigid root is `iff`, which
    // differs from the goal's `imp`. The prune now (soundly) fires on this, where
    // the committed code abstained on every `termNeedsSemantic` def head. Doomed:
    // with left_plug == hole, the motive is forced to the ref, and `[a:=b]` of
    // `c <-> c` (no `a`) is `c <-> c` ≠ the goal `b -> top`.
    const def_clash_expr = try parseConcreteGoal(
        &fixture,
        &theorem,
        &theorem_vars,
        "wrapiff c c",
    );
    // A transparent identity def whose body is a bare binder. Head-only
    // resolution sees no rigid root, but the body walk can compare the
    // concrete argument and reject `c -> top` against the goal `b -> top`.
    const def_opaque_expr = try parseConcreteGoal(
        &fixture,
        &theorem,
        &theorem_vars,
        "hold (c -> top)",
    );
    // A genuinely reducible (`@rewrite`) head: `sb` is not a transparent def, so
    // it has no rigid root and a `@rewrite` rule could rewrite it to any head.
    // The prune must abstain rather than treat `sb` as a rigid root (the
    // `resolveRigidHead` `rewrites_by_head` guard).
    const reducible_expr = try parseConcreteGoal(
        &fixture,
        &theorem,
        &theorem_vars,
        "sb a a (c -> top)",
    );
    // Same transparent-def head on both sides: head resolution sees `imp` on
    // each side and used to abstain. The body walk can still find the definite
    // mismatch `c` vs `b` away from the plug pair (`a`, `b`).
    const same_def_bad_expr = try parseConcreteGoal(
        &fixture,
        &theorem,
        &theorem_vars,
        "wrapimp c top",
    );
    const same_def_good_expr = try parseConcreteGoal(
        &fixture,
        &theorem,
        &theorem_vars,
        "wrapimp a top",
    );
    const same_def_goal = try parseConcreteGoal(
        &fixture,
        &theorem,
        &theorem_vars,
        "wrapimp b top",
    );
    // Cross-def/raw comparison: `box c` unfolds to `pair x (c -> top)`,
    // so comparing against raw `pair a (b -> top)` can reject on `c` vs `b`
    // while ignoring the hidden dummy argument.
    const cross_def_bad_expr = try parseConcreteGoal(
        &fixture,
        &theorem,
        &theorem_vars,
        "box c",
    );
    const cross_def_good_expr = try parseConcreteGoal(
        &fixture,
        &theorem,
        &theorem_vars,
        "box a",
    );
    const cross_def_goal = try parseConcreteGoal(
        &fixture,
        &theorem,
        &theorem_vars,
        "pair a (b -> top)",
    );

    const eq_fill = abstract_prune.Fill{ .hyp_index = 0, .ref_expr = eq_expr };
    try std.testing.expect(!abstract_prune.abstractInfeasible(
        &theorem,
        &context,
        view,
        goal_expr,
        &.{ eq_fill, .{ .hyp_index = 1, .ref_expr = good_expr } },
    ));
    try std.testing.expect(abstract_prune.abstractInfeasible(
        &theorem,
        &context,
        view,
        goal_expr,
        &.{ eq_fill, .{ .hyp_index = 1, .ref_expr = rigid_bad_expr } },
    ));
    try std.testing.expect(abstract_prune.abstractInfeasible(
        &theorem,
        &context,
        view,
        goal_expr,
        &.{ eq_fill, .{ .hyp_index = 1, .ref_expr = def_clash_expr } },
    ));
    try std.testing.expect(abstract_prune.abstractInfeasible(
        &theorem,
        &context,
        view,
        goal_expr,
        &.{ eq_fill, .{ .hyp_index = 1, .ref_expr = def_opaque_expr } },
    ));
    try std.testing.expect(!abstract_prune.abstractInfeasible(
        &theorem,
        &context,
        view,
        goal_expr,
        &.{ eq_fill, .{ .hyp_index = 1, .ref_expr = reducible_expr } },
    ));
    try std.testing.expect(abstract_prune.abstractInfeasible(
        &theorem,
        &context,
        view,
        same_def_goal,
        &.{ eq_fill, .{ .hyp_index = 1, .ref_expr = same_def_bad_expr } },
    ));
    try std.testing.expect(!abstract_prune.abstractInfeasible(
        &theorem,
        &context,
        view,
        same_def_goal,
        &.{ eq_fill, .{ .hyp_index = 1, .ref_expr = same_def_good_expr } },
    ));
    try std.testing.expect(abstract_prune.abstractInfeasible(
        &theorem,
        &context,
        view,
        cross_def_goal,
        &.{ eq_fill, .{ .hyp_index = 1, .ref_expr = cross_def_bad_expr } },
    ));
    try std.testing.expect(!abstract_prune.abstractInfeasible(
        &theorem,
        &context,
        view,
        cross_def_goal,
        &.{ eq_fill, .{ .hyp_index = 1, .ref_expr = cross_def_good_expr } },
    ));

    // Reducible-PLUG cases. The equation ref `wrapiff c c <-> b` binds the
    // plug/hole `a` to `wrapiff c c` — a transparent-def-headed (reducible) term,
    // so the raw-ExprId hole test is unreliable and the committed code bailed the
    // whole decl. The walk now switches to the head-aware hole guard.
    const eq_reducible_expr = try parseConcreteGoal(
        &fixture,
        &theorem,
        &theorem_vars,
        "wrapiff c c <-> b",
    );
    const eq_reducible_fill = abstract_prune.Fill{
        .hyp_index = 0,
        .ref_expr = eq_reducible_expr,
    };
    // The replaced hypothesis `wrapiff c c -> top`: the plug occurs at `imp`'s
    // first arg, in folded form here (and unfolds to `c <-> c`).
    const imp_wrap_expr = try parseConcreteGoal(
        &fixture,
        &theorem,
        &theorem_vars,
        "wrapiff c c -> top",
    );
    // PRUNE: conclusion `b <-> top` clashes at the top `imp` (hyp) vs `iff` (goal)
    // — a rigid-root clash at a node the head-aware guard proves is NOT the hole
    // (`imp`/`iff` ≠ the plug's resolved root `iff`/… is irrelevant: the clash is
    // above any hole). Replacing `wrapiff c c` by `b` in `wrapiff c c -> top`
    // yields `b -> top` (`imp`), never `b <-> top`, so the candidate is doomed.
    const goal_iff = try parseConcreteGoal(
        &fixture,
        &theorem,
        &theorem_vars,
        "b <-> top",
    );
    try std.testing.expect(abstract_prune.abstractInfeasible(
        &theorem,
        &context,
        view,
        goal_iff,
        &.{ eq_reducible_fill, .{ .hyp_index = 1, .ref_expr = imp_wrap_expr } },
    ));
    // ABSTAIN: the genuinely valid replacement — `wrapiff c c -> top` with
    // `wrapiff c c` ↦ `b` is exactly the goal `b -> top`. At the plug position the
    // head-aware guard sees the folded occurrence share the plug's rigid root and
    // holds no opinion, so the prune must NOT fire.
    try std.testing.expect(!abstract_prune.abstractInfeasible(
        &theorem,
        &context,
        view,
        goal_expr,
        &.{ eq_reducible_fill, .{ .hyp_index = 1, .ref_expr = imp_wrap_expr } },
    ));
}

test "context pruner counts absent members against the discharge budget" {
    const mm0_src =
        \\delimiter $ ( ) , $;
        \\strict provable sort wff;
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
        \\term A: wff;
        \\term B: wff;
        \\term C: wff;
        \\term D: wff;
        \\term Q: wff;
        \\axiom ctx_assoc (G H K: ctx): $ ctx_eq ((G , H) , K) (G , (H , K)) $;
        \\axiom ctx_comm (G H: ctx): $ ctx_eq (G , H) (H , G) $;
        \\axiom ctx_idem (G: ctx): $ ctx_eq (G , G) G $;
        \\--| @view (G H: ctx) (p q r: wff): $ G ⊢ p $ > $ H ⊢ q $ > $ G , H ⊢ r $
        \\axiom carry (G H: ctx) (p q r: wff):
        \\  $ G ⊢ p $ > $ H ⊢ q $ > $ G , H ⊢ r $;
        \\--| @view (G H: ctx) (p c: wff): $ G ⊢ p $ > $ H , p ⊢ c $ > $ G , H ⊢ c $
        \\axiom discharge (G H: ctx) (p c: wff):
        \\  $ G ⊢ p $ > $ H , p ⊢ c $ > $ G , H ⊢ c $;
        \\--| @view (G H K: ctx) (p q r: wff): $ G ⊢ p $ > $ K ⊢ q $ > $ G , H ⊢ r $
        \\axiom drop (G H K: ctx) (p q r: wff):
        \\  $ G ⊢ p $ > $ K ⊢ q $ > $ G , H ⊢ r $;
        \\theorem t (G H: ctx): $ G , H ⊢ Q $;
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

    const carry_view = fixture.views.get(
        fixture.env.getRuleId("carry") orelse return error.MissingRule,
    ) orelse return error.MissingView;
    const discharge_view = fixture.views.get(
        fixture.env.getRuleId("discharge") orelse return error.MissingRule,
    ) orelse return error.MissingView;

    const drop_view = fixture.views.get(
        fixture.env.getRuleId("drop") orelse return error.MissingRule,
    ) orelse return error.MissingView;

    const carry_info = context_prune.analyzeView(&context, carry_view) orelse
        return error.AnalyzeFailed;
    const discharge_info = context_prune.analyzeView(&context, discharge_view) orelse
        return error.AnalyzeFailed;
    const drop_info = context_prune.analyzeView(&context, drop_view) orelse
        return error.AnalyzeFailed;
    // `carry` keeps every hypothesis context member; `discharge`'s second hyp
    // (`H , p`) drops the coerced `hyp(p)`, so its budget is one.
    try std.testing.expectEqual(@as(?u8, 0), carry_info.hyp_budgets[1]);
    try std.testing.expectEqual(@as(?u8, 1), discharge_info.hyp_budgets[1]);
    // `drop`'s second hyp context (`K`) is a bare binder absent from the
    // conclusion context (`G , H`): it discharges a WHOLE sub-context, which can
    // stand for unboundedly many concrete members, so the budget is null
    // (abstain — no prune may fire for that hypothesis).
    try std.testing.expectEqual(@as(?u8, null), drop_info.hyp_budgets[1]);

    const goal = try parseConcreteGoal(&fixture, &theorem, &theorem_vars, "A , B ⊢ Q");
    const ref_B = try parseConcreteGoal(&fixture, &theorem, &theorem_vars, "B ⊢ Q");
    const ref_C = try parseConcreteGoal(&fixture, &theorem, &theorem_vars, "C ⊢ Q");
    const ref_BC = try parseConcreteGoal(&fixture, &theorem, &theorem_vars, "B , C ⊢ Q");
    const ref_CD = try parseConcreteGoal(&fixture, &theorem, &theorem_vars, "C , D ⊢ Q");

    // Non-discharging (budget 0): a ref-context member absent from the goal
    // context (`C`) prunes; one already present (`B`) abstains.
    try std.testing.expect(context_prune.contextInfeasible(
        &theorem,
        &context,
        carry_info,
        goal,
        &.{.{ .hyp_index = 1, .ref_expr = ref_C }},
        null,
    ));
    try std.testing.expect(!context_prune.contextInfeasible(
        &theorem,
        &context,
        carry_info,
        goal,
        &.{.{ .hyp_index = 1, .ref_expr = ref_B }},
        null,
    ));

    // Discharging (budget 1): one absent member (`C`, the discharged assumption)
    // is under budget and abstains; two absent members (`C`, `D`) exceed it.
    try std.testing.expect(!context_prune.contextInfeasible(
        &theorem,
        &context,
        discharge_info,
        goal,
        &.{.{ .hyp_index = 1, .ref_expr = ref_BC }},
        null,
    ));
    try std.testing.expect(context_prune.contextInfeasible(
        &theorem,
        &context,
        discharge_info,
        goal,
        &.{.{ .hyp_index = 1, .ref_expr = ref_CD }},
        null,
    ));

    // Null budget (abstain): `drop`'s second hyp could discharge any number of
    // members, so even a ref-context full of absent members (`C , D`) must NOT
    // prune — the analyzer holds no opinion on that hypothesis.
    try std.testing.expect(!context_prune.contextInfeasible(
        &theorem,
        &context,
        drop_info,
        goal,
        &.{.{ .hyp_index = 1, .ref_expr = ref_CD }},
        null,
    ));

    // The ACUI unit (`emp`, written `_`) contributes no member: a ref context
    // `B , emp` flattens to just `B`, which is present in the goal, so the
    // budget-0 `carry` hyp abstains rather than counting `emp` as absent.
    const ref_B_emp = try parseConcreteGoal(&fixture, &theorem, &theorem_vars, "B , _ ⊢ Q");
    try std.testing.expect(!context_prune.contextInfeasible(
        &theorem,
        &context,
        carry_info,
        goal,
        &.{.{ .hyp_index = 1, .ref_expr = ref_B_emp }},
        null,
    ));
}

test "raw context pruner matches discharged member shape" {
    const mm0_src =
        \\delimiter $ ( ) , $;
        \\strict provable sort wff;
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
        \\term eq (p q: wff): wff;
        \\infixl eq: $=$ prec 10;
        \\term Q: wff;
        \\term T: wff;
        \\term U: wff;
        \\term X: wff;
        \\axiom ctx_assoc (G H K: ctx): $ ctx_eq ((G , H) , K) (G , (H , K)) $;
        \\axiom ctx_comm (G H: ctx): $ ctx_eq (G , H) (H , G) $;
        \\axiom ctx_idem (G: ctx): $ ctx_eq (G , G) G $;
        \\axiom inst (G: ctx) {x: wff} (t a: wff x):
        \\  $ G ⊢ t $ > $ G , x = t ⊢ a $ > $ G ⊢ a $;
        \\theorem th (G: ctx) {X: wff}: $ G ⊢ Q $;
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    var fixture = try fixtureFor(allocator, mm0_src, "th");
    var theorem = TheoremContext.init(allocator);
    defer theorem.deinit();
    try theorem.seedAssertion(fixture.assertion);
    var theorem_vars = try Check.buildTheoremVarMap(allocator, fixture.assertion);
    defer theorem_vars.deinit();
    var harness = ContextHarness.init(allocator);
    defer harness.deinit();
    const context = harness.context(&fixture);

    const rule_id = fixture.env.getRuleId("inst") orelse return error.MissingRule;
    const rule = fixture.env.rules.items[rule_id];
    const info = context_prune.analyzeRule(&context, rule) orelse
        return error.AnalyzeFailed;
    try std.testing.expectEqual(@as(?u8, 1), info.hyp_budgets[1]);

    const goal = try parseConcreteGoal(&fixture, &theorem, &theorem_vars, "G ⊢ Q");
    const ref_good = try parseConcreteGoal(
        &fixture,
        &theorem,
        &theorem_vars,
        "G , X = T ⊢ Q",
    );
    const ref_bad = try parseConcreteGoal(
        &fixture,
        &theorem,
        &theorem_vars,
        "G , X = U ⊢ Q",
    );
    const t_jdg = try parseConcreteGoal(&fixture, &theorem, &theorem_vars, "G ⊢ T");
    const t_expr = theorem.interner.node(t_jdg).app.args[1];
    var bindings = [_]?ExprId{null} ** 4;
    bindings[2] = t_expr;

    try std.testing.expect(!context_prune.contextInfeasible(
        &theorem,
        &context,
        info,
        goal,
        &.{.{ .hyp_index = 1, .ref_expr = ref_good }},
        &bindings,
    ));
    try std.testing.expect(context_prune.contextInfeasible(
        &theorem,
        &context,
        info,
        goal,
        &.{.{ .hyp_index = 1, .ref_expr = ref_bad }},
        &bindings,
    ));

    // Idempotent case: the selected ref contributes no absent member because
    // the goal already carries `X = T`. With `x` still open, requiring explicit
    // support for the bound-binder discharge prunes `x = U` but keeps `x = T`.
    const goal_with_eq = try parseConcreteGoal(
        &fixture,
        &theorem,
        &theorem_vars,
        "G , X = T ⊢ Q",
    );
    const u_jdg = try parseConcreteGoal(&fixture, &theorem, &theorem_vars, "G ⊢ U");
    const u_expr = theorem.interner.node(u_jdg).app.args[1];
    bindings[2] = u_expr;
    try std.testing.expect(context_prune.contextInfeasible(
        &theorem,
        &context,
        info,
        goal_with_eq,
        &.{.{ .hyp_index = 1, .ref_expr = goal_with_eq }},
        &bindings,
    ));
    bindings[2] = t_expr;
    try std.testing.expect(!context_prune.contextInfeasible(
        &theorem,
        &context,
        info,
        goal_with_eq,
        &.{.{ .hyp_index = 1, .ref_expr = goal_with_eq }},
        &bindings,
    ));
}

fn parseConcreteGoal(
    fixture: anytype,
    theorem: *TheoremContext,
    theorem_vars: *NameExprMap,
    text: []const u8,
) !ExprId {
    return switch (try parseGoal(fixture, theorem, theorem_vars, text)) {
        .concrete => |expr| expr,
        .implicit_whole_conclusion, .holey => error.ExpectedConcreteGoal,
    };
}

test "exact keeps ACUI view conclusion split binders open" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    const mm0_src = try readProofCase(allocator, "euclid", "mm0");
    const proof_src =
        \\le_antisym_ax
        \\-------------
        \\l1: $ g ⊢ ∃ k (a + k = b) $ by le_iff_add [#1]
        \\l2: $ h ⊢ ∃ m (b + m = a) $ by le_iff_add [#2]
        \\l3: $ a + k = b ⊢ a + k = b $ by ax
        \\l4: $ b + m = a ⊢ b + m = a $ by ax
        \\l5: $ a + k = b ⊢ b = a + k $ by eq_sym_nd [l3]
        \\l7: $ a + k = b , b + m = a ⊢ (a + k) + m = a $
        \\  by eq_replace [l5, l4]
        \\l8: $ _ ⊢ (a + k) + m = a + (k + m) $ by add_assoc_ax
        \\l9: $ a + k = b , b + m = a ⊢ a + (k + m) = a $
        \\  by exact?
    ;
    const offset = std.mem.indexOf(u8, proof_src, "exact?") orelse
        return error.MissingNeedle;
    var suggestions = try source.suggestionsAtSourceOffset(
        allocator,
        mm0_src,
        proof_src,
        offset,
        .{},
    );
    defer suggestions.deinit();

    for (suggestions.items) |item| {
        if (std.mem.eql(u8, item.replacement, "eq_replace [l8, l7]")) {
            return;
        }
    }
    return error.ExpectedSourceSuggestion;
}

test "exact recovers ex_intro with reused named existential binder" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    const mm0_src = try readProofCase(allocator, "euclid", "mm0");
    const proof_src =
        \\le_iff_add
        \\----------
        \\l1: $ x + k = y ⊢ x + k = y $ by ax
        \\l2: $ x + k = y ⊢ ∃ k (x + k = y) $ by exact?
    ;
    const offset = std.mem.indexOf(u8, proof_src, "exact?") orelse
        return error.MissingNeedle;
    var suggestions = try source.suggestionsAtSourceOffset(
        allocator,
        mm0_src,
        proof_src,
        offset,
        .{},
    );
    defer suggestions.deinit();

    for (suggestions.items) |item| {
        if (std.mem.eql(u8, item.replacement, "ex_intro [l1]")) {
            return;
        }
    }
    return error.ExpectedSourceSuggestion;
}

test "exact uses view hyp shape to discover ex_intro past substitution head" {
    // The raw hypothesis of `ex_intro` is `[x/t] p` — substitution-headed.
    // The theorem hypothesis `P c` does not have `sb_f` at the head, so both
    // the ref-index lookup and per-hyp matching using the raw template skip
    // it, leaving `exact?` with no candidate. The @view exposes the
    // hypothesis as just `q` (an unconstrained wff), making the ref
    // discoverable. The full validator then accepts `ex_intro [l1]` via the
    // `sb_f_P` / `sb_s_var` rewrite axioms (with the help of `P_congr`).
    const mm0_src =
        \\delimiter $ ( ) [ / ] $;
        \\provable sort wff;
        \\--| @vars x y z t
        \\sort nat;
        \\
        \\term ex {x: nat} (p: wff x): wff;
        \\prefix ex: $E$ prec 41;
        \\
        \\term sb_f {x: nat} (t: nat x) (p: wff x): wff;
        \\notation sb_f {x: nat} (t: nat x) (p: wff x): wff =
        \\  ($[$:41) x ($/$:0) t ($]$:0) p;
        \\
        \\term sb_s {x: nat} (t: nat x) (a: nat x): nat;
        \\notation sb_s {x: nat} (t: nat x) (a: nat x): nat =
        \\  ($subst$:41) x ($/$:0) t a;
        \\
        \\term P (a: nat): wff;
        \\term c: nat;
        \\
        \\term iff (a b: wff): wff;
        \\infixr iff: $<->$ prec 20;
        \\term nat_eq (a b: nat): wff;
        \\infixl nat_eq: $==$ prec 35;
        \\
        \\--| @relation wff iff iff_refl iff_trans iff_sym iff_mp
        \\axiom iff_refl (a: wff): $ a <-> a $;
        \\axiom iff_trans (a b c: wff): $ a <-> b $ > $ b <-> c $ > $ a <-> c $;
        \\axiom iff_sym (a b: wff): $ a <-> b $ > $ b <-> a $;
        \\axiom iff_mp (a b: wff): $ a <-> b $ > $ a $ > $ b $;
        \\
        \\--| @relation nat nat_eq eq_refl eq_trans eq_sym _
        \\axiom eq_refl (a: nat): $ a == a $;
        \\axiom eq_trans (a b c: nat): $ a == b $ > $ b == c $ > $ a == c $;
        \\axiom eq_sym (a b: nat): $ a == b $ > $ b == a $;
        \\
        \\--| @congr
        \\axiom P_congr (a b: nat): $ a == b $ > $ P a <-> P b $;
        \\
        \\--| @rewrite
        \\axiom sb_f_P {x: nat} (t a: nat x):
        \\  $ [x/t] (P a) <-> P (subst x / t a) $;
        \\
        \\--| @rewrite
        \\axiom sb_s_var {x: nat} (t: nat x): $ subst x / t x == t $;
        \\
        \\axiom have_Pc: $ P c $;
        \\
        \\--| @view {x: nat} (t: nat x) (p: wff x) (q: wff): $ q $ > $ E x p $
        \\--| @recover t q p x
        \\axiom ex_intro {x: nat} (t: nat x) (p: wff x):
        \\  $ [x/t] p $ > $ E x p $;
        \\
        \\theorem prove_exists {x: nat}: $ E x (P x) $;
    ;
    const proof_src =
        \\prove_exists
        \\------------
        \\l1: $ P c $ by have_Pc
        \\l2: $ E x (P x) $ by exact?
    ;
    try expectFirstExactRefs(
        mm0_src,
        proof_src,
        "prove_exists",
        "E x (P x)",
        1,
        "ex_intro",
        &[_]ProofScript.Ref{.{ .line = .{
            .label = "l1",
            .span = .{ .start = 0, .end = 0 },
        } }},
    );
}

// ============================================================
// Single-layer forward saturation with universal metas
// (META.md). Forward firing is gated on `@auto forward` metadata
// and runs only inside the `auto?` generation driver.
// ============================================================

// Concrete forward chain: `pq` is fired forward on hyp #1 (`P K`),
// deriving `Q K` with recipe `pq (x := $ K $) [#1]`. The backward
// `qr` premise `Q x` is open (x does not appear in the conclusion
// `R`), so neither the pool nor concrete generation can fill it —
// only the derived ref can.
const fwd_concrete_mm0 =
    \\delimiter $ ( ) $;
    \\provable sort wff;
    \\sort obj;
    \\term P (x: obj): wff;
    \\term Q (x: obj): wff;
    \\term R: wff;
    \\term K: obj;
    \\term pr (a b: obj): obj;
    \\--| @auto forward
    \\axiom pq (x: obj): $ P x $ > $ Q x $;
    \\--| @auto forward
    \\axiom pq2 (x y: obj): $ P x $ > $ Q (pr x y) $;
    \\axiom qr (x: obj): $ Q x $ > $ R $;
    \\theorem t: $ P K $ > $ R $;
;

test "forward saturation derives a concrete ref usable by auto" {
    const proof_src =
        \\t
        \\----
        \\l1: $ R $ by auto?
    ;
    const offset = std.mem.indexOf(u8, proof_src, "auto?") orelse
        return error.MissingNeedle;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    var suggestions = try source.suggestionsAtSourceOffset(
        arena.allocator(),
        fwd_concrete_mm0,
        proof_src,
        offset,
        .{ .counters = &counters, .generate = .{ .enabled = true } },
    );
    defer suggestions.deinit();

    var found = false;
    for (suggestions.items) |item| {
        if (std.mem.eql(
            u8,
            item.replacement,
            "qr [pq (x := $ K $) [#1]]",
        )) found = true;
    }
    try std.testing.expect(found);
    // `pq` fired on `P K` concretely. `pq2`'s unbound conclusion binder `y`
    // is deferred as a universal meta, deriving the family fact
    // `Q (pr K ?y)` — nothing solves `?y` here (the goal `R` never shows a
    // witness), so the family fact fails cleanly and adds no suggestion.
    try std.testing.expectEqual(@as(usize, 2), counters.derived_ref_count);
    try std.testing.expect(counters.forward_rule_attempts > 0);
    try std.testing.expectEqual(@as(usize, 1), counters.universal_metas_created);
}

// Family-fact derivation from an unbound conclusion binder (the bot_elim
// shape): `seq g bot > seq g a` fires forward on a `⊥`-style fact as
// `seq G ?a`, and a later goal solves the hole positionally — the same
// use-time discipline as a `@recover`-deferred witness. The `anything`
// rule's conclusion is a bare binder, so its surface would be a bare meta
// (an absorber, not a fact): it must derive nothing.
const fwd_family_mm0 =
    \\delimiter $ ( ) $;
    \\provable sort jdg;
    \\sort wff;
    \\sort ctx;
    \\term seq (g: ctx) (a: wff): jdg;
    \\term bot: wff;
    \\term G: ctx;
    \\term q: wff;
    \\--| @auto forward
    \\axiom bot_elim (g: ctx) (a: wff): $ seq g bot $ > $ seq g a $;
    \\--| @auto forward
    \\axiom anything (j: jdg) (g: ctx): $ seq g bot $ > $ j $;
    \\theorem t: $ seq G bot $ > $ seq G q $;
;

test "forward family fact from unbound conclusion binder solves at the goal" {
    const proof_src =
        \\t
        \\----
        \\l1: $ seq G q $ by auto?
    ;
    const offset = std.mem.indexOf(u8, proof_src, "auto?") orelse
        return error.MissingNeedle;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    var suggestions = try source.suggestionsAtSourceOffset(
        arena.allocator(),
        fwd_family_mm0,
        proof_src,
        offset,
        .{ .counters = &counters, .generate = .{ .enabled = true } },
    );
    defer suggestions.deinit();

    var found = false;
    for (suggestions.items) |item| {
        if (std.mem.eql(
            u8,
            item.replacement,
            "bot_elim (g := $ G $, a := $ q $) [#1]",
        )) found = true;
    }
    try std.testing.expect(found);
    // `bot_elim` derived the family fact; `anything`'s bare-meta surface
    // was rejected by the absorber guard.
    try std.testing.expectEqual(@as(usize, 1), counters.derived_ref_count);
}

// Forward JOIN grounding a nested source's universal meta. `genimp` fires on
// `Trigger`, deferring its unbound conclusion binder `x` to derive the universal
// FAMILY fact `imp (P ?x) (Q ?x)`. `mp` (forward) then joins that family's
// major premise with the concrete `P c`: matching the already-bound `a := P ?x`
// against `P c` grounds `?x := c` in the join overlay, so the consequent
// dereferences to the concrete fact `Q c` (`?x := c` baked as a pin on `Q c`'s
// recipe). The backward `qr` premise `Q x` (x absent from its conclusion) can
// only be filled by that derived `Q c` — so finding the proof at all proves the
// join produced a concrete consequent (without the join, no `Q` fact exists).
const fwd_join_mm0 =
    \\delimiter $ ( ) $;
    \\provable sort wff;
    \\sort obj;
    \\term imp (a b: wff): wff;
    \\term P (x: obj): wff;
    \\term Q (x: obj): wff;
    \\term Trigger: wff;
    \\term Goal: wff;
    \\term c: obj;
    \\--| @auto forward
    \\axiom genimp (x: obj): $ Trigger $ > $ imp (P x) (Q x) $;
    \\--| @auto forward
    \\axiom mp (a b: wff): $ imp a b $ > $ a $ > $ b $;
    \\axiom qr (x: obj): $ Q x $ > $ Goal $;
    \\theorem t: $ Trigger $ > $ P c $ > $ Goal $;
;

test "forward join grounds a nested family meta into a concrete fact" {
    const proof_src =
        \\t
        \\----
        \\l1: $ Goal $ by auto?
    ;
    const offset = std.mem.indexOf(u8, proof_src, "auto?") orelse
        return error.MissingNeedle;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    var suggestions = try source.suggestionsAtSourceOffset(
        arena.allocator(),
        fwd_join_mm0,
        proof_src,
        offset,
        .{ .counters = &counters, .generate = .{ .enabled = true } },
    );
    defer suggestions.deinit();

    // The witness `c` must ride the join into the nested family instance: the
    // recipe renders `genimp (x := $ c $)` (the pin), wrapped by `mp` and `qr`.
    var found = false;
    for (suggestions.items) |item| {
        if (std.mem.indexOf(u8, item.replacement, "genimp (x := $ c $)") != null and
            std.mem.indexOf(u8, item.replacement, "mp ") != null)
        {
            found = true;
        }
    }
    try std.testing.expect(found);
    // Two derived facts: the `imp (P ?x) (Q ?x)` family and the join's `Q c`.
    try std.testing.expectEqual(@as(usize, 2), counters.derived_ref_count);
}

// Negative: the forward join must not FABRICATE a witness. Same chain as the
// join test but with NO base fact — only the implication families `imp (P ?x)
// (Q ?x)` and `imp (Q ?y) (S ?y)` are derivable from `Trigger`, and nothing
// seeds a concrete `P`/`Q`/`S`. So `Goal` (which needs some `S x`) is genuinely
// underivable (countermodel: one element, P=Q=S false). The engine must return
// no proof — search may only PROPOSE; `tryCandidate` validates, so a returned
// suggestion would have to be a real proof, which cannot exist here.
const fwd_no_anchor_mm0 =
    \\delimiter $ ( ) $;
    \\provable sort wff;
    \\sort obj;
    \\term imp (a b: wff): wff;
    \\term P (x: obj): wff;
    \\term Q (x: obj): wff;
    \\term S (x: obj): wff;
    \\term Trigger: wff;
    \\term Goal: wff;
    \\--| @auto forward
    \\axiom genPQ (x: obj): $ Trigger $ > $ imp (P x) (Q x) $;
    \\--| @auto forward
    \\axiom genQS (x: obj): $ Trigger $ > $ imp (Q x) (S x) $;
    \\--| @auto forward
    \\axiom mp (a b: wff): $ imp a b $ > $ a $ > $ b $;
    \\axiom sr (x: obj): $ S x $ > $ Goal $;
    \\theorem t: $ Trigger $ > $ Goal $;
;

test "forward join does not fabricate a witness without a base fact" {
    const proof_src =
        \\t
        \\----
        \\l1: $ Goal $ by auto?
    ;
    const offset = std.mem.indexOf(u8, proof_src, "auto?") orelse
        return error.MissingNeedle;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    var suggestions = try source.suggestionsAtSourceOffset(
        arena.allocator(),
        fwd_no_anchor_mm0,
        proof_src,
        offset,
        .{ .counters = &counters, .generate = .{ .enabled = true } },
    );
    defer suggestions.deinit();

    // No proof exists: the engine must offer none (and not loop/crash trying to
    // invent the impossible witness). The two implication families derive; the
    // join finds no concrete antecedent to fire on.
    try std.testing.expectEqual(@as(usize, 0), suggestions.items.len);
}

test "forward premise matching unfolds nested concrete defs on demand" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\sort obj;
        \\term P (x: obj): wff;
        \\term Q (x: obj): wff;
        \\term box (p: wff): wff;
        \\term R: wff;
        \\term K: obj;
        \\def folded (x: obj): wff = $ P x $;
        \\--| @auto forward
        \\axiom pq_box (x: obj): $ box (P x) $ > $ Q x $;
        \\axiom qr (x: obj): $ Q x $ > $ R $;
        \\theorem t: $ box (folded K) $ > $ R $;
    ;
    const proof_src =
        \\t
        \\----
        \\l1: $ R $ by auto?
    ;
    const offset = std.mem.indexOf(u8, proof_src, "auto?") orelse
        return error.MissingNeedle;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    var suggestions = try source.suggestionsAtSourceOffset(
        arena.allocator(),
        mm0_src,
        proof_src,
        offset,
        .{ .counters = &counters, .generate = .{ .enabled = true } },
    );
    defer suggestions.deinit();

    var found = false;
    for (suggestions.items) |item| {
        if (std.mem.eql(
            u8,
            item.replacement,
            "qr [pq_box (x := $ K $) [#1]]",
        )) found = true;
    }
    try std.testing.expect(found);
    try std.testing.expectEqual(@as(usize, 1), counters.derived_ref_count);
    try std.testing.expect(counters.forward_match_tuples > 0);
}

test "exact does not run forward saturation or use derived refs" {
    const proof_src =
        \\t
        \\----
        \\l1: $ R $ by exact?
    ;
    const offset = std.mem.indexOf(u8, proof_src, "exact?") orelse
        return error.MissingNeedle;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    var suggestions = try source.suggestionsAtSourceOffset(
        arena.allocator(),
        fwd_concrete_mm0,
        proof_src,
        offset,
        .{ .counters = &counters, .generate = .{ .enabled = true } },
    );
    defer suggestions.deinit();
    try std.testing.expectEqual(@as(usize, 0), suggestions.items.len);
    try std.testing.expectEqual(@as(usize, 0), counters.derived_ref_count);
    try std.testing.expectEqual(@as(usize, 0), counters.forward_rule_attempts);
}

// Universal-meta theory: a self-contained copy of the bench `all_elim`
// theory (no `mono` def), so the forward premise match is DIRECT (no
// unfold) and the derived shape carries the witness meta at two
// positions: `pair f ?t = pair ?t f`.
const fwd_universal_mm0 =
    \\delimiter $ ( ) [ / ] $;
    \\provable sort wff;
    \\sort obj;
    \\term imp (a b: wff): wff;
    \\infixr imp: $→$ prec 25;
    \\term iff (a b: wff): wff;
    \\infixr iff: $↔$ prec 20;
    \\term all {x: obj} (p: wff x): wff;
    \\prefix all: $∀$ prec 41;
    \\term eq (a b: obj): wff;
    \\infixl eq: $=$ prec 35;
    \\term pair (a b: obj): obj;
    \\term sb_t {x: obj} (t: obj x) (a: obj x): obj;
    \\notation sb_t {x: obj} (t: obj x) (a: obj x): obj =
    \\  ($subst$:41) x ($/$:0) t a;
    \\term sb_f {x: obj} (t: obj x) (p: wff x): wff;
    \\notation sb_f {x: obj} (t: obj x) (p: wff x): wff =
    \\  ($[$:41) x ($/$:0) t ($]$:0) p;
    \\--| @relation wff iff iff_refl iff_trans iff_sym iff_mp
    \\axiom iff_refl (a: wff): $ a ↔ a $;
    \\axiom iff_trans (a b c: wff): $ a ↔ b $ > $ b ↔ c $ > $ a ↔ c $;
    \\axiom iff_sym (a b: wff): $ a ↔ b $ > $ b ↔ a $;
    \\axiom iff_mp (a b: wff): $ a ↔ b $ > $ a $ > $ b $;
    \\--| @relation obj eq eq_refl eq_trans eq_sym _
    \\axiom eq_refl (a: obj): $ a = a $;
    \\axiom eq_trans (a b c: obj): $ a = b $ > $ b = c $ > $ a = c $;
    \\axiom eq_sym (a b: obj): $ a = b $ > $ b = a $;
    \\--| @congr
    \\axiom pair_congr (a b c d: obj):
    \\  $ a = b $ > $ c = d $ > $ pair a c = pair b d $;
    \\--| @congr
    \\axiom eq_congr (a b c d: obj):
    \\  $ a = b $ > $ c = d $ > $ (a = c) ↔ (b = d) $;
    \\--| @rewrite
    \\axiom sb_t_var {x: obj} (t: obj x): $ subst x / t x = t $;
    \\--| @rewrite
    \\axiom sb_t_pair {x: obj} (t: obj x) (a b: obj x):
    \\  $ subst x / t (pair a b) = pair (subst x / t a) (subst x / t b) $;
    \\--| @rewrite
    \\axiom sb_t_irrel {x: obj} (t: obj x) (a: obj): $ subst x / t a = a $;
    \\--| @rewrite
    \\axiom sb_f_eq {x: obj} (t: obj x) (a b: obj x):
    \\  $ [x/t] (a = b) ↔ (subst x / t a = subst x / t b) $;
    \\--| @view {x: obj} (t: obj x) (p: wff x) (q: wff): $ ∀ x p $ > $ q $
    \\--| @recover t q p x
    \\--| @auto forward
    \\axiom all_elim {x: obj} (t: obj x) (p: wff x):
    \\  $ ∀ x p $ > $ [x/t] p $;
    \\theorem fwd_match {x u: obj} (f: obj):
    \\  $ ∀ x (pair f x = pair x f) $ > $ pair f u = pair u f $;
    \\theorem fwd_mismatch {x u v: obj} (f: obj):
    \\  $ ∀ x (pair f x = pair x f) $ > $ pair f u = pair v f $;
;

test "derived ref with universal meta matches a later concrete goal" {
    const proof_src =
        \\fwd_match
        \\---------
        \\l1: $ pair f u = pair u f $ by auto?
    ;
    const offset = std.mem.indexOf(u8, proof_src, "auto?") orelse
        return error.MissingNeedle;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    var suggestions = try source.suggestionsAtSourceOffset(
        arena.allocator(),
        fwd_universal_mm0,
        proof_src,
        offset,
        .{ .counters = &counters, .generate = .{ .enabled = true } },
    );
    defer suggestions.deinit();

    // The goal-direct derived use renders explicit bindings for the solved
    // universal meta (`t := u`) and the premise-match binders. The plain
    // backward `all_elim [#1]` is also offered (supported boundary).
    var found_derived = false;
    var found_direct = false;
    for (suggestions.items) |item| {
        if (std.mem.eql(
            u8,
            item.replacement,
            "all_elim (x := $ x $, t := $ u $, " ++
                "p := $ pair f x = pair x f $) [#1]",
        )) found_derived = true;
        if (std.mem.eql(u8, item.replacement, "all_elim [#1]")) {
            found_direct = true;
        }
    }
    try std.testing.expect(found_direct);
    try std.testing.expect(found_derived);
    try std.testing.expectEqual(@as(usize, 1), counters.derived_ref_count);
    try std.testing.expectEqual(@as(usize, 1), counters.universal_metas_created);
    // The repeated meta occurrence (`pair f ?t` / `pair ?t f`) was assigned
    // once and checked consistent at the second position.
    try std.testing.expect(counters.meta_assignments > 0);
    try std.testing.expect(counters.meta_rollbacks > 0);
}

test "inconsistent repeated universal meta occurrence rejects the use" {
    const proof_src =
        \\fwd_mismatch
        \\------------
        \\l1: $ pair f u = pair v f $ by auto?
    ;
    const offset = std.mem.indexOf(u8, proof_src, "auto?") orelse
        return error.MissingNeedle;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    var suggestions = try source.suggestionsAtSourceOffset(
        arena.allocator(),
        fwd_universal_mm0,
        proof_src,
        offset,
        .{ .counters = &counters, .generate = .{ .enabled = true } },
    );
    defer suggestions.deinit();
    // The derived shape demands the same witness at both positions; the goal
    // shows u and v, so no derived use (and no other proof) exists. The
    // forward layer still ran and derived the ref — bounded clean no-result.
    try std.testing.expectEqual(@as(usize, 0), suggestions.items.len);
    try std.testing.expectEqual(@as(usize, 1), counters.derived_ref_count);
}

test "auto solves the nested forward-instantiation flagship (Stage 7)" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    const mm0_src = try std.fs.cwd().readFileAlloc(
        allocator,
        "tests/search_bench_cases/all_elim_forward.mm0",
        std.math.maxInt(usize),
    );
    const proof_src =
        \\all_elim_forward_inst
        \\---------------------
        \\l1: $ (pair f u = pair f v) → (u = v) $ by auto?
    ;
    const offset = std.mem.indexOf(u8, proof_src, "auto?") orelse
        return error.MissingNeedle;
    var counters = types.SearchCounters{};
    var suggestions = try source.suggestionsAtSourceOffset(
        allocator,
        mm0_src,
        proof_src,
        offset,
        .{ .counters = &counters, .generate = .{ .enabled = true } },
    );
    defer suggestions.deinit();

    // The forward layer unfolds `mono f` (transparent binder def), defers the
    // witness as a universal meta, and the derived ref fills the backward
    // `all_elim` premise slot; the `@recover` correspondence solves `?t := u`
    // from the goal. The hidden unfold dummies are named from the theorem's
    // unused bound vars (a, b).
    var found = false;
    for (suggestions.items) |item| {
        if (std.mem.eql(
            u8,
            item.replacement,
            "all_elim [all_elim (x := $ a $, t := $ u $, " ++
                "p := $ ∀ b (pair f a = pair f b → a = b) $) [#1]]",
        )) found = true;
    }
    try std.testing.expect(found);
    try std.testing.expect(counters.derived_ref_count > 0);
    try std.testing.expect(counters.universal_metas_created > 0);
    try std.testing.expect(counters.forward_rule_attempts > 0);
}

// Full flagship theory (bench copy) plus a conjunction, so one assembly
// must select the SAME derived ref twice at two different witnesses.
const fwd_twice_mm0 =
    \\delimiter $ ( ) [ / ] $;
    \\provable sort wff;
    \\sort obj;
    \\term imp (a b: wff): wff;
    \\infixr imp: $→$ prec 25;
    \\term iff (a b: wff): wff;
    \\infixr iff: $↔$ prec 20;
    \\term and (a b: wff): wff;
    \\infixl and: $∧$ prec 21;
    \\term all {x: obj} (p: wff x): wff;
    \\prefix all: $∀$ prec 41;
    \\term eq (a b: obj): wff;
    \\infixl eq: $=$ prec 35;
    \\term pair (a b: obj): obj;
    \\term sb_t {x: obj} (t: obj x) (a: obj x): obj;
    \\notation sb_t {x: obj} (t: obj x) (a: obj x): obj =
    \\  ($subst$:41) x ($/$:0) t a;
    \\term sb_f {x: obj} (t: obj x) (p: wff x): wff;
    \\notation sb_f {x: obj} (t: obj x) (p: wff x): wff =
    \\  ($[$:41) x ($/$:0) t ($]$:0) p;
    \\--| @relation wff iff iff_refl iff_trans iff_sym iff_mp
    \\axiom iff_refl (a: wff): $ a ↔ a $;
    \\axiom iff_trans (a b c: wff): $ a ↔ b $ > $ b ↔ c $ > $ a ↔ c $;
    \\axiom iff_sym (a b: wff): $ a ↔ b $ > $ b ↔ a $;
    \\axiom iff_mp (a b: wff): $ a ↔ b $ > $ a $ > $ b $;
    \\--| @relation obj eq eq_refl eq_trans eq_sym _
    \\axiom eq_refl (a: obj): $ a = a $;
    \\axiom eq_trans (a b c: obj): $ a = b $ > $ b = c $ > $ a = c $;
    \\axiom eq_sym (a b: obj): $ a = b $ > $ b = a $;
    \\axiom and_intro (p q: wff): $ p $ > $ q $ > $ p ∧ q $;
    \\--| @congr
    \\axiom pair_congr (a b c d: obj):
    \\  $ a = b $ > $ c = d $ > $ pair a c = pair b d $;
    \\--| @congr
    \\axiom eq_congr (a b c d: obj):
    \\  $ a = b $ > $ c = d $ > $ (a = c) ↔ (b = d) $;
    \\--| @congr
    \\axiom imp_congr (a b c d: wff):
    \\  $ a ↔ b $ > $ c ↔ d $ > $ (a → c) ↔ (b → d) $;
    \\--| @congr
    \\axiom all_congr {x: obj} (p q: wff x):
    \\  $ p ↔ q $ > $ ∀ x p ↔ ∀ x q $;
    \\--| @rewrite
    \\axiom sb_t_var {x: obj} (t: obj x): $ subst x / t x = t $;
    \\--| @rewrite
    \\axiom sb_t_pair {x: obj} (t: obj x) (a b: obj x):
    \\  $ subst x / t (pair a b) = pair (subst x / t a) (subst x / t b) $;
    \\--| @rewrite
    \\axiom sb_t_other {x y: obj} (t: obj x): $ subst x / t y = y $;
    \\--| @rewrite
    \\axiom sb_t_irrel {x: obj} (t: obj x) (a: obj): $ subst x / t a = a $;
    \\--| @rewrite
    \\axiom sb_f_eq {x: obj} (t: obj x) (a b: obj x):
    \\  $ [x/t] (a = b) ↔ (subst x / t a = subst x / t b) $;
    \\--| @rewrite
    \\axiom sb_f_imp {x: obj} (t: obj x) (p q: wff x):
    \\  $ [x/t] (p → q) ↔ ([x/t] p → [x/t] q) $;
    \\--| @rewrite
    \\axiom sb_f_all {x y: obj} (t: obj x) (p: wff x y):
    \\  $ [x/t] (∀ y p) ↔ ∀ y ([x/t] p) $;
    \\--| @view {x: obj} (t: obj x) (p: wff x) (q: wff): $ ∀ x p $ > $ q $
    \\--| @recover t q p x
    \\--| @auto forward
    \\axiom all_elim {x: obj} (t: obj x) (p: wff x):
    \\  $ ∀ x p $ > $ [x/t] p $;
    \\def mono {.a .b: obj} (f: obj): wff =
    \\  $ ∀ a ∀ b ((pair f a = pair f b) → (a = b)) $;
    \\theorem fwd_twice {u v a b : obj} (f: obj):
    \\  $ mono f $ >
    \\  $ ((pair f u = pair f v) → (u = v)) ∧ ((pair f a = pair f b) → (a = b)) $;
    \\theorem fwd_nested {u v a b: obj} (f: obj):
    \\  $ ∀ a ∀ b ((pair f a = pair f b) → (a = b)) $ >
    \\  $ (pair f u = pair f v) → (u = v) $;
;

test "same derived ref is selected twice at two different witnesses" {
    const proof_src =
        \\fwd_twice
        \\---------
        \\l1: $ ((pair f u = pair f v) → (u = v)) ∧ ((pair f a = pair f b) → (a = b)) $ by auto?
    ;
    const offset = std.mem.indexOf(u8, proof_src, "auto?") orelse
        return error.MissingNeedle;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    var suggestions = try source.suggestionsAtSourceOffset(
        arena.allocator(),
        fwd_twice_mm0,
        proof_src,
        offset,
        .{ .counters = &counters, .generate = .{ .enabled = true } },
    );
    defer suggestions.deinit();

    // The single-layer derived ref (all_elim fired once on `mono f`) is used
    // twice in the same assembly with independent transient instantiations:
    // `?t := u` in the left conjunct and `?t := a` in the right.
    var found = false;
    for (suggestions.items) |item| {
        const r = item.replacement;
        if (std.mem.startsWith(u8, r, "and_intro [") and
            std.mem.indexOf(u8, r, "t := $ u $") != null and
            std.mem.indexOf(u8, r, "t := $ a $") != null)
        {
            found = true;
        }
    }
    try std.testing.expect(found);
    // Multi-layer saturation also fires `all_elim` on the layer-1
    // shape `∀ b (…?t…)`, deriving the fully instantiated two-hole surface
    // as a second fact.
    try std.testing.expectEqual(@as(usize, 2), counters.derived_ref_count);
}

// ============================================================
// Multi-premise and multi-layer forward saturation
// (META.md). Layered semi-naive firing over pool + derived
// sources, configurable bounds, recipe/shape dedupe, nested
// recipe materialization.
// ============================================================

// Two-step chain: layer 1 fires `pq` on `P K` (deriving `Q K`), layer 2
// fires `qr` on the derived `Q K` (deriving `R K` whose recipe nests the
// layer-1 recipe). The backward `rs` premise `R x` is open (x not in the
// conclusion `S`), so only the two-layer derived ref can fill it.
const fwd_chain_mm0 =
    \\delimiter $ ( ) $;
    \\provable sort wff;
    \\sort obj;
    \\term P (x: obj): wff;
    \\term Q (x: obj): wff;
    \\term R (x: obj): wff;
    \\term S: wff;
    \\term K: obj;
    \\--| @auto forward
    \\axiom pq (x: obj): $ P x $ > $ Q x $;
    \\--| @auto forward
    \\axiom qr (x: obj): $ Q x $ > $ R x $;
    \\axiom rs (x: obj): $ R x $ > $ S $;
    \\theorem t: $ P K $ > $ S $;
;

test "two-step forward chain renders a nested recipe" {
    const proof_src =
        \\t
        \\----
        \\l1: $ S $ by auto?
    ;
    const offset = std.mem.indexOf(u8, proof_src, "auto?") orelse
        return error.MissingNeedle;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    var suggestions = try source.suggestionsAtSourceOffset(
        arena.allocator(),
        fwd_chain_mm0,
        proof_src,
        offset,
        .{ .counters = &counters, .generate = .{ .enabled = true } },
    );
    defer suggestions.deinit();

    var found = false;
    for (suggestions.items) |item| {
        if (std.mem.eql(
            u8,
            item.replacement,
            "rs [qr (x := $ K $) [pq (x := $ K $) [#1]]]",
        )) found = true;
    }
    try std.testing.expect(found);
    // Layer 1: `Q K`; layer 2: `R K`; layer 3 derives nothing (fixpoint —
    // a clean stop, not budget exhaustion).
    try std.testing.expectEqual(@as(usize, 2), counters.derived_ref_count);
    try std.testing.expect(counters.forward_layers_run >= 2);
    try std.testing.expect(!counters.forward_saturation_exhausted);
}

test "multi-premise forward rule fires on a source tuple" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\sort obj;
        \\term P (x: obj): wff;
        \\term Q (x: obj): wff;
        \\term R (x: obj): wff;
        \\term S: wff;
        \\term K: obj;
        \\--| @auto forward
        \\axiom pqr (x: obj): $ P x $ > $ Q x $ > $ R x $;
        \\axiom rs (x: obj): $ R x $ > $ S $;
        \\theorem t: $ P K $ > $ Q K $ > $ S $;
    ;
    const proof_src =
        \\t
        \\----
        \\l1: $ S $ by auto?
    ;
    const offset = std.mem.indexOf(u8, proof_src, "auto?") orelse
        return error.MissingNeedle;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    var suggestions = try source.suggestionsAtSourceOffset(
        arena.allocator(),
        mm0_src,
        proof_src,
        offset,
        .{ .counters = &counters, .generate = .{ .enabled = true } },
    );
    defer suggestions.deinit();

    var found = false;
    for (suggestions.items) |item| {
        if (std.mem.eql(
            u8,
            item.replacement,
            "rs [pqr (x := $ K $) [#1, #2]]",
        )) found = true;
    }
    try std.testing.expect(found);
    // One tuple (#1, #2) matches both premises consistently (x := K at both
    // positions); the cross pairings reject on the shared binder.
    try std.testing.expectEqual(@as(usize, 1), counters.derived_ref_count);
}

test "duplicate derivations collapse to one derived ref" {
    // Two pool refs state the same fact `P K`; the recipe key is the source
    // EXPRESSION, so `pq` fires once, not twice.
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\sort obj;
        \\term P (x: obj): wff;
        \\term Q (x: obj): wff;
        \\term R: wff;
        \\term K: obj;
        \\--| @auto forward
        \\axiom pq (x: obj): $ P x $ > $ Q x $;
        \\axiom qr (x: obj): $ Q x $ > $ R $;
        \\theorem t: $ P K $ > $ P K $ > $ R $;
    ;
    const proof_src =
        \\t
        \\----
        \\l1: $ R $ by auto?
    ;
    const offset = std.mem.indexOf(u8, proof_src, "auto?") orelse
        return error.MissingNeedle;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    var suggestions = try source.suggestionsAtSourceOffset(
        arena.allocator(),
        mm0_src,
        proof_src,
        offset,
        .{ .counters = &counters, .generate = .{ .enabled = true } },
    );
    defer suggestions.deinit();

    var found = false;
    for (suggestions.items) |item| {
        if (std.mem.eql(
            u8,
            item.replacement,
            "qr [pq (x := $ K $) [#1]]",
        )) found = true;
    }
    try std.testing.expect(found);
    try std.testing.expectEqual(@as(usize, 1), counters.derived_ref_count);
}

// Self-feeding loop theory: `step` derives `P (f K)`, then `P (f (f K))`,
// ... — one new fact per layer, forever. Only the bounds stop it.
const fwd_loop_mm0 =
    \\delimiter $ ( ) $;
    \\provable sort wff;
    \\sort obj;
    \\term P (x: obj): wff;
    \\term f (x: obj): obj;
    \\term K: obj;
    \\term R: wff;
    \\--| @auto forward
    \\axiom step (x: obj): $ P x $ > $ P (f x) $;
    \\theorem t: $ P K $ > $ R $;
;

test "layer bound stops a self-feeding forward loop" {
    const proof_src =
        \\t
        \\----
        \\l1: $ R $ by auto?
    ;
    const offset = std.mem.indexOf(u8, proof_src, "auto?") orelse
        return error.MissingNeedle;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    var suggestions = try source.suggestionsAtSourceOffset(
        arena.allocator(),
        fwd_loop_mm0,
        proof_src,
        offset,
        .{ .counters = &counters, .generate = .{ .enabled = true } },
    );
    defer suggestions.deinit();

    // No proof exists; saturation stops at the layer cap with the frontier
    // still productive, and reports that as exhaustion — distinct from the
    // chain test's clean fixpoint.
    try std.testing.expectEqual(@as(usize, 0), suggestions.items.len);
    const default_layers = (types.ForwardOptions{}).max_forward_layers;
    try std.testing.expectEqual(default_layers, counters.derived_ref_count);
    try std.testing.expectEqual(default_layers, counters.forward_layers_run);
    try std.testing.expect(counters.forward_saturation_exhausted);
}

test "fact bound stops a forward explosion" {
    const proof_src =
        \\t
        \\----
        \\l1: $ R $ by auto?
    ;
    const offset = std.mem.indexOf(u8, proof_src, "auto?") orelse
        return error.MissingNeedle;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    var suggestions = try source.suggestionsAtSourceOffset(
        arena.allocator(),
        fwd_loop_mm0,
        proof_src,
        offset,
        .{
            .counters = &counters,
            .generate = .{
                .enabled = true,
                .forward = .{ .max_forward_facts = 1 },
            },
        },
    );
    defer suggestions.deinit();

    try std.testing.expectEqual(@as(usize, 0), suggestions.items.len);
    try std.testing.expectEqual(@as(usize, 1), counters.derived_ref_count);
    try std.testing.expect(counters.forward_saturation_exhausted);
}

test "two-layer derived ref solves a shared hole in both recipe layers" {
    // The nested universal sits directly in the hypothesis (no def unfold).
    // Layer 1 derives `∀ b ((pair f ?t = pair f b) → (?t = b))`; layer 2
    // fires on that shape, deriving `(pair f ?t = pair f ?t2) → (?t = ?t2)`
    // with the layer-1 hole ?t shared. The goal-direct use solves ?t := u,
    // ?t2 := v in ONE walk, and the rendered two-layer recipe shows the
    // shared witness consistently: inner `t := u`, outer `p` mentioning `u`.
    const proof_src =
        \\fwd_nested
        \\----------
        \\l1: $ (pair f u = pair f v) → (u = v) $ by auto?
    ;
    const offset = std.mem.indexOf(u8, proof_src, "auto?") orelse
        return error.MissingNeedle;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    var suggestions = try source.suggestionsAtSourceOffset(
        arena.allocator(),
        fwd_twice_mm0,
        proof_src,
        offset,
        .{ .counters = &counters, .generate = .{ .enabled = true } },
    );
    defer suggestions.deinit();

    var found = false;
    for (suggestions.items) |item| {
        if (std.mem.eql(
            u8,
            item.replacement,
            "all_elim (x := $ b $, t := $ v $, " ++
                "p := $ pair f u = pair f b → u = b $) " ++
                "[all_elim (x := $ a $, t := $ u $, " ++
                "p := $ ∀ b (pair f a = pair f b → a = b) $) " ++
                "[#1]]",
        )) found = true;
    }
    try std.testing.expect(found);
    try std.testing.expectEqual(@as(usize, 2), counters.derived_ref_count);
    try std.testing.expectEqual(@as(usize, 2), counters.universal_metas_created);
}

// ---------------------------------------------------------------------------
// `@auto trigger` seeding (phase 6). The fixture is the guarded bench theory
// (tests/search_bench_cases/nd_minimal.*): the pure repro of the
// elimination-major left-rule gap, closed by ground `ax` seeds harvested
// from the goal's subterms.
// ---------------------------------------------------------------------------

fn readBenchCase(
    allocator: std.mem.Allocator,
    stem: []const u8,
    ext: []const u8,
) ![]u8 {
    const path = try std.fmt.allocPrint(
        allocator,
        "tests/search_bench_cases/{s}.{s}",
        .{ stem, ext },
    );
    defer allocator.free(path);
    return try std.fs.cwd().readFileAlloc(
        allocator,
        path,
        std.math.maxInt(usize),
    );
}

test "auto trigger seeds close an elimination major from an empty pool" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    const mm0_src = try readBenchCase(allocator, "nd_minimal", "mm0");

    // The pure left-rule repro: `p → q , p ⊢ q` from an EMPTY ref pool.
    // Without seeding this is a clean miss at any budget (imp_elim's `p` is
    // premise-only, so backward search has no ref to pin it); the `(hyp p)`
    // trigger seeds `p → q ⊢ p → q` and `p ⊢ p`, which pin it.
    const proof_src =
        "nd_mp_inner\n" ++
        "-----------\n" ++
        "l1: $ p → q , p ⊢ q $ by auto?\n";
    const offset = std.mem.indexOf(u8, proof_src, "auto?") orelse
        return error.MissingNeedle;
    var counters = types.SearchCounters{};
    var suggestions = try source.suggestionsAtSourceOffset(
        allocator,
        mm0_src,
        proof_src,
        offset,
        .{ .counters = &counters, .generate = .{ .enabled = true } },
    );
    defer suggestions.deinit();

    try std.testing.expect(suggestions.items.len > 0);
    try std.testing.expect(counters.trigger_seed_count > 0);
    var found_imp_elim = false;
    for (suggestions.items) |item| {
        if (std.mem.indexOf(u8, item.replacement, "imp_elim") != null) {
            found_imp_elim = true;
        }
    }
    try std.testing.expect(found_imp_elim);
}

test "theories without trigger annotations mint no seeds on a miss" {
    // A clean full-ladder miss in a trigger-free theory: the phase-6 gate
    // (`triggerRuleCount() > 0`) must skip the harvest entirely.
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term P: wff;
        \\term Q: wff;
        \\term R: wff;
        \\axiom p: $ P $;
        \\axiom pq: $ P $ > $ Q $;
        \\theorem t: $ R $;
    ;
    const proof_src =
        \\t
        \\----
        \\l1: $ R $ by auto?
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const offset = std.mem.indexOf(u8, proof_src, "auto?") orelse
        return error.MissingNeedle;
    var counters = types.SearchCounters{};
    var suggestions = try source.suggestionsAtSourceOffset(
        arena.allocator(),
        mm0_src,
        proof_src,
        offset,
        .{ .counters = &counters, .generate = .{ .enabled = true } },
    );
    defer suggestions.deinit();

    try std.testing.expectEqual(@as(usize, 0), suggestions.items.len);
    try std.testing.expectEqual(@as(usize, 0), counters.trigger_seed_count);
}

test "verdict memo counts distinct rejects once" {
    var memo = types.VerdictMemo{ .allocator = std.testing.allocator };
    defer memo.deinit();

    memo.recordReject(11);
    memo.recordReject(22);
    memo.recordReject(11);
    try std.testing.expect(memo.rejectedBefore(11));
    try std.testing.expect(memo.rejectedBefore(22));
    try std.testing.expect(!memo.rejectedBefore(33));
    try std.testing.expectEqual(@as(usize, 3), memo.reject_total);
    try std.testing.expectEqual(@as(usize, 2), memo.reject_distinct);
    try std.testing.expectEqual(memo.seen.count(), memo.reject_distinct);
}

fn contentHashOf(theorem: *const TheoremContext, id: ExprId) u64 {
    var h = std.hash.Wyhash.init(0);
    types.hashCanonicalContent(theorem, id, &h);
    return h.final();
}

test "canonical content hash is stable across an interner-scope discard" {
    // The invariant that lets the concrete/verdict/deep memos skip scope-exit
    // eviction entirely: keys hash canonical CONTENT, so a `hookSolveOpen`
    // scope discard — which re-mints the same raw ExprIds with different
    // content — can never alias a surviving entry.
    var base = TheoremContext.init(std.testing.allocator);
    defer base.deinit();
    const d0 = try base.addDummyVarResolved("wff", 0);

    // Scope 1: a COW clone interns `f(d0)` (term_id 7).
    var scope1 = try base.clone();
    const a1 = try scope1.interner.internApp(7, &.{d0});
    const hash_f = contentHashOf(&scope1, a1);
    scope1.deinit();

    // Scope 2: same base, so the discarded id is re-minted — this time for
    // `g(d0)` (term_id 8). Same raw ExprId, different content: the raw id is
    // ABA-ambiguous, the content hash is not.
    var scope2 = try base.clone();
    defer scope2.deinit();
    const b2 = try scope2.interner.internApp(8, &.{d0});
    try std.testing.expectEqual(a1, b2);
    try std.testing.expect(contentHashOf(&scope2, b2) != hash_f);

    // Re-interning the SAME content in the new scope reproduces the hash.
    const a2 = try scope2.interner.internApp(7, &.{d0});
    try std.testing.expectEqual(hash_f, contentHashOf(&scope2, a2));
}

test "canonical content hash keys dummies by index and sort" {
    // Dummy leaves hash (index, sort), the pair that fully determines a
    // dummy's semantics — so a same-index same-sort re-mint after a scope
    // discard deliberately collides (it is interchangeable), while a
    // different-sort re-mint at the same index does not.
    var base = TheoremContext.init(std.testing.allocator);
    defer base.deinit();

    var scope1 = try base.clone();
    const d_wff = try scope1.addDummyVarResolved("wff", 0);
    const app1 = try scope1.interner.internApp(7, &.{d_wff});
    const hash_wff = contentHashOf(&scope1, app1);
    scope1.deinit();

    var scope2 = try base.clone();
    defer scope2.deinit();
    const d_nat = try scope2.addDummyVarResolved("nat", 1);
    const app2 = try scope2.interner.internApp(7, &.{d_nat});
    try std.testing.expectEqual(app1, app2);
    try std.testing.expect(contentHashOf(&scope2, app2) != hash_wff);

    var scope3 = try base.clone();
    defer scope3.deinit();
    const d_wff_again = try scope3.addDummyVarResolved("wff", 0);
    const app3 = try scope3.interner.internApp(7, &.{d_wff_again});
    try std.testing.expectEqual(hash_wff, contentHashOf(&scope3, app3));
}

test "complement shapes derive from ax's repeated-binder template pair" {
    // tait's `ax (d: ctx) (a: wff): ⊢ a , (¬ a) , d` repeats binder `a`
    // (arg index 1) across two region members — coercion-wrapped as
    // `hyp(a)` / `hyp(¬ a)`, so neither member is a bare binder. It must be
    // the fixture's ONLY complement shape: the ctx_eq axioms repeat `g`
    // only as identical bare members (excluded), and every other repeated
    // binder sits outside an ACUI carrier region.
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    const mm0 = try std.fs.cwd().readFileAlloc(
        allocator,
        "tests/search_bench_cases/tait.mm0",
        std.math.maxInt(usize),
    );
    var fixture = try fixtureFor(allocator, mm0, "ex_all_to_all_ex");
    var harness = ContextHarness.init(allocator);
    defer harness.deinit();
    const context = harness.context(&fixture);

    var shapes: [Witness.max_complement_shapes]Witness.ComplementShape = undefined;
    const count = Witness.collectComplementShapes(&context, &shapes);
    try std.testing.expectEqual(@as(usize, 1), count);
    try std.testing.expectEqual(@as(usize, 1), shapes[0].hole);
    // Both members are compound (coercion-wrapped), not bare binders.
    try std.testing.expect(shapes[0].first.* == .app);
    try std.testing.expect(shapes[0].second.* == .app);
}

test "auto co-solves a complementary two-meta ax leaf through the rule template" {
    // Regenerating `⊢ (∃ x ¬ R x y) , (∃ w R z w)` from the bare goal takes
    // two nested `rex` slots whose witnesses only the `ax` leaf forces: the
    // leaf goal members `¬ R ?x y` / `R z ?w` BOTH carry metas (no rigid
    // anchor), so closure requires co-solving `?x := z`, `?w := y` through
    // ax's repeated-binder template pair — the complementary coupled pass.
    // Without it this is a clean miss (the tait ex_all_to_all_ex gap).
    const proof_src =
        \\ex_all_to_all_ex
        \\----------------
        \\l1: $ ⊢ (∃ x (¬ R x y)) , (∃ w R z w) $ by auto?
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    const mm0 = try std.fs.cwd().readFileAlloc(
        allocator,
        "tests/search_bench_cases/tait.mm0",
        std.math.maxInt(usize),
    );
    const offset = std.mem.indexOf(u8, proof_src, "auto?").?;
    var suggestions = try source.suggestionsAtSourceOffset(
        allocator,
        mm0,
        proof_src,
        offset,
        .{ .generate = .{ .enabled = true } },
    );
    defer suggestions.deinit();

    try std.testing.expect(suggestions.items.len > 0);
    // The regenerated chain goes through rex and closes at the ax leaf.
    var found = false;
    for (suggestions.items) |item| {
        if (std.mem.indexOf(u8, item.replacement, "rex") != null and
            std.mem.indexOf(u8, item.replacement, "ax") != null)
        {
            found = true;
        }
    }
    try std.testing.expect(found);
}

test "member witness match rejects values captured under a member binder" {
    // A meta-bearing fragment may ground its witness off any *free* subterm
    // of a domain member, but not off a subterm under the member's own
    // intact binder: that value escapes its scope (the materialized target
    // would mention the variable free while the sibling member still binds
    // it), so the fill can never validate — before the capture check each
    // one launched a full doomed child search (the forall_mono node flood).
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\sort ctx;
        \\sort obj;
        \\term not (a: wff): wff;
        \\term ex {x: obj} (p: wff x): wff;
        \\term Q (a: obj): wff;
        \\term hyp (a: wff): ctx;
        \\term T: wff;
        \\theorem t: $ T $;
    ;
    var fixture = try fixtureFor(allocator, mm0_src, "t");
    var theorem = TheoremContext.init(allocator);
    defer theorem.deinit();
    try theorem.seedAssertion(fixture.assertion);
    var harness = ContextHarness.init(allocator);
    defer harness.deinit();
    const context = harness.context(&fixture);

    const not_id = fixture.env.term_names.get("not").?;
    const ex_id = fixture.env.term_names.get("ex").?;
    const q_id = fixture.env.term_names.get("Q").?;
    const hyp_id = fixture.env.term_names.get("hyp").?;

    var store = MetaStore.init(allocator, &fixture.env);
    defer store.deinit();
    const meta = try store.mint(&theorem, "obj", std.math.maxInt(u55), .existential);
    const fragment = try theorem.interner.internApp(q_id, &.{meta});

    // Captured anchor: hyp(∃ x ¬(Q x)) — the only Q-node sits under the
    // member's own binder, so ?w := x must be refused outright (the old
    // descent read it off and returned true).
    const x = try theorem.interner.internVar(.{ .theorem_var = 0 });
    const captured = try theorem.interner.internApp(hyp_id, &.{
        try theorem.interner.internApp(ex_id, &.{
            x,
            try theorem.interner.internApp(not_id, &.{
                try theorem.interner.internApp(q_id, &.{x}),
            }),
        }),
    });
    const mark = store.mark();
    try std.testing.expect(!Witness.matchFragmentToMember(
        &context,
        &store,
        &theorem,
        fragment,
        captured,
    ));
    store.rollbackTo(mark);

    // Free anchor: hyp(Q z) with z free in the member still forces ?w := z
    // (the ordinary member-force, e.g. off a rall eigenvariable).
    const z = try theorem.interner.internVar(.{ .theorem_var = 1 });
    const free_anchor = try theorem.interner.internApp(hyp_id, &.{
        try theorem.interner.internApp(q_id, &.{z}),
    });
    try std.testing.expect(Witness.matchFragmentToMember(
        &context,
        &store,
        &theorem,
        fragment,
        free_anchor,
    ));
    try std.testing.expectEqual(z, try store.materialize(&theorem, meta));
    store.rollbackTo(mark);
}

// ---------------------------------------------------------------------------
// Per-call tunables + failure detail (search/tunables.zig, buildStatusDetail)

const tunables = @import("./tunables.zig");

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

// End-to-end fixture: `R` needs a two-level generated chain
// (`qr [pq [p []]]`), `S` is unprovable.
const tunable_chain_mm0 =
    \\delimiter $ ( ) $;
    \\provable sort wff;
    \\term P: wff;
    \\term Q: wff;
    \\term R: wff;
    \\term S: wff;
    \\axiom p: $ P $;
    \\axiom pq: $ P $ > $ Q $;
    \\axiom qr: $ Q $ > $ R $;
    \\theorem t: $ R $;
    \\theorem ts: $ S $;
;

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

const conversion_prelude =
    \\delimiter $ ( ) $;
    \\provable sort wff;
    \\term iff (p q: wff): wff;
    \\term an (p q: wff): wff;
    \\term or (p q: wff): wff;
    \\--| @relation wff iff iff_refl iff_trans iff_symm mpbi
    \\axiom iff_refl (a: wff): $ iff a a $;
    \\axiom iff_trans (a b c: wff) (h1: $ iff a b $) (h2: $ iff b c $): $ iff a c $;
    \\axiom iff_symm (a b: wff) (h: $ iff a b $): $ iff b a $;
    \\axiom mpbi (a b: wff) (h1: $ iff a b $) (h2: $ a $): $ b $;
    \\--| @congr
    \\axiom an_congr (a b c d: wff) (h1: $ iff a b $) (h2: $ iff c d $): $ iff (an a c) (an b d) $;
    \\--| @congr
    \\axiom or_congr (a b c d: wff) (h1: $ iff a b $) (h2: $ iff c d $): $ iff (or a c) (or b d) $;
    \\--| @conversion both
    \\axiom an_comm (a b: wff): $ iff (an a b) (an b a) $;
    \\--| @conversion both
    \\axiom or_comm (a b: wff): $ iff (or a b) (or b a) $;
    \\--| @conversion ltr
    \\axiom an_contract (a: wff): $ iff (an a a) a $;
    \\
;

fn conversionSuggestions(
    arena: *std.heap.ArenaAllocator,
    mm0_src: []const u8,
    proof_src: []const u8,
    options: types.SourceSuggestionOptions,
) !types.SourceSuggestions {
    const offset = std.mem.indexOf(u8, proof_src, "conversion?") orelse
        return error.MissingNeedle;
    return source.suggestionsAtSourceOffset(
        arena.allocator(),
        mm0_src,
        proof_src,
        offset,
        options,
    );
}

/// Splice the suggestion into the proof source and run the full compile
/// path over the pair: the emitted chain must actually check.
fn expectConversionCompiles(
    arena: *std.heap.ArenaAllocator,
    mm0_src: []const u8,
    proof_src: []const u8,
    suggestion: types.SourceSuggestion,
) !void {
    const spliced = try std.mem.concat(arena.allocator(), u8, &.{
        proof_src[0..suggestion.replace_span.start],
        suggestion.replacement,
        proof_src[suggestion.replace_span.end..],
    });
    const Compiler = @import("../../compiler.zig").Compiler;
    var compiler = Compiler.initWithProof(
        arena.allocator(),
        mm0_src,
        spliced,
    );
    try compiler.check();
}

test "conversion? proves a nested commutativity goal from a hypothesis" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const mm0_src = conversion_prelude ++
        \\theorem conv_deep (p q r: wff) (h: $ or (an p q) r $): $ or r (an q p) $;
    ;
    const proof_src =
        \\conv_deep
        \\----
        \\goal: $ or r (an q p) $ by conversion?
        \\
    ;

    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    try std.testing.expectEqual(@as(usize, 1), found.items.len);

    // The chain lowers through the enrolled rewrites, a congruence lift, a
    // trans join, and the relation transport citing the hypothesis.
    const replacement = found.items[0].replacement;
    try std.testing.expect(std.mem.indexOf(u8, replacement, "an_comm") != null);
    try std.testing.expect(std.mem.indexOf(u8, replacement, "or_congr") != null);
    try std.testing.expect(std.mem.indexOf(u8, replacement, "iff_trans") != null);
    try std.testing.expect(std.mem.indexOf(u8, replacement, "mpbi") != null);
    try std.testing.expect(std.mem.indexOf(u8, replacement, "#1") != null);

    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "conversion? lowers a reversed ltr rule through symm" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // `an_contract` is enrolled ltr only; proving the expanded form from
    // the contracted hypothesis traverses its union edge backwards.
    const mm0_src = conversion_prelude ++
        \\theorem conv_expand (p: wff) (h: $ p $): $ an p p $;
    ;
    const proof_src =
        \\conv_expand
        \\----
        \\goal: $ an p p $ by conversion?
        \\
    ;

    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    const replacement = found.items[0].replacement;
    try std.testing.expect(
        std.mem.indexOf(u8, replacement, "an_contract") != null,
    );
    try std.testing.expect(std.mem.indexOf(u8, replacement, "iff_symm") != null);

    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "conversion? saturated miss is reported as a forced negative" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const mm0_src = conversion_prelude ++
        \\theorem conv_none (p q: wff) (h: $ an p q $): $ or p q $;
    ;
    const proof_src =
        \\conv_none
        \\----
        \\goal: $ or p q $ by conversion?
        \\
    ;

    var miss = try conversionSuggestions(&arena, mm0_src, proof_src, .{
        .status_detail = true,
    });
    defer miss.deinit();
    try std.testing.expectEqual(types.SearchStatus.miss, miss.status);
    const detail = miss.status_detail orelse return error.MissingStatusDetail;
    try std.testing.expect(
        std.mem.indexOf(u8, detail, "the egraph saturated") != null,
    );
    try std.testing.expect(
        std.mem.indexOf(u8, detail, "no chain of the enrolled") != null,
    );

    // Opt-in: the same miss without the flag carries no detail.
    var plain = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer plain.deinit();
    try std.testing.expectEqual(types.SearchStatus.miss, plain.status);
    try std.testing.expectEqual(@as(?[]const u8, null), plain.status_detail);
}

// The same connectives with comm/assoc as role certificates: the AC laws
// are absorbed into bag interning instead of saturating, and the lowering
// pays them back as explicit certificate chains.
const conversion_ac_prelude =
    \\delimiter $ ( ) $;
    \\provable sort wff;
    \\term iff (p q: wff): wff;
    \\term an (p q: wff): wff;
    \\term or (p q: wff): wff;
    \\--| @relation wff iff iff_refl iff_trans iff_symm mpbi
    \\axiom iff_refl (a: wff): $ iff a a $;
    \\axiom iff_trans (a b c: wff) (h1: $ iff a b $) (h2: $ iff b c $): $ iff a c $;
    \\axiom iff_symm (a b: wff) (h: $ iff a b $): $ iff b a $;
    \\axiom mpbi (a b: wff) (h1: $ iff a b $) (h2: $ a $): $ b $;
    \\--| @congr
    \\axiom an_congr (a b c d: wff) (h1: $ iff a b $) (h2: $ iff c d $): $ iff (an a c) (an b d) $;
    \\--| @congr
    \\axiom or_congr (a b c d: wff) (h1: $ iff a b $) (h2: $ iff c d $): $ iff (or a c) (or b d) $;
    \\--| @conversion comm
    \\axiom an_comm (a b: wff): $ iff (an a b) (an b a) $;
    \\--| @conversion assoc
    \\axiom an_assoc (a b c: wff): $ iff (an (an a b) c) (an a (an b c)) $;
    \\--| @conversion comm
    \\axiom or_comm (a b: wff): $ iff (or a b) (or b a) $;
    \\--| @conversion assoc
    \\axiom or_assoc (a b c: wff): $ iff (or (or a b) c) (or a (or b c)) $;
    \\--| @conversion ltr
    \\axiom an_contract (a: wff): $ iff (an a a) a $;
    \\
;

test "conversion? AC: pure reassociation+permutation lowers via certificates" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const mm0_src = conversion_ac_prelude ++
        \\theorem conv_ac (p q r: wff) (h: $ an (an p q) r $): $ an r (an q p) $;
    ;
    const proof_src =
        \\conv_ac
        \\----
        \\goal: $ an r (an q p) $ by conversion?
        \\
    ;

    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    const replacement = found.items[0].replacement;
    // Zero saturation steps: the whole chain is seam re-treeing citing
    // the certificates.
    try std.testing.expect(std.mem.indexOf(u8, replacement, "an_comm") != null);
    try std.testing.expect(std.mem.indexOf(u8, replacement, "mpbi") != null);
    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "conversion? AC: rule fires on a sub-multiset with extension" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // an_contract's redex {p, p} is a sub-multiset of the 3-member bag
    // {p, p, q}; the leftover member rejoins the contracted target.
    const mm0_src = conversion_ac_prelude ++
        \\theorem conv_ext (p q: wff) (h: $ an p (an q p) $): $ an q p $;
    ;
    const proof_src =
        \\conv_ext
        \\----
        \\goal: $ an q p $ by conversion?
        \\
    ;

    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    const replacement = found.items[0].replacement;
    try std.testing.expect(
        std.mem.indexOf(u8, replacement, "an_contract") != null,
    );
    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "conversion? AC: rewrite inside a bag member lifts through the comb" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const mm0_src = conversion_ac_prelude ++
        \\theorem conv_in (p q r: wff) (h: $ or (an p (an q q)) r $): $ or r (an q p) $;
    ;
    const proof_src =
        \\conv_in
        \\----
        \\goal: $ or r (an q p) $ by conversion?
        \\
    ;

    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    const replacement = found.items[0].replacement;
    try std.testing.expect(
        std.mem.indexOf(u8, replacement, "an_contract") != null,
    );
    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "conversion? AC: local equation over bags cites the written formula" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const mm0_src = conversion_ac_prelude ++
        \\theorem conv_eq (p q s: wff) (h1: $ iff (an p q) s $) (h2: $ an q p $): $ s $;
    ;
    const proof_src =
        \\conv_eq
        \\----
        \\goal: $ s $ by conversion?
        \\
    ;

    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "conversion? AC: seven-atom forced negative saturates at defaults" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // The tree-representation baseline dies at n = 7: the miss degrades
    // to budget_exhausted before the AC closure completes (see
    // docs/design_notes/ac_representation.md). With bags the closure is
    // definitional and the forced negative survives.
    const mm0_src = conversion_ac_prelude ++
        \\theorem conv_neg (p1 p2 p3 p4 p5 p6 p7: wff)
        \\  (h: $ an p1 (an p2 (an p3 (an p4 (an p5 (an p6 p7))))) $):
        \\  $ or p1 (or p2 (or p3 (or p4 (or p5 (or p6 p7))))) $;
    ;
    const proof_src =
        \\conv_neg
        \\----
        \\goal: $ or p1 (or p2 (or p3 (or p4 (or p5 (or p6 p7))))) $ by conversion?
        \\
    ;

    var miss = try conversionSuggestions(&arena, mm0_src, proof_src, .{
        .status_detail = true,
    });
    defer miss.deinit();
    try std.testing.expectEqual(types.SearchStatus.miss, miss.status);
    const detail = miss.status_detail orelse return error.MissingStatusDetail;
    try std.testing.expect(
        std.mem.indexOf(u8, detail, "the egraph saturated") != null,
    );
    // The forced negative must be unhedged: a budget-capped or
    // cyclic-dropped run would append a "NOT a forced negative" caveat,
    // which is exactly the regression this fixture guards against.
    try std.testing.expect(
        std.mem.indexOf(u8, detail, "NOT a forced negative") == null,
    );

    // And the positive twin — a reversed seven-atom conjunction — is
    // found and compiles.
    const found_src = conversion_ac_prelude ++
        \\theorem conv_pos (p1 p2 p3 p4 p5 p6 p7: wff)
        \\  (h: $ an p1 (an p2 (an p3 (an p4 (an p5 (an p6 p7))))) $):
        \\  $ an p7 (an p6 (an p5 (an p4 (an p3 (an p2 p1))))) $;
    ;
    const found_proof =
        \\conv_pos
        \\----
        \\goal: $ an p7 (an p6 (an p5 (an p4 (an p3 (an p2 p1))))) $ by conversion?
        \\
    ;
    var found = try conversionSuggestions(&arena, found_src, found_proof, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    try expectConversionCompiles(&arena, found_src, found_proof, found.items[0]);
}

test "conversion? AC: absorbed certificates alone keep the search alive" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // The ONLY @conversion annotations are the absorbed certificates, so
    // zero rules enroll for saturation and the pool has no rel-shaped
    // equations — yet a pure permutation goal converts by bag interning
    // alone. Regression: the "nothing can ever union" early-out must not
    // fire while absorbed heads exist.
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term iff (p q: wff): wff;
        \\term an (p q: wff): wff;
        \\--| @relation wff iff iff_refl iff_trans iff_symm mpbi
        \\axiom iff_refl (a: wff): $ iff a a $;
        \\axiom iff_trans (a b c: wff) (h1: $ iff a b $) (h2: $ iff b c $): $ iff a c $;
        \\axiom iff_symm (a b: wff) (h: $ iff a b $): $ iff b a $;
        \\axiom mpbi (a b: wff) (h1: $ iff a b $) (h2: $ a $): $ b $;
        \\--| @congr
        \\axiom an_congr (a b c d: wff) (h1: $ iff a b $) (h2: $ iff c d $): $ iff (an a c) (an b d) $;
        \\--| @conversion comm
        \\axiom an_comm (a b: wff): $ iff (an a b) (an b a) $;
        \\--| @conversion assoc
        \\axiom an_assoc (a b c: wff): $ iff (an (an a b) c) (an a (an b c)) $;
        \\theorem conv_pure (p q r: wff) (h: $ an (an p q) r $): $ an r (an q p) $;
    ;
    const proof_src =
        \\conv_pure
        \\----
        \\goal: $ an r (an q p) $ by conversion?
        \\
    ;

    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "conversion? tree path still lowers assoc laws (direction tokens)" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // Direction-token comm/assoc rules (role == none) stay on the tree
    // representation — the supported configuration for theories that
    // never migrate to role certificates. Pin the assoc lowering there.
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term iff (p q: wff): wff;
        \\term an (p q: wff): wff;
        \\--| @relation wff iff iff_refl iff_trans iff_symm mpbi
        \\axiom iff_refl (a: wff): $ iff a a $;
        \\axiom iff_trans (a b c: wff) (h1: $ iff a b $) (h2: $ iff b c $): $ iff a c $;
        \\axiom iff_symm (a b: wff) (h: $ iff a b $): $ iff b a $;
        \\axiom mpbi (a b: wff) (h1: $ iff a b $) (h2: $ a $): $ b $;
        \\--| @congr
        \\axiom an_congr (a b c d: wff) (h1: $ iff a b $) (h2: $ iff c d $): $ iff (an a c) (an b d) $;
        \\--| @conversion both
        \\axiom an_comm (a b: wff): $ iff (an a b) (an b a) $;
        \\--| @conversion both
        \\axiom an_assoc (a b c: wff): $ iff (an (an a b) c) (an a (an b c)) $;
        \\theorem conv_tree (p q r: wff) (h: $ an (an p q) r $): $ an q (an p r) $;
    ;
    const proof_src =
        \\conv_tree
        \\----
        \\goal: $ an q (an p r) $ by conversion?
        \\
    ;

    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    const replacement = found.items[0].replacement;
    try std.testing.expect(
        std.mem.indexOf(u8, replacement, "an_assoc") != null or
            std.mem.indexOf(u8, replacement, "an_comm") != null,
    );
    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "conversion? reports missing enrollment and node-cap truncation" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    // A theory with no @conversion rules at all.
    var unenrolled = try conversionSuggestions(&arena, tunable_chain_mm0,
        \\t
        \\----
        \\l1: $ R $ by conversion?
    , .{ .status_detail = true });
    defer unenrolled.deinit();
    try std.testing.expectEqual(types.SearchStatus.miss, unenrolled.status);
    const no_rules = unenrolled.status_detail orelse
        return error.MissingStatusDetail;
    try std.testing.expect(
        std.mem.indexOf(u8, no_rules, "no @conversion rules are enrolled") != null,
    );

    // A starved e-node cap surfaces as truncation with a concrete hint.
    const mm0_src = conversion_prelude ++
        \\theorem conv_deep (p q r: wff) (h: $ or (an p q) r $): $ or r (an q p) $;
    ;
    var capped = try conversionSuggestions(&arena, mm0_src,
        \\conv_deep
        \\----
        \\goal: $ or r (an q p) $ by conversion? (nodes: 1)
        \\
    , .{ .status_detail = true });
    defer capped.deinit();
    try std.testing.expectEqual(
        types.SearchStatus.budget_exhausted,
        capped.status,
    );
    const detail = capped.status_detail orelse return error.MissingStatusDetail;
    try std.testing.expect(
        std.mem.indexOf(u8, detail, "e-node cap (1)") != null,
    );
    try std.testing.expect(
        std.mem.indexOf(u8, detail, "conversion? (nodes: 2)") != null,
    );
}

// A theory with a relation bundle and congruence but ZERO @conversion
// rules: local equations are the only way anything ever unions.
const equation_only_prelude =
    \\delimiter $ ( ) $;
    \\provable sort wff;
    \\term iff (p q: wff): wff;
    \\term an (p q: wff): wff;
    \\--| @relation wff iff iff_refl iff_trans iff_symm mpbi
    \\axiom iff_refl (a: wff): $ iff a a $;
    \\axiom iff_trans (a b c: wff) (h1: $ iff a b $) (h2: $ iff b c $): $ iff a c $;
    \\axiom iff_symm (a b: wff) (h: $ iff a b $): $ iff b a $;
    \\axiom mpbi (a b: wff) (h1: $ iff a b $) (h2: $ a $): $ b $;
    \\--| @congr
    \\axiom an_congr (a b c d: wff) (h1: $ iff a b $) (h2: $ iff c d $): $ iff (an a c) (an b d) $;
    \\
;

test "conversion? converges through a local equation with no rules enrolled" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // h1 is an ordinary iff hypothesis, not an enrolled rewrite: its sides
    // union at seed time and congruence closure alone connects the goal.
    const mm0_src = equation_only_prelude ++
        \\theorem conv_ground (p q r: wff) (h1: $ iff q p $) (h2: $ an q r $): $ an p r $;
    ;
    const proof_src =
        \\conv_ground
        \\----
        \\goal: $ an p r $ by conversion?
        \\
    ;

    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);

    // The forward equation step is the hypothesis cited as-is — no rule
    // line, just the congruence lift and the transport.
    const replacement = found.items[0].replacement;
    try std.testing.expect(std.mem.indexOf(u8, replacement, "#1") != null);
    try std.testing.expect(std.mem.indexOf(u8, replacement, "an_congr") != null);
    try std.testing.expect(std.mem.indexOf(u8, replacement, "mpbi") != null);
    try std.testing.expect(std.mem.indexOf(u8, replacement, "iff_symm") == null);

    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "conversion? joins a local equation with enrolled rewrites" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // Needs BOTH: the equation q ~ p (no enrolled rule swaps atoms) and
    // an_comm for the argument flip.
    const mm0_src = conversion_prelude ++
        \\theorem conv_mixed (p q r: wff) (h1: $ iff q p $) (h2: $ an q r $): $ an r p $;
    ;
    const proof_src =
        \\conv_mixed
        \\----
        \\goal: $ an r p $ by conversion?
        \\
    ;

    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    const replacement = found.items[0].replacement;
    try std.testing.expect(std.mem.indexOf(u8, replacement, "#1") != null);
    try std.testing.expect(std.mem.indexOf(u8, replacement, "an_comm") != null);
    try std.testing.expect(std.mem.indexOf(u8, replacement, "iff_trans") != null);

    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "conversion? cites a local equation backwards through symm" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // h1 proves iff(p, q); the chain rewrites q -> p, traversing the
    // equation's union edge against its stated direction.
    const mm0_src = equation_only_prelude ++
        \\theorem conv_eq_rev (p q r: wff) (h1: $ iff p q $) (h2: $ an q r $): $ an p r $;
    ;
    const proof_src =
        \\conv_eq_rev
        \\----
        \\goal: $ an p r $ by conversion?
        \\
    ;

    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    const replacement = found.items[0].replacement;
    try std.testing.expect(std.mem.indexOf(u8, replacement, "iff_symm") != null);
    try std.testing.expect(std.mem.indexOf(u8, replacement, "#1") != null);

    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "conversion? tolerates a self-referential local equation" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // h1 unions p with a compound containing p's own class — a cyclic
    // e-class from the first rebuild. The found case must not pay for it
    // and the miss case must still saturate to a forced negative.
    const found_mm0 = conversion_prelude ++
        \\theorem conv_cyc (p q: wff) (h1: $ iff p (an p p) $) (h2: $ an p q $): $ an q p $;
    ;
    const found_proof =
        \\conv_cyc
        \\----
        \\goal: $ an q p $ by conversion?
        \\
    ;
    var found = try conversionSuggestions(&arena, found_mm0, found_proof, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    try expectConversionCompiles(&arena, found_mm0, found_proof, found.items[0]);

    const miss_mm0 = conversion_prelude ++
        \\theorem conv_cyc_miss (p q: wff) (h1: $ iff p (an p p) $) (h2: $ an p q $): $ or p q $;
    ;
    var miss = try conversionSuggestions(&arena, miss_mm0,
        \\conv_cyc_miss
        \\----
        \\goal: $ or p q $ by conversion?
        \\
    , .{ .status_detail = true });
    defer miss.deinit();
    try std.testing.expectEqual(types.SearchStatus.miss, miss.status);
    const detail = miss.status_detail orelse return error.MissingStatusDetail;
    try std.testing.expect(
        std.mem.indexOf(u8, detail, "the egraph saturated") != null,
    );
    try std.testing.expect(
        std.mem.indexOf(u8, detail, "1 local equations") != null,
    );
}

// --- conversion? dep safety: prenex/CNF rules of passage ------------------
//
// A first-order theory whose interesting rewrites carry variable-dependency
// side conditions (the classical rules of passage: quantifier scope moves
// legal only when the moved formula does not mention the bound variable).
// The egraph's dep gate must admit exactly the matches whose side condition
// some class representative can witness, and extraction must cite that
// representative. Without the gate, `al_vac` alone would "prove"
// `Pr x ⊢ al x (Pr x)`.

const fol_passage_prelude =
    \\delimiter $ ( ) $;
    \\sort var;
    \\provable sort form;
    \\term iff (p q: form): form;
    \\term an (p q: form): form;
    \\term or (p q: form): form;
    \\term imp (p q: form): form;
    \\term not (p: form): form;
    \\term al {x: var} (p: form x): form;
    \\term ex {x: var} (p: form x): form;
    \\term Pr (v: var): form;
    \\--| @relation form iff iff_refl iff_trans iff_symm mpbi
    \\axiom iff_refl (a: form): $ iff a a $;
    \\axiom iff_trans (a b c: form) (h1: $ iff a b $) (h2: $ iff b c $): $ iff a c $;
    \\axiom iff_symm (a b: form) (h: $ iff a b $): $ iff b a $;
    \\axiom mpbi (a b: form) (h1: $ iff a b $) (h2: $ a $): $ b $;
    \\--| @congr
    \\axiom an_congr (a b c d: form) (h1: $ iff a b $) (h2: $ iff c d $): $ iff (an a c) (an b d) $;
    \\--| @congr
    \\axiom or_congr (a b c d: form) (h1: $ iff a b $) (h2: $ iff c d $): $ iff (or a c) (or b d) $;
    \\--| @congr
    \\axiom imp_congr (a b c d: form) (h1: $ iff a b $) (h2: $ iff c d $): $ iff (imp a c) (imp b d) $;
    \\--| @congr
    \\axiom not_congr (a b: form) (h: $ iff a b $): $ iff (not a) (not b) $;
    \\--| @congr
    \\axiom al_congr {x: var} (p q: form x) (h: $ iff p q $): $ iff (al x p) (al x q) $;
    \\--| @congr
    \\axiom ex_congr {x: var} (p q: form x) (h: $ iff p q $): $ iff (ex x p) (ex x q) $;
    \\--| @conversion both
    \\axiom pass_al_or {x: var} (a: form) (b: form x): $ iff (al x (or a b)) (or a (al x b)) $;
    \\--| @conversion ltr
    \\axiom al_vac {x: var} (a: form): $ iff (al x a) a $;
    \\--| @conversion both
    \\axiom not_al {x: var} (b: form x): $ iff (not (al x b)) (ex x (not b)) $;
    \\--| @conversion both
    \\axiom imp_def (a b: form): $ iff (imp a b) (or (not a) b) $;
    \\
;

test "conversion? applies a rule of passage when the side condition holds" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // x does not occur in p, so pulling p out of the quantifier is legal.
    const mm0_src = fol_passage_prelude ++
        \\theorem pass_out {x: var} (p: form) (h: $ or p (al x (Pr x)) $): $ al x (or p (Pr x)) $;
    ;
    const proof_src =
        \\pass_out
        \\----
        \\goal: $ al x (or p (Pr x)) $ by conversion?
        \\
    ;

    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    const replacement = found.items[0].replacement;
    try std.testing.expect(
        std.mem.indexOf(u8, replacement, "pass_al_or") != null,
    );
    try std.testing.expect(std.mem.indexOf(u8, replacement, "mpbi") != null);
    try std.testing.expect(std.mem.indexOf(u8, replacement, "#1") != null);

    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "conversion? refuses an unsound generalization as a dep-deferred miss" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // al_vac matches `al x (Pr x)` textually, but its `a` binder must
    // avoid x and the class holds only `Pr x` — the gate defers forever
    // and the saturated miss names the dependency constraint. Without the
    // gate this "proves" Pr x ⊢ al x (Pr x) and emits a broken splice.
    const mm0_src = fol_passage_prelude ++
        \\theorem vac_blocked {x: var} (h: $ Pr x $): $ al x (Pr x) $;
    ;
    const proof_src =
        \\vac_blocked
        \\----
        \\goal: $ al x (Pr x) $ by conversion?
        \\
    ;

    var miss = try conversionSuggestions(&arena, mm0_src, proof_src, .{
        .status_detail = true,
    });
    defer miss.deinit();
    try std.testing.expectEqual(types.SearchStatus.miss, miss.status);
    const detail = miss.status_detail orelse return error.MissingStatusDetail;
    try std.testing.expect(
        std.mem.indexOf(u8, detail, "the egraph saturated") != null,
    );
    try std.testing.expect(
        std.mem.indexOf(u8, detail, "variable-dependency") != null,
    );
}

test "conversion? discharges a side condition through a local equation" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // The pulled-out slot's class is {Pr x, an p q}: the unmasked
    // extraction minimum is the x-containing `Pr x`, so the splice only
    // checks if the restricted binder extracts under its avoid-mask and
    // cites `an p q`. This is the test that fails if the gate admits
    // without constraint-aware extraction.
    const mm0_src = fol_passage_prelude ++
        \\theorem pass_via_eq {x: var} (p q: form) (h1: $ iff (Pr x) (an p q) $) (h2: $ or (Pr x) (al x (Pr x)) $): $ al x (or (Pr x) (Pr x)) $;
    ;
    const proof_src =
        \\pass_via_eq
        \\----
        \\goal: $ al x (or (Pr x) (Pr x)) $ by conversion?
        \\
    ;

    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    const replacement = found.items[0].replacement;
    try std.testing.expect(
        std.mem.indexOf(u8, replacement, "pass_al_or") != null,
    );

    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "conversion? applies fully-dependent binder rules without deferral" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // not_al's binder depends on x — no restriction, no gate involvement.
    const mm0_src = fol_passage_prelude ++
        \\theorem prenex_neg {x: var} (h: $ ex x (not (Pr x)) $): $ not (al x (Pr x)) $;
    ;
    const proof_src =
        \\prenex_neg
        \\----
        \\goal: $ not (al x (Pr x)) $ by conversion?
        \\
    ;

    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    try std.testing.expect(
        std.mem.indexOf(u8, found.items[0].replacement, "not_al") != null,
    );

    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "conversion? rewrites implications into CNF shape" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const mm0_src = fol_passage_prelude ++
        \\theorem cnf_imp (p q: form) (h: $ or (not p) q $): $ imp p q $;
    ;
    const proof_src =
        \\cnf_imp
        \\----
        \\goal: $ imp p q $ by conversion?
        \\
    ;

    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    try std.testing.expect(
        std.mem.indexOf(u8, found.items[0].replacement, "imp_def") != null,
    );

    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

// --- conversion? stress: two-sorted equational theories -------------------
//
// Boolean-algebra and commutative-ring axiom sets adapted from
// gleachkr/eggbau (tests/fixtures/domain_boolean_algebra.mm0 and
// domain_ring.mm0). Unlike the wff-only prelude above, every rewrite step
// here happens at a non-provable object sort (`bool`/`R`) under `eq`, so a
// chain must lift through the relation term's own congruence (`eq_congr`)
// into provable `iff` land before the mpbi transport fires. The object
// sort's `@relation` bundle is transport-free (`_`).

const bool_conversion_prelude =
    \\delimiter $ ( ) $;
    \\sort bool;
    \\provable sort wff;
    \\term iff (p q: wff): wff;
    \\term eq (x y: bool): wff;
    \\term top: bool;
    \\term bot: bool;
    \\term and (x y: bool): bool;
    \\term or (x y: bool): bool;
    \\term not (x: bool): bool;
    \\--| @relation wff iff iff_refl iff_trans iff_symm mpbi
    \\axiom iff_refl (a: wff): $ iff a a $;
    \\axiom iff_trans (a b c: wff) (h1: $ iff a b $) (h2: $ iff b c $): $ iff a c $;
    \\axiom iff_symm (a b: wff) (h: $ iff a b $): $ iff b a $;
    \\axiom mpbi (a b: wff) (h1: $ iff a b $) (h2: $ a $): $ b $;
    \\--| @relation bool eq eq_refl eq_trans eq_symm _
    \\axiom eq_refl (x: bool): $ eq x x $;
    \\axiom eq_trans (x y z: bool) (h1: $ eq x y $) (h2: $ eq y z $): $ eq x z $;
    \\axiom eq_symm (x y: bool) (h: $ eq x y $): $ eq y x $;
    \\--| @congr
    \\axiom eq_congr (a b c d: bool) (h1: $ eq a b $) (h2: $ eq c d $): $ iff (eq a c) (eq b d) $;
    \\--| @congr
    \\axiom and_congr (a b c d: bool) (h1: $ eq a b $) (h2: $ eq c d $): $ eq (and a c) (and b d) $;
    \\--| @congr
    \\axiom or_congr (a b c d: bool) (h1: $ eq a b $) (h2: $ eq c d $): $ eq (or a c) (or b d) $;
    \\--| @congr
    \\axiom not_congr (a b: bool) (h: $ eq a b $): $ eq (not a) (not b) $;
    \\--| @conversion comm
    \\axiom and_comm (x y: bool): $ eq (and x y) (and y x) $;
    \\--| @conversion assoc
    \\axiom and_assoc (x y z: bool): $ eq (and (and x y) z) (and x (and y z)) $;
    \\--| @conversion ltr
    \\axiom and_idem (x: bool): $ eq (and x x) x $;
    \\--| @conversion ltr
    \\axiom and_top (x: bool): $ eq (and top x) x $;
    \\--| @conversion ltr
    \\axiom and_bot (x: bool): $ eq (and bot x) bot $;
    \\--| @conversion comm
    \\axiom or_comm (x y: bool): $ eq (or x y) (or y x) $;
    \\--| @conversion assoc
    \\axiom or_assoc (x y z: bool): $ eq (or (or x y) z) (or x (or y z)) $;
    \\--| @conversion ltr
    \\axiom or_idem (x: bool): $ eq (or x x) x $;
    \\--| @conversion ltr
    \\axiom or_bot (x: bool): $ eq (or bot x) x $;
    \\--| @conversion ltr
    \\axiom or_top (x: bool): $ eq (or x top) top $;
    \\--| @conversion ltr
    \\axiom and_absorb (x y: bool): $ eq (and x (or x y)) x $;
    \\--| @conversion ltr
    \\axiom or_absorb (x y: bool): $ eq (or x (and x y)) x $;
    \\--| @conversion ltr
    \\axiom and_compl (x: bool): $ eq (and x (not x)) bot $;
    \\--| @conversion ltr
    \\axiom or_compl (x: bool): $ eq (or x (not x)) top $;
    \\--| @conversion ltr
    \\axiom not_not (x: bool): $ eq (not (not x)) x $;
    \\--| @conversion ltr
    \\axiom not_top: $ eq (not top) bot $;
    \\--| @conversion ltr
    \\axiom not_bot: $ eq (not bot) top $;
    \\--| @conversion both
    \\axiom demorgan_and (x y: bool): $ eq (not (and x y)) (or (not x) (not y)) $;
    \\--| @conversion both
    \\axiom demorgan_or (x y: bool): $ eq (not (or x y)) (and (not x) (not y)) $;
    \\--| @conversion ltr
    \\axiom or_factor (x y z: bool): $ eq (or (and x y) (and x z)) (and x (or y z)) $;
    \\--| @conversion ltr
    \\axiom and_factor (x y z: bool): $ eq (and (or x y) (or x z)) (or x (and y z)) $;
    \\
;

const ring_conversion_prelude =
    \\delimiter $ ( ) $;
    \\sort R;
    \\provable sort wff;
    \\term iff (p q: wff): wff;
    \\term eq (x y: R): wff;
    \\term zero: R;
    \\term one: R;
    \\term add (x y: R): R;
    \\term mul (x y: R): R;
    \\term neg (x: R): R;
    \\term sub (x y: R): R;
    \\--| @relation wff iff iff_refl iff_trans iff_symm mpbi
    \\axiom iff_refl (a: wff): $ iff a a $;
    \\axiom iff_trans (a b c: wff) (h1: $ iff a b $) (h2: $ iff b c $): $ iff a c $;
    \\axiom iff_symm (a b: wff) (h: $ iff a b $): $ iff b a $;
    \\axiom mpbi (a b: wff) (h1: $ iff a b $) (h2: $ a $): $ b $;
    \\--| @relation R eq eq_refl eq_trans eq_symm _
    \\axiom eq_refl (x: R): $ eq x x $;
    \\axiom eq_trans (x y z: R) (h1: $ eq x y $) (h2: $ eq y z $): $ eq x z $;
    \\axiom eq_symm (x y: R) (h: $ eq x y $): $ eq y x $;
    \\--| @congr
    \\axiom eq_congr (a b c d: R) (h1: $ eq a b $) (h2: $ eq c d $): $ iff (eq a c) (eq b d) $;
    \\--| @congr
    \\axiom add_congr (a b c d: R) (h1: $ eq a b $) (h2: $ eq c d $): $ eq (add a c) (add b d) $;
    \\--| @congr
    \\axiom mul_congr (a b c d: R) (h1: $ eq a b $) (h2: $ eq c d $): $ eq (mul a c) (mul b d) $;
    \\--| @congr
    \\axiom neg_congr (a b: R) (h: $ eq a b $): $ eq (neg a) (neg b) $;
    \\--| @congr
    \\axiom sub_congr (a b c d: R) (h1: $ eq a b $) (h2: $ eq c d $): $ eq (sub a c) (sub b d) $;
    \\--| @conversion ltr
    \\axiom add_zero (x: R): $ eq (add x zero) x $;
    \\--| @conversion ltr
    \\axiom zero_add (x: R): $ eq (add zero x) x $;
    \\--| @conversion comm
    \\axiom add_comm (x y: R): $ eq (add x y) (add y x) $;
    \\--| @conversion assoc
    \\axiom add_assoc (x y z: R): $ eq (add (add x y) z) (add x (add y z)) $;
    \\--| @conversion ltr
    \\axiom add_neg (x: R): $ eq (add x (neg x)) zero $;
    \\--| @conversion ltr
    \\axiom neg_neg (x: R): $ eq (neg (neg x)) x $;
    \\--| @conversion ltr
    \\axiom mul_one (x: R): $ eq (mul x one) x $;
    \\--| @conversion ltr
    \\axiom one_mul (x: R): $ eq (mul one x) x $;
    \\--| @conversion ltr
    \\axiom mul_zero (x: R): $ eq (mul x zero) zero $;
    \\--| @conversion ltr
    \\axiom zero_mul (x: R): $ eq (mul zero x) zero $;
    \\--| @conversion comm
    \\axiom mul_comm (x y: R): $ eq (mul x y) (mul y x) $;
    \\--| @conversion assoc
    \\axiom mul_assoc (x y z: R): $ eq (mul (mul x y) z) (mul x (mul y z)) $;
    \\--| @conversion both
    \\axiom factor_l (x y z: R): $ eq (add (mul x y) (mul x z)) (mul x (add y z)) $;
    \\--| @conversion both
    \\axiom factor_r (x y z: R): $ eq (add (mul x z) (mul y z)) (mul (add x y) z) $;
    \\--| @conversion ltr
    \\axiom neg_mul_l (x y: R): $ eq (mul (neg x) y) (neg (mul x y)) $;
    \\--| @conversion ltr
    \\axiom neg_mul_r (x y: R): $ eq (mul x (neg y)) (neg (mul x y)) $;
    \\--| @conversion ltr
    \\axiom sub_def (x y: R): $ eq (sub x y) (add x (neg y)) $;
    \\
;

test "conversion? lifts a two-sorted chained De Morgan through eq_congr" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const mm0_src = bool_conversion_prelude ++
        \\theorem conv_chained_demorgan (x y z w: bool)
        \\  (h: $ eq (not (or x (and y z))) w $):
        \\  $ eq (and (not x) (or (not y) (not z))) w $;
    ;
    const proof_src =
        \\conv_chained_demorgan
        \\----
        \\goal: $ eq (and (not x) (or (not y) (not z))) w $ by conversion?
        \\
    ;

    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    const replacement = found.items[0].replacement;
    // Both De Morgan steps happen at sort bool; the inner one additionally
    // lifts through and_congr, and every step crosses into iff land via
    // the relation term's own congruence before the transport.
    try std.testing.expect(std.mem.indexOf(u8, replacement, "demorgan_or") != null);
    try std.testing.expect(std.mem.indexOf(u8, replacement, "demorgan_and") != null);
    try std.testing.expect(std.mem.indexOf(u8, replacement, "and_congr") != null);
    try std.testing.expect(std.mem.indexOf(u8, replacement, "eq_congr") != null);
    try std.testing.expect(std.mem.indexOf(u8, replacement, "iff_trans") != null);
    try std.testing.expect(std.mem.indexOf(u8, replacement, "mpbi") != null);
    try std.testing.expect(std.mem.indexOf(u8, replacement, "#1") != null);

    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "conversion? proves boolean consensus through factor, complement, and unit" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // or(x∧y, x∧¬y) → x∧(y∨¬y) → x∧⊤ → ⊤∧x → x: the complement and unit
    // collapse only exist as nodes minted by earlier rule instantiations,
    // so the chain needs several saturation rounds.
    const mm0_src = bool_conversion_prelude ++
        \\theorem conv_consensus (x y w: bool) (h: $ eq x w $):
        \\  $ eq (or (and x y) (and x (not y))) w $;
    ;
    const proof_src =
        \\conv_consensus
        \\----
        \\goal: $ eq (or (and x y) (and x (not y))) w $ by conversion?
        \\
    ;

    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    const replacement = found.items[0].replacement;
    try std.testing.expect(std.mem.indexOf(u8, replacement, "or_factor") != null);
    try std.testing.expect(std.mem.indexOf(u8, replacement, "or_compl") != null);
    try std.testing.expect(std.mem.indexOf(u8, replacement, "and_top") != null);
    try std.testing.expect(std.mem.indexOf(u8, replacement, "mpbi") != null);

    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "conversion? reverses an ltr rule at the object sort through eq_symm" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // The goal's lhs IS the or_absorb redex, so the ref-to-goal chain
    // traverses that union edge backwards: the symm fires at sort bool
    // (eq_symm), not at the wff level.
    const mm0_src = bool_conversion_prelude ++
        \\theorem conv_absorb_expand (x y w: bool) (h: $ eq x w $):
        \\  $ eq (or x (and x y)) w $;
    ;
    const proof_src =
        \\conv_absorb_expand
        \\----
        \\goal: $ eq (or x (and x y)) w $ by conversion?
        \\
    ;

    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    const replacement = found.items[0].replacement;
    try std.testing.expect(std.mem.indexOf(u8, replacement, "or_absorb") != null);
    try std.testing.expect(std.mem.indexOf(u8, replacement, "eq_symm") != null);

    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "conversion? extracts through cyclic nested ground-sum classes" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // Digit-addition rules make derived ground-sum classes self-containing
    // (hZ+hZ=hZ chains 0-padded numerals into classes containing same-head
    // compounds of themselves). Extraction must thread the exact forest
    // vertices to stay well-founded; class-anchored re-rendering used to
    // re-pose parent alignments unboundedly (a misleading miss).
    const mm0_src = @embedFile("fixtures/cyclic_ground_sums.mm0");
    const proof_src = @embedFile("fixtures/cyclic_ground_sums.auf");

    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);

    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "conversion? extracts chained ground sums under AC certificates" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // Same cyclic-class family as above, but the assoc/comm laws are
    // enrolled as AC role certificates (bag nodes), and the second ground
    // sum is computed from the first across a comm rearrangement.
    const mm0_src = @embedFile("fixtures/ac_certificate_ground_sums.mm0");
    const proof_src = @embedFile("fixtures/ac_certificate_ground_sums.auf");

    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);

    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "conversion? survives a goal-irrelevant reconvergent match flood" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // The goal needs only assoc + one digit rule, but the pool carries an
    // unrelated reconvergent add chain (a symbolic a+b, two +1 links, and
    // a join of two chain levels) whose assoc/comm closure floods one
    // iteration's match collection past the retained-match budget. The
    // driver saturates one iteration per call (goal-converged early
    // exit), so match dedup must persist on the egraph across calls —
    // rebuilt per call, every iteration re-collected the same
    // already-applied no-op effects, tripped the budget, and starved the
    // goal's matches forever: a node-count fixpoint that never saturated
    // and could not be rescued by any `iters:` value.
    const mm0_src = @embedFile("fixtures/reconvergent_interference_chain.mm0");
    const proof_src = @embedFile("fixtures/reconvergent_interference_chain.auf");

    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "conversion? bounds a carry-rule splice flood to an honest capped miss" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // Carry rules mint nested sums whose classes chain 16 deep under
    // bag absorption; splice flattening used to expand every member
    // reference independently (the cycle guard is per-path, blind to
    // sharing), so one rebuild allocated flat forms exponentially
    // longer than the node graph and the process died of OOM at ~650
    // e-nodes. The splice member cap, the per-iteration enumeration
    // step pool, and budget-fixpoint detection must bound the whole
    // widened search (iters: 80, nodes: 100000) to seconds, and the
    // report must say that raising `iters:` cannot help.
    const mm0_src = @embedFile("fixtures/carry_cascade_interference.mm0");
    const proof_src = @embedFile("fixtures/carry_cascade_interference.auf");

    var miss = try conversionSuggestions(&arena, mm0_src, proof_src, .{
        .status_detail = true,
    });
    defer miss.deinit();
    try std.testing.expectEqual(
        types.SearchStatus.budget_exhausted,
        miss.status,
    );
    const detail = miss.status_detail orelse return error.MissingStatusDetail;
    try std.testing.expect(
        std.mem.indexOf(u8, detail, "budget-limited fixpoint") != null,
    );
    try std.testing.expect(
        std.mem.indexOf(u8, detail, "NOT a forced negative") != null,
    );
}

test "conversion? forced negative on the boolean lattice" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // x∧y and x∨y are never lattice-convertible; the full boolean rule set
    // must still saturate (AC permutations of the seeds are finite) and
    // report a forced negative.
    const mm0_src = bool_conversion_prelude ++
        \\theorem conv_bool_none (x y w: bool) (h: $ eq (and x y) w $):
        \\  $ eq (or x y) w $;
    ;
    const proof_src =
        \\conv_bool_none
        \\----
        \\goal: $ eq (or x y) w $ by conversion?
        \\
    ;

    var miss = try conversionSuggestions(&arena, mm0_src, proof_src, .{
        .status_detail = true,
    });
    defer miss.deinit();
    try std.testing.expectEqual(types.SearchStatus.miss, miss.status);
    const detail = miss.status_detail orelse return error.MissingStatusDetail;
    try std.testing.expect(
        std.mem.indexOf(u8, detail, "the egraph saturated") != null,
    );
    try std.testing.expect(
        std.mem.indexOf(u8, detail, "no chain of the enrolled") != null,
    );
}

test "conversion? proves ring sub_self through the definitional unfold" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const mm0_src = ring_conversion_prelude ++
        \\theorem conv_sub_self (x w: R) (h: $ eq zero w $):
        \\  $ eq (sub x x) w $;
    ;
    const proof_src =
        \\conv_sub_self
        \\----
        \\goal: $ eq (sub x x) w $ by conversion?
        \\
    ;

    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    const replacement = found.items[0].replacement;
    try std.testing.expect(std.mem.indexOf(u8, replacement, "sub_def") != null);
    try std.testing.expect(std.mem.indexOf(u8, replacement, "add_neg") != null);

    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "conversion? pushes negation through a product under neg_congr" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // (−x)·(−y) → ¬(x·(−y)) → ¬(¬(x·y)) → x·y: the middle step rewrites
    // underneath neg, exercising the unary congruence lift.
    const mm0_src = ring_conversion_prelude ++
        \\theorem conv_neg_mul_neg (x y w: R) (h: $ eq (mul x y) w $):
        \\  $ eq (mul (neg x) (neg y)) w $;
    ;
    const proof_src =
        \\conv_neg_mul_neg
        \\----
        \\goal: $ eq (mul (neg x) (neg y)) w $ by conversion?
        \\
    ;

    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    const replacement = found.items[0].replacement;
    // Either neg_mul orientation may anchor the route; both share the
    // prefix, and the double negation must collapse under the unary lift.
    try std.testing.expect(std.mem.indexOf(u8, replacement, "neg_mul") != null);
    try std.testing.expect(std.mem.indexOf(u8, replacement, "neg_neg") != null);
    try std.testing.expect(std.mem.indexOf(u8, replacement, "neg_congr") != null);

    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "conversion? proves difference of squares across distributivity and AC" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // The deep stress: (a+b)(a−b) expands through both-direction
    // distributivity, commutes ba into ab, cancels via add_neg after AC
    // regrouping, and refolds into sub — many rounds, dense egraph.
    const mm0_src = ring_conversion_prelude ++
        \\theorem conv_diff_squares (a b w: R)
        \\  (h: $ eq (mul (add a b) (sub a b)) w $):
        \\  $ eq (sub (mul a a) (mul b b)) w $;
    ;
    const proof_src =
        \\conv_diff_squares
        \\----
        \\goal: $ eq (sub (mul a a) (mul b b)) w $ by conversion?
        \\
    ;

    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    const replacement = found.items[0].replacement;
    try std.testing.expect(std.mem.indexOf(u8, replacement, "mpbi") != null);
    try std.testing.expect(std.mem.indexOf(u8, replacement, "#1") != null);

    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

// --- conversion? def-wrangling (@conversion unfold/fold/both) -------------
//
// Enrolled defs saturate as ordinary rules built from the def's own
// equation rel(definiens, head args). Each def step lowers as a single
// refl line the checker closes through transparent unfolding. A hidden
// dummy is a pattern binder BOUND to an existing variable at match time;
// its freshness against every arg instantiation rides the dep-gate
// restrictions, which is load-bearing for suggestion validity (the
// verifier rejects a captured witness with DepViolation).

const conversion_def_prelude =
    \\delimiter $ ( ) $;
    \\sort var;
    \\provable sort form;
    \\term an (p q: form): form;
    \\term or (p q: form): form;
    \\term iff (p q: form): form;
    \\term eqv (a b: var): form;
    \\term ex {x: var} (p: form x): form;
    \\--| @relation form iff iff_refl iff_trans iff_symm mpbi
    \\axiom iff_refl (a: form): $ iff a a $;
    \\axiom iff_trans (a b c: form) (h1: $ iff a b $) (h2: $ iff b c $): $ iff a c $;
    \\axiom iff_symm (a b: form) (h: $ iff a b $): $ iff b a $;
    \\axiom mpbi (a b: form) (h1: $ iff a b $) (h2: $ a $): $ b $;
    \\--| @congr
    \\axiom an_congr (a b c d: form) (h1: $ iff a b $) (h2: $ iff c d $): $ iff (an a c) (an b d) $;
    \\--| @congr
    \\axiom or_congr (a b c d: form) (h1: $ iff a b $) (h2: $ iff c d $): $ iff (or a c) (or b d) $;
    \\
;

test "conversion? folds a dummy-free def" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const mm0_src = conversion_def_prelude ++
        \\--| @conversion fold
        \\def dup (a: form): form = $ an a a $;
        \\theorem conv_fold (p q: form) (h: $ or (an p p) q $): $ or (dup p) q $;
    ;
    const proof_src =
        \\conv_fold
        \\----
        \\goal: $ or (dup p) q $ by conversion?
        \\
    ;

    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    const replacement = found.items[0].replacement;
    // The def boundary lowers as a refl line, lifted through @congr and
    // transported onto the hypothesis.
    try std.testing.expect(std.mem.indexOf(u8, replacement, "iff_refl") != null);
    try std.testing.expect(std.mem.indexOf(u8, replacement, "or_congr") != null);
    try std.testing.expect(std.mem.indexOf(u8, replacement, "mpbi") != null);

    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "conversion? unfolds a dummy-free def" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const mm0_src = conversion_def_prelude ++
        \\--| @conversion unfold
        \\def dup (a: form): form = $ an a a $;
        \\theorem conv_unfold (p q: form) (h: $ or (dup p) q $): $ or (an p p) q $;
    ;
    const proof_src =
        \\conv_unfold
        \\----
        \\goal: $ or (an p p) q $ by conversion?
        \\
    ;

    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "conversion? both-enrolled def rewrites in both directions at once" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // One chain needs an unfold (dup p) and a fold (an q q) of the same def.
    const mm0_src = conversion_def_prelude ++
        \\--| @conversion both
        \\def dup (a: form): form = $ an a a $;
        \\theorem conv_both (p q: form) (h: $ or (dup p) (an q q) $): $ or (an p p) (dup q) $;
    ;
    const proof_src =
        \\conv_both
        \\----
        \\goal: $ or (an p p) (dup q) $ by conversion?
        \\
    ;

    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "conversion? folds a hidden-dummy def binding the written witness" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // someeq's dummy w is a pattern binder matched against the theorem's
    // own bound variable u; the freshness condition u ∉ deps(a) holds.
    const mm0_src = conversion_def_prelude ++
        \\--| @conversion fold
        \\def someeq {.w: var} (v: var): form = $ ex w (eqv w v) $;
        \\theorem conv_hidden {u: var} (a: var) (q: form) (h: $ an (ex u (eqv u a)) q $): $ an (someeq a) q $;
    ;
    const proof_src =
        \\conv_hidden
        \\----
        \\goal: $ an (someeq a) q $ by conversion?
        \\
    ;

    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    const replacement = found.items[0].replacement;
    try std.testing.expect(std.mem.indexOf(u8, replacement, "iff_refl") != null);

    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "conversion? refuses a captured dummy witness as a deferred miss" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // ex u (eqv u u) is NOT an unfolding of someeq u: the witness u is the
    // arg itself (capture), which the verifier rejects as a DepViolation.
    // The dep gate must defer the fold match forever — an honest miss, no
    // unsound suggestion.
    const mm0_src = conversion_def_prelude ++
        \\--| @conversion fold
        \\def someeq {.w: var} (v: var): form = $ ex w (eqv w v) $;
        \\theorem conv_capture {u: var} (q: form) (h: $ an (ex u (eqv u u)) q $): $ an (someeq u) q $;
    ;
    const proof_src =
        \\conv_capture
        \\----
        \\goal: $ an (someeq u) q $ by conversion?
        \\
    ;

    var miss = try conversionSuggestions(&arena, mm0_src, proof_src, .{
        .status_detail = true,
    });
    defer miss.deinit();
    try std.testing.expectEqual(types.SearchStatus.miss, miss.status);
    const detail = miss.status_detail orelse return error.MissingStatusDetail;
    try std.testing.expect(
        std.mem.indexOf(u8, detail, "the egraph saturated") != null,
    );
    try std.testing.expect(
        std.mem.indexOf(u8, detail, "variable-dependency") != null,
    );
}

test "conversion? unannotated defs stay dormant" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const mm0_src = conversion_def_prelude ++
        \\def dup (a: form): form = $ an a a $;
        \\theorem conv_dormant (p q: form) (h: $ or (an p p) q $): $ or (dup p) q $;
    ;
    const proof_src =
        \\conv_dormant
        \\----
        \\goal: $ or (dup p) q $ by conversion?
        \\
    ;

    var miss = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer miss.deinit();
    try std.testing.expectEqual(types.SearchStatus.miss, miss.status);
}

test "conversion? folds a bag-shaped definiens on the AC path" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // dup's definiens flattens to the sub-multiset {p, p} of the 3-member
    // bag {q, p, p}; the leftover q rejoins the folded target as the
    // extension, exercising the bag-step lowering of a def rule.
    const mm0_src = conversion_ac_prelude ++
        \\--| @conversion fold
        \\def dup (a: wff): wff = $ an a a $;
        \\theorem conv_bag_fold (p q: wff) (h: $ an q (an p p) $): $ an (dup p) q $;
    ;
    const proof_src =
        \\conv_bag_fold
        \\----
        \\goal: $ an (dup p) q $ by conversion?
        \\
    ;

    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    const replacement = found.items[0].replacement;
    try std.testing.expect(std.mem.indexOf(u8, replacement, "iff_refl") != null);

    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}
