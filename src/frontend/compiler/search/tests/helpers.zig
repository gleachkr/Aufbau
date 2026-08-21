//! Shared fixtures and expectation helpers for the test files in this
//! directory. Everything here is re-exported `pub` so topic files can
//! alias what they use.

pub const std = @import("std");

pub const build_options = @import("build_options");

pub const types = @import("../types.zig");

pub const source = @import("../source.zig");

pub const fixture_mod = @import("../fixture.zig");

pub const apply_mod = @import("../apply.zig");

pub const backtrack = @import("../backward/backtrack.zig");

pub const prune = @import("../backward/prune.zig");

pub const plausible = @import("../backward/plausible.zig");

pub const abstract_prune = @import("../abstract_prune.zig");

pub const context_prune = @import("../context_prune.zig");

pub const seed = @import("../backward/seed.zig");

pub const def_match = @import("../backward/def_match.zig");

pub const acui = @import("../backward/acui.zig");

pub const Witness = @import("../backward/witness.zig");

pub const MetaStore = @import("../../inference/meta_store.zig").MetaStore;

pub const TemplateExpr = @import("../../../rules.zig").TemplateExpr;

pub const candidate_mod = @import("../candidate.zig");

pub const session_mod = @import("../session.zig");

pub const expr_mod = @import("../../../expr.zig");

pub const ExprId = expr_mod.ExprId;

pub const TheoremContext = expr_mod.TheoremContext;

pub const ProofScript = @import("../../../proof_script.zig");

pub const CompilerDiag = @import("../../../diag.zig");

pub const CompilerContext = @import("../../context.zig").CompilerContext;

pub const CheckedIr = @import("../../../checked_ir.zig");

pub const CheckedLine = CheckedIr.CheckedLine;

pub const Inference = @import("../../inference.zig");

pub const Check = @import("../../check.zig");

pub const DiagnosticSink = @import("../../diagnostic_sink.zig").DiagnosticSink;

pub const ProofParser = ProofScript.Parser;

pub const Goal = types.Goal;

pub const Context = types.Context;

pub const AttemptResult = types.AttemptResult;

pub const NameExprMap = types.NameExprMap;

pub const LabelIndexMap = types.LabelIndexMap;

pub const apply = apply_mod.apply;

pub const applyWithSession = apply_mod.applyWithSession;

pub const exact = backtrack.exact;

pub const tryCandidate = candidate_mod.tryCandidate;

pub const fixtureFor = fixture_mod.fixtureFor;

pub const fixtureForFullEnv = fixture_mod.fixtureForFullEnv;

pub const parseGoal = fixture_mod.parseGoal;

pub const runSearchLine = fixture_mod.runSearchLine;

pub const readProofCase = fixture_mod.readProofCase;

pub fn expectTimingCounter(value: u64) !void {
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
pub const ContextHarness = struct {
    allocator: std.mem.Allocator,
    labels: LabelIndexMap,
    checked: std.ArrayListUnmanaged(CheckedLine) = .{},
    diag_scratch: CompilerDiag.Scratch,
    cache: Inference.RuleUnifyCache,

    pub fn init(allocator: std.mem.Allocator) ContextHarness {
        return .{
            .allocator = allocator,
            .labels = LabelIndexMap.init(allocator),
            .diag_scratch = CompilerDiag.Scratch.init(allocator),
            .cache = Inference.RuleUnifyCache.init(allocator),
        };
    }

    pub fn deinit(self: *ContextHarness) void {
        self.labels.deinit();
        CheckedIr.deinitLines(self.allocator, self.checked.items);
        self.checked.deinit(self.allocator);
        self.diag_scratch.deinit();
        self.cache.deinit();
    }

    pub fn context(self: *ContextHarness, fixture: *fixture_mod.Fixture) Context {
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

pub fn expectCaseLineSearch(
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

pub fn expectApplyContains(
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

pub fn expectApplyNotContains(
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

pub fn expectRuleIsUnavailableAtSearchPoint(
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

pub fn expectApplyRuleOrder(
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

pub fn expectExactRuleOrderWithPrefix(
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

pub fn expectExactRuleOrder(
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

pub fn expectInlineSearch(
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

// `auto?` recursive generation. Goal `Q` is not provable by any
// single rule over the (empty) ref pool — `pq` needs a proof of `P` — but it is
// provable by `pq [p]`, one level of generated inline application.
pub const auto_chain_mm0 =
    \\delimiter $ ( ) $;
    \\provable sort wff;
    \\term P: wff;
    \\term Q: wff;
    \\axiom p: $ P $;
    \\axiom pq: $ P $ > $ Q $;
    \\theorem t: $ Q $;
;

// Inline `auto?` generation. Outer rule `qr` needs a proof of `Q` in its slot;
// `Q` is not provable by any single rule over the (empty) ref pool, but is
// provable by `pq [p]` — so an `auto?` in the slot must recursively generate,
// exactly as a top-level `auto?` does. `p2` gives a direct-ref alternative for
// the regression case; `S` is deliberately unreachable for the negative case.
pub const auto_inline_mm0 =
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

pub const GeneratedConclusionHookCtx = struct {
    wrong_conclusion: bool,
    wrong_expr: ExprId,
    calls: usize = 0,

    pub fn solve(
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

pub fn expectFirstExactRefs(
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

pub const tunables = @import("../tunables.zig");

// End-to-end fixture: `R` needs a two-level generated chain
// (`qr [pq [p []]]`), `S` is unprovable.
pub const tunable_chain_mm0 =
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

pub fn conversionSuggestions(
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
pub fn expectConversionCompiles(
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
    const Compiler = @import("../../../compiler.zig").Compiler;
    var compiler = Compiler.initWithProof(
        arena.allocator(),
        mm0_src,
        spliced,
    );
    try compiler.check();
}

// The same connectives with comm/assoc as role certificates: the AC laws
// are absorbed into bag interning instead of saturating, and the lowering
// pays them back as explicit certificate chains.
pub const conversion_ac_prelude =
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

pub const bool_conversion_prelude =
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
