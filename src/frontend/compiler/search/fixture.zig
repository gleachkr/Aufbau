//! Search fixture: the theory and target assertion a search runs against.
//! The editor's search builds one with `fixtureForSourceTarget`, which runs
//! the analysis walk up to the target (`Analyze.analyzeToSearchPoint`); the
//! unit tests build theirs with the `.mm0`-only walks in `tests/helpers.zig`.
//! Also the per-line helpers both share (`parseGoal`, `commitSearchLine`,
//! `searchContext`) and `readProofCase`.

const std = @import("std");
const types = @import("./types.zig");
const candidate_mod = @import("./candidate.zig");
const TheoremContext = @import("../../expr.zig").TheoremContext;
const ParseRecovery = @import("../../parse_recovery.zig");
const AssertionStmt = ParseRecovery.AssertionStmt;
const ProofScript = @import("../../proof_script.zig");
const CompilerDiag = @import("../../diag.zig");
const CompilerContext = @import("../context.zig").CompilerContext;
const CheckedIr = @import("../../checked_ir.zig");
const CheckedLine = CheckedIr.CheckedLine;
const Inference = @import("../inference.zig");
const Check = @import("../check.zig");
const Holes = @import("../holes.zig");
const DiagnosticSink = @import("../diagnostic_sink.zig").DiagnosticSink;
const Analyze = @import("../pipeline/analyze.zig");
const TheoryState = @import("../theory_state.zig").TheoryState;
const Goal = types.Goal;
const Context = types.Context;
const AttemptOptions = types.AttemptOptions;
const NameExprMap = types.NameExprMap;
const LabelIndexMap = types.LabelIndexMap;

/// A search target resolved from a proof source: the enclosing block plus the
/// path to the specific line/inline application to search at. Consumed by
/// `fixtureForSourceTarget`; produced by `source.findSearchLine`.
pub const SourceTarget = struct {
    block: ProofScript.ProofBlock,
    line_index: usize,
    path: []const usize,
};

pub const Fixture = struct {
    theory: TheoryState,
    assertion: AssertionStmt,
    available_rule_count: usize,
};

pub fn fixtureForSourceTarget(
    allocator: std.mem.Allocator,
    mm0_src: []const u8,
    proof_src: []const u8,
    target: SourceTarget,
) !Fixture {
    var sink = DiagnosticSink.init(mm0_src, proof_src);
    var compiler = CompilerContext.init(mm0_src, proof_src, .none, &sink);
    // A local lemma before the target may itself hold a placeholder or a
    // half-typed line; tolerate both the way the LSP analysis does, so the
    // target's search survives an unfinished sibling.
    compiler.allow_search_placeholders = true;
    // The analysis walk, which recovers from a broken statement or local
    // item by dropping it, so a broken statement earlier in the file
    // silences neither the analysis nor the search of a later theorem. Its
    // proof stream is lenient like `findSearchLine`'s parse, so the target
    // lemma's span matches.
    const point = try Analyze.analyzeToSearchPoint(
        &compiler,
        allocator,
        switch (target.block.kind) {
            .theorem => .{ .theorem = target.block.name },
            .lemma => .{ .lemma = target.block.span },
        },
    );
    return .{
        .theory = point.theory,
        .assertion = point.assertion,
        .available_rule_count = point.theory.env.rules.items.len,
    };
}

pub fn readProofCase(
    allocator: std.mem.Allocator,
    stem: []const u8,
    ext: []const u8,
) ![]u8 {
    const path = try std.fmt.allocPrint(
        allocator,
        "tests/proof_cases/{s}.{s}",
        .{ stem, ext },
    );
    defer allocator.free(path);
    return try std.Io.Dir.cwd().readFileAlloc(std.testing.io, path, allocator, .unlimited);
}

pub fn parseGoal(
    fixture: *Fixture,
    theorem: *TheoremContext,
    theorem_vars: *NameExprMap,
    text: []const u8,
) !Goal {
    const parsed = try Holes.parseAssertion(
        &fixture.theory.parser,
        theorem,
        theorem_vars,
        &fixture.theory.sort_vars,
        text,
    );
    return switch (parsed) {
        .concrete => |expr| .{ .concrete = expr },
        .holey => |expr| .{ .holey = expr },
    };
}

/// Check `line` against the fixture and commit it: its lines join `checked`
/// and `theorem`/`theorem_vars` advance. Returns the produced line's index.
pub fn commitSearchLine(
    allocator: std.mem.Allocator,
    compiler: *CompilerContext,
    fixture: *Fixture,
    labels: *LabelIndexMap,
    checked: *std.ArrayListUnmanaged(CheckedLine),
    theorem: *TheoremContext,
    theorem_vars: *NameExprMap,
    diag_scratch: *CompilerDiag.Scratch,
    rule_unify_cache: *Inference.RuleUnifyCache,
    line: ProofScript.ProofLine,
) !usize {
    const context = searchContext(
        allocator,
        fixture,
        labels,
        checked,
        diag_scratch,
        rule_unify_cache,
    );
    return candidate_mod.commit(
        compiler,
        &context,
        line.application,
        try parseGoal(fixture, theorem, theorem_vars, line.assertion.text),
        theorem,
        theorem_vars,
        searchLineOptions(line),
    );
}

/// The search context over the fixture's theory and target, with the
/// caller's per-search state.
pub fn searchContext(
    allocator: std.mem.Allocator,
    fixture: *Fixture,
    labels: *LabelIndexMap,
    checked: *std.ArrayListUnmanaged(CheckedLine),
    diag_scratch: *CompilerDiag.Scratch,
    rule_unify_cache: *Inference.RuleUnifyCache,
) Context {
    return .{
        .allocator = allocator,
        .parser = &fixture.theory.parser,
        .env = &fixture.theory.env,
        .registry = &fixture.theory.registry,
        .rule_catalog = &fixture.theory.rule_catalog,
        .fresh_bindings = &fixture.theory.fresh_bindings,
        .freshen_bindings = &fixture.theory.freshen_bindings,
        .views = &fixture.theory.views,
        .sort_vars = &fixture.theory.sort_vars,
        .assertion = fixture.assertion,
        .labels = labels,
        .checked = checked,
        .diag_scratch = diag_scratch,
        .rule_unify_cache = rule_unify_cache,
        .available_rule_count = fixture.available_rule_count,
    };
}

pub fn searchLineOptions(line: ProofScript.ProofLine) AttemptOptions {
    return .{
        .line_label = line.label,
        .assertion_span = line.assertion.span,
        .diagnostic_span = line.span,
    };
}
