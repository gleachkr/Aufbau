const std = @import("std");
const types = @import("./types.zig");
const tunables = @import("./tunables.zig");
const ConversionSearch = @import("./conversion.zig");
const timer = @import("./timer.zig");
const apply_mod = @import("./apply.zig");
const backtrack = @import("./backward/backtrack.zig");
const candidate_mod = @import("./candidate.zig");
const generate_mod = @import("./generate.zig");
const refs_mod = @import("./refs.zig");
const session_mod = @import("./session.zig");
const prune = @import("./backward/prune.zig");
const ExprId = @import("../../expr.zig").ExprId;
const TheoremContext = @import("../../expr.zig").TheoremContext;
const GlobalEnv = @import("../../env.zig").GlobalEnv;
const ParseRecovery = @import("../../parse_recovery.zig");
const AssertionStmt = ParseRecovery.AssertionStmt;
const SortStmt = ParseRecovery.SortStmt;
const TermStmt = ParseRecovery.TermStmt;
const MM0Parser = ParseRecovery.MM0Parser;
const MM0Stmt = ParseRecovery.MM0Stmt;
const ProofScript = @import("../../proof_script.zig");
const RuleApplication = ProofScript.RuleApplication;
const Ref = ProofScript.Ref;
const Span = ProofScript.Span;
const TemplateExpr = @import("../../rules.zig").TemplateExpr;
const RewriteRegistry = @import("../../rewrite_registry.zig").RewriteRegistry;
const RuleCatalog = @import("../rule_catalog.zig");
const CompilerViews = @import("../views.zig");
const FreshSelect = @import("../fresh_select.zig");
const CompilerDiag = @import("../diag.zig");
const CompilerContext = @import("../context.zig").CompilerContext;
const CheckedIr = @import("../checked_ir.zig");
const CheckedLine = CheckedIr.CheckedLine;
const Inference = @import("../inference.zig");
const OpenTerms = @import("../inference/open_terms.zig");
const Check = @import("../check.zig");
const CompilerVars = @import("../vars.zig");
const Metadata = @import("../metadata.zig");
const Holes = @import("../holes.zig");
const DiagnosticSink = @import("../diagnostic_sink.zig").DiagnosticSink;
const PipelineCommon = @import("../pipeline/common.zig");
const ProofParser = ProofScript.Parser;
const Goal = types.Goal;
const Context = types.Context;
const ApplyCandidate = types.ApplyCandidate;
const ExactCandidate = types.ExactCandidate;
const SourceSuggestion = types.SourceSuggestion;
const SourceSuggestionOptions = types.SourceSuggestionOptions;
const SourceSuggestions = types.SourceSuggestions;
const AttemptResult = types.AttemptResult;
const NameExprMap = types.NameExprMap;
const LabelIndexMap = types.LabelIndexMap;
const FreshDecl = types.FreshDecl;
const FreshenDecl = types.FreshenDecl;
const ViewDecl = types.ViewDecl;
const SortVarRegistry = types.SortVarRegistry;
const applyWithSession = apply_mod.applyWithSession;
const exactWithSession = backtrack.exactWithSession;
const tryCandidate = candidate_mod.tryCandidate;
const extractHypPartialBindings = prune.extractHypPartialBindings;
const fixture_mod = @import("./fixture.zig");
const SourceTarget = fixture_mod.SourceTarget;
const fixtureForSourceTarget = fixture_mod.fixtureForSourceTarget;
const parseGoal = fixture_mod.parseGoal;
const runSearchLine = fixture_mod.runSearchLine;

pub fn suggestionsAtSourceOffset(
    allocator: std.mem.Allocator,
    mm0_src: []const u8,
    proof_src: []const u8,
    offset: usize,
    caller_options: SourceSuggestionOptions,
) !SourceSuggestions {
    // The result's `status` is derived from the counters' exhaustion flags, so
    // thread a local block when the caller didn't pass one. `collect` stays
    // false, which skips every per-candidate diagnostic; search behavior never
    // depends on the counters (they are observe-only), so this is free.
    var local_counters = types.SearchCounters{};
    var options = caller_options;
    if (options.counters == null) {
        // The per-rule attempt tallies feed the failure report's
        // "most-tried rules" line; they are only recorded under `collect`,
        // which stays off unless the caller asked for the detail string.
        local_counters.collect = options.status_detail;
        options.counters = &local_counters;
    }

    const setup_start = if (options.counters != null)
        timer.nanoTimestamp()
    else
        0;
    // A single per-call work arena backs the ENTIRE search: the fixture (the
    // whole compiled environment — parser, env, registry, rule catalog, the
    // view/fresh/freshen maps, sort vars), the theorem context and its clones,
    // the label/checked/scratch/cache scaffolding, and every transient
    // allocation the search machinery makes through `context.allocator` below.
    // None of it escapes — the returned `SourceSuggestions` is deep-copied onto
    // the caller `allocator` at each real return site (`copyOutSuggestions`),
    // and the empty returns own no memory. Because the theorem interner and the
    // def_ops contexts all draw from `work`, the `internAppOwned` ownership
    // contract (shared allocator == interner allocator) holds uniformly.
    // Registered first so LIFO frees it LAST, after the `deinit` calls below
    // that still read through arena-backed structures. Without this, every call
    // (LSP code action, bench frontier run) retained its transient search state;
    // the depth corpus grew to ~20 GiB live across theorems — a diffuse per-call
    // leak spread across the parser, diagnostics, def_ops, and inference layers,
    // not any one site.
    var work_arena = std.heap.ArenaAllocator.init(allocator);
    defer work_arena.deinit();
    const work = work_arena.allocator();

    const target = try findSearchLine(
        work,
        proof_src,
        offset,
        options.apply_at_offset,
    ) orelse {
        return .{ .allocator = allocator, .items = &.{} };
    };
    var fixture = try fixtureForSourceTarget(
        work,
        mm0_src,
        proof_src,
        target,
    );
    var sink = DiagnosticSink.init(mm0_src, proof_src);
    var compiler = CompilerContext.init(mm0_src, proof_src, .none, &sink);

    var theorem = TheoremContext.init(work);
    defer theorem.deinit();
    try theorem.seedAssertion(fixture.assertion);
    var theorem_vars = try Check.buildTheoremVarMap(
        work,
        fixture.assertion,
    );
    defer theorem_vars.deinit();

    var labels = LabelIndexMap.init(work);
    defer labels.deinit();
    var checked = std.ArrayListUnmanaged(CheckedLine){};
    defer {
        CheckedIr.deinitLines(work, checked.items);
        checked.deinit(work);
    }
    var diag_scratch = CompilerDiag.Scratch.init(work);
    defer diag_scratch.deinit();
    var cache = Inference.RuleUnifyCache.init(work);
    defer cache.deinit();

    for (target.block.lines[0..target.line_index]) |line| {
        if (ProofScript.applicationHasSearchPlaceholder(line.application)) {
            break;
        }
        var result = runSearchLine(
            work,
            &compiler,
            &fixture,
            &labels,
            &checked,
            &theorem,
            &theorem_vars,
            &diag_scratch,
            &cache,
            line,
            true,
        ) catch return .{ .allocator = allocator, .items = &.{} };
        defer result.deinit();
        labels.put(line.label, result.line_idx) catch return error.OutOfMemory;
    }

    const context = Context{
        .allocator = work,
        .parser = &fixture.parser,
        .env = &fixture.env,
        .registry = &fixture.registry,
        .rule_catalog = &fixture.rule_catalog,
        .fresh_bindings = &fixture.fresh_bindings,
        .freshen_bindings = &fixture.freshen_bindings,
        .views = &fixture.views,
        .sort_vars = &fixture.sort_vars,
        .assertion = fixture.assertion,
        .labels = &labels,
        .checked = &checked,
        .diag_scratch = &diag_scratch,
        .rule_unify_cache = &cache,
        .available_rule_count = fixture.available_rule_count,
    };
    var session = session_mod.SearchSession.init(&context, .{
        .counters = options.counters,
        .query_shape_cache = options.generate.shape_cache,
    });
    defer session.deinit();

    const target_line = target.block.lines[target.line_index];
    const line_goal = try parseGoal(
        &fixture,
        &theorem,
        &theorem_vars,
        target_line.assertion.text,
    );
    const target_application = applicationAtPath(
        target_line.application,
        target.path,
    ) orelse return .{ .allocator = allocator, .items = &.{} };

    // The catchment span for this target: any cursor offset within it resolves
    // to the same placeholder (mirrors `findSearchLine`'s match — the whole line
    // for a top-level placeholder, the nested application for an inline one).
    const match_span = if (target.path.len == 0)
        target_line.span
    else
        target_application.span;

    if (options.counters) |counters| {
        counters.cold_setup_ns += timer.elapsedSince(setup_start);
    }
    const search_start = if (options.counters != null)
        timer.nanoTimestamp()
    else
        0;

    var inline_expectation: ?InlineExpectedRef = null;
    defer if (inline_expectation) |*expected| expected.deinit();
    if (target.path.len != 0) {
        inline_expectation = try expectedGoalForInlineTarget(
            &compiler,
            &context,
            target_line,
            line_goal,
            target.path,
            &theorem,
            &theorem_vars,
        ) orelse {
            if (options.counters) |counters| {
                counters.warm_search_ns += timer.elapsedSince(search_start);
            }
            return .{
                .allocator = allocator,
                .items = &.{},
                .target_span = match_span,
            };
        };
    }

    const search_goal = if (inline_expectation) |expected|
        Goal{ .implicit_whole_conclusion = expected.query }
    else
        line_goal;

    const is_exact = !options.apply_at_offset and
        std.mem.eql(u8, target_application.rule_name, "exact?");
    const is_auto = !options.apply_at_offset and
        std.mem.eql(u8, target_application.rule_name, "auto?");
    const is_conversion = !options.apply_at_offset and
        std.mem.eql(u8, target_application.rule_name, "conversion?");
    // `auto?` shares `exact?`'s direct-search dispatch; generation is layered on
    // top of the direct results below.
    const is_exact_like = is_exact or is_auto;

    // Per-call tunables (`auto? (depth: 8)`): overlay the placeholder's valid
    // parameters onto this one call's generation options. Invalid entries are
    // skipped here — the LSP's placeholder diagnostics report them — so a
    // typo never silently changes or blocks the search.
    if (is_auto) {
        tunables.applySearchParams(
            &options.generate,
            target_application.search_params,
        );
    }

    if (inline_expectation) |expected| {
        if (expected.has_placeholder and !is_exact_like) {
            if (options.counters) |counters| {
                counters.warm_search_ns += timer.elapsedSince(search_start);
            }
            return .{
                .allocator = allocator,
                .items = &.{},
                .target_span = match_span,
            };
        }
    }

    if (is_conversion) {
        // Top-level lines only: an inline conversion has no line of its own
        // in front of which the chain could be spliced.
        if (target.path.len != 0) {
            if (options.counters) |counters| {
                counters.warm_search_ns += timer.elapsedSince(search_start);
            }
            return .{
                .allocator = allocator,
                .items = &.{},
                .target_span = match_span,
            };
        }
        var conv_options = ConversionSearch.Options{};
        tunables.applyConversionParams(
            &conv_options,
            target_application.search_params,
        );
        const goal_expr: ?ExprId = switch (line_goal) {
            .concrete => |expr| expr,
            else => null,
        };
        var conv_result = ConversionSearch.Result{};
        if (goal_expr) |expr| {
            conv_result = try ConversionSearch.run(
                work,
                &context,
                &theorem,
                &theorem_vars,
                expr,
                proof_src,
                target.block.lines,
                target_line,
                conv_options,
            );
        }
        var conv_suggestions = SourceSuggestions{
            .allocator = work,
            .items = &.{},
            .target_span = match_span,
        };
        if (conv_result.replacement) |replacement| {
            const items = try work.alloc(SourceSuggestion, 1);
            items[0] = .{
                .title = try std.fmt.allocPrint(
                    work,
                    "conversion from {s}",
                    .{conv_result.via.?},
                ),
                .replacement = replacement,
                .replace_span = target_line.span,
            };
            conv_suggestions.items = items;
            conv_suggestions.status = .found;
        } else {
            conv_suggestions.status = switch (conv_result.stats.outcome) {
                // A saturated miss is a forced negative ONLY without
                // `@compute` rules: the directed fold reduces each redex
                // once in one order, so its fixpoint never certifies that
                // no chain exists.
                .saturated => if (conv_result.compute_rule_count != 0)
                    types.SearchStatus.budget_exhausted
                else
                    types.SearchStatus.miss,
                .iteration_capped,
                .node_capped,
                .budget_fixpoint,
                => .budget_exhausted,
            };
            if (options.status_detail) {
                conv_suggestions.status_detail = try buildConversionDetail(
                    work,
                    conv_result,
                    conv_options,
                    goal_expr != null,
                );
            }
        }
        if (options.counters) |counters| {
            counters.warm_search_ns += timer.elapsedSince(search_start);
        }
        return try copyOutSuggestions(allocator, conv_suggestions);
    }

    if (is_exact_like) {
        // Single-proof modes (`exact?`/`auto?`) honor the tighter
        // `exact_result_limit` when set, so the editor gets one best proof and
        // `exact?` can short-circuit recursive generation. `apply?` (below) keeps
        // the full `max_results`, since it lists candidate rules.
        var exact_options = options;
        if (options.exact_result_limit) |limit| {
            exact_options.max_results = @min(options.max_results, limit);
        }
        var suggestions = if (target.path.len == 0)
            try topLevelExactSuggestions(
                work,
                &compiler,
                &session,
                search_goal,
                target_application.span,
                target_application.rule_name,
                &theorem,
                &theorem_vars,
                exact_options,
            )
        else
            try inlineExactSuggestions(
                work,
                &compiler,
                &context,
                &session,
                target_line,
                line_goal,
                search_goal,
                target.path,
                inline_expectation,
                &theorem,
                &theorem_vars,
                is_auto,
                exact_options,
            );
        // `auto?` appends bounded recursive generation to the direct
        // results. Top-level concrete goals only in Step 1.
        if (is_auto and options.generate.enabled and target.path.len == 0) {
            suggestions = try appendGeneratedSuggestions(
                work,
                &compiler,
                &session,
                search_goal,
                target_application.span,
                &theorem,
                &theorem_vars,
                exact_options,
                suggestions,
            );
        }
        if (options.counters) |counters| {
            counters.warm_search_ns += timer.elapsedSince(search_start);
        }
        suggestions.target_span = match_span;
        suggestions.status = searchStatus(
            suggestions.items.len,
            options.counters.?,
        );
        if (options.status_detail and suggestions.status != .found) {
            suggestions.status_detail = try buildStatusDetail(
                work,
                target_application.rule_name,
                is_auto,
                suggestions.status,
                options.counters.?,
                options.generate,
            );
        }
        // `suggestions` lives on the work arena; hand the caller an owned copy.
        return try copyOutSuggestions(allocator, suggestions);
    }

    var results = try applyWithSession(
        &compiler,
        &session,
        search_goal,
        &theorem,
        &theorem_vars,
        .{
            .max_results = options.max_results,
            .counters = options.counters,
        },
    );
    defer results.deinit();
    if (options.counters) |counters| {
        counters.warm_search_ns += timer.elapsedSince(search_start);
    }
    var apply_suggestions = try renderApplySourceSuggestions(
        work,
        results.candidates,
        target_application.span,
        if (options.apply_at_offset)
            target_application.rule_name
        else
            "apply?",
    );
    apply_suggestions.target_span = match_span;
    apply_suggestions.status = searchStatus(
        apply_suggestions.items.len,
        options.counters.?,
    );
    if (options.status_detail and apply_suggestions.status != .found) {
        apply_suggestions.status_detail = try buildStatusDetail(
            work,
            if (options.apply_at_offset)
                target_application.rule_name
            else
                "apply?",
            false,
            apply_suggestions.status,
            options.counters.?,
            options.generate,
        );
    }
    // `apply_suggestions` lives on the work arena; hand the caller an owned copy.
    return try copyOutSuggestions(allocator, apply_suggestions);
}

/// Failure report for a `conversion?` search. A saturated egraph with no
/// convertible pool formula is a forced negative (no chain of the enrolled
/// rules exists, period); a capped run gets the concrete next parameter.
fn buildConversionDetail(
    allocator: std.mem.Allocator,
    result: ConversionSearch.Result,
    conv_options: ConversionSearch.Options,
    goal_concrete: bool,
) !?[]const u8 {
    var buf: std.ArrayListUnmanaged(u8) = .{};
    errdefer buf.deinit(allocator);
    const w = buf.writer(allocator);
    if (!goal_concrete) {
        try w.writeAll(
            "conversion? needs a concrete goal formula (no holes).",
        );
    } else if (result.rule_count == 0 and
        result.pool_equations == 0 and
        result.ac_heads == 0)
    {
        try w.writeAll(
            "no @conversion rules are enrolled — annotate theorems " ++
                "concluding rel(lhs, rhs) with '@conversion ltr|rtl|both' " ++
                "to give the egraph rewrites to saturate.",
        );
    } else if (result.convertible_unlowered) {
        if (result.lower_capped) {
            try w.writeAll(
                "a reference convertible to this goal was found, but the " ++
                    "extracted proof chain outgrew the lowering's emission " ++
                    "cap — the conversion is proven, its re-treeing proof " ++
                    "is too large to write out.",
            );
        } else {
            try w.writeAll(
                "a reference convertible to this goal was found, but a proof " ++
                    "chain could not be extracted from it (missing @congr " ++
                    "coverage or a missing @relation transport are the usual " ++
                    "causes).",
            );
        }
    } else switch (result.stats.outcome) {
        .saturated => {
            try w.print(
                "the egraph saturated ({d} e-classes, {d} e-nodes, {d} " ++
                    "iterations, {d} rule orientations, {d} local equations): " ++
                    "no chain of the enrolled @conversion rewrites connects " ++
                    "this goal to any of the {d} pool references.",
                .{
                    result.classes,
                    result.nodes,
                    result.stats.iterations,
                    result.rule_count,
                    result.pool_equations,
                    result.pool_size,
                },
            );
            if (result.compute_rule_count != 0) {
                try w.print(
                    " {d} @compute orientations folded by the directed " ++
                        "scheduler, which reduces each redex once in " ++
                        "declaration order — alternative reduction " ++
                        "orders were never explored, so this is NOT a " ++
                        "forced negative.",
                    .{result.compute_rule_count},
                );
            }
            if (result.stats.ac_match_capped != 0) {
                try w.writeAll(
                    " Some rule matches hit their enumeration budget, " ++
                        "so this is NOT a forced negative: assignments " ++
                        "were left untried.",
                );
            }
            if (result.stats.ac_cyclic_dropped != 0) {
                try w.writeAll(
                    " Some self-containing classes (idempotence/" ++
                        "absorption unions) were kept atomic during AC " ++
                        "canonicalization, so this is NOT a forced " ++
                        "negative: a few congruence merges were forfeited.",
                );
            }
        },
        .iteration_capped => try w.print(
            "the egraph hit its iteration cap ({d}) before saturating " ++
                "({d} e-nodes so far). A conversion may still exist — try " ++
                "'conversion? (iters: {d})'.",
            .{
                conv_options.max_iterations,
                result.nodes,
                @min(
                    conv_options.max_iterations * 2,
                    tunables.max_iters_value,
                ),
            },
        ),
        .node_capped => try w.print(
            "the egraph hit its e-node cap ({d}) after {d} iterations. " ++
                "A conversion may still exist — try 'conversion? " ++
                "(nodes: {d})'.",
            .{
                conv_options.max_nodes,
                result.stats.iterations,
                @min(conv_options.max_nodes * 2, tunables.max_nodes_value),
            },
        ),
        .budget_fixpoint => try w.print(
            "the egraph stopped after {d} iterations at a budget-limited " ++
                "fixpoint ({d} e-nodes): rule matching kept hitting its " ++
                "enumeration budget while no further iteration could make " ++
                "progress, so raising 'iters:' will not help. A conversion " ++
                "may still exist beyond the enumeration budget — this is " ++
                "NOT a forced negative. Dense clusters of interacting " ++
                "equations in the hypothesis pool are the usual cause.",
            .{
                result.stats.iterations,
                result.nodes,
            },
        ),
    }
    if (goal_concrete and result.stats.dep_deferred != 0) {
        try w.writeAll(
            " Some rule matches were refused because no instantiation " ++
                "could satisfy the rule's variable-dependency " ++
                "constraints; if a rewrite you expected did not fire, " ++
                "check the binders' declared dependencies.",
        );
    }
    if (goal_concrete and result.partial_ac_heads != 0) {
        try w.print(
            " {d} operator(s) hold an assoc/comm certificate without the " ++
                "partner law or @congr coverage; their certificates enroll " ++
                "as ordinary both-way rewrites instead of absorbing.",
            .{result.partial_ac_heads},
        );
    }
    return try buf.toOwnedSlice(allocator);
}

/// Derive the user-facing outcome of a completed search: found beats
/// everything; an empty result is a definitive miss unless one of the
/// counters' exhaustion flags shows a budget truncated the search first.
fn searchStatus(
    items_len: usize,
    counters: *const types.SearchCounters,
) types.SearchStatus {
    if (items_len > 0) return .found;
    if (counters.gen_budget_exhausted or
        counters.recursive_budget_exhausted or
        counters.forward_saturation_exhausted)
    {
        return .budget_exhausted;
    }
    return .miss;
}

const ladder_phase_names = [_][]const u8{
    "non-splitting generation",
    "context splitting",
    "witness invention",
    "principal retention",
    "constrained modus ponens",
};

/// Elaborate a failed search into the user-facing detail string: which bound
/// truncated it (per-call work budget vs. per-phase fuel vs. forward
/// saturation), how far the generation ladder got, how many candidates were
/// validated vs. accepted, and — since every number is actionable — the
/// concrete per-call parameter to try next (`auto? (depth: 8)`). Built on the
/// caller's allocator (the per-call work arena; `copyOutSuggestions` deep-
/// copies it out). Purely observational: reads the same counters the search
/// already fills, never influences it.
fn buildStatusDetail(
    allocator: std.mem.Allocator,
    keyword: []const u8,
    is_auto: bool,
    status: types.SearchStatus,
    counters: *const types.SearchCounters,
    gen: types.GenerateOptions,
) !?[]const u8 {
    var buf = std.ArrayListUnmanaged(u8){};
    errdefer buf.deinit(allocator);
    const w = buf.writer(allocator);

    const validated = counters.full_try_candidate_calls;
    const accepted = counters.accepted_candidates;
    const rejected = counters.rejected_candidates_after_validation;
    // The ladder records the cell it is in as each pass starts, so a nonzero
    // phase means recursive generation actually ran (an `exact?`, an open
    // inline slot, or a disabled generation permit leaves it 0).
    const generation_ran = is_auto and counters.gen_last_phase != 0;

    switch (status) {
        .found => return null,
        .miss => {
            if (generation_ran) {
                try w.print(
                    "no proof found within depth {d}. The search space was " ++
                        "exhausted ({d} applications validated: {d} " ++
                        "accepted, {d} rejected), so only a deeper proof " ++
                        "can exist — try '{s} (depth: {d})'.",
                    .{
                        gen.max_depth,
                        validated,
                        accepted,
                        rejected,
                        keyword,
                        @min(gen.max_depth + 2, tunables.max_depth_value),
                    },
                );
            } else {
                try w.print(
                    "no rule application closes this goal from existing " ++
                        "references ({d} candidate rules considered " ++
                        "against a pool of {d} references).",
                    .{
                        counters.candidate_rules_before_conclusion_validation,
                        counters.ref_pool_size,
                    },
                );
                if (std.mem.eql(u8, keyword, "exact?")) {
                    try w.writeAll(
                        " auto? can additionally synthesize sub-proofs.",
                    );
                }
            }
        },
        .budget_exhausted => {
            if (counters.gen_budget_exhausted) {
                // Whole-call weighted-tick cap: report consumption in the
                // `budget` parameter's unit (billions of ticks ≈ seconds of
                // calibrated work) and suggest roughly doubling it.
                const limit = gen.global_budget orelse 0;
                const limit_units = std.math.divCeil(
                    u64,
                    limit,
                    tunables.ticks_per_budget_unit,
                ) catch unreachable;
                try w.print(
                    "stopped by the per-call work budget (~{d}s of work) " ++
                        "during {s} at depth {d} of {d}; {d} applications " ++
                        "validated ({d} accepted). A proof may still " ++
                        "exist — try '{s} (budget: {d})', or 'budget: 0' " ++
                        "for no cap.",
                    .{
                        limit_units,
                        ladderPhaseName(counters.gen_last_phase),
                        counters.gen_last_depth,
                        gen.max_depth,
                        validated,
                        accepted,
                        keyword,
                        std.math.clamp(
                            limit_units * 2,
                            1,
                            tunables.max_budget_value,
                        ),
                    },
                );
            } else if (counters.recursive_budget_exhausted) {
                try w.print(
                    "a search phase ran out of fuel ({d} candidate " ++
                        "validations per phase) during {s} at depth {d} " ++
                        "of {d}. A proof may still exist — try " ++
                        "'{s} (fuel: {d})'.",
                    .{
                        gen.fuel,
                        ladderPhaseName(counters.gen_last_phase),
                        counters.gen_last_depth,
                        gen.max_depth,
                        keyword,
                        @min(gen.fuel * 2, tunables.max_fuel_value),
                    },
                );
            } else {
                try w.writeAll(
                    "forward saturation stopped at its bounds before " ++
                        "reaching a fixpoint, so the derived-fact pool is " ++
                        "incomplete and a proof may still exist.",
                );
            }
        },
    }

    // Where the work went: the most-tried rules with their accept counts
    // (attempts ≠ accepts — a rule tried 500 times with 0 accepted is a
    // reject-flood, the usual budget sink). Only recorded under `collect`.
    try appendTopRuleAttempts(w, counters);

    return try buf.toOwnedSlice(allocator);
}

fn ladderPhaseName(phase_1based: usize) []const u8 {
    if (phase_1based == 0 or phase_1based > ladder_phase_names.len) {
        return "generation";
    }
    return ladder_phase_names[phase_1based - 1];
}

/// Append a "Most-tried rules: ..." sentence listing the top 3 rules by
/// validation attempts. Silent when the per-rule tallies were not collected
/// or nothing was attempted.
fn appendTopRuleAttempts(
    w: anytype,
    counters: *const types.SearchCounters,
) !void {
    const len = counters.rule_attempt_diagnostics_len;
    if (len == 0) return;
    const tallies = counters.rule_attempt_diagnostics[0..len];

    // Insertion-select the top 3 indices by attempts.
    var top: [3]usize = undefined;
    var top_len: usize = 0;
    for (0..len) |idx| {
        var insert = idx;
        for (top[0..top_len]) |*held| {
            if (tallies[insert].attempts > tallies[held.*].attempts) {
                std.mem.swap(usize, &insert, held);
            }
        }
        if (top_len < top.len) {
            top[top_len] = insert;
            top_len += 1;
        }
    }

    var wrote_header = false;
    for (top[0..top_len]) |idx| {
        const tally = tallies[idx];
        if (tally.attempts == 0) continue;
        if (!wrote_header) {
            try w.writeAll(" Most-tried rules: ");
            wrote_header = true;
        } else {
            try w.writeAll(", ");
        }
        try w.print(
            "{s} ({d} tried, {d} accepted)",
            .{ tally.rule_name.slice(), tally.attempts, tally.accepted },
        );
    }
    if (wrote_header) try w.writeAll(".");
}

const InlineExpectedRef = struct {
    allocator: std.mem.Allocator,
    rule_id: u32,
    child_index: usize,
    bindings: []const ?ExprId,
    expected: ?ExprId,
    query: ExprId,
    has_placeholder: bool,

    fn deinit(self: *InlineExpectedRef) void {
        self.allocator.free(self.bindings);
        self.* = undefined;
    }
};

/// One search placeholder occurrence in a proof source, as enumerated by
/// `searchPlaceholders`. Spans index into the proof source; nothing borrows
/// the parse.
pub const SearchPlaceholder = struct {
    pub const Kind = enum {
        exact,
        apply,
        auto,
        conversion,

        pub fn keyword(self: Kind) []const u8 {
            return switch (self) {
                .exact => "exact?",
                .apply => "apply?",
                .auto => "auto?",
                .conversion => "conversion?",
            };
        }

        /// The parameter set this placeholder accepts (per-keyword
        /// validation in `tunables.validateSearchParams`).
        pub fn paramContext(self: Kind) tunables.ParamContext {
            return switch (self) {
                .exact => .exact,
                .apply => .apply,
                .auto => .auto,
                .conversion => .conversion,
            };
        }
    };

    kind: Kind,
    /// The placeholder application's span (keyword through refs) — the
    /// natural diagnostic underline. Falls inside the catchment `target_span`
    /// a search at this placeholder reports (the whole line for a top-level
    /// placeholder, this same span for a nested one).
    span: Span,
    /// The placeholder's `name: INTEGER` parameters, verbatim from the parse
    /// (name strings are slices of the proof source, not the parse arena).
    /// The LSP validates these per placeholder (`tunables.validateSearchParams`)
    /// to diagnose typos without running a search.
    params: []const ProofScript.SearchParam = &.{},
};

/// Enumerate every search placeholder (`exact?`/`apply?`/`auto?`) in
/// `proof_src`, top-level and nested, in source order. Used by the LSP to
/// publish a status diagnostic per placeholder. A parse error ends the scan
/// early (the compiler's own diagnostics already cover malformed source);
/// whatever was collected before it is returned. The result is allocated on
/// `allocator` (including each placeholder's non-empty `params` array);
/// parser transients are torn down before returning.
pub fn searchPlaceholders(
    allocator: std.mem.Allocator,
    proof_src: []const u8,
) ![]SearchPlaceholder {
    var parse_arena = std.heap.ArenaAllocator.init(allocator);
    defer parse_arena.deinit();
    var out = std.ArrayListUnmanaged(SearchPlaceholder){};
    errdefer out.deinit(allocator);
    var parser = ProofParser.init(parse_arena.allocator(), proof_src);
    while (parser.nextBlock() catch null) |block| {
        for (block.lines) |line| {
            try collectSearchPlaceholders(allocator, &out, line.application);
        }
    }
    return try out.toOwnedSlice(allocator);
}

fn collectSearchPlaceholders(
    allocator: std.mem.Allocator,
    out: *std.ArrayListUnmanaged(SearchPlaceholder),
    application: RuleApplication,
) !void {
    // Gate on the canonical predicate so this can't drift from what the
    // checker/search treat as a placeholder; the kind mapping below only
    // discriminates names that already passed it.
    if (ProofScript.isSearchPlaceholderRuleName(application.rule_name)) {
        const kind: SearchPlaceholder.Kind =
            if (std.mem.eql(u8, application.rule_name, "exact?"))
                .exact
            else if (std.mem.eql(u8, application.rule_name, "apply?"))
                .apply
            else if (std.mem.eql(u8, application.rule_name, "conversion?"))
                .conversion
            else
                .auto;
        // The param structs hold only source slices and values, but the
        // ARRAY lives on the parse arena — copy it onto the caller's
        // allocator alongside the placeholder itself (empty stays a literal
        // so param-free placeholders allocate nothing extra).
        const params: []const ProofScript.SearchParam =
            if (application.search_params.len == 0)
                &.{}
            else
                try allocator.dupe(
                    ProofScript.SearchParam,
                    application.search_params,
                );
        try out.append(allocator, .{
            .kind = kind,
            .span = application.span,
            .params = params,
        });
    }
    for (application.refs) |ref| switch (ref) {
        .application => |child| try collectSearchPlaceholders(
            allocator,
            out,
            child,
        ),
        .hyp, .line => {},
    };
}

fn findSearchLine(
    allocator: std.mem.Allocator,
    proof_src: []const u8,
    offset: usize,
    apply_at_offset: bool,
) !?SourceTarget {
    var parser = ProofParser.init(allocator, proof_src);
    while (try parser.nextBlock()) |block| {
        for (block.lines, 0..) |line, line_index| {
            if (apply_at_offset and spanContains(
                line.application.rule_span,
                offset,
            )) {
                return .{
                    .block = block,
                    .line_index = line_index,
                    .path = &.{},
                };
            }
            if (ProofScript.isSearchPlaceholderRuleName(
                line.application.rule_name,
            )) {
                const span = line.application.ruleApplicationSpan();
                if (offset >= span.start and offset <= span.end) {
                    return .{
                        .block = block,
                        .line_index = line_index,
                        .path = &.{},
                    };
                }
                if (offset >= line.span.start and offset <= line.span.end) {
                    return .{
                        .block = block,
                        .line_index = line_index,
                        .path = &.{},
                    };
                }
            }
            if (try findNestedSearchPath(
                allocator,
                line.application,
                offset,
                apply_at_offset,
            )) |path| {
                return .{
                    .block = block,
                    .line_index = line_index,
                    .path = path,
                };
            }
        }
    }
    return null;
}

fn findNestedSearchPath(
    allocator: std.mem.Allocator,
    application: RuleApplication,
    offset: usize,
    apply_at_offset: bool,
) !?[]const usize {
    for (application.refs, 0..) |ref, idx| {
        const child = switch (ref) {
            .application => |app| app,
            .hyp, .line => continue,
        };
        if (!spanContains(child.span, offset)) continue;
        if ((apply_at_offset and spanContains(child.rule_span, offset)) or
            (!apply_at_offset and
                ProofScript.isSearchPlaceholderRuleName(child.rule_name)))
        {
            const path = try allocator.alloc(usize, 1);
            path[0] = idx;
            return path;
        }
        if (try findNestedSearchPath(
            allocator,
            child,
            offset,
            apply_at_offset,
        )) |suffix| {
            const path = try allocator.alloc(usize, suffix.len + 1);
            path[0] = idx;
            @memcpy(path[1..], suffix);
            return path;
        }
    }
    return null;
}

fn spanContains(span: Span, offset: usize) bool {
    return offset >= span.start and offset <= span.end;
}

fn applicationAtPath(
    root: RuleApplication,
    path: []const usize,
) ?RuleApplication {
    var current = root;
    for (path) |idx| {
        if (idx >= current.refs.len) return null;
        current = switch (current.refs[idx]) {
            .application => |app| app,
            .hyp, .line => return null,
        };
    }
    return current;
}

fn topLevelExactSuggestions(
    allocator: std.mem.Allocator,
    compiler: *CompilerContext,
    session: *session_mod.SearchSession,
    goal: Goal,
    replace_span: Span,
    keyword: []const u8,
    theorem: *const TheoremContext,
    theorem_vars: *const NameExprMap,
    options: SourceSuggestionOptions,
) !SourceSuggestions {
    var results = try exactWithSession(
        compiler,
        session,
        goal,
        theorem,
        theorem_vars,
        .{
            .max_results = options.max_results,
            .counters = options.counters,
        },
    );
    defer results.deinit();
    return try renderExactSourceSuggestions(
        allocator,
        results.candidates,
        replace_span,
        keyword,
    );
}

/// Run bounded recursive generation for an `auto?` goal and merge the resulting
/// proof-tree suggestions into the direct-search results, deduplicating by
/// replacement text and respecting `max_results`. Takes ownership of `existing`.
fn appendGeneratedSuggestions(
    allocator: std.mem.Allocator,
    compiler: *CompilerContext,
    session: *session_mod.SearchSession,
    goal: Goal,
    replace_span: Span,
    theorem: *const TheoremContext,
    theorem_vars: *const NameExprMap,
    options: SourceSuggestionOptions,
    existing: SourceSuggestions,
) !SourceSuggestions {
    var items = std.ArrayListUnmanaged(SourceSuggestion){};
    errdefer deinitSourceSuggestionItems(allocator, items.items);
    // Seed with the already-rendered direct suggestions. `existing` and its
    // strings live on the per-call work arena (as does everything appended
    // below), so there is no ownership hand-off to manage: the caller receives a
    // deep copy at the return boundary, and the arena reclaims the rest.
    try items.appendSlice(allocator, existing.items);

    if (items.items.len >= options.max_results) {
        return .{ .allocator = allocator, .items = try items.toOwnedSlice(allocator) };
    }

    var gen_options = options.generate;
    gen_options.max_results = options.max_results - items.items.len;
    var generated = try generate_mod.generateTopLevel(
        compiler,
        session,
        goal,
        theorem,
        theorem_vars,
        gen_options,
    );
    defer generated.deinit();

    for (generated.applications) |app| {
        if (items.items.len >= options.max_results) break;
        const replacement = try renderApplication(
            allocator,
            app.rule_name,
            app.arg_bindings,
            app.refs,
        );
        var duplicate = false;
        for (items.items) |item| {
            if (std.mem.eql(u8, item.replacement, replacement)) {
                duplicate = true;
                break;
            }
        }
        if (duplicate) {
            allocator.free(replacement);
            continue;
        }
        errdefer allocator.free(replacement);
        const title = try std.fmt.allocPrint(
            allocator,
            "Replace auto? with {s}",
            .{replacement},
        );
        errdefer allocator.free(title);
        try items.append(allocator, .{
            .title = title,
            .replacement = replacement,
            .replace_span = replace_span,
        });
    }
    return .{ .allocator = allocator, .items = try items.toOwnedSlice(allocator) };
}

fn inlineExactSuggestions(
    allocator: std.mem.Allocator,
    compiler: *CompilerContext,
    context: *const Context,
    session: *session_mod.SearchSession,
    line: ProofScript.ProofLine,
    line_goal: Goal,
    search_goal: Goal,
    path: []const usize,
    inline_expectation: ?InlineExpectedRef,
    theorem: *const TheoremContext,
    theorem_vars: *const NameExprMap,
    is_auto: bool,
    options: SourceSuggestionOptions,
) !SourceSuggestions {
    var items = std.ArrayListUnmanaged(SourceSuggestion){};
    errdefer deinitSourceSuggestionItems(allocator, items.items);

    const max_results = options.max_results;
    if (inline_expectation) |expected| {
        try appendDirectRefSuggestions(
            allocator,
            compiler,
            context,
            session,
            line,
            line_goal,
            path,
            expected,
            theorem,
            theorem_vars,
            &items,
            max_results,
            options.counters,
        );
    }

    if (items.items.len < max_results) {
        const remaining = max_results - items.items.len;
        var results = try exactWithSession(
            compiler,
            session,
            search_goal,
            theorem,
            theorem_vars,
            .{
                .max_results = remaining,
                .counters = options.counters,
            },
        );
        defer results.deinit();
        try appendInlineExactApplications(
            allocator,
            compiler,
            context,
            line,
            line_goal,
            path,
            theorem,
            theorem_vars,
            results.candidates,
            &items,
            max_results,
        );
    }

    // `auto?` in a slot position layers bounded recursive generation on top of
    // the direct results, exactly as the top-level path does — but only when the
    // slot goal is fully concrete. An open slot goal (an undetermined rule
    // argument) needs `generateTopLevel` to accept a goal carrying `.existential`
    // metas, which it does not yet (the deferred holey-goal path); until then an
    // open inline slot stays exact-only. See
    // docs/design_notes/inline_auto_open_slot_existential_gap.md.
    if (is_auto and options.generate.enabled and items.items.len < max_results) {
        if (inline_expectation) |expected| {
            if (!expected.has_placeholder) {
                try appendInlineGeneratedApplications(
                    allocator,
                    compiler,
                    context,
                    session,
                    line,
                    line_goal,
                    path,
                    expected,
                    theorem,
                    theorem_vars,
                    options,
                    &items,
                    max_results,
                );
            }
        }
    }

    return .{ .allocator = allocator, .items = try items.toOwnedSlice(allocator) };
}

fn renderExactSourceSuggestions(
    allocator: std.mem.Allocator,
    candidates: []const ExactCandidate,
    replace_span: Span,
    keyword: []const u8,
) !SourceSuggestions {
    var items = std.ArrayListUnmanaged(SourceSuggestion){};
    errdefer deinitSourceSuggestionItems(allocator, items.items);
    for (candidates) |candidate| {
        const replacement = try renderApplication(
            allocator,
            candidate.rule_name,
            candidate.application.arg_bindings,
            candidate.refs,
        );
        errdefer allocator.free(replacement);
        const title = try std.fmt.allocPrint(
            allocator,
            "Replace {s} with {s}",
            .{ keyword, replacement },
        );
        errdefer allocator.free(title);
        try items.append(allocator, .{
            .title = title,
            .replacement = replacement,
            .replace_span = replace_span,
        });
    }
    return .{ .allocator = allocator, .items = try items.toOwnedSlice(allocator) };
}

fn renderApplySourceSuggestions(
    allocator: std.mem.Allocator,
    candidates: []const ApplyCandidate,
    replace_span: Span,
    replaced_rule_name: []const u8,
) !SourceSuggestions {
    var items = std.ArrayListUnmanaged(SourceSuggestion){};
    errdefer deinitSourceSuggestionItems(allocator, items.items);
    for (candidates) |candidate| {
        const replacement = try renderApplyApplication(allocator, candidate);
        errdefer allocator.free(replacement);
        const title = try std.fmt.allocPrint(
            allocator,
            "Replace {s} with {s}",
            .{ replaced_rule_name, replacement },
        );
        errdefer allocator.free(title);
        try items.append(allocator, .{
            .title = title,
            .replacement = replacement,
            .replace_span = replace_span,
        });
    }
    return .{ .allocator = allocator, .items = try items.toOwnedSlice(allocator) };
}

fn appendDirectRefSuggestions(
    allocator: std.mem.Allocator,
    compiler: *CompilerContext,
    context: *const Context,
    session: *session_mod.SearchSession,
    line: ProofScript.ProofLine,
    line_goal: Goal,
    path: []const usize,
    expected: InlineExpectedRef,
    theorem: *const TheoremContext,
    theorem_vars: *const NameExprMap,
    items: *std.ArrayListUnmanaged(SourceSuggestion),
    max_results: usize,
    counters: ?*types.SearchCounters,
) !void {
    const ref_index = try session.getRefIndex(theorem, counters);
    const rule = &context.env.rules.items[expected.rule_id];
    if (expected.child_index >= rule.hyps.len) return;
    var lookup = try ref_index.lookupTemplate(
        theorem,
        rule.hyps[expected.child_index],
        rule.args,
        expected.bindings,
        counters,
    );
    defer lookup.deinit();
    for (lookup.indices) |pool_index| {
        if (items.items.len >= max_results) return;
        const ref = ref_index.entries[pool_index].ref orelse continue;
        const application = try applicationWithReplacedRef(
            allocator,
            line.application,
            path,
            ref,
        );
        if (!try validateReplacementApplication(
            compiler,
            context,
            application,
            line,
            line_goal,
            theorem,
            theorem_vars,
        )) continue;
        const replacement = try renderRefString(allocator, ref);
        errdefer allocator.free(replacement);
        const title = try std.fmt.allocPrint(
            allocator,
            "Replace exact? with {s}",
            .{replacement},
        );
        errdefer allocator.free(title);
        try items.append(allocator, .{
            .title = title,
            .replacement = replacement,
            .replace_span = (applicationAtPath(line.application, path) orelse
                line.application).span,
        });
    }
}

fn appendInlineExactApplications(
    allocator: std.mem.Allocator,
    compiler: *CompilerContext,
    context: *const Context,
    line: ProofScript.ProofLine,
    line_goal: Goal,
    path: []const usize,
    theorem: *const TheoremContext,
    theorem_vars: *const NameExprMap,
    candidates: []const ExactCandidate,
    items: *std.ArrayListUnmanaged(SourceSuggestion),
    max_results: usize,
) !void {
    for (candidates) |candidate| {
        if (items.items.len >= max_results) return;
        const replacement_ref = Ref{ .application = candidate.application };
        const application = try applicationWithReplacedRef(
            allocator,
            line.application,
            path,
            replacement_ref,
        );
        if (!try validateReplacementApplication(
            compiler,
            context,
            application,
            line,
            line_goal,
            theorem,
            theorem_vars,
        )) continue;
        const replacement = try renderApplication(
            allocator,
            candidate.rule_name,
            candidate.application.arg_bindings,
            candidate.refs,
        );
        errdefer allocator.free(replacement);
        const title = try std.fmt.allocPrint(
            allocator,
            "Replace exact? with {s}",
            .{replacement},
        );
        errdefer allocator.free(title);
        try items.append(allocator, .{
            .title = title,
            .replacement = replacement,
            .replace_span = (applicationAtPath(line.application, path) orelse
                line.application).span,
        });
    }
}

/// Run bounded recursive generation for a concrete inline `auto?` slot goal and
/// splice each resulting proof tree into the slot, keeping only those whose
/// reconstructed whole line still validates. Mirrors `appendGeneratedSuggestions`
/// (top-level) and `appendInlineExactApplications` (inline direct): the generated
/// proof is a single nested `RuleApplication`, so it drops into the slot the same
/// way a direct exact candidate does. Deduplicates against `items` by replacement
/// text and respects `max_results`.
fn appendInlineGeneratedApplications(
    allocator: std.mem.Allocator,
    compiler: *CompilerContext,
    context: *const Context,
    session: *session_mod.SearchSession,
    line: ProofScript.ProofLine,
    line_goal: Goal,
    path: []const usize,
    expected: InlineExpectedRef,
    theorem: *const TheoremContext,
    theorem_vars: *const NameExprMap,
    options: SourceSuggestionOptions,
    items: *std.ArrayListUnmanaged(SourceSuggestion),
    max_results: usize,
) !void {
    // Only concrete slot goals reach here (the caller gates on
    // `!expected.has_placeholder`); `generateTopLevel` accepts `.concrete` goals
    // exactly as it does for a top-level line.
    var gen_options = options.generate;
    gen_options.max_results = max_results - items.items.len;
    var generated = try generate_mod.generateTopLevel(
        compiler,
        session,
        Goal{ .concrete = expected.query },
        theorem,
        theorem_vars,
        gen_options,
    );
    defer generated.deinit();

    for (generated.applications) |app| {
        if (items.items.len >= max_results) return;
        const replacement_ref = Ref{ .application = app };
        const application = try applicationWithReplacedRef(
            allocator,
            line.application,
            path,
            replacement_ref,
        );
        if (!try validateReplacementApplication(
            compiler,
            context,
            application,
            line,
            line_goal,
            theorem,
            theorem_vars,
        )) continue;
        const replacement = try renderApplication(
            allocator,
            app.rule_name,
            app.arg_bindings,
            app.refs,
        );
        var duplicate = false;
        for (items.items) |item| {
            if (std.mem.eql(u8, item.replacement, replacement)) {
                duplicate = true;
                break;
            }
        }
        if (duplicate) {
            allocator.free(replacement);
            continue;
        }
        errdefer allocator.free(replacement);
        const title = try std.fmt.allocPrint(
            allocator,
            "Replace auto? with {s}",
            .{replacement},
        );
        errdefer allocator.free(title);
        try items.append(allocator, .{
            .title = title,
            .replacement = replacement,
            .replace_span = (applicationAtPath(line.application, path) orelse
                line.application).span,
        });
    }
}

fn renderRefString(
    allocator: std.mem.Allocator,
    ref: Ref,
) ![]const u8 {
    var buf = std.ArrayListUnmanaged(u8){};
    errdefer buf.deinit(allocator);
    try renderRef(allocator, &buf, ref);
    return try buf.toOwnedSlice(allocator);
}

fn validateReplacementApplication(
    compiler: *CompilerContext,
    context: *const Context,
    application: RuleApplication,
    line: ProofScript.ProofLine,
    line_goal: Goal,
    theorem: *const TheoremContext,
    theorem_vars: *const NameExprMap,
) !bool {
    // Non-commit probe: no pre-clones needed (see `tryCandidateProbe`), and
    // with `.borrowed` the attempt theorem is a COW clone based directly on
    // the caller's `theorem`, which outlives it.
    var attempt = candidate_mod.tryCandidateProbe(
        compiler,
        context,
        application,
        line_goal,
        theorem,
        theorem_vars,
        .{
            .line_label = line.label,
            .assertion_span = line.assertion.span,
            .diagnostic_span = line.span,
            .result_ownership = .borrowed,
        },
    ) catch |err| switch (err) {
        error.OutOfMemory => return err,
        else => return false,
    };
    defer attempt.deinit();
    CheckedIr.validateLinesCached(
        &attempt.theorem.?,
        attempt.checked_lines,
    ) catch {
        return false;
    };
    return true;
}

fn applicationWithReplacedRef(
    allocator: std.mem.Allocator,
    application: RuleApplication,
    path: []const usize,
    replacement: Ref,
) !RuleApplication {
    if (path.len == 0) return error.EmptyReplacementPath;
    if (path[0] >= application.refs.len) return error.BadReplacementPath;
    var copy = application;
    const refs = try allocator.dupe(Ref, application.refs);
    copy.refs = refs;
    if (path.len == 1) {
        refs[path[0]] = replacement;
        return copy;
    }
    const child = switch (refs[path[0]]) {
        .application => |app| app,
        .hyp, .line => return error.BadReplacementPath,
    };
    refs[path[0]] = .{ .application = try applicationWithReplacedRef(
        allocator,
        child,
        path[1..],
        replacement,
    ) };
    return copy;
}

fn expectedGoalForInlineTarget(
    compiler: *CompilerContext,
    context: *const Context,
    line: ProofScript.ProofLine,
    line_goal: Goal,
    path: []const usize,
    theorem: *TheoremContext,
    theorem_vars: *NameExprMap,
) !?InlineExpectedRef {
    if (path.len == 0) return null;
    var current_goal = line_goal;
    var prefix_len: usize = 0;
    while (prefix_len < path.len) : (prefix_len += 1) {
        const parent_path = path[0..prefix_len];
        const parent_app = applicationAtPath(line.application, parent_path) orelse
            return null;
        const child_index = path[prefix_len];
        var expected = try expectedRefForApplication(
            compiler,
            context,
            line,
            parent_app,
            current_goal,
            child_index,
            theorem,
            theorem_vars,
        ) orelse return null;
        if (prefix_len + 1 == path.len) return expected;
        const expected_expr = expected.expected orelse {
            expected.deinit();
            return null;
        };
        expected.deinit();
        current_goal = .{ .implicit_whole_conclusion = expected_expr };
    }
    return null;
}

/// True when binder `target_idx` occurs inside `template` as (a descendant of)
/// an operand of an `@acui` structural combiner — e.g. `G` or `H` within a
/// sequent context `G , H`. Such a binder is an ACUI split position, not a
/// value the goal alone determines, so the inline-slot goal must leave it open
/// rather than commit the probe's canonical split.
fn binderUnderAcuiCombiner(
    registry: *const RewriteRegistry,
    template: TemplateExpr,
    target_idx: usize,
    under_combiner: bool,
) bool {
    return switch (template) {
        .binder => |idx| under_combiner and idx == target_idx,
        .app => |app| blk: {
            const now_under = under_combiner or
                registry.hasStructuralCombiner(app.term_id);
            for (app.args) |arg| {
                if (binderUnderAcuiCombiner(registry, arg, target_idx, now_under))
                    break :blk true;
            }
            break :blk false;
        },
    };
}

fn expectedRefForApplication(
    compiler: *CompilerContext,
    context: *const Context,
    line: ProofScript.ProofLine,
    application: RuleApplication,
    goal: Goal,
    child_index: usize,
    theorem: *TheoremContext,
    theorem_vars: *NameExprMap,
) !?InlineExpectedRef {
    const rule_context = context.ruleApplyContext(context.allocator, context.checked);
    const app_line = Check.ApplicationLine{
        .label = line.label,
        .application = application,
        .assertion_span = application.span,
    };
    var probe = Check.probeExpectedRefsForApplication(
        compiler,
        &rule_context,
        application,
        goal.lineAssertion(),
        goal.expectedHint(),
        .{
            .theorem_name = context.assertion.name,
            .line_label = line.label,
            .span = application.span,
        },
        app_line,
        theorem,
        theorem_vars,
    ) catch |err| switch (err) {
        error.OutOfMemory => return err,
        else => return null,
    };
    defer probe.deinit();
    if (child_index >= probe.expected_refs.len) return null;

    const rule = &context.env.rules.items[probe.rule_id];
    if (child_index >= rule.hyps.len) return null;
    const bindings = try context.allocator.dupe(?ExprId, probe.bindings);
    errdefer context.allocator.free(bindings);
    if (goal.concreteOrHint()) |line_expr| {
        if (!theorem.matchTemplate(rule.concl, line_expr, bindings)) {
            extractHypPartialBindings(
                context,
                theorem,
                rule.concl,
                line_expr,
                bindings,
            );
        }
    }
    for (application.refs, 0..) |sibling, idx| {
        if (idx == child_index or idx >= rule.hyps.len) continue;
        const expr = refs_mod.sourceRefExpr(
            context,
            theorem,
            sibling,
        ) catch continue;
        if (!theorem.matchTemplate(rule.hyps[idx], expr, bindings)) {
            extractHypPartialBindings(
                context,
                theorem,
                rule.hyps[idx],
                expr,
                bindings,
            );
        }
    }
    for (bindings, 0..) |*binding, idx| {
        if (binding.* == null and idx < probe.contextual_bindings.len) {
            // Skip binders that sit as an operand of an `@acui` combiner in the
            // rule conclusion (e.g. a sequent context `G , H`). The probe's
            // inference commits one canonical ACUI split — the whole context to
            // the last operand, the unit `emp` to the earlier ones — so an
            // earlier-operand context binder would inherit `emp`, and a slot goal
            // resolved through it (`emp ⊢ q`) would match nothing in the pool.
            // Leaving it open lets the slot's own search pick the split that a
            // real reference supplies.
            if (binderUnderAcuiCombiner(
                context.registry,
                rule.concl,
                idx,
                false,
            )) continue;
            binding.* = probe.contextual_bindings[idx];
        }
    }
    const instantiated = try OpenTerms.instantiateTemplatePartial(
        theorem,
        rule.hyps[child_index],
        bindings,
    );
    var has_placeholder = false;
    const query = try instantiateTemplateQuery(
        context.allocator,
        theorem,
        rule.hyps[child_index],
        rule.args,
        bindings,
        &has_placeholder,
    );
    return .{
        .allocator = context.allocator,
        .rule_id = probe.rule_id,
        .child_index = child_index,
        .bindings = bindings,
        .expected = instantiated orelse probe.expected_refs[child_index],
        .query = query,
        .has_placeholder = has_placeholder,
    };
}

fn instantiateTemplateQuery(
    allocator: std.mem.Allocator,
    theorem: *TheoremContext,
    template: TemplateExpr,
    args: []const ParseRecovery.ArgInfo,
    bindings: []const ?ExprId,
    has_placeholder: *bool,
) !ExprId {
    const query_bindings = try allocator.dupe(?ExprId, bindings);
    defer allocator.free(query_bindings);
    return try instantiateTemplateQueryInner(
        theorem,
        template,
        args,
        query_bindings,
        has_placeholder,
    );
}

fn instantiateTemplateQueryInner(
    theorem: *TheoremContext,
    template: TemplateExpr,
    args: []const ParseRecovery.ArgInfo,
    bindings: []?ExprId,
    has_placeholder: *bool,
) !ExprId {
    return switch (template) {
        .binder => |idx| blk: {
            if (idx >= bindings.len or idx >= args.len) {
                return error.TemplateBinderOutOfRange;
            }
            if (bindings[idx]) |expr| break :blk expr;
            const placeholder = try theorem.addPlaceholderResolved(
                args[idx].sort_name,
            );
            bindings[idx] = placeholder;
            has_placeholder.* = true;
            break :blk placeholder;
        },
        .app => |app| blk: {
            const app_args = try theorem.allocator.alloc(
                ExprId,
                app.args.len,
            );
            errdefer theorem.allocator.free(app_args);
            for (app.args, 0..) |arg, idx| {
                app_args[idx] = try instantiateTemplateQueryInner(
                    theorem,
                    arg,
                    args,
                    bindings,
                    has_placeholder,
                );
            }
            break :blk try theorem.interner.internAppOwned(
                app.term_id,
                app_args,
            );
        },
    };
}

fn deinitSourceSuggestionItems(
    allocator: std.mem.Allocator,
    items: []SourceSuggestion,
) void {
    for (items) |item| {
        allocator.free(item.title);
        allocator.free(item.replacement);
    }
}

/// Deep-copy `src` (built on the per-call work arena) onto `allocator`, the
/// caller's allocator, so the result survives the arena's release. Only the
/// title/replacement strings are heap-owned; spans are values. On failure every
/// partial allocation is unwound so nothing leaks.
fn copyOutSuggestions(
    allocator: std.mem.Allocator,
    src: SourceSuggestions,
) !SourceSuggestions {
    const items = try allocator.alloc(SourceSuggestion, src.items.len);
    errdefer allocator.free(items);
    var filled: usize = 0;
    errdefer for (items[0..filled]) |item| {
        allocator.free(item.title);
        allocator.free(item.replacement);
    };
    for (src.items, 0..) |item, idx| {
        const title = try allocator.dupe(u8, item.title);
        errdefer allocator.free(title);
        const replacement = try allocator.dupe(u8, item.replacement);
        items[idx] = .{
            .title = title,
            .replacement = replacement,
            .replace_span = item.replace_span,
        };
        filled = idx + 1;
    }
    const status_detail: ?[]const u8 = if (src.status_detail) |detail|
        try allocator.dupe(u8, detail)
    else
        null;
    return .{
        .allocator = allocator,
        .items = items,
        .target_span = src.target_span,
        .status = src.status,
        .status_detail = status_detail,
    };
}

fn renderApplyApplication(
    allocator: std.mem.Allocator,
    candidate: ApplyCandidate,
) ![]const u8 {
    if (candidate.unresolved_hyps.len == 0) {
        return try allocator.dupe(u8, candidate.rule_name);
    }
    var buf = std.ArrayListUnmanaged(u8){};
    errdefer buf.deinit(allocator);
    try buf.writer(allocator).print("{s} [", .{candidate.rule_name});
    for (candidate.unresolved_hyps, 0..) |_, idx| {
        if (idx != 0) try buf.appendSlice(allocator, ", ");
        try buf.writer(allocator).print("ref{}", .{idx + 1});
    }
    try buf.append(allocator, ']');
    return try buf.toOwnedSlice(allocator);
}

fn renderApplication(
    allocator: std.mem.Allocator,
    rule_name: []const u8,
    arg_bindings: []const ProofScript.ArgBinding,
    refs: []const ProofScript.Ref,
) anyerror![]const u8 {
    var buf = std.ArrayListUnmanaged(u8){};
    errdefer buf.deinit(allocator);
    try buf.appendSlice(allocator, rule_name);
    if (arg_bindings.len != 0) {
        try buf.appendSlice(allocator, " (");
        for (arg_bindings, 0..) |binding, idx| {
            if (idx != 0) try buf.appendSlice(allocator, ", ");
            try buf.writer(allocator).print(
                "{s} := $ {s} $",
                .{ binding.name, binding.formula.text },
            );
        }
        try buf.append(allocator, ')');
    }
    if (refs.len != 0) {
        try buf.appendSlice(allocator, " [");
        for (refs, 0..) |ref, idx| {
            if (idx != 0) try buf.appendSlice(allocator, ", ");
            try renderRef(allocator, &buf, ref);
        }
        try buf.append(allocator, ']');
    }
    return try buf.toOwnedSlice(allocator);
}

fn renderRef(
    allocator: std.mem.Allocator,
    buf: *std.ArrayListUnmanaged(u8),
    ref: ProofScript.Ref,
) anyerror!void {
    switch (ref) {
        .hyp => |hyp| if (hyp.name) |name|
            try buf.writer(allocator).print("#{s}", .{name})
        else
            try buf.writer(allocator).print("#{}", .{hyp.index}),
        .line => |line| try buf.appendSlice(allocator, line.label),
        .application => |app| {
            const rendered = try renderApplication(
                allocator,
                app.rule_name,
                app.arg_bindings,
                app.refs,
            );
            defer allocator.free(rendered);
            try buf.appendSlice(allocator, rendered);
            // An inline 0-ref application must keep explicit `[]`, otherwise a
            // bare rule name re-parses as a line-label ref (`unknown proof line
            // label`). Top-level applications don't need this (a bare rule name
            // after `by` is an application there).
            if (app.refs.len == 0) try buf.appendSlice(allocator, " []");
        },
    }
}
