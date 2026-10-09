const std = @import("std");
const types = @import("./types.zig");
const tunables = @import("./tunables.zig");
const miss = @import("./miss.zig");
const ConversionSearch = @import("./conversion.zig");
const timer = @import("./timer.zig");
const apply_mod = @import("./apply.zig");
const backtrack = @import("./backward/backtrack.zig");
const candidate_mod = @import("./candidate.zig");
const generate_mod = @import("./generate.zig");
const session_mod = @import("./session.zig");
const ExprId = @import("../../expr.zig").ExprId;
const TheoremContext = @import("../../expr.zig").TheoremContext;
const ProofScript = @import("../../proof_script.zig");
const RuleApplication = ProofScript.RuleApplication;
const Ref = ProofScript.Ref;
const Span = ProofScript.Span;
const CompilerDiag = @import("../../diag.zig");
const CompilerContext = @import("../context.zig").CompilerContext;
const BindingOracle = @import("../context.zig").BindingOracle;
const CheckedIr = @import("../../checked_ir.zig");
const CheckedLine = CheckedIr.CheckedLine;
const Inference = @import("../inference.zig");
const Check = @import("../check.zig");
const DiagnosticSink = @import("../diagnostic_sink.zig").DiagnosticSink;
const Goal = types.Goal;
const Context = types.Context;
const ApplyCandidate = types.ApplyCandidate;
const ExactCandidate = types.ExactCandidate;
const SourceSuggestion = types.SourceSuggestion;
const SourceSuggestionOptions = types.SourceSuggestionOptions;
const SourceSuggestions = types.SourceSuggestions;
const NameExprMap = types.NameExprMap;
const LabelIndexMap = types.LabelIndexMap;
const applyWithSession = apply_mod.applyWithSession;
const exactWithSession = backtrack.exactWithSession;
const fixture_mod = @import("./fixture.zig");
const fixtureForSourceTarget = fixture_mod.fixtureForSourceTarget;
const parseGoal = fixture_mod.parseGoal;
const commitSearchLine = fixture_mod.commitSearchLine;
const inline_target_mod = @import("./source/inline_target.zig");
const InlineExpectedRef = inline_target_mod.InlineExpectedRef;
const expectedGoalForInlineTarget = inline_target_mod.expectedGoalForInlineTarget;
const placeholders_mod = @import("./source/placeholders.zig");
const findSearchLine = placeholders_mod.findSearchLine;
const applicationAtPath = placeholders_mod.applicationAtPath;
const report_mod = @import("./source/report.zig");
const buildConversionDetail = report_mod.buildConversionDetail;
const searchStatus = report_mod.searchStatus;
pub const buildStatusDetail = report_mod.buildStatusDetail;
const retrySuggestion = report_mod.retrySuggestion;
const trim_mod = @import("./source/trim.zig");
const withNeededBindings = trim_mod.withNeededBindings;
const trimBindings = trim_mod.trimBindings;
const withBindingsDropped = trim_mod.withBindingsDropped;
const withBindingsDroppedFrom = trim_mod.withBindingsDroppedFrom;
pub const statusDetailWithoutRules = report_mod.statusDetailWithoutRules;
pub const SearchPlaceholder = placeholders_mod.SearchPlaceholder;
pub const searchPlaceholders = placeholders_mod.searchPlaceholders;
pub const PlaceholderNotice = placeholders_mod.PlaceholderNotice;
pub const placeholderNotices = placeholders_mod.placeholderNotices;

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
    var checked = std.ArrayListUnmanaged(CheckedLine).empty;
    defer {
        CheckedIr.deinitLines(work, checked.items);
        checked.deinit(work);
    }
    var diag_scratch = CompilerDiag.Scratch.init(work);
    defer diag_scratch.deinit();
    var cache = Inference.RuleUnifyCache.init(work);
    defer cache.deinit();

    // Labels of earlier lines with no statement to admit, as in the
    // checker's analysis: a holey placeholder line, or a holey line citing one.
    var unfinished = std.ArrayListUnmanaged([]const u8).empty;
    defer unfinished.deinit(work);
    for (target.block.lines[0..target.line_index]) |line| {
        // An incomplete line has no rule to run: stop accumulating context,
        // but keep searching at the target with the lines checked so far.
        if (line.incomplete) break;
        // An admitted line (`by sorry!`), an earlier placeholder, and a line
        // citing an unfinished line have no rule to run either, but each
        // names its goal: keep a concrete one in the context so a later
        // search can cite it, as the checker does. A goal that does not
        // parse ends the context like an incomplete line.
        const is_sorry = ProofScript.isSorryRuleName(line.application.rule_name);
        if (is_sorry or
            ProofScript.applicationHasSearchPlaceholder(line.application) or
            ProofScript.findLineRef(line.application, unfinished.items) != null)
        {
            const goal = parseGoal(
                &fixture,
                &theorem,
                &theorem_vars,
                line.assertion.text,
            ) catch break;
            switch (goal) {
                .concrete => |expr| {
                    const line_idx = CheckedIr.appendSorryLine(&checked, work, expr) catch
                        return error.OutOfMemory;
                    labels.put(line.label, line_idx) catch return error.OutOfMemory;
                },
                else => {
                    if (is_sorry) break;
                    unfinished.append(work, line.label) catch
                        return error.OutOfMemory;
                },
            }
            continue;
        }
        const line_idx = commitSearchLine(
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
        ) catch return .{
            .allocator = allocator,
            .items = &.{},
            .blocked_by = line.label_span,
        };
        labels.put(line.label, line_idx) catch return error.OutOfMemory;
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
                // A null `via` is the equation-goal path: the chain joins
                // the goal's own sides, no reference is cited.
                .title = if (conv_result.via) |via|
                    try std.fmt.allocPrint(
                        work,
                        "conversion from {s}",
                        .{via},
                    )
                else
                    "conversion joining the goal's sides",
                .replacement = replacement,
                .replace_span = target_line.span,
            };
            conv_suggestions.items = items;
            conv_suggestions.status = .found;
        } else {
            conv_suggestions.status = switch (conv_result.stats.outcome) {
                // A saturated miss is a forced negative ONLY without
                // `@compute` rules (the directed fold reduces each redex
                // once in one order, so its fixpoint certifies nothing)
                // and with an exact alpha pass (the pairing filter is
                // approximate only when it actually resolved a comparison
                // conservatively — `alpha_filter_skips` counts those in
                // the final pass; merely enrolling an alpha rule does not
                // weaken a miss).
                .saturated => if (conv_result.compute_rule_count != 0 or
                    conv_result.stats.alpha_filter_skips != 0)
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

    var budgets: CallBudgets = undefined;
    budgets.init(&compiler, options.generate.global_budget);

    if (is_exact_like) {
        // Single-proof modes (`exact?`/`auto?`) honor the tighter
        // `exact_result_limit` when set, so the editor gets one best proof and
        // `exact?` can short-circuit recursive generation. `apply?` (below) keeps
        // the full `max_results`, since it lists candidate rules.
        var exact_options = options;
        if (options.exact_result_limit) |limit| {
            exact_options.max_results = @min(options.max_results, limit);
        }
        const site = SuggestionSite{
            .compiler = &compiler,
            .context = &context,
            .budgets = &budgets,
            .counters = options.counters,
            .line = target_line,
            .line_goal = line_goal,
            .path = target.path,
            .theorem = &theorem,
            .theorem_vars = &theorem_vars,
        };
        var suggestions = if (target.path.len == 0)
            try topLevelExactSuggestions(
                work,
                &session,
                site,
                target_application.span,
                target_application.rule_name,
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
                &budgets,
                exact_options,
            );
        // `auto?` appends bounded recursive generation to the direct
        // results. Top-level concrete goals only in Step 1.
        if (is_auto and options.generate.enabled and target.path.len == 0) {
            suggestions = try appendGeneratedSuggestions(
                work,
                &session,
                site,
                target_application.span,
                exact_options,
                suggestions,
            );
        }
        if (options.counters) |counters| {
            counters.warm_search_ns += timer.elapsedSince(search_start);
        }
        suggestions.target_span = match_span;
        options.counters.?.work_budget_exhausted = budgets.searchExhausted();
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
            if (is_auto) {
                if (miss.retryFor(
                    miss.MissReport.of(options.counters.?),
                    options.generate,
                )) |retry| {
                    suggestions.retry = try retrySuggestion(
                        work,
                        proof_src,
                        target_application,
                        retry,
                    );
                }
            }
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
            .budget = budgets.searchBudget(),
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
    options.counters.?.work_budget_exhausted = budgets.searchExhausted();
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

fn topLevelExactSuggestions(
    allocator: std.mem.Allocator,
    session: *session_mod.SearchSession,
    site: SuggestionSite,
    replace_span: Span,
    keyword: []const u8,
    options: SourceSuggestionOptions,
) !SourceSuggestions {
    var results = try exactWithSession(
        site.compiler,
        session,
        site.line_goal,
        site.theorem,
        site.theorem_vars,
        .{
            .max_results = options.max_results,
            .counters = options.counters,
            .budget = site.budgets.searchBudget(),
        },
    );
    defer results.deinit();
    return try renderExactSourceSuggestions(
        allocator,
        site,
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
    session: *session_mod.SearchSession,
    site: SuggestionSite,
    replace_span: Span,
    options: SourceSuggestionOptions,
    existing: SourceSuggestions,
) !SourceSuggestions {
    var items = std.ArrayListUnmanaged(SourceSuggestion).empty;
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
        site.compiler,
        session,
        site.line_goal,
        site.theorem,
        site.theorem_vars,
        gen_options,
        site.budgets.searchBudget(),
    );
    defer generated.deinit();

    for (generated.applications) |generated_app| {
        if (items.items.len >= options.max_results) break;
        const trimmed = try trimBindings(allocator, site, generated_app);
        const app = trimmed orelse generated_app;
        // A holey goal was searched with metas for its holes; the line itself
        // must check with the rendered proof in place, filling them.
        if (site.line_goal == .holey and trimmed == null and
            !try site.validates(allocator, app)) continue;
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
    budgets: *CallBudgets,
    options: SourceSuggestionOptions,
) !SourceSuggestions {
    var items = std.ArrayListUnmanaged(SourceSuggestion).empty;
    errdefer deinitSourceSuggestionItems(allocator, items.items);

    const max_results = options.max_results;
    const site = SuggestionSite{
        .compiler = compiler,
        .context = context,
        .budgets = budgets,
        .line = line,
        .line_goal = line_goal,
        .path = path,
        .theorem = theorem,
        .theorem_vars = theorem_vars,
        .counters = options.counters,
    };
    if (inline_expectation) |expected| {
        try appendDirectRefSuggestions(
            allocator,
            site,
            session,
            expected,
            &items,
            max_results,
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
                .budget = budgets.searchBudget(),
            },
        );
        defer results.deinit();
        try appendInlineExactApplications(
            allocator,
            site,
            results.candidates,
            &items,
            max_results,
        );
    }

    // `auto?` in a slot position layers bounded recursive generation on top of
    // the direct results, exactly as the top-level path does — but only when the
    // slot goal is fully concrete. An open slot goal (an undetermined rule
    // argument) would reach `generateTopLevel` as a meta-bearing expected ref;
    // only a top-level holey line is searched that way today (its holes become
    // metas in `generateTopLevel`), so an open inline slot stays exact-only. See
    // docs/design_notes/inline_auto_open_slot_existential_gap.md.
    if (is_auto and options.generate.enabled and items.items.len < max_results) {
        if (inline_expectation) |expected| {
            if (!expected.has_placeholder) {
                try appendInlineGeneratedApplications(
                    allocator,
                    site,
                    session,
                    expected,
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
    site: SuggestionSite,
    candidates: []const ExactCandidate,
    replace_span: Span,
    keyword: []const u8,
) !SourceSuggestions {
    var items = std.ArrayListUnmanaged(SourceSuggestion).empty;
    errdefer deinitSourceSuggestionItems(allocator, items.items);
    for (candidates) |candidate| {
        const app = try withNeededBindings(allocator, site, candidate.application);
        const replacement = try renderApplication(
            allocator,
            app.rule_name,
            app.arg_bindings,
            app.refs,
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
    var items = std.ArrayListUnmanaged(SourceSuggestion).empty;
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

/// The pool refs that fill an inline slot directly. Each check is part of the
/// search, so it spends from the search budget, not the checks budget.
fn appendDirectRefSuggestions(
    allocator: std.mem.Allocator,
    site: SuggestionSite,
    session: *session_mod.SearchSession,
    expected: InlineExpectedRef,
    items: *std.ArrayListUnmanaged(SourceSuggestion),
    max_results: usize,
) !void {
    const line = site.line;
    const path = site.path;
    const ref_index = try session.getRefIndex(site.theorem, site.counters);
    const rule = &site.context.env.rules.items[expected.rule_id];
    if (expected.child_index >= rule.hyps.len) return;
    var lookup = try ref_index.lookupTemplate(
        site.theorem,
        rule.hyps[expected.child_index],
        rule.args,
        expected.bindings,
        site.counters,
    );
    defer lookup.deinit();
    for (lookup.indices) |pool_index| {
        if (items.items.len >= max_results) return;
        if (site.budgets.searchBudget()) |budget| budget.spendCandidate() catch return;
        const ref = ref_index.entries[pool_index].ref orelse continue;
        const application = try applicationWithReplacedRef(
            allocator,
            line.application,
            path,
            ref,
        );
        if (!try validateReplacementApplication(
            site.compiler,
            site.context,
            application,
            line,
            site.line_goal,
            site.theorem,
            site.theorem_vars,
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
    site: SuggestionSite,
    candidates: []const ExactCandidate,
    items: *std.ArrayListUnmanaged(SourceSuggestion),
    max_results: usize,
) !void {
    const line = site.line;
    const path = site.path;
    for (candidates) |candidate| {
        if (items.items.len >= max_results) return;
        if (!try site.validates(allocator, candidate.application)) continue;
        const app = try withNeededBindings(allocator, site, candidate.application);
        const replacement = try renderInlineApplication(allocator, app);
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
    site: SuggestionSite,
    session: *session_mod.SearchSession,
    expected: InlineExpectedRef,
    options: SourceSuggestionOptions,
    items: *std.ArrayListUnmanaged(SourceSuggestion),
    max_results: usize,
) !void {
    const line = site.line;
    const path = site.path;
    // Only concrete slot goals reach here (the caller gates on
    // `!expected.has_placeholder`); `generateTopLevel` accepts `.concrete` goals
    // exactly as it does for a top-level line.
    var gen_options = options.generate;
    gen_options.max_results = max_results - items.items.len;
    var generated = try generate_mod.generateTopLevel(
        site.compiler,
        session,
        Goal{ .concrete = expected.query },
        site.theorem,
        site.theorem_vars,
        gen_options,
        site.budgets.searchBudget(),
    );
    defer generated.deinit();

    for (generated.applications) |generated_app| {
        if (items.items.len >= max_results) return;
        if (!try site.validates(allocator, generated_app)) continue;
        const app = try withNeededBindings(allocator, site, generated_app);
        const replacement = try renderInlineApplication(allocator, app);
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
    var buf = std.ArrayListUnmanaged(u8).empty;
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
    // The probe's theorem is a COW clone based directly on the caller's
    // `theorem`, which outlives it.
    var attempt = candidate_mod.probe(
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
        },
    ) catch |err| switch (err) {
        error.OutOfMemory => return err,
        else => return false,
    };
    defer attempt.deinit();
    CheckedIr.validateLinesCached(
        &attempt.theorem,
        attempt.checked_lines,
    ) catch {
        return false;
    };
    return true;
}

/// The work budgets of one search call, each of `GenerateOptions.global_budget`
/// (none when that is null). `search` bounds the search: the direct pass,
/// generation, and the pool refs tried in an inline slot. `checks` bounds the
/// checks of the results it found (`SuggestionSite.validates`: the line with
/// a result in place, and trimming its bindings), so a search that spent its
/// whole budget still has its results checked. Each is charged only for its
/// own work, and the one charged is installed as `compiler.work_budget`.
const CallBudgets = struct {
    compiler: *CompilerContext,
    search: ?types.GlobalBudget,
    checks: ?types.GlobalBudget,

    /// In place: `compiler.work_budget` points into `self`.
    fn init(self: *CallBudgets, compiler: *CompilerContext, limit: ?u64) void {
        self.* = .{
            .compiler = compiler,
            .search = if (limit) |l| types.GlobalBudget.init(l) else null,
            .checks = if (limit) |l| types.GlobalBudget.initPaused(l) else null,
        };
        if (self.search) |*search| compiler.work_budget = search.workBudget();
    }

    fn searchBudget(self: *CallBudgets) ?*types.GlobalBudget {
        return if (self.search) |*search| search else null;
    }

    fn searchExhausted(self: *const CallBudgets) bool {
        return if (self.search) |search| search.exhausted else false;
    }

    pub fn checksExhausted(self: *const CallBudgets) bool {
        return if (self.checks) |checks| checks.exhausted else false;
    }

    /// Charge the work until `endChecks` to the checks budget.
    fn beginChecks(self: *CallBudgets) void {
        const search = &(self.search orelse return);
        const checks = &self.checks.?;
        search.pause();
        checks.unpause();
        self.compiler.work_budget = checks.workBudget();
    }

    fn endChecks(self: *CallBudgets) void {
        const search = &(self.search orelse return);
        const checks = &self.checks.?;
        checks.pause();
        search.unpause();
        self.compiler.work_budget = search.workBudget();
    }
};

/// Where a suggestion lands: the proof line holding the search placeholder,
/// and the path to the placeholder inside it (empty for a whole line).
pub const SuggestionSite = struct {
    compiler: *CompilerContext,
    context: *const Context,
    budgets: *CallBudgets,
    line: ProofScript.ProofLine,
    line_goal: Goal,
    path: []const usize,
    theorem: *const TheoremContext,
    theorem_vars: *const NameExprMap,
    /// Receives the time spent trimming bindings (`trim_ns`) and the
    /// suggestions left untrimmed (`untrimmed`).
    counters: ?*types.SearchCounters,

    /// Whether the line checks with `app` in the placeholder's place, within
    /// the checks budget.
    pub fn validates(
        self: SuggestionSite,
        allocator: std.mem.Allocator,
        app: RuleApplication,
    ) !bool {
        self.budgets.beginChecks();
        defer self.budgets.endChecks();
        const line_app = if (self.path.len == 0)
            app
        else
            try applicationWithReplacedRef(
                allocator,
                self.line.application,
                self.path,
                .{ .application = app },
            );
        return validateReplacementApplication(
            self.compiler,
            self.context,
            line_app,
            self.line,
            self.line_goal,
            self.theorem,
            self.theorem_vars,
        );
    }

    /// Check the line with the `drop`ped `bindings` of `app` withheld
    /// behind a `BindingOracle`, and keep (clear in `drop`) those the
    /// checker takes from it, setting `coarse` for those it took
    /// over-approximately. A failed check that forced a binding reruns with
    /// it supplied. Null when the check fails; otherwise whether it took
    /// any. A check that takes none has checked exactly the suggestion
    /// `drop` leaves.
    pub fn neededBindings(
        self: SuggestionSite,
        allocator: std.mem.Allocator,
        app: RuleApplication,
        bindings: []const *const ProofScript.ArgBinding,
        drop: []bool,
        coarse: []bool,
    ) !?bool {
        var oracle = BindingOracle{ .allocator = allocator };
        defer oracle.deinit();
        var next: usize = 0;
        const withheld = try withBindingsDroppedFrom(allocator, app, drop, &next, &oracle);
        const saved = self.compiler.binding_oracle;
        self.compiler.binding_oracle = &oracle;
        defer self.compiler.binding_oracle = saved;
        while (true) {
            const forced = oracle.forced.count();
            if (try self.validates(allocator, withheld)) break;
            // Each rerun forces at least one more binding, so this ends.
            if (oracle.forced.count() == forced) return null;
            oracle.used.clearRetainingCapacity();
        }
        var took = false;
        for (bindings, drop, coarse) |binding, *slot, *spare| {
            if (!slot.* or !oracle.used.contains(binding)) continue;
            slot.* = false;
            spare.* = oracle.forced.contains(binding);
            took = true;
        }
        return took;
    }

    /// Drop each `coarse` binding `drop` keeps whose line still checks
    /// without it.
    pub fn dropCoarse(
        self: SuggestionSite,
        allocator: std.mem.Allocator,
        app: RuleApplication,
        drop: []bool,
        coarse: []const bool,
    ) !void {
        for (coarse, drop) |spare, *slot| {
            if (!spare or slot.*) continue;
            slot.* = true;
            const trial = try withBindingsDropped(allocator, app, drop);
            if (!try self.validates(allocator, trial)) slot.* = false;
        }
    }
};

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
pub fn copyOutSuggestions(
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
    errdefer if (status_detail) |detail| allocator.free(detail);
    var retry: ?SourceSuggestion = null;
    if (src.retry) |item| {
        const title = try allocator.dupe(u8, item.title);
        errdefer allocator.free(title);
        retry = .{
            .title = title,
            .replacement = try allocator.dupe(u8, item.replacement),
            .replace_span = item.replace_span,
        };
    }
    return .{
        .allocator = allocator,
        .items = items,
        .target_span = src.target_span,
        .status = src.status,
        .status_detail = status_detail,
        .retry = retry,
    };
}

fn renderApplyApplication(
    allocator: std.mem.Allocator,
    candidate: ApplyCandidate,
) ![]const u8 {
    if (candidate.unresolved_hyps.len == 0) {
        return try allocator.dupe(u8, candidate.rule_name);
    }
    var buf = std.ArrayListUnmanaged(u8).empty;
    errdefer buf.deinit(allocator);
    try buf.print(allocator, "{s} [", .{candidate.rule_name});
    for (candidate.unresolved_hyps, 0..) |_, idx| {
        if (idx != 0) try buf.appendSlice(allocator, ", ");
        try buf.print(allocator, "ref{}", .{idx + 1});
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
    var buf = std.ArrayListUnmanaged(u8).empty;
    errdefer buf.deinit(allocator);
    try buf.appendSlice(allocator, rule_name);
    if (arg_bindings.len != 0) {
        try buf.appendSlice(allocator, " (");
        for (arg_bindings, 0..) |binding, idx| {
            if (idx != 0) try buf.appendSlice(allocator, ", ");
            try buf.print(
                allocator,
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

/// An application rendered to stand in a ref list (see `renderRef`).
fn renderInlineApplication(
    allocator: std.mem.Allocator,
    app: RuleApplication,
) ![]const u8 {
    var buf = std.ArrayListUnmanaged(u8).empty;
    errdefer buf.deinit(allocator);
    try renderRef(allocator, &buf, .{ .application = app });
    return try buf.toOwnedSlice(allocator);
}

fn renderRef(
    allocator: std.mem.Allocator,
    buf: *std.ArrayListUnmanaged(u8),
    ref: ProofScript.Ref,
) anyerror!void {
    switch (ref) {
        .hyp => |hyp| if (hyp.name) |name|
            try buf.print(allocator, "#{s}", .{name})
        else
            try buf.print(allocator, "#{}", .{hyp.index}),
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
