const std = @import("std");
const ReclaimingAllocator = @import("../../reclaiming_allocator.zig").ReclaimingAllocator;
const types = @import("./types.zig");
const tunables = @import("./tunables.zig");
const miss = @import("./miss.zig");
const ConversionSearch = @import("./conversion.zig");
const timer = @import("./timer.zig");
const apply_mod = @import("./apply.zig");
const candidate_mod = @import("./candidate.zig");
const entry = @import("./entry.zig");
const session_mod = @import("./session.zig");
const ExprId = @import("../../expr.zig").ExprId;
const TheoremContext = @import("../../expr.zig").TheoremContext;
const ProofScript = @import("../../proof_script.zig");
const RuleApplication = ProofScript.RuleApplication;
const Ref = ProofScript.Ref;
const Span = ProofScript.Span;
const CompilerContext = @import("../context.zig").CompilerContext;
const BindingOracle = @import("../context.zig").BindingOracle;
const CheckedIr = @import("../../checked_ir.zig");
const Check = @import("../check.zig");
const DiagnosticSink = @import("../diagnostic_sink.zig").DiagnosticSink;
const Goal = types.Goal;
const Context = types.Context;
const SourceSuggestion = types.SourceSuggestion;
const SourceSuggestionOptions = types.SourceSuggestionOptions;
const SourceSuggestions = types.SourceSuggestions;
const NameExprMap = types.NameExprMap;
const applyWithSession = apply_mod.applyWithSession;
const fixture_mod = @import("./fixture.zig");
const fixtureForSourceTarget = fixture_mod.fixtureForSourceTarget;
const parseGoal = fixture_mod.parseGoal;
const inline_target_mod = @import("./source/inline_target.zig");
const InlineExpectedRef = inline_target_mod.InlineExpectedRef;
const expectedGoalForInlineTarget = inline_target_mod.expectedGoalForInlineTarget;
const placeholders_mod = @import("./source/placeholders.zig");
const open_goal_mod = @import("./source/open_goal.zig");
const OpenGoals = @import("../check/open_goals.zig");
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
    // thread a local block when the caller didn't pass one. Search behavior
    // never depends on the counters (they are observe-only).
    var local_counters = types.SearchCounters{};
    var options = caller_options;
    if (options.counters == null) {
        // `collect` times candidates, which only the detail string reports;
        // it stays off unless the caller asked for it.
        local_counters.collect = options.status_detail;
        options.counters = &local_counters;
    }

    const setup_start = if (options.counters != null)
        timer.nanoTimestamp()
    else
        0;
    // One per-call work allocator backs the ENTIRE search: the fixture (the
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
    // that still read through `work`-backed structures.
    //
    // It reuses what the search frees, so freed clones and scratch don't
    // pile up (a bump arena here held them all until the call ended: memory
    // grew with the work, to gigabytes on retried searches), and it releases
    // whatever is still live when the call ends, since the transient state is
    // spread across the parser, diagnostics, def_ops and inference layers and
    // not all of it is freed (the depth corpus once grew to ~20 GiB across
    // theorems from that).
    var work_state = ReclaimingAllocator.init(caller_options.work_allocator orelse allocator);
    defer work_state.deinit();
    const work = work_state.allocator();

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
    // A result is checked in the whole line, where another placeholder may
    // still stand: the checker admits it as the goal it fills.
    compiler.allow_search_placeholders = true;

    var theorem = TheoremContext.init(work);
    defer theorem.deinit();
    try theorem.seedAssertion(fixture.assertion);
    // Replay the lines before the target through the checker's own walk, so
    // the search plans against the context the checker builds. An
    // incomplete line ends the context, as in the analysis; a line the
    // checker rejects blocks the search.
    var walk = try Check.LineWalk.init(
        &compiler,
        work,
        &fixture.theory,
        fixture.assertion,
        target.block.lines,
        &theorem,
    );
    defer walk.deinit();
    try walk.solveUnknowns(try theorem.internParsedExpr(fixture.assertion.concl));
    for (target.block.lines[0..target.line_index]) |line| {
        const next = walk.step(line) catch |err| switch (err) {
            error.OutOfMemory => return err,
            else => return .{
                .allocator = allocator,
                .items = &.{},
                .blocked_by = line.label_span,
            },
        };
        if (next == .stop) break;
    }
    const theorem_vars = &walk.theorem_vars;

    const context = fixture_mod.searchContext(
        work,
        &fixture,
        &walk.labels,
        &walk.checked,
        &walk.diag_scratch,
        &walk.rule_unify_cache,
    );
    var session = session_mod.SearchSession.init(&context, .{
        .counters = options.counters,
        .query_shape_cache = options.generate.shape_cache,
    });
    // No `session.deinit()`: the session, its rule and reference indexes and
    // the query-shape cache all live in `work`, which is freed whole on
    // return. Walking the cached shape trees to free them node by node first
    // cost about 1.5% of a search (#446).

    const target_line = target.block.lines[target.line_index];
    const line_goal = try boundGoal(&walk, try parseGoal(
        &fixture,
        &theorem,
        theorem_vars,
        target_line.assertion.text,
    ));
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
    const is_open_goal = !options.apply_at_offset and
        ProofScript.isOpenGoalRuleName(target_application.rule_name);
    const target_kind: SourceSuggestions.TargetKind =
        if (is_open_goal) .open_goal else .search;

    if (options.counters) |counters| {
        counters.cold_setup_ns += timer.elapsedSince(setup_start);
    }
    const search_start = if (options.counters != null)
        timer.nanoTimestamp()
    else
        0;
    // Everything from here on is the warm search, rendering included.
    defer if (options.counters) |counters| {
        counters.warm_search_ns += timer.elapsedSince(search_start);
    };

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
            theorem_vars,
        ) orelse {
            return .{
                .allocator = allocator,
                .items = &.{},
                .target_span = match_span,
                .target_kind = target_kind,
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
            return .{
                .allocator = allocator,
                .items = &.{},
                .target_span = match_span,
                .target_kind = target_kind,
            };
        }
    }

    if (is_conversion) {
        // Top-level lines only: an inline conversion has no line of its own
        // in front of which the chain could be spliced.
        if (target.path.len != 0) {
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
                theorem_vars,
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
        return try copyOutSuggestions(allocator, conv_suggestions);
    }

    var budgets: CallBudgets = undefined;
    budgets.init(&compiler, options.generate.global_budget);

    if (is_open_goal) {
        // An inline open goal whose position fixes only part of its goal
        // returned above, so this one is concrete: it is probed as the
        // statement it is, which lets a rule leave premise binders open, as
        // on a line.
        const goal: Goal = if (inline_expectation) |expected|
            .{ .concrete = expected.query }
        else
            search_goal;
        const empty: SourceSuggestions = .{
            .allocator = work,
            .items = &.{},
            .target_span = match_span,
            .target_kind = target_kind,
        };
        // A `?` with bindings is malformed; its error is the only thing to fix.
        if (OpenGoals.hasBindings(target_application)) return try copyOutSuggestions(allocator, empty);
        // Every rule the goal matches is ranked by what the facts close, so
        // none is cut before the ranking, unless the budget runs out first.
        var results = try applyWithSession(
            &compiler,
            &session,
            goal,
            &theorem,
            theorem_vars,
            .{
                .max_results = null,
                .counters = options.counters,
                .budget = budgets.searchBudget(),
                .premises = if (target_application.refs.len == 0) null else target_application.refs,
            },
        );
        defer results.deinit();
        options.counters.?.work_budget_exhausted = budgets.searchExhausted();
        var suggestions = empty;
        suggestions.items = try open_goal_mod.actions(work, .{
            .proof_src = proof_src,
            .block_lines = target.block.lines,
            .line_index = target.line_index,
            .marker = target_application,
            .top_level = target.path.len == 0,
            .context = &context,
            .theorem = &theorem,
        }, results.candidates, line_goal);
        return try copyOutSuggestions(allocator, suggestions);
    }

    if (is_exact_like) {
        // `exact?` and `auto?` honor the tighter `exact_result_limit` when
        // set, so the editor gets one best proof and `exact?` can
        // short-circuit recursive generation.
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
            .theorem_vars = theorem_vars,
        };
        // `auto?`'s search finds the one-step proofs `exact?` would too.
        var suggestions = if (target.path.len != 0)
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
                theorem_vars,
                is_auto,
                &budgets,
                exact_options,
            )
        else if (is_auto and options.generate.enabled)
            try generatedSuggestions(
                work,
                &session,
                site,
                target_application.span,
                exact_options,
            )
        else
            try topLevelExactSuggestions(
                work,
                &session,
                site,
                target_application.span,
                target_application.rule_name,
                exact_options,
            );
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
        // `suggestions` lives on the work allocator; hand the caller an owned copy.
        return try copyOutSuggestions(allocator, suggestions);
    }

    // What is left is an ordinary rule name under the cursor
    // (`apply_at_offset`): the rules whose conclusion matches its goal, each
    // as its bare name.
    std.debug.assert(options.apply_at_offset);
    var results = try applyWithSession(
        &compiler,
        &session,
        search_goal,
        &theorem,
        theorem_vars,
        .{
            .max_results = options.max_results,
            .counters = options.counters,
            .budget = budgets.searchBudget(),
        },
    );
    defer results.deinit();
    const items = try work.alloc(SourceSuggestion, results.candidates.len);
    for (results.candidates, items) |candidate, *item| {
        item.* = .{
            .title = candidate.rule_name,
            .replacement = candidate.rule_name,
            .replace_span = target_application.span,
        };
    }
    // `items` lives on the work allocator; hand the caller an owned copy.
    return try copyOutSuggestions(allocator, .{
        .allocator = work,
        .items = items,
        .target_span = match_span,
    });
}

/// `goal` with the named unknowns the walk bound written as their values,
/// as the checker reads the line.
fn boundGoal(walk: *Check.LineWalk, goal: Goal) !Goal {
    const surface = switch (goal) {
        .holey => |surface| surface,
        .concrete, .implicit_whole_conclusion => return goal,
    };
    return switch (try walk.writeBoundUnknowns(.{ .holey = surface })) {
        .concrete => |expr| .{ .concrete = expr },
        .holey => |written| .{ .holey = written },
    };
}

fn topLevelExactSuggestions(
    allocator: std.mem.Allocator,
    session: *session_mod.SearchSession,
    site: SuggestionSite,
    replace_span: Span,
    keyword: []const u8,
    options: SourceSuggestionOptions,
) !SourceSuggestions {
    var found = try entry.exactTopLevel(
        site.compiler,
        session,
        site.line_goal,
        site.theorem,
        site.theorem_vars,
        options.generate.stack_guard_bytes,
        site.budgets.searchBudget(),
    );
    defer found.deinit();
    return try foundSuggestions(allocator, site, found.applications, replace_span, keyword, options.max_results);
}

/// Run bounded recursive generation for an `auto?` goal, keeping at most
/// `max_results` distinct suggestions.
fn generatedSuggestions(
    allocator: std.mem.Allocator,
    session: *session_mod.SearchSession,
    site: SuggestionSite,
    replace_span: Span,
    options: SourceSuggestionOptions,
) !SourceSuggestions {
    var generated = try entry.generateTopLevel(
        site.compiler,
        session,
        site.line_goal,
        site.theorem,
        site.theorem_vars,
        options.generate,
        site.budgets.searchBudget(),
    );
    defer generated.deinit();
    return try foundSuggestions(allocator, site, generated.applications, replace_span, "auto?", options.max_results);
}

/// The suggestions for the proofs a search found for a top-level line, each
/// with only the bindings the checker needs, deduplicated by replacement
/// text, at most `max_results`.
fn foundSuggestions(
    allocator: std.mem.Allocator,
    site: SuggestionSite,
    applications: []const RuleApplication,
    replace_span: Span,
    keyword: []const u8,
    max_results: usize,
) !SourceSuggestions {
    var items = std.ArrayListUnmanaged(SourceSuggestion).empty;
    errdefer deinitSourceSuggestionItems(allocator, items.items);
    for (applications) |found_app| {
        if (items.items.len >= max_results) break;
        const trimmed = try trimBindings(allocator, site, found_app);
        const app = trimmed orelse found_app;
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
        if (offers(items.items, replacement)) {
            allocator.free(replacement);
            continue;
        }
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

    // A concrete slot goal of `auto?` is generated below, which finds the
    // one-step proofs too.
    const generates = is_auto and options.generate.enabled and
        inline_expectation != null and !inline_expectation.?.has_placeholder;
    if (items.items.len < max_results and !generates) {
        var found = try entry.exactTopLevel(
            compiler,
            session,
            search_goal,
            theorem,
            theorem_vars,
            options.generate.stack_guard_bytes,
            budgets.searchBudget(),
        );
        defer found.deinit();
        try appendInlineExactApplications(
            allocator,
            site,
            found.applications,
            &items,
            max_results,
        );
    }

    // `auto?` in a slot position layers bounded recursive generation on top of
    // the direct results, exactly as the top-level path does — but only when the
    // slot goal is fully concrete. An open slot goal (an undetermined rule
    // argument) would reach `generateTopLevel` as a meta-bearing expected ref;
    // only a top-level holey line is searched that way today (its holes become
    // witness variables of the search core), so an open inline slot stays
    // exact-only. See
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
    applications: []const RuleApplication,
    items: *std.ArrayListUnmanaged(SourceSuggestion),
    max_results: usize,
) !void {
    const line = site.line;
    const path = site.path;
    for (applications) |found_app| {
        if (items.items.len >= max_results) return;
        if (!try site.validates(allocator, found_app)) continue;
        const app = try withNeededBindings(allocator, site, found_app);
        const replacement = try renderInlineApplication(allocator, app);
        if (offers(items.items, replacement)) {
            allocator.free(replacement);
            continue;
        }
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
/// reconstructed whole line still validates. Mirrors `generatedSuggestions`
/// (top-level) and `appendInlineExactApplications` (inline one step): the
/// generated proof is a single nested `RuleApplication`, so it drops into the
/// slot the same way a proof of one step does. Deduplicates against `items` by replacement
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
    var generated = try entry.generateTopLevel(
        site.compiler,
        session,
        Goal{ .concrete = expected.query },
        site.theorem,
        site.theorem_vars,
        options.generate,
        site.budgets.searchBudget(),
    );
    defer generated.deinit();

    for (generated.applications) |generated_app| {
        if (items.items.len >= max_results) return;
        if (!try site.validates(allocator, generated_app)) continue;
        const app = try withNeededBindings(allocator, site, generated_app);
        const replacement = try renderInlineApplication(allocator, app);
        if (offers(items.items, replacement)) {
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

/// Whether `items` already offers `replacement`.
fn offers(items: []const SourceSuggestion, replacement: []const u8) bool {
    for (items) |item| {
        if (std.mem.eql(u8, item.replacement, replacement)) return true;
    }
    return false;
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
/// (none when that is null). `search` bounds the search: the search core,
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

/// Deep-copy `src` (built on the per-call work allocator) onto `allocator`, the
/// caller's allocator, so the result survives the work allocator's release. Only the
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
            .cursor = item.cursor,
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
        .target_kind = src.target_kind,
    };
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
