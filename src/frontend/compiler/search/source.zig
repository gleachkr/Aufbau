const std = @import("std");
const types = @import("./types.zig");
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
    if (options.counters == null) options.counters = &local_counters;

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

    const target = try findSearchLine(work, proof_src, offset) orelse {
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

    const is_exact = std.mem.eql(u8, target_application.rule_name, "exact?");
    const is_auto = std.mem.eql(u8, target_application.rule_name, "auto?");
    // `auto?` shares `exact?`'s direct-search dispatch; generation is layered on
    // top of the direct results below.
    const is_exact_like = is_exact or is_auto;

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
    );
    apply_suggestions.target_span = match_span;
    apply_suggestions.status = searchStatus(
        apply_suggestions.items.len,
        options.counters.?,
    );
    // `apply_suggestions` lives on the work arena; hand the caller an owned copy.
    return try copyOutSuggestions(allocator, apply_suggestions);
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

const SourceTarget = struct {
    block: ProofScript.ProofBlock,
    line_index: usize,
    path: []const usize,
};

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

        pub fn keyword(self: Kind) []const u8 {
            return switch (self) {
                .exact => "exact?",
                .apply => "apply?",
                .auto => "auto?",
            };
        }
    };

    kind: Kind,
    /// The placeholder application's span (keyword through refs) — the
    /// natural diagnostic underline. Falls inside the catchment `target_span`
    /// a search at this placeholder reports (the whole line for a top-level
    /// placeholder, this same span for a nested one).
    span: Span,
};

/// Enumerate every search placeholder (`exact?`/`apply?`/`auto?`) in
/// `proof_src`, top-level and nested, in source order. Used by the LSP to
/// publish a status diagnostic per placeholder. A parse error ends the scan
/// early (the compiler's own diagnostics already cover malformed source);
/// whatever was collected before it is returned. The result is allocated on
/// `allocator`; parser transients are torn down before returning.
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
            else
                .auto;
        try out.append(allocator, .{ .kind = kind, .span = application.span });
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
) !?SourceTarget {
    var parser = ProofParser.init(allocator, proof_src);
    while (try parser.nextBlock()) |block| {
        for (block.lines, 0..) |line, line_index| {
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
) !?[]const usize {
    for (application.refs, 0..) |ref, idx| {
        const child = switch (ref) {
            .application => |app| app,
            .hyp, .line => continue,
        };
        if (offset < child.span.start or offset > child.span.end) continue;
        if (ProofScript.isSearchPlaceholderRuleName(child.rule_name)) {
            const path = try allocator.alloc(usize, 1);
            path[0] = idx;
            return path;
        }
        if (try findNestedSearchPath(allocator, child, offset)) |suffix| {
            const path = try allocator.alloc(usize, suffix.len + 1);
            path[0] = idx;
            @memcpy(path[1..], suffix);
            return path;
        }
    }
    return null;
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
) !SourceSuggestions {
    var items = std.ArrayListUnmanaged(SourceSuggestion){};
    errdefer deinitSourceSuggestionItems(allocator, items.items);
    for (candidates) |candidate| {
        const replacement = try renderApplyApplication(allocator, candidate);
        errdefer allocator.free(replacement);
        const title = try std.fmt.allocPrint(
            allocator,
            "Replace apply? with {s}",
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
    const rule_context = Check.RuleApplyContext{
        .allocator = context.allocator,
        .parser = context.parser,
        .env = context.env,
        .registry = context.registry,
        .rule_catalog = context.rule_catalog,
        .fresh_bindings = context.fresh_bindings,
        .freshen_bindings = context.freshen_bindings,
        .views = context.views,
        .sort_vars = context.sort_vars,
        .assertion = context.assertion,
        .labels = context.labels,
        .checked = context.checked,
        .diag_scratch = context.diag_scratch,
        .rule_unify_cache = context.rule_unify_cache,
    };
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
    if (goalConcreteExpectation(goal)) |line_expr| {
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
    const instantiated = try instantiateTemplatePartial(
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

fn goalConcreteExpectation(goal: Goal) ?ExprId {
    return switch (goal) {
        .concrete => |expr| expr,
        .implicit_whole_conclusion => |maybe_expr| maybe_expr,
        .holey => null,
    };
}

fn instantiateTemplatePartial(
    theorem: *TheoremContext,
    template: TemplateExpr,
    bindings: []const ?ExprId,
) !?ExprId {
    return switch (template) {
        .binder => |idx| blk: {
            if (idx >= bindings.len) return error.TemplateBinderOutOfRange;
            break :blk bindings[idx];
        },
        .app => |app| blk: {
            const args = try theorem.allocator.alloc(ExprId, app.args.len);
            errdefer theorem.allocator.free(args);
            for (app.args, 0..) |arg, idx| {
                args[idx] = (try instantiateTemplatePartial(
                    theorem,
                    arg,
                    bindings,
                )) orelse {
                    theorem.allocator.free(args);
                    break :blk null;
                };
            }
            break :blk try theorem.interner.internAppOwned(app.term_id, args);
        },
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
    return .{
        .allocator = allocator,
        .items = items,
        .target_span = src.target_span,
        .status = src.status,
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
        .hyp => |hyp| try buf.writer(allocator).print("#{}", .{hyp.index}),
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

pub const Fixture = struct {
    parser: MM0Parser,
    env: GlobalEnv,
    registry: RewriteRegistry,
    rule_catalog: RuleCatalog.Catalog,
    fresh_bindings: std.AutoHashMap(u32, []const FreshDecl),
    freshen_bindings: std.AutoHashMap(u32, []const FreshenDecl),
    views: std.AutoHashMap(u32, ViewDecl),
    sort_vars: SortVarRegistry,
    assertion: AssertionStmt,
    available_rule_count: usize,
};

pub fn fixtureFor(
    allocator: std.mem.Allocator,
    mm0_src: []const u8,
    theorem_name: []const u8,
) !Fixture {
    return fixtureForSearchPoint(
        allocator,
        mm0_src,
        theorem_name,
        false,
    );
}

pub fn fixtureForFullEnv(
    allocator: std.mem.Allocator,
    mm0_src: []const u8,
    theorem_name: []const u8,
) !Fixture {
    return fixtureForSearchPoint(
        allocator,
        mm0_src,
        theorem_name,
        true,
    );
}

fn fixtureForSourceTarget(
    allocator: std.mem.Allocator,
    mm0_src: []const u8,
    proof_src: []const u8,
    target: SourceTarget,
) !Fixture {
    const anchor_name = try sourceTargetAnchorName(
        allocator,
        proof_src,
        target.block,
    ) orelse return error.MissingTheorem;
    var fixture = try initSearchFixture(allocator, mm0_src);
    var sink = DiagnosticSink.init(mm0_src, proof_src);
    var compiler = CompilerContext.init(mm0_src, proof_src, .none, &sink);
    var proof_stream: ?PipelineCommon.ProofItemStream =
        PipelineCommon.ProofItemStream.init(allocator, proof_src);

    while (true) {
        try fixture.parser.prepareNextPublicStatement();
        const header = fixture.parser.peekNextPublicStmtHeader() orelse {
            return error.MissingTheorem;
        };
        if (target.block.kind == .lemma and
            publicHeaderNameEql(header, anchor_name))
        {
            const block = try drainLocalItemsBeforeSearchTarget(
                &compiler,
                allocator,
                &fixture,
                &proof_stream,
                target.block.span,
            );
            fixture.assertion = try PipelineCommon.parseLemmaAssertion(
                &compiler,
                allocator,
                &fixture.parser,
                block,
            );
            fixture.available_rule_count = fixture.env.rules.items.len;
            return fixture;
        }

        try PipelineCommon.drainAnchoredLocalProofItems(
            &compiler,
            allocator,
            &fixture.parser,
            &fixture.env,
            &fixture.registry,
            &fixture.rule_catalog,
            &fixture.fresh_bindings,
            &fixture.freshen_bindings,
            &fixture.views,
            &fixture.sort_vars,
            &proof_stream,
            null,
        );

        const stmt = try fixture.parser.next() orelse {
            return error.MissingTheorem;
        };
        switch (stmt) {
            .sort => |sort_stmt| try processSearchSortStmt(
                &fixture,
                stmt,
                sort_stmt,
            ),
            .term => |term_stmt| try processSearchTermStmt(
                &compiler,
                allocator,
                &fixture,
                &proof_stream,
                term_stmt,
            ),
            .assertion => |assertion| {
                if (target.block.kind == .theorem and
                    std.mem.eql(u8, assertion.name, anchor_name))
                {
                    fixture.assertion = assertion;
                    fixture.available_rule_count = fixture.env.rules.items.len;
                    return fixture;
                }
                try processSearchAssertionStmt(
                    &fixture,
                    &proof_stream,
                    assertion,
                );
            },
        }
    }
}

fn initSearchFixture(
    allocator: std.mem.Allocator,
    mm0_src: []const u8,
) !Fixture {
    return .{
        .parser = MM0Parser.init(mm0_src, allocator),
        .env = GlobalEnv.init(allocator),
        .registry = RewriteRegistry.init(allocator),
        .rule_catalog = try RuleCatalog.build(allocator, mm0_src),
        .fresh_bindings = std.AutoHashMap(
            u32,
            []const FreshDecl,
        ).init(allocator),
        .freshen_bindings = std.AutoHashMap(
            u32,
            []const FreshenDecl,
        ).init(allocator),
        .views = std.AutoHashMap(u32, ViewDecl).init(allocator),
        .sort_vars = SortVarRegistry.init(allocator),
        .assertion = undefined,
        .available_rule_count = 0,
    };
}

fn fixtureForSearchPoint(
    allocator: std.mem.Allocator,
    mm0_src: []const u8,
    theorem_name: []const u8,
    include_trailing_rules: bool,
) !Fixture {
    var fixture = try initSearchFixture(allocator, mm0_src);
    var found_theorem = false;

    while (try fixture.parser.next()) |stmt| {
        switch (stmt) {
            .sort => |sort_stmt| {
                try fixture.env.addStmt(stmt);
                try Metadata.processSortMetadata(
                    &fixture.parser,
                    sort_stmt,
                    fixture.parser.last_annotations,
                    &fixture.sort_vars,
                );
            },
            .term => |term_stmt| {
                try fixture.env.addStmt(stmt);
                try Metadata.processTermMetadata(
                    &fixture.env,
                    &fixture.registry,
                    term_stmt,
                    fixture.parser.last_annotations,
                );
            },
            .assertion => |assertion| {
                if (!found_theorem and
                    std.mem.eql(u8, assertion.name, theorem_name))
                {
                    fixture.assertion = assertion;
                    fixture.available_rule_count =
                        fixture.env.rules.items.len;
                    found_theorem = true;
                    if (!include_trailing_rules) return fixture;
                    continue;
                }
                try fixture.env.addStmt(stmt);
                try Metadata.processAssertionMetadata(
                    allocator,
                    &fixture.parser,
                    &fixture.env,
                    &fixture.registry,
                    &fixture.fresh_bindings,
                    &fixture.freshen_bindings,
                    &fixture.views,
                    assertion,
                    fixture.parser.last_annotations,
                );
            },
        }
    }
    if (found_theorem) return fixture;
    return error.MissingTheorem;
}

fn sourceTargetAnchorName(
    allocator: std.mem.Allocator,
    proof_src: []const u8,
    target_block: ProofScript.ProofBlock,
) !?[]const u8 {
    if (target_block.kind == .theorem) return target_block.name;

    var parser = ProofParser.init(allocator, proof_src);
    var found_target = false;
    while (try parser.nextItem()) |item| {
        switch (item) {
            .block => |block| {
                if (spanEql(block.span, target_block.span)) {
                    found_target = true;
                    continue;
                }
                if (!found_target) continue;
                if (block.kind == .theorem) return block.name;
            },
            .def => |def| {
                if (!found_target) continue;
                if (def.header_tail == null) return def.name;
            },
        }
    }
    return null;
}

fn publicHeaderNameEql(header: anytype, name: []const u8) bool {
    const header_name = header.name orelse return false;
    return std.mem.eql(u8, header_name, name);
}

fn drainLocalItemsBeforeSearchTarget(
    compiler: *CompilerContext,
    allocator: std.mem.Allocator,
    fixture: *Fixture,
    proof_stream: *?PipelineCommon.ProofItemStream,
    target_span: Span,
) !ProofScript.ProofBlock {
    const proofs = if (proof_stream.*) |*value| value else {
        return error.MissingProofBlock;
    };
    var locals = std.ArrayListUnmanaged(ProofScript.TopLevelItem){};
    defer locals.deinit(allocator);

    while (true) {
        const item = (try proofs.next()) orelse return error.MissingProofBlock;
        switch (item) {
            .block => |block| {
                if (spanEql(block.span, target_span)) {
                    try processSearchLocalItems(
                        compiler,
                        allocator,
                        fixture,
                        locals.items,
                    );
                    return block;
                }
                if (PipelineCommon.isLocalProofItem(item)) {
                    try locals.append(allocator, item);
                    continue;
                }
                proofs.putBack(item);
                putBackProofItems(proofs, locals.items);
                return error.MissingProofBlock;
            },
            .def => {
                if (PipelineCommon.isLocalProofItem(item)) {
                    try locals.append(allocator, item);
                    continue;
                }
                proofs.putBack(item);
                putBackProofItems(proofs, locals.items);
                return error.MissingProofBlock;
            },
        }
    }
}

fn processSearchLocalItems(
    compiler: *CompilerContext,
    allocator: std.mem.Allocator,
    fixture: *Fixture,
    items: []const ProofScript.TopLevelItem,
) !void {
    for (items) |item| {
        try PipelineCommon.processLocalProofItem(
            compiler,
            allocator,
            &fixture.parser,
            &fixture.env,
            &fixture.registry,
            &fixture.rule_catalog,
            &fixture.fresh_bindings,
            &fixture.freshen_bindings,
            &fixture.views,
            &fixture.sort_vars,
            item,
            null,
        );
    }
}

fn putBackProofItems(
    proofs: *PipelineCommon.ProofItemStream,
    items: []const ProofScript.TopLevelItem,
) void {
    var idx = items.len;
    while (idx > 0) {
        idx -= 1;
        proofs.putBack(items[idx]);
    }
}

fn processSearchSortStmt(
    fixture: *Fixture,
    stmt: MM0Stmt,
    sort_stmt: SortStmt,
) !void {
    try fixture.env.addStmt(stmt);
    try Metadata.processSortMetadata(
        &fixture.parser,
        sort_stmt,
        fixture.parser.last_annotations,
        &fixture.sort_vars,
    );
}

fn processSearchTermStmt(
    compiler: *CompilerContext,
    allocator: std.mem.Allocator,
    fixture: *Fixture,
    proof_stream: *?PipelineCommon.ProofItemStream,
    term_stmt: TermStmt,
) !void {
    var filled_term_stmt = term_stmt;
    var filled_body_span: ?Span = null;
    if (term_stmt.is_def and term_stmt.body == null) {
        const filled = try PipelineCommon.fillPublicDefBody(
            compiler,
            allocator,
            &fixture.parser,
            proof_stream,
            term_stmt,
        );
        filled_term_stmt = filled.stmt;
        filled_body_span = filled.body_span;
    }

    try PipelineCommon.validateDefinitionBody(
        compiler,
        allocator,
        &fixture.parser,
        &fixture.env,
        filled_term_stmt,
        if (filled_body_span != null) .proof else .mm0,
        filled_body_span,
    );
    try fixture.env.addStmt(.{ .term = filled_term_stmt });
    try Metadata.processTermMetadata(
        &fixture.env,
        &fixture.registry,
        filled_term_stmt,
        fixture.parser.last_annotations,
    );
}

fn processSearchAssertionStmt(
    fixture: *Fixture,
    proof_stream: *?PipelineCommon.ProofItemStream,
    assertion: AssertionStmt,
) !void {
    try fixture.env.addStmt(.{ .assertion = assertion });
    try Metadata.processAssertionMetadata(
        fixture.env.allocator,
        &fixture.parser,
        &fixture.env,
        &fixture.registry,
        &fixture.fresh_bindings,
        &fixture.freshen_bindings,
        &fixture.views,
        assertion,
        fixture.parser.last_annotations,
    );
    consumeMatchingPublicProofBlock(proof_stream, assertion) catch {};
}

fn consumeMatchingPublicProofBlock(
    proof_stream: *?PipelineCommon.ProofItemStream,
    assertion: AssertionStmt,
) !void {
    if (assertion.kind != .theorem) return;
    const proofs = if (proof_stream.*) |*value| value else return;
    const item = (try proofs.next()) orelse return;
    switch (item) {
        .block => |block| {
            if (block.kind == .theorem and
                std.mem.eql(u8, block.name, assertion.name))
            {
                return;
            }
            proofs.putBack(item);
        },
        .def => proofs.putBack(item),
    }
}

fn spanEql(lhs: Span, rhs: Span) bool {
    return lhs.start == rhs.start and lhs.end == rhs.end;
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
    return try std.fs.cwd().readFileAlloc(
        allocator,
        path,
        std.math.maxInt(usize),
    );
}

pub fn parseGoal(
    fixture: *Fixture,
    theorem: *TheoremContext,
    theorem_vars: *NameExprMap,
    text: []const u8,
) !Goal {
    const parsed = try Holes.parseAssertion(
        &fixture.parser,
        theorem,
        theorem_vars,
        &fixture.sort_vars,
        text,
    );
    return switch (parsed) {
        .concrete => |expr| .{ .concrete = expr },
        .holey => |expr| .{ .holey = expr },
    };
}

pub fn runSearchLine(
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
    commit: bool,
) !AttemptResult {
    const context = Context{
        .allocator = allocator,
        .parser = &fixture.parser,
        .env = &fixture.env,
        .registry = &fixture.registry,
        .rule_catalog = &fixture.rule_catalog,
        .fresh_bindings = &fixture.fresh_bindings,
        .freshen_bindings = &fixture.freshen_bindings,
        .views = &fixture.views,
        .sort_vars = &fixture.sort_vars,
        .assertion = fixture.assertion,
        .labels = labels,
        .checked = checked,
        .diag_scratch = diag_scratch,
        .rule_unify_cache = rule_unify_cache,
        .available_rule_count = fixture.available_rule_count,
    };
    return tryCandidate(
        compiler,
        &context,
        line.application,
        try parseGoal(fixture, theorem, theorem_vars, line.assertion.text),
        theorem,
        theorem_vars,
        .{
            .commit = commit,
            .line_label = line.label,
            .assertion_span = line.assertion.span,
            .diagnostic_span = line.span,
        },
    );
}
