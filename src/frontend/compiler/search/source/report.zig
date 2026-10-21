//! The text of a search's status report: the hover detail for a found or missed
//! search, the `conversion?` detail, the retry advice and its replacement
//! text, and the top rule attempts of a miss.

const std = @import("std");
const types = @import("../types.zig");
const tunables = @import("../tunables.zig");
const miss = @import("../miss.zig");
const ConversionSearch = @import("../conversion.zig");
const generate_mod = @import("../generate.zig");
const ProofScript = @import("../../../proof_script.zig");
const RuleApplication = ProofScript.RuleApplication;
const text_util = @import("../../../text_util.zig");
const SourceSuggestion = types.SourceSuggestion;
const source_mod = @import("../source.zig");
const copyOutSuggestions = source_mod.copyOutSuggestions;

/// Failure report for a `conversion?` search. A saturated egraph with no
/// convertible pool formula is a forced negative (no chain of the enrolled
/// rules exists, period); a capped run gets the concrete next parameter.
pub fn buildConversionDetail(
    allocator: std.mem.Allocator,
    result: ConversionSearch.Result,
    conv_options: ConversionSearch.Options,
    goal_concrete: bool,
) !?[]const u8 {
    return try text_util.allocRender(
        allocator,
        writeConversionDetail,
        .{ result, conv_options, goal_concrete },
    );
}

fn writeConversionDetail(
    w: *std.Io.Writer,
    result: ConversionSearch.Result,
    conv_options: ConversionSearch.Options,
    goal_concrete: bool,
) !void {
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
                "a conversion proving this goal was found, but the " ++
                    "extracted proof chain outgrew the lowering's emission " ++
                    "cap — the conversion is proven, its re-treeing proof " ++
                    "is too large to write out.",
            );
        } else if (result.missing_congr_name) |name| {
            try w.print(
                "a conversion proving this goal was found, but its proof " ++
                    "chain rewrites under '{s}', which has no @congr rule — " ++
                    "the rewrite cannot be lifted through that operator " ++
                    "into a proof line. Annotate a congruence theorem for " ++
                    "'{s}' with @congr to let the chain lower.",
                .{ name, name },
            );
        } else if (result.blocked_congr) |blocked| {
            try w.print(
                "a conversion proving this goal was found, but its proof " ++
                    "chain rewrites under '{s}' where the @congr rule " ++
                    "'{s}' cannot lift it: '{s}' may not depend on '{s}', " ++
                    "and here that argument mentions it. Unless '{s}' " ++
                    "depends on the variable's name there, letting '{s}' " ++
                    "depend on '{s}' in '{s}' is sound and lets the chain " ++
                    "lower.",
                .{
                    blocked.head,  blocked.rule, blocked.arg,
                    blocked.bound, blocked.head, blocked.arg,
                    blocked.bound, blocked.rule,
                },
            );
        } else {
            try w.writeAll(
                "a conversion proving this goal was found, but a proof " ++
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
            if (result.equation_goal) {
                try w.writeAll(
                    " The goal is itself a relation statement, so its two " ++
                        "sides were seeded directly; they never joined " ++
                        "either.",
                );
            }
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
            if (result.stats.alpha_filter_skips != 0) {
                try w.print(
                    " The alpha pairing scheduler resolved {d} candidate " ++
                        "comparison(s) approximately (cyclic classes, " ++
                        "greedy bag alignment, or truncated instance " ++
                        "enumeration) — some renaming opportunities may " ++
                        "have been skipped, so this is NOT a forced " ++
                        "negative.",
                    .{result.stats.alpha_filter_skips},
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
    if (goal_concrete and result.stats.premise_deferred != 0) {
        try w.writeAll(
            " Some conditional-rule matches stayed deferred: their " ++
                "hypotheses never became provable from the pool (an " ++
                "equational premise needs its sides to convert; any other " ++
                "premise needs a hypothesis or earlier line in its " ++
                "e-class, which takes @congr coverage on the premise's " ++
                "head), so those rewrites were never licensed.",
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
}

/// Derive the user-facing outcome of a completed search: found beats
/// everything; an empty result is a definitive miss unless a limit cut the
/// search short first (`miss.MissReport.truncated`).
pub fn searchStatus(
    items_len: usize,
    counters: *const types.SearchCounters,
) types.SearchStatus {
    if (items_len > 0) return .found;
    if (miss.MissReport.of(counters).truncated()) return .budget_exhausted;
    return .miss;
}

/// Elaborate a failed search into the user-facing detail string: which
/// limits cut it short, how far the generation ladder got, how many
/// candidates were validated vs. accepted, and the per-call parameters to
/// raise together (`miss.retryFor`). Built on the caller's allocator (the
/// per-call work arena; `copyOutSuggestions` deep-copies it out). Purely
/// observational: reads the same counters the search already fills, never
/// influences it.
pub fn buildStatusDetail(
    allocator: std.mem.Allocator,
    keyword: []const u8,
    is_auto: bool,
    status: types.SearchStatus,
    counters: *const types.SearchCounters,
    gen: types.GenerateOptions,
) !?[]const u8 {
    if (status == .found) return null;
    return try text_util.allocRender(
        allocator,
        writeStatusDetail,
        .{ keyword, is_auto, status, counters, gen },
    );
}

fn writeStatusDetail(
    w: *std.Io.Writer,
    keyword: []const u8,
    is_auto: bool,
    status: types.SearchStatus,
    counters: *const types.SearchCounters,
    gen: types.GenerateOptions,
) !void {
    const validated = counters.full_try_candidate_calls;
    const accepted = counters.accepted_candidates;
    const rejected = counters.rejected_candidates_after_validation;
    const report = miss.MissReport.of(counters);
    // Only `auto?` generates (an `exact?`, an open inline slot, or a
    // disabled generation permit leaves the ladder unrun).
    const generation_ran = is_auto and report.generation_ran;
    const retry: ?miss.Retry = if (is_auto) miss.retryFor(report, gen) else null;

    switch (status) {
        .found => unreachable,
        .miss => {
            if (generation_ran) {
                try w.print(
                    "no proof found within depth {d}. The search space was " ++
                        "exhausted ({d} applications validated: {d} " ++
                        "accepted, {d} rejected), so a proof, if one " ++
                        "exists, is deeper or needs a rule the search " ++
                        "cannot use backward here.",
                    .{ gen.max_depth, validated, accepted, rejected },
                );
                if (retry) |r| try writeRetryAdvice(w, keyword, r, false);
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
            if (report.stop == .stack) {
                // No user-tunable parameter raises this bound (it protects
                // the process stack itself), so the actionable advice is to
                // shrink the search, not to grow a budget.
                try w.print(
                    "stopped by the call-stack guard during {s} at depth " ++
                        "{d} of {d}: one search branch recursed deep " ++
                        "enough to risk exhausting the process stack and " ++
                        "was abandoned. A proof may still exist — try a " ++
                        "smaller goal or prove an intermediate lemma first.",
                    .{
                        generate_mod.phaseName(counters.gen_last_phase),
                        counters.gen_last_depth,
                        gen.max_depth,
                    },
                );
            } else {
                // Every limit that was hit, not just the first: they bind
                // together, and naming one sends the author from limit to
                // limit.
                try w.writeAll("the search was cut short: ");
                var first = true;
                if (report.stop == .budget) {
                    first = false;
                    const seconds = std.math.divCeil(
                        u64,
                        gen.global_budget orelse 0,
                        tunables.ticks_per_budget_unit,
                    ) catch unreachable;
                    // The call ends where the budget runs out, so the last
                    // cell started is the one that tripped it.
                    if (generation_ran) {
                        try w.print(
                            "the per-call work budget (~{d}s of work) ran out " ++
                                "during {s} at depth {d} of {d}",
                            .{
                                seconds,
                                generate_mod.phaseName(counters.gen_last_phase),
                                counters.gen_last_depth,
                                gen.max_depth,
                            },
                        );
                    } else {
                        try w.print(
                            "the per-call work budget (~{d}s of work) ran out " ++
                                "before every candidate was tried",
                            .{seconds},
                        );
                    }
                }
                if (report.nodes) {
                    if (!first) try w.writeAll("; ");
                    first = false;
                    const passes = counters.gen_node_capped_passes;
                    try w.print(
                        "the limit of {d} subgoals per pass was reached in " ++
                            "{d} pass{s}",
                        .{ gen.max_nodes, passes, if (passes == 1) "" else "es" },
                    );
                }
                if (report.fuel) {
                    if (!first) try w.writeAll("; ");
                    first = false;
                    try w.print(
                        "a search phase ran out of fuel ({d} candidate " ++
                            "validations per phase)",
                        .{gen.fuel},
                    );
                }
                if (report.forward) {
                    if (!first) try w.writeAll("; ");
                    first = false;
                    try w.writeAll(
                        "forward saturation stopped before reaching a " ++
                            "fixpoint, so the derived-fact pool is incomplete",
                    );
                }
                try w.print(
                    ". {d} applications validated ({d} accepted).",
                    .{ validated, accepted },
                );
                if (generation_ran and
                    report.searchedBelowDepthLimit(gen.max_depth))
                {
                    try w.print(
                        " Every depth below {d} was searched, so the " ++
                            "proof may also be deeper.",
                        .{gen.max_depth},
                    );
                }
                if (retry) |r| {
                    try writeRetryAdvice(w, keyword, r, true);
                } else {
                    try w.writeAll(" A proof may still exist.");
                }
            }
        },
    }

    // Where the work went: the most-tried rules with their accept counts
    // (attempts ≠ accepts — a rule tried 500 times with 0 accepted is a
    // reject-flood, the usual budget sink). Only recorded under `collect`.
    try appendTopRuleAttempts(w, counters);
}

/// " Try 'auto? (nodes: 512, budget: 14)'." — on a cut-short miss, with
/// the reason to raise the limits together and what to try if that fails.
fn writeRetryAdvice(
    w: anytype,
    keyword: []const u8,
    retry: miss.Retry,
    cut_short: bool,
) !void {
    if (cut_short) {
        try w.writeAll(
            " These limits share one work budget, so raise them together:",
        );
    }
    try w.print(" {s} '{s} (", .{ if (cut_short) "try" else "Try", keyword });
    try w.print("{f})'.", .{retry});
    if (cut_short) {
        try w.writeAll(
            " A larger search finds only some of the proofs a smaller " ++
                "one misses; if it fails too, try proving an intermediate " ++
                "lemma first.",
        );
    }
}

/// The code action for a retry: the placeholder with its parameter list
/// rewritten to carry the raised limits. Bindings and every parameter the
/// retry does not set are kept verbatim. Requesting code actions again on
/// the edited placeholder runs the larger search.
pub fn retrySuggestion(
    allocator: std.mem.Allocator,
    proof_src: []const u8,
    application: RuleApplication,
    retry: miss.Retry,
) !SourceSuggestion {
    return .{
        .title = try std.fmt.allocPrint(allocator, "Retry with {f}", .{retry}),
        .replacement = try text_util.allocRender(
            allocator,
            writeRetryReplacement,
            .{ proof_src, application, retry },
        ),
        .replace_span = .{
            .start = application.rule_span.start,
            .end = (application.binding_list_span orelse
                application.rule_span).end,
        },
    };
}

/// The placeholder with its parameter list rewritten: bindings, then the
/// parameters `retry` leaves alone, then the ones it raises.
fn writeRetryReplacement(
    w: *std.Io.Writer,
    proof_src: []const u8,
    application: RuleApplication,
    retry: miss.Retry,
) std.Io.Writer.Error!void {
    try w.print("{s} (", .{application.rule_name});
    for (application.arg_bindings) |binding| {
        try w.print("{s}, ", .{proof_src[binding.span.start..binding.span.end]});
    }
    for (application.search_params) |param| {
        if (retry.sets(param.name)) continue;
        try w.print("{s}, ", .{proof_src[param.span.start..param.span.end]});
    }
    try w.print("{f})", .{retry});
}

const top_rules_lead = " Most-tried rules: ";

/// `detail` without the "Most-tried rules: ..." sentence that ends it, for
/// a caller that reports the rule tallies itself.
pub fn statusDetailWithoutRules(detail: []const u8) []const u8 {
    const end = std.mem.lastIndexOf(u8, detail, top_rules_lead) orelse
        detail.len;
    return detail[0..end];
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
            try w.writeAll(top_rules_lead);
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
