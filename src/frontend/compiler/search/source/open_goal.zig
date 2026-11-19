//! The code actions on an open goal `?`: apply a rule whose conclusion
//! matches the goal, or, on a line with a concrete statement, admit it with
//! `sorry!`.
//!
//! Applying a rule cites, for each premise the goal and the references
//! fix completely, a theorem hypothesis or earlier line that states it, and
//! leaves the other premises open. On a line they become new `?` lines above
//! it, with the premise as their statement; inline they become `?` in place.
//! A premise still partly unknown is never closed: which fact it should cite
//! is a choice, not something the goal decides. References written on the
//! `?` (`? [l1, ?]`) make that choice: they are the rule's premises in order,
//! and the rule is probed with the facts they cite, so it must accept them
//! and what they fix can complete the others (`ApplyOptions.premises`).
//!
//! A premise still partly unknown is written with its sort's `@hole` token;
//! a rule that would need a hole in a sort without one is not offered. A
//! `@fresh` variable a stated premise mentions is written as a binding
//! (`freshPins`).

const std = @import("std");
const types = @import("../types.zig");
const ExprId = @import("../../../expr.zig").ExprId;
const TheoremContext = @import("../../../expr.zig").TheoremContext;
const ProofScript = @import("../../../proof_script.zig");
const OpenTerms = @import("../../inference/open_terms.zig");
const OpenGoals = @import("../../check/open_goals.zig");
const mintHintHole = @import("../../check/inline_hints.zig").mintHintHole;
const Ref = ProofScript.Ref;
const ProofLine = ProofScript.ProofLine;
const RuleApplication = ProofScript.RuleApplication;
const ApplyCandidate = types.ApplyCandidate;
const Context = types.Context;
const Goal = types.Goal;
const SourceSuggestion = types.SourceSuggestion;

/// Where the `?` stands.
pub const Site = struct {
    proof_src: []const u8,
    /// The lines of its block, for fresh labels and the facts before it.
    block_lines: []const ProofLine,
    line_index: usize,
    /// The `?` itself: the line's application, or an inline one in it.
    marker: RuleApplication,
    /// Whether the `?` justifies the whole line.
    top_level: bool,
    context: *const Context,
    theorem: *const TheoremContext,
};

/// The actions for the `?` at `site`, at most `max_results` rule
/// applications (those the facts close completely first, then those whose
/// open premises are all concrete, then the rest, each group in the order
/// of `candidates`), then the `sorry!` admission when `goal` is concrete.
/// `candidates` were probed with the `?`'s refs (`ApplyOptions.premises`).
/// Allocates from `allocator` without freeing: give it an arena.
pub fn actions(
    allocator: std.mem.Allocator,
    site: Site,
    candidates: []ApplyCandidate,
    goal: Goal,
    max_results: usize,
) ![]const SourceSuggestion {
    var items = std.ArrayListUnmanaged(SourceSuggestion).empty;
    const pool = try facts(allocator, site);
    const labels = try ProofScript.FreshLabels.init(
        allocator,
        site.block_lines[site.line_index].label,
        site.block_lines,
    );
    var planned = std.ArrayListUnmanaged(Planned).empty;
    for (candidates) |*candidate| {
        if (try plan(allocator, site, pool, labels, candidate)) |p| {
            try planned.append(allocator, p);
        }
    }
    // Stable: each tier keeps the order of `candidates`.
    std.mem.sort(Planned, planned.items, {}, Planned.lessThan);
    for (planned.items[0..@min(max_results, planned.items.len)]) |p| {
        try items.append(allocator, p.suggestion);
    }

    if (site.top_level and goal == .concrete) {
        try items.append(allocator, .{
            .title = "Admit with sorry!",
            .replacement = "sorry!",
            .replace_span = site.marker.span,
        });
    }
    return try items.toOwnedSlice(allocator);
}

const Planned = struct {
    suggestion: SourceSuggestion,
    /// 0: every premise cited; 1: every open premise concrete; 2: some
    /// open premise partly unknown.
    tier: u2,

    fn lessThan(_: void, lhs: Planned, rhs: Planned) bool {
        return lhs.tier < rhs.tier;
    }
};

/// A fact a premise may cite.
const Fact = struct {
    expr: ExprId,
    /// The reference as written in the proof.
    text: []const u8,
};

/// The theorem's hypotheses, then the lines before the `?` that can be
/// cited, in source order.
fn facts(allocator: std.mem.Allocator, site: Site) ![]const Fact {
    var out = std.ArrayListUnmanaged(Fact).empty;
    for (site.theorem.theorem_hyps.items, 0..) |expr, idx| {
        try out.append(allocator, .{
            .expr = expr,
            .text = try std.fmt.allocPrint(allocator, "#{d}", .{idx + 1}),
        });
    }
    for (site.block_lines[0..site.line_index]) |line| {
        const line_idx = site.context.labels.get(line.label) orelse continue;
        if (line_idx >= site.context.checked.items.len) continue;
        try out.append(allocator, .{
            .expr = site.context.checked.items[line_idx].expr,
            .text = line.label,
        });
    }
    return try out.toOwnedSlice(allocator);
}

/// The action applying `candidate`, or null when an open premise cannot be
/// written.
fn plan(
    allocator: std.mem.Allocator,
    site: Site,
    pool: []const Fact,
    block_labels: ProofScript.FreshLabels,
    candidate: *ApplyCandidate,
) !?Planned {
    const rule = &site.context.env.rules.items[candidate.rule_id];
    const premises = rule.hyps;
    // The probe ran only rules with as many premises as are written, checked
    // the facts they cite and folded those into the bindings.
    const written = site.marker.refs;
    const theorem = &candidate.theorem;

    // The open premises, written out when the `?` is a line of its own.
    var open_lines = std.ArrayListUnmanaged(u8).empty;
    var labels: ProofScript.FreshLabels = .{
        .base = block_labels.base,
        .used = try block_labels.used.clone(allocator),
    };
    var tier: u2 = 0;
    var refs = std.ArrayListUnmanaged(u8).empty;
    // The variables the premises this action states mention: the facts it
    // cites and the lines it adds.
    var stated_deps: u55 = 0;
    for (premises, candidate.unresolved_hyps, 0..) |premise, unresolved, idx| {
        if (idx != 0) try refs.appendSlice(allocator, ", ");
        // A ref written on the `?` stays as written, unless it is a `?`.
        if (written.len != 0) {
            const ref = written[idx];
            if (ref != .application or
                !ProofScript.isOpenGoalRuleName(ref.application.rule_name))
            {
                try refs.appendSlice(allocator, refText(site.proof_src, ref));
                continue;
            }
        }
        // An open premise: closed by a fact if one states it.
        const concrete = unresolved.expected;
        const known = if (concrete) |expr| !theorem.containsPlaceholder(expr) else false;
        if (known) if (factStating(pool, concrete.?)) |text| {
            try refs.appendSlice(allocator, text);
            stated_deps |= try theorem.exprDeps(concrete.?, .{});
            continue;
        };
        tier = @max(tier, @as(u2, if (known) 1 else 2));
        if (!site.top_level) {
            try refs.append(allocator, '?');
            continue;
        }
        const statement = concrete orelse (try OpenTerms.instantiateTemplateHoley(
            theorem,
            site.context.env,
            site.context.registry,
            rule,
            premise,
            candidate.bindings,
            .{ .placeholder_factory = .{ .makeFn = mintHintHole } },
        ) orelse return null);
        const text = (try OpenGoals.formatStatement(
            allocator,
            theorem,
            site.context.env,
            site.context.parser,
            &candidate.theorem_vars,
            statement,
        )) orelse return null;
        stated_deps |= try theorem.exprDeps(statement, .{});
        const label = try labels.next(allocator);
        try open_lines.print(allocator, "{s}{s}: $ {s} $ by ?\n", .{
            indentOf(site),
            label,
            text,
        });
        try refs.appendSlice(allocator, label);
    }

    const pins = (try freshPins(allocator, site, candidate, stated_deps)) orelse return null;
    const application = if (premises.len == 0)
        try std.fmt.allocPrint(allocator, "{s}{s}{s}", .{
            rule.name,
            pins,
            if (site.top_level) "" else " []",
        })
    else
        try std.fmt.allocPrint(allocator, "{s}{s} [{s}]", .{ rule.name, pins, refs.items });
    const title = try std.fmt.allocPrint(allocator, "Apply {s}", .{application});
    if (!site.top_level) return .{
        .suggestion = .{
            .title = title,
            .replacement = application,
            .replace_span = site.marker.span,
        },
        .tier = tier,
    };

    // The line itself keeps its label, statement and whatever follows the
    // application (a comment, the newline).
    const line = site.block_lines[site.line_index];
    try open_lines.print(allocator, "{s}{s}: {s} by {s}{s}", .{
        indentOf(site),
        line.label,
        site.proof_src[line.assertion.span.start..line.assertion.span.end],
        application,
        site.proof_src[line.application.span.end..line.span.end],
    });
    return .{
        .suggestion = .{
            .title = title,
            .replacement = try open_lines.toOwnedSlice(allocator),
            .replace_span = line.span,
        },
        .tier = tier,
    };
}

/// The bindings `candidate` must write for its `@fresh` binders: each one
/// whose variable a premise the action states mentions (`stated_deps`), as
/// ` (x := $ y $)`. The checker picks a `@fresh` variable absent from the
/// line's references, so it would pick another one there. Null when a
/// variable cannot be written.
fn freshPins(
    allocator: std.mem.Allocator,
    site: Site,
    candidate: *ApplyCandidate,
    stated_deps: u55,
) !?[]const u8 {
    const fresh = site.context.fresh_bindings.get(candidate.rule_id) orelse return "";
    const rule = &site.context.env.rules.items[candidate.rule_id];
    var pins = std.ArrayListUnmanaged(u8).empty;
    for (fresh) |decl| {
        const value = candidate.bindings[decl.target_arg_idx] orelse continue;
        if ((try candidate.theorem.exprDeps(value, .{})) & stated_deps == 0) continue;
        const text = (try OpenGoals.formatStatement(
            allocator,
            &candidate.theorem,
            site.context.env,
            site.context.parser,
            &candidate.theorem_vars,
            value,
        )) orelse return null;
        try pins.print(allocator, "{s}{s} := $ {s} $", .{
            if (pins.items.len == 0) " (" else ", ",
            rule.arg_names[decl.target_arg_idx].?,
            text,
        });
    }
    if (pins.items.len != 0) try pins.append(allocator, ')');
    return pins.items;
}

/// The first fact in `pool` that states `expr`.
fn factStating(pool: []const Fact, expr: ExprId) ?[]const u8 {
    for (pool) |fact| {
        if (fact.expr == expr) return fact.text;
    }
    return null;
}

fn refText(proof_src: []const u8, ref: Ref) []const u8 {
    const span = switch (ref) {
        .hyp => |hyp| hyp.span,
        .line => |line| line.span,
        .application => |app| app.span,
    };
    return proof_src[span.start..span.end];
}

fn indentOf(site: Site) []const u8 {
    const line = site.block_lines[site.line_index];
    return site.proof_src[line.span.start..line.label_span.start];
}
