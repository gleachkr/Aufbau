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
//! A rule variable the goal leaves open is a fresh named unknown (`?a`)
//! when its sort has an `@unknown` prefix, so the premises that mention it
//! share it by name; a named unknown in the goal keeps its name. Any other
//! part still unknown is written with its sort's `@hole` token; a rule that
//! would need a hole in a sort without one is not offered. A
//! `@fresh` variable a stated premise mentions is written as a binding
//! (`freshPins`).

const std = @import("std");
const types = @import("../types.zig");
const ExprId = @import("../../../expr.zig").ExprId;
const TheoremContext = @import("../../../expr.zig").TheoremContext;
const ProofScript = @import("../../../proof_script.zig");
const TextUtil = @import("../../../text_util.zig");
const OpenTerms = @import("../../inference/open_terms.zig");
const OpenGoals = @import("../../check/open_goals.zig");
const mintHintHole = @import("../../check/inline_hints.zig").mintHintHole;
const Ref = ProofScript.Ref;
const ProofLine = ProofScript.ProofLine;
const RuleApplication = ProofScript.RuleApplication;
const ApplyCandidate = types.ApplyCandidate;
const RuleDecl = @import("../../../env.zig").RuleDecl;
const TrustedParser = @FieldType(@import("../../../parse_recovery.zig").MM0Parser, "core");
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
    // Only a line states its premises, so only a line names their unknowns.
    const names: ?NameSet = if (site.top_level) try unknownNames(allocator, site) else null;
    var planned = std.ArrayListUnmanaged(Planned).empty;
    for (candidates) |*candidate| {
        if (try plan(allocator, site, pool, labels, names, candidate)) |p| {
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
    /// The unknown names the proof uses, on a line; null inline.
    names: ?NameSet,
    candidate: *ApplyCandidate,
) !?Planned {
    const rule = &site.context.env.rules.items[candidate.rule_id];
    const premises = rule.hyps;
    // The probe ran only rules with as many premises as are written, checked
    // the facts they cite and folded those into the bindings.
    const written = site.marker.refs;
    const theorem = &candidate.theorem;
    const bindings = if (names) |used|
        try nameOpenBinders(allocator, site, rule, candidate, used)
    else
        candidate.bindings;
    // A premise the probe settled names what was renamed the same way as
    // the premises still open.
    const renamed = !std.mem.eql(?ExprId, bindings, candidate.bindings);

    // The open premises, written out when the `?` is a line of its own.
    var open_lines = std.ArrayListUnmanaged(u8).empty;
    var labels: ProofScript.FreshLabels = .{
        .base = block_labels.base,
        .used = try block_labels.used.clone(allocator),
    };
    var tier: u2 = 0;
    var refs = std.ArrayListUnmanaged(u8).empty;
    // The first `?` the action writes, in `open_lines` on a line, in `refs`
    // inline.
    var first_open: ?usize = null;
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
            if (first_open == null) first_open = refs.items.len;
            try refs.append(allocator, '?');
            continue;
        }
        const settled = if (renamed) null else concrete;
        const statement = settled orelse (try OpenTerms.instantiateTemplateHoley(
            theorem,
            site.context.env,
            site.context.registry,
            rule,
            premise,
            bindings,
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
        if (first_open == null) first_open = open_lines.items.len - "?\n".len;
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
            .cursor = if (first_open) |at| rule.name.len + pins.len + " [".len + at else null,
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
            .cursor = first_open,
        },
        .tier = tier,
    };
}

/// `candidate.bindings` with each variable the goal leaves open, in a sort
/// with an `@unknown` prefix, a new named unknown: the prefix and the
/// variable's name (`?a`), or with a number after it (`?a1`, …) when the
/// proof uses that name already (`used`). A variable whose name would not
/// read back as an unknown of its sort stays open. One that stands where the goal has
/// a part with a hole in it is that part, which the probe bound it to, names
/// included; a bare anonymous hole says nothing a new name would not, so a
/// variable bound to one is named too.
fn nameOpenBinders(
    allocator: std.mem.Allocator,
    site: Site,
    rule: *const RuleDecl,
    candidate: *ApplyCandidate,
    used: NameSet,
) ![]const ?ExprId {
    const parser = &site.context.parser.core;
    const bindings = try allocator.dupe(?ExprId, candidate.bindings);
    if (parser.sort_unknown_prefixes.count() == 0) return bindings;
    var minted = std.ArrayListUnmanaged([]const u8).empty;
    for (rule.args, rule.arg_names, 0..) |arg, arg_name, idx| {
        if (idx >= bindings.len or arg.bound) continue;
        if (bindings[idx]) |bound| if (!isAnonymousHole(&candidate.theorem, bound)) continue;
        const prefix = parser.sort_unknown_prefixes.get(arg.sort_name) orelse continue;
        const base = arg_name orelse continue;
        const name = (try freshUnknown(allocator, parser, prefix, base, used, minted.items)) orelse continue;
        try minted.append(allocator, name);
        bindings[idx] = try candidate.theorem.addNamedLineHolePlaceholder(arg.sort_name, name);
    }
    return bindings;
}

fn isAnonymousHole(theorem: *const TheoremContext, expr: ExprId) bool {
    const pid = switch (theorem.interner.node(expr).*) {
        .placeholder => |pid| pid,
        .app, .variable => return false,
    };
    const info = theorem.placeholderInfo(pid) orelse return false;
    return info.line_hole and info.name == null;
}

/// `prefix` and `base`, numbered when `used` or `minted` already has that
/// name. Null when the token would not read as an unknown with `prefix`.
fn freshUnknown(
    allocator: std.mem.Allocator,
    parser: *const TrustedParser,
    prefix: []const u8,
    base: []const u8,
    used: NameSet,
    minted: []const []const u8,
) !?[]const u8 {
    for (base) |c| {
        if (parser.left_delims[c] or parser.right_delims[c]) return null;
    }
    var number: usize = 0;
    while (true) : (number += 1) {
        const name = if (number == 0)
            try std.mem.concat(allocator, u8, &.{ prefix, base })
        else
            try std.fmt.allocPrint(allocator, "{s}{s}{d}", .{ prefix, base, number });
        const read = parser.unknownPrefixOf(name) orelse return null;
        if (!std.mem.eql(u8, read, prefix) or parser.hole_tokens.contains(name)) return null;
        if (!used.contains(name) and !hasName(minted, name)) return name;
    }
}

/// Names of unknowns, as written.
const NameSet = std.StringHashMapUnmanaged(void);

/// The unknown names the `?`'s proof writes: every token of a statement or
/// a binding value, inline applications' included, that reads as a named
/// unknown.
fn unknownNames(allocator: std.mem.Allocator, site: Site) !NameSet {
    var names: NameSet = .empty;
    const parser = &site.context.parser.core;
    if (parser.sort_unknown_prefixes.count() == 0) return names;
    for (site.block_lines) |line| {
        try addUnknownNames(allocator, parser, &names, line.assertion.text);
        try addApplicationNames(allocator, parser, &names, line.application);
    }
    return names;
}

fn addApplicationNames(
    allocator: std.mem.Allocator,
    parser: *const TrustedParser,
    names: *NameSet,
    application: RuleApplication,
) !void {
    for (application.arg_bindings) |binding| {
        try addUnknownNames(allocator, parser, names, binding.formula.text);
    }
    for (application.refs) |ref| switch (ref) {
        .application => |child| try addApplicationNames(allocator, parser, names, child),
        .hyp, .line => {},
    };
}

fn addUnknownNames(
    allocator: std.mem.Allocator,
    parser: *const TrustedParser,
    names: *NameSet,
    math: []const u8,
) !void {
    var tokens: TextUtil.MathTokenCursor = .{
        .src = math,
        .left_delims = parser.left_delims,
        .right_delims = parser.right_delims,
    };
    while (tokens.next()) |token| {
        if (parser.unknownPrefixOf(token.text) != null) try names.put(allocator, token.text, {});
    }
}

fn hasName(names: []const []const u8, name: []const u8) bool {
    for (names) |other| {
        if (std.mem.eql(u8, other, name)) return true;
    }
    return false;
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
