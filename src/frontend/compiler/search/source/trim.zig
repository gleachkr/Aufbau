//! Trimming a found application's bindings to the ones the checker cannot
//! infer, by asking the checker (`BindingOracle`) whether the line still
//! checks without each.

const std = @import("std");
const timer = @import("../timer.zig");
const ProofScript = @import("../../../proof_script.zig");
const RuleApplication = ProofScript.RuleApplication;
const Ref = ProofScript.Ref;
const BindingOracle = @import("../../context.zig").BindingOracle;
const source_mod = @import("../source.zig");
const SuggestionSite = source_mod.SuggestionSite;

/// `app` without the explicit bindings the checker does not need, or
/// `app` itself when trimming fails (`trimBindings`).
pub fn withNeededBindings(
    allocator: std.mem.Allocator,
    site: SuggestionSite,
    app: RuleApplication,
) !RuleApplication {
    return (try trimBindings(allocator, site, app)) orelse app;
}

/// Drop the explicit bindings of `app` the checker does not need. The search
/// renders every binder it chose (existential metas, bound witnesses, ACUI
/// split and principal choices) so that its own validation cannot misread
/// them; most of them the checker re-derives from the refs and the goal.
/// The bare application, with every binding dropped, is tried first.
/// Failing that, a check with the bindings withheld behind a
/// `BindingOracle` keeps the ones the checker takes from the search
/// (`SuggestionSite.neededBindings`), and one more validates the result;
/// should that fail, the oracle checks again with the kept bindings stated,
/// as the suggestion will state them. Each binding the oracle supplied
/// over-approximately is then dropped if the line checks without it. The
/// result has been validated. Null, with `app` unchecked, when it has no
/// bindings, the checks budget runs out, or the oracle check fails; the last
/// counts as untrimmed (`SearchCounters.untrimmed`), which no corpus line may
/// be. Allocates on the per-call work arena and frees nothing.
pub fn trimBindings(
    allocator: std.mem.Allocator,
    site: SuggestionSite,
    app: RuleApplication,
) !?RuleApplication {
    const start = timer.timestampIf(site.counters != null);
    defer if (site.counters) |counters| {
        counters.trim_ns += timer.elapsedSince(start);
    };
    var list = std.ArrayListUnmanaged(*const ProofScript.ArgBinding).empty;
    try appendPreorderBindings(allocator, &list, app);
    const bindings = list.items;
    if (bindings.len == 0) return null;
    const drop = try allocator.alloc(bool, bindings.len);
    @memset(drop, true);
    const bare = try withBindingsDropped(allocator, app, drop);
    if (try site.validates(allocator, bare)) return bare;
    const coarse = try allocator.alloc(bool, bindings.len);
    @memset(coarse, false);
    // Every check that takes a binding keeps at least one more, so this
    // ends.
    while (try site.neededBindings(allocator, app, bindings, drop, coarse)) |took| {
        if (!took or try site.validates(allocator, try withBindingsDropped(allocator, app, drop))) {
            // A check the budget cut short only keeps a binding.
            try site.dropCoarse(allocator, app, drop, coarse);
            return try withBindingsDropped(allocator, app, drop);
        }
        if (site.budgets.checksExhausted()) return null;
    }
    // A check the budget cut short failed for want of work, not bindings.
    if (site.budgets.checksExhausted()) return null;
    if (site.counters) |counters| counters.untrimmed += 1;
    return null;
}

/// `app`'s bindings in preorder (an application's own, then each nested
/// ref's), the order a `drop` mask indexes.
fn appendPreorderBindings(
    allocator: std.mem.Allocator,
    out: *std.ArrayListUnmanaged(*const ProofScript.ArgBinding),
    app: RuleApplication,
) !void {
    for (app.arg_bindings) |*binding| try out.append(allocator, binding);
    for (app.refs) |ref| switch (ref) {
        .application => |child| try appendPreorderBindings(allocator, out, child),
        .hyp, .line => {},
    };
}

/// A copy of `app` without the bindings `drop` selects, indexed in preorder
/// (`appendPreorderBindings`).
pub fn withBindingsDropped(
    allocator: std.mem.Allocator,
    app: RuleApplication,
    drop: []const bool,
) !RuleApplication {
    var next: usize = 0;
    return withBindingsDroppedFrom(allocator, app, drop, &next, null);
}

/// `withBindingsDropped`, registering with `oracle`, if given, each
/// application's full list against what the copy still states.
pub fn withBindingsDroppedFrom(
    allocator: std.mem.Allocator,
    app: RuleApplication,
    drop: []const bool,
    next: *usize,
    oracle: ?*BindingOracle,
) !RuleApplication {
    var copy = app;
    var kept = std.ArrayListUnmanaged(ProofScript.ArgBinding).empty;
    for (app.arg_bindings) |binding| {
        if (!drop[next.*]) try kept.append(allocator, binding);
        next.* += 1;
    }
    // A slice of its own (the original's, when empty), so the oracle can key
    // on it.
    copy.arg_bindings = if (kept.items.len == 0) app.arg_bindings[0..0] else kept.items;
    if (kept.items.len == 0) copy.binding_list_span = null;
    if (oracle) |o| if (app.arg_bindings.len != 0) {
        try o.register(copy.arg_bindings, app.arg_bindings);
    };
    const refs = try allocator.dupe(Ref, app.refs);
    for (refs) |*ref| switch (ref.*) {
        .application => |child| ref.* = .{
            .application = try withBindingsDroppedFrom(allocator, child, drop, next, oracle),
        },
        .hyp, .line => {},
    };
    copy.refs = refs;
    return copy;
}
