//! `@auto trigger` seed harvesting for the `auto?` seeding retry phase.
//!
//! Each trigger annotation is a pattern e-matched (structurally) against the
//! subterms of the original goal. Every match grounds the annotated rule's
//! binders; binders the pattern does not name default to their sort's ACUI
//! unit (validated at annotation time). The resulting fully concrete rule
//! instance — for `ax`: `φ ⊢ φ` per harvested formula φ — is minted as a
//! *seed*: a sourceless `DerivedRef` that enters the derived pool (backward
//! use) and the forward-saturation frontier (joins). Seeding operationalizes
//! the subformula property: cut-free proofs use only subformulas of the
//! end-sequent, so identity axioms over goal subterms enumerate exactly the
//! analytic leaf set the backward search cannot otherwise invent (the
//! elimination-major "left rule" gap).
//!
//! Bounded and forced: one pass over the original goal only (no re-trigger
//! on generated subgoals), O(goal size × patterns) matches, ground instances
//! only. Soundness rides on the ordinary discipline — a seed is a search
//! hint whose materialized application (`by ax`, binders inferred from the
//! slot) is re-checked by `tryCandidate` at the point of use; a useless seed
//! is just a pool entry nobody selects.

const std = @import("std");
const types = @import("./types.zig");
const acui = @import("./backward/acui.zig");
const ExprId = @import("../../expr.zig").ExprId;
const TheoremContext = @import("../../expr.zig").TheoremContext;
const MetaStore = @import("../inference/meta_store.zig").MetaStore;
const OpenTerms = @import("../inference/open_terms.zig");
const TriggerPattern = @import("../../rewrite_registry.zig").TriggerPattern;

const Context = types.Context;
const DerivedRef = types.DerivedRef;

/// Harvest ground seed instances for every `@auto trigger` rule against the
/// subterms of `goal_expr`. Returns an `allocator`-owned slice of sourceless
/// `DerivedRef`s (all recipe slices empty; shapes interned in `theorem`),
/// deduped by (rule, shape) and deterministically ordered: rules ascending
/// by id, then annotation order, then goal-subterm DFS order.
pub fn harvestSeeds(
    context: *const Context,
    theorem: *TheoremContext,
    goal_expr: ExprId,
    allocator: std.mem.Allocator,
) ![]DerivedRef {
    var seeds = std.ArrayListUnmanaged(DerivedRef){};
    errdefer seeds.deinit(allocator);

    // Deterministic rule order (hash-map iteration order is not part of the
    // byte-identical contract).
    var rule_ids = std.ArrayListUnmanaged(u32){};
    defer rule_ids.deinit(allocator);
    var key_it = context.registry.trigger_by_rule.keyIterator();
    while (key_it.next()) |rule_id| {
        try rule_ids.append(allocator, rule_id.*);
    }
    std.mem.sort(u32, rule_ids.items, {}, std.sort.asc(u32));
    if (rule_ids.items.len == 0) return try seeds.toOwnedSlice(allocator);

    // Goal subterms in DFS order, deduped (hash-consing makes ExprId
    // identity expression identity). Only apps are collected: a trigger
    // pattern's root always names a term head.
    var subterms = std.ArrayListUnmanaged(ExprId){};
    defer subterms.deinit(allocator);
    var visited = std.AutoHashMapUnmanaged(ExprId, void){};
    defer visited.deinit(allocator);
    try collectAppSubterms(theorem, goal_expr, allocator, &visited, &subterms);

    // Lazily resolved unit expression per binder sort (the default for
    // pattern-unnamed context binders).
    var units = std.StringHashMapUnmanaged(?ExprId){};
    defer units.deinit(allocator);

    const SeedKey = struct { rule_id: u32, shape: ExprId };
    var minted = std.AutoHashMapUnmanaged(SeedKey, void){};
    defer minted.deinit(allocator);

    for (rule_ids.items) |rule_id| {
        const rule = &context.env.rules.items[rule_id];
        const patterns =
            context.registry.trigger_by_rule.get(rule_id) orelse continue;
        const bindings = try allocator.alloc(?ExprId, rule.args.len);
        defer allocator.free(bindings);

        for (patterns.items) |pattern| {
            subterm: for (subterms.items) |subterm| {
                @memset(bindings, null);
                if (!matchTriggerPattern(theorem, pattern, subterm, bindings)) {
                    continue;
                }
                // Default the unnamed binders to their sort's ACUI unit;
                // annotation validation guarantees a unit sort, but a
                // missing/unresolvable unit term just skips the match.
                for (bindings, rule.args) |*binding, arg| {
                    if (binding.* != null) continue;
                    if (arg.bound) continue :subterm;
                    binding.* = (try unitExprForSort(
                        context,
                        theorem,
                        &units,
                        allocator,
                        arg.sort_name,
                    )) orelse continue :subterm;
                }
                const concl = (try OpenTerms.instantiateTemplateConcrete(
                    theorem,
                    rule.concl,
                    bindings,
                )) orelse continue;
                // Unit-normalize so the seed states the surface form goals
                // and slots actually use (`G, φ ⊢ φ` at `G := emp` becomes
                // `φ ⊢ φ`, not a dangling `join emp …`).
                const shape = acui.normalizeAcuiUnits(
                    context,
                    theorem,
                    concl,
                ) catch concl;

                const gop = try minted.getOrPut(
                    allocator,
                    .{ .rule_id = rule_id, .shape = shape },
                );
                if (gop.found_existing) continue;
                try seeds.append(allocator, .{
                    .rule_id = rule_id,
                    .rule_name = rule.name,
                    .declaration_order = rule_id,
                    .sources = &.{},
                    .shape = shape,
                    // No explicit bindings: the rendered application is a
                    // bare rule reference whose binders the checker infers
                    // from the slot's expected sequent.
                    .bindings = &.{},
                    .required_metas = &.{},
                    .pinned_metas = &.{},
                    .has_universal_meta = false,
                    .source_depth = 0,
                });
            }
        }
    }
    return try seeds.toOwnedSlice(allocator);
}

/// A derived pool holding only seeds, for theories with `@auto trigger`
/// rules but no `@auto forward` rules (no saturation to ride on).
pub fn seedOnlyPool(
    context: *const Context,
    seeds: []const DerivedRef,
) !types.DerivedPool {
    var pool = types.DerivedPool{
        .arena = std.heap.ArenaAllocator.init(context.allocator),
        .store = MetaStore.init(context.allocator, context.env),
    };
    errdefer pool.deinit();
    pool.refs = try pool.arena.allocator().dupe(DerivedRef, seeds);
    pool.has_seeds = seeds.len > 0;
    return pool;
}

fn collectAppSubterms(
    theorem: *const TheoremContext,
    expr_id: ExprId,
    allocator: std.mem.Allocator,
    visited: *std.AutoHashMapUnmanaged(ExprId, void),
    out: *std.ArrayListUnmanaged(ExprId),
) anyerror!void {
    const gop = try visited.getOrPut(allocator, expr_id);
    if (gop.found_existing) return;
    switch (theorem.interner.node(expr_id).*) {
        .variable, .placeholder => {},
        .app => |app| {
            try out.append(allocator, expr_id);
            for (app.args) |arg| {
                try collectAppSubterms(theorem, arg, allocator, visited, out);
            }
        },
    }
}

/// Structural pattern match against one subterm. `binder` captures fill
/// `bindings`; a repeated binder must capture the identical expression
/// (hash-consed ExprId equality). No rollback needed: the caller resets
/// `bindings` per attempt. A capture that would embed a placeholder is
/// rejected — seeds are ground by contract (the goal is concrete on this
/// path, so this is belt-and-braces).
fn matchTriggerPattern(
    theorem: *const TheoremContext,
    pattern: TriggerPattern,
    expr_id: ExprId,
    bindings: []?ExprId,
) bool {
    switch (pattern) {
        .wildcard => return true,
        .binder => |idx| {
            if (idx >= bindings.len) return false;
            if (exprEmbedsPlaceholder(theorem, expr_id)) return false;
            if (bindings[idx]) |existing| return existing == expr_id;
            bindings[idx] = expr_id;
            return true;
        },
        .app => |papp| {
            const app = switch (theorem.interner.node(expr_id).*) {
                .app => |a| a,
                else => return false,
            };
            if (app.term_id != papp.term_id) return false;
            if (app.args.len != papp.args.len) return false;
            for (papp.args, app.args) |child, arg| {
                if (!matchTriggerPattern(theorem, child, arg, bindings)) {
                    return false;
                }
            }
            return true;
        },
    }
}

fn exprEmbedsPlaceholder(
    theorem: *const TheoremContext,
    expr_id: ExprId,
) bool {
    return switch (theorem.interner.node(expr_id).*) {
        .variable => false,
        .placeholder => true,
        .app => |app| blk: {
            for (app.args) |arg| {
                if (exprEmbedsPlaceholder(theorem, arg)) break :blk true;
            }
            break :blk false;
        },
    };
}

/// The nullary unit expression of the ACUI combiner returning `sort_name`,
/// memoized per sort. Smallest combiner head wins when several combiners
/// share a sort (deterministic; annotation validation makes this a
/// pathological case anyway). Null when no unit resolves — the match is
/// skipped.
fn unitExprForSort(
    context: *const Context,
    theorem: *TheoremContext,
    units: *std.StringHashMapUnmanaged(?ExprId),
    allocator: std.mem.Allocator,
    sort_name: []const u8,
) !?ExprId {
    if (units.get(sort_name)) |cached| return cached;
    var best_head: ?u32 = null;
    var best_unit_name: []const u8 = undefined;
    var it = context.registry.acui_by_head.iterator();
    while (it.next()) |entry| {
        const head = entry.key_ptr.*;
        if (head >= context.env.terms.items.len) continue;
        const term = &context.env.terms.items[head];
        if (!std.mem.eql(u8, term.ret_sort_name, sort_name)) continue;
        if (best_head == null or head < best_head.?) {
            best_head = head;
            best_unit_name = entry.value_ptr.unit_term_name;
        }
    }
    const result: ?ExprId = blk: {
        if (best_head == null) break :blk null;
        const unit_term_id = context.env.term_names.get(best_unit_name) orelse
            break :blk null;
        break :blk try theorem.interner.internApp(unit_term_id, &.{});
    };
    try units.put(allocator, sort_name, result);
    return result;
}
