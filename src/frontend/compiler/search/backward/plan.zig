//! Per-hypothesis slot planning for backward search: decide the order in which
//! a candidate's hypothesis slots are filled. Builds a `HypPlan` per slot
//! (initial ref-pool lookup, constraint strength, recover dependencies) and
//! orders them by a fan-out-proxy cost so the most-constrained slots are tried
//! first. Also holds the template-binder mask helpers the ordering and the
//! generation paths share. Split out of `backtrack.zig`.

const std = @import("std");
const types = @import("../types.zig");
const ref_index_mod = @import("../ref_index.zig");
const match = @import("./match.zig");
const lookup_mod = @import("./lookup.zig");
const ExprId = @import("../../../expr.zig").ExprId;
const TheoremContext = @import("../../../expr.zig").TheoremContext;
const TemplateExpr = @import("../../../rules.zig").TemplateExpr;
const ArgInfo = @import("../../../parse_recovery.zig").ArgInfo;
const GlobalEnv = @import("../../../env.zig").GlobalEnv;
const RewriteRegistry = @import("../../../rewrite_registry.zig").RewriteRegistry;
const Context = types.Context;
const SearchCounters = types.SearchCounters;
const ApplyCandidate = types.ApplyCandidate;
const DerivedPool = types.DerivedPool;
const findRecoverSourceLocation = match.findRecoverSourceLocation;
const templateMentionsBinder = @import("../../../rules.zig").templateMentionsBinder;
const lookupHypReferences = lookup_mod.lookupHypReferences;

pub const HypPlan = struct {
    position: usize,
    initial_len: usize,
    /// Derived-pool slot candidates for a pool-empty slot, and ONLY when the
    /// pool carries `@auto trigger` seeds (`DerivedPool.has_seeds`, the
    /// phase-6 seeding retry). Zero everywhere else, so pre-seeding search
    /// plans are untouched. A seed is a ref for planning purposes: filling
    /// the slot pins the rule's premise-only binders exactly like a pool ref
    /// would, so a seed-fillable slot must sort with ref-like cost, not
    /// generate-only cost — otherwise the elimination MAJOR the seed
    /// determines sorts after its wide open minors and is never reached
    /// (the wildcard-vs-rigid inversion; see the trigger-seeding design
    /// note).
    seeded_len: usize,
    strength: usize,
    // True when this is a generate-only slot (a generator is present and no pool
    // ref fits it at seed time) that should be visited LAST so a sibling can pin
    // its binders first. We defer it only when an *app-structured*, ref-fillable
    // sibling shares one of this slot's still-unpinned binders — i.e. a sibling
    // that can actually pin it via ref matching (`auto_two_hyp_pin`: `N a`
    // deferred behind `L a`). Two cases are deliberately NOT deferred:
    //   * a slot with no unpinned binders (already concrete — e.g. a recursive
    //     intro like `all_intro` whose hyp is conclusion-pinned); and
    //   * a slot whose only ref-fillable siblings are bare binders (e.g. `mpbi`'s
    //     `p`), which match every ref and so don't usefully constrain — deferring
    //     behind them makes generation explore the wide slot first and explode.
    // (Regression guard: nested `all_intro [all_intro [all_intro [l4]]]`, where
    // deferring behind bare-binder hyps of bystander rules like `mpbi`/`bitr`
    // blew the per-depth node budget; see search_bench `nested all_intro`.)
    defer_generate: bool,
    // Phase-5 (constrained backward MP) occurrence ordering: true when this
    // slot's template is a *wildcard sequent* — an app whose every argument is
    // a bare, still-unpinned binder (e.g. `imp_elim`'s minor `?H ⊢ ?p`) — and a
    // sibling shares one of those unpinned binders under RIGID nested structure
    // (e.g. the major `?G ⊢ ?p → r`, where `p` sits under `im`). Sorted last
    // (first comparator key, above `defer_generate`): the shared meta's most
    // rigid occurrence is solved first, so the child search runs on the
    // constrained target (`? ⊢ ?p → r` only admits →-conclusions) instead of
    // the wildcard (`nd(?,?)` accepts every ref-tuple of every intro rule —
    // the cut-formula ACCEPT-flood). Because the DFS is sequential per
    // candidate, the ordering is also a gate: if the rigid sibling fails, the
    // wildcard slot is never opened. Set ONLY when `buildHypPlans` runs with
    // `constrained_mp` (phase 5), so phases 1–4 plans are byte-identical.
    defer_wildcard: bool,
};

pub fn buildHypPlans(
    allocator: std.mem.Allocator,
    context: *const Context,
    ref_index: *const ref_index_mod.Index,
    candidate: *const ApplyCandidate,
    generate_present: bool,
    constrained_mp: bool,
    derived: ?*DerivedPool,
    counters: ?*SearchCounters,
) ![]HypPlan {
    const rule = &context.env.rules.items[candidate.rule_id];
    const n = candidate.unresolved_hyps.len;
    const plans = try allocator.alloc(HypPlan, n);
    errdefer allocator.free(plans);

    // Per-slot scratch for the generate-deferral decision (second pass below).
    const slots = try allocator.alloc(SlotShape, n);
    defer allocator.free(slots);

    for (candidate.unresolved_hyps, 0..) |hyp, position| {
        var lookup = try lookupHypReferences(
            context,
            ref_index,
            null,
            candidate,
            candidate.bindings,
            position,
            .initial,
            0,
            false,
            counters,
        );
        defer lookup.deinit();
        const template = rule.hyps[hyp.index];
        const binders = templateBinderMask(template);
        const unpinned = unpinnedBinderMask(binders.mask, candidate.bindings);
        const rigid = if (constrained_mp)
            rigidNestedBinderMask(context.registry, template)
        else
            TemplateBinderMask{};
        slots[position] = .{
            .initial_len = lookup.pool.indices.len,
            .is_app = template == .app,
            .mask = binders.mask,
            .unpinned = unpinned,
            .overflow = binders.overflow,
            .wildcard = constrained_mp and
                isWildcardSequent(template, candidate.bindings),
            .rigid_mask = rigid.mask,
        };
        var seeded_len: usize = 0;
        if (lookup.pool.indices.len == 0) {
            if (derived) |dpool| {
                if (dpool.has_seeds) {
                    seeded_len = if (try derivedSlotCandidates(
                        context,
                        dpool,
                        candidate,
                        hyp.index,
                        counters,
                    )) |list| list.len else dpool.refs.len;
                }
            }
        }
        plans[position] = .{
            .position = position,
            .initial_len = lookup.pool.indices.len,
            .seeded_len = seeded_len,
            .strength = templateConstraintStrength(
                context.env,
                &candidate.theorem,
                template,
                rule.args,
                candidate.bindings,
            ),
            .defer_generate = false, // resolved in the second pass
            .defer_wildcard = false, // resolved in the second pass
        };
    }

    if (generate_present) {
        for (0..n) |i| {
            plans[i].defer_generate = shouldDeferGenerate(slots, i);
        }
    }
    if (constrained_mp) {
        for (0..n) |i| {
            plans[i].defer_wildcard = shouldDeferWildcard(slots, i);
        }
    }

    std.mem.sort(HypPlan, plans, {}, hypPlanLessThan);
    orderRecoverDeps(context, candidate, plans);
    return plans;
}

/// Slot-candidate derived refs for `(candidate.rule_id, hyp_index)`: the
/// derived-pool index queried with the slot's (view) hypothesis template and
/// ALL binders unbound — a superset of every dynamically-pinned lookup, so
/// one cached result soundly serves every goal, depth, and binding state in
/// the search (the per-ref structural match still arbitrates). Null means
/// "no filter" (no index, or the lookup failed): callers scan every derived
/// ref, the pre-index behavior.
pub fn derivedSlotCandidates(
    context: *const Context,
    dpool: *DerivedPool,
    candidate: *const ApplyCandidate,
    hyp_index: usize,
    counters: ?*SearchCounters,
) !?[]const usize {
    if (dpool.index == null) return null;
    const dref_index = &dpool.index.?;
    const key = (@as(u64, candidate.rule_id) << 32) | @as(u64, hyp_index);
    const map_allocator = dpool.arena.child_allocator;
    const gop = try dpool.slot_cache.getOrPut(map_allocator, key);
    if (gop.found_existing) return gop.value_ptr.*;
    // Record the failure outcome up front; overwritten on success below.
    gop.value_ptr.* = null;

    const rule = &context.env.rules.items[candidate.rule_id];
    var template: TemplateExpr = undefined;
    var args: []const ArgInfo = undefined;
    if (context.views.get(candidate.rule_id)) |view| {
        if (hyp_index >= view.hyps.len) return null;
        template = view.hyps[hyp_index];
        args = view.arg_infos;
    } else {
        if (hyp_index >= rule.hyps.len) return null;
        template = rule.hyps[hyp_index];
        args = rule.args;
    }
    const unbound = try context.allocator.alloc(?ExprId, args.len);
    defer context.allocator.free(unbound);
    @memset(unbound, null);
    var lookup = dref_index.lookupTemplate(
        &candidate.theorem,
        template,
        args,
        unbound,
        counters,
    ) catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
        else => return null,
    };
    defer lookup.deinit();
    const list = try dpool.arena.allocator().dupe(usize, lookup.indices);
    gop.value_ptr.* = list;
    return list;
}

const SlotShape = struct {
    initial_len: usize,
    is_app: bool,
    /// Binder indices the slot's template references (bit i = binder i).
    mask: u64,
    /// Subset of `mask` not yet bound in the candidate.
    unpinned: u64,
    /// A referenced binder index exceeded the 64-bit mask.
    overflow: bool,
    /// Wildcard sequent: the template is an app whose every argument is a
    /// bare, still-unpinned binder (`?H ⊢ ?p`). Computed only under
    /// `constrained_mp`, false otherwise. See `HypPlan.defer_wildcard`.
    wildcard: bool = false,
    /// Binders occurring under rigid nested structure (inside a non-ACUI app
    /// below the template's top-level app). Computed only under
    /// `constrained_mp`, zero otherwise. See `HypPlan.defer_wildcard`.
    rigid_mask: u64 = 0,
};

/// Whether generate-only slot `i` should be deferred to last. True only when an
/// app-structured, ref-fillable sibling shares one of slot `i`'s still-unpinned
/// binders, so that sibling can pin it via ref matching before generation runs.
/// See `HypPlan.defer_generate` for the rationale and the cases excluded.
fn shouldDeferGenerate(slots: []const SlotShape, i: usize) bool {
    const self = slots[i];
    if (self.initial_len != 0) return false; // ref-fillable, not generate-only
    // Rules with >64 binders fall back to the original "defer all generate-only"
    // behavior rather than risk a wrong mask-based decision.
    if (self.overflow) return true;
    if (self.unpinned == 0) return false; // already concrete — nothing to gain
    for (slots, 0..) |other, j| {
        if (j == i) continue;
        if (other.initial_len == 0) continue; // sibling can't be filled from a ref
        if (!other.is_app) continue; // bare-binder sibling doesn't usefully constrain
        if (other.overflow) return true;
        if (other.mask & self.unpinned != 0) return true;
    }
    return false;
}

/// Whether wildcard-sequent slot `i` should sort last under phase-5 occurrence
/// ordering: some sibling shares one of `i`'s unpinned binders under rigid
/// nested structure, so that sibling determines the shared meta on a
/// constrained child target before the wildcard is ever opened. See
/// `HypPlan.defer_wildcard`. Overflowed masks (binder index ≥ 64) disable the
/// demotion — a wrong ordering decision is worse than the flood.
fn shouldDeferWildcard(slots: []const SlotShape, i: usize) bool {
    const self = slots[i];
    if (!self.wildcard) return false;
    if (self.overflow or self.unpinned == 0) return false;
    for (slots, 0..) |other, j| {
        if (j == i) continue;
        if (other.overflow) continue; // rigid_mask may be incomplete
        if (other.rigid_mask & self.unpinned != 0) return true;
    }
    return false;
}

/// Wildcard sequent test for `HypPlan.defer_wildcard`: an app whose every
/// argument is a bare binder with no current binding. Instantiated, such a
/// template is rigid ONLY at its root — in a sequent-style theory that root
/// (`nd`, `has_ty`, …) is shared by every rule conclusion, so the open target
/// matches the entire catalog (`nd(?,?)` is the cut-formula-enumeration flood
/// shape). A pinned argument, or any nested app, keeps the slot out of this
/// class: it constrains the child match.
fn isWildcardSequent(template: TemplateExpr, bindings: []const ?ExprId) bool {
    switch (template) {
        .binder => return false,
        .app => |app| {
            if (app.args.len == 0) return false;
            for (app.args) |arg| switch (arg) {
                .app => return false,
                .binder => |idx| {
                    if (idx < bindings.len and bindings[idx] != null) {
                        return false;
                    }
                },
            };
            return true;
        },
    }
}

/// Binders of `template` occurring under rigid nested structure: inside an
/// argument subtree of the top-level app, below at least one app whose head
/// term is NOT an ACUI structural combiner. The top-level head is excluded
/// (every hypothesis of a sequent-style rule shares it — it discriminates
/// nothing), and ACUI combiners grant no rigidity (their matching is
/// associative/commutative with unit absorption, so a binder directly under
/// `join` is as loose as a top-level one; a binder under `hyp` inside `join`
/// IS rigid). `imp_elim`'s major `nd(G, im(p, q))` yields `{p, q}`.
fn rigidNestedBinderMask(
    registry: *const RewriteRegistry,
    template: TemplateExpr,
) TemplateBinderMask {
    var result = TemplateBinderMask{};
    switch (template) {
        .binder => {},
        .app => |app| for (app.args) |arg| {
            collectRigidNestedMask(registry, arg, false, &result);
        },
    }
    return result;
}

fn collectRigidNestedMask(
    registry: *const RewriteRegistry,
    template: TemplateExpr,
    under_rigid: bool,
    out: *TemplateBinderMask,
) void {
    switch (template) {
        .binder => |idx| {
            if (!under_rigid) return;
            if (idx >= 64) {
                out.overflow = true;
            } else {
                out.mask |= @as(u64, 1) << @intCast(idx);
            }
        },
        .app => |app| {
            const rigid = under_rigid or
                !registry.hasStructuralCombiner(app.term_id);
            for (app.args) |arg| {
                collectRigidNestedMask(registry, arg, rigid, out);
            }
        },
    }
}

/// Bitset of binder indices a template references, plus an overflow flag for any
/// index >= 64. Canonical implementation lives beside `TemplateExpr` in
/// `rules.zig` (the `@auto eager` annotation validation shares it); re-exported
/// here for the search-side users.
pub const TemplateBinderMask = @import("../../../rules.zig").TemplateBinderMask;

pub const templateBinderMask = @import("../../../rules.zig").templateBinderMask;

/// Binder indices occurring in `concl`, as a `conclusion_binders` mask for the
/// open-target instantiation (those binders are determined by the goal match
/// and must not be deferred as fresh metas). On binder-index overflow (≥ 64,
/// not representable) returns 0 — restricting nothing, the prior behaviour —
/// rather than risk masking a real binder.
pub fn conclusionBinderMaskOrNone(concl: TemplateExpr) u64 {
    const mask = templateBinderMask(concl);
    return if (mask.overflow) 0 else mask.mask;
}

fn unpinnedBinderMask(mask: u64, bindings: []const ?ExprId) u64 {
    var unpinned: u64 = 0;
    var m = mask;
    while (m != 0) {
        const idx: u6 = @intCast(@ctz(m));
        m &= m - 1;
        if (idx >= bindings.len or bindings[idx] == null) {
            unpinned |= @as(u64, 1) << idx;
        }
    }
    return unpinned;
}

/// A generate-only slot (`initial_len == 0`, no pool ref fits it at seed time) is
/// NOT cheapest to fill — it matches the whole *generation* space, a large
/// branching factor — so ranking it first (`0 < everything`) is wrong. We cost it
/// as `generate_only_cost` refs: it then sorts after a tightly-constrained ref slot
/// (`initial_len < 4`) and ahead of a wide one (`initial_len > 4`), with a slot of
/// exactly `initial_len == 4` tying and decided by the `strength`/`position`
/// tiebreaks below. This is a heuristic *fan-out proxy*, not an exact branching
/// estimate: a loose bare-binder slot is only reliably *wider* than generation
/// when its pool is large, so the ordering vs a small-pool bare-binder slot rests
/// on the `defer_generate` gate (which runs first) rather than on this cost. The
/// value 4 was swept against the depth frontier: it is the peak (peano 37,
/// zermelo_hilbert 117); higher costs plateau lower as gen-only is deferred behind
/// loose refs. Behavior is corpus-validated (breadth byte-identical, depth 301);
/// retuning it can shift depth-frontier results, so it is pinned by the `eq_euclid`
/// and `additive_fol`-total guards in `tests/frontier_guards.zig`.
const generate_only_cost: usize = 4;

fn hypSlotCost(plan: HypPlan) usize {
    if (plan.initial_len != 0) return plan.initial_len;
    // Seed-fillable slot (phase 6 only; see `HypPlan.seeded_len`): costed
    // like a ref slot of the same width.
    if (plan.seeded_len != 0) return plan.seeded_len;
    return generate_only_cost;
}

fn hypPlanLessThan(_: void, lhs: HypPlan, rhs: HypPlan) bool {
    // Phase-5 occurrence ordering, above every other key: a wildcard-sequent
    // slot goes after the rigid occurrences of its shared binders — including
    // after `defer_generate` slots, because the deferred generate-only major
    // IS the rigid occurrence that must determine the meta first (see
    // `HypPlan.defer_wildcard`). Always false outside phase 5.
    if (lhs.defer_wildcard != rhs.defer_wildcard) {
        return !lhs.defer_wildcard;
    }
    // Generate-only slots go last: they pin no binders for siblings and need
    // their own binders pinned first (see `HypPlan.defer_generate`).
    if (lhs.defer_generate != rhs.defer_generate) {
        return !lhs.defer_generate;
    }
    const lhs_cost = hypSlotCost(lhs);
    const rhs_cost = hypSlotCost(rhs);
    if (lhs_cost != rhs_cost) {
        return lhs_cost < rhs_cost;
    }
    if (lhs.strength != rhs.strength) return lhs.strength > rhs.strength;
    return lhs.position < rhs.position;
}

// Reorder a length-sorted plan so each `@recover` source hypothesis is visited
// only after the hypotheses that pin its pattern/hole binders. This is what lets
// the dynamic lookup inject the recover member shape (see
// `lookupHypReferencesViaView`): the pattern is resolved by then, so the index
// can filter the source hypothesis's context instead of leaving it to post-hoc
// validation. A stable greedy pass over the length order — it only moves a
// source later when a provider would otherwise follow it, preserving the
// most-constrained-first preference everywhere else. Ordering never changes
// which tuples validate, only the order they are explored.
fn orderRecoverDeps(
    context: *const Context,
    candidate: *const ApplyCandidate,
    plans: []HypPlan,
) void {
    const max_plans = 64;
    if (plans.len <= 1 or plans.len > max_plans) return;
    const view = context.views.get(candidate.rule_id) orelse return;
    if (view.derived_bindings.len == 0) return;

    // predecessors[i]: bitmask of plan slots that must precede slot i.
    var preds = [_]u64{0} ** max_plans;
    var any = false;
    for (view.derived_bindings) |derived| {
        const rec = switch (derived) {
            .recover => |r| r,
            .abstract => continue,
        };
        const loc = findRecoverSourceLocation(
            context,
            view,
            rec.source_view_idx,
        ) orelse continue;
        const source_slot = planSlotForHyp(candidate, plans, loc.hyp_index) orelse
            continue;
        for (plans, 0..) |plan, provider_slot| {
            if (provider_slot == source_slot) continue;
            const hyp = candidate.unresolved_hyps[plan.position];
            if (hyp.index >= view.hyps.len) continue;
            const provides_pattern =
                templateMentionsBinder(view.hyps[hyp.index], rec.pattern_view_idx) or
                templateMentionsBinder(view.hyps[hyp.index], rec.hole_view_idx);
            if (!provides_pattern) continue;
            preds[source_slot] |= @as(u64, 1) << @intCast(provider_slot);
            any = true;
        }
    }
    if (!any) return;

    var ordered: [max_plans]HypPlan = undefined;
    var placed: u64 = 0;
    var out: usize = 0;
    while (out < plans.len) : (out += 1) {
        var chosen: ?usize = null;
        for (0..plans.len) |slot| {
            const bit = @as(u64, 1) << @intCast(slot);
            if (placed & bit != 0) continue;
            // Available when all predecessors are already placed.
            if (preds[slot] & ~placed != 0) continue;
            chosen = slot;
            break;
        }
        // A cycle (shouldn't happen for well-formed recover laws) would leave
        // nothing available; fall back to the next length-best unplaced slot.
        const slot = chosen orelse blk: {
            for (0..plans.len) |s| {
                if (placed & (@as(u64, 1) << @intCast(s)) == 0) break :blk s;
            }
            break :blk 0;
        };
        ordered[out] = plans[slot];
        placed |= @as(u64, 1) << @intCast(slot);
    }
    @memcpy(plans, ordered[0..plans.len]);
}

fn planSlotForHyp(
    candidate: *const ApplyCandidate,
    plans: []const HypPlan,
    hyp_index: usize,
) ?usize {
    for (plans, 0..) |plan, slot| {
        if (candidate.unresolved_hyps[plan.position].index == hyp_index) {
            return slot;
        }
    }
    return null;
}

fn templateConstraintStrength(
    env: *const GlobalEnv,
    theorem: *const TheoremContext,
    template: TemplateExpr,
    args: []const ArgInfo,
    bindings: []const ?ExprId,
) usize {
    return switch (template) {
        .binder => |idx| blk: {
            if (idx >= bindings.len) break :blk 0;
            const expr_id = bindings[idx] orelse break :blk 0;
            break :blk exprConstraintStrength(env, theorem, expr_id);
        },
        .app => |app| blk: {
            var strength: usize = 1;
            for (app.args) |arg| {
                strength += templateConstraintStrength(
                    env,
                    theorem,
                    arg,
                    args,
                    bindings,
                );
            }
            break :blk strength;
        },
    };
}

fn exprConstraintStrength(
    env: *const GlobalEnv,
    theorem: *const TheoremContext,
    expr_id: ExprId,
) usize {
    const node = theorem.interner.node(expr_id);
    return switch (node.*) {
        .variable, .placeholder => 0,
        .app => |app| blk: {
            var strength: usize = 1;
            for (app.args) |arg| strength += exprConstraintStrength(
                env,
                theorem,
                arg,
            );
            break :blk strength;
        },
    };
}

// ---------------------------------------------------------------------------
// Tests (phase-5 occurrence ordering helpers)
// ---------------------------------------------------------------------------

const testing = std.testing;

// Template literals for an `imp_elim`-shaped rule over binders
// 0=G, 1=H, 2=p, 3=q: conclusion `G u H |- q`, major `G |- p -> q`,
// minor `H |- p`. Term ids: 10=nd (sequent head), 11=im, 12=join, 13=hyp.
const t_G = TemplateExpr{ .binder = 0 };
const t_H = TemplateExpr{ .binder = 1 };
const t_p = TemplateExpr{ .binder = 2 };
const t_q = TemplateExpr{ .binder = 3 };
const t_im_pq = TemplateExpr{ .app = .{ .term_id = 11, .args = &.{ t_p, t_q } } };
const t_major = TemplateExpr{ .app = .{ .term_id = 10, .args = &.{ t_G, t_im_pq } } };
const t_minor = TemplateExpr{ .app = .{ .term_id = 10, .args = &.{ t_H, t_p } } };
const t_hyp_p = TemplateExpr{ .app = .{ .term_id = 13, .args = &.{t_p} } };
const t_join_G_hyp_p = TemplateExpr{ .app = .{
    .term_id = 12,
    .args = &.{ t_G, t_hyp_p },
} };
const t_or_minor = TemplateExpr{ .app = .{
    .term_id = 10,
    .args = &.{ t_join_G_hyp_p, t_q },
} };

test "isWildcardSequent classifies bare-unpinned-arg apps only" {
    const none = [_]?ExprId{ null, null, null, null };
    // `?H |- ?p`: every arg a bare unpinned binder -> wildcard.
    try testing.expect(isWildcardSequent(t_minor, &none));
    // Nested app arg (`?G |- ?p -> ?q`) -> not wildcard.
    try testing.expect(!isWildcardSequent(t_major, &none));
    // A pinned argument -> not wildcard.
    var pinned_p = none;
    pinned_p[2] = 7;
    try testing.expect(!isWildcardSequent(t_minor, &pinned_p));
    // Bare binder template and nullary app -> not wildcard.
    try testing.expect(!isWildcardSequent(t_p, &none));
    const nullary = TemplateExpr{ .app = .{ .term_id = 10, .args = &.{} } };
    try testing.expect(!isWildcardSequent(nullary, &none));
}

test "rigidNestedBinderMask skips the top level and ACUI combiners" {
    // The registry has no deinit (it is arena-backed in production); give it
    // a test-local arena so the map allocations are reclaimed.
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    var registry = RewriteRegistry.init(arena.allocator());
    // `join` (term 12) is the ACUI context combiner.
    try registry.acui_by_head.put(12, .{
        .unit_term_name = "emp",
        .assoc_name = "join_assoc",
        .comm_name = null,
        .idem_name = null,
    });

    // Major `nd(G, im(p, q))`: G is a top-level arg (not rigid); p, q sit
    // under the nested rigid `im`.
    const major = rigidNestedBinderMask(&registry, t_major);
    try testing.expect(!major.overflow);
    try testing.expectEqual(@as(u64, 0b1100), major.mask);

    // Minor `nd(H, p)`: no nested structure at all.
    const minor = rigidNestedBinderMask(&registry, t_minor);
    try testing.expectEqual(@as(u64, 0), minor.mask);

    // `nd(join(G, hyp(p)), q)`: G sits only under the ACUI `join` (loose),
    // p is under the rigid `hyp` inside it, q is top-level.
    const or_minor = rigidNestedBinderMask(&registry, t_or_minor);
    try testing.expectEqual(@as(u64, 0b0100), or_minor.mask);
}

test "shouldDeferWildcard demotes the wildcard minor behind the rigid major" {
    // Slot 0 = minor `?H |- ?p` (wildcard, matches the whole pool), slot 1 =
    // major `?G |- ?p -> r` (generate-only, rigid occurrence of the shared
    // `p`). The minor must defer; the major must not.
    const slots = [_]SlotShape{
        .{
            .initial_len = 3,
            .is_app = true,
            .mask = 0b0110,
            .unpinned = 0b0110,
            .overflow = false,
            .wildcard = true,
            .rigid_mask = 0,
        },
        .{
            .initial_len = 0,
            .is_app = true,
            .mask = 0b1101,
            .unpinned = 0b0101,
            .overflow = false,
            .wildcard = false,
            .rigid_mask = 0b0100,
        },
    };
    try testing.expect(shouldDeferWildcard(&slots, 0));
    try testing.expect(!shouldDeferWildcard(&slots, 1));

    // No rigid occurrence of a shared binder anywhere -> no demotion.
    var loose = slots;
    loose[1].rigid_mask = 0b1000; // rigid only at a binder the minor lacks
    try testing.expect(!shouldDeferWildcard(&loose, 0));

    // Overflowed sibling masks are incomplete -> conservative, no demotion.
    var overflowed = slots;
    overflowed[1].overflow = true;
    try testing.expect(!shouldDeferWildcard(&overflowed, 0));
}

test "hypPlanLessThan sorts defer_wildcard last, above defer_generate" {
    const wildcard_minor = HypPlan{
        .position = 0,
        .initial_len = 3,
        .seeded_len = 0,
        .strength = 1,
        .defer_generate = false,
        .defer_wildcard = true,
    };
    const generate_major = HypPlan{
        .position = 1,
        .initial_len = 0,
        .seeded_len = 0,
        .strength = 3,
        .defer_generate = true,
        .defer_wildcard = false,
    };
    // The deferred-generate major still sorts BEFORE the wildcard minor: it
    // is the rigid occurrence that determines the shared meta.
    try testing.expect(hypPlanLessThan({}, generate_major, wildcard_minor));
    try testing.expect(!hypPlanLessThan({}, wildcard_minor, generate_major));
}
