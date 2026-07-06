//! Speculative ACUI context splitting for *generated* multiplicative subproofs.
//!
//! A rule whose conclusion combines two or more contexts under a registered ACUI
//! combiner — e.g. `union_intro` (`Γ ⊢ a, Δ ⊢ b ⟹ Γ,Δ ⊢ …`), `ex_elim`,
//! `or_elim` — leaves a hypothesis context binder (`Γ`/`Δ`/`Σ`) open whenever the
//! subproof for that hypothesis must be *generated* rather than discharged from
//! the ref pool. Generation needs a concrete context, so it bails
//! (`backtrack.zig` `instantiateTemplateIfConcrete` returns null).
//!
//! This module proposes concrete values for such an open binder by distributing
//! the goal's concrete context members across the conclusion's combiner spine
//! binders. Splitting is inherently speculative — `H ∪ K = ctx` only bounds each
//! half (`H ⊇ ctx∖upper(others)`, `H ⊆ ctx`); pinning siblings tightens the
//! interval but never forces a value. We therefore enumerate within the interval,
//! ordered minimal-first so the common no-contraction split is tried first, and
//! let the ordinary `tryCandidate` validator confirm soundness (it does the real
//! member-level ACUI check). Restriction to small contexts + the global fuel
//! floor + iterative deepening keep the fan-out bounded.

const std = @import("std");
const types = @import("../types.zig");
const UsizeShift = std.math.Log2Int(usize);
const acui = @import("./acui.zig");
const plan = @import("./plan.zig");
const ExprId = @import("../../../expr.zig").ExprId;
const TheoremContext = @import("../../../expr.zig").TheoremContext;
const TemplateExpr = @import("../../../rules.zig").TemplateExpr;
const Context = types.Context;

/// Distinct-member and spine-binder caps. Contexts at a split point are small in
/// practice; a larger one simply skips the split (falls back to today's
/// no-generation behaviour) rather than risk a `2^n` blow-up.
const max_members = 8;
const max_spine = 8;
/// Optional (non-required) members enumerated as subsets. Caps the candidate
/// count at `2^max_optional`.
const max_optional = 6;
const max_masks = 1 << max_optional;

/// Where a conclusion's ACUI combiner aligns with the goal: the concrete goal
/// subterm holding the members to distribute, the combiner head, and the spine
/// binder indices (the direct bare-binder summands).
pub const SplitSite = struct {
    container: ExprId,
    head_id: u32,
    spine: [max_spine]usize = undefined,
    spine_len: usize = 0,
    /// Structured (non-binder) summands of the combiner spine — the principal
    /// formulas an additive rule writes alongside the open context rests, e.g.
    /// `im(a,b)` in `rim`'s succedent `(a→b), d`. Each claims one goal member
    /// (matched read-only with the conclusion seed's bindings); the remaining
    /// members are what the open spine binder distributes over.
    fixed: [max_spine]TemplateExpr = undefined,
    fixed_len: usize = 0,
};

/// True when `concl` combines two or more distinct template binders under a
/// registered ACUI combiner — i.e. the rule is "multiplicative" and a hypothesis
/// of it may need a speculative context split. Used to order non-splitting
/// (additive) rule candidates first, so a goal solvable without splitting claims
/// the generation budget before split-capable rules explore (regression guard:
/// nested `all_intro`, where split-capable bystanders would otherwise starve it).
pub fn conclusionIsSplit(context: *const Context, concl: TemplateExpr) bool {
    switch (concl) {
        .binder => return false,
        .app => |app| {
            if (context.registry.acui_by_head.contains(app.term_id)) {
                const binders = plan.templateBinderMask(concl);
                if (binders.overflow or @popCount(binders.mask) >= 2) return true;
            }
            for (app.args) |arg| {
                if (conclusionIsSplit(context, arg)) return true;
            }
            return false;
        },
    }
}

/// Locate the ACUI combiner in `concl` that references rule binder `binder_idx`,
/// returning the aligned concrete goal subterm. Walks `concl` against `goal_expr`
/// in parallel, descending matching non-ACUI app heads positionally (the same
/// alignment `partialMatchTemplate` uses). Returns null when no combiner spine
/// references the binder, when the goal shape diverges, or when the combiner has
/// a non-binder summand (a concrete required member) — a current limitation:
/// that case is left to the existing non-split behaviour.
pub fn findSplitSite(
    context: *const Context,
    theorem: *const TheoremContext,
    concl: TemplateExpr,
    goal_expr: ExprId,
    binder_idx: usize,
) ?SplitSite {
    switch (concl) {
        .binder => return null,
        .app => |app| {
            if (context.registry.acui_by_head.contains(app.term_id)) {
                if (!templateRefsBinder(concl, binder_idx)) return null;
                var site = SplitSite{ .container = goal_expr, .head_id = app.term_id };
                if (!collectSpine(concl, app.term_id, &site)) return null;
                return site;
            }
            const node = theorem.interner.node(goal_expr);
            switch (node.*) {
                .app => |concrete| {
                    if (concrete.term_id != app.term_id) return null;
                    if (concrete.args.len != app.args.len) return null;
                    for (app.args, concrete.args) |targ, carg| {
                        if (findSplitSite(context, theorem, targ, carg, binder_idx)) |s| {
                            return s;
                        }
                    }
                    return null;
                },
                else => return null,
            }
        },
    }
}

/// True when every binder leaf of `template` already has a value in `bindings`,
/// so the template instantiates to a concrete expression (used to decide whether
/// a fixed principal summand can claim a goal member with an exact read-only
/// match rather than a wildcard one).
pub fn templateFullyBound(template: TemplateExpr, bindings: []const ?ExprId) bool {
    return switch (template) {
        .binder => |idx| idx < bindings.len and bindings[idx] != null,
        .app => |app| blk: {
            for (app.args) |arg| {
                if (!templateFullyBound(arg, bindings)) break :blk false;
            }
            break :blk true;
        },
    };
}

fn templateRefsBinder(template: TemplateExpr, idx: usize) bool {
    return switch (template) {
        .binder => |i| i == idx,
        .app => |app| blk: {
            for (app.args) |arg| {
                if (templateRefsBinder(arg, idx)) break :blk true;
            }
            break :blk false;
        },
    };
}

/// Collect the combiner spine's summands: bare binders become spine entries that
/// distribute container members; structured (non-binder) summands are recorded as
/// `fixed` principals that each claim one member. Returns false only if either
/// array overflows `max_spine` (then the split is skipped).
fn collectSpine(template: TemplateExpr, head_id: u32, site: *SplitSite) bool {
    switch (template) {
        .binder => |idx| {
            if (site.spine_len >= site.spine.len) return false;
            site.spine[site.spine_len] = idx;
            site.spine_len += 1;
            return true;
        },
        .app => |app| {
            if (app.term_id != head_id) {
                // A structured principal summand (e.g. `a→b` in `(a→b), d`). The
                // additive rule keeps it on this side; it claims one goal member,
                // and the open spine binder distributes the rest. Recording it
                // (rather than bailing) is what makes additive rule hypotheses
                // with an open context rest generatable.
                if (site.fixed_len >= site.fixed.len) return false;
                site.fixed[site.fixed_len] = template;
                site.fixed_len += 1;
                return true;
            }
            for (app.args) |arg| {
                if (!collectSpine(arg, head_id, site)) return false;
            }
            return true;
        },
    }
}

/// Enumerates candidate concrete contexts for one open spine binder, ordered
/// minimal-first (fewest members). Each candidate is a sub-multiset of the
/// container's distinct members within the binder's `[lower, upper]` interval.
pub const SplitEnumerator = struct {
    members: [max_members]ExprId = undefined,
    member_len: usize = 0,
    head_id: u32 = 0,
    masks: [max_masks]u64 = undefined,
    mask_len: usize = 0,

    pub fn count(self: *const SplitEnumerator) usize {
        return self.mask_len;
    }

    /// Build the `i`-th candidate context expression in `theorem`'s interner.
    /// Returns null for the empty selection when the combiner has no unit term
    /// (an empty context is then unrepresentable, so the caller skips it).
    pub fn candidate(
        self: *const SplitEnumerator,
        context: *const Context,
        theorem: *TheoremContext,
        i: usize,
    ) !?ExprId {
        const mask = self.masks[i];
        var chosen: [max_members]ExprId = undefined;
        var n: usize = 0;
        var b: usize = 0;
        while (b < self.member_len) : (b += 1) {
            if (mask & (@as(u64, 1) << @as(u6, @intCast(b))) != 0) {
                chosen[n] = self.members[b];
                n += 1;
            }
        }
        if (n == 0) {
            const unit = acui.acuiUnitIdForHead(context, self.head_id) orelse
                return null;
            return try theorem.interner.internApp(unit, &.{});
        }
        if (n == 1) return chosen[0];
        // Right-fold into binary combiner applications, preserving order.
        var result = chosen[n - 1];
        var k = n - 1;
        while (k > 0) {
            k -= 1;
            result = try theorem.interner.internApp(self.head_id, &.{ chosen[k], result });
        }
        return result;
    }
};

/// Build the enumerator for open binder `target_b` at `site`. Computes the
/// interval: `upper` = all container members; `lower` (required) = members no
/// *other* spine binder can cover (an open sibling can cover anything; a bound
/// sibling covers exactly its own members). Returns null — skip the split — when
/// the container is empty/oversized or the optional set is too large to enumerate.
pub fn buildEnumerator(
    context: *const Context,
    theorem: *const TheoremContext,
    site: SplitSite,
    bindings: []const ?ExprId,
    target_b: usize,
    retain_claimed: bool,
) ?SplitEnumerator {
    var en = SplitEnumerator{ .head_id = site.head_id };
    var all: [max_members]ExprId = undefined;
    var all_len: usize = 0;
    if (!flattenDistinct(theorem, site.container, site.head_id, &all, &all_len)) {
        return null;
    }
    const had_members = all_len > 0;

    // Under an idempotent combiner (`g , g = g`) a goal member may sit in BOTH a
    // fixed principal summand AND the open rest binder, so claimed members below
    // are retained as OPTIONAL rest members instead of removed. Non-idempotent
    // subsets (AU / ACU) keep the additive-minimal reading: a claimed member is
    // removed from the rest's distribution. Gated on the declared `@acui` idem
    // axiom (subset soundness) AND `retain_claimed` — the principal-retaining
    // split broadens every additive node, so the driver only enables it in a
    // final phase on a clean miss (see `GenerationHook.allow_retain_principal`).
    const retain = retain_claimed and
        if (context.registry.acui_by_head.get(site.head_id)) |c|
            c.idem_name != null
        else
            false;

    // Members claimed by structured principal summands. Each fully-bound fixed
    // summand that uniquely matches one remaining member claims it (the principal
    // already sits on this side). A partially-bound or ambiguous summand claims
    // nothing — the validator's ACUI weakening still confirms the assembly.
    var claimed = [_]bool{false} ** max_members;
    var f: usize = 0;
    while (f < site.fixed_len) : (f += 1) {
        const ftmpl = site.fixed[f];
        if (!templateFullyBound(ftmpl, bindings)) continue;
        var match_idx: ?usize = null;
        var matches: usize = 0;
        var mi: usize = 0;
        while (mi < all_len) : (mi += 1) {
            if (claimed[mi]) continue;
            if (acui.templateMatchesExprReadOnly(theorem, ftmpl, all[mi], bindings)) {
                matches += 1;
                match_idx = mi;
            }
        }
        if (matches == 1) claimed[match_idx.?] = true;
    }

    // Collect the rest binder's distributable members. Claimed members are
    // dropped under a non-idempotent combiner; under idempotency they are kept
    // and marked optional (`optional_claimed`) so the minimal claimed-excluded
    // split is still enumerated first, with the principal-retaining split behind.
    var optional_claimed: u64 = 0;
    var mi: usize = 0;
    while (mi < all_len) : (mi += 1) {
        if (claimed[mi]) {
            if (!retain) continue;
            optional_claimed |= (@as(u64, 1) << @as(u6, @intCast(en.member_len)));
        }
        en.members[en.member_len] = all[mi];
        en.member_len += 1;
    }

    // A genuinely empty container offers no split. But a container whose members
    // were *all* claimed by fixed principals leaves the open rest forced to the
    // unit (e.g. rim's succedent `d = emp`) — emit that single candidate, provided
    // the combiner has a representable unit.
    if (en.member_len == 0) {
        if (!had_members) return null;
        if (acui.acuiUnitIdForHead(context, site.head_id) == null) return null;
    }

    // Required mask: members that no other spine binder can cover.
    var required: u64 = 0;
    var m: usize = 0;
    while (m < en.member_len) : (m += 1) {
        const member = en.members[m];
        var coverable = false;
        var s: usize = 0;
        while (s < site.spine_len) : (s += 1) {
            const bidx = site.spine[s];
            if (bidx == target_b) continue;
            if (bidx >= bindings.len or bindings[bidx] == null) {
                coverable = true; // an open sibling can absorb this member
                break;
            }
            if (memberInValue(theorem, bindings[bidx].?, site.head_id, member)) {
                coverable = true;
                break;
            }
        }
        if (!coverable) required |= (@as(u64, 1) << @as(u6, @intCast(m)));
    }
    // Claimed members are covered by the fixed principal, so the open rest never
    // *requires* them — keep them strictly optional (idempotent retention only).
    required &= ~optional_claimed;

    // Optional members (may or may not also sit in target_b): enumerate subsets.
    // Unclaimed optionals first, so that if the optional budget is exceeded it is
    // the idempotent-retained claimed members that are dropped — this keeps the
    // non-idempotent candidate set byte-identical and only ever *adds* the
    // principal-retaining splits, within budget.
    var opt_bits: [max_members]usize = undefined;
    var opt_n: usize = 0;
    var t: usize = 0;
    while (t < en.member_len) : (t += 1) {
        const bit = @as(u64, 1) << @as(u6, @intCast(t));
        if (required & bit != 0) continue;
        if (optional_claimed & bit != 0) continue;
        opt_bits[opt_n] = t;
        opt_n += 1;
    }
    if (opt_n > max_optional) return null;
    t = 0;
    while (t < en.member_len and opt_n < max_optional) : (t += 1) {
        const bit = @as(u64, 1) << @as(u6, @intCast(t));
        if (optional_claimed & bit == 0) continue;
        opt_bits[opt_n] = t;
        opt_n += 1;
    }

    const subsets = @as(usize, 1) << @as(UsizeShift, @intCast(opt_n));
    var idx: usize = 0;
    while (idx < subsets) : (idx += 1) {
        var mask = required;
        var j: usize = 0;
        while (j < opt_n) : (j += 1) {
            if (idx & (@as(usize, 1) << @as(UsizeShift, @intCast(j))) != 0) {
                mask |= (@as(u64, 1) << @as(u6, @intCast(opt_bits[j])));
            }
        }
        en.masks[en.mask_len] = mask;
        en.mask_len += 1;
    }
    // Minimal-first: try the fewest-member (disjoint) splits before the
    // overlapping (contraction) ones.
    std.sort.insertion(u64, en.masks[0..en.mask_len], {}, lessPopcount);
    return en;
}

fn lessPopcount(_: void, a: u64, b: u64) bool {
    return @popCount(a) < @popCount(b);
}

/// Flatten the ACUI multiset rooted at `container` into distinct members (by
/// hash-cons `ExprId` equality — idempotency makes duplicates redundant).
/// Returns false on overflow (caller skips the split).
fn flattenDistinct(
    theorem: *const TheoremContext,
    container: ExprId,
    head_id: u32,
    buf: *[max_members]ExprId,
    count: *usize,
) bool {
    switch (theorem.interner.node(container).*) {
        .app => |app| {
            if (app.term_id == head_id) {
                for (app.args) |arg| {
                    if (!flattenDistinct(theorem, arg, head_id, buf, count)) return false;
                }
                return true;
            }
        },
        else => {},
    }
    for (buf[0..count.*]) |existing| {
        if (existing == container) return true; // dedupe
    }
    if (count.* >= buf.len) return false;
    buf[count.*] = container;
    count.* += 1;
    return true;
}

/// Does the ACUI context `value` contain `member` as one of its flattened
/// members?
fn memberInValue(
    theorem: *const TheoremContext,
    value: ExprId,
    head_id: u32,
    member: ExprId,
) bool {
    if (value == member) return true;
    switch (theorem.interner.node(value).*) {
        .app => |app| {
            if (app.term_id == head_id) {
                for (app.args) |arg| {
                    if (memberInValue(theorem, arg, head_id, member)) return true;
                }
            }
        },
        else => {},
    }
    return false;
}
