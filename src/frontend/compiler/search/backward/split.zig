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
//! binders. What a candidate may hold depends on the combiner's laws (`bag.Law`):
//!   * a set (ACUI) splits with overlap — `H ∪ K = ctx` only bounds each half
//!     (`H ⊇ ctx∖upper(others)`, `H ⊆ ctx`) — so we enumerate sub-sets within
//!     that interval;
//!   * a multiset (ACU) splits by count: a candidate is a sub-multiset of what
//!     the bound siblings and principals leave, forced when no sibling is open;
//!   * a sequence (AU) splits by position: a candidate is one contiguous run,
//!     pinned at each end the summands before and after it fix exactly.
//! Candidates are tried smallest first, so the common no-contraction split comes
//! first, and the ordinary `tryCandidate` validator confirms each one (it does
//! the real member-level ACUI check). A site with more than `max_candidates`
//! candidates skips the split; the global fuel floor and iterative deepening
//! bound the rest.

const std = @import("std");
const types = @import("../types.zig");
const acui = @import("./acui.zig");
const bag = @import("./bag.zig");
const semantic = @import("./semantic.zig");
const ExprId = @import("../../../expr.zig").ExprId;
const TheoremContext = @import("../../../expr.zig").TheoremContext;
const TemplateExpr = @import("../../../rules.zig").TemplateExpr;
const Context = types.Context;

/// Summands of one conclusion spine. Rule conclusions combine a handful.
const max_spine = 8;
/// Candidates one split may try. Sub-bags grow as `2^optional`, so a site with
/// more candidates than this skips the split rather than risk the blow-up.
const max_candidates = 64;

/// Where a conclusion's ACUI combiner aligns with the goal: the concrete goal
/// subterm holding the members to distribute, the combiner head, and the spine
/// binder indices (the direct bare-binder summands).
pub const SplitSite = struct {
    container: ExprId,
    head_id: u32,
    /// The conclusion's combiner subterm, whose summand order a sequence split
    /// reads.
    template: TemplateExpr,
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

/// True when `concl` combines two or more distinct context binders as bare
/// summands of a registered ACUI combiner — i.e. the rule is "multiplicative"
/// and a hypothesis of it may need a speculative context split. A binder inside
/// a structured summand (the `a` of `g , ¬ a`) is a principal formula, not a
/// context, so such an additive rule does not count. Used to order non-splitting
/// (additive) rule candidates first, so a goal solvable without splitting claims
/// the generation budget before split-capable rules explore (regression guard:
/// nested `all_intro`, where split-capable bystanders would otherwise starve it).
pub fn conclusionIsSplit(context: *const Context, concl: TemplateExpr) bool {
    switch (concl) {
        .binder => return false,
        .app => |app| {
            if (context.registry.acui_by_head.contains(app.term_id)) {
                var site = SplitSite{ .container = undefined, .head_id = app.term_id, .template = concl };
                if (!collectSpine(context, &site)) return true;
                var seen: u64 = 0;
                for (site.spine[0..site.spine_len]) |idx| {
                    if (idx >= 64) return true;
                    seen |= @as(u64, 1) << @intCast(idx);
                }
                if (@popCount(seen) >= 2) return true;
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
/// in parallel, descending matching non-ACUI app heads positionally. Returns null
/// when the binder is not a bare summand of the combiner spine or when the goal
/// shape diverges.
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
                var site = SplitSite{ .container = goal_expr, .head_id = app.term_id, .template = concl };
                if (!collectSpine(context, &site)) return null;
                // Only a bare spine binder distributes context members. A
                // binder inside a fixed summand (the `A` of `g , x : A`) is not
                // a context, and enumerating contexts for it is ill-sorted.
                for (site.spine[0..site.spine_len]) |idx| {
                    if (idx == binder_idx) return site;
                }
                return null;
            }
            // Every arg of a same-head app, not just the determined ones (see
            // `lockstep`): a site under a `@rewrite` head or a dropped def arg is
            // only a guess, but the split pass merely adds candidates, and the
            // validator checks each one.
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

/// Collect the combiner spine's summands (units dropped): bare binders become
/// spine entries that distribute container members; structured (non-binder)
/// summands are recorded as `fixed` principals that each claim one member.
/// Returns false only if either array overflows `max_spine` (then the split is
/// skipped).
fn collectSpine(context: *const Context, site: *SplitSite) bool {
    const summands = bag.flattenTemplate(context, site.head_id, site.template) orelse
        return false;
    for (summands.slice()) |summand| switch (summand) {
        .binder => |idx| {
            if (site.spine_len == max_spine) return false;
            site.spine[site.spine_len] = idx;
            site.spine_len += 1;
        },
        // A structured principal summand (e.g. `a→b` in `(a→b), d`). The
        // additive rule keeps it on this side; it claims one goal member, and
        // the open spine binder distributes the rest. Recording it (rather than
        // bailing) is what makes additive rule hypotheses with an open context
        // rest generatable.
        .app => {
            if (site.fixed_len == max_spine) return false;
            site.fixed[site.fixed_len] = summand;
            site.fixed_len += 1;
        },
    };
    return true;
}

/// True when `hyp` restates every fixed principal summand of `site` as a
/// summand of its own `site.head_id` combiner holding the split binder `b`,
/// as `rex`'s premise `[x/t] p , (∃ x p) , d` restates `∃ x p`. Retaining a
/// claimed member in the open rest then only duplicates it, and a set
/// combiner identifies that premise with the non-retaining split's. (An
/// ordered idempotent combiner does not: `a , b , a` need not equal `a , b`.)
pub fn hypRestatesPrincipals(
    context: *const Context,
    site: SplitSite,
    hyp: TemplateExpr,
    b: usize,
) bool {
    if (site.fixed_len == 0) return false;
    if (bag.lawOf(context, site.head_id) != .set) return false;
    const summands = summandsHolding(context, hyp, site.head_id, b) orelse return false;
    for (site.fixed[0..site.fixed_len]) |principal| {
        for (summands.slice()) |summand| {
            if (summand.eql(principal)) break;
        } else return false;
    }
    return true;
}

/// The summands of the outermost `head_id` combiner in `template` that has
/// binder `b` as a summand: the context `b` stands for, not another one
/// (a two-sided sequent has two).
fn summandsHolding(
    context: *const Context,
    template: TemplateExpr,
    head_id: u32,
    b: usize,
) ?bag.TemplateBag {
    const app = switch (template) {
        .binder => return null,
        .app => |app| app,
    };
    if (app.term_id == head_id) {
        if (bag.flattenTemplate(context, head_id, template)) |summands| {
            for (summands.slice()) |summand| switch (summand) {
                .binder => |idx| if (idx == b) return summands,
                .app => {},
            };
        }
    }
    for (app.args) |arg| {
        if (summandsHolding(context, arg, head_id, b)) |found| return found;
    }
    return null;
}

/// Enumerates candidate concrete contexts for one open spine binder, smallest
/// first. Each candidate is a mask over `members`, the goal's members in order.
pub const SplitEnumerator = struct {
    members: bag.ExprBag = .{},
    head_id: u32 = 0,
    masks: [max_candidates]u64 = undefined,
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
        var chosen: [bag.capacity]ExprId = undefined;
        var n: usize = 0;
        for (self.members.slice(), 0..) |member, b| {
            if (self.masks[i] & bit(b) != 0) {
                chosen[n] = member;
                n += 1;
            }
        }
        return bag.build(context, theorem, self.head_id, chosen[0..n]);
    }

    fn push(self: *SplitEnumerator, mask: u64) bool {
        if (self.mask_len == max_candidates) return false;
        self.masks[self.mask_len] = mask;
        self.mask_len += 1;
        return true;
    }
};

/// Build the enumerator for open binder `target_b` at `site`, or null — skip the
/// split — when a bag overflows or the site has more than `max_candidates`
/// candidates.
pub fn buildEnumerator(
    context: *const Context,
    theorem: *const TheoremContext,
    site: SplitSite,
    bindings: []const ?ExprId,
    target_b: usize,
    retain_claimed: bool,
) ?SplitEnumerator {
    const law = bag.lawOf(context, site.head_id) orelse return null;
    const goal = bag.flatten(context, theorem, site.head_id, site.container) orelse
        return null;
    var en = SplitEnumerator{ .head_id = site.head_id };
    const ok = switch (law) {
        .set => enumerateSet(context, theorem, site, bindings, target_b, retain_claimed, goal, &en),
        .multiset => enumerateMultiset(context, theorem, site, bindings, target_b, goal, &en),
        .sequence, .idempotent_sequence => enumerateSequence(
            context,
            theorem,
            site,
            bindings,
            target_b,
            retain_claimed and law.isIdempotent(),
            goal,
            &en,
        ),
    };
    if (!ok) return null;
    std.sort.insertion(u64, en.masks[0..en.mask_len], {}, lessPopcount);
    return en;
}

/// Set (ACUI) split: sub-sets of the distinct members within the target's
/// interval. `upper` is every member (idempotency lets siblings overlap);
/// `lower` (required) is what no *other* spine binder can cover (an open
/// sibling can cover anything; a bound sibling covers exactly its own members).
fn enumerateSet(
    context: *const Context,
    theorem: *const TheoremContext,
    site: SplitSite,
    bindings: []const ?ExprId,
    target_b: usize,
    retain_claimed: bool,
    goal: bag.ExprBag,
    en: *SplitEnumerator,
) bool {
    var distinct = bag.ExprBag{};
    for (goal.slice()) |member| _ = distinct.appendDistinct(member);
    var free = [_]bool{true} ** bag.capacity;
    claimPrincipals(theorem, site, bindings, distinct.slice(), free[0..distinct.len]);

    // A goal member may sit in BOTH a fixed principal summand AND the open rest
    // binder (`g , g = g`), so with `retain_claimed` claimed members stay as
    // OPTIONAL rest members instead of being removed. That principal-retaining
    // split broadens every additive node, so the driver enables it only in
    // phases 4–5: at depth 1, and deeper only after the core misses (see
    // `GenerationHook.allow_retain_principal`).
    var optional_claimed: u64 = 0;
    for (distinct.slice(), 0..) |member, i| {
        if (!free[i]) {
            if (!retain_claimed) continue;
            optional_claimed |= bit(en.members.len);
        }
        _ = en.members.append(member);
    }

    var covered = bag.ExprBag{};
    const covers_all = siblingsCover(context, theorem, site, bindings, target_b, &covered);
    var required: u64 = 0;
    if (!covers_all) {
        for (en.members.slice(), 0..) |member, m| {
            if (std.mem.indexOfScalar(ExprId, covered.slice(), member) == null)
                required |= bit(m);
        }
    }
    // Claimed members are covered by the fixed principal, so the open rest never
    // *requires* them.
    required &= ~optional_claimed;

    // Optional members (may or may not also sit in the target): enumerate
    // subsets. Unclaimed optionals first, so that if the candidate budget is
    // exceeded it is the retained claimed members that are dropped — the
    // principal-retaining splits are only ever *added*, within budget.
    const max_optional = std.math.log2_int(usize, max_candidates);
    var opt_bits: [bag.capacity]usize = undefined;
    var opt_n: usize = 0;
    for (0..en.members.len) |t| {
        if ((required | optional_claimed) & bit(t) != 0) continue;
        opt_bits[opt_n] = t;
        opt_n += 1;
    }
    if (opt_n > max_optional) return false;
    for (0..en.members.len) |t| {
        if (opt_n == max_optional) break;
        if (optional_claimed & bit(t) == 0) continue;
        opt_bits[opt_n] = t;
        opt_n += 1;
    }

    const subsets = @as(usize, 1) << @intCast(opt_n);
    for (0..subsets) |idx| {
        var mask = required;
        for (opt_bits[0..opt_n], 0..) |b, j| {
            if (idx & (@as(usize, 1) << @intCast(j)) != 0) mask |= bit(b);
        }
        if (!en.push(mask)) return false;
    }
    return true;
}

/// What the spine binders other than `target_b` can hold in a set split: true
/// when that is anything (an open sibling, one too large to read, or one with
/// a meta or def member, which may stand for any members), else exactly the
/// members collected into `covered`.
fn siblingsCover(
    context: *const Context,
    theorem: *const TheoremContext,
    site: SplitSite,
    bindings: []const ?ExprId,
    target_b: usize,
    covered: *bag.ExprBag,
) bool {
    for (site.spine[0..site.spine_len]) |b| {
        if (b == target_b) continue;
        const value = boundValue(bindings, b) orelse return true;
        const held = bag.flatten(context, theorem, site.head_id, value) orelse return true;
        for (held.slice()) |member| {
            if (!acui.memberIsFixed(context, theorem, member)) return true;
            if (!covered.appendDistinct(member)) return true;
        }
    }
    return false;
}

/// Multiset (ACU) split: the target holds what the fixed principals and bound
/// siblings leave, copy by copy. With an open sibling it may hold any sub-bag
/// of that; without one it must hold all of it.
fn enumerateMultiset(
    context: *const Context,
    theorem: *const TheoremContext,
    site: SplitSite,
    bindings: []const ?ExprId,
    target_b: usize,
    goal: bag.ExprBag,
    en: *SplitEnumerator,
) bool {
    en.members = goal;
    const members = en.members.slice();
    var free = [_]bool{true} ** bag.capacity;
    claimPrincipals(theorem, site, bindings, members, free[0..members.len]);

    var open_sibling = false;
    for (site.spine[0..site.spine_len]) |b| {
        if (b == target_b) continue;
        const value = boundValue(bindings, b) orelse {
            open_sibling = true;
            continue;
        };
        const held = bag.flatten(context, theorem, site.head_id, value) orelse return false;
        for (held.slice()) |member| {
            // A meta or def member may stand for any number of members, so
            // the sibling is as good as open.
            if (!acui.memberIsFixed(context, theorem, member)) open_sibling = true;
            // A member the goal lacks may still match after conversion; the
            // validator decides.
            _ = takeCopy(members, free[0..members.len], member);
        }
    }

    var rest: u64 = 0;
    for (0..members.len) |i| {
        if (free[i]) rest |= bit(i);
    }
    if (!open_sibling) return en.push(rest);

    // Each distinct member contributes 0..n of its n free copies, always the
    // leftmost ones, so equal sub-multisets are built once.
    var firsts: [bag.capacity]usize = undefined;
    var copies: [bag.capacity]usize = undefined;
    var groups: usize = 0;
    var total: usize = 1;
    for (members, 0..) |member, i| {
        if (!free[i] or firstFreeCopy(members, free[0..members.len], member) != i) continue;
        var n: usize = 0;
        for (members, 0..) |other, j| {
            if (free[j] and other == member) n += 1;
        }
        firsts[groups] = i;
        copies[groups] = n;
        groups += 1;
        total = std.math.mul(usize, total, n + 1) catch return false;
        if (total > max_candidates) return false;
    }

    var counts = [_]usize{0} ** bag.capacity;
    while (true) {
        var mask: u64 = 0;
        for (0..groups) |g| {
            var left = counts[g];
            var j = firsts[g];
            while (left > 0) : (j += 1) {
                if (free[j] and members[j] == members[firsts[g]]) {
                    mask |= bit(j);
                    left -= 1;
                }
            }
        }
        if (!en.push(mask)) return false;
        // Next count vector (mixed radix).
        var g: usize = 0;
        while (g < groups) : (g += 1) {
            if (counts[g] < copies[g]) {
                counts[g] += 1;
                break;
            }
            counts[g] = 0;
        }
        if (g == groups) return true;
    }
}

/// Sequence (AU) split: the target holds one contiguous run of the goal. Each
/// end of the run is pinned when every summand on that side has a known member
/// count (a rigid fixed summand holds one member, a bound binder its own);
/// otherwise that end ranges over what is left. Under idempotence (AUI) a
/// summand may overlap its neighbours (`a , a = a`), so when the caller
/// retains claimed members (`overlap`) the run may be any contiguous run, as
/// the set split retains principals.
fn enumerateSequence(
    context: *const Context,
    theorem: *const TheoremContext,
    site: SplitSite,
    bindings: []const ?ExprId,
    target_b: usize,
    overlap: bool,
    goal: bag.ExprBag,
    en: *SplitEnumerator,
) bool {
    en.members = goal;
    const members = goal.slice();
    const n = goal.len;
    const summands = bag.flattenTemplate(context, site.head_id, site.template) orelse
        return false;
    const pos = for (summands.slice(), 0..) |summand, i| {
        if (summand == .binder and summand.binder == target_b) break i;
    } else return false;

    const before = if (overlap)
        Span{ .exact = false }
    else
        summandSpan(context, theorem, site.head_id, summands.slice()[0..pos], bindings);
    const after = if (overlap)
        Span{ .exact = false }
    else
        summandSpan(context, theorem, site.head_id, summands.slice()[pos + 1 ..], bindings);
    if (before.count + after.count > n) return true; // no run fits
    const start_max = if (before.exact) before.count else n - after.count;
    const end_min = if (after.exact) n - after.count else before.count;

    for (0..n + 1) |len| {
        var start = before.count;
        while (start <= start_max) : (start += 1) {
            const end = start + len;
            if (end < end_min or end > n - after.count) continue;
            // An earlier valid start with the same members builds the same
            // candidate (always so for the empty run).
            const first = @max(before.count, end_min -| len);
            const repeat = for (first..start) |earlier| {
                if (std.mem.eql(ExprId, members[earlier .. earlier + len], members[start..end])) break true;
            } else false;
            if (repeat) continue;
            var mask: u64 = 0;
            for (start..end) |i| mask |= bit(i);
            if (!en.push(mask)) return false;
        }
    }
    return true;
}

const Span = struct {
    /// Members the summands hold at least.
    count: usize = 0,
    /// Whether they hold exactly `count`.
    exact: bool = true,
};

fn summandSpan(
    context: *const Context,
    theorem: *const TheoremContext,
    head_id: u32,
    summands: []const TemplateExpr,
    bindings: []const ?ExprId,
) Span {
    var span = Span{};
    for (summands) |summand| switch (summand) {
        .binder => |b| {
            const value = boundValue(bindings, b) orelse {
                span.exact = false;
                continue;
            };
            const members = bag.flatten(context, theorem, head_id, value) orelse {
                span.exact = false;
                continue;
            };
            // A meta or def member may stand for any number of members.
            for (members.slice()) |member| {
                if (acui.memberIsFixed(context, theorem, member)) {
                    span.count += 1;
                } else {
                    span.exact = false;
                }
            }
        },
        // A def or `@rewrite` summand may unfold to any number of members.
        .app => |app| {
            if (semantic.isRigidHead(context, app.term_id)) {
                span.count += 1;
            } else {
                span.exact = false;
            }
        },
    };
    return span;
}

/// Each fully-bound fixed summand that matches exactly one distinct free member
/// claims one copy of it (the principal already sits on this side). A
/// partially-bound or ambiguous summand claims nothing — the validator's ACUI
/// weakening still confirms the assembly.
fn claimPrincipals(
    theorem: *const TheoremContext,
    site: SplitSite,
    bindings: []const ?ExprId,
    members: []const ExprId,
    free: []bool,
) void {
    for (site.fixed[0..site.fixed_len]) |ftmpl| {
        if (!templateFullyBound(ftmpl, bindings)) continue;
        var match: ?ExprId = null;
        const unique = for (members, 0..) |member, i| {
            if (!free[i]) continue;
            if (!acui.templateMatchesExprReadOnly(theorem, ftmpl, member, bindings)) continue;
            if (match) |first| {
                if (first != member) break false;
            } else match = member;
        } else true;
        if (unique) {
            if (match) |member| _ = takeCopy(members, free, member);
        }
    }
}

fn takeCopy(members: []const ExprId, free: []bool, member: ExprId) bool {
    const i = firstFreeCopy(members, free, member) orelse return false;
    free[i] = false;
    return true;
}

fn firstFreeCopy(members: []const ExprId, free: []const bool, member: ExprId) ?usize {
    for (members, 0..) |other, i| {
        if (free[i] and other == member) return i;
    }
    return null;
}

fn boundValue(bindings: []const ?ExprId, b: usize) ?ExprId {
    return if (b < bindings.len) bindings[b] else null;
}

fn bit(i: usize) u64 {
    return @as(u64, 1) << @intCast(i);
}

fn lessPopcount(_: void, a: u64, b: u64) bool {
    return @popCount(a) < @popCount(b);
}
