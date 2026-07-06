//! ACUI finite-domain witness enumeration for existential metas.
//!
//! An open target (e.g. the recover-shaped `A ∈ A ⊢ ?t ∈ A`) is
//! normally closed by the open generation hook: a child proof's conclusion is
//! matched back against the target, solving its metas structurally. That
//! fails when the witness is only *visible in an ACUI region* of the target
//! itself — `?t ∈ A` corresponds to the context member `A ∈ A`, but no child
//! conclusion ever shows it, because the child (`ax`) needs the witness
//! already solved to be applicable at all.
//!
//! This module proposes witnesses from that finite domain: the concrete
//! members of the target's own ACUI regions. Matching a meta-bearing rigid
//! fragment of the target against a member (or a member's subterm — region
//! members are often coercion-wrapped, e.g. `hyp(A ∈ A)`) assigns the metas
//! by the same structural correspondence used everywhere else
//! (`forward.solveCorrespondence`); repeated metas are consistent for free
//! via the hash-consed shared leaf. The enumeration is speculative — every
//! solved target still goes through ordinary generation and `tryCandidate`
//! validation — and bounded: only finite concrete regions, small member and
//! fragment caps, and a per-slot attempt cap.

const std = @import("std");
const types = @import("../types.zig");
const forward = @import("../forward.zig");
const acui = @import("./acui.zig");
const ExprId = @import("../../../expr.zig").ExprId;
const TheoremContext = @import("../../../expr.zig").TheoremContext;
const MetaStore = @import("../../inference/meta_store.zig").MetaStore;
const TemplateExpr = @import("../../../rules.zig").TemplateExpr;
const templateBinderMask = @import("../../../rules.zig").templateBinderMask;
const RuleDecl = @import("../../../env.zig").RuleDecl;
const Context = types.Context;

/// Distinct concrete domain members collected from the target's ACUI
/// regions. Enumeration considers at most this many distinct members;
/// additional members are ignored, and the ordinary child-search plus
/// `tryCandidate` validation still arbitrate every proposed fill.
pub const max_domain_members = 12;
/// Meta-bearing fragments of one open target considered for member matching.
pub const max_fragments = 6;

/// Collect the concrete members of every ACUI region in `target` into `buf`,
/// deduplicated by hash-cons id, returning the count. A region is any
/// argument position whose declared sort is the carrier sort of a registered
/// ACUI combiner — this catches singleton regions (`hyp(A ∈ A)`) that carry
/// no combiner node at all. Unit elements and members containing any
/// placeholder leaf (live meta or otherwise) are not domain values.
pub fn collectDomainMembers(
    context: *const Context,
    theorem: *const TheoremContext,
    target: ExprId,
    buf: *[max_domain_members]ExprId,
) usize {
    var count: usize = 0;
    collectFromExpr(context, theorem, target, buf, &count);
    return count;
}

fn collectFromExpr(
    context: *const Context,
    theorem: *const TheoremContext,
    expr: ExprId,
    buf: *[max_domain_members]ExprId,
    count: *usize,
) void {
    const app = switch (theorem.interner.node(expr).*) {
        .app => |app| app,
        else => return,
    };
    const decl = termDecl(context, app.term_id) orelse return;
    for (app.args, 0..) |arg, idx| {
        if (idx < decl.args.len) {
            if (carrierCombinerHead(context, decl.args[idx].sort_name)) |head_id| {
                collectRegionMembers(context, theorem, arg, head_id, buf, count);
            }
        }
        collectFromExpr(context, theorem, arg, buf, count);
    }
}

fn termDecl(
    context: *const Context,
    term_id: u32,
) ?*const @import("../../../env.zig").TermDecl {
    if (term_id >= context.env.terms.items.len) return null;
    return &context.env.terms.items[term_id];
}

/// The registered ACUI combiner whose carrier (return) sort is `sort_name`,
/// or null when the sort is not an ACUI carrier.
fn carrierCombinerHead(context: *const Context, sort_name: []const u8) ?u32 {
    var it = context.registry.acui_by_head.iterator();
    while (it.next()) |entry| {
        const decl = termDecl(context, entry.key_ptr.*) orelse continue;
        if (std.mem.eql(u8, decl.ret_sort_name, sort_name)) {
            return entry.key_ptr.*;
        }
    }
    return null;
}

/// Flatten the region rooted at `container` by `head_id` and append its
/// concrete non-unit members. A singleton region (no combiner node) is one
/// member.
fn collectRegionMembers(
    context: *const Context,
    theorem: *const TheoremContext,
    container: ExprId,
    head_id: u32,
    buf: *[max_domain_members]ExprId,
    count: *usize,
) void {
    switch (theorem.interner.node(container).*) {
        .app => |app| {
            if (app.term_id == head_id) {
                for (app.args) |arg| {
                    collectRegionMembers(context, theorem, arg, head_id, buf, count);
                }
                return;
            }
        },
        else => {},
    }
    if (!exprIsConcrete(theorem, container)) return;
    if (acui.isAcuiUnitExpr(context, theorem, container)) return;
    for (buf[0..count.*]) |existing| {
        if (existing == container) return;
    }
    if (count.* >= buf.len) return;
    buf[count.*] = container;
    count.* += 1;
}

/// No placeholder leaf at all — neither a live meta nor a standard
/// placeholder. Domain values must be plain concrete expressions.
fn exprIsConcrete(theorem: *const TheoremContext, expr: ExprId) bool {
    return switch (theorem.interner.node(expr).*) {
        .variable => true,
        .placeholder => false,
        .app => |app| blk: {
            for (app.args) |arg| {
                if (!exprIsConcrete(theorem, arg)) break :blk false;
            }
            break :blk true;
        },
    };
}

/// Collect the app-rooted subterms of `target` that contain at least one
/// unsolved meta, children before parents (the innermost fragment is the
/// most discriminating match candidate), capped at `max_fragments`.
/// Returns the count.
pub fn collectMetaFragments(
    theorem: *const TheoremContext,
    store: *const MetaStore,
    target: ExprId,
    buf: *[max_fragments]ExprId,
) usize {
    var count: usize = 0;
    _ = fragmentWalk(theorem, store, target, buf, &count);
    return count;
}

/// Post-order walk; returns whether `expr` contains an unsolved meta.
fn fragmentWalk(
    theorem: *const TheoremContext,
    store: *const MetaStore,
    expr: ExprId,
    buf: *[max_fragments]ExprId,
    count: *usize,
) bool {
    switch (theorem.interner.node(expr).*) {
        .variable => return false,
        .placeholder => |pid| {
            if (store.info(pid) == null) return false;
            if (store.lookup(pid)) |value| {
                return fragmentWalk(theorem, store, value, buf, count);
            }
            return true;
        },
        .app => |app| {
            var open = false;
            for (app.args) |arg| {
                if (fragmentWalk(theorem, store, arg, buf, count)) open = true;
            }
            if (open and count.* < buf.len) {
                buf[count.*] = expr;
                count.* += 1;
            }
            return open;
        },
    }
}

/// Match the meta-bearing `fragment` against `concrete` or any of its
/// subterms, assigning the fragment's existential metas on success (the
/// structural correspondence solve). Region members are routinely
/// coercion-wrapped (`hyp(A ∈ A)`), so the descent through subterms is what
/// lets a wff fragment meet a ctx member. Rolls back its own partial
/// assignments on failure; on success the assignments are left in `store`
/// and the caller owns the rollback site.
///
/// A *buried* witness — one under a binder, e.g. the `lall`/`rex` instance
/// `∀y R(?t y)` whose meta `?t` is only forced when the eventual leaf closes
/// against a succedent member `R(a b)` — never matches structurally (the
/// bound `y` conflicts with the member's concrete argument). For such a
/// binder-rooted fragment we strip the binders and match the body with each
/// bound variable acting as a wildcard: the universally-quantified instance
/// can close the member exactly one way, so the meta's value (`?t := a`) is
/// read off forcibly, no guessing. This is the same forced extraction the
/// nested witness rule + `ax` would perform, done locally in one store.
pub fn matchFragmentToMember(
    context: *const Context,
    store: *MetaStore,
    theorem: *TheoremContext,
    fragment: ExprId,
    concrete: ExprId,
) bool {
    var member_bound = BoundSet{};
    return matchFragmentAt(context, store, theorem, fragment, concrete, &member_bound);
}

/// One descent position of `matchFragmentToMember`. `member_bound` holds the
/// bound variables of every member-side binder crossed on the way down to
/// `concrete`: a witness value read off a match under a still-intact member
/// binder would let that variable escape its binder (the materialized target
/// mentions it free while the sibling member still binds it), so a solve
/// whose assignments mention one is rejected exactly like `solveBound`
/// rejects fragment-side captures. Such a fill can never validate; without
/// this check each one launched a full doomed child search.
fn matchFragmentAt(
    context: *const Context,
    store: *MetaStore,
    theorem: *TheoremContext,
    fragment: ExprId,
    concrete: ExprId,
    member_bound: *BoundSet,
) bool {
    const mark = store.mark();
    if (forward.solveCorrespondence(
        store,
        theorem,
        concrete,
        fragment,
        null,
    ) == .ok and !assignmentCapturesMemberBound(store, theorem, mark, member_bound)) {
        return true;
    }
    store.rollbackTo(mark);

    // Buried-witness fallback: a binder-rooted fragment is stripped and its
    // body matched with bound variables as wildcards.
    if (binderParts(context, theorem, fragment) != null) {
        var bound = BoundSet{};
        if (solveBound(context, store, theorem, concrete, fragment, &bound) == .ok and
            !assignmentCapturesMemberBound(store, theorem, mark, member_bound))
        {
            return true;
        }
        store.rollbackTo(mark);
    }

    switch (theorem.interner.node(concrete).*) {
        .app => |app| {
            // Descending into a member binder's body scopes its bound
            // variable; the binder head and bound-var arg themselves can't
            // match an app-rooted fragment, so only the body is explored.
            if (binderParts(context, theorem, concrete)) |parts| {
                const bv = theorem.interner.node(parts.bound_var).*.variable;
                member_bound.add(bv);
                defer member_bound.pop();
                return matchFragmentAt(context, store, theorem, fragment, parts.body, member_bound);
            }
            for (app.args) |arg| {
                if (matchFragmentAt(context, store, theorem, fragment, arg, member_bound)) {
                    return true;
                }
            }
            return false;
        },
        else => return false,
    }
}

/// True if any meta assignment recorded after `trail_mark` has a value that
/// mentions a variable in `member_bound`. Chained assignments are covered
/// entry-wise: every assignment in the chain has its own trail entry, and a
/// captured variable can only enter through the entry whose value embeds it
/// directly.
fn assignmentCapturesMemberBound(
    store: *const MetaStore,
    theorem: *const TheoremContext,
    trail_mark: usize,
    member_bound: *const BoundSet,
) bool {
    if (member_bound.len == 0) return false;
    for (store.trail.items[trail_mark..]) |entry| {
        switch (entry) {
            .assigned => |pid| {
                const value = store.lookup(pid) orelse continue;
                if (referencesBound(theorem, value, member_bound)) return true;
            },
            .minted => {},
        }
    }
    return false;
}

/// Bound variables (by `VarId`) in scope while matching a buried fragment.
/// Tiny: a fragment nests at most a handful of binders.
const BoundSet = struct {
    ids: [8]@import("../../../expr.zig").VarId = undefined,
    len: usize = 0,

    fn add(self: *BoundSet, id: @import("../../../expr.zig").VarId) void {
        if (self.len < self.ids.len) {
            self.ids[self.len] = id;
            self.len += 1;
        }
    }

    fn pop(self: *BoundSet) void {
        if (self.len > 0) self.len -= 1;
    }

    fn contains(self: *const BoundSet, id: @import("../../../expr.zig").VarId) bool {
        for (self.ids[0..self.len]) |existing| {
            if (std.meta.eql(existing, id)) return true;
        }
        return false;
    }
};

/// If `expr` is a canonical binder application (exactly two args, the first
/// bound, the second the body — the `∀`/`∃` shape), return the bound-variable
/// leaf and the body; null otherwise.
fn binderParts(
    context: *const Context,
    theorem: *const TheoremContext,
    expr: ExprId,
) ?struct { bound_var: ExprId, body: ExprId } {
    const app = switch (theorem.interner.node(expr).*) {
        .app => |app| app,
        else => return null,
    };
    const decl = termDecl(context, app.term_id) orelse return null;
    if (app.args.len != 2 or decl.args.len != 2) return null;
    if (!decl.args[0].bound or decl.args[1].bound) return null;
    if (theorem.interner.node(app.args[0]).* != .variable) return null;
    return .{ .bound_var = app.args[0], .body = app.args[1] };
}

/// Bound-aware structural correspondence: assign `pattern`'s metas from
/// `source`, treating any binder on the pattern side as transparent (its
/// bound variable becomes a wildcard). Mirrors `forward.solveCorrespondence`
/// otherwise. `source` is concrete (a domain member), so it carries no metas.
fn solveBound(
    context: *const Context,
    store: *MetaStore,
    theorem: *TheoremContext,
    source: ExprId,
    pattern: ExprId,
    bound: *BoundSet,
) forward.SolveResult {
    switch (theorem.interner.node(pattern).*) {
        .placeholder => |pid| {
            if (store.info(pid) == null) return .ok;
            if (store.lookup(pid)) |value| {
                return solveBound(context, store, theorem, source, value, bound);
            }
            // A witness may not capture a bound variable.
            if (referencesBound(theorem, source, bound)) return .conflict;
            store.assign(theorem, pid, source) catch return .conflict;
            return .ok;
        },
        .variable => |v| {
            if (bound.contains(v)) return .ok;
            return if (source == pattern) .ok else .conflict;
        },
        .app => |pattern_app| {
            if (binderParts(context, theorem, pattern)) |parts| {
                const bv = theorem.interner.node(parts.bound_var).*.variable;
                bound.add(bv);
                defer bound.pop();
                return solveBound(context, store, theorem, source, parts.body, bound);
            }
            switch (theorem.interner.node(source).*) {
                .app => |source_app| {
                    if (source_app.term_id != pattern_app.term_id) return .conflict;
                    if (source_app.args.len != pattern_app.args.len) return .conflict;
                    for (source_app.args, pattern_app.args) |s_arg, p_arg| {
                        if (solveBound(context, store, theorem, s_arg, p_arg, bound) == .conflict) {
                            return .conflict;
                        }
                    }
                    return .ok;
                },
                else => return .conflict,
            }
        },
    }
}

/// True if `expr` mentions any variable currently in `bound`.
fn referencesBound(
    theorem: *const TheoremContext,
    expr: ExprId,
    bound: *const BoundSet,
) bool {
    return theorem.exprAny(expr, bound, boundVarPred);
}

fn boundVarPred(
    bound: *const BoundSet,
    theorem: *const TheoremContext,
    expr_id: ExprId,
) bool {
    return switch (theorem.interner.node(expr_id).*) {
        .variable => |v| bound.contains(v),
        else => false,
    };
}

/// Collect region members of `target` that carry at least one *registered*
/// meta (local or ancestor), deduplicated, returning the count. These are the
/// candidates for meta-meta unification: a coupled witness (e.g. `lall`'s
/// `R ?t ey` and `rex`'s `R ez ?w`) is forced only when an antecedent member
/// unifies with a succedent member, binding the metas on both sides at once —
/// the leaf capture that the kept-principal conclusion never exposes.
pub fn collectMetaMembers(
    context: *const Context,
    store: *const MetaStore,
    theorem: *const TheoremContext,
    target: ExprId,
    buf: *[max_domain_members]ExprId,
) usize {
    var count: usize = 0;
    collectMetaFromExpr(context, store, theorem, target, buf, &count);
    return count;
}

fn collectMetaFromExpr(
    context: *const Context,
    store: *const MetaStore,
    theorem: *const TheoremContext,
    expr: ExprId,
    buf: *[max_domain_members]ExprId,
    count: *usize,
) void {
    const app = switch (theorem.interner.node(expr).*) {
        .app => |app| app,
        else => return,
    };
    const decl = termDecl(context, app.term_id) orelse return;
    for (app.args, 0..) |arg, idx| {
        if (idx < decl.args.len) {
            if (carrierCombinerHead(context, decl.args[idx].sort_name)) |head_id| {
                collectMetaRegionMembers(context, store, theorem, arg, head_id, buf, count);
            }
        }
        collectMetaFromExpr(context, store, theorem, arg, buf, count);
    }
}

fn collectMetaRegionMembers(
    context: *const Context,
    store: *const MetaStore,
    theorem: *const TheoremContext,
    container: ExprId,
    head_id: u32,
    buf: *[max_domain_members]ExprId,
    count: *usize,
) void {
    switch (theorem.interner.node(container).*) {
        .app => |app| {
            if (app.term_id == head_id) {
                for (app.args) |arg| {
                    collectMetaRegionMembers(context, store, theorem, arg, head_id, buf, count);
                }
                return;
            }
        },
        else => {},
    }
    if (!exprHasRegisteredMeta(store, theorem, container)) return;
    for (buf[0..count.*]) |existing| {
        if (existing == container) return;
    }
    if (count.* >= buf.len) return;
    buf[count.*] = container;
    count.* += 1;
}

fn exprHasRegisteredMeta(
    store: *const MetaStore,
    theorem: *const TheoremContext,
    expr: ExprId,
) bool {
    return theorem.exprAny(expr, store, registeredMetaPred);
}

fn registeredMetaPred(
    store: *const MetaStore,
    theorem: *const TheoremContext,
    expr_id: ExprId,
) bool {
    return switch (theorem.interner.node(expr_id).*) {
        .placeholder => |pid| store.info(pid) != null,
        else => false,
    };
}

/// ACUI-aware variant of `forward.solveCorrespondence` for the open-target
/// read-back: walk the meta-bearing `pattern` (the open target) against the
/// concrete `source` (the child's accepted conclusion) in lockstep, but where
/// the two sides meet in a region of a registered COMMUTATIVE ACUI combiner,
/// match member-wise as multisets instead of positionally: identical members
/// cancel, structured members unify recursively (deterministic first-fit with
/// trail-backtracking), and a single whole-member meta absorbs the re-joined
/// complement. This recovers the read-backs a child conclusion loses to pure
/// reordering/reassociation — the checker bridges conclusion-vs-hint modulo
/// ACUI, but the checked line keeps the child rule's own association, so the
/// positional walk conflicts on an ACUI-equal conclusion.
///
/// No `hole` handling (the read-back passes none). Abstains (returns false)
/// on non-commutative subsets (an AU leftover is order-constrained, not a
/// free multiset — see the @acui-subset note), on more than one whole-member
/// meta per region (no forced partition exists), on region overflow, and when
/// the deterministic member-match attempt budget is exhausted (the
/// backtracking is worst-case factorial; the cap keeps the failure path
/// bounded). Only `error.OutOfMemory` propagates — every other failure is an
/// abstention, and on abstention the store is rolled back to the entry mark
/// (on success, assignments persist and the caller owns the rollback site).
/// Sound: it only *proposes* assignments; the recompiled assembly is still
/// arbitrated by `tryCandidate`, which inserts the ACUI reorder bridge.
pub fn solveCorrespondenceAcui(
    context: *const Context,
    store: *MetaStore,
    theorem: *TheoremContext,
    source: ExprId,
    pattern: ExprId,
) error{OutOfMemory}!bool {
    const mark = store.mark();
    var attempts: usize = 0;
    const ok = try solveAcuiInner(context, store, theorem, source, pattern, &attempts);
    if (!ok) store.rollbackTo(mark);
    return ok;
}

/// Total member-pair match trials allowed per top-level read-back attempt.
/// Wide honest regions fit comfortably; a factorial backtracking blow-up
/// (shared metas across many mutually-unifiable members) abstains instead of
/// stalling between global-budget checks.
const max_member_match_attempts = 256;

fn solveAcuiInner(
    context: *const Context,
    store: *MetaStore,
    theorem: *TheoremContext,
    source: ExprId,
    pattern: ExprId,
    attempts: *usize,
) error{OutOfMemory}!bool {
    const dp = store.deref(theorem, pattern) catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
        else => return false,
    };
    if (store.metaIdOf(theorem, dp)) |pid| {
        store.assign(theorem, pid, source) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            else => return false,
        };
        return true;
    }
    switch (theorem.interner.node(dp).*) {
        // Standard (unregistered) placeholder: no opinion, validation
        // arbitrates — mirrors `solveCorrespondence`.
        .placeholder => return true,
        .variable => return source == dp,
        .app => |pattern_app| {
            const region_head: ?u32 = blk: {
                if (acui.isCommutative(context, pattern_app.term_id)) {
                    break :blk pattern_app.term_id;
                }
                switch (theorem.interner.node(source).*) {
                    .app => |source_app| {
                        if (acui.isCommutative(context, source_app.term_id)) {
                            break :blk source_app.term_id;
                        }
                    },
                    else => {},
                }
                break :blk null;
            };
            if (region_head) |head| {
                return matchAcuiRegion(context, store, theorem, head, source, dp, attempts);
            }
            switch (theorem.interner.node(source).*) {
                // An unfilled source position may still become anything.
                .placeholder => return true,
                .variable => return false,
                .app => |source_app| {
                    if (source_app.term_id != pattern_app.term_id) return false;
                    if (source_app.args.len != pattern_app.args.len) return false;
                    for (source_app.args, pattern_app.args) |s_arg, p_arg| {
                        if (!try solveAcuiInner(context, store, theorem, s_arg, p_arg, attempts)) {
                            return false;
                        }
                    }
                    return true;
                },
            }
        },
    }
}

/// Members considered per ACUI region in the read-back matcher; a region
/// wider than this abstains rather than truncating.
const max_region_members = 16;

fn matchAcuiRegion(
    context: *const Context,
    store: *MetaStore,
    theorem: *TheoremContext,
    head: u32,
    source: ExprId,
    pattern: ExprId,
    attempts: *usize,
) error{OutOfMemory}!bool {
    // Only the region head's OWN unit is droppable: `join(emp2, X)` with a
    // foreign combiner's unit is not ACUI-equal to `X` under `join`'s laws.
    const unit_id = acui.acuiUnitIdForHead(context, head);
    var sbuf: [max_region_members]ExprId = undefined;
    var pbuf: [max_region_members]ExprId = undefined;
    var scount: usize = 0;
    var pcount: usize = 0;
    if (!try flattenRegion(store, theorem, head, unit_id, source, &sbuf, &scount)) return false;
    if (!try flattenRegion(store, theorem, head, unit_id, pattern, &pbuf, &pcount)) return false;

    var sused = [_]bool{false} ** max_region_members;
    var pdone = [_]bool{false} ** max_region_members;

    // Pass 1: cancel identical members (multiset, multiplicity-aware —
    // hash-consing makes ExprId equality member equality).
    for (pbuf[0..pcount], 0..) |pm, pi| {
        for (sbuf[0..scount], 0..) |sm, si| {
            if (sused[si]) continue;
            if (sm == pm) {
                sused[si] = true;
                pdone[pi] = true;
                break;
            }
        }
    }

    // A whole-member meta absorbs the complement; two of them would need a
    // partition nothing forces — abstain.
    var meta_pi: ?usize = null;
    for (pbuf[0..pcount], 0..) |pm, pi| {
        if (pdone[pi]) continue;
        if (store.metaIdOf(theorem, pm) != null) {
            if (meta_pi != null) return false;
            meta_pi = pi;
            pdone[pi] = true;
        }
    }

    // Pass 2: match the remaining structured pattern members against unused
    // source members (first-fit, deterministic order, backtracking, capped).
    if (!try matchStructuredMembers(
        context,
        store,
        theorem,
        pbuf[0..pcount],
        &pdone,
        sbuf[0..scount],
        &sused,
        0,
        attempts,
    )) return false;

    if (meta_pi) |pi| {
        const rest = (try joinLeftoverMembers(context, theorem, head, sbuf[0..scount], &sused)) orelse
            return false;
        // Pass 2 may have solved the whole-member meta through a nested
        // occurrence (e.g. `?m` also under `f ?m` in the same region): require
        // consistency with the complement instead of failing the blind assign.
        const dm = store.deref(theorem, pbuf[pi]) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            else => return false,
        };
        if (store.metaIdOf(theorem, dm)) |pid| {
            store.assign(theorem, pid, rest) catch |err| switch (err) {
                error.OutOfMemory => return error.OutOfMemory,
                else => return false,
            };
            return true;
        }
        return solveAcuiInner(context, store, theorem, rest, dm, attempts);
    }
    for (sbuf[0..scount], 0..) |_, si| {
        if (!sused[si]) return false;
    }
    return true;
}

/// Flatten the region rooted at `expr` by `head` into `buf`, dereferencing
/// solved metas and dropping members equal to the region head's OWN unit
/// (`unit_id`; a foreign combiner's unit is a real member). Returns false on
/// overflow (the matcher abstains rather than truncates).
///
/// Deliberately separate from `acui.collectAcuiMembers`: that one is a
/// raw member collection (no meta store to deref through, units kept for the
/// caller to judge), and parameterizing one flattener over both behaviors
/// would cost more than the shared spine saves.
fn flattenRegion(
    store: *MetaStore,
    theorem: *TheoremContext,
    head: u32,
    unit_id: ?u32,
    expr: ExprId,
    buf: *[max_region_members]ExprId,
    count: *usize,
) error{OutOfMemory}!bool {
    const d = store.deref(theorem, expr) catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
        else => return false,
    };
    switch (theorem.interner.node(d).*) {
        .app => |app| {
            if (app.term_id == head) {
                for (app.args) |arg| {
                    if (!try flattenRegion(store, theorem, head, unit_id, arg, buf, count)) {
                        return false;
                    }
                }
                return true;
            }
            if (unit_id) |uid| {
                if (app.term_id == uid and app.args.len == 0) return true;
            }
        },
        else => {},
    }
    if (count.* >= buf.len) return false;
    buf[count.*] = d;
    count.* += 1;
    return true;
}

fn matchStructuredMembers(
    context: *const Context,
    store: *MetaStore,
    theorem: *TheoremContext,
    pmembers: []const ExprId,
    pdone: *const [max_region_members]bool,
    smembers: []const ExprId,
    sused: *[max_region_members]bool,
    start: usize,
    attempts: *usize,
) error{OutOfMemory}!bool {
    var pi = start;
    while (pi < pmembers.len and pdone[pi]) : (pi += 1) {}
    if (pi >= pmembers.len) return true;
    for (smembers, 0..) |sm, si| {
        if (sused[si]) continue;
        // Deterministic work bound: the first-fit backtracking is worst-case
        // factorial in region width; exceeding the trial budget abstains.
        if (attempts.* >= max_member_match_attempts) return false;
        attempts.* += 1;
        const mark = store.mark();
        if (try solveAcuiInner(context, store, theorem, sm, pmembers[pi], attempts)) {
            sused[si] = true;
            if (try matchStructuredMembers(
                context,
                store,
                theorem,
                pmembers,
                pdone,
                smembers,
                sused,
                pi + 1,
                attempts,
            )) return true;
            sused[si] = false;
        }
        store.rollbackTo(mark);
    }
    return false;
}

/// Right-fold the unused source members back into one region expression, or
/// the combiner's unit when none remain. Null when the unit is unresolvable
/// or interning hits a non-OOM limit (abstain); OOM propagates.
fn joinLeftoverMembers(
    context: *const Context,
    theorem: *TheoremContext,
    head: u32,
    smembers: []const ExprId,
    sused: *const [max_region_members]bool,
) error{OutOfMemory}!?ExprId {
    var kept: [max_region_members]ExprId = undefined;
    var kept_n: usize = 0;
    for (smembers, 0..) |member, i| {
        if (sused[i]) continue;
        kept[kept_n] = member;
        kept_n += 1;
    }
    if (kept_n == 0) {
        const unit_id = acui.acuiUnitIdForHead(context, head) orelse return null;
        return theorem.interner.internApp(unit_id, &.{}) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            else => return null,
        };
    }
    return acui.internRightFold(theorem, head, kept[0..kept_n]) catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
        else => return null,
    };
}

/// Symmetric unification of two meta-bearing members, assigning registered
/// metas on *either* side (the coupled leaf capture). Returns true on success
/// with assignments left in `store` (caller owns the rollback site).
pub fn unifyMembers(
    store: *MetaStore,
    theorem: *TheoremContext,
    a: ExprId,
    b: ExprId,
) bool {
    const da = store.deref(theorem, a) catch return false;
    const db = store.deref(theorem, b) catch return false;
    if (da == db) return true;
    if (store.metaIdOf(theorem, da)) |pid| {
        store.assign(theorem, pid, db) catch return false;
        return true;
    }
    if (store.metaIdOf(theorem, db)) |pid| {
        store.assign(theorem, pid, da) catch return false;
        return true;
    }
    const na = theorem.interner.node(da).*;
    const nb = theorem.interner.node(db).*;
    switch (na) {
        .app => |aa| switch (nb) {
            .app => |bb| {
                if (aa.term_id != bb.term_id) return false;
                if (aa.args.len != bb.args.len) return false;
                for (aa.args, bb.args) |arg_a, arg_b| {
                    // Re-deref per arg (inside the recursive call): an earlier
                    // arg's assignment may bind a meta referenced later.
                    if (!unifyMembers(store, theorem, arg_a, arg_b)) return false;
                }
                return true;
            },
            else => return false,
        },
        else => return false,
    }
}

/// Distinct complement shapes considered by the coupled pass. Real theories
/// declare at most one or two `ax`-style closure rules.
pub const max_complement_shapes = 4;

/// A complementation a hypothesis-free rule's conclusion declares: an ACUI
/// region that repeats one binder across two distinct members (`ax`'s
/// `⊢ a , (¬ a) , d` — with a wff→ctx coercion the members are `hyp(a)` and
/// `hyp(¬ a)`, so neither need be a bare binder). The pair of member
/// templates (env-owned, stable) with the shared binder as the hole.
pub const ComplementShape = struct {
    first: *const TemplateExpr,
    second: *const TemplateExpr,
    hole: usize,
};

/// Derive complement shapes from the visible hypothesis-free rules. Such a
/// rule closes a goal by identifying two region members through the repeated
/// binder, so two meta-bearing goal members (`¬ R ?x y` vs `R z ?w`) can be
/// co-solved *through* the pair even though neither is concrete — the
/// closure `unifyMembers` alone cannot express because the members' heads
/// differ. Theory-agnostic: driven entirely off the rule template's repeated
/// binder, never off the wrapper's meaning.
pub fn collectComplementShapes(
    context: *const Context,
    buf: *[max_complement_shapes]ComplementShape,
) usize {
    var count: usize = 0;
    const rules = context.env.rules.items;
    const visible = @min(context.available_rule_count, rules.len);
    for (rules[0..visible]) |*rule| {
        if (count >= buf.len) break;
        if (rule.hyps.len != 0) continue;
        complementWalkTemplate(context, rule, &rule.concl, buf, &count);
    }
    return count;
}

/// Mirror of `collectFromExpr` over a rule-conclusion template: analyze every
/// argument position whose declared sort is an ACUI carrier as a region.
fn complementWalkTemplate(
    context: *const Context,
    rule: *const RuleDecl,
    tmpl: *const TemplateExpr,
    buf: *[max_complement_shapes]ComplementShape,
    count: *usize,
) void {
    const app = switch (tmpl.*) {
        .app => |*app| app,
        else => return,
    };
    const decl = termDecl(context, app.term_id) orelse return;
    for (app.args, 0..) |*arg, idx| {
        if (idx < decl.args.len) {
            if (carrierCombinerHead(context, decl.args[idx].sort_name)) |head_id| {
                analyzeComplementRegion(rule, arg, head_id, buf, count);
            }
        }
        complementWalkTemplate(context, rule, arg, buf, count);
    }
}

/// Flatten the template region and record each pair of distinct members
/// whose binder occurrences are exactly one shared binder (the repetition is
/// what makes the two members "the same formula" to the rule).
fn analyzeComplementRegion(
    rule: *const RuleDecl,
    container: *const TemplateExpr,
    head_id: u32,
    buf: *[max_complement_shapes]ComplementShape,
    count: *usize,
) void {
    var members: [max_region_members]*const TemplateExpr = undefined;
    var member_count: usize = 0;
    var overflow = false;
    flattenTemplateRegion(container, head_id, &members, &member_count, &overflow);
    if (overflow) return;

    for (members[0..member_count], 0..) |first, i| {
        const hole = singleBinderOf(first) orelse continue;
        // A bound (eigenvariable-class) hole would raise capture questions
        // the hole unification cannot arbitrate; abstain.
        if (hole >= rule.args.len or rule.args[hole].bound) continue;
        for (members[i + 1 .. member_count]) |second| {
            if (singleBinderOf(second) != hole) continue;
            if (first.eql(second.*)) continue;
            var duplicate = false;
            for (buf[0..count.*]) |existing| {
                if (existing.hole == hole and
                    existing.first.eql(first.*) and
                    existing.second.eql(second.*))
                {
                    duplicate = true;
                    break;
                }
            }
            if (duplicate) continue;
            if (count.* >= buf.len) return;
            buf[count.*] = .{ .first = first, .second = second, .hole = hole };
            count.* += 1;
        }
    }
}

fn flattenTemplateRegion(
    tmpl: *const TemplateExpr,
    head_id: u32,
    members: *[max_region_members]*const TemplateExpr,
    count: *usize,
    overflow: *bool,
) void {
    switch (tmpl.*) {
        .app => |app| {
            if (app.term_id == head_id) {
                for (app.args) |*arg| {
                    flattenTemplateRegion(arg, head_id, members, count, overflow);
                }
                return;
            }
        },
        .binder => {},
    }
    if (count.* >= members.len) {
        overflow.* = true;
        return;
    }
    members[count.*] = tmpl;
    count.* += 1;
}

/// The single distinct binder index occurring in `tmpl`, or null when the
/// template mentions zero or several binders (or overflows the mask).
fn singleBinderOf(tmpl: *const TemplateExpr) ?usize {
    const m = templateBinderMask(tmpl.*);
    if (m.overflow) return null;
    if (@popCount(m.mask) != 1) return null;
    return @ctz(m.mask);
}

/// Unify the member pair (`member_a`, `member_b`) through the shape's
/// template pair: `member_a` must match `shape.first` and `member_b`
/// `shape.second` rigidly, with every hole occurrence resolving to ONE
/// shared subexpression — the first occurrence captures, later occurrences
/// unify against the capture via `unifyMembers` (assigning registered metas
/// on either side). The complementary leaf capture: `ax`'s `hyp(a)` /
/// `hyp(¬ a)` pair co-solves `hyp(R z ?w)` against `hyp(¬ R ?x y)` even
/// though the members' own heads differ under the wrapper. Partial
/// assignments are left in `store` on failure; the caller owns the
/// mark/rollback site.
pub fn unifyMembersThroughShape(
    store: *MetaStore,
    theorem: *TheoremContext,
    shape: ComplementShape,
    member_a: ExprId,
    member_b: ExprId,
) bool {
    var captured: ?ExprId = null;
    if (!matchTemplateCapture(store, theorem, shape.first, shape.hole, member_a, &captured)) {
        return false;
    }
    return matchTemplateCapture(store, theorem, shape.second, shape.hole, member_b, &captured);
}

fn matchTemplateCapture(
    store: *MetaStore,
    theorem: *TheoremContext,
    tmpl: *const TemplateExpr,
    hole: usize,
    member: ExprId,
    captured: *?ExprId,
) bool {
    switch (tmpl.*) {
        .binder => |idx| {
            if (idx != hole) return false;
            const dm = store.deref(theorem, member) catch return false;
            if (captured.*) |prior| {
                return unifyMembers(store, theorem, prior, dm);
            }
            captured.* = dm;
            return true;
        },
        .app => |sapp| {
            // A rigid template node meeting a bare meta would require
            // instantiating the template (inventing structure); abstain.
            const dm = store.deref(theorem, member) catch return false;
            switch (theorem.interner.node(dm).*) {
                .app => |mapp| {
                    if (mapp.term_id != sapp.term_id) return false;
                    if (mapp.args.len != sapp.args.len) return false;
                    for (sapp.args, mapp.args) |*s_arg, m_arg| {
                        if (!matchTemplateCapture(
                            store,
                            theorem,
                            s_arg,
                            hole,
                            m_arg,
                            captured,
                        )) return false;
                    }
                    return true;
                },
                else => return false,
            }
        },
    }
}
