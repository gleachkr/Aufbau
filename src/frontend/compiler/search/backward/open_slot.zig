//! The open-slot engine of backward generation: an `@auto backward` rule's
//! premise whose binders the goal leaves open. It builds an open target with
//! existential metas, solves it by a child search, reads the solution back
//! into the parent's bindings, and otherwise runs the witness ladder (ACUI
//! member, coupled, paired-member and pool witnesses). Entered through
//! `tryOpenGenerateSlot` from `backtrack.zig`'s slot loop, which it calls back
//! for the next sibling slot.

const std = @import("std");
const types = @import("../types.zig");
const semantic = @import("./semantic.zig");
const seed = @import("./seed.zig");
const split = @import("./split.zig");
const acui = @import("./acui.zig");
const Witness = @import("./witness.zig");
const match = @import("./match.zig");
const plausible = @import("./plausible.zig");
const plan = @import("./plan.zig");
const forward = @import("../forward.zig");
const ExprId = @import("../../../expr.zig").ExprId;
const PlaceholderId = @import("../../../expr.zig").PlaceholderId;
const TheoremContext = @import("../../../expr.zig").TheoremContext;
const RuleDecl = @import("../../../env.zig").RuleDecl;
const ArgInfo = @import("../../../parse_recovery.zig").ArgInfo;
const OpenTerms = @import("../../inference/open_terms.zig");
const Redex = @import("./redex.zig");
const MetaStoreMod = @import("../meta_store.zig");
const MetaStore = MetaStoreMod.MetaStore;
const PoolVars = @import("../../vars.zig").PoolVars;
const Context = types.Context;
const ApplyCandidate = types.ApplyCandidate;
const GenerationHook = types.GenerationHook;
const normalizeAcuiUnits = acui.normalizeAcuiUnits;

const seedViewBindingsForMatch = match.seedViewBindingsForMatch;
const rollbackOneHypMatch = match.rollbackOneHypMatch;
const conclusionBinderMaskOrNone = plan.conclusionBinderMaskOrNone;

const backtrack = @import("./backtrack.zig");
const OpenMode = backtrack.OpenMode;
const openMode = backtrack.openMode;
const tryFreshBoundGenerate = backtrack.tryFreshBoundGenerate;
const SlotCtx = backtrack.SlotCtx;
const Slot = backtrack.Slot;
const tryGenerateSlot = backtrack.tryGenerateSlot;
const emitGeneratedSlot = backtrack.emitGeneratedSlot;

/// State for one open-slot attempt, on top of the candidate's `SlotCtx`. The
/// open path recurses over bound-witness choices and recover/meta
/// construction layers, which all share it.
const OpenSlot = struct {
    ctx: *const SlotCtx,
    hook: *const GenerationHook,
    at: Slot,
    /// Branch-local existential store for this slot attempt. Mint marks are
    /// taken before each construction layer and rolled back beside the
    /// bindings snapshot (the meta-store rollback invariant).
    store: *MetaStore,
    /// Open policy for this candidate, computed once at slot entry.
    /// `.witness` gates the existential machinery (bound-binder meta
    /// deferral, ancestor-meta registration, the force-first ladder);
    /// `.constrained` keeps the child-search-first read-back discipline.
    mode: OpenMode,
    /// The slot's open binders are bound variables nothing outside the premise
    /// sees (`tryFreshBoundGenerate`): when the child search leaves one
    /// unsolved, it takes a fresh `@vars` variable (`tryPoolWitnesses`).
    fresh_bound: bool = false,
    /// Binders whose values hold metas `rebindHiddenVars` minted for this slot;
    /// a solved fill materializes them too.
    rebound: u64 = 0,

    /// The candidate is `@auto eager`: its open subgoal keeps the parent's
    /// remaining depth, as a concrete one does (`tryGenerateSlot`).
    fn eagerStep(self: *const OpenSlot) bool {
        return self.ctx.context.registry.eagerPriority(self.ctx.candidate.rule_id) != null;
    }
};

/// Structured open backward generation for one hypothesis
/// slot of an `@auto backward` rule. Builds an open target whose unsolved
/// leaves are existential metas — preferring the `@recover`-shaped surface
/// over raw template deferral — asks the hook to solve it with a generated
/// child proof, matches the child's concrete conclusion back against the
/// target to pin the parent's binders, and continues to the next sibling.
pub fn tryOpenGenerateSlot(
    ctx: *const SlotCtx,
    hook: *const GenerationHook,
    at: Slot,
    /// What opens as fresh bound variables (`tryFreshBoundGenerate`);
    /// empty for an ordinary open slot.
    fresh: FreshOpen,
) anyerror!void {
    const context = ctx.context;
    const candidate = ctx.candidate;
    const bindings = ctx.bindings;
    const fresh_bound = fresh.binders != 0 or fresh.hosts != 0;
    // Each `.bound_choice` meta the open path mints takes a dependency slot.
    // Candidates leave as proof text and the bindings roll back below, so
    // nothing holds those slots once the slot attempt is over: give them back
    // (this defer runs after the rollback).
    const slot_mark = candidate.theorem.depSlotMark();
    defer candidate.theorem.releaseUnheldDepSlots(slot_mark, &.{bindings});
    var store = MetaStore.init(ctx.context.allocator, context.env);
    // Share the driver's global meta-id counter so witness metas keep a stable
    // identity across the open-target recursion's interner clones.
    store.meta_id_counter = hook.meta_id_counter;
    store.dep_bans = hook.meta_dep_bans;
    // The pool-ref loop at this depth is done with its snapshot slice;
    // reuse it as the open path's bindings rollback point.
    const snapshot = ctx.snapshotAt(at.depth);
    @memcpy(snapshot, bindings);
    defer rollbackOneHypMatch(bindings, snapshot);
    const rebound = try rebindHiddenVars(&store, &candidate.theorem, bindings, fresh.binders | fresh.hosts);
    // Narrow the carried-meta dependency bans for this slot's lifetime: the
    // candidate's bindings are fixed for everything opened beneath it.
    const ban_mark = if (hook.meta_dep_bans) |bans| blk: {
        const mark = bans.mark();
        try banCarriedMetaDeps(ctx.rule, &candidate.theorem, bindings, bans);
        break :blk mark;
    } else 0;
    defer if (hook.meta_dep_bans) |bans| bans.rollback(ban_mark);
    defer {
        // Mirror this branch's meta activity into the bench counters.
        if (ctx.counters) |c| {
            c.existential_metas_created += store.stats.existential_created;
            c.bound_choice_metas_created += store.stats.bound_choice_created;
            c.meta_assignments += store.stats.assignments;
            c.meta_rollbacks += store.stats.rollbacks;
        }
        store.deinit();
    }

    var slot = OpenSlot{
        .ctx = ctx,
        .hook = hook,
        .at = at,
        .store = &store,
        .mode = if (fresh_bound) .constrained else openMode(
            context,
            candidate.rule_id,
            hook.allow_constrained_mp,
        ),
        .fresh_bound = fresh_bound,
        .rebound = rebound,
    };
    if (context.views.get(candidate.rule_id)) |view| {
        try openSlotViaView(&slot, view);
    } else {
        try openSlotRaw(&slot);
    }
}

/// The parts of a premise `tryFreshBoundGenerate` opens as fresh bound
/// variables.
const FreshOpen = struct {
    /// Bound binders that open as metas.
    binders: u64 = 0,
    /// Binders whose values are terms over a def's hidden variable.
    hosts: u64 = 0,
};

/// Replace each hidden-variable leaf in the values of `hosts` with a
/// `.bound_choice` meta of `store`, in every binding that mentions it, so the
/// child search can name the variable and `tryPoolWitnesses` can fill it.
/// Two leaves stand for a def's hidden variable: an unfolded dummy, and a
/// seed meta (`ih` on an open binder, unmatched by any ref, or inside a kept
/// term such as `reflt`'s `t := λ x. x` under `T`). A hidden variable only
/// another premise's binders mention stays put: this slot's solve could not
/// fill it. Returns the binders whose values changed.
pub fn rebindHiddenVars(
    store: *MetaStore,
    theorem: *TheoremContext,
    bindings: []?ExprId,
    hosts: u64,
) !u64 {
    var changed: u64 = 0;
    var rest = hosts;
    while (rest != 0) {
        const idx: u6 = @intCast(@ctz(rest));
        rest &= rest - 1;
        while (bindings[idx]) |value| {
            const leaf = firstHiddenVarLeaf(theorem, value) orelse break;
            const pid = theorem.interner.node(leaf).placeholder;
            const info = theorem.placeholderInfo(pid) orelse break;
            const meta = try store.mintBoundVar(theorem, info.sort_name, info.deps, std.math.maxInt(u55));
            for (bindings, 0..) |*binding, other| {
                const other_value = binding.* orelse continue;
                const swapped = try forward.leafSwap(theorem, other_value, leaf, meta);
                if (swapped == other_value) continue;
                binding.* = swapped;
                if (other < 64) changed |= @as(u64, 1) << @intCast(other);
            }
        }
    }
    return changed;
}

/// True when a binding other than `bindings[idx]` mentions `leaf`.
pub fn heldElsewhere(theorem: *const TheoremContext, bindings: []const ?ExprId, idx: usize, leaf: ExprId) bool {
    for (bindings, 0..) |maybe, other| {
        if (other == idx) continue;
        const value = maybe orelse continue;
        if (theorem.exprAny(value, leaf, isExpr)) return true;
    }
    return false;
}

fn isExpr(target: ExprId, _: *const TheoremContext, expr: ExprId) bool {
    return expr == target;
}

pub fn isHiddenVarLeaf(_: void, theorem: *const TheoremContext, expr: ExprId) bool {
    const kind = theorem.leafPlaceholderKind(expr) orelse return false;
    return kind == .dummy or kind == .seed_meta;
}

fn firstHiddenVarLeaf(theorem: *const TheoremContext, expr: ExprId) ?ExprId {
    return switch (theorem.interner.node(expr).*) {
        .variable => null,
        .placeholder => if (isHiddenVarLeaf({}, theorem, expr)) expr else null,
        .app => |app| for (app.args) |arg| {
            if (firstHiddenVarLeaf(theorem, arg)) |leaf| break leaf;
        } else null,
    };
}

/// The eigenvariable condition, read off the rule's own dependency data: a
/// non-bound binder whose `ArgInfo.deps` omits bound arg `x` must not depend
/// on `x`'s value, so no meta inside it may be filled with anything
/// mentioning that value. Bans the value's dep bits on every such meta (by
/// stable `meta_id`, so the ban survives the child search's interner
/// clones); `MetaStore.registerAncestorMeta` turns the ban into the meta's
/// `allowed_deps`.
fn banCarriedMetaDeps(
    rule: *const RuleDecl,
    theorem: *const TheoremContext,
    bindings: []const ?ExprId,
    bans: *MetaStoreMod.MetaDepBans,
) !void {
    for (rule.args, 0..) |arg, idx| {
        if (arg.bound) continue;
        const value = bindings[idx] orelse continue;
        if (!theorem.containsMetaLeaf(value)) continue;
        const banned = bannedDeps(theorem, rule, bindings, idx);
        if (banned != 0) try banMetasIn(theorem, value, banned, bans);
    }
}

/// The dependency bits non-bound binder `idx` of `rule` must avoid, as the
/// checker's dependency condition reads them: those of the values of the bound
/// binders `idx`'s `ArgInfo.deps` omits.
fn bannedDeps(
    theorem: *const TheoremContext,
    rule: *const RuleDecl,
    bindings: []const ?ExprId,
    idx: usize,
) u55 {
    const deps = rule.args[idx].deps;
    var banned: u55 = 0;
    for (rule.args, 0..) |bound_arg, bound_idx| {
        if (!bound_arg.bound or deps & bound_arg.deps != 0) continue;
        const bound_value = bindings[bound_idx] orelse continue;
        banned |= (theorem.exprDeps(bound_value, .{}) catch 0);
    }
    return banned;
}

/// How a matched non-bound binder's value mentions the value of a bound arg
/// its `ArgInfo.deps` omits. Occurrences under a term with alpha rules don't
/// count (`@freshen` renames only through those). A meta leaf counts as no hit,
/// even a seed meta carrying a dep bit: an open meta may still be assigned
/// something that avoids the bound variable, so a partially open binding is
/// judged on its concrete part.
const DepHit = enum {
    none,
    /// Reached only through a head conversion can rewrite away: a def
    /// argument its body may drop, a `@rewrite` head, or an unavailable term.
    soft,
    /// Reached along heads no conversion removes (`argSurvivesConversion`).
    /// ACUI combiners count: rearrangement never drops a member (idempotence
    /// keeps a copy, and the unit mentions nothing).
    rigid,
};

/// The strongest `DepHit` over the rule's non-bound binders, as matched.
pub fn bindingsDepHit(
    context: *const Context,
    theorem: *const TheoremContext,
    rule: *const RuleDecl,
    bindings: []const ?ExprId,
) DepHit {
    var result: DepHit = .none;
    for (rule.args, 0..) |arg, idx| {
        if (arg.bound) continue;
        const value = bindings[idx] orelse continue;
        const banned = bannedDeps(theorem, rule, bindings, idx);
        if (banned == 0) continue;
        const hit = exprDepHit(context, theorem, value, banned);
        if (@backingInt(hit) > @backingInt(result)) result = hit;
        if (result == .rigid) break;
    }
    return result;
}

fn exprDepHit(
    context: *const Context,
    theorem: *const TheoremContext,
    expr: ExprId,
    banned: u55,
) DepHit {
    return switch (theorem.interner.node(expr).*) {
        .placeholder => .none,
        .variable => blk: {
            const info = (theorem.currentLeafInfo(expr) catch null) orelse break :blk .none;
            break :blk if (info.deps & banned != 0) .rigid else .none;
        },
        .app => |app| blk: {
            if (context.registry.getAlphaRules(app.term_id).len != 0) break :blk .none;
            var result: DepHit = .none;
            for (app.args, 0..) |arg, i| {
                var hit = exprDepHit(context, theorem, arg, banned);
                if (hit == .rigid and !argSurvivesConversion(context, app.term_id, i)) hit = .soft;
                if (@backingInt(hit) > @backingInt(result)) result = hit;
                if (result == .rigid) break;
            }
            break :blk result;
        },
    };
}

/// No checker conversion can remove argument `arg_idx` of a `term_id` app: the
/// head is rigid, an ACUI combiner (rearrangement never drops a member), or a
/// def whose body keeps the argument along determining heads
/// (`semantic.argDetermined`). Alpha-rule heads are screened by the caller.
fn argSurvivesConversion(context: *const Context, term_id: u32, arg_idx: usize) bool {
    return switch (semantic.headClass(context, term_id)) {
        .rigid, .acui => true,
        .def => semantic.argDetermined(context, term_id, arg_idx),
        .rewrite, .unavailable => false,
    };
}

/// A view, `@fresh`, or `@freshen` can re-choose a bound binder after the
/// conclusion match, so a dependency hit as matched is not decisive.
pub fn ruleMayRechooseBound(context: *const Context, rule_id: u32) bool {
    return context.views.contains(rule_id) or
        context.fresh_bindings.contains(rule_id) or
        context.freshen_bindings.contains(rule_id);
}

fn banMetasIn(
    theorem: *const TheoremContext,
    expr: ExprId,
    banned: u55,
    bans: *MetaStoreMod.MetaDepBans,
) !void {
    switch (theorem.interner.node(expr).*) {
        .variable => {},
        .placeholder => |pid| {
            const info = theorem.placeholderInfo(pid) orelse return;
            if (info.meta_id) |meta_id| try bans.ban(meta_id, banned);
        },
        .app => |app| for (app.args) |arg| try banMetasIn(theorem, arg, banned, bans),
    }
}

/// Open path for a rule without a `@view`: enumerate witnesses for open
/// bound-class binders, defer the remaining open binders as existential
/// metas, and emit the structured target.
fn openSlotRaw(slot: *OpenSlot) anyerror!void {
    const template = slot.ctx.rule.hyps[slot.at.hyp_index];
    // See `openSlotView`: open bound binders defer to the existential-meta path
    // (carry-to-leaf) rather than enumerating a concrete witness pool.
    const unknowns = try slot.ctx.context.allocator.alloc(?ExprId, slot.ctx.bindings.len);
    defer slot.ctx.context.allocator.free(unknowns);
    @memset(unknowns, null);
    var options = OpenTerms.OpenInstantiateOptions{
        .factory = .{
            .context = slot.store,
            .kind = .existential,
            .makeFn = mintStoreMeta,
        },
        .logical_unknowns = unknowns,
        .excluded = null,
        .conclusion_binders = conclusionBinderMaskOrNone(slot.ctx.rule.concl),
        .open_bound_in_combiner = slot.mode != .witness,
        .arg_infos = slot.ctx.rule.args,
    };
    const mark = slot.store.mark();
    defer slot.store.rollbackTo(mark);
    // A bound binder opens as a variable with its own dependency bit; with
    // the theorem's bits spent, the slot cannot open.
    const target = (OpenTerms.instantiateTemplateOpen(
        &slot.ctx.candidate.theorem,
        slot.ctx.context.env,
        slot.ctx.context.registry,
        template,
        slot.ctx.bindings,
        &options,
    ) catch |err| switch (err) {
        error.DependencySlotExhausted => return,
        else => return err,
    }) orelse return;
    try emitOpenTarget(slot, target, unknowns, null, null);
}

/// Open path for a rule with a `@view`: the open target is the *view*
/// hypothesis surface. `@recover` laws whose pattern/hole are pinned defer
/// their witness as one existential meta and build the source surface by the
/// leaf swap (`φ[x ↦ ?t]` instead of the raw `sb`-headed template);
/// a law that cannot fire owns its binders exclusively (no bare-meta
/// fallback for them).
fn openSlotViaView(slot: *OpenSlot, view: types.ViewDecl) anyerror!void {
    if (slot.at.hyp_index >= view.hyps.len) return;
    const theorem = &slot.ctx.candidate.theorem;
    const view_bindings = try slot.ctx.context.allocator.alloc(?ExprId, view.num_binders);
    defer slot.ctx.context.allocator.free(view_bindings);
    seedViewBindingsForMatch(
        view,
        slot.ctx.bindings,
        slot.ctx.candidate.view_concl_seed,
        view_bindings,
    );

    const excluded = try slot.ctx.context.allocator.alloc(bool, view.num_binders);
    defer slot.ctx.context.allocator.free(excluded);
    @memset(excluded, false);

    const mark = slot.store.mark();
    defer slot.store.rollbackTo(mark);

    for (view.derived_bindings) |derived_binding| {
        const rec = switch (derived_binding) {
            .recover => |r| r,
            .abstract => continue,
        };
        if (rec.target_view_idx >= view_bindings.len) continue;
        if (rec.source_view_idx >= view_bindings.len) continue;
        if (rec.pattern_view_idx >= view_bindings.len) continue;
        if (rec.hole_view_idx >= view_bindings.len) continue;
        if (view_bindings[rec.target_view_idx] != null) continue;
        if (view_bindings[rec.source_view_idx] != null) continue;
        const fired = blk: {
            const pattern = view_bindings[rec.pattern_view_idx] orelse
                break :blk false;
            const hole = view_bindings[rec.hole_view_idx] orelse
                break :blk false;
            if (view.arg_infos[rec.target_view_idx].bound) break :blk false;
            const meta = try slot.store.mint(
                theorem,
                view.arg_infos[rec.target_view_idx].sort_name,
                std.math.maxInt(u55),
                .existential,
            );
            view_bindings[rec.target_view_idx] = meta;
            view_bindings[rec.source_view_idx] = try forward.leafSwap(
                theorem,
                pattern,
                hole,
                meta,
            );
            break :blk true;
        };
        if (!fired) {
            // Recover-owned exclusion: the rule derives nothing for these
            // binders in this branch — never fall back to bare-meta deferral.
            excluded[rec.target_view_idx] = true;
            excluded[rec.source_view_idx] = true;
        }
    }

    // All open binders — including the principal quantifier's bound variable —
    // defer to the existential-meta path and are pinned to a concrete variable
    // at the leaf (carry-to-leaf). Earlier code enumerated bound binders over a
    // `@vars` witness pool here; that proved to be dead weight (the meta path
    // subsumes it: corpus byte-identical with the enumeration removed) and a
    // smell (it fired `rex`/`lall` even on purely propositional goals).
    try instantiateAndEmitView(slot, view, view_bindings, excluded);
}

/// Defer the remaining open view binders of the slot's hypothesis as
/// existential metas, instantiate the view surface, and emit it.
fn instantiateAndEmitView(
    slot: *OpenSlot,
    view: types.ViewDecl,
    view_bindings: []?ExprId,
    excluded: []const bool,
) anyerror!void {
    const unknowns = try slot.ctx.context.allocator.alloc(?ExprId, view.num_binders);
    defer slot.ctx.context.allocator.free(unknowns);
    @memset(unknowns, null);
    var options = OpenTerms.OpenInstantiateOptions{
        .factory = .{
            .context = slot.store,
            .kind = .existential,
            .makeFn = mintStoreMeta,
        },
        .logical_unknowns = unknowns,
        .excluded = excluded,
        .conclusion_binders = conclusionBinderMaskOrNone(view.concl),
        .open_bound_in_combiner = slot.mode != .witness,
        .arg_infos = view.arg_infos,
    };
    const mark = slot.store.mark();
    defer slot.store.rollbackTo(mark);
    // A bound binder opens as a variable with its own dependency bit; with
    // the theorem's bits spent, the slot cannot open.
    const target = (OpenTerms.instantiateTemplateOpen(
        &slot.ctx.candidate.theorem,
        slot.ctx.context.env,
        slot.ctx.context.registry,
        view.hyps[slot.at.hyp_index],
        view_bindings,
        &options,
    ) catch |err| switch (err) {
        error.DependencySlotExhausted => return,
        else => return err,
    }) orelse return;

    // Overlay the freshly minted per-binder metas into a local copy of the
    // view bindings so the match-back materialization covers them.
    const effective = try slot.ctx.context.allocator.dupe(?ExprId, view_bindings);
    defer slot.ctx.context.allocator.free(effective);
    for (unknowns, 0..) |maybe_meta, vi| {
        if (maybe_meta) |meta| {
            if (effective[vi] == null) effective[vi] = meta;
        }
    }
    try emitOpenTarget(slot, target, unknowns, view, effective);
}

/// Emit one structured open target: route fully concrete targets through the
/// ordinary concrete generated-slot path; otherwise enforce the rigid-root
/// (absorber) guard, let the hook solve the target, pin the parent's binders
/// from the solved metas, and continue the backtrack at the next sibling.
pub fn emitOpenTarget(
    slot: *OpenSlot,
    raw_target_in: ExprId,
    unknowns: []const ?ExprId,
    view: ?types.ViewDecl,
    view_bindings: ?[]?ExprId,
) anyerror!void {
    const theorem = &slot.ctx.candidate.theorem;
    // Canonicalize ACUI units away before the recursive solve and readback.
    // An open target can carry a redundant `emp` (e.g. a witness rule whose
    // context binder `g` is the unit, so its hypothesis instantiates to
    // `emp , (∀ x p) , [x/t]p ⊢ d`). The child's accepted conclusion comes
    // back unit-free, so without this the readback `solveCorrespondence` cannot
    // align the ACUI members to bind the carried ancestor witness. Meta leaves
    // survive normalization unchanged, so the open binders stay intact. The
    // concrete generated path already normalizes (see `tryGenerateSlot`).
    const reduced_target = try Redex.reduceRedexOnly(slot.ctx.context, theorem, raw_target_in);
    const raw_target = try normalizeAcuiUnits(slot.ctx.context, theorem, reduced_target);
    // Register the witness metas threaded in from enclosing open slots before
    // anything reads the store: an unregistered ancestor leaf counts as
    // solved, which would send a target carrying one down the concrete route
    // below, where `hook.solve` cannot lift a placeholder and drops it. Also
    // before the rollback mark, so the registration survives the per-pass
    // rollbacks: every pass (concrete-member, child `solveOpen`, coupled)
    // needs the ancestor leaves bindable, and `solveOpen`'s hint reintern
    // bails outright on an unregistered meta. Registration is trailed and
    // unwound by `tryOpenGenerateSlot`'s outer mark, so it does not leak past
    // this slot. Only `.witness` open slots carry witness metas, except under
    // an open root (`hook.open_root`): there a constrained slot carries its
    // ancestors' metas too, the root's hole metas and those minted between.
    if (slot.mode == .witness or (slot.mode == .constrained and slot.hook.open_root)) {
        try registerAncestorMetas(slot.store, theorem, raw_target);
    }
    if (slot.store.isFullySolved(theorem, raw_target)) {
        // A meta the bindings still hold but the target no longer mentions
        // dangles: a fresh variable the premise substitutes away
        // (`nat_ind_elim`'s base case `g ⊢ z : [k/zero] C` still holds `k`
        // in `C`), or an erased witness (`PoolPick.dangling`). No proof of
        // the premise can determine it, so the concrete route below could
        // only send the branch to validation with it undeterminable. It takes
        // a `@vars` name now instead, and the solved-target pinning path
        // renders the explicit binding the validator requires.
        if (slot.fresh_bound and
            try tryPoolWitnesses(slot, raw_target, unknowns, view, view_bindings, .fresh)) return;
        if (slot.mode == .witness and slot.hook.allow_invent_witness and
            try tryPoolWitnesses(slot, raw_target, unknowns, view, view_bindings, .dangling)) return;
        // Bound-witness enumeration closed every open binder: this is an
        // ordinary concrete generated slot (for view rules, a concrete
        // view-surface target the validator reconciles through the view
        // machinery).
        try emitGeneratedSlot(slot.ctx, slot.hook, slot.at, raw_target);
        return;
    }
    // Steps 4–5: reject bare-meta targets and targets with no rigid root (the
    // forward absorber check, reused as the "no useful concrete shape"
    // first line). Erring on the forced side: a target this open would make
    // child search guessing, not deduction.
    switch (theorem.interner.node(raw_target).*) {
        .app => {},
        .variable, .placeholder => return,
    }

    const candidates_before = slot.ctx.candidates.items.len;
    const mark = slot.store.mark();

    // Force-first is a *witness-rule* optimization: only a `.witness` open
    // slot defers a witness that a leaf must force. Gate on that so
    // witness-free `.constrained` open generation (notably `@abstract` motive
    // inference, which has no `@auto` rule but still mints open metas) keeps
    // its original child-search-first ordering untouched.
    if (slot.mode == .witness) {
        // Witness migration: FORCE the carried witness by the cheap,
        // deterministic concrete-member pass first (e.g. an `ax` leaf whose
        // `[x/t]p` instance must equal a concrete succedent member uniquely
        // determines `t`). Pinning the witness from a member identity here —
        // rather than enumerating candidate witnesses in the child search and
        // reading one back — collapses the per-level `open_child_max_results`
        // fan that otherwise compounds through nested open targets. The
        // expensive O(n²) coupled pass is left last (`try_coupled = false`).
        // Every emitted fill is still revalidated by `tryCandidate`.
        try tryAcuiMemberWitnesses(slot, raw_target, unknowns, view, view_bindings, false);
        if (slot.ctx.candidates.items.len != candidates_before) return;
        slot.store.rollbackTo(mark);
        try solveOpenTargetByChild(slot, raw_target, unknowns, view, view_bindings);
        if (slot.ctx.candidates.items.len != candidates_before) return;
        slot.store.rollbackTo(mark);
        try tryCoupledWitnesses(slot, raw_target, unknowns, view, view_bindings);
        if (slot.ctx.candidates.items.len != candidates_before) return;
        // Last resort: the witness is genuinely free — invent it from the
        // `@vars` pool. The flag is set whenever the theory has a pool; the
        // forced passes above stay the default because they run first and
        // this rung is reached only when they leave metas unsolved.
        if (slot.hook.allow_invent_witness) {
            slot.store.rollbackTo(mark);
            _ = try tryPoolWitnesses(slot, raw_target, unknowns, view, view_bindings, .shared);
        }
        return;
    }

    // Witness-free open target (e.g. `@abstract` motive inference): keep the
    // original child-search-first ordering, with member/coupled witness
    // enumeration as the fallback.
    try solveOpenTargetByChild(slot, raw_target, unknowns, view, view_bindings);
    if (slot.ctx.candidates.items.len != candidates_before) return;
    slot.store.rollbackTo(mark);
    try tryAcuiMemberWitnesses(slot, raw_target, unknowns, view, view_bindings, true);
    if (slot.ctx.candidates.items.len != candidates_before) return;
    // No proof below fixed the variable (`weaken` only echoes it back), so
    // any fresh one will do.
    if (slot.fresh_bound) {
        slot.store.rollbackTo(mark);
        _ = try tryPoolWitnesses(slot, raw_target, unknowns, view, view_bindings, .fresh);
    }
}

/// Solve an open target by child search (`GenerationHook.solveOpen`),
/// continuing the slot from each child proof in turn until one continuation
/// emits a candidate.
fn solveOpenTargetByChild(
    slot: *OpenSlot,
    raw_target: ExprId,
    unknowns: []const ?ExprId,
    view: ?types.ViewDecl,
    view_bindings: ?[]const ?ExprId,
) anyerror!void {
    const Continuation = struct {
        slot: *OpenSlot,
        raw_target: ExprId,
        unknowns: []const ?ExprId,
        view: ?types.ViewDecl,
        view_bindings: ?[]const ?ExprId,
        candidates_before: usize,

        fn accept(ctx: *anyopaque, proof: types.GeneratedProof) anyerror!bool {
            const self: *@This() = @ptrCast(@alignCast(ctx));
            try continueOpenTargetSolved(
                self.slot,
                self.raw_target,
                self.unknowns,
                self.view,
                self.view_bindings,
                proof,
            );
            return self.slot.ctx.candidates.items.len != self.candidates_before;
        }
    };
    var continuation = Continuation{
        .slot = slot,
        .raw_target = raw_target,
        .unknowns = unknowns,
        .view = view,
        .view_bindings = view_bindings,
        .candidates_before = slot.ctx.candidates.items.len,
    };
    try slot.hook.solveOpen(
        raw_target,
        &slot.ctx.candidate.theorem,
        slot.store,
        slot.eagerStep(),
        .{ .ctx = &continuation, .acceptFn = Continuation.accept },
    );
}

/// Continue a structured open slot whose metas are all solved in the store:
/// pin the parent's binders from the solved metas, prune, flag the binders
/// for explicit-binding rendering, and resume the backtrack. With `proof`
/// set this is the open-hook success path (the child's accepted conclusion
/// must equal the materialized target); with `proof == null` (the
/// member-witness path) the now-concrete target is routed through the
/// ordinary concrete generation pipeline instead.
fn continueOpenTargetSolved(
    slot: *OpenSlot,
    raw_target: ExprId,
    unknowns: []const ?ExprId,
    view: ?types.ViewDecl,
    view_bindings: ?[]const ?ExprId,
    proof: ?types.GeneratedProof,
) anyerror!void {
    const theorem = &slot.ctx.candidate.theorem;
    // The metas the target mentions must all be solved; the materialized
    // target is the concrete hypothesis this branch commits to.
    const concrete_target = slot.store.materialize(theorem, raw_target) catch {
        return;
    };
    if (proof) |p| {
        if (concrete_target != p.conclusion) return;
    }

    // Pin parent binders from the solved metas, remembering exactly which
    // binders this fill set (and their prior value) so they roll back with the
    // branch and render as explicit bindings on the final application.
    const Flag = struct { idx: usize, orig: ?ExprId };
    var flagged = std.ArrayListUnmanaged(Flag).empty;
    defer flagged.deinit(slot.ctx.context.allocator);
    var solve_failed = false;
    if (view) |v| {
        const vb = try slot.ctx.context.allocator.dupe(?ExprId, view_bindings.?);
        defer slot.ctx.context.allocator.free(vb);
        for (vb) |*entry| {
            const value = entry.* orelse continue;
            // A view binder whose meta is still unsolved is left unpinned (the
            // binder_map loop skips null and `tryCandidate` infers it from the
            // goal). On the member/coupled witness paths every binding is
            // already solved, so this is inert there; only the invented-witness
            // path reaches here with an open context binder (e.g. `g`/`d`) that
            // never appeared in the now-concrete `raw_target`.
            entry.* = slot.store.materialize(theorem, value) catch null;
        }
        for (v.binder_map, 0..) |maybe_rule_idx, vi| {
            const rule_idx = maybe_rule_idx orelse continue;
            if (rule_idx >= slot.ctx.bindings.len) continue;
            if (slot.ctx.bindings[rule_idx] != null) continue;
            const value = vb[vi] orelse continue;
            slot.ctx.bindings[rule_idx] = value;
            try flagged.append(slot.ctx.context.allocator, .{ .idx = rule_idx, .orig = null });
        }
    } else {
        for (unknowns, 0..) |maybe_meta, idx| {
            const meta = maybe_meta orelse continue;
            const value = slot.store.materialize(theorem, meta) catch {
                solve_failed = true;
                break;
            };
            if (slot.ctx.bindings[idx] == null) {
                slot.ctx.bindings[idx] = value;
                try flagged.append(slot.ctx.context.allocator, .{ .idx = idx, .orig = null });
            }
        }
    }
    // Carry-to-leaf: a binder whose value mentions an ancestor witness meta
    // that just got solved at this leaf must be re-materialized and rendered
    // explicitly, so its now-concrete value reaches the slot that minted the
    // meta (via the conclusion of the assembled child proof). Inert unless an
    // ancestor meta is present (only the cross-boundary generation path).
    var coupled = false;
    if (!solve_failed) {
        for (slot.ctx.bindings, 0..) |maybe_val, idx| {
            const val = maybe_val orelse continue;
            var already = false;
            for (flagged.items) |f| {
                if (f.idx == idx) {
                    already = true;
                    break;
                }
            }
            if (already) continue;
            const rebound = idx < 64 and slot.rebound & (@as(u64, 1) << @intCast(idx)) != 0;
            if (!rebound and !slot.store.exprMentionsAncestor(theorem, val)) continue;
            // A value still holding an unsolved meta is not this leaf's to
            // fill (another slot's witness): it stays unrendered, for the
            // checker to infer.
            const concrete = slot.store.materialize(theorem, val) catch continue;
            if (concrete == val) continue;
            slot.ctx.bindings[idx] = concrete;
            try flagged.append(slot.ctx.context.allocator, .{ .idx = idx, .orig = val });
            coupled = true;
        }
    }
    // Carry-to-leaf only: this slot is being validated against a holey
    // (implicit-whole-conclusion) goal — the open-generation child has no
    // concrete conclusion to infer the rule's conclusion-pinned binders from,
    // so `tryCandidate`'s binder inference leaves them null
    // (`MissingBinderAssignment`). Because the coupled solve has already pinned
    // *every* binder in the search, render them all as explicit bindings so the
    // holey-goal validation needs no inference. Gated on `coupled` (an ancestor
    // witness flowed back here) so the single-witness path — used by the
    // byte-identical broad corpus — is untouched.
    if (coupled) {
        for (slot.ctx.bindings, 0..) |maybe_val, idx| {
            const val = maybe_val orelse continue;
            var already = false;
            for (flagged.items) |f| {
                if (f.idx == idx) {
                    already = true;
                    break;
                }
            }
            if (already) continue;
            try flagged.append(slot.ctx.context.allocator, .{ .idx = idx, .orig = val });
        }
    }
    defer for (flagged.items) |f| {
        slot.ctx.bindings[f.idx] = f.orig;
    };
    if (solve_failed) return;

    // Same incremental prune as the pool-ref loop: a fill whose pinned
    // binders contradict the conclusion-vs-goal correspondence dooms every
    // tuple under it.
    if (!slot.ctx.conclusionPlausible()) {
        if (slot.ctx.counters) |c| c.final_conclusion_prunes += 1;
        return;
    }

    const explicit = try slot.ctx.context.allocator.alloc(ExplicitFlag, flagged.items.len);
    defer slot.ctx.context.allocator.free(explicit);
    for (flagged.items, explicit) |f, *e| e.* = try setExplicitFlag(slot.ctx.candidate, f.idx);
    defer for (explicit) |e| e.restore(slot.ctx.candidate);

    if (proof) |p| {
        try slot.ctx.descendGenerated(slot.at.depth, slot.at.position, p.application);
        return;
    }
    try emitGeneratedSlot(slot.ctx, slot.hook, slot.at, concrete_target);
}

/// Cap on member-witness fills attempted per open slot. The domain is the
/// target's own concrete ACUI members, so this is small in practice; the cap
/// is a hard brake on pathological member × fragment products.
const max_member_witness_attempts: usize = 8;

/// ACUI finite-domain witness enumeration. The open
/// target's own ACUI regions hold concrete members (`A ∈ A ⊢ ?t ∈ A` —
/// the context member shows the witness `?t := A`); matching each
/// meta-bearing fragment of the target against each member proposes
/// assignments by the same structural correspondence the open hook uses.
/// Only fills that solve the target completely are pursued (the concrete
/// target then runs the ordinary generation pipeline, and `tryCandidate`
/// still validates the whole assembly); partial fills are rolled back.
/// Concrete members come first by construction — metas never enter the
/// domain — and each distinct fill is attempted once.
pub fn tryAcuiMemberWitnesses(
    slot: *OpenSlot,
    raw_target: ExprId,
    unknowns: []const ?ExprId,
    view: ?types.ViewDecl,
    view_bindings: ?[]const ?ExprId,
    try_coupled: bool,
) anyerror!void {
    const theorem = &slot.ctx.candidate.theorem;

    // Collect meta fragments first and bail before the (more expensive) domain
    // member walk when the target has none — the common case for open targets
    // that carry no witness meta (e.g. `@abstract` motive slots), so they pay
    // almost nothing for this now-first pass.
    var fragments: [Witness.max_fragments]ExprId = undefined;
    const fragment_count = Witness.collectMetaFragments(
        theorem,
        slot.store,
        raw_target,
        &fragments,
    );
    if (fragment_count == 0) return;
    var members: [Witness.max_domain_members]ExprId = undefined;
    const member_count = Witness.collectDomainMembers(
        slot.ctx.context,
        theorem,
        raw_target,
        &members,
    );

    // Distinct materialized targets already attempted: two members often
    // propose the same fill (shared subterms), and one child solve per
    // distinct fill is enough.
    var seen: [max_member_witness_attempts]ExprId = undefined;
    var attempts: usize = 0;
    const before_concrete = slot.ctx.candidates.items.len;
    for (members[0..member_count]) |member| {
        for (fragments[0..fragment_count]) |fragment| {
            if (attempts >= max_member_witness_attempts) break;
            const mark = slot.store.mark();
            if (!Witness.matchFragmentToMember(
                slot.ctx.context,
                slot.store,
                theorem,
                fragment,
                member,
            )) continue;
            try pursueSolvedWitnessFill(
                slot,
                raw_target,
                unknowns,
                view,
                view_bindings,
                &seen,
                &attempts,
            );
            slot.store.rollbackTo(mark);
        }
    }

    // Coupled-witness fallback (carry-to-leaf): when the concrete pass found
    // nothing, two metas may be jointly forced by an `ax`-style member
    // identity — an antecedent member must unify with a succedent member,
    // binding metas on both sides (e.g. `R ?t ey` = `R ez ?w` → `?t:=ez`,
    // `?w:=ey`). One of those metas is typically an ancestor witness; solving
    // it here concretizes the conclusion that carries it back up.
    if (try_coupled and slot.ctx.candidates.items.len == before_concrete) {
        try tryCoupledWitnesses(slot, raw_target, unknowns, view, view_bindings);
    }
}

/// Shared tail of every witness-enumeration loop (member, equal-coupled,
/// complementary-coupled): if the store's current assignments fully solve
/// `raw_target`, materialize it, dedupe against `seen`, and pursue the fill
/// through `continueOpenTargetSolved`. Abstains (returns early) otherwise;
/// the caller owns the mark/rollback bracket around each attempt.
fn pursueSolvedWitnessFill(
    slot: *OpenSlot,
    raw_target: ExprId,
    unknowns: []const ?ExprId,
    view: ?types.ViewDecl,
    view_bindings: ?[]const ?ExprId,
    seen: *[max_member_witness_attempts]ExprId,
    attempts: *usize,
) anyerror!void {
    const theorem = &slot.ctx.candidate.theorem;
    if (!slot.store.isFullySolved(theorem, raw_target)) return;
    const concrete = slot.store.materialize(theorem, raw_target) catch return;
    for (seen[0..attempts.*]) |prior| {
        if (prior == concrete) return;
    }
    seen[attempts.*] = concrete;
    attempts.* += 1;
    if (slot.ctx.counters) |c| c.acui_witness_attempts += 1;
    try continueOpenTargetSolved(
        slot,
        raw_target,
        unknowns,
        view,
        view_bindings,
        null,
    );
}

/// Walk `expr` and register every ancestor-witness meta leaf (stable
/// `meta_id`, not yet locally registered) in `store`, so the leaf unification
/// can bind it. See `MetaStore.registerAncestorMeta`.
fn registerAncestorMetas(
    store: *MetaStore,
    theorem: *const TheoremContext,
    expr: ExprId,
) anyerror!void {
    switch (theorem.interner.node(expr).*) {
        .variable => {},
        .placeholder => try store.registerAncestorMeta(theorem, expr),
        .app => |app| {
            for (app.args) |arg| {
                try registerAncestorMetas(store, theorem, arg);
            }
        },
    }
}

/// Meta-meta unification fallback: unify each pair of distinct meta-bearing
/// region members; a success that fully solves the target is pursued through
/// the ordinary concrete generation pipeline (and `tryCandidate` revalidates).
fn tryCoupledWitnesses(
    slot: *OpenSlot,
    raw_target: ExprId,
    unknowns: []const ?ExprId,
    view: ?types.ViewDecl,
    view_bindings: ?[]const ?ExprId,
) anyerror!void {
    const theorem = &slot.ctx.candidate.theorem;

    // The ancestor witness metas this pass may bind were registered by
    // `emitOpenTarget`, under its open-root gate.
    var members: [Witness.max_domain_members]ExprId = undefined;
    const member_count = Witness.collectMetaMembers(
        slot.ctx.context,
        slot.store,
        theorem,
        raw_target,
        &members,
    );
    if (member_count == 0) return;
    const before_coupled = slot.ctx.candidates.items.len;
    var seen: [max_member_witness_attempts]ExprId = undefined;
    var attempts: usize = 0;
    if (member_count >= 2) try tryPairedMembers(
        slot,
        raw_target,
        unknowns,
        view,
        view_bindings,
        members[0..member_count],
        &seen,
        &attempts,
    );
    if (attempts >= max_member_witness_attempts) return;

    // Anchored closure: nothing paired inside a region, but a
    // hypothesis-free rule may identify a region member with a position
    // outside every region — `ax`'s `g , a ⊢ a` pairs a context member with
    // the succedent. A meta-bearing member (`R ?t y`, an `all_left`
    // instance) and the formula at that position (`R z ?w`, an `ex_intro`
    // premise) are co-solved through the shape, which needs only ONE
    // meta-bearing member. Same guard as the complementary pass: runs only
    // when the region sweeps emitted nothing.
    if (slot.ctx.candidates.items.len != before_coupled) return;
    var anchors: [Witness.max_anchor_shapes]Witness.AnchorShape = undefined;
    const anchor_count = Witness.collectAnchorShapes(slot.ctx.context, &anchors);
    for (anchors[0..anchor_count]) |shape| {
        const anchor = Witness.anchorSubterm(theorem, shape, raw_target) orelse continue;
        for (members[0..member_count]) |member| {
            if (attempts >= max_member_witness_attempts) return;
            const mark = slot.store.mark();
            if (Witness.unifyMemberWithAnchor(
                slot.store,
                theorem,
                shape,
                member,
                anchor,
            )) {
                try pursueSolvedWitnessFill(
                    slot,
                    raw_target,
                    unknowns,
                    view,
                    view_bindings,
                    &seen,
                    &attempts,
                );
            }
            slot.store.rollbackTo(mark);
        }
    }
}

/// The region-pair sweeps of `tryCoupledWitnesses`: equal unification of two
/// meta-bearing members, then (if that emitted nothing) the complementary
/// closure through a rule's repeated-binder member pair.
fn tryPairedMembers(
    slot: *OpenSlot,
    raw_target: ExprId,
    unknowns: []const ?ExprId,
    view: ?types.ViewDecl,
    view_bindings: ?[]const ?ExprId,
    members: []const ExprId,
    seen: *[max_member_witness_attempts]ExprId,
    attempts: *usize,
) anyerror!void {
    const theorem = &slot.ctx.candidate.theorem;
    const before_coupled = slot.ctx.candidates.items.len;
    for (members, 0..) |a, i| {
        for (members, 0..) |b, j| {
            if (i >= j) continue;
            if (attempts.* >= max_member_witness_attempts) return;
            const mark = slot.store.mark();
            if (Witness.unifyMembers(slot.store, theorem, a, b)) {
                try pursueSolvedWitnessFill(
                    slot,
                    raw_target,
                    unknowns,
                    view,
                    view_bindings,
                    seen,
                    attempts,
                );
            }
            slot.store.rollbackTo(mark);
        }
    }

    // Complementary closure: no pair unifies EQUAL, but a hypothesis-free
    // rule may declare a complementation — `ax`'s `⊢ a , (¬ a) , d` repeats
    // binder `a` across two members — so two meta-bearing goal members
    // related by the repeated binder (`¬ R ?x y` vs `R z ?w`, both `rex`
    // witness outputs with no rigid anchor) are co-solved through the
    // template pair. The shapes come from the visible rule templates alone;
    // the engine never knows the wrapper means negation. Runs only when the
    // equal-unify sweep emitted nothing, so existing outcomes are untouched,
    // and every fill is revalidated by the child search plus `tryCandidate`.
    if (slot.ctx.candidates.items.len != before_coupled) return;
    var shapes: [Witness.max_complement_shapes]Witness.ComplementShape = undefined;
    const shape_count = Witness.collectComplementShapes(slot.ctx.context, &shapes);
    if (shape_count == 0) return;
    for (members, 0..) |member_a, i| {
        for (members, 0..) |member_b, j| {
            if (i == j) continue;
            for (shapes[0..shape_count]) |shape| {
                if (attempts.* >= max_member_witness_attempts) return;
                const mark = slot.store.mark();
                if (Witness.unifyMembersThroughShape(
                    slot.store,
                    theorem,
                    shape,
                    member_a,
                    member_b,
                )) {
                    try pursueSolvedWitnessFill(
                        slot,
                        raw_target,
                        unknowns,
                        view,
                        view_bindings,
                        seen,
                        attempts,
                    );
                }
                slot.store.rollbackTo(mark);
            }
        }
    }
}

/// Which `@vars` variables `tryPoolWitnesses` gives the unsolved metas.
const PoolPick = enum {
    /// The invented witness, the ladder's last rung (`allow_invent_witness`,
    /// set whenever the theory has a `@vars` pool): an open target still
    /// carrying unsolved existential metas after the concrete-member and
    /// coupled passes has a *genuinely free* witness — e.g. the `y` in
    /// `(∀x P x) → (∃y P y)`, which any domain element satisfies. The calculus
    /// is sound only over a non-empty domain, so completeness here requires
    /// *picking* a witness rather than forcing one. Every meta takes the first
    /// pool dummy of its sort, in sorted token order, that `assign` accepts
    /// (its dep-mask check is the theory-agnostic guard against a witness that
    /// would capture an in-scope bound variable). This is the "diagonal"
    /// assignment: the coupled slots of one chain pick the SAME witness, so an
    /// equality the proof implies between the metas holds (the `lall`
    /// instantiation and `rex` witness in `all_ex_inst` must coincide).
    shared,
    /// `fresh_bound`, after the child search left the slot's opened bound
    /// metas unsolved: each takes a variable occurring in no binding of the
    /// rule, distinct from every variable of the instance and from the other
    /// fills. Names the refs use in the same place come first
    /// (`assignRefNames`), then the first free `@vars` names
    /// (`fillFromPool`). Any other meta (a view binder) must come from
    /// the child search.
    fresh,
    /// A witness meta *erased* from a fully solved target, the invention
    /// rung's last resort: a vacuous `@recover` body makes the leaf swap
    /// `p[x ↦ ?t]` a no-op, and redex reduction can collapse `[x/?t]p` to `p`
    /// when `x` is not free in `p`. The meta then dangles in the bindings, so
    /// the concrete route sends the branch to validation with the witness
    /// binder undeterminable. Such a witness is genuinely unconstrained; each
    /// one the bindings or the view's still hold is filled like `shared`.
    dangling,
};

/// Ground every unsolved meta of `raw_target` to a `@vars`-pool dummy per
/// `pick`, then continue like the member- and coupled-witness passes:
/// `continueOpenTargetSolved` pins the parent's binders from the solved
/// metas, flags them for explicit-binding rendering (a witness is not
/// inferable from a freshly generated premise, and a bare generated
/// `lall`/`rex` leaves it unassigned → `MissingBinderAssignment`), and resumes
/// the backtrack. Nothing is minted: the dummies are pre-materialized pool
/// tokens (generate.zig), reinterned by `internParsedExpr`, so no dependency
/// bit is consumed however many slots request one. A meta whose sort has no
/// acceptable pool token fails the branch. `tryCandidate` revalidates every
/// fill. Returns whether any meta needed a fill.
pub fn tryPoolWitnesses(
    slot: *OpenSlot,
    raw_target: ExprId,
    unknowns: []const ?ExprId,
    view: ?types.ViewDecl,
    view_bindings: ?[]const ?ExprId,
    pick: PoolPick,
) anyerror!bool {
    const theorem = &slot.ctx.candidate.theorem;
    var unsolved = std.ArrayListUnmanaged(PlaceholderId).empty;
    defer unsolved.deinit(slot.ctx.context.allocator);
    try slot.store.collectUnsolved(theorem, raw_target, &unsolved);
    switch (pick) {
        .shared => {},
        .fresh => try collectSlotUnsolved(slot, unknowns, &unsolved),
        .dangling => {
            if (view_bindings) |vb| {
                for (vb) |maybe| if (maybe) |b| try slot.store.collectUnsolved(theorem, b, &unsolved);
            }
            for (unknowns) |maybe| if (maybe) |b| try slot.store.collectUnsolved(theorem, b, &unsolved);
        },
    }
    if (unsolved.items.len == 0) return false;

    const mark = slot.store.mark();
    defer slot.store.rollbackTo(mark);
    switch (pick) {
        .shared, .dangling => {
            var taken = bindingDeps(slot, theorem);
            if (!try fillFromPool(slot, theorem, unsolved.items, &taken, false)) return true;
        },
        .fresh => {
            var taken = bindingDeps(slot, theorem);
            const ref_names = try slot.ctx.context.allocator.alloc(ExprId, unsolved.items.len);
            defer slot.ctx.context.allocator.free(ref_names);
            if (try assignRefNames(slot, theorem, raw_target, unknowns, unsolved.items)) {
                for (unsolved.items, ref_names) |meta_id, *name| name.* = slot.store.lookup(meta_id).?;
                const before = slot.ctx.candidates.items.len;
                if (slot.store.isFullySolved(theorem, raw_target)) {
                    try continueOpenTargetSolved(slot, raw_target, unknowns, view, view_bindings, null);
                }
                if (slot.ctx.candidates.items.len != before) return true;
                slot.store.rollbackTo(mark);
                if (!try fillFromPool(slot, theorem, unsolved.items, &taken, true)) return true;
                // The blind pick repeats the ref-named attempt.
                for (unsolved.items, ref_names) |meta_id, name| {
                    if (slot.store.lookup(meta_id).? != name) break;
                } else return true;
            } else {
                // A false return can leave some names assigned; the blind
                // pick names every variable afresh.
                slot.store.rollbackTo(mark);
                if (!try fillFromPool(slot, theorem, unsolved.items, &taken, true)) return true;
            }
        },
    }
    if (!slot.store.isFullySolved(theorem, raw_target)) return true;
    try continueOpenTargetSolved(slot, raw_target, unknowns, view, view_bindings, null);
    return true;
}

/// Append the unsolved `.bound_choice` metas the slot's bindings and opened
/// binders still hold to `out`, skipping those already listed. Other metas
/// there (an open root's carried ones) are not this slot's to name.
fn collectSlotUnsolved(
    slot: *const OpenSlot,
    unknowns: []const ?ExprId,
    out: *std.ArrayListUnmanaged(PlaceholderId),
) !void {
    const theorem = &slot.ctx.candidate.theorem;
    var found = std.ArrayListUnmanaged(PlaceholderId).empty;
    defer found.deinit(slot.store.allocator);
    for (slot.ctx.bindings) |maybe| if (maybe) |value| try slot.store.collectUnsolved(theorem, value, &found);
    for (unknowns) |maybe| if (maybe) |value| try slot.store.collectUnsolved(theorem, value, &found);
    for (found.items) |meta_id| {
        if (slot.store.info(meta_id).?.kind != .bound_choice) continue;
        if (std.mem.indexOfScalar(PlaceholderId, out.items, meta_id) != null) continue;
        try out.append(slot.store.allocator, meta_id);
    }
}

/// The dependency bits of every variable the rule's bindings mention: what a
/// fresh variable must avoid.
fn bindingDeps(slot: *const OpenSlot, theorem: *const TheoremContext) u55 {
    var taken: u55 = 0;
    for (slot.ctx.bindings) |maybe| {
        const value = maybe orelse continue;
        taken |= (theorem.exprDeps(value, .{}) catch 0);
    }
    return taken;
}

/// Name the slot's fresh variables after the refs. MM0 has no
/// alpha-equivalence, so the name decides which refs a proof of the premise
/// can use. The first free `@vars` names in sorted order give
/// `nat_ind_elim`'s step premise `g , k : Nat , ih : C ⊢ …` the names
/// `ih` for `k` and `k` for `ih`, and no add_comm line `g , k : Nat ⊢ …`
/// fits it any more. So every part of the target or the bindings that
/// mentions an unsolved variable (the bindings still hold one the target
/// substituted away) is matched against every same-headed subterm of the refs
/// (`g , ?k : Nat` against `g , k : Nat`), and each variable takes the bound
/// variable those matches put in its place most often, ties going to the
/// first seen. A name must still occur in no binding and differ from the
/// other fills; a variable no ref names takes the first free `@vars` name
/// (`fillFromPool`). Returns false when no ref names any variable, one of
/// them is not a `.bound_choice` meta, or one cannot be filled; the caller's
/// rollback undoes any fills made before that.
fn assignRefNames(
    slot: *OpenSlot,
    theorem: *TheoremContext,
    raw_target: ExprId,
    unknowns: []const ?ExprId,
    unsolved: []const PlaceholderId,
) !bool {
    const allocator = slot.ctx.context.allocator;
    for (unsolved) |meta_id| {
        const meta = slot.store.info(meta_id) orelse return false;
        if (meta.kind != .bound_choice) return false;
    }
    var tally = RefNameTally{
        .slot = slot,
        .theorem = theorem,
        .unsolved = unsolved,
    };
    defer tally.deinit(allocator);
    try tally.collectParts(raw_target);
    for (slot.ctx.bindings) |maybe| if (maybe) |value| try tally.collectParts(value);
    for (unknowns) |maybe| if (maybe) |value| try tally.collectParts(value);
    if (tally.parts.items.len == 0) return false;
    for (slot.ctx.ref_index.entries) |entry| {
        try theorem.exprForEach(entry.expr, &tally, RefNameTally.visit);
    }
    if (tally.votes.count() == 0) return false;

    var taken = bindingDeps(slot, theorem);
    var named = false;
    for (unsolved) |meta_id| {
        // Most votes first; `votes` keeps first-seen order for ties.
        var best: ?ExprId = null;
        var best_deps: u55 = 0;
        var best_count: u32 = 0;
        var it = tally.votes.iterator();
        while (it.next()) |vote| {
            if (vote.key_ptr.meta != meta_id or vote.value_ptr.* <= best_count) continue;
            const info = (theorem.currentLeafInfo(vote.key_ptr.name) catch null) orelse continue;
            if (info.deps & taken != 0) continue;
            best = vote.key_ptr.name;
            best_deps = info.deps;
            best_count = vote.value_ptr.*;
        }
        const name = best orelse continue;
        slot.store.assign(theorem, meta_id, name) catch continue;
        taken |= best_deps;
        named = true;
    }
    if (!named) return false;
    return fillFromPool(slot, theorem, unsolved, &taken, true);
}

/// `assignRefNames`'s tally: which bound variable each ref subterm puts in
/// place of each unsolved variable, matched against the target's parts.
const RefNameTally = struct {
    slot: *OpenSlot,
    theorem: *TheoremContext,
    unsolved: []const PlaceholderId,
    /// App subterms of the target and bindings that mention an unsolved
    /// variable.
    parts: std.ArrayListUnmanaged(ExprId) = .empty,
    /// Ref subterms already matched (refs share subterms).
    seen: std.AutoHashMapUnmanaged(ExprId, void) = .{},
    votes: std.AutoArrayHashMapUnmanaged(Vote, u32) = .{},

    const Vote = struct { meta: PlaceholderId, name: ExprId };

    fn deinit(self: *RefNameTally, allocator: std.mem.Allocator) void {
        self.parts.deinit(allocator);
        self.seen.deinit(allocator);
        self.votes.deinit(allocator);
    }

    fn collectParts(self: *RefNameTally, expr: ExprId) !void {
        const app = switch (self.theorem.interner.node(expr).*) {
            .app => |app| app,
            .variable, .placeholder => return,
        };
        if (!self.mentionsUnsolved(expr)) return;
        for (self.parts.items) |part| {
            if (part == expr) return;
        }
        try self.parts.append(self.slot.ctx.context.allocator, expr);
        for (app.args) |arg| try self.collectParts(arg);
    }

    fn mentionsUnsolved(self: *const RefNameTally, expr: ExprId) bool {
        return switch (self.theorem.interner.node(expr).*) {
            .variable => false,
            .placeholder => |pid| std.mem.indexOfScalar(PlaceholderId, self.unsolved, pid) != null,
            .app => |app| for (app.args) |arg| {
                if (self.mentionsUnsolved(arg)) break true;
            } else false,
        };
    }

    fn visit(self: *RefNameTally, theorem: *const TheoremContext, sub: ExprId) anyerror!void {
        const sub_app = switch (theorem.interner.node(sub).*) {
            .app => |app| app,
            .variable, .placeholder => return,
        };
        const allocator = self.slot.ctx.context.allocator;
        if ((try self.seen.getOrPut(allocator, sub)).found_existing) return;
        const store = self.slot.store;
        for (self.parts.items) |part| {
            if (theorem.interner.node(part).app.term_id != sub_app.term_id) continue;
            const mark = store.mark();
            defer store.rollbackTo(mark);
            if (forward.solveCorrespondence(store, self.theorem, sub, part, null) != .ok) continue;
            for (self.unsolved) |meta_id| {
                const name = store.lookup(meta_id) orelse continue;
                const info = (theorem.currentLeafInfo(name) catch null) orelse continue;
                if (!info.bound) continue;
                const gop = try self.votes.getOrPut(allocator, .{ .meta = meta_id, .name = name });
                gop.value_ptr.* = if (gop.found_existing) gop.value_ptr.* + 1 else 1;
            }
        }
    }
};

/// Fill each still unassigned meta of `metas` from the `@vars` pool, a
/// `.bound_choice` one with a variable outside `taken` that then joins it
/// (`boundAvoid`). With `require_bound`, every meta must be a `.bound_choice`
/// one. False when one cannot be filled; the caller's rollback undoes the
/// fills made before it.
fn fillFromPool(
    slot: *OpenSlot,
    theorem: *TheoremContext,
    metas: []const PlaceholderId,
    taken: *u55,
    require_bound: bool,
) !bool {
    for (metas) |meta_id| {
        if (slot.store.lookup(meta_id) != null) continue;
        const meta = slot.store.info(meta_id) orelse return false;
        if (require_bound and meta.kind != .bound_choice) return false;
        if (!try assignPoolWitness(slot, theorem, meta_id, meta.sort_name, boundAvoid(meta.kind, taken))) return false;
    }
    return true;
}

/// The avoid set for a pool fill of a meta of `kind`: a `.bound_choice` meta
/// is a bound variable, so it must be none of the instance's variables and
/// none of the other fills; a witness may be any of them.
fn boundAvoid(kind: OpenTerms.MetaKind, taken: *u55) ?*u55 {
    return if (kind == .bound_choice) taken else null;
}

/// Assign `meta_id` a `@vars`-pool dummy of `sort_name`, trying tokens in sorted
/// order and committing the first that `store.assign` accepts (its dep-mask /
/// sort / occurs checks reject a witness that would capture an in-scope bound
/// variable). With `avoid`, a dummy must also be a variable none of whose
/// dependency bits are in `avoid.*`, and its bits join the set. Returns true
/// on success. The dummies were pre-materialized into the work theorem
/// (generate.zig) and registered in `theorem_vars`; reinterning the parser var
/// here is dependency-free. A successful `assign` records a trail entry; a
/// rejected one records nothing, so the caller's single mark/rollback covers
/// the whole loop.
fn assignPoolWitness(
    slot: *OpenSlot,
    theorem: *TheoremContext,
    meta_id: PlaceholderId,
    sort_name: []const u8,
    avoid: ?*u55,
) !bool {
    var pool = try PoolVars.init(
        slot.ctx.context.allocator,
        slot.ctx.context.sort_vars,
        sort_name,
        theorem,
        slot.ctx.theorem_vars,
    );
    defer pool.deinit();
    while (try pool.nextAvoiding(if (avoid) |taken| taken.* else null)) |pool_var| {
        slot.store.assign(theorem, meta_id, pool_var.expr) catch continue;
        if (avoid) |taken| taken.* |= pool_var.deps;
        return true;
    }
    return false;
}

/// `PlaceholderFactory.makeFn` minting branch-local existential metas.
fn mintStoreMeta(
    ctx: ?*anyopaque,
    theorem: *TheoremContext,
    sort_name: []const u8,
    kind: OpenTerms.MetaKind,
) anyerror!ExprId {
    const store: *MetaStore = @ptrCast(@alignCast(ctx.?));
    return store.mint(theorem, sort_name, std.math.maxInt(u55), kind);
}

/// A rule binder's explicit-rendering flag as `setExplicitFlag` set it, with
/// what `restore` puts back.
pub const ExplicitFlag = struct {
    idx: usize,
    /// The previous value; null when the flag array did not exist before, so
    /// restoring just clears the bit.
    prev: ?bool,

    pub fn restore(self: ExplicitFlag, candidate: *ApplyCandidate) void {
        const flags = candidate.explicit orelse return;
        if (self.idx >= flags.len) return;
        flags[self.idx] = self.prev orelse false;
    }
};

/// Set the candidate's explicit flag for rule binder `idx`.
fn setExplicitFlag(candidate: *ApplyCandidate, idx: usize) !ExplicitFlag {
    const flags = blk: {
        if (candidate.explicit) |flags| break :blk flags;
        const flags = try candidate.allocator.alloc(bool, candidate.bindings.len);
        @memset(flags, false);
        candidate.explicit = flags;
        break :blk flags;
    };
    if (idx >= flags.len) return .{ .idx = idx, .prev = null };
    defer flags[idx] = true;
    return .{ .idx = idx, .prev = flags[idx] };
}

/// Mark binder `idx`, just bound to `value` by an ACUI split or principal
/// choice, for explicit rendering. The checker re-derives such a binder by
/// its own positional reading of the bag, which need not agree with the
/// search's choice, least of all inside a nested inline application.
/// A value holding a goal meta is not a choice the checker can take, so it
/// stays unmarked (null).
pub fn handSplitChoice(candidate: *ApplyCandidate, idx: usize, value: ?ExprId) !?ExplicitFlag {
    const expr = value orelse return null;
    if (candidate.theorem.containsPlaceholder(expr)) return null;
    return try setExplicitFlag(candidate, idx);
}
