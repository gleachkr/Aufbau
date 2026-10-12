//! The state one candidate's backtracking search shares between the
//! backtracker (`backtrack.zig`) and the open-slot engine (`open_slot.zig`),
//! and the helpers both call: the concrete emit path, the open-generation
//! policy, explicit-rendering flags for split choices, and the dependency
//! condition as matched. Neither of those files is imported here.
const std = @import("std");
const types = @import("../types.zig");
const refs_mod = @import("../refs.zig");
const ref_index_mod = @import("../ref_index.zig");
const context_prune = @import("../context_prune.zig");
const semantic = @import("./semantic.zig");
const acui = @import("./acui.zig");
const plausible = @import("./plausible.zig");
const plan = @import("./plan.zig");
const validate_mod = @import("./validate.zig");
const Redex = @import("./redex.zig");
const ExprId = @import("../../../expr.zig").ExprId;
const TheoremContext = @import("../../../expr.zig").TheoremContext;
const RuleDecl = @import("../../../env.zig").RuleDecl;
const RuleApplication = @import("../../../proof_script.zig").RuleApplication;
const CompilerContext = @import("../../context.zig").CompilerContext;
const Goal = types.Goal;
const Context = types.Context;
const ApplyCandidate = types.ApplyCandidate;
const ExactCandidate = types.ExactCandidate;
const SearchCounters = types.SearchCounters;
const SearchRuntime = types.SearchRuntime;
const CandidateFilter = types.CandidateFilter;
const NameExprMap = types.NameExprMap;
const GenerationHook = types.GenerationHook;
const DerivedPool = types.DerivedPool;
const Fuel = types.Fuel;
const HypPlan = plan.HypPlan;
const normalizeAcuiUnits = acui.normalizeAcuiUnits;
const finalConclusionPlausible = plausible.finalConclusionPlausible;
const validateSelectedRefs = validate_mod.validateSelectedRefs;

/// The hypothesis slot a generator fills: its search depth, its index into
/// `candidate.unresolved_hyps`, and the rule hypothesis it instantiates.
pub const Slot = struct {
    depth: usize,
    position: usize,
    hyp_index: usize,
};

/// The bindings `SlotCtx.conclusionPlausible` last accepted.
pub const AcceptedConclusion = struct {
    bindings: []?ExprId,
    valid: bool = false,
};

/// One candidate's backtracking search: what `backtrackRefs` and the slot
/// generators share for the lifetime of one `enumerateCandidateRefs` call.
/// The slices are the search's mutable state (the rule bindings, a bindings
/// snapshot per depth, and the pool ref or generated sub-application chosen
/// for each slot); everything else is fixed for the candidate.
pub const SlotCtx = struct {
    compiler: *CompilerContext,
    context: *const Context,
    ref_index: *const ref_index_mod.Index,
    pool: []const refs_mod.RefPoolEntry,
    candidate: *ApplyCandidate,
    rule: *const RuleDecl,
    goal: Goal,
    theorem: *const TheoremContext,
    theorem_vars: *const NameExprMap,
    plans: []const HypPlan,
    bindings: []?ExprId,
    snapshots: []?ExprId,
    selected: []?usize,
    /// Parallel to `selected`: a generated inline sub-application chosen for
    /// a slot instead of a pool ref. Always `null` without a `generator`, so
    /// the pool-only `exact?` path is unaffected.
    generated: []?RuleApplication,
    generator: ?*const GenerationHook,
    derived: ?*DerivedPool,
    runtime: SearchRuntime,
    keep: ?CandidateFilter,
    counters: ?*SearchCounters,
    fuel: ?*Fuel,
    candidates: *std.ArrayListUnmanaged(ExactCandidate),
    prune_setup: PruneSetup,
    /// The bindings `finalConclusionPlausible` last accepted. It reads
    /// nothing else that changes during this search, so the same bindings
    /// pass again without rerunning it.
    accepted_conclusion: *AcceptedConclusion,
    /// Searches the slots from `depth` on: the backtracker's
    /// `backtrackRefs`, passed in so this file does not import it.
    descend: *const fn (ctx: *const SlotCtx, depth: usize) anyerror!void,

    /// The bindings snapshot of search depth `depth`.
    pub fn snapshotAt(self: *const SlotCtx, depth: usize) []?ExprId {
        return self.snapshots[depth * self.bindings.len ..][0..self.bindings.len];
    }

    /// `finalConclusionPlausible` for the current bindings.
    pub fn conclusionPlausible(self: *const SlotCtx) bool {
        const accepted = self.accepted_conclusion;
        if (accepted.valid and std.mem.eql(?ExprId, accepted.bindings, self.bindings)) return true;
        if (!finalConclusionPlausible(
            self.context,
            self.candidate,
            self.goal,
            self.bindings,
            self.runtime,
            self.counters,
        )) return false;
        @memcpy(accepted.bindings, self.bindings);
        accepted.valid = true;
        return true;
    }

    /// Validate the fills chosen for every slot as one complete application.
    pub fn validate(self: *const SlotCtx) !void {
        if (!self.conclusionPlausible()) {
            if (self.counters) |actual| actual.final_conclusion_prunes += 1;
            return;
        }
        try validateSelectedRefs(
            self.compiler,
            self.context.allocator,
            self.context,
            self.pool,
            self.candidate,
            self.goal,
            self.theorem,
            self.theorem_vars,
            self.bindings,
            self.selected,
            self.generated,
            self.prune_setup.concl_has_rewrite_head,
            self.runtime,
            self.keep,
            self.counters,
            self.fuel,
            self.candidates,
        );
    }

    /// Descend to the next slot with slot `position` filled by `application`.
    pub fn descendGenerated(
        self: *const SlotCtx,
        depth: usize,
        position: usize,
        application: RuleApplication,
    ) anyerror!void {
        self.generated[position] = application;
        defer self.generated[position] = null;
        try self.descend(self, depth + 1);
    }
};

/// Loop-invariant candidate-ref pruning setup for one rule. Every field is a
/// pure function of `(context, rule_id)`, so each candidate computes it once
/// (`SlotCtx.prune_setup`) rather than at every DFS node (a single hoisted
/// `views.get` plus the static `analyzeView` flatten).
pub const PruneSetup = struct {
    /// The view when it carries an `@abstract` decl (else null): gates the
    /// Leibniz one-hole-context prefilter (`abstract_prune.zig`).
    abstract_view: ?types.ViewDecl,
    /// The analysed ACUI context-combination info (`context_prune.zig`), or null
    /// when the rule has no context position to reason about.
    context_info: ?context_prune.Info,
    /// True when `context_info` was built in raw rule binder space, so the
    /// current rule bindings can be used for shape-aware discharge pruning.
    context_uses_rule_bindings: bool,
    /// The rule's conclusion has a `@rewrite` head, so `validateSelectedRefs`
    /// runs the redex check.
    concl_has_rewrite_head: bool,
};

/// Open-generation policy for one candidate slot, computed once at each
/// open-path seam instead of re-deriving `isAutoBackwardRule` at every layer.
///
/// `.witness` — exactly `@auto backward` enrollment: the rule may defer a
/// premise-only binder as an existential meta, with the full witness
/// machinery (ancestor-meta carrying, force-first member pass, coupled leaf
/// solving, and — only under `allow_invent_witness` — `@vars` pool
/// invention).
///
/// `.constrained` — a structured open target is built, but the child proof
/// must determine every meta by read-back; no meta propagates into nested
/// open slots (except under a holey root, `hook.open_root`) and nothing is
/// invented. Un-enrolled rules get it in phase 5
/// (constrained backward modus ponens, `hook.allow_constrained_mp`), and
/// `@abstract` motive inference rides that branch too. A premise that only
/// opens a hidden bound variable gets it in every phase
/// (`tryFreshBoundGenerate`).
///
/// `.none` — no open generation for this candidate.
pub const OpenMode = enum { none, constrained, witness };

pub fn openMode(
    context: *const Context,
    rule_id: u32,
    allow_constrained_mp: bool,
) OpenMode {
    if (context.registry.isAutoBackwardRule(rule_id)) return .witness;
    if (allow_constrained_mp) return .constrained;
    return .none;
}

/// Emit a single generated slot: canonicalize ACUI units out of the (now
/// concrete) sub-target, ask the hook to prove it, and recurse with the slot
/// filled. Canonicalizing the unit (`emp`) lets the sub-target match unit-free
/// pool refs — an `imp_intro` over an `emp ⊢ …` goal binds the context binder to
/// `emp`, leaving a redundant unit the strict `matchTemplate` would otherwise
/// reject (the validator absorbs it anyway).
pub fn emitGeneratedSlot(
    ctx: *const SlotCtx,
    hook: *const GenerationHook,
    slot: Slot,
    raw_target: ExprId,
) anyerror!void {
    const candidate = ctx.candidate;
    const reduced = try Redex.reduceRedexOnly(ctx.context, &candidate.theorem, raw_target);
    const target = try normalizeAcuiUnits(ctx.context, &candidate.theorem, reduced);
    // The application matched the goal and is launching a subgoal solve —
    // the signal that arms the `@auto eager` set-commit cut (consulted only
    // for eager candidates). An eager application is also exempt from the
    // depth budget: `eager_step` tells the driver to solve the child at the
    // parent's remaining depth.
    candidate.reached_child_solve = true;
    const eager_step = ctx.context.registry.eagerPriority(candidate.rule_id) != null;
    const proof = (try hook.solve(target, &candidate.theorem, eager_step)) orelse {
        return;
    };
    if (proof.conclusion != target) {
        return;
    }
    try ctx.descendGenerated(slot.depth, slot.position, proof.application);
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
pub fn setExplicitFlag(candidate: *ApplyCandidate, idx: usize) !ExplicitFlag {
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

/// How a matched non-bound binder's value mentions the value of a bound arg
/// its `ArgInfo.deps` omits. Occurrences under a term with alpha rules don't
/// count (`@freshen` renames only through those). A meta leaf counts as no hit,
/// even a seed meta carrying a dep bit: an open meta may still be assigned
/// something that avoids the bound variable, so a partially open binding is
/// judged on its concrete part.
pub const DepHit = enum {
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

/// The dependency bits non-bound binder `idx` of `rule` must avoid, as the
/// checker's dependency condition reads them: those of the values of the bound
/// binders `idx`'s `ArgInfo.deps` omits.
pub fn bannedDeps(
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
