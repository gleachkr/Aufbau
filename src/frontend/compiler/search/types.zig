const std = @import("std");
const ArenaAllocator = @import("../../arena_allocator.zig").ArenaAllocator;
const expr_mod = @import("../../expr.zig");
const ExprId = @import("../../expr.zig").ExprId;
const PlaceholderId = @import("../../expr.zig").PlaceholderId;
const TheoremContext = @import("../../expr.zig").TheoremContext;
const GlobalEnv = @import("../../env.zig").GlobalEnv;
const ParseRecovery = @import("../../parse_recovery.zig");
const AssertionStmt = ParseRecovery.AssertionStmt;
const MM0Parser = ParseRecovery.MM0Parser;
const Expr = @import("../../../trusted/expressions.zig").Expr;
const ProofScript = @import("../../proof_script.zig");
const RuleApplication = ProofScript.RuleApplication;
pub const Span = ProofScript.Span;
const RewriteRegistry = @import("../../rewrite_registry.zig").RewriteRegistry;
const MetaStore = @import("./meta_store.zig").MetaStore;
const RuleCatalog = @import("../rule_catalog.zig");
const CompilerViews = @import("../../views.zig");
const FreshSelect = @import("../fresh_select.zig");
const CompilerDiag = @import("../../diag.zig");
const CheckedIr = @import("../../checked_ir.zig");
const CheckedLine = CheckedIr.CheckedLine;
const Inference = @import("../inference.zig");
const Check = @import("../check.zig");
const CompilerVars = @import("../vars.zig");

pub const NameExprMap = Check.NameExprMap;
pub const LabelIndexMap = Check.LabelIndexMap;
pub const FreshDecl = FreshSelect.FreshDecl;
pub const FreshenDecl = FreshSelect.FreshenDecl;
pub const ViewDecl = CompilerViews.ViewDecl;
pub const SortVarRegistry = CompilerVars.SortVarRegistry;

pub const Goal = union(enum) {
    concrete: ExprId,
    holey: *const Expr,
    implicit_whole_conclusion: ?ExprId,

    /// The goal as a line assertion checked in `theorem`, a holey goal
    /// interned there with its line holes.
    pub fn lineAssertion(
        self: Goal,
        theorem: *TheoremContext,
        env: *const GlobalEnv,
    ) !Check.LineAssertion {
        return switch (self) {
            .concrete => |expr| .{ .concrete = expr },
            .holey => |expr| .{ .holey = try Check.HoleyLine.init(theorem, env, expr) },
            .implicit_whole_conclusion => .implicit_whole_conclusion,
        };
    }

    pub fn expectedHint(self: Goal) ?ExprId {
        return switch (self) {
            .implicit_whole_conclusion => |hint| hint,
            else => null,
        };
    }

    /// The concrete goal expression, or the whole-conclusion hint when the goal
    /// is implicit. Null for a holey goal or a hintless implicit goal. Callers
    /// that must bail on those cases spell it `goal.concreteOrHint() orelse ...`.
    pub fn concreteOrHint(self: Goal) ?ExprId {
        return switch (self) {
            .concrete => |expr| expr,
            .implicit_whole_conclusion => |hint| hint,
            .holey => null,
        };
    }
};

pub const Context = struct {
    allocator: std.mem.Allocator,
    parser: *MM0Parser,
    env: *const GlobalEnv,
    registry: *RewriteRegistry,
    rule_catalog: *RuleCatalog.Catalog,
    fresh_bindings: *const std.AutoHashMap(u32, []const FreshDecl),
    freshen_bindings: *const std.AutoHashMap(u32, []const FreshenDecl),
    views: *const std.AutoHashMap(u32, ViewDecl),
    sort_vars: *const SortVarRegistry,
    assertion: AssertionStmt,
    labels: *const LabelIndexMap,
    checked: *std.ArrayListUnmanaged(CheckedLine),
    diag_scratch: *CompilerDiag.Scratch,
    rule_unify_cache: *Inference.RuleUnifyCache,
    available_rule_count: usize,

    /// Build the trusted checker's `RuleApplyContext` from this search context.
    /// `allocator` and `checked` vary per caller (probes run against a scratch
    /// checked-line buffer); every other field forwards verbatim. Keeping the
    /// mapping here means a new `RuleApplyContext` field is a one-line change,
    /// not a silent three-way drift across the search call sites.
    pub fn ruleApplyContext(
        self: *const Context,
        allocator: std.mem.Allocator,
        checked: *std.ArrayListUnmanaged(CheckedLine),
    ) Check.RuleApplyContext {
        return .{
            .allocator = allocator,
            .parser = self.parser,
            .env = self.env,
            .registry = self.registry,
            .rule_catalog = self.rule_catalog,
            .fresh_bindings = self.fresh_bindings,
            .freshen_bindings = self.freshen_bindings,
            .views = self.views,
            .sort_vars = self.sort_vars,
            .assertion = self.assertion,
            .labels = self.labels,
            .checked = checked,
            .diag_scratch = self.diag_scratch,
            .rule_unify_cache = self.rule_unify_cache,
        };
    }
};

pub const AttemptOptions = struct {
    line_label: []const u8 = "<search>",
    assertion_span: Span = .{ .start = 0, .end = 0 },
    diagnostic_span: ?Span = null,
    counters: ?*SearchCounters = null,
};

pub const UnresolvedHypothesis = Check.UnresolvedHypothesis;

pub const ApplyCandidate = struct {
    allocator: std.mem.Allocator,
    rule_id: u32,
    rule_name: []const u8,
    declaration_order: usize,
    theorem: TheoremContext,
    /// The theorem's variables with those the probe named (a `@fresh`
    /// binder's pick from its `@vars` pool).
    theorem_vars: NameExprMap,
    bindings: []const ?ExprId,
    conclusion: ExprId,
    unresolved_hyps: []const UnresolvedHypothesis,

    pub fn deinit(self: *ApplyCandidate) void {
        self.allocator.free(self.bindings);
        self.allocator.free(self.unresolved_hyps);
        self.theorem_vars.deinit();
        self.theorem.deinit();
        self.* = undefined;
    }
};

pub const ApplyResults = struct {
    allocator: std.mem.Allocator,
    candidates: []ApplyCandidate,

    pub fn deinit(self: *ApplyResults) void {
        for (self.candidates) |*candidate| {
            candidate.deinit();
        }
        self.allocator.free(self.candidates);
        self.* = undefined;
    }
};

/// Name storage inside the `SearchCounters` block, which the bench copies BY
/// VALUE out of the search (`runFrontierSearch` returns it inside
/// `FrontierRun`) and prints only after `suggestionsAtSourceOffset` has freed
/// its per-call `work_arena`, which owns the names. Borrowing the arena slice
/// was a use-after-free that crashed `--counters` mode (task #63), so the name
/// bytes are copied inline. Longer names truncate, which only affects display.
pub const InlineName = struct {
    pub const cap: usize = 64;

    buf: [cap]u8 = undefined,
    len: usize = 0,

    pub fn set(self: *InlineName, name: []const u8) void {
        const n = @min(name.len, cap);
        @memcpy(self.buf[0..n], name[0..n]);
        self.len = n;
    }

    pub fn slice(self: *const InlineName) []const u8 {
        return self.buf[0..self.len];
    }
};

/// A sort whose `@vars` pool ran out during a search
/// (`SearchCounters.vars_pool_exhausted`).
pub const VarsPoolExhaustion = struct {
    sort_name: InlineName = .{},
    pool_size: usize = 0,

    pub fn of(sort_name: []const u8, pool_size: usize) VarsPoolExhaustion {
        var out: VarsPoolExhaustion = .{ .pool_size = pool_size };
        out.sort_name.set(sort_name);
        return out;
    }
};

/// How a search core run that found no proof ended
/// (`SearchCounters.core_end`).
pub const CoreEnd = enum {
    /// It searched every depth up to `max_depth`, so the proof may be
    /// deeper.
    depth_limit,
    /// It ran out of alternatives at every depth, with and without the
    /// limits on a passed cut: no limit hid a proof from it.
    exhausted,
    budget,
    /// The call-stack guard stopped one branch, and with it the run.
    stack,
};

/// Search statistics: a value-only observation sink. Every field is a plain
/// count, flag, or duration; nothing the search DOES depends on this block,
/// and it holds no pointers, so
/// a caller may keep one block across calls or pass none at all. A test pins
/// the no-pointer property.
pub const SearchCounters = struct {
    /// When false, the per-candidate `tryCandidate` timers are skipped. It
    /// only gates observability. The bench sets it, and so do the editor and
    /// `abc search`.
    collect: bool = false,
    /// Times index builds, shape emission and reference/rule lookups into
    /// the `*_build_ns`, `shape_emission_ns` and `*_lookup_ns` fields. Those
    /// clocks run on every lookup, so they stay off outside the bench's
    /// `--counters` and scenario reports (#446).
    timing: bool = false,
    cold_setup_ns: u64 = 0,
    warm_search_ns: u64 = 0,
    /// The part of `warm_search_ns` spent trimming a suggestion's bindings
    /// (`source/trim.zig:trimBindings`): checker runs, never ticks.
    trim_ns: u64 = 0,
    /// Suggestions that came back with every binding the search chose,
    /// because the `BindingOracle` check failed (`source/trim.zig:trimBindings`).
    /// The bench, and search tests that go through `tests/helpers.zig`,
    /// fail on any.
    untrimmed: u32 = 0,
    /// Work ticks consumed by the whole `auto?` call — the raw counts behind
    /// the per-call `GlobalBudget`'s weighted cost. Zero when the call never
    /// searched. See `expr.zig` `work_ticks` /
    /// `work_ticks_sym`. `gen_core_ticks` is already weighted, as
    /// `work_ticks_core` is.
    gen_work_ticks: u64 = 0,
    gen_sym_ticks: u64 = 0,
    gen_core_ticks: u64 = 0,
    gen_walk_ticks: u64 = 0,
    /// Set when the per-call `GlobalBudget` ran out.
    work_budget_exhausted: bool = false,
    /// The search core ran on an `auto?` goal (it did not abstain), and the
    /// depth it found the proof at, or the last depth it started on a miss.
    core_ran: bool = false,
    gen_last_depth: usize = 0,
    /// The search core (`core/`): goals it
    /// expanded, and finished proofs the checker rejected at close-out.
    core_nodes: usize = 0,
    core_rejects: usize = 0,
    /// How the search core's run ended without a proof; null when it did
    /// not run, abstained, or found one. Read by `miss.MissReport`.
    core_end: ?CoreEnd = null,
    rule_index_build_ns: u64 = 0,
    ref_index_build_ns: u64 = 0,
    shape_emission_ns: u64 = 0,
    /// Number of query-side `ShapeSet` builds (one per `lookupTemplate*`/goal
    /// lookup). Paired with `shape_emission_ns` to gauge per-lookup shape cost
    /// and redundancy across a search.
    shape_emissions: usize = 0,
    /// Subset of `shape_emissions` from the rule-index (goal-shape) path; the
    /// remainder are ref-index (template-shape) lookups.
    rule_shape_emissions: usize = 0,
    /// Content-keyed query-shape cache (`ref_index.ShapeCache`): template
    /// lookups served from the memo vs. built fresh. Hits + misses ≤
    /// `shape_emissions` (uncacheable and non-template lookups bypass it).
    shape_cache_hits: usize = 0,
    shape_cache_misses: usize = 0,
    rule_lookup_ns: u64 = 0,
    ref_lookup_ns: u64 = 0,
    tc_clone_ns: u64 = 0,
    tc_apply_ns: u64 = 0,
    candidate_rules_before_conclusion_validation: usize = 0,
    conclusion_probes: usize = 0,
    ref_pool_size: usize = 0,
    full_try_candidate_calls: usize = 0,
    /// The last `@vars` pool fill that found no variable it could use: every
    /// pool name was already taken by the instance or rejected for the meta.
    /// No limit reaches a branch that dies there, so the miss report names
    /// the pool (`source/report.zig`).
    vars_pool_exhausted: ?VarsPoolExhaustion = null,
    accepted_candidates: usize = 0,
    rejected_candidates_after_validation: usize = 0,
    universal_metas_created: usize = 0,
    meta_assignments: usize = 0,
    meta_rollbacks: usize = 0,
    derived_ref_count: usize = 0,
    forward_rule_attempts: usize = 0,
    forward_match_tuples: usize = 0,
    forward_layers_run: usize = 0,
    /// Set when forward saturation stopped at a budget rather than reaching a
    /// fixpoint (exhaustion is reported separately from a
    /// clean no-result).
    forward_saturation_exhausted: bool = false,

    pub fn timingOn(counters: ?*const SearchCounters) bool {
        const actual = counters orelse return false;
        return actual.timing;
    }
};

pub const ApplyOptions = struct {
    max_results: ?usize = null,
    counters: ?*SearchCounters = null,
    /// Per-call work budget: each rule probe spends a candidate from it,
    /// and when it runs out the remaining rules are not probed.
    budget: ?*GlobalBudget = null,
    /// The refs written on an open goal (`? [l1, ?, l5]`), when there are
    /// any: only rules with that many premises are probed, and each fact
    /// cited constrains the rule's bindings as the checker's ref would.
    premises: ?[]const ProofScript.Ref = null,
};

/// Cost-weighted budget for one whole search call (`exact?`, `auto?` or an
/// open goal's rule probe): forward saturation and the search core. The cost
/// unit is the interner work tick (`expr.zig` `work_ticks`): one per intern attempt,
/// everywhere on the thread. Unlike a `tryCandidate` count, tick
/// consumption tracks how *expensive* each candidate's validation cascade
/// actually was (cheap syntactic rejects vs. the full def/ACUI/normalization
/// fallback differ ~100x), so a tick ceiling bounds wall-clock latency far
/// more tightly than a candidate-count ceiling can. Deterministic: tick counts
/// depend only on the operations performed, never on time or machine.
///
/// Checked at candidate granularity (each `spendCandidate`, and each goal the
/// core expands), so exhaustion ends the search with
/// `error.SearchBudgetExhausted`. The one
/// sub-candidate poll is the inference solver's (`expr.zig` `WorkBudget`,
/// installed on the `CompilerContext` for the call): its branch fan-out is
/// the only per-candidate work with no bound of its own, so a solve that
/// explodes aborts at the budget and the candidate counts as a reject.
/// Relative unit costs of the tick populations (see `expr.zig`) plus a fixed
/// per-candidate charge (each `spendCandidate` — a `tryCandidate` — carries fixed
/// overhead: theorem/vars clones, session setup/hash — that no per-node tick
/// sees). Calibrated on the full depth corpus by regressing per-call wall
/// time on the counts; units are ≈nanoseconds of calibrated wall, so a
/// budget limit reads as "estimated ns of search work" (4e9 ≈ 4s). The counts
/// themselves are machine-independent, so capped behavior is deterministic
/// even though the ns calibration is machine-specific.
pub const intern_tick_weight: u64 = 150;
pub const sym_tick_weight: u64 = 48;
pub const walk_tick_weight: u64 = 28;
pub const candidate_weight: u64 = 25_000;
/// The search core's work per visit, from the same regression: a comparison
/// that may stop at the first differing head, a matcher step, a walk over
/// wvars, a walk that builds a memo key. Each site adds its weight to
/// `expr.work_ticks_core` directly, a threadlocal per kind being more than one
/// sum needs.
pub const core_compare_weight: u64 = 14;
pub const core_match_weight: u64 = 31;
pub const core_wvar_weight: u64 = 9;
pub const core_key_weight: u64 = 5;
/// The bag work, fit on searches over long sums and products (Cardano),
/// where it is most of the cost: resolving an expression under the current
/// bindings, which mostly finds it ground, and reading a member of a bag.
pub const core_resolve_weight: u64 = 7;
pub const core_member_weight: u64 = 12;

/// The budget's cost unit: weighted ticks.
pub fn weightedTicks(
    intern_ticks: u64,
    sym_ticks: u64,
    walk_ticks: u64,
    candidates: u64,
    core_ticks: u64,
) u64 {
    return intern_ticks *% intern_tick_weight +%
        sym_ticks *% sym_tick_weight +%
        walk_ticks *% walk_tick_weight +%
        candidates *% candidate_weight +%
        core_ticks;
}

pub const GlobalBudget = struct {
    /// Weighted-tick ceiling for the whole call.
    limit: u64,
    /// `expr.work_ticks*` snapshots at driver entry.
    start_intern: u64,
    start_sym: u64,
    start_walk: u64,
    start_core: u64,
    /// Candidates spent so far (counted here, not threadlocally).
    candidates: u64 = 0,
    /// Set once exhausted; observability for the driver/bench.
    exhausted: bool = false,
    /// `expr.work_ticks*` when `pause` was called; null while charging.
    paused_at: ?[4]u64 = null,

    pub fn init(limit: u64) GlobalBudget {
        return .{
            .limit = limit,
            .start_intern = expr_mod.work_ticks,
            .start_sym = expr_mod.work_ticks_sym,
            .start_walk = expr_mod.work_ticks_walk,
            .start_core = expr_mod.work_ticks_core,
        };
    }

    /// A budget that charges nothing until `unpause`.
    pub fn initPaused(limit: u64) GlobalBudget {
        var budget = init(limit);
        budget.pause();
        return budget;
    }

    /// Stop charging the work done from now until `unpause`.
    pub fn pause(self: *GlobalBudget) void {
        std.debug.assert(self.paused_at == null);
        self.paused_at = ticksNow();
    }

    pub fn unpause(self: *GlobalBudget) void {
        const at = self.paused_at.?;
        const now = ticksNow();
        self.start_intern +%= now[0] -% at[0];
        self.start_sym +%= now[1] -% at[1];
        self.start_walk +%= now[2] -% at[2];
        self.start_core +%= now[3] -% at[3];
        self.paused_at = null;
    }

    fn ticksNow() [4]u64 {
        return .{ expr_mod.work_ticks, expr_mod.work_ticks_sym, expr_mod.work_ticks_walk, expr_mod.work_ticks_core };
    }

    pub fn spent(self: *const GlobalBudget) u64 {
        const now = self.paused_at orelse ticksNow();
        return weightedTicks(
            now[0] -% self.start_intern,
            now[1] -% self.start_sym,
            now[2] -% self.start_walk,
            self.candidates,
            now[3] -% self.start_core,
        );
    }

    pub fn check(self: *GlobalBudget) error{SearchBudgetExhausted}!void {
        if (self.spent() > self.limit) {
            self.exhausted = true;
            return error.SearchBudgetExhausted;
        }
    }

    /// The ceiling as the interface sub-candidate work polls (`expr.zig`
    /// `WorkBudget`).
    pub fn workBudget(self: *GlobalBudget) expr_mod.WorkBudget {
        return .{ .ctx = @ptrCast(self), .check_fn = checkOpaque };
    }

    fn checkOpaque(ctx: *anyopaque) error{SearchBudgetExhausted}!void {
        const self: *GlobalBudget = @ptrCast(@alignCast(ctx));
        return self.check();
    }

    pub fn spendCandidate(self: *GlobalBudget) error{SearchBudgetExhausted}!void {
        self.candidates += 1;
        try self.check();
    }
};

/// A solved (or universal-meta-deferred) rule-binder value carried by a
/// derived forward ref's proof recipe. Values live in the search
/// driver's work theorem; meta leaves are dereferenced through the pool's
/// store at materialize time.
pub const DerivedRefBinding = struct {
    arg_index: usize,
    value: ExprId,
};

/// A universal meta of a *nested* derived source that a forward join grounded
/// to a concrete witness *within this recipe* (e.g. `mp` joining the family
/// `P ?t → Q ?t` with `P c` pins the family's `?t := c` to produce `Q c`). The
/// family fact stays general; this pin is re-applied transiently when *this*
/// fact is materialized, so the nested source re-instantiates at the witness
/// this derivation used. Empty for every fact whose sources carry no grounded
/// meta (the common case).
pub const MetaAssignment = struct {
    meta: PlaceholderId,
    value: ExprId,
};

/// One premise source in a derived ref's proof recipe. A derived
/// source points at an earlier entry of the same `DerivedPool` (strictly
/// lower index, so recipes are acyclic); its recipe is materialized in place
/// as a nested inline application at use time.
pub const DerivedSource = union(enum) {
    pool: ProofScript.Ref,
    derived: usize,
};

/// One bounded forward-saturation fact: a rule applied to pool refs and/or
/// earlier derived refs, with any instantiation witness left as a universal
/// metavariable. The derived ref is a search *hint*,
/// never trusted on its own — its recipe is spliced in as a nested
/// `RuleApplication` and re-checked by `tryCandidate` at the point of use.
pub const DerivedRef = struct {
    rule_id: u32,
    rule_name: []const u8,
    declaration_order: usize,
    /// One recipe source per rule hypothesis, in hypothesis order.
    sources: []const DerivedSource,
    /// The `@recover`-derived applied surface: the concrete matrix from the
    /// forward premise match with the recover hole structurally replaced by
    /// the universal meta — NOT the rule's raw conclusion, and NOT produced
    /// by normalization. Matching a goal against this IS the `@recover`
    /// solve: where the shape has the meta, the goal shows the witness.
    shape: ExprId,
    /// Rule-binder values for rendering explicit bindings, ascending by
    /// `arg_index`.
    bindings: []const DerivedRefBinding,
    /// Every unsolved universal meta the recipe needs solved at use time:
    /// this layer's binding values plus every derived source's, recursively.
    /// Derivation guarantees these all occur in `shape`, so the use-time
    /// shape match solves the whole (possibly multi-layer) recipe — shared
    /// holes across layers are literally the same store meta.
    required_metas: []const PlaceholderId,
    /// Nested-source universals grounded to concrete witnesses by the forward
    /// join that produced this fact (see `MetaAssignment`). Layered over the
    /// pool store in a scoped overlay while this recipe is resolved at
    /// materialize time; a nested layer's pin of the same family meta shadows
    /// this one within that layer's subtree (`forward.resolveRecipeValues`).
    pinned_metas: []const MetaAssignment = &.{},
    has_universal_meta: bool,
    /// 1 for a fact derived from pool refs only; 1 + max(source depths)
    /// otherwise (the saturation layer that produced it).
    source_depth: usize = 1,
};

/// Bounds for forward saturation. Saturation stops at the
/// first bound it hits and reports that distinctly from a clean fixpoint
/// (`DerivedPool.budget_exhausted`).
pub const ForwardOptions = struct {
    max_forward_layers: usize = 3,
    max_forward_facts: usize = 64,
    max_forward_rule_attempts: usize = 1024,
    max_forward_match_tuples: usize = 2048,
};

/// Branch-shared pool of derived refs plus the metavariable store their
/// universal holes live in. Use-time discipline: a use transiently assigns
/// the holes, materializes the concrete recipe, then rolls the assignments back, so the same derived ref can be
/// selected twice in one proof at two different witnesses.
pub const DerivedPool = struct {
    arena: ArenaAllocator,
    store: MetaStore,
    refs: []const DerivedRef = &.{},
    /// Saturation layers actually run (a layer that derives nothing ends the
    /// loop early — a clean fixpoint).
    layers_run: usize = 0,
    /// True when saturation stopped at a budget (layers while the frontier
    /// was still productive, facts, rule attempts, or match tuples) rather
    /// than reaching a fixpoint. Distinct from a clean no-result: an absent
    /// derived fact is inconclusive when this is set.
    budget_exhausted: bool = false,

    pub fn deinit(self: *DerivedPool) void {
        self.store.deinit();
        self.arena.deinit();
        self.* = undefined;
    }
};

pub const SourceSuggestion = struct {
    title: []const u8,
    replacement: []const u8,
    replace_span: Span,
    /// Where in `replacement` the editor puts the cursor after the edit: on
    /// the first open goal `?` it adds, so the next action can follow.
    cursor: ?usize = null,
};

/// How a source-offset search concluded, for surfacing to the user (LSP
/// diagnostics). Purely informational — derived after the fact from the
/// results and the counters' exhaustion flags, never consulted by the search.
pub const SearchStatus = enum {
    /// At least one suggestion was produced.
    found,
    /// The search ran its candidate set to completion without a result: no
    /// proof exists within the configured search space.
    miss,
    /// A budget (the per-call global budget, the stack guard, or a forward-
    /// saturation bound) truncated the search before it completed — an empty
    /// result is inconclusive, a proof may still exist.
    budget_exhausted,
};

pub const SourceSuggestions = struct {
    allocator: std.mem.Allocator,
    items: []const SourceSuggestion,
    /// The source span of the placeholder these suggestions resolve to — the
    /// catchment region in which any cursor offset maps to this same search
    /// target. `null` when no search placeholder was found at the offset.
    /// Callers (the LSP cache) use it to serve every offset within one
    /// placeholder from a single computed result. Purely informational; does
    /// not affect the suggestions themselves.
    target_span: ?Span = null,
    /// How the search concluded (see `SearchStatus`). Meaningful only when
    /// `target_span` is set and `target_kind` is `.search` (a placeholder
    /// was actually searched); the other returns leave the default.
    status: SearchStatus = .miss,
    /// Set instead of searching when an earlier line of the placeholder's
    /// block does not check: that line's label span. `target_span` is null.
    blocked_by: ?Span = null,
    /// Human-readable elaboration of a `.miss`/`.budget_exhausted` status —
    /// which bound truncated the search, how far it got, what to tune. Only
    /// built when `SourceSuggestionOptions.status_detail` is set (the LSP
    /// path); null otherwise. Owned by `allocator` when present.
    status_detail: ?[]const u8 = null,
    /// After an `auto?` miss that larger limits might fix: the edit that
    /// rewrites the placeholder's parameters to the raised values (see
    /// `miss.retryFor`). Built alongside `status_detail`; null otherwise.
    /// Owned by `allocator` when present.
    retry: ?SourceSuggestion = null,
    /// What stood at the offset: a search placeholder, whose outcome backs
    /// its status diagnostic, or an open goal, which runs no search.
    target_kind: TargetKind = .search,

    pub const TargetKind = enum { search, open_goal };

    pub fn deinit(self: *SourceSuggestions) void {
        for (self.items) |item| {
            self.allocator.free(item.title);
            self.allocator.free(item.replacement);
        }
        self.allocator.free(self.items);
        if (self.status_detail) |detail| self.allocator.free(detail);
        if (self.retry) |retry| {
            self.allocator.free(retry.title);
            self.allocator.free(retry.replacement);
        }
        self.* = undefined;
    }
};

/// Controls bounded recursive generation (`auto?`). Generation only
/// runs when the `auto?` keyword is under the cursor AND `enabled` is set by the
/// caller (the permit). The bench and `exact?` paths never enable it,
/// so they never pay generation cost.
pub const GenerateOptions = struct {
    enabled: bool = false,
    /// Maximum search depth, the `depth:` parameter. Null runs the search
    /// core until the budget runs out or a pass cuts nothing (`core/root.zig`).
    /// A budget of `null` needs a finite limit, since a goal with no proof
    /// would otherwise deepen for ever (`coreDepth`).
    max_depth: ?usize = null,
    /// Forward-saturation bounds. Saturation only runs at all when
    /// the theory declares `@auto forward` rules.
    forward: ForwardOptions = .{},
    /// Content-keyed query-shape cache (Lever M-content): memoize the
    /// query-side template `ShapeSet` per session, keyed by a structural
    /// serialization of everything the shape builder reads (sound by
    /// construction — see `ref_index.ShapeCache`). Default on; the bench A/Bs
    /// it via `--no-shape-cache`.
    shape_cache: bool = true,
    /// Cost-weighted per-call latency cap: total weighted work ticks one
    /// `auto?` call may consume, forward saturation and the core (see
    /// `GlobalBudget`; units ≈ ns of native wall on the calibration machine,
    /// so 2.3e9 ≈ 2.3 s, and the corpus's slowest search takes about 3 s).
    /// Exhaustion ends the search, and the tick counts are deterministic, so
    /// capped results are machine-independent. The default is set by that
    /// latency, not by the corpus's most expensive proof: a few proofs cost
    /// more and need a raised `budget:`, which the miss report suggests.
    /// Null disables the cap.
    global_budget: ?u64 = 2_300_000_000,
    /// Call-stack guard for the recursive descent: the deepest point (in
    /// stack bytes below the driver's entry frame, measured via
    /// `@frameAddress`) the search may recurse to before the branch is
    /// abandoned with an honest exhaustion report. A safety bound, not a
    /// search parameter: the logical bound (`max_depth`) does not
    /// bound *native* call depth — `@auto eager` steps are depth-exempt and
    /// each logical level costs many machine frames — and on wasm a stack
    /// overflow is not a crash but silent linear-memory corruption that
    /// poisons the allocator for the rest of the session (the instance is
    /// dead until page reload). Sized far above anything real proofs reach
    /// (the tait depth corpus — the deepest known workload — peaks at
    /// ~430 KiB of native stack, measured below the driver's entry frame at
    /// the guard's check points) and comfortably under the 8 MiB
    /// stack the wasm executables link with (`build.zig` `stack_size`),
    /// leaving headroom for the frames between two check points (one level
    /// of the core's descent plus expression walks). On wasm the engine's own
    /// call stack (984 KiB in V8) runs out first, with a trap that kills the
    /// instance, and these bytes count only the part of a frame kept in linear
    /// memory: a chain of rules traps between 1 and 1.5 MiB of them, and
    /// Pelletier 34 between 1.5 and 2 MiB. Overridable only for tests.
    stack_guard_bytes: usize = if (@import("builtin").target.cpu.arch.isWasm()) 768 * 1024 else 4 * 1024 * 1024,

    /// The depth limit of a call that sets none and has no budget.
    pub const default_depth: usize = 6;

    /// The call's depth limit, or `default_depth`: the depth a miss report
    /// and its retry advice start from.
    pub fn defaultDepth(self: GenerateOptions) usize {
        return self.max_depth orelse default_depth;
    }

    /// The core's limit: none, unless the call sets one or has no budget.
    pub fn coreDepth(self: GenerateOptions) ?usize {
        return self.max_depth orelse if (self.global_budget == null) default_depth else null;
    }
};

pub const SourceSuggestionOptions = struct {
    /// The most suggestions a search tactic or the completion filter
    /// returns. An open goal lists every rule that applies.
    max_results: usize = 5,
    /// Probe every rule against the goal of the ordinary rule application
    /// under the requested source offset, and return the names of those
    /// whose conclusion matches (the completion filter). The default needs
    /// a search placeholder or an open goal there.
    apply_at_offset: bool = false,
    /// Optional tighter cap for `exact?`/`auto?`, which want one best result,
    /// leaving the completion filter's rules on the full `max_results`. When
    /// set, it also lets `exact?` short-circuit recursive generation once it
    /// has enough proofs. `null` = use `max_results` for every mode (the bench
    /// does this to keep generation hotspots visible).
    exact_result_limit: ?usize = null,
    counters: ?*SearchCounters = null,
    generate: GenerateOptions = .{},
    /// Build a human-readable `status_detail` string for failed searches
    /// (see `SourceSuggestions.status_detail`) and enable the candidate
    /// timers (`SearchCounters.collect` on the local counters block, when
    /// the caller supplies none). Off by default so the bench and
    /// programmatic callers pay nothing.
    status_detail: bool = false,
    /// Backs the search's working memory, which it frees as it goes; null
    /// uses the caller's allocator. A caller whose allocator is an arena (the
    /// LSP's per-request one) passes the allocator under it here, or the
    /// search's frees reclaim nothing until the request ends.
    work_allocator: ?std.mem.Allocator = null,
};
