//! Bounded recursive proof search for `auto?`.
//!
//! Architecture: **lazy slot recursion via a generation hook** (see
//! `search/ARCHITECTURE.md`). The `backward/backtrack.zig` backtracker is
//! the single engine: it grounds a rule's hypotheses from the ref pool, and —
//! through the `GenerationHook` this module installs — asks us to synthesize a
//! sub-proof for any slot the pool can't close whose binders are already pinned
//! (by the conclusion or by sibling refs chosen earlier in the backtrack). The
//! sub-proof is itself produced by re-running the backtracker one depth shallower
//! with the same hook, so open hypotheses get grounded before recursion reaches
//! them. Generation is candidate construction only; the whole assembly is
//! validated through the ordinary `tryCandidate` pipeline inside `backward/backtrack.zig`.

const std = @import("std");
const types = @import("./types.zig");
const backtrack = @import("./backward/backtrack.zig");
const acui = @import("./backward/acui.zig");
const Witness = @import("./backward/witness.zig");
const forward = @import("./forward.zig");
const trigger = @import("./trigger.zig");
const ref_index_mod = @import("./ref_index.zig");
const session_mod = @import("./session.zig");
const candidate_mod = @import("./candidate.zig");
const expr_mod = @import("../../expr.zig");
const ExprId = @import("../../expr.zig").ExprId;
const PlaceholderId = @import("../../expr.zig").PlaceholderId;
const TheoremContext = @import("../../expr.zig").TheoremContext;
const MetaStore = @import("../inference/meta_store.zig").MetaStore;
const OpenTerms = @import("../inference/open_terms.zig");
const ProofScript = @import("../../proof_script.zig");
const RuleApplication = ProofScript.RuleApplication;
const Ref = ProofScript.Ref;
const CompilerContext = @import("../context.zig").CompilerContext;
const Check = @import("../check.zig");
const Goal = types.Goal;
const Context = types.Context;
const SearchCounters = types.SearchCounters;
const VerdictMemo = types.VerdictMemo;
const DeepVerdictCache = types.DeepVerdictCache;
const NameExprMap = types.NameExprMap;
const GenerateOptions = types.GenerateOptions;
const GenerationHook = types.GenerationHook;

/// Generated full proof trees for a goal. The trees are owned by `arena`; they
/// stay valid until `deinit`, which the caller invokes after rendering.
pub const GeneratedResults = struct {
    arena: std.heap.ArenaAllocator,
    applications: []const RuleApplication,
    /// True when the global fuel floor was hit before the search completed. A
    /// distinct outcome from "no proof found": the search stopped early, so the
    /// absence of a suggestion is inconclusive rather than a definite miss.
    budget_exhausted: bool = false,

    pub fn deinit(self: *GeneratedResults) void {
        self.arena.deinit();
        self.* = undefined;
    }
};

/// Key for the within-pass concrete-failure memo: a `solveProof` result
/// depends on both the target and the remaining recursion depth. `target` is
/// the canonical content hash of the ACUI-*canonical* form (`contentKey`),
/// shared with `concrete_ok`, so an exhausted failure skips every ACUI
/// variant of the goal, not just the literal one searched.
const ConcreteFailKey = struct { target: u64, depth: usize };

/// Value for the concrete-success memo (`concrete_ok`): the cached sub-proof's
/// application tree plus the actual generation depth it occupies, so it is
/// replayed only when the current remaining budget admits it. Only the
/// application is stored — a replay is relabeled to the caller's exact target
/// (see `solveProof`), so the proof's own concluded `ExprId` is never reused.
const OkMemo = struct { application: RuleApplication, gen_depth: usize };

const Driver = struct {
    compiler: *CompilerContext,
    session: *session_mod.SearchSession,
    context: *const Context,
    /// Driver-owned mutable clone of the caller's theorem. Cloning preserves
    /// `ExprId` numbering, so the caller's goal/pool ids stay valid. Subgoal
    /// expressions (which the backtracker produces in *throwaway* candidate
    /// clones) are re-interned into whatever this points at so their `ExprId`s
    /// are stable for the duration of the sub-solve — but the pointer is NOT
    /// constant across the recursion: every child sub-solve (`solveProof` and
    /// `hookSolveOpen` alike) swaps in a discardable COW scope clone for its
    /// own subtree and restores the parent on exit, so child-search interning
    /// dies with the subtree instead of accumulating for the whole search.
    /// Only root-level interning (the pass goal, pool-var dummies, trigger
    /// seeds, forward saturation) lands in the root theorem permanently.
    work_theorem: *TheoremContext,
    theorem_vars: *const NameExprMap,
    /// Arena for the proof trees that escape into `GeneratedResults`.
    arena: std.mem.Allocator,
    /// Real allocator for transient search work. Never escapes the driver.
    scratch: std.mem.Allocator,
    options: GenerateOptions,
    counters: ?*SearchCounters,
    /// Forward-saturation pool (null when the theory declares no
    /// `@auto forward` rules). Shared across every depth and sub-solve; uses
    /// are transient (solve, materialize, roll back).
    derived: ?*types.DerivedPool = null,
    hook: GenerationHook = undefined,
    /// Depth at which the next hook-driven sub-proof should be solved. Set
    /// before each `exactWithSession` call that carries the hook and restored
    /// after, so sibling slots at the same level share a depth.
    current_depth: usize = 0,
    visited: std.AutoHashMapUnmanaged(ExprId, void) = .{},
    /// Visited guard for open targets. Freshly minted metas get
    /// fresh `ExprId`s on every attempt, so the `ExprId`-keyed set above
    /// would never collide for alpha-variant open goals; open targets are
    /// keyed canonically instead (metas numbered by first occurrence). Keys
    /// are owned by `scratch` and freed on removal.
    visited_open: std.StringHashMapUnmanaged(void) = .{},
    /// Within-pass negative memo for structured open targets (carry-to-leaf
    /// witness solves). `visited_open` is only a DFS *path* guard — it is
    /// removed when a solve returns, so sibling subtrees re-solve an identical
    /// canonical open target from scratch. The large two-branch additive
    /// proofs (`*_dist_*`) re-derive the same ~100 doomed leaf witness targets
    /// per depth pass that way. This cache remembers canonical keys whose
    /// solve was fully explored and genuinely failed (all candidates tried, no
    /// match-back) so siblings skip them. Sound within a pass because failures
    /// are memoized only when neither the node budget nor the DFS path guard
    /// pruned the subtree, and fuel exhaustion propagates as an error, not a
    /// null.
    /// Cleared at each (depth, phase) ladder cell, like `visited_open`. Keyed by
    /// the (depth-independent) canonical open key; the value is a bitset of the
    /// `current_depth`s at which that target genuinely failed. Depth matters —
    /// a target unprovable shallow may be provable deeper — so a failure only
    /// replays at the same depth. A bitset value (not a depth-augmented key)
    /// keeps the per-call check allocation-free (`current_depth < 16`).
    open_fail: std.StringHashMapUnmanaged(u16) = .{},
    /// Concrete (`solveProof`) analogue of `open_fail`, keyed by `(canonical
    /// target content hash, depth)` (the same key as `concrete_ok`, so an
    /// exhausted failure covers every ACUI variant). `visited` is only a path
    /// guard (removed on exit), so sibling subtrees re-solve identical concrete
    /// leaf targets; this remembers the genuinely-exhausted failures within a
    /// pass.
    concrete_fail: std.AutoHashMapUnmanaged(ConcreteFailKey, void) = .{},
    /// Success ("transposition table") dual of `concrete_fail`. A concrete
    /// subgoal proved once is reusable wherever it recurs (the pool and
    /// `work_theorem` are constant across the search), so this collapses the
    /// re-proof of shared subgoals in convergent / DAG-shaped proofs and the
    /// redundant re-derivation of a goal reached via different (commuting)
    /// invertible-rule orderings.
    ///
    /// Keyed by the canonical content hash (`contentKey`) of the ACUI-
    /// *canonical* form of the target, NOT by `(target, depth)`. A found proof
    /// is a complete, valid tree; its validity does not depend on the budget it
    /// was found under (unlike a *failure*, which is depth-relative — hence
    /// `concrete_fail` keeps its depth). We instead store the proof's actual
    /// generation depth (`gen_depth`) and replay it only when the current
    /// remaining budget is at least that deep, so a shallow subproof found
    /// anywhere is reused everywhere it fits, never returning a proof too deep
    /// for the budget.
    ///
    /// The ACUI-canonical key lets two ACUI-equal subgoals share a slot: a
    /// sub-proof found for one is reused for the other. The cached application
    /// proves the canonical variant, so on a hit it is returned *relabeled* to
    /// the caller's exact target — `tryCandidate` recompiles the spliced
    /// assembly and the proof compiler inserts the reordering bridge (the same
    /// ACUI matching that lets `exact?` fire against a reordered ref). Without
    /// the relabel the cached variant's conclusion would fail
    /// `emitGeneratedSlot`'s strict conclusion gate and poison the slot.
    ///
    /// The CONTENT hash (never a raw `ExprId`) is what lets entries survive
    /// `hookSolveOpen` interner-scope discards: a subgoal first proved inside
    /// an open scope keeps its memo entry (the stored application is
    /// arena-owned source syntax, id-free), so the transposition memo works
    /// across open-chain boundaries with no eviction or re-keying machinery.
    ///
    /// NOT cleared per depth: a success is valid in every later pass.
    concrete_ok: std.AutoHashMapUnmanaged(u64, OkMemo) = .{},
    /// Ladder phase index (0-based) of the currently running cell. Set by
    /// `runPhaseLadder` next to the capability flags; keys the persisted
    /// failure memos below by the capability set they were recorded under.
    phase_index: usize = 0,
    /// Cross-cell persisted failure memos (`GenerateOptions.
    /// persist_negative`, default on). Unlike the per-cell memos above,
    /// these survive the whole retry ladder: a genuinely-exhaustive
    /// failure at (target, depth d, phase p) is a pure semantic fact —
    /// "no proof of gen-depth ≤ d under phase-p capabilities and this
    /// pool" — because the phase capability flags are cumulative, linearly
    /// ordered, and purely additive (each only ADDS candidate branches),
    /// and the exhaustiveness guards (`budget_trips`/`path_prunes`)
    /// already exclude truncated verdicts. So a recorded failure soundly
    /// covers any later re-solve at depth ≤ d under phase ≤ p — which the
    /// depth-major core re-encounters constantly (phases 1–2 re-run at
    /// every depth after phase 3 already failed the same targets) — and,
    /// because depth-0 solves carry no hook at all, ANY recorded failure
    /// covers depth-0 re-solves at every phase. `concrete_ok` growth
    /// cannot contradict a covered verdict (a replayed proof of gen-depth
    /// g ≤ d under covered flags would contradict the recorded
    /// exhaustiveness), but the ok-replay is still checked FIRST in
    /// `solveProof`: an ok entry found under STRONGER flags than a
    /// recorded fail is consistent with it and must win on re-encounter.
    /// Keys are scope-stable canonical content (the `contentKey` hash /
    /// the canonical open key bytes), values per-phase failure depths
    /// (max depth for concrete, depth bitset for open). Cleared at the
    /// two ladder-rerun boundaries where the verdict inputs genuinely
    /// change (phase-6 seeded pool, eager-cut valve). Open verdicts are
    /// recorded only when the child enumeration was NOT truncated by
    /// `open_child_max_results` — a truncated fail ("the first N
    /// candidates didn't match back") is not a pure semantic fact and was
    /// observed to flip on re-solve; truncated open fails keep their
    /// per-cell lifetime in `open_fail` above. When `persist_negative` is
    /// off nothing is recorded here, so lookups degrade to the per-cell
    /// maps and behavior is bit-identical to the per-cell-only scheme.
    /// Corpus-validated by shadow instrumentation before the real
    /// implementation: zero contradicted verdicts across ~550k would-skip
    /// re-solves; ~17-21% of generation ticks had been re-deriving
    /// already-known failures.
    persist_concrete_fail: std.AutoHashMapUnmanaged(u64, [5]u8) = .{},
    persist_open_fail: std.StringHashMapUnmanaged([5]u16) = .{},
    /// True when the theory registers at least one ACUI combiner. Gates the
    /// canonicalization walk in `canonicalKey` so non-ACUI theories pay nothing.
    has_acui: bool = false,
    /// Any registered combiner declares commutativity — the precondition for
    /// the member-wise ACUI read-back pass (which abstains on everything else).
    has_comm_acui: bool = false,
    nodes: usize = 0,
    /// Monotonic count of node-budget early-returns. Used to decide whether a
    /// failure was truncated by the `nodes` cap inside its own subtree (compare
    /// the value at subtree entry and exit): if it grew, some descendant bailed
    /// on budget, so the failure is not exhaustive and must not enter a
    /// failure memo.
    budget_trips: usize = 0,
    /// Monotonic count of DFS path-guard prunes. A solve that only fails
    /// because a descendant target is already on the current recursion path is
    /// not an unconditional failure; the same target may succeed from a sibling
    /// branch with a different ancestor set. Failure memos are therefore only
    /// written when this count is unchanged across the subtree.
    path_prunes: usize = 0,
    /// Global counter for stable cross-interner `meta_id`s, shared by every
    /// open slot's store so a witness meta keeps one identity through the
    /// open-target recursion (carry-to-leaf). See `MetaStore.meta_id_counter`.
    next_meta_id: u64 = 0,
    /// Expensive-op budget for the currently running phase, shared by all
    /// recursive sub-solves. Each retry phase owns one fuel pool spanning all
    /// its depths (the per-depth bound is `nodes`); the ladder swaps the
    /// running phase's pool in here around every (depth, phase) cell.
    fuel: types.Fuel,
};

/// Top-level entry: find proof trees for `goal` that use at least one generated
/// inline application (so they are genuinely novel relative to direct `exact?`).
pub fn generateTopLevel(
    compiler: *CompilerContext,
    session: *session_mod.SearchSession,
    goal: Goal,
    theorem: *const TheoremContext,
    theorem_vars: *const NameExprMap,
    options: GenerateOptions,
) !GeneratedResults {
    var arena = std.heap.ArenaAllocator.init(session.allocator);
    errdefer arena.deinit();

    // Per-call cost budget (ticks), spanning forward saturation and all retry
    // phases. Initialized before any work so the tick snapshot covers the
    // whole call; every phase's fresh `Fuel` shares this one budget.
    const ticks_start = expr_mod.work_ticks;
    const sym_ticks_start = expr_mod.work_ticks_sym;
    const walk_ticks_start = expr_mod.work_ticks_walk;
    var global_budget: ?types.GlobalBudget = if (options.global_budget) |limit|
        types.GlobalBudget.init(limit)
    else
        null;
    const budget_ptr: ?*types.GlobalBudget = if (global_budget) |*budget|
        budget
    else
        null;

    const goal_expr = switch (goal) {
        .concrete => |expr| expr,
        // Holey / whole-conclusion goals are deferred (Step 4).
        else => return .{ .arena = arena, .applications = &.{} },
    };
    if (options.max_depth == 0) {
        return .{ .arena = arena, .applications = &.{} };
    }

    var work_theorem = try theorem.clone();
    defer work_theorem.deinit();

    // When the theory enrolls rules in open backward generation,
    // pre-materialize every `@vars` pool token as a named theorem-local dummy
    // in the work theorem (sorted for deterministic dummy ids), through a
    // driver-owned clone of the theorem-vars map. Open bound binders then
    // enumerate these as concrete witnesses; the rendered explicit binding
    // re-materializes the same name on the user's side. Theories without
    // `@auto backward` skip this entirely, keeping behavior byte-identical.
    var vars_clone: ?types.NameExprMap = null;
    defer if (vars_clone) |*clone| clone.deinit();
    var effective_vars: *const NameExprMap = theorem_vars;
    if (session.context.registry.autoBackwardRuleCount() > 0 and
        session.context.sort_vars.count() > 0)
    {
        vars_clone = try Check.cloneNameExprMap(
            session.allocator,
            theorem_vars,
        );
        var tokens = std.ArrayListUnmanaged([]const u8){};
        defer tokens.deinit(session.allocator);
        var token_iter = session.context.sort_vars.tokens.keyIterator();
        while (token_iter.next()) |token| {
            try tokens.append(session.allocator, token.*);
        }
        std.mem.sort([]const u8, tokens.items, {}, stringLessThan);
        for (tokens.items) |token| {
            const decl = session.context.sort_vars.getTokenDecl(token) orelse
                continue;
            work_theorem.ensureNamedDummyParserVar(
                session.context.parser.core.allocator,
                &vars_clone.?,
                token,
                decl.sort_name,
                decl.sort_id,
            ) catch |err| switch (err) {
                error.OutOfMemory => return error.OutOfMemory,
                // Dep-slot exhaustion: the pool variable is simply not
                // available as a witness; branches needing it fail cleanly.
                else => {},
            };
        }
        effective_vars = &vars_clone.?;
    }

    // Bounded multi-layer forward saturation over the ref pool
    // before backward search. Skipped entirely (no cost) when the theory
    // declares no `@auto forward` rules — and never run on the
    // `exact?`/`apply?` paths, which don't reach this driver. The session's
    // clipper-backed ref index (built here, reused by the backward search
    // right after) pre-filters pool sources per premise slot.
    var derived_pool: ?types.DerivedPool = null;
    defer if (derived_pool) |*dpool| dpool.deinit();
    if (session.context.registry.autoForwardRuleCount() > 0) {
        const ref_pool = try session.getReferencePool(
            theorem,
            session.effectiveCounters(null),
        );
        const ref_index = try session.getRefIndex(
            theorem,
            session.effectiveCounters(null),
        );
        derived_pool = try forward.saturate(
            session.context,
            &work_theorem,
            ref_pool,
            ref_index,
            options.forward,
            session.effectiveCounters(null),
            &.{},
        );
        try buildDerivedIndex(session, &work_theorem, &derived_pool.?);
    }

    // Search-reuse memos (Lever A reject-verdict memo + Lever B re-pin prune)
    // ride on a counters block that spans this whole `generateTopLevel` (all
    // retry phases). The bench supplies a counters block; production usually
    // doesn't, so fall back to a local one purely as the memo's carrier. The
    // memo's stats are snapshotted into the (value-readable) counters fields
    // before it deinits, so observability survives in either case.
    var fallback_counters = SearchCounters{};
    const gen_counters = session.effectiveCounters(null) orelse &fallback_counters;
    var verdict_memo = VerdictMemo{
        .allocator = session.allocator,
        .skip_enabled = options.search_memo,
    };
    defer {
        // Snapshot stats for an observing caller, then DETACH the pointer before
        // freeing — `gen_counters` may be a caller-owned block that outlives this
        // call, so it must never be left pointing at the freed stack memo.
        gen_counters.verdict_reject_total = verdict_memo.reject_total;
        gen_counters.verdict_reject_distinct = verdict_memo.reject_distinct;
        gen_counters.verdict_skips = verdict_memo.skips;
        gen_counters.verdict_memo = null;
        verdict_memo.deinit();
    }
    // Cross-candidate deep-member verdict cache (same Driver-owned lifecycle).
    var deep_cache = DeepVerdictCache{ .allocator = session.allocator };
    defer {
        gen_counters.deep_cache_hits = deep_cache.hits;
        gen_counters.deep_cache_misses = deep_cache.misses;
        gen_counters.deep_verdict_cache = null;
        deep_cache.deinit();
    }
    gen_counters.deep_verdict_cache = &deep_cache;
    // Only arm the memo + prune when enabled; otherwise leave the carrier clean
    // so `tryCandidate` computes no signature and the baseline path is untouched.
    if (options.search_memo) {
        gen_counters.verdict_memo = &verdict_memo;
        gen_counters.repin_prune_enabled = true;
    }
    // Lever E (default-on, independent of the memo bundle so it can be A/B'd
    // alone): the deep-unfold ACUI member prune.
    gen_counters.deep_member_prune_enabled = options.deep_member_prune;

    var driver = Driver{
        .compiler = compiler,
        .session = session,
        .context = session.context,
        .work_theorem = &work_theorem,
        .theorem_vars = effective_vars,
        .arena = arena.allocator(),
        .scratch = session.allocator,
        .options = options,
        .counters = gen_counters,
        .derived = if (derived_pool) |*dpool| dpool else null,
        .fuel = .{ .remaining = options.fuel, .global = budget_ptr },
        .has_acui = session.context.registry.acui_by_head.count() > 0,
        .has_comm_acui = acui.hasCommutativeCombiner(session.context),
    };
    driver.hook = .{
        .ctx = &driver,
        .solveFn = hookSolve,
        .solveOpenFn = hookSolveOpen,
        .allow_split = false,
        .meta_id_counter = &driver.next_meta_id,
    };
    defer driver.visited.deinit(driver.scratch);
    defer {
        var key_iter = driver.visited_open.keyIterator();
        while (key_iter.next()) |key| driver.scratch.free(key.*);
        driver.visited_open.deinit(driver.scratch);
    }
    defer {
        var key_iter = driver.open_fail.keyIterator();
        while (key_iter.next()) |key| driver.scratch.free(key.*);
        driver.open_fail.deinit(driver.scratch);
    }
    defer driver.concrete_fail.deinit(driver.scratch);
    defer driver.concrete_ok.deinit(driver.scratch);
    defer driver.persist_concrete_fail.deinit(driver.scratch);
    defer {
        var key_iter = driver.persist_open_fail.keyIterator();
        while (key_iter.next()) |key| driver.scratch.free(key.*);
        driver.persist_open_fail.deinit(driver.scratch);
    }

    var applications = std.ArrayListUnmanaged(RuleApplication){};
    var budget_exhausted = try runPhaseLadder(
        &driver,
        goal_expr,
        &applications,
        budget_ptr,
        vars_clone != null,
    );

    // Phase 6: only on a clean miss of the whole ladder, and only when the
    // theory declares `@auto trigger` rules — harvest ground seed instances
    // from the goal's subterms (the analytic leaf set; see `trigger.zig`),
    // rebuild the derived pool with the seeds included, and re-run the
    // ladder against it. Seeds are ordinary derived refs, so backward search
    // can pin premise-only elimination binders from them (the sequent
    // left-rule gap) and forward joins fire over them. Like phases 2–5, this
    // runs last with fresh fuel only when everything else found nothing:
    // proofs the ordinary phases handle never pay, and breadth stays
    // byte-identical by construction.
    var seeded_pool: ?types.DerivedPool = null;
    defer if (seeded_pool) |*dpool| dpool.deinit();
    if (applications.items.len == 0 and !budget_exhausted and
        session.context.registry.triggerRuleCount() > 0)
    {
        const seeds = try trigger.harvestSeeds(
            session.context,
            &work_theorem,
            goal_expr,
            session.allocator,
        );
        defer session.allocator.free(seeds);
        if (seeds.len > 0) {
            gen_counters.trigger_seed_count += seeds.len;
            seeded_pool = blk: {
                if (session.context.registry.autoForwardRuleCount() > 0) {
                    // Re-saturate with the seeds as depth-0 sources so
                    // forward joins fire over them too.
                    const ref_pool = try session.getReferencePool(
                        theorem,
                        session.effectiveCounters(null),
                    );
                    const ref_index = try session.getRefIndex(
                        theorem,
                        session.effectiveCounters(null),
                    );
                    break :blk try forward.saturate(
                        session.context,
                        &work_theorem,
                        ref_pool,
                        ref_index,
                        options.forward,
                        session.effectiveCounters(null),
                        seeds,
                    );
                }
                break :blk try trigger.seedOnlyPool(session.context, seeds);
            };
            try buildDerivedIndex(session, &work_theorem, &seeded_pool.?);
            driver.derived = &seeded_pool.?;
            // The seeded pool changes every failure verdict's inputs; the
            // persisted memos must not carry across.
            clearPersistedFails(&driver);
            budget_exhausted = try runPhaseLadder(
                &driver,
                goal_expr,
                &applications,
                budget_ptr,
                vars_clone != null,
            );
        }
    }

    // Eager-cut safety valve: still a clean miss and the theory declares
    // `@auto eager` rules — the set-commit cut may have pruned the only
    // proof (a mis-annotated, non-invertible eager rule). Re-run the whole
    // ladder with the cut disabled; the eager band order and the depth
    // exemption stay (they are scheduling, not commitment). Fresh per-phase
    // fuel like every retry, same global tick budget. Theories without
    // eager annotations never reach this, and annotated theories pay only
    // on a clean miss — proofs the cut-honoring ladder finds never do.
    if (applications.items.len == 0 and !budget_exhausted and
        session.context.registry.autoEagerRuleCount() > 0)
    {
        driver.hook.honor_eager_cut = false;
        // Disabling the cut widens exploration relative to every verdict
        // recorded with it honored; cut-honoring failures do not cover
        // cut-free re-solves. (Depth-0 verdicts would survive — no hook at
        // depth 0 — but clear conservatively.)
        clearPersistedFails(&driver);
        budget_exhausted = try runPhaseLadder(
            &driver,
            goal_expr,
            &applications,
            budget_ptr,
            vars_clone != null,
        );
    }

    // Mirror the forward layer's meta-store activity into the bench counters
    // (META.md performance gates).
    if (derived_pool) |*dpool| {
        if (driver.counters) |c| {
            c.universal_metas_created += dpool.store.stats.universal_created;
            c.meta_assignments += dpool.store.stats.assignments;
            c.meta_rollbacks += dpool.store.stats.rollbacks;
        }
    }
    if (seeded_pool) |*dpool| {
        if (driver.counters) |c| {
            c.universal_metas_created += dpool.store.stats.universal_created;
            c.meta_assignments += dpool.store.stats.assignments;
            c.meta_rollbacks += dpool.store.stats.rollbacks;
        }
    }

    // Per-call cost observability: ticks consumed by this whole call and
    // whether the per-call budget (not per-phase fuel) truncated it.
    gen_counters.gen_work_ticks = expr_mod.work_ticks -% ticks_start;
    gen_counters.gen_sym_ticks = expr_mod.work_ticks_sym -% sym_ticks_start;
    gen_counters.gen_walk_ticks =
        expr_mod.work_ticks_walk -% walk_ticks_start;
    if (global_budget) |budget| {
        gen_counters.gen_budget_exhausted = budget.exhausted;
    }

    return .{
        .arena = arena,
        .applications = try driver.arena.dupe(
            RuleApplication,
            applications.items,
        ),
        .budget_exhausted = budget_exhausted,
    };
}

/// Index a derived pool's shapes so backward search pre-filters them per
/// slot/goal exactly like pool refs, instead of attempting every derived ref
/// at every open hypothesis slot at every depth. A failed build (e.g. an
/// unknown term in a shape) just keeps the linear-scan fallback.
fn buildDerivedIndex(
    session: *session_mod.SearchSession,
    work_theorem: *TheoremContext,
    dpool: *types.DerivedPool,
) !void {
    if (dpool.refs.len == 0) return;
    const shapes = try session.allocator.alloc(ExprId, dpool.refs.len);
    defer session.allocator.free(shapes);
    for (dpool.refs, 0..) |dref, idx| shapes[idx] = dref.shape;
    dpool.index = blk: {
        break :blk ref_index_mod.Index.buildFromExprs(
            session.allocator,
            session.context,
            work_theorem,
            shapes,
            session.shape_options,
            session.effectiveCounters(null),
        ) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            else => break :blk null,
        };
    };
}

/// The retry-phase ladder (phases 1–5): a DEPTH-MAJOR core over phases 1–3
/// (outer iterative deepening 1..max_depth, inner phases per depth, stopping
/// at the first (depth, phase) cell that yields results), followed by
/// phase-major tail ladders for phases 4–5 on a clean core miss. Extracted
/// so the phase-6 trigger-seeding retry can re-run the whole ladder against
/// the seeded derived pool. Returns true if a budget floor was hit.
///
/// Why depth-major: `max_depth` monotonicity is a PREFIX property of the cell
/// visit order. Depth-major makes a higher max_depth's cell sequence a strict
/// prefix-extension of a lower one's, so under the same global budget raising
/// max_depth can never lose a finding — it executes the identical prefix,
/// then continues. The original phase-major nesting (each phase running its
/// own complete depth ladder, later phases only on a clean ladder miss)
/// REORDERED the sequence as max_depth grew: a proof living in a later phase
/// at a shallow depth was reachable only after the earlier phases exhausted
/// all depths, so raising max_depth inserted exponentially costlier doomed
/// deep passes in front of the finding cell until the shared global budget
/// died inside one of them (the drinker md≥8 flood; its usable window was
/// md∈[5,7] before this reorder). Depth-major visits cells in roughly
/// increasing cost order, so found searches never pay a deeper pass of any
/// phase.
///
/// Why phases 4–5 stay phase-major tails: depth-major's cost ordering
/// assumes cost grows exponentially in depth but only modestly across phases
/// at a fixed depth. That holds for phases 1–3 — splitting and witness
/// invention fire only at specific node types (split sites, open witness
/// slots) — but NOT for retention and constrained MP, which broaden the
/// branching of every additive split node / every implication-shaped goal
/// respectively: their fixed-depth cost has a strictly larger exponential
/// base. Interleaved below a core find they inflate found cost ~3x and blow
/// budget-marginal finds (measured on tait ex_swap/all_an_dist_fwd,
/// 2026-07-05); as clean-miss tails they cost exactly what they do today.
/// The md-monotonicity guarantee therefore covers proofs reachable by
/// phases 1–3; phase-4/5 proofs keep the old phase-major behavior.
///
/// What phase-major guaranteed and how it is preserved:
/// - Within a core depth, phase order still runs anchored-first: a
///   split-free proof beats a split proof beats an invented witness, at
///   equal proof height; retention and constrained-MP proofs rank last
///   overall exactly as before. Each phase's capability flags stay
///   cumulative (see the flag docs on `GenerationHook`). What changes is
///   the CROSS-depth preference within the core: a shallow invented-witness
///   proof now beats a deeper split-free proof.
/// - Each phase still draws from its own per-phase fuel pool across depths
///   (`phase_fuel`). A phase's own cell sequence in depth order is identical
///   in both nestings, so its fuel drains — and exhausts — at exactly the
///   same cell as before; only the interleaving with other phases' cells
///   changed.
/// - Exhaustion of the GLOBAL tick budget aborts the whole ladder, exactly
///   as before. Exhaustion of one core phase's own fuel, however, only
///   RETIRES that phase (its remaining cells are skipped); the other phases
///   keep their pools and continue. Phase-major could afford to abort
///   everything on any exhaustion because an exhausted phase had, by the
///   clean-miss gating, no earlier phase left to hurt — here an expensive
///   phase flooding out at a shallow cell must not kill a sibling phase's
///   deeper find. A retirement still reports the ladder as budget-truncated
///   (the miss is not clean, so the tail phases and the phase-6
///   trigger-seeding gate stay exactly as conservative as before). Abort and
///   retire points depend only on cumulative work along the fixed visit
///   order, so md monotonicity holds even on truncated calls.
fn runPhaseLadder(
    driver: *Driver,
    goal_expr: ExprId,
    applications: *std.ArrayListUnmanaged(RuleApplication),
    budget_ptr: ?*types.GlobalBudget,
    has_vars_pool: bool,
) anyerror!bool {
    const options = driver.options;
    // Phase gates, constant across the ladder. Phase 3 (witness invention)
    // needs the pre-materialized `@vars` witness pool (the `@auto backward` +
    // non-empty `@vars` gate in `generateTopLevel`); phase 4 (principal
    // retention) needs an idempotent structural combiner. A gated-off phase
    // contributes neither its cell nor its capability flag to later phases,
    // exactly as phase-major's cumulative flag inheritance did.
    const has_idem = hasIdempotentCombiner(driver.context);
    var phase_fuel = [5]usize{
        options.fuel,
        options.fuel,
        options.fuel,
        options.fuel,
        options.phase5_fuel orelse options.fuel,
    };
    // Core: phases 1–3, depth-major.
    var retired = [_]bool{false} ** core_phase_count;
    var any_retired = false;
    var depth_limit: usize = 1;
    while (depth_limit <= options.max_depth) : (depth_limit += 1) {
        for (0..core_phase_count) |phase| {
            if (retired[phase]) continue;
            if (phase == 2 and !has_vars_pool) continue;
            // Cumulative capabilities, phase index 0-based: 0 ordinary
            // (non-splitting) generation, 1 + ACUI context splitting, 2
            // + witness invention, 3 + idempotent principal retention, 4
            // + constrained backward modus ponens.
            driver.hook.allow_split = phase >= 1;
            driver.hook.allow_invent_witness = phase >= 2 and has_vars_pool;
            driver.hook.allow_retain_principal = false;
            driver.hook.allow_constrained_mp = false;
            driver.phase_index = phase;
            driver.fuel = .{
                .remaining = phase_fuel[phase],
                .global = budget_ptr,
            };
            const exhausted = try runDepthPass(
                driver,
                goal_expr,
                depth_limit,
                applications,
            );
            phase_fuel[phase] = driver.fuel.remaining;
            if (exhausted) {
                // The global tick budget aborts everything; a core phase's
                // own fuel running dry only retires that phase. `GlobalBudget`
                // marks itself exhausted before erroring, so the two share
                // an error but are distinguishable here.
                const global_exhausted = if (budget_ptr) |budget|
                    budget.exhausted
                else
                    false;
                if (global_exhausted) return true;
                retired[phase] = true;
                any_retired = true;
                continue;
            }
            if (applications.items.len > 0) return false;
        }
    }
    // A retired core phase means the miss is not clean; stay exactly as
    // conservative as phase-major (where any fuel exhaustion blocked all
    // later phases) and skip the tails.
    if (any_retired) return true;

    // Tail: phases 4–5, phase-major full ladders, each only on a clean miss
    // of everything before it — identical to the original nesting.
    for (core_phase_count..phase_fuel.len) |phase| {
        if (phase == 3 and !has_idem) continue;
        driver.hook.allow_split = true;
        driver.hook.allow_invent_witness = has_vars_pool;
        driver.hook.allow_retain_principal = phase >= 3 and has_idem;
        driver.hook.allow_constrained_mp = phase >= 4;
        driver.phase_index = phase;
        driver.fuel = .{
            .remaining = phase_fuel[phase],
            .global = budget_ptr,
        };
        var tail_depth: usize = 1;
        while (tail_depth <= options.max_depth) : (tail_depth += 1) {
            const exhausted = try runDepthPass(
                driver,
                goal_expr,
                tail_depth,
                applications,
            );
            if (exhausted) return true;
            if (applications.items.len > 0) return false;
        }
    }
    return false;
}

/// Phases 1–3 (indices 0–2) form the depth-major core of `runPhaseLadder`;
/// phases 4–5 run as phase-major tails. See the ladder doc for why the
/// boundary sits here (fixed-depth cost growth across phases).
const core_phase_count = 3;

/// True when the theory declares at least one *idempotent* structural combiner
/// (`@acui ... idem`). Gates the phase-4 principal-retention pass so a theory
/// without an idempotent context never pays even the extra clean-miss pass.
fn hasIdempotentCombiner(context: *const Context) bool {
    var it = context.registry.acui_by_head.valueIterator();
    while (it.next()) |combiner| {
        if (combiner.idem_name != null) return true;
    }
    return false;
}

/// One single-depth generation pass over `goal_expr` under the driver's
/// currently configured phase flags and fuel — one (depth, phase) ladder
/// cell — appending generation-using assemblies to `applications`. Returns
/// true if a budget floor was hit. The per-cell `nodes` counter and the
/// per-cell failure memos reset here (a deeper pass can succeed where a
/// shallow one failed, and a later phase can succeed where an earlier one
/// failed at the same depth — the raw (target, depth) verdicts don't carry).
/// The `persist_*_fail` maps do NOT reset: they tag each verdict with the
/// phase it was recorded under and replay it only at covering
/// (depth ≤, phase ≤) re-encounters, which stays sound across cells (see
/// the field doc).
fn runDepthPass(
    driver: *Driver,
    goal_expr: ExprId,
    depth_limit: usize,
    applications: *std.ArrayListUnmanaged(RuleApplication),
) anyerror!bool {
    driver.nodes = 0;
    // Ladder-progress observability for the failure report: which (depth,
    // phase) cell was running when the search ended (phase 1-based).
    if (driver.counters) |c| {
        c.gen_last_depth = depth_limit;
        c.gen_last_phase = driver.phase_index + 1;
    }
    driver.visited.clearRetainingCapacity();
    var open_keys = driver.visited_open.keyIterator();
    while (open_keys.next()) |key| driver.scratch.free(key.*);
    driver.visited_open.clearRetainingCapacity();
    var fail_keys = driver.open_fail.keyIterator();
    while (fail_keys.next()) |key| driver.scratch.free(key.*);
    driver.open_fail.clearRetainingCapacity();
    driver.concrete_fail.clearRetainingCapacity();
    // NB: `concrete_ok` is deliberately NOT cleared between cells. A found
    // proof is valid in every later pass, so persisting it lets later cells
    // replay sub-solves already proved instead of re-deriving them — the
    // `nodes` counter resets per cell, so these replays cost it nothing (and
    // every replay is revalidated by `tryCandidate`).
    // Don't let a sub-proof recurse back onto the root goal.
    try driver.visited.put(driver.scratch, goal_expr, {});
    // The root's hypotheses' sub-proofs are one level shallower than the
    // current limit.
    driver.current_depth = depth_limit - 1;

    var results = backtrack.exactWithSession(
        driver.compiler,
        driver.session,
        Goal{ .concrete = goal_expr },
        driver.work_theorem,
        driver.theorem_vars,
        .{
            .max_results = driver.options.max_results,
            .generator = &driver.hook,
            .counters = driver.counters,
            .fuel = &driver.fuel,
            .derived = driver.derived,
        },
    ) catch |err| switch (err) {
        // A budget floor was hit mid-search; stop and report it distinctly.
        error.SearchBudgetExhausted => {
            if (driver.counters) |c| c.recursive_budget_exhausted = true;
            return true;
        },
        else => return err,
    };
    defer results.deinit();

    for (results.candidates) |candidate| {
        // Only surface assemblies that actually used generation; pure-ref
        // proofs are already offered by direct `exact?`.
        if (!applicationUsesInlineApp(candidate.application)) {
            continue;
        }
        try applications.append(
            driver.arena,
            try cloneApplication(driver.arena, candidate.application),
        );
    }
    return false;
}

/// `GenerationHook.solveFn`: the backtracker calls this for a hypothesis slot it
/// could not close from the pool. `target` is concrete in `target_theorem` (a
/// clone of `work_theorem`); we lift it into `work_theorem` and solve it.
fn hookSolve(
    ctx: *anyopaque,
    target: ExprId,
    target_theorem: *TheoremContext,
    eager_step: bool,
) anyerror!?types.GeneratedProof {
    const driver: *Driver = @ptrCast(@alignCast(ctx));
    const lifted = (try reinternConcrete(
        driver.work_theorem,
        target_theorem,
        target,
    )) orelse return null;
    // `@auto eager` depth exemption: an eager application is a "don't-care"
    // decomposition, so its subgoal keeps the parent's remaining depth —
    // `current_depth` was already decremented at the parent's `solveProof`
    // entry (or set to `depth_limit - 1` at the pass root), so add the level
    // back. Never exceeds the pass's `depth_limit`, and stays bounded
    // regardless: eager children still pay nodes, fuel, and global ticks,
    // and the `visited` path guard catches cycles.
    const depth = if (eager_step)
        driver.current_depth + 1
    else
        driver.current_depth;
    var proof = (try solveProof(driver, lifted, depth)) orelse
        return null;
    proof.conclusion = (try reinternConcrete(
        target_theorem,
        driver.work_theorem,
        proof.conclusion,
    )) orelse return null;
    return proof;
}

/// Number of child candidates the open-target solver inspects before giving
/// up on a slot: the implicit-conclusion child search is hint-guided but not
/// hint-enforcing, so the first accepted proof may conclude something the
/// match-back rejects.
const open_child_max_results: usize = 4;

/// `GenerationHook.solveOpenFn`: solve a *structured open*
/// hypothesis target whose unsolved leaves are existential metas in `store`.
/// The target is lifted into `work_theorem` with each distinct meta replaced
/// by one dep-free wildcard placeholder (identity preserved), and solved by
/// an ordinary child search against that hint via an implicit-conclusion
/// goal. Each child candidate's checker-accepted conclusion is translated
/// back and matched structurally against the open target — the match IS the
/// witness solve; on success the assignments are left in `store` (they
/// persist in the branch; the caller owns the rollback site) and the proof
/// is returned with its concrete conclusion.
fn hookSolveOpen(
    ctx: *anyopaque,
    target: ExprId,
    target_theorem: *TheoremContext,
    store: *MetaStore,
) anyerror!?types.GeneratedProof {
    const driver: *Driver = @ptrCast(@alignCast(ctx));

    // Canonical visited key: metas numbered by first occurrence, so two
    // alpha-variant open targets (fresh meta ids each attempt) collide.
    const key = try canonicalOpenKey(driver.scratch, target_theorem, target);
    // Depth bit for the failure memo: the solve depends on remaining recursion
    // depth, so a failure is only replayable at the same depth.
    const depth_bit: u16 = if (driver.current_depth < 16)
        @as(u16, 1) << @intCast(driver.current_depth)
    else
        0;
    // Cheap O(1) skips (DFS path guard + failure memos) are charged no node
    // budget: the budget bounds real exploration work, and counting a
    // memoized skip would defeat the memo (the dist proofs have ~70% repeat
    // open targets, so charging skips burns the whole budget on dedup hits).
    // The persisted map holds only untruncated cross-cell verdicts (empty
    // when `persist_negative` is off); the per-cell map keeps the truncated
    // ones.
    if (persistOpenCovered(driver, key, driver.current_depth)) {
        if (driver.counters) |c| c.persist_open_skips += 1;
        driver.scratch.free(key);
        return null;
    }
    const memo_hit = if (driver.open_fail.get(key)) |bits|
        (depth_bit != 0 and (bits & depth_bit) != 0)
    else
        false;
    if (memo_hit) {
        driver.scratch.free(key);
        return null;
    }
    if (driver.visited_open.contains(key)) {
        driver.path_prunes += 1;
        driver.scratch.free(key);
        return null;
    }
    // Per-call cost budget: bound long generation stretches between
    // `Fuel.spend` sites too (candidate assembly/enumeration burns ticks
    // without spending fuel). Checked only where real exploration begins, so
    // memoized skips stay free, mirroring the node budget above.
    if (driver.fuel.global) |budget| {
        budget.check() catch |err| {
            driver.scratch.free(key);
            return err;
        };
    }
    if (driver.nodes >= driver.options.max_nodes) {
        driver.budget_trips += 1;
        driver.scratch.free(key);
        return null;
    }
    driver.nodes += 1;
    const trips_at_entry = driver.budget_trips;
    const path_prunes_at_entry = driver.path_prunes;
    try driver.visited_open.put(driver.scratch, key, {});
    defer {
        _ = driver.visited_open.remove(key);
        driver.scratch.free(key);
    }

    // Interner scope: everything this call interns into the work theorem —
    // the fresh-meta hint below, the child search's candidate assemblies and
    // canonical forms, generation-local dummies — goes into a discardable COW
    // clone and dies here. Fresh meta ids make every open target unique, so
    // without the scope a doomed open chain grows the shared append-only
    // interner without bound (multi-GiB on a single miss). Nothing returned
    // references the scope's id-space: the proof application is arena-owned
    // source syntax and the conclusion is reinterned into `target_theorem`.
    // The swap is safe because a COW clone extends its base's id-space — every
    // pre-existing ExprId (derived-ref shapes, theorem vars) stays valid and
    // identical inside the scope. Persistent memos that outlive the scope
    // (`concrete_ok`/`concrete_fail`, `VerdictMemo`, `DeepVerdictCache`) key
    // by scope-stable canonical CONTENT (`types.hashCanonicalContent`), never
    // raw ExprIds, so a discarded id-space invalidates nothing and successes
    // first proved inside the scope stay reusable after it (the transposition
    // memo works across open-chain boundaries). `open_fail`/`visited_open`
    // key on canonical byte strings; `visited` is strictly LIFO within
    // `solveProof`. Any NEW persistent cache on the Driver or SearchCounters
    // must follow the same rule: content keys, or a strictly scope-local
    // lifetime.
    // The session's ref pool / index are built lazily from the FIRST theorem
    // a search passes in (`exactWithSession` fetches the pool on entry). A
    // scoped child search must never be that first build — the entries would
    // capture scope-minted ids in session-persistent state. Our enclosing
    // `exactWithSession` already built the pool against the parent id-space;
    // enforce that ordering here rather than leave it implicit.
    std.debug.assert(driver.session.reference_pool != null);
    var scope_theorem = try driver.work_theorem.clone();
    defer scope_theorem.deinit();
    // Dummy analogue of the interner scope: dummies minted during the child
    // search (indexes at or above this) die with the scope, so a child
    // conclusion referencing one must not be read back — `target_theorem`
    // either lacks the index (dangling) or owns an unrelated dummy there
    // (misbinding).
    const scope_dummy_base = scope_theorem.theorem_dummies.items.len;
    const parent_theorem = driver.work_theorem;
    driver.work_theorem = &scope_theorem;
    defer driver.work_theorem = parent_theorem;

    var meta_map = std.AutoHashMapUnmanaged(PlaceholderId, ExprId){};
    defer meta_map.deinit(driver.scratch);
    const hint = (try reinternHint(
        driver.work_theorem,
        target_theorem,
        store,
        &meta_map,
        driver.scratch,
        target,
    )) orelse return null;

    const depth = driver.current_depth;
    const generator: ?*const GenerationHook = if (depth > 0) &driver.hook else null;
    const saved_depth = driver.current_depth;
    driver.current_depth = if (depth > 0) depth - 1 else 0;
    defer driver.current_depth = saved_depth;

    var results = try backtrack.exactWithSession(
        driver.compiler,
        driver.session,
        Goal{ .implicit_whole_conclusion = hint },
        driver.work_theorem,
        driver.theorem_vars,
        .{
            .max_results = open_child_max_results,
            .generator = generator,
            .counters = driver.counters,
            .fuel = &driver.fuel,
            .derived = driver.derived,
            .internal_open_child = true,
        },
    );
    defer results.deinit();
    if (driver.counters) |c| c.generated_chain_attempts += 1;

    for (results.candidates) |candidate| {
        const accepted = acceptedConclusion(
            driver,
            candidate.application,
            Goal{ .implicit_whole_conclusion = hint },
        ) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            else => continue,
        };
        // A conclusion referencing a scope-minted dummy cannot escape (see
        // `scope_dummy_base`); `reinternConcrete`'s per-index check alone
        // cannot catch the case where `target_theorem` owns an unrelated
        // same-sort dummy at the same index.
        if (driver.work_theorem.exprAny(
            accepted,
            scope_dummy_base,
            scopeDummyEscapes,
        )) continue;
        const back = (try reinternConcrete(
            target_theorem,
            driver.work_theorem,
            accepted,
        )) orelse continue;
        const mark = store.mark();
        if (forward.solveCorrespondence(
            store,
            target_theorem,
            back,
            target,
            null,
        ) == .ok and store.isFullySolved(target_theorem, target)) {
            return .{
                .application = try cloneApplication(
                    driver.arena,
                    candidate.application,
                ),
                .conclusion = back,
            };
        }
        store.rollbackTo(mark);
        // Fallback: the positional `solveCorrespondence` can conflict when the
        // child's accepted conclusion carries redundant ACUI units (a stray
        // `emp` member) that the open target — built unit-free — does not. This
        // is the readback dual of `emitOpenTarget`'s unit canonicalization.
        // Normalizing both sides' units away and retrying lets the
        // member-for-member match align (meta leaves survive normalization).
        // Only reached after the un-normalized match already failed, so any
        // readback that succeeds today is untouched.
        //
        // NOT subsumed by the member-wise third pass below: normalizeAcuiUnits
        // flattens and drops units for EVERY registered combiner head,
        // including non-commutative (AU) subsets, where the third pass
        // deliberately abstains. This pass is the only unit/reassociation
        // recovery an AU-subset theory gets — keep it even if it looks
        // redundant on fully-commutative theories.
        const back_n = acui.normalizeAcuiUnits(driver.context, target_theorem, back) catch back;
        const target_n = acui.normalizeAcuiUnits(driver.context, target_theorem, target) catch target;
        if ((back_n != back or target_n != target) and
            forward.solveCorrespondence(
                store,
                target_theorem,
                back_n,
                target_n,
                null,
            ) == .ok and store.isFullySolved(target_theorem, target_n))
        {
            return .{
                .application = try cloneApplication(
                    driver.arena,
                    candidate.application,
                ),
                .conclusion = back_n,
            };
        }
        store.rollbackTo(mark);
        // Third pass: member-wise ACUI-aware correspondence. The child's
        // accepted conclusion can be ACUI-equal to the target yet positionally
        // misaligned (the checker bridges conclusion-vs-hint, but the checked
        // line keeps the child rule's own association/order), which both
        // passes above reject. Match the commutative ACUI regions as
        // multisets instead. The returned conclusion is RELABELED to the
        // materialized target (the child proof concludes an ACUI variant of
        // it): `continueOpenTargetSolved` requires conclusion == materialized
        // target by identity, and the recompile validates the spliced
        // assembly, inserting the ACUI reorder bridge — the same relabeling
        // discipline as the transposition memo replay. Skipped when the
        // theory registers no commutative combiner (the pass degenerates to
        // the positional walk that already failed twice).
        if (driver.has_comm_acui) {
            if (try Witness.solveCorrespondenceAcui(
                driver.context,
                store,
                target_theorem,
                back,
                target,
            ) and store.isFullySolved(target_theorem, target)) {
                const relabeled: ?ExprId = store.materialize(target_theorem, target) catch |err| switch (err) {
                    error.OutOfMemory => return error.OutOfMemory,
                    else => null,
                };
                if (relabeled) |conclusion| {
                    if (driver.counters) |c| c.readback_acui_recovered += 1;
                    return .{
                        .application = try cloneApplication(
                            driver.arena,
                            candidate.application,
                        ),
                        .conclusion = conclusion,
                    };
                }
            }
            store.rollbackTo(mark);
            // Observe-only probe, AFTER the pass so the two counters are
            // disjoint outcomes: `readback_acui_recovered` = third pass
            // succeeded; `readback_acui_misalign` = it abstained although the
            // child conclusion still contains every rigid ACUI member of the
            // target (the plausibly-missed residual).
            if (driver.counters) |c| {
                if (readbackAcuiPlausible(driver.context, target_theorem, back, target)) {
                    c.readback_acui_misalign += 1;
                }
            }
        }
    }
    // Genuine exhaustive failure: every child candidate was tried and none
    // matched back. Cache it so sibling subtrees skip this canonical target.
    // Guard: only when no node-budget bail or DFS path-prune happened anywhere
    // in this subtree (`budget_trips` / `path_prunes` unchanged since entry) —
    // otherwise the exploration was truncated or ancestor-dependent, so the
    // failure is not exhaustive. Fuel exhaustion propagates as an error, never
    // a null, so it cannot reach here. The key is owned by the `defer` above,
    // so the memo takes its own copy.
    if (driver.budget_trips == trips_at_entry and
        driver.path_prunes == path_prunes_at_entry and
        depth_bit != 0)
    {
        // Persist only untruncated verdicts: a fail with a full candidate
        // list means "the first `open_child_max_results` child candidates
        // didn't match back", not "no candidate matches back" —
        // `concrete_ok` growth between cells can change which candidates
        // surface, so a truncated verdict is not a pure semantic fact
        // (observed flipping on euclid dvd_add). Truncated fails keep
        // their per-cell lifetime in `open_fail` below.
        if (driver.options.persist_negative and
            results.candidates.len < open_child_max_results)
        {
            persistOpenRecord(driver, key, depth_bit);
            return null;
        }
        const gop = driver.open_fail.getOrPut(driver.scratch, key) catch
            return null;
        if (gop.found_existing) {
            gop.value_ptr.* |= depth_bit;
        } else {
            // New entry: own a copy of the key (the live `key` is freed by the
            // `defer` above). On dup failure, drop the entry rather than alias.
            const owned = driver.scratch.dupe(u8, key) catch {
                _ = driver.open_fail.remove(key);
                return null;
            };
            gop.key_ptr.* = owned;
            gop.value_ptr.* = depth_bit;
        }
    }
    return null;
}

// Measurement predicate for the ACUI read-back residual. True when
// the open target has at least one rigid (concrete, non-unit) ACUI-region
// member and every such member also appears among the child conclusion's
// rigid members — i.e. the positional failure is plausibly a pure
// reorder/reassociation, not a genuinely different conclusion. Set-level
// (dedup) containment; both exprs live in `theorem`, so hash-consing makes
// ExprId equality member equality.
fn readbackAcuiPlausible(
    context: *const Context,
    theorem: *const TheoremContext,
    back: ExprId,
    target: ExprId,
) bool {
    var tmembers: [Witness.max_domain_members]ExprId = undefined;
    const tcount = Witness.collectDomainMembers(context, theorem, target, &tmembers);
    if (tcount == 0) return false;
    var bmembers: [Witness.max_domain_members]ExprId = undefined;
    const bcount = Witness.collectDomainMembers(context, theorem, back, &bmembers);
    for (tmembers[0..tcount]) |tm| {
        var found = false;
        for (bmembers[0..bcount]) |bm| {
            if (bm == tm) {
                found = true;
                break;
            }
        }
        if (!found) return false;
    }
    return true;
}

/// Lift an open target from a candidate clone into `dst` for use as a child
/// search hint. Unsolved store metas become dep-free wildcard placeholders
/// in `dst`, one per distinct meta (the hash-consed shared leaf preserves
/// repeated-occurrence identity); solved metas are dereferenced. Returns
/// null for a placeholder that is not a registered meta.
fn reinternHint(
    dst: *TheoremContext,
    src: *const TheoremContext,
    store: *const MetaStore,
    meta_map: *std.AutoHashMapUnmanaged(PlaceholderId, ExprId),
    scratch: std.mem.Allocator,
    id: ExprId,
) anyerror!?ExprId {
    return switch (src.interner.node(id).*) {
        .variable => |var_id| try dst.interner.internVar(var_id),
        .placeholder => |pid| {
            if (store.lookup(pid)) |value| {
                return try reinternHint(dst, src, store, meta_map, scratch, value);
            }
            const info = store.info(pid) orelse return null;
            const gop = try meta_map.getOrPut(scratch, pid);
            if (!gop.found_existing) {
                // Preserve the meta's stable identity across the interner
                // boundary: the child's hole is the *same* logical meta, so a
                // descendant slot can re-register and bind it at the leaf
                // (carry-to-leaf). Falls back to a plain hole for metas with
                // no stable id (legacy path).
                gop.value_ptr.* = if (src.placeholderMetaId(pid)) |meta_id|
                    try dst.addMetaPlaceholderWithMetaId(info.sort_name, meta_id)
                else
                    try dst.addMetaPlaceholderResolved(info.sort_name);
            }
            return gop.value_ptr.*;
        },
        .app => |app| {
            const args = try dst.allocator.alloc(ExprId, app.args.len);
            defer dst.allocator.free(args);
            for (app.args, 0..) |arg, idx| {
                args[idx] = (try reinternHint(
                    dst,
                    src,
                    store,
                    meta_map,
                    scratch,
                    arg,
                )) orelse return null;
            }
            return try dst.interner.internApp(app.term_id, args);
        },
    };
}

/// Serialize an open target with every placeholder numbered by first
/// occurrence — the canonical form for the open visited set.
fn canonicalOpenKey(
    allocator: std.mem.Allocator,
    theorem: *const TheoremContext,
    expr: ExprId,
) ![]u8 {
    var out = std.ArrayListUnmanaged(u8){};
    errdefer out.deinit(allocator);
    var numbering = std.AutoHashMapUnmanaged(u32, u32){};
    defer numbering.deinit(allocator);
    try appendCanonicalKey(&out, &numbering, allocator, theorem, expr);
    return try out.toOwnedSlice(allocator);
}

fn appendCanonicalKey(
    out: *std.ArrayListUnmanaged(u8),
    numbering: *std.AutoHashMapUnmanaged(u32, u32),
    allocator: std.mem.Allocator,
    theorem: *const TheoremContext,
    expr: ExprId,
) anyerror!void {
    switch (theorem.interner.node(expr).*) {
        .variable => |var_id| switch (var_id) {
            .theorem_var => |idx| {
                try out.append(allocator, 'v');
                try appendCanonicalInt(out, allocator, idx);
            },
            .dummy_var => |idx| {
                try out.append(allocator, 'w');
                try appendCanonicalInt(out, allocator, idx);
            },
        },
        .placeholder => |pid| {
            const gop = try numbering.getOrPut(allocator, pid);
            if (!gop.found_existing) {
                gop.value_ptr.* = @intCast(numbering.count() - 1);
            }
            try out.append(allocator, 'm');
            try appendCanonicalInt(out, allocator, gop.value_ptr.*);
        },
        .app => |app| {
            try out.append(allocator, 'a');
            try appendCanonicalInt(out, allocator, app.term_id);
            try appendCanonicalInt(out, allocator, @intCast(app.args.len));
            for (app.args) |arg| {
                try appendCanonicalKey(out, numbering, allocator, theorem, arg);
            }
        },
    }
}

fn appendCanonicalInt(
    out: *std.ArrayListUnmanaged(u8),
    allocator: std.mem.Allocator,
    value: u32,
) !void {
    var buf: [4]u8 = undefined;
    std.mem.writeInt(u32, &buf, value, .little);
    try out.appendSlice(allocator, &buf);
}

fn stringLessThan(_: void, lhs: []const u8, rhs: []const u8) bool {
    return std.mem.lessThan(u8, lhs, rhs);
}

// ---------------------------------------------------------------------------
// Cross-cell persisted failure memos (see the `persist_concrete_fail` /
// `persist_open_fail` field doc). Two covering rules:
//   - phase closure: a genuinely-exhaustive fail at (target, depth d,
//     phase p) covers re-solves at depth ≤ d under phase ≤ p (capability
//     flags are cumulative and purely additive along the phase order);
//   - depth-0 universality: depth-0 solves run generator=null (no hook),
//     so ANY recorded fail covers a depth-0 re-solve at every phase.

const persist_no_depth: u8 = 0xff;

fn clearPersistedFails(driver: *Driver) void {
    driver.persist_concrete_fail.clearRetainingCapacity();
    var key_iter = driver.persist_open_fail.keyIterator();
    while (key_iter.next()) |key| driver.scratch.free(key.*);
    driver.persist_open_fail.clearRetainingCapacity();
}

fn persistConcreteCovered(
    driver: *const Driver,
    target: u64,
    depth: usize,
) bool {
    const entry = driver.persist_concrete_fail.get(target) orelse return false;
    var p: usize = driver.phase_index;
    while (p < entry.len) : (p += 1) {
        if (entry[p] != persist_no_depth and @as(usize, entry[p]) >= depth)
            return true;
    }
    if (depth == 0) {
        p = 0;
        while (p < driver.phase_index) : (p += 1) {
            if (entry[p] != persist_no_depth) return true;
        }
    }
    return false;
}

fn persistConcreteRecord(driver: *Driver, target: u64, depth: usize) void {
    // Clamping only loses coverage (a fail at a deeper budget covers the
    // clamped depth's ≤-cone too), never overstates it. Best-effort: an
    // OOM just forgoes the memo, like the per-cell maps.
    const d: u8 = @intCast(@min(depth, persist_no_depth - 1));
    const gop = driver.persist_concrete_fail.getOrPut(
        driver.scratch,
        target,
    ) catch return;
    if (!gop.found_existing) gop.value_ptr.* = @splat(persist_no_depth);
    const cur = &gop.value_ptr.*[driver.phase_index];
    if (cur.* == persist_no_depth or d > cur.*) cur.* = d;
}

fn persistOpenCovered(
    driver: *const Driver,
    key: []const u8,
    depth: usize,
) bool {
    if (depth >= 16) return false;
    const entry = driver.persist_open_fail.get(key) orelse return false;
    // A fail recorded at depth d covers re-solves at depth ≤ d: any set
    // bit at position ≥ depth is a covering verdict.
    const mask_ge: u16 = @as(u16, 0xffff) << @intCast(depth);
    var p: usize = driver.phase_index;
    while (p < entry.len) : (p += 1) {
        if (entry[p] & mask_ge != 0) return true;
    }
    if (depth == 0) {
        p = 0;
        while (p < driver.phase_index) : (p += 1) {
            if (entry[p] != 0) return true;
        }
    }
    return false;
}

fn persistOpenRecord(driver: *Driver, key: []const u8, depth_bit: u16) void {
    const gop = driver.persist_open_fail.getOrPut(
        driver.scratch,
        key,
    ) catch return;
    if (gop.found_existing) {
        gop.value_ptr.*[driver.phase_index] |= depth_bit;
        return;
    }
    // Own a copy of the key (the caller's is freed on solve exit). On dup
    // failure, drop the entry rather than alias.
    const owned = driver.scratch.dupe(u8, key) catch {
        _ = driver.persist_open_fail.remove(key);
        return;
    };
    gop.key_ptr.* = owned;
    gop.value_ptr.* = @splat(0);
    gop.value_ptr.*[driver.phase_index] = depth_bit;
}

/// Produce one proof of `target` (already in `work_theorem`) at the given depth,
/// as an arena-owned `GeneratedProof`, or null. At depth 0 the sub-search is
/// pool-refs-only (a leaf); deeper, it carries the hook so its own open hyps can
/// recurse.
fn solveProof(
    driver: *Driver,
    target: ExprId,
    depth: usize,
) anyerror!?types.GeneratedProof {
    // One canonical content key feeds both concrete memos. Two ACUI-equal
    // subgoals are equi-provable at a given depth (the proof compiler bridges
    // the reordering at compile time, costing no generation depth), so a
    // cached success replays for either and an exhausted failure skips
    // either. Computed once here and reused, so the failure memo shares the
    // success memo's only cost (one canonicalization walk — a no-op on a
    // non-ACUI theory via the `has_acui` gate — plus one content-hash walk).
    const ok_key = contentKey(driver, target);
    const fail_key = ConcreteFailKey{ .target = ok_key, .depth = depth };
    // Transposition hit: this `target` was already proved in a sibling subtree
    // (or an earlier pass) at a generation depth the current budget admits.
    // Replay the cached proof (a fresh arena clone so the spliced copy never
    // aliases the memo entry). Charged no node budget, like the failure-memo /
    // path-guard skips. Safe even when `target` is on the DFS path: the cached
    // proof is a complete acyclic tree.
    //
    // Checked BEFORE the failure memos: a persisted failure recorded under
    // weaker phase flags is consistent with a proof found later under
    // stronger ones (the ok entry), and the proof must win on re-encounter.
    // (Within one cell the two cannot conflict — an exhaustive fail at
    // (target, d) rules out any same-flags proof of gen-depth ≤ d — so this
    // ordering is only load-bearing for the persisted memo.)
    if (driver.concrete_ok.get(ok_key)) |memo| {
        if (depth >= memo.gen_depth) {
            // Relabel the cached proof to the caller's *exact* target. When the
            // memo hit is an ACUI variant the application concludes a reordered
            // form, but `tryCandidate` recompiles the spliced assembly and the
            // proof compiler bridges the reordering — so the conclusion the
            // parent splice sees (and the `proof.conclusion != target` gate at
            // `emitGeneratedSlot`) must be `target`, not the cached variant.
            return .{
                .application = try cloneApplication(
                    driver.arena,
                    memo.application,
                ),
                .conclusion = target,
            };
        }
    }
    // Cheap O(1) skips (failure memos + DFS path guard) are charged no node
    // budget, mirroring `hookSolveOpen`. The persisted map is empty when
    // `persist_negative` is off (nothing records into it), so the check
    // degrades to the per-cell memo alone.
    if (persistConcreteCovered(driver, ok_key, depth)) {
        if (driver.counters) |c| c.persist_concrete_skips += 1;
        return null;
    }
    if (driver.concrete_fail.contains(fail_key)) return null;
    if (driver.visited.contains(target)) {
        driver.path_prunes += 1;
        return null;
    }
    // Per-call cost budget (see `hookSolveOpen`'s twin check).
    if (driver.fuel.global) |budget| try budget.check();
    if (driver.nodes >= driver.options.max_nodes) {
        driver.budget_trips += 1;
        return null;
    }
    driver.nodes += 1;
    try driver.visited.put(driver.scratch, target, {});
    defer _ = driver.visited.remove(target);
    const trips_at_entry = driver.budget_trips;
    const path_prunes_at_entry = driver.path_prunes;

    // Interner scope: the concrete twin of `hookSolveOpen`'s (see the full
    // rationale there). Everything this sub-solve interns into the work
    // theorem — nested targets lifted by `hookSolve`, ACUI-canonical memo
    // forms, accepted conclusions, per-theorem def-cache growth — goes into
    // a discardable COW clone and dies here, so a long non-repeating
    // concrete chain can no longer grow the shared interner without bound
    // (the open-chain flood's concrete sibling). `target` is a parent id and
    // stays valid inside the scope (a clone extends its base's id-space).
    // Everything that escapes is id-free or translated back: the
    // application is arena-owned source syntax, the conclusion is
    // re-interned into the parent below, and the memos written here
    // (`concrete_ok`/`concrete_fail`, keys computed above pre-scope) key by
    // canonical content, never scope ids. Established only after the cheap
    // O(1) skips above, so memo hits and path prunes pay no clone.
    std.debug.assert(driver.session.reference_pool != null);
    var scope_theorem = try driver.work_theorem.clone();
    defer scope_theorem.deinit();
    const scope_dummy_base = scope_theorem.theorem_dummies.items.len;
    const parent_theorem = driver.work_theorem;
    driver.work_theorem = &scope_theorem;
    defer driver.work_theorem = parent_theorem;

    const generator: ?*const GenerationHook = if (depth > 0) &driver.hook else null;
    const saved_depth = driver.current_depth;
    driver.current_depth = if (depth > 0) depth - 1 else 0;
    defer driver.current_depth = saved_depth;

    var results = try backtrack.exactWithSession(
        driver.compiler,
        driver.session,
        Goal{ .concrete = target },
        driver.work_theorem,
        driver.theorem_vars,
        .{
            .max_results = 1,
            .generator = generator,
            .counters = driver.counters,
            .fuel = &driver.fuel,
            .derived = driver.derived,
            .internal_open_child = true,
        },
    );
    defer results.deinit();
    if (driver.counters) |c| c.generated_chain_attempts += 1;
    if (results.candidates.len == 0) {
        // Genuine exhaustive failure (no candidate at this depth), with no
        // node-budget bail and no DFS path-prune inside the subtree: memoize so
        // siblings skip it.
        if (driver.budget_trips == trips_at_entry and
            driver.path_prunes == path_prunes_at_entry)
        {
            if (driver.options.persist_negative) {
                persistConcreteRecord(driver, ok_key, depth);
            } else {
                // Best-effort: an OOM just forgoes the memo.
                driver.concrete_fail.put(driver.scratch, fail_key, {}) catch {};
            }
        }
        return null;
    }
    const application = try cloneApplication(
        driver.arena,
        results.candidates[0].application,
    );
    const accepted = try acceptedConclusion(
        driver,
        application,
        Goal{ .concrete = target },
    );
    // A conclusion referencing a scope-minted dummy cannot escape (same
    // guard as `hookSolveOpen`'s read-back; `reinternConcrete`'s per-index
    // check alone cannot catch the parent owning an unrelated same-sort
    // dummy at the same index). Not a genuine exhaustive failure, so it is
    // deliberately NOT memoized into `concrete_fail`.
    if (driver.work_theorem.exprAny(
        accepted,
        scope_dummy_base,
        scopeDummyEscapes,
    )) return null;
    const conclusion = (try reinternConcrete(
        parent_theorem,
        driver.work_theorem,
        accepted,
    )) orelse return null;
    // Record the success so a sibling subtree (or later pass) re-reaching this
    // `target` replays it instead of re-searching. Store the shallowest proof
    // seen (best reuse). Best-effort: an OOM here just forgoes the memo.
    const gen_depth = genDepth(driver, application);
    if (driver.concrete_ok.getOrPut(driver.scratch, ok_key)) |gop| {
        if (!gop.found_existing or gen_depth < gop.value_ptr.gen_depth) {
            gop.value_ptr.* = .{
                .application = application,
                .gen_depth = gen_depth,
            };
        }
    } else |_| {}
    return .{
        .application = application,
        .conclusion = conclusion,
    };
}

/// Actual generation depth of a proof tree: the longest chain of nested inline
/// (generated) applications. Pool/hyp refs cost nothing; a proof solvable from
/// the pool alone is depth 0, one generation level is depth 1, etc. Used to
/// decide whether a memoized success fits the current remaining budget.
///
/// An `@auto eager` application does not consume a depth level (`hookSolve`'s
/// exemption), so its child edges cost 0 here too — otherwise a cached
/// ladder-heavy proof would report an inflated depth and refuse to replay at
/// exactly the shallow budgets the exemption makes sufficient.
fn genDepth(driver: *const Driver, app: RuleApplication) usize {
    const edge: usize = if (isEagerApplication(driver, app)) 0 else 1;
    var best: usize = 0;
    for (app.refs) |ref| {
        switch (ref) {
            .application => |child| {
                const d = edge + genDepth(driver, child);
                if (d > best) best = d;
            },
            .hyp, .line => {},
        }
    }
    return best;
}

fn isEagerApplication(driver: *const Driver, app: RuleApplication) bool {
    const registry = driver.context.registry;
    if (registry.autoEagerRuleCount() == 0) return false;
    const rule_id = driver.context.env.getRuleId(app.rule_name) orelse
        return false;
    return registry.eagerPriority(rule_id) != null;
}

/// ACUI-canonical memo key for a concrete target, so two ACUI-equal subgoals
/// share a slot in `concrete_ok` / `concrete_fail`. The identity on a non-ACUI
/// theory (gated by `has_acui`, so those theories pay nothing), with a
/// best-effort fallback to the raw target if canonicalization runs out of
/// interner space — a degraded key is still sound, it just keys exactly rather
/// than canonically.
fn canonicalKey(driver: *Driver, target: ExprId) ExprId {
    if (!driver.has_acui) return target;
    return acui.canonicalizeAcui(
        driver.context,
        driver.work_theorem,
        target,
    ) catch target;
}

/// Scope-stable memo key for a concrete target: the canonical content hash
/// (`types.hashCanonicalContent`) of the target's ACUI-canonical form. The
/// content hash — never the canonical form's raw `ExprId` — is what lets
/// `concrete_ok` / `concrete_fail` entries survive `hookSolveOpen`
/// interner-scope discards without any eviction bookkeeping: a discarded id
/// is re-minted later with different content, but content hashes name the
/// expression itself. Within one interner the hash distinguishes exactly what
/// the id did (hash-consing), so this is a pure superset of id keying. A
/// 64-bit collision replays a wrong cached application — which the
/// `tryCandidate` recompile of the spliced assembly then rejects — so the
/// risk (shared with `applicationSignature`) is a missed proof, never an
/// unsound accept.
fn contentKey(driver: *Driver, target: ExprId) u64 {
    const canon = canonicalKey(driver, target);
    var h = std.hash.Wyhash.init(0x434F4E4352455445);
    types.hashCanonicalContent(driver.work_theorem, canon, &h);
    return h.final();
}

/// Re-check a generated child application and return the conclusion line the
/// checker actually accepted, translated back into `work_theorem`. This is a
/// deliberate belt-and-braces step: generation still proposes ordinary
/// syntax, and the existing checker remains the source of truth for the child
/// conclusion attached to that syntax.
///
/// For an implicit-conclusion goal (the open-target hint), the line's
/// recorded expr is the rule's RAW conclusion (e.g. all_elim's `[x/K] p`),
/// while the open target was built in the `@recover`-applied surface form
/// (`P K → Q K`) — the structural match-back would conflict on the head. When
/// the accepted rule carries a recover view, recompute the applied surface
/// from the checker's own resolved bindings (the same leaf-swap that built
/// the target) and return that instead; the full assembly is still validated
/// by `tryCandidate` afterwards, so a wrong surface can only fail, never leak.
fn acceptedConclusion(
    driver: *Driver,
    application: RuleApplication,
    goal: Goal,
) anyerror!ExprId {
    // Borrowed probe: the returned attempt theorem is a COW clone based
    // directly on `work_theorem` (which outlives it), so the `.owned`
    // materialization this used to request (a whole-interner `flatten()` per
    // accepted candidate — the cost `flatten`'s contract reserves for
    // committed lines) and the pre-clones it required are both pure waste.
    var attempt = try candidate_mod.tryCandidateProbe(
        driver.compiler,
        driver.context,
        application,
        goal,
        driver.work_theorem,
        driver.theorem_vars,
        .{ .result_ownership = .borrowed },
    );
    defer attempt.deinit();

    if (attempt.line_idx < attempt.checked_start) return error.InvalidLineIndex;
    const local_idx = attempt.line_idx - attempt.checked_start;
    if (local_idx >= attempt.checked_lines.len) return error.InvalidLineIndex;
    const line = attempt.checked_lines[local_idx];
    const accepted_theorem = &attempt.theorem.?;
    var accepted = line.expr;
    if (goal == .implicit_whole_conclusion and line.data == .rule) {
        if (try viewSurfaceConclusion(
            driver,
            accepted_theorem,
            line.data.rule,
        )) |surface| accepted = surface;
    }
    return (try reinternConcrete(
        driver.work_theorem,
        accepted_theorem,
        accepted,
    )) orelse error.PlaceholderLeakage;
}

/// The `@recover`-applied surface conclusion of a checked rule line: project
/// the resolved rule bindings into view-binder space, fire each recover law
/// (source := pattern with the hole leaf swapped for the solved target — the
/// same construction as `forward.derive` and the open-target builder), and
/// instantiate the view conclusion. Null when the rule has no view, a law
/// cannot fire, or the view conclusion stays unresolved — callers keep the
/// raw conclusion in that case.
fn viewSurfaceConclusion(
    driver: *Driver,
    theorem: *TheoremContext,
    rule_line: @import("../checked_ir.zig").CheckedLine.RuleLine,
) anyerror!?ExprId {
    const view = driver.context.views.get(rule_line.rule_id) orelse return null;
    const view_bindings = try driver.scratch.alloc(?ExprId, view.num_binders);
    defer driver.scratch.free(view_bindings);
    @memset(view_bindings, null);
    for (view.binder_map, 0..) |maybe_rule_idx, vi| {
        const rule_idx = maybe_rule_idx orelse continue;
        if (rule_idx >= rule_line.bindings.len) continue;
        view_bindings[vi] = rule_line.bindings[rule_idx];
    }
    for (view.derived_bindings) |derived_binding| {
        const rec = switch (derived_binding) {
            .recover => |r| r,
            // No guidance for an abstract motive here; keep the raw form.
            .abstract => return null,
        };
        if (rec.source_view_idx >= view_bindings.len) continue;
        if (view_bindings[rec.source_view_idx] != null) continue;
        if (rec.target_view_idx >= view_bindings.len) return null;
        if (rec.pattern_view_idx >= view_bindings.len) return null;
        if (rec.hole_view_idx >= view_bindings.len) return null;
        const target = view_bindings[rec.target_view_idx] orelse return null;
        const pattern = view_bindings[rec.pattern_view_idx] orelse return null;
        const hole = view_bindings[rec.hole_view_idx] orelse return null;
        view_bindings[rec.source_view_idx] = try forward.leafSwap(
            theorem,
            pattern,
            hole,
            target,
        );
    }
    return try OpenTerms.instantiateTemplateConcrete(
        theorem,
        view.concl,
        view_bindings,
    );
}

/// Re-intern a concrete expression from `src`'s interner into `dst`'s. Returns
/// null if the expression is not concrete (contains a placeholder). Rebuilds
/// structurally (by `var_id` / `term_id`), so it is correct for ANY src/dst
/// pair — ancestor, descendant, or sibling COW clones — and never aliases a
/// raw `ExprId` across interners. (The hookSolveOpen readback at the `back`
/// site uses it sibling-to-sibling: `dst` = the candidate clone, `src` = the
/// discardable scope clone; both extend the same base but neither contains the
/// other's overlay ids. Do NOT "optimize" this to copy ids directly — that is
/// valid only for a true ancestor and would import a scope id that denotes a
/// different expression once the scope is discarded.)
/// `exprAny` predicate: true when `expr` is a dummy at or above the scope's
/// dummy base — a generation-local eigenvariable that must not escape.
fn scopeDummyEscapes(
    base: usize,
    theorem: *const TheoremContext,
    expr: ExprId,
) bool {
    return switch (theorem.interner.node(expr).*) {
        .variable => |var_id| switch (var_id) {
            .dummy_var => |idx| idx >= base,
            .theorem_var => false,
        },
        else => false,
    };
}

fn reinternConcrete(
    dst: *TheoremContext,
    src: *const TheoremContext,
    id: ExprId,
) anyerror!?ExprId {
    return switch (src.interner.node(id).*) {
        .variable => |var_id| {
            // Dummy indexes are a second id-space the ExprId reintern does not
            // translate: they only stay meaningful across theorems that share
            // the append-only `theorem_dummies` prefix (the clone lineage). A
            // dummy `dst` does not know — a child-search-minted eigenvariable
            // escaping its discardable COW scope — would be a dangling index
            // (`requireDummyInfo` crash downstream), so reject the candidate
            // instead. The sort check guards the subtler collision where `dst`
            // happens to own an unrelated dummy at the same index.
            if (var_id == .dummy_var) {
                const idx = var_id.dummy_var;
                if (idx >= dst.theorem_dummies.items.len) return null;
                if (idx >= src.theorem_dummies.items.len) return null;
                const src_info = src.theorem_dummies.items[idx];
                const dst_info = dst.theorem_dummies.items[idx];
                if (src_info.sort_id != dst_info.sort_id or
                    src_info.deps != dst_info.deps) return null;
            }
            return try dst.interner.internVar(var_id);
        },
        .placeholder => null,
        .app => |app| {
            const args = try dst.allocator.alloc(ExprId, app.args.len);
            defer dst.allocator.free(args);
            for (app.args, 0..) |arg, idx| {
                args[idx] = (try reinternConcrete(dst, src, arg)) orelse
                    return null;
            }
            return try dst.interner.internApp(app.term_id, args);
        },
    };
}

/// Deep-copy a `RuleApplication` (recursively, through inline refs) into `arena`
/// so it outlives the transient `ExactResults` it came from. Leaf data
/// (rule/label name slices) point into the stable env/source and are aliased;
/// explicit-binding strings (derived recipes render these into the
/// transient derived pool's arena) are duplicated.
fn cloneApplication(
    arena: std.mem.Allocator,
    app: RuleApplication,
) anyerror!RuleApplication {
    const refs = try arena.alloc(Ref, app.refs.len);
    for (app.refs, 0..) |ref, idx| {
        refs[idx] = switch (ref) {
            .hyp, .line => ref,
            .application => |child| .{
                .application = try cloneApplication(arena, child),
            },
        };
    }
    const zero_span = ProofScript.Span{ .start = 0, .end = 0 };
    const arg_bindings = try arena.alloc(
        ProofScript.ArgBinding,
        app.arg_bindings.len,
    );
    for (app.arg_bindings, 0..) |binding, idx| {
        arg_bindings[idx] = .{
            .name = try arena.dupe(u8, binding.name),
            .name_span = zero_span,
            .formula = .{
                .text = try arena.dupe(u8, binding.formula.text),
                .span = zero_span,
            },
            .span = zero_span,
        };
    }
    var copy = app;
    copy.refs = refs;
    copy.arg_bindings = arg_bindings;
    copy.binding_list_span = null;
    copy.rule_span = zero_span;
    copy.refs_span = if (refs.len == 0) null else zero_span;
    copy.span = zero_span;
    return copy;
}

/// True if the application was produced by generation rather than pure pool
/// refs: it uses an inline `.application` ref somewhere in its tree, or it
/// carries explicit bindings (only derived recipes render those —
/// direct `exact?` never does).
fn applicationUsesInlineApp(app: RuleApplication) bool {
    if (app.arg_bindings.len != 0) return true;
    for (app.refs) |ref| {
        switch (ref) {
            .hyp, .line => {},
            .application => return true,
        }
    }
    return false;
}
