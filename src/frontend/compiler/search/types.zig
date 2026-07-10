const std = @import("std");
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
const MetaStore = @import("../inference/meta_store.zig").MetaStore;
const RuleCatalog = @import("../rule_catalog.zig");
const CompilerViews = @import("../views.zig");
const FreshSelect = @import("../fresh_select.zig");
const CompilerDiag = @import("../diag.zig");
const CheckedIr = @import("../checked_ir.zig");
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

    pub fn lineAssertion(self: Goal) Check.LineAssertion {
        return switch (self) {
            .concrete => |expr| .{ .concrete = expr },
            .holey => |expr| .{ .holey = expr },
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
    rule_catalog: *const RuleCatalog.Catalog,
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

pub const AttemptResultOwnership = enum {
    /// Returned result owns a standalone theorem and may outlive the input.
    owned,
    /// Returned result borrows the input theorem's expression interner.
    /// The caller must not use result theorem data after the input theorem is
    /// destroyed or moved. Intended for hot internal validation paths only.
    borrowed,
};

pub const AttemptOptions = struct {
    commit: bool = false,
    line_label: []const u8 = "<search>",
    assertion_span: Span = .{ .start = 0, .end = 0 },
    diagnostic_span: ?Span = null,
    counters: ?*SearchCounters = null,
    result_ownership: AttemptResultOwnership = .owned,
    /// Caller-computed scope of `validateSelectedRefs`' UnifyMismatch retry arm
    /// (holey goal + view rule + meta-bearing candidate theorem). The verdict
    /// memo consults it so a bare-assembly UnifyMismatch reject that the caller
    /// WILL retry with explicit bindings is never memoized as terminal — the
    /// memo's retry-eligibility predicate must mirror the caller's gate exactly,
    /// and only the caller has the rule/theorem context to compute this arm.
    unify_retry_eligible: bool = false,
};

pub const AttemptResult = struct {
    allocator: std.mem.Allocator,
    committed: bool,
    line_idx: usize,
    checked_start: usize,
    checked_lines: []const CheckedLine,
    theorem: ?TheoremContext,
    theorem_vars: ?NameExprMap,

    pub fn deinit(self: *AttemptResult) void {
        if (!self.committed) {
            CheckedIr.deinitLines(self.allocator, self.checked_lines);
        }
        self.allocator.free(self.checked_lines);
        if (self.theorem_vars) |*vars| vars.deinit();
        if (self.theorem) |*theorem| theorem.deinit();
        self.* = undefined;
    }
};

pub const UnresolvedHypothesis = Check.UnresolvedHypothesis;

pub const ApplyCandidate = struct {
    allocator: std.mem.Allocator,
    rule_id: u32,
    rule_name: []const u8,
    declaration_order: usize,
    theorem: TheoremContext,
    bindings: []const ?ExprId,
    conclusion: ExprId,
    unresolved_hyps: []const UnresolvedHypothesis,
    /// For rules with a `@view`: the view binders solved by matching the
    /// view conclusion against the goal, indexed in view-binder space and
    /// including phantom binders that do not map to any rule binder. Used by
    /// the `@recover` pruning guard during hypothesis matching. `null` when
    /// the rule has no view or the goal is not concrete.
    view_concl_seed: ?[]const ?ExprId = null,
    /// Open backward generation: rule binders whose current value was
    /// solved through an existential meta (or an enumerated bound witness)
    /// rather than pinned by the goal or a ref. Validation renders these as
    /// explicit bindings so the suggestion checks robustly. Allocated lazily
    /// by the open-target path; null on every other path.
    meta_solved: ?[]bool = null,
    /// Set when a generated slot of this candidate launched a child solve
    /// (`emitGeneratedSlot`'s hook call): the application matched the goal
    /// and reached its subgoals. For an `@auto eager` candidate this is the
    /// signal that arms the set-commit cut — a candidate rejected at
    /// conclusion assembly (the rule never actually applied) must not arm it.
    reached_child_solve: bool = false,
    /// True when this candidate is enumerated inside an internal generation
    /// child solve (`ExactOptions.internal_open_child`): its accepted
    /// application will be spliced as a NESTED inline node of a parent
    /// assembly, not surfaced as a suggestion. Validation then renders the
    /// resolved bindings of an accepted `@auto eager` candidate explicitly,
    /// so the parent's re-check never has to re-infer them from an
    /// ACUI-reassociated hint (the nested-inline binder-extraction gap).
    internal_child: bool = false,

    pub fn deinit(self: *ApplyCandidate) void {
        self.allocator.free(self.bindings);
        self.allocator.free(self.unresolved_hyps);
        if (self.view_concl_seed) |seed| self.allocator.free(seed);
        if (self.meta_solved) |flags| self.allocator.free(flags);
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

pub const HypLookupPhase = enum {
    initial,
    dynamic,
};

pub const HypLookupFallback = enum {
    none,
    template_error,
    broad_shape,
};

/// Rule-name storage for the bench diagnostics. These live in the
/// `SearchCounters` block, which the bench copies BY VALUE out of the search
/// (`runFrontierSearch` returns it inside `FrontierRun`) and prints only after
/// `suggestionsAtSourceOffset` has freed its per-call `work_arena` — the very
/// arena that owns every `rule.name` string. Borrowing the arena slice was a
/// use-after-free that crashed `--counters` mode (task #63), so the diagnostics
/// copy the name bytes inline. The cap comfortably covers the corpus (longest
/// identifier ~40 bytes); longer names truncate, which only affects display.
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

pub const HypLookupDiagnostic = struct {
    rule_name: InlineName = .{},
    hyp_index: usize = 0,
    depth: usize = 0,
    phase: HypLookupPhase = .initial,
    filtered_len: usize = 0,
    fallback: HypLookupFallback = .none,
};

pub const RuleAttemptDiagnostic = struct {
    rule_name: InlineName = .{},
    attempts: usize = 0,
    accepted: usize = 0,
    rejected: usize = 0,
};

pub const max_search_diagnostics: usize = 256;

/// Scope-stable canonical content hash of an expression: hashes what the
/// expression MEANS, never a raw `ExprId`, so the result survives a
/// `hookSolveOpen` interner-scope discard (raw ids are ABA-unstable there — a
/// discarded id is re-minted later with different content). Any memo that
/// outlives a scope must key expressions through this, not their ids.
///
/// Leaf identities, chosen so that hash-equal ⟹ semantically interchangeable
/// even across a scope discard:
/// - Theorem vars by index: the theorem's binder list is fixed for a search.
/// - Dummies by (index, sort): `DummyInfo` carries nothing else, and the dep
///   bit advances in lockstep with the index, so the pair fully determines a
///   dummy's semantics — including a same-index same-sort re-mint after a
///   scope discard (the conflation `canonicalOpenKey`'s raw-index dummy
///   serialization already relies on for `open_fail`/`visited_open`).
/// - Placeholders by (id, class, sort, deps, meta_id): within one interner
///   family this is exactly as fine as the ExprId (hash-consing makes
///   distinct pids distinct nodes). Across a scope discard a re-minted pid
///   only collides when all of these match — and `meta_id`s come from a
///   never-reused global counter (`MetaStore.meta_id_counter`), so a
///   colliding `.meta` leaf IS the same metavariable.
///
/// Within one interner the hash is a bijection-preserving image of the id
/// (hash-consing: distinct content ⟺ distinct id), so replacing an id key
/// with this hash changes nothing inside a single search — it only removes
/// the cross-scope ABA hazard. Collisions between genuinely distinct 64-bit
/// keys carry the usual hash risk shared with `applicationSignature`.
pub fn hashCanonicalContent(
    theorem: *const TheoremContext,
    id: ExprId,
    h: *std.hash.Wyhash,
) void {
    switch (theorem.interner.node(id).*) {
        .variable => |var_id| switch (var_id) {
            .theorem_var => |idx| {
                h.update("v");
                h.update(std.mem.asBytes(&idx));
            },
            .dummy_var => |idx| {
                h.update("w");
                h.update(std.mem.asBytes(&idx));
                if (theorem.requireDummyInfo(idx)) |info| {
                    h.update(std.mem.asBytes(&info.sort_id));
                } else |_| {}
            },
        },
        .placeholder => |pid| {
            h.update("m");
            h.update(std.mem.asBytes(&pid));
            if (theorem.placeholderInfo(pid)) |info| {
                const class_byte: u8 = @intFromEnum(info.class);
                h.update(std.mem.asBytes(&class_byte));
                h.update(info.sort_name);
                h.update(std.mem.asBytes(&info.deps));
                if (info.meta_id) |mid| {
                    h.update("M");
                    h.update(std.mem.asBytes(&mid));
                }
            }
        },
        .app => |app| {
            h.update("a");
            h.update(std.mem.asBytes(&app.term_id));
            for (app.args) |arg| hashCanonicalContent(theorem, arg, h);
        },
    }
}

/// Cross-phase verdict memo for `tryCandidate` (Lever A). A `tryCandidate`
/// verdict is a pure function of the concrete `RuleApplication` (the proof term
/// that gets recompiled), the goal, and the fixed base theorem — it does NOT
/// depend on the generation phase or depth limit (those control which proof
/// terms are *assembled*, never whether an already-assembled term checks). So a
/// rejected assembly is monotone: it rejects identically in every later phase.
///
/// CRITICAL soundness rule: the key is the full concrete assembly, NEVER the
/// goal/subgoal alone. Subgoal-provability is NOT monotone across phases (a
/// later phase's split/MP can prove what an earlier one couldn't) — that is why
/// `concrete_fail` stays per-phase/depth. This memo keys on the assembly, so
/// "failure at one phase guarantees failure later" holds by construction.
pub const VerdictMemo = struct {
    /// Set of signatures of assemblies that `tryCandidate` rejected.
    /// Signatures hash goal CONTENT (`hashCanonicalContent`), never raw
    /// `ExprId`s, so they stay valid across `hookSolveOpen` interner-scope
    /// discards — no scope-exit eviction is needed.
    seen: std.AutoHashMapUnmanaged(u64, void) = .{},
    allocator: std.mem.Allocator,
    /// When false (measurement mode) the memo only observes: it records rejects
    /// and counts repeats but never changes behavior. When true it also skips
    /// re-validation on a hit.
    skip_enabled: bool = false,
    reject_total: usize = 0,
    reject_distinct: usize = 0,
    skips: usize = 0,

    pub fn deinit(self: *VerdictMemo) void {
        self.seen.deinit(self.allocator);
    }

    /// True if this assembly was already rejected (skip-eligible). Only consult
    /// when `skip_enabled`.
    pub fn rejectedBefore(self: *VerdictMemo, sig: u64) bool {
        return self.seen.contains(sig);
    }

    /// Record a reject verdict; updates total/distinct repeat measurement.
    /// Best-effort: an OOM just forgoes the entry.
    pub fn recordReject(self: *VerdictMemo, sig: u64) void {
        self.reject_total += 1;
        const gop = self.seen.getOrPut(self.allocator, sig) catch return;
        if (gop.found_existing) return;
        self.reject_distinct += 1;
    }
};

/// Cross-candidate memo for the deep-unfold member verdict
/// (`unfoldedExprMismatch(leaf, member)`). The verdict is a pure function of the
/// two exprs' content + the (fixed-per-search) env; the goal members repeat
/// across every candidate in a search, so caching by a content key amortizes the
/// def-unfolding the per-candidate validator can't share. Driver-owned, spans all
/// of `generateTopLevel`. Key is a 64-bit content hash (collision risk identical
/// to `VerdictMemo`/`applicationSignature`); value is the mismatch verdict.
pub const DeepVerdictCache = struct {
    /// Keys hash both exprs' canonical content (`hashCanonicalContent`), so
    /// entries stay valid across `hookSolveOpen` interner-scope discards — no
    /// scope-exit eviction is needed.
    map: std.AutoHashMapUnmanaged(u64, bool) = .{},
    allocator: std.mem.Allocator,
    hits: usize = 0,
    misses: usize = 0,

    pub fn deinit(self: *DeepVerdictCache) void {
        self.map.deinit(self.allocator);
    }

    pub fn lookup(self: *DeepVerdictCache, key: u64) ?bool {
        if (self.map.get(key)) |v| {
            self.hits += 1;
            return v;
        }
        self.misses += 1;
        return null;
    }

    /// Best-effort: an OOM just forgoes the entry. On a repeat store the
    /// verdict is a pure function of the key, so this can only rewrite the
    /// same value.
    pub fn store(self: *DeepVerdictCache, key: u64, verdict: bool) void {
        self.map.put(self.allocator, key, verdict) catch return;
    }
};

/// Structural signature of a candidate assembly + goal: identical signature ⟹
/// identical `tryCandidate` verdict (against the search's fixed base theorem).
/// Hashes the `RuleApplication` proof term (rule name, explicit binding texts,
/// refs incl. nested inline sub-proofs) — exactly what gets recompiled — plus
/// the goal's canonical CONTENT (`hashCanonicalContent`), so signatures are
/// stable across `hookSolveOpen` interner-scope discards (a raw goal `ExprId`
/// would be ABA-unstable there).
pub fn applicationSignature(
    theorem: *const TheoremContext,
    app: RuleApplication,
    goal: Goal,
) u64 {
    var h = std.hash.Wyhash.init(0x5645524449435421);
    hashApplication(app, &h);
    switch (goal) {
        .concrete => |e| {
            h.update("gc");
            hashCanonicalContent(theorem, e, &h);
        },
        .holey => |p| {
            // Never memoized (tryCandidate's `.holey => null` memo gate): a
            // raw `*const Expr` address is ABA-unstable across phases. Kept
            // only so the function is total over `Goal`.
            h.update("gh");
            const addr = @intFromPtr(p);
            h.update(std.mem.asBytes(&addr));
        },
        .implicit_whole_conclusion => |opt| {
            h.update("gi");
            if (opt) |e| hashCanonicalContent(theorem, e, &h);
        },
    }
    return h.final();
}

fn hashApplication(app: RuleApplication, h: *std.hash.Wyhash) void {
    h.update(app.rule_name);
    h.update(std.mem.asBytes(&app.arg_bindings.len));
    for (app.arg_bindings) |b| {
        h.update(b.name);
        h.update("=");
        h.update(b.formula.text);
    }
    h.update(std.mem.asBytes(&app.refs.len));
    for (app.refs) |r| switch (r) {
        .hyp => |x| {
            h.update("H");
            h.update(std.mem.asBytes(&x.index));
        },
        .line => |x| {
            h.update("L");
            h.update(x.label);
        },
        .application => |x| {
            h.update("A");
            hashApplication(x, h);
        },
    };
}

pub const SearchCounters = struct {
    /// When false (the production default), the expensive per-candidate
    /// diagnostics — `tryCandidate` timers and the per-rule/per-hyp attempt
    /// tallies (`recordRuleAttempt`/`recordHypLookup`, an O(n) name lookup each)
    /// — are skipped. Search BEHAVIOR (the memo + re-pin prune below) never
    /// depends on this; it only gates observability. The bench sets it true.
    /// This keeps the counters block usable purely as the memo carrier (the
    /// Driver attaches a fallback in production) without paying for diagnostics
    /// nothing reads there.
    collect: bool = false,
    /// Lever A reject-verdict memo (optional; bench/driver-owned). Null on paths
    /// that don't use it (plain `exact?`).
    verdict_memo: ?*VerdictMemo = null,
    /// Scalar mirrors of the memo stats, snapshotted before the (value-copied)
    /// counters outlive the memo. `total - distinct` is the skippable repeat
    /// work; `skips` is what the enabled memo actually avoided.
    verdict_reject_total: usize = 0,
    verdict_reject_distinct: usize = 0,
    verdict_skips: usize = 0,
    /// Lever B: re-pin conclusion-plausibility prune. `repin_prune_enabled`
    /// gates the BEHAVIOR (prune on a definite re-pinned mismatch); the counts
    /// are diagnostics gated by `collect`. `would_prune` counts candidates the
    /// re-pin enrichment would reject that the plain check passed; `prunes`
    /// counts actual prunes.
    repin_prune_enabled: bool = false,
    repin_would_prune: usize = 0,
    repin_prunes: usize = 0,
    /// Lever E: deep-unfold ACUI member prune. `deep_member_prune_enabled` gates
    /// the BEHAVIOR (reject on a complete-unfold member divergence); `would_prune`
    /// counts candidates the deep check would reject that the plain check passed,
    /// `prunes` the actual rejects. Counts gated by `collect`. Tests whether
    /// complete def-unfold (vs the one-layer member check) cracks church's
    /// ax/membership reject-flood.
    deep_member_prune_enabled: bool = false,
    deep_member_would_prune: usize = 0,
    deep_member_prunes: usize = 0,
    /// Diagnostic denominator: how many times the deep member check ran (every
    /// candidate that passed the shallow plausibility check). `would_prune /
    /// calls` is the hit rate — distinguishes "cost is inherent to pruning"
    /// (high) from "cost is wasted abstaining walks" (low).
    deep_member_calls: usize = 0,
    /// Cross-candidate verdict cache for the deep member check (optional;
    /// Driver-owned). Amortizes the repeated def-unfolding of fixed goal members.
    deep_verdict_cache: ?*DeepVerdictCache = null,
    deep_cache_hits: usize = 0,
    deep_cache_misses: usize = 0,
    cold_setup_ns: u64 = 0,
    warm_search_ns: u64 = 0,
    /// Work ticks consumed by the whole generation call (all retry phases) —
    /// the raw counts behind the per-call `GlobalBudget`'s weighted cost.
    /// Zero when generation never ran. See `expr.zig` `work_ticks` /
    /// `work_ticks_sym`.
    gen_work_ticks: u64 = 0,
    gen_sym_ticks: u64 = 0,
    gen_walk_ticks: u64 = 0,
    /// Set when the generation call was truncated by the per-call
    /// `GlobalBudget` (as opposed to per-phase fuel).
    gen_budget_exhausted: bool = false,
    rule_index_build_ns: u64 = 0,
    ref_index_build_ns: u64 = 0,
    shape_emission_ns: u64 = 0,
    /// Number of query-side `ShapeSet` builds (one per `lookupTemplate*`/goal
    /// lookup). Paired with `shape_emission_ns` to gauge per-lookup shape cost
    /// and redundancy across a search (see `project_found_outlier_shape_cost`).
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
    conclusion_member_prunes: usize = 0,
    final_conclusion_prunes: usize = 0,
    /// (candidate, refs) tuples refuted by the hyp-vs-ref ACUI member
    /// consistency check (`hypRefMembersPlausible`) before `tryCandidate`:
    /// no conclusion-vs-goal binder assignment makes every pool-ref
    /// conclusion member-consistent with its instantiated hypothesis.
    hyp_ref_prunes: usize = 0,
    /// Broad-slot ref tuples skipped by the `@abstract` one-hole-context
    /// feasibility prefilter (`abstract_prune.zig`) before reaching
    /// `tryCandidate`. Targets the Leibniz-substitution (`eq_replace`) flood.
    abstract_prunes: usize = 0,
    /// Broad-slot ref tuples skipped by the ACUI context-combination prefilter
    /// (`context_prune.zig`): a hypothesis context contributes more rigid members
    /// absent from the goal context than the view discharges.
    context_prunes: usize = 0,
    conclusion_probes: usize = 0,
    ref_pool_size: usize = 0,
    per_hyp_filtered_ref_list_total: usize = 0,
    ref_tuple_count_after_filtering: usize = 0,
    full_try_candidate_calls: usize = 0,
    recursive_apply_calls: usize = 0,
    generated_chain_attempts: usize = 0,
    /// Set when recursive `auto?` generation hit the global fuel floor and
    /// stopped early (distinct from an ordinary no-result miss). Observability
    /// for tests/bench; the authoritative signal is `GeneratedResults`.
    recursive_budget_exhausted: bool = false,
    accepted_candidates: usize = 0,
    rejected_candidates_after_validation: usize = 0,
    hyp_match_syntactic: usize = 0,
    hyp_match_definite_mismatch: usize = 0,
    hyp_match_unknown: usize = 0,
    recover_member_injections: usize = 0,
    split_context_guard_rejects: usize = 0,
    // Distinct ACUI member-witness fills attempted on open
    // targets (each one is a full child generation attempt).
    acui_witness_attempts: usize = 0,
    // Invented-witness fills: an unsolved existential meta with no concrete or
    // coupled anchor grounded to a reused `@vars`-pool dummy (phase-3 only).
    var_pool_witness_attempts: usize = 0,
    // Open-target read-back triple-failures (positional, unit-normalized, and
    // member-wise passes all failed) where the child conclusion still contains
    // every rigid ACUI member of the target — the plausibly-missed residual
    // the member-wise pass did NOT recover. Disjoint from `recovered` below.
    readback_acui_misalign: usize = 0,
    // Read-backs the member-wise ACUI-aware third pass actually recovered
    // (witness solved from an ACUI-equal but reordered child conclusion).
    readback_acui_recovered: usize = 0,
    // Per-call-site work done by the validation-time per-hyp `@recover` clash
    // guard, split by the path that reached it (clean view match vs. partial
    // extraction after a structural match failure).
    recover_guard_match_rejects: usize = 0,
    recover_guard_extract_rejects: usize = 0,
    // Metavariable / forward-saturation counters (META.md
    // "Performance gates"). Landed — and baselined at zero — before any
    // behavior change, so later stages' bench claims diff against recorded
    // numbers. The search driver mirrors `MetaStore.stats` into these once
    // stages 4/7 wire the store in; the forward counters move in stages 7/8.
    wildcard_metas_created: usize = 0,
    existential_metas_created: usize = 0,
    universal_metas_created: usize = 0,
    bound_choice_metas_created: usize = 0,
    meta_assignments: usize = 0,
    meta_rollbacks: usize = 0,
    derived_ref_count: usize = 0,
    /// `@auto trigger` seeds minted for the phase-6 seeding retry (zero when
    /// phase 6 never ran or the harvest matched nothing).
    trigger_seed_count: usize = 0,
    /// Sub-solves skipped by the cross-cell persisted failure memos
    /// (`GenerateOptions.persist_negative`): re-solves whose target was
    /// already exhaustively failed at a covering (depth, phase) in an
    /// earlier ladder cell.
    persist_concrete_skips: usize = 0,
    persist_open_skips: usize = 0,
    forward_rule_attempts: usize = 0,
    forward_match_tuples: usize = 0,
    forward_layers_run: usize = 0,
    /// Set when forward saturation stopped at a budget rather than reaching a
    /// fixpoint (exhaustion is reported separately from a
    /// clean no-result).
    forward_saturation_exhausted: bool = false,
    hyp_lookup_diagnostics_len: usize = 0,
    hyp_lookup_diagnostics: [max_search_diagnostics]HypLookupDiagnostic =
        [_]HypLookupDiagnostic{.{}} ** max_search_diagnostics,
    rule_attempt_diagnostics_len: usize = 0,
    rule_attempt_diagnostics: [max_search_diagnostics]RuleAttemptDiagnostic =
        [_]RuleAttemptDiagnostic{.{}} ** max_search_diagnostics,
    pub fn recordHypLookup(
        self: *SearchCounters,
        rule_name: []const u8,
        diagnostic: HypLookupDiagnostic,
    ) void {
        if (!self.collect) return;
        if (self.hyp_lookup_diagnostics_len >= max_search_diagnostics) return;
        var stored = diagnostic;
        stored.rule_name.set(rule_name);
        self.hyp_lookup_diagnostics[self.hyp_lookup_diagnostics_len] = stored;
        self.hyp_lookup_diagnostics_len += 1;
    }

    pub fn recordRuleAttempt(
        self: *SearchCounters,
        rule_name: []const u8,
        accepted: bool,
    ) void {
        if (!self.collect) return;
        const idx = self.ruleAttemptIndex(rule_name) orelse return;
        self.rule_attempt_diagnostics[idx].attempts += 1;
        if (accepted) {
            self.rule_attempt_diagnostics[idx].accepted += 1;
        } else {
            self.rule_attempt_diagnostics[idx].rejected += 1;
        }
    }

    fn ruleAttemptIndex(
        self: *SearchCounters,
        rule_name: []const u8,
    ) ?usize {
        for (
            self.rule_attempt_diagnostics[0..self.rule_attempt_diagnostics_len],
            0..,
        ) |diagnostic, idx| {
            if (std.mem.eql(u8, diagnostic.rule_name.slice(), rule_name)) return idx;
        }
        if (self.rule_attempt_diagnostics_len >= max_search_diagnostics) {
            return null;
        }
        const idx = self.rule_attempt_diagnostics_len;
        self.rule_attempt_diagnostics[idx] = .{};
        self.rule_attempt_diagnostics[idx].rule_name.set(rule_name);
        self.rule_attempt_diagnostics_len += 1;
        return idx;
    }
};

pub const ApplyOptions = struct {
    max_results: ?usize = null,
    counters: ?*SearchCounters = null,
    use_rule_index: bool = true,
};

pub const ExactCandidate = struct {
    allocator: std.mem.Allocator,
    rule_id: u32,
    rule_name: []const u8,
    declaration_order: usize,
    refs: []const ProofScript.Ref,
    application: RuleApplication,
    reference_rank: usize,
    /// True when `application.arg_bindings` (and each formula text) were
    /// allocated with `allocator` by the open-target path. Derived
    /// recipes' bindings live in the derived pool's arena instead and must
    /// not be freed here.
    owns_arg_bindings: bool = false,

    pub fn deinit(self: *ExactCandidate) void {
        if (self.owns_arg_bindings) {
            for (self.application.arg_bindings) |binding| {
                self.allocator.free(binding.formula.text);
            }
            self.allocator.free(self.application.arg_bindings);
        }
        self.allocator.free(self.refs);
        self.* = undefined;
    }
};

pub const ExactResults = struct {
    allocator: std.mem.Allocator,
    candidates: []ExactCandidate,

    pub fn deinit(self: *ExactResults) void {
        for (self.candidates) |*candidate| {
            candidate.deinit();
        }
        self.allocator.free(self.candidates);
        self.* = undefined;
    }
};

/// A generated sub-proof returned by the recursive generation hook. The
/// application is ordinary proof syntax to splice into a hypothesis slot. The
/// conclusion is the concrete expression accepted for that child proof,
/// translated into the `target_theorem` interner passed to the hook.
pub const GeneratedProof = struct {
    application: RuleApplication,
    /// The conclusion the open-target path commits to. Usually the child
    /// proof's own accepted conclusion — but the member-wise ACUI read-back
    /// pass RELABELS it to the materialized open target (an ACUI
    /// reorder/reassociation variant of what `application` literally proves);
    /// the recompile validates the spliced assembly and inserts the ACUI
    /// bridge. Do not assume this equals the child's checked-line expression.
    conclusion: ExprId,
};

/// Per-slot generation hook. When set, the `backward/backtrack.zig` backtracker
/// may ask it to synthesize a sub-proof for a hypothesis slot whose binders are
/// already pinned (by the conclusion or by sibling refs) but which no pool ref
/// closes. The hook returns a `GeneratedProof`; the application is spliced into
/// the slot and the whole assembly is still validated through `tryCandidate`.
/// `null` (the default) means pool-refs-only — the `exact?` path is unchanged.
///
/// `target` is the concrete hypothesis expression in `target_theorem`'s interner
/// (the backtracker's working clone). The hook may re-intern it into its own
/// stable interner before solving, but translates the returned conclusion back.
pub const GenerationHook = struct {
    ctx: *anyopaque,
    /// `eager_step` is true when the applying rule is `@auto eager`: the
    /// application is a "don't-care" decomposition, so the driver solves the
    /// subgoal at the parent's remaining depth instead of one level below
    /// (the eager depth exemption — nodes/fuel/global ticks still charge).
    solveFn: *const fn (
        ctx: *anyopaque,
        target: ExprId,
        target_theorem: *TheoremContext,
        eager_step: bool,
    ) anyerror!?GeneratedProof,
    /// Open-target solver. `target` is a *structured open* hypothesis
    /// expression in `target_theorem` whose unsolved leaves are existential
    /// metas registered in `store` (a branch-local store owned by the
    /// caller). The hook finds a child proof whose concrete conclusion
    /// matches the target structurally, assigns the metas in `store` (they
    /// persist in the branch; the caller rolls them back at its backtrack
    /// site), and returns the proof with its concrete conclusion translated
    /// into `target_theorem`. Null (the default) disables open backward
    /// generation entirely — `exact?`/`apply?` never set it.
    solveOpenFn: ?*const fn (
        ctx: *anyopaque,
        target: ExprId,
        target_theorem: *TheoremContext,
        store: *MetaStore,
    ) anyerror!?GeneratedProof = null,
    /// When false, the backtracker never attempts a speculative ACUI context
    /// split for an open hypothesis context binder (see `backward/backtrack.zig`
    /// `trySplitGenerate`). The driver runs a non-splitting generation pass first
    /// and only flips this on for a second pass if the first found nothing, so
    /// goals provable without splitting never pay split cost.
    allow_split: bool = true,

    /// When true, an open witness slot whose existential meta has no concrete
    /// member or coupled-member anchor may *invent* a witness by grounding the
    /// meta to a reused `@vars`-pool dummy (`backward/backtrack.zig` `tryVarPoolWitnesses`).
    /// This is the only place search picks an underdetermined witness rather
    /// than forcing one, so it is gated to a final phase-3 generation pass run
    /// with fresh fuel only on a clean miss — by construction it can only add
    /// found-ness, never displace an anchored proof found in an earlier phase.
    /// `exact?`/`apply?` never set it.
    allow_invent_witness: bool = false,

    /// When true, a speculative ACUI split for an *idempotent* combiner may also
    /// retain a member already claimed by a fixed principal summand in the open
    /// rest binder — the non-minimal complement `g , g = g` allows (see
    /// `split.buildEnumerator`). Broadens every additive split node, so it
    /// is gated to a final phase run with fresh fuel only on a clean miss
    /// (mirrors `allow_invent_witness`): theories whose proofs use the minimal
    /// complement never pay the cost. `exact?`/`apply?` never set it.
    allow_retain_principal: bool = false,

    /// When true, *any* backward candidate (not only `@auto backward` rules)
    /// may open a binder the goal does not pin as an existential meta, provided
    /// the child search closes that hypothesis with a rule whose conclusion
    /// *pins* the meta (the non-`@auto` branch of `emitOpenTarget`, which is
    /// child-search-first and never invents a witness). This is the constrained
    /// backward modus-ponens path: `ax_mp`'s cut `a` is determined by the major
    /// premise's proving rule (e.g. a congruence axiom), never propagated or
    /// guessed. Broadens every implication-shaped goal, so — like
    /// `allow_invent_witness`/`allow_retain_principal` — it is gated to a final
    /// phase run with fresh fuel only on a clean miss; proofs found by the
    /// ordinary phases never pay the cost. `exact?`/`apply?` never set it.
    allow_constrained_mp: bool = false,

    /// When false, the backtracker ignores the `@auto eager` set-commit cut:
    /// the eager band is still tried first and its applications stay exempt
    /// from `max_depth`, but after the band is exhausted the remaining
    /// candidate bands are tried as usual. The driver honors the cut in every
    /// ladder phase and flips this off only for a final clean-miss retry, so
    /// a mis-annotated (non-invertible) eager rule costs miss-side latency,
    /// never proofs. Irrelevant without eager rules (the cut never arms).
    honor_eager_cut: bool = true,

    /// Shared global counter for stable `meta_id`s (see
    /// `MetaStore.meta_id_counter`). The generation driver owns the counter and
    /// points every open slot's store at it, so a witness meta keeps one
    /// identity across the open-target recursion's interner clones — the
    /// carry-to-leaf channel. Null disables it (legacy per-slot behavior).
    meta_id_counter: ?*u64 = null,

    pub fn solve(
        self: *const GenerationHook,
        target: ExprId,
        target_theorem: *TheoremContext,
        eager_step: bool,
    ) anyerror!?GeneratedProof {
        return self.solveFn(self.ctx, target, target_theorem, eager_step);
    }

    pub fn solveOpen(
        self: *const GenerationHook,
        target: ExprId,
        target_theorem: *TheoremContext,
        store: *MetaStore,
    ) anyerror!?GeneratedProof {
        const solve_open = self.solveOpenFn orelse return null;
        return solve_open(self.ctx, target, target_theorem, store);
    }
};

/// Global expensive-op budget for recursive `auto?` search. It counts
/// `tryCandidate` invocations — the measured cost center (strict-replay plus the
/// def/ACUI/structural fallback cascade) — and, unlike the per-depth node
/// counter, is **not** reset across iterative-deepening depths. So it bounds the
/// *total* validation/cascade work for the "never lock up the machine" guarantee
/// and, because the cascade is the arena-heavy engine, bounds memory too. It is a
/// pure safety floor, not a per-candidate doomed-detector: the recon measurement
/// showed cascade success and failure costs overlap, so a per-candidate cap
/// cannot separate winnable from doomed. Plain
/// `exact?`/`apply?` leave `ExactOptions.fuel` null and are unbounded by it.
pub const Fuel = struct {
    remaining: usize,
    /// Whole-call cost-weighted budget shared by every phase's fresh `Fuel`
    /// (see `GlobalBudget`). Null for plain `exact?`/`apply?` and for
    /// generation with no per-call cap configured.
    global: ?*GlobalBudget = null,

    /// Spend one unit. Returns `error.SearchBudgetExhausted` when empty — a
    /// distinct signal the caller separates from an ordinary no-result miss.
    pub fn spend(self: *Fuel) error{SearchBudgetExhausted}!void {
        if (self.global) |budget| try budget.spendCandidate();
        if (self.remaining == 0) return error.SearchBudgetExhausted;
        self.remaining -= 1;
    }
};

/// Cost-weighted budget for one whole `auto?` generation call, spanning all
/// retry phases (unlike `Fuel`, which each phase resets). The cost unit is the
/// interner work tick (`expr.zig` `work_ticks`): one per intern attempt,
/// everywhere on the thread. Unlike the per-phase `tryCandidate` count, tick
/// consumption tracks how *expensive* each candidate's validation cascade
/// actually was (cheap syntactic rejects vs. the full def/ACUI/normalization
/// fallback differ ~100x), so a tick ceiling bounds wall-clock latency far
/// more tightly than a candidate-count ceiling can. Deterministic: tick counts
/// depend only on the operations performed, never on time or machine.
///
/// Checked at candidate granularity (the `Fuel.spend` sites plus the
/// generation node entries): a candidate already being validated always runs
/// to completion, so exhaustion can only truncate the un-tried tail — exactly
/// the failure mode per-phase fuel exhaustion already has, reported the same
/// way (`error.SearchBudgetExhausted`).
/// Relative unit costs of the tick populations (see `expr.zig`) plus a fixed
/// per-candidate charge (each `Fuel.spend` — a `tryCandidate` — carries fixed
/// overhead: theorem/vars clones, session setup/hash — that no per-node tick
/// sees). Calibrated on the full depth corpus by regressing per-call wall
/// time on the four counts; units are ≈nanoseconds of calibrated wall, so a
/// budget limit reads as "estimated ns of search work" (4e9 ≈ 4s). The counts
/// themselves are machine-independent, so capped behavior is deterministic
/// even though the ns calibration is machine-specific.
pub const intern_tick_weight: u64 = 600;
pub const sym_tick_weight: u64 = 190;
pub const walk_tick_weight: u64 = 110;
pub const candidate_weight: u64 = 100_000;

/// The budget's cost unit: weighted ticks.
pub fn weightedTicks(
    intern_ticks: u64,
    sym_ticks: u64,
    walk_ticks: u64,
    candidates: u64,
) u64 {
    return intern_ticks *% intern_tick_weight +%
        sym_ticks *% sym_tick_weight +%
        walk_ticks *% walk_tick_weight +%
        candidates *% candidate_weight;
}

pub const GlobalBudget = struct {
    /// Weighted-tick ceiling for the whole call.
    limit: u64,
    /// `expr.work_ticks*` snapshots at driver entry.
    start_intern: u64,
    start_sym: u64,
    start_walk: u64,
    /// Candidates spent so far (counted here, not threadlocally: `Fuel.spend`
    /// reports each one via `spendCandidate`).
    candidates: u64 = 0,
    /// Set once exhausted; observability for the driver/bench.
    exhausted: bool = false,

    pub fn init(limit: u64) GlobalBudget {
        return .{
            .limit = limit,
            .start_intern = expr_mod.work_ticks,
            .start_sym = expr_mod.work_ticks_sym,
            .start_walk = expr_mod.work_ticks_walk,
        };
    }

    pub fn spent(self: *const GlobalBudget) u64 {
        return weightedTicks(
            expr_mod.work_ticks -% self.start_intern,
            expr_mod.work_ticks_sym -% self.start_sym,
            expr_mod.work_ticks_walk -% self.start_walk,
            self.candidates,
        );
    }

    pub fn check(self: *GlobalBudget) error{SearchBudgetExhausted}!void {
        if (self.spent() > self.limit) {
            self.exhausted = true;
            return error.SearchBudgetExhausted;
        }
    }

    pub fn spendCandidate(self: *GlobalBudget) error{SearchBudgetExhausted}!void {
        self.candidates += 1;
        try self.check();
    }
};

pub const ExactOptions = struct {
    max_results: ?usize = null,
    counters: ?*SearchCounters = null,
    generator: ?*const GenerationHook = null,
    /// Global recursive-search budget; null for non-generating `exact?`/`apply?`.
    fuel: ?*Fuel = null,
    /// Derived-ref pool from forward saturation. Only the `auto?`
    /// generation driver ever sets this; plain `exact?`/`apply?` leave it null
    /// and never see derived refs.
    derived: ?*DerivedPool = null,
    /// Set only by the generation driver (`hookSolveOpen`/`solveProof`) for
    /// its internal child searches. When set, candidate enumeration stops as
    /// soon as `max_results` results exist: an internal child's caller keeps
    /// at most that many, so exhausting the remaining apply candidates only
    /// burns budget on results the sort-and-truncate would discard anyway.
    /// The child keeps the first `max_results` results in enumeration order
    /// (split-last, witness-class, then seed order) rather than the best by
    /// declaration order — the price of not exploring every speculative
    /// subtree at every node (the tait `rex` contraction cascade made that
    /// exhaustiveness exponential). Top-level searches (line suggestions,
    /// inline slots) never set this: their ranked, user-visible result lists
    /// stay exhaustive.
    internal_open_child: bool = false,
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
    /// join that produced this fact (see `MetaAssignment`). Applied transiently
    /// to the pool store before this recipe is resolved at materialize time.
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
/// the holes (inside an open universal-use window), materializes the concrete
/// recipe, then rolls the assignments back, so the same derived ref can be
/// selected twice in one proof at two different witnesses.
pub const DerivedPool = struct {
    arena: std.heap.ArenaAllocator,
    store: MetaStore,
    refs: []const DerivedRef = &.{},
    /// Clipper-backed shape index over `refs` (universal-meta leaves shape to
    /// covering wildcards, so lookups over-approximate and never miss a
    /// matching derived ref). Built by the generation driver after
    /// saturation; null means callers fall back to a linear scan.
    index: ?@import("./ref_index.zig").Index = null,
    /// Memoized per-(rule, hyp) slot-candidate lists from `index`, queried
    /// with all binders unbound (a superset of every dynamically-pinned
    /// lookup, so reuse across goals and binding states is sound). Keyed by
    /// `rule_id << 32 | hyp_index`; a null value records a failed lookup
    /// (fall back to scanning all refs). Slices live in `arena`.
    slot_cache: std.AutoHashMapUnmanaged(u64, ?[]const usize) = .empty,
    /// True when the pool carries `@auto trigger` seeds (built by the
    /// phase-6 seeding retry; see `trigger.zig`). Gates the seed-aware slot
    /// cost in `plan.buildHypPlans`: only seeded pools may promote a
    /// pool-empty slot from generate-only cost to ref-like cost, so every
    /// pre-phase-6 search plans exactly as before.
    has_seeds: bool = false,
    /// Saturation layers actually run (a layer that derives nothing ends the
    /// loop early — a clean fixpoint).
    layers_run: usize = 0,
    /// True when saturation stopped at a budget (layers while the frontier
    /// was still productive, facts, rule attempts, or match tuples) rather
    /// than reaching a fixpoint. Distinct from a clean no-result: an absent
    /// derived fact is inconclusive when this is set.
    budget_exhausted: bool = false,

    pub fn deinit(self: *DerivedPool) void {
        self.slot_cache.deinit(self.arena.child_allocator);
        if (self.index) |*index| index.deinit();
        self.store.deinit();
        self.arena.deinit();
        self.* = undefined;
    }
};

pub const SourceSuggestion = struct {
    title: []const u8,
    replacement: []const u8,
    replace_span: Span,
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
    /// A budget (per-call global budget, recursive fuel floor, or forward-
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
    /// `target_span` is set (a placeholder was actually searched); the early
    /// no-placeholder returns leave the default.
    status: SearchStatus = .miss,

    pub fn deinit(self: *SourceSuggestions) void {
        for (self.items) |item| {
            self.allocator.free(item.title);
            self.allocator.free(item.replacement);
        }
        self.allocator.free(self.items);
        self.* = undefined;
    }
};

/// Controls bounded recursive generation (`auto?`). Generation only
/// runs when the `auto?` keyword is under the cursor AND `enabled` is set by the
/// caller (the permit). The bench and `exact?`/`apply?` paths never enable it,
/// so they never pay generation cost.
pub const GenerateOptions = struct {
    enabled: bool = false,
    /// Maximum recursion depth, explored via iterative deepening (depth 1, then
    /// 2, ... up to this), stopping at the SHALLOWEST depth that yields a proof
    /// (generate.zig:`runIterativeDeepening`) — so raising this never costs a
    /// shallow solution, it only lets a deeper one be found. A finite cap (not
    /// unbounded) keeps the no-result case bounded: a goal with no proof runs
    /// every depth 1..max before giving up, so an unbounded limit would burn the
    /// whole `fuel` floor on every miss.
    max_depth: usize = 6,
    /// Per-depth budget of *distinct* generated-node solves (skips deduplicated
    /// by `generate.zig`'s within-pass path guard + failure memo cost nothing),
    /// reset at each iterative-deepening depth. The cheap *secondary* guard; the
    /// load-bearing bound is `fuel` (global, expensive-op-counted, not reset per
    /// depth). Sized so the deepest additive_fol proofs regenerate fully from an
    /// empty pool: the two-branch `*_dist_*` proofs touch ~76 distinct
    /// sub-targets, but `forall_mono` (whose double-`lall` eigenvariable
    /// meta-coupling widens the search relative to its existential dual) needs
    /// ~170, and `drinker` (the underdetermined `@vars`-pool witness case) needs
    /// the full 256 to reach its forced witness — at 192 it stalls at frontier
    /// 1/5, at 256 it regenerates fully. Raising it never changes a found proof
    /// (iterative deepening stops at the shallowest); it only lets doomed
    /// searches explore further before giving up, so it is kept as tight as
    /// full coverage allows. The cost is bounded doomed-search latency, since
    /// real proofs solve shallow.
    max_nodes: usize = 256,
    /// Global `tryCandidate` budget for the whole recursive search, NOT reset per
    /// depth. The safety floor that guarantees termination/bounded memory; sized
    /// generously so ordinary proofs never hit it while pathological goals do.
    /// Lowered in tests to assert clean budget-exhausted behaviour.
    fuel: usize = 4096,
    /// Cap on generated top-level suggestions. Set by the dispatch to the number
    /// of result slots still free after direct `exact?` suggestions.
    max_results: ?usize = null,
    /// Fuel for the constrained-backward-MP retry (phase 5). It opens every
    /// implication-shaped goal to `ax_mp`-style backward search, so on a deep
    /// miss it can explore far before failing; a tighter budget than the main
    /// `fuel` caps that doomed-miss latency while keeping the (shallow) real
    /// gains. Null means reuse `fuel`.
    phase5_fuel: ?usize = null,
    /// Forward-saturation bounds. Saturation only runs at all when
    /// the theory declares `@auto forward` rules.
    forward: ForwardOptions = .{},
    /// Enable the search-reuse memos (default on): the reject-verdict memo
    /// (skip re-validating an assembly that already rejected this search) and
    /// the re-pin conclusion-plausibility prune. Both are completeness-neutral
    /// (proven byte-identical breadth + depth TOTAL); the flag exists only so
    /// the bench can A/B them. Driver-owned, spanning all retry phases.
    search_memo: bool = true,
    /// Lever E: deep-unfold ACUI member prune. When a candidate's fully-bound
    /// required context members provably diverge from every goal member after
    /// COMPLETE (to-fixpoint) def-unfolding, reject before `tryCandidate`.
    /// Targets church's `ax`/membership reject-flood (choose_eq 42.5s→1.9s);
    /// completeness-neutral (breadth byte-identical + depth TOTAL preserved).
    /// Default on; the bench A/Bs it via `--no-deep-member-prune`.
    deep_member_prune: bool = true,
    /// Content-keyed query-shape cache (Lever M-content): memoize the
    /// query-side template `ShapeSet` per session, keyed by a structural
    /// serialization of everything the shape builder reads (sound by
    /// construction — see `ref_index.ShapeCache`). Default on; the bench A/Bs
    /// it via `--no-shape-cache`.
    shape_cache: bool = true,
    /// Persist sub-solve failure verdicts across the retry ladder's
    /// (depth, phase) cells instead of clearing them per cell. Sound because
    /// a genuinely-exhaustive failure at (target, depth d, phase p) is a
    /// pure semantic fact — "no proof of gen-depth ≤ d under phase-p
    /// capabilities and this pool" — the phase capability flags are
    /// cumulative and purely additive, and depth-0 solves carry no hook at
    /// all (so any recorded failure covers depth-0 re-solves at every
    /// phase). Corpus-validated by shadow instrumentation: zero
    /// contradicted verdicts across ~550k would-skip re-solves; ~17-21% of
    /// generation ticks were being spent re-deriving already-known
    /// failures. Open-target verdicts persist only when the child
    /// enumeration was NOT truncated by `open_child_max_results` (a
    /// truncated fail is "the first N candidates didn't match back", which
    /// `concrete_ok` growth between cells can invalidate — observed on
    /// euclid dvd_add). Default on; the bench A/Bs it via
    /// `--no-persist-negative`.
    persist_negative: bool = true,
    /// Cost-weighted per-call latency cap: total weighted work ticks one
    /// `auto?` generation call may consume across ALL retry phases (see
    /// `GlobalBudget`; units ≈ ns of calibrated wall, so 6.3e9 ≈ 6s —
    /// though with `persist_negative` the observed wall per tick on
    /// miss-heavy workloads is well below the calibration).
    /// Exhaustion truncates the un-tried candidate tail exactly like
    /// per-phase fuel exhaustion, and the tick counts are deterministic, so
    /// capped results are machine-independent. Default sized 1.15x above the
    /// most expensive FOUND search in the depth corpus (surj_wit_maps k=1 at
    /// 5.48e9 after `persist_negative` freed per-phase fuel to explore more
    /// distinct candidates per cell — the memo skips spend no fuel; it was
    /// 3.34e9 after the solveProof interner scope, 2.91e9 after the
    /// pure-representative memo, 4.33e9 pre-memo), so every known proof
    /// clears it while doomed misses stop near the found ceiling: zero
    /// frontier loss. The wall cost of the higher tick cap is offset by
    /// persistence cutting wall-per-tick on miss-heavy workloads (fail-max
    /// dropped despite the raise). Null disables the cap.
    global_budget: ?u64 = 6_300_000_000,
};

pub const SourceSuggestionOptions = struct {
    max_results: usize = 5,
    /// Treat the ordinary rule application under the requested source offset
    /// as an `apply?` target. This lets editor features reuse source search
    /// without rewriting the proof document. The default still requires an
    /// explicit search-placeholder rule name.
    apply_at_offset: bool = false,
    /// Optional tighter cap for the single-proof modes (`exact?`/`auto?`), which
    /// want one best result, leaving `apply?` (a list of candidate rules) on the
    /// full `max_results`. When set, it also lets `exact?` short-circuit
    /// recursive generation once it has enough proofs. `null` = use `max_results`
    /// for every mode (the bench does this to keep generation hotspots visible).
    exact_result_limit: ?usize = null,
    counters: ?*SearchCounters = null,
    generate: GenerateOptions = .{},
};
