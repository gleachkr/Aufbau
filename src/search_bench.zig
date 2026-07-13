const std = @import("std");
const mm0 = @import("mm0");

const Search = mm0.CompilerSupport.Search;
const ProofScript = mm0.ProofScript;

const Scenario = struct {
    name: []const u8,
    mm0_path: []const u8,
    proof_path: []const u8,
    marker: []const u8,
    expected_replacement: []const u8,
    max_results: usize = 5,
    /// Mirrors the LSP/editor single-proof cap. `null` = uncapped (keeps all
    /// generation hotspots visible); the LSP path uses `1`.
    exact_result_limit: ?usize = null,
    generate: Search.GenerateOptions = .{},
    /// When false, the scenario is a latency probe with no required
    /// replacement (e.g. a hard `auto?` goal that exercises full iterative
    /// deepening).
    expect_result: bool = true,
    /// When set, assert the exact number of suggestions. Use `0` for
    /// deliberately unsupported probes so unexpected new suggestions fail the
    /// bench until the scenario is intentionally reclassified.
    expected_suggestion_count: ?usize = null,
    /// When set, assert the forward-saturation exhaustion flag. Guards the
    /// adversarial-saturation probes (META_STRESS theory #5): a commutativity /
    /// confluence loop must reach a fixpoint (`false`); a genuinely unbounded
    /// mutual-regeneration loop must stop on the budget (`true`). A dedupe-key
    /// regression flips this flag, so it is a tighter guard than the no-result
    /// check alone.
    expect_saturation_exhausted: ?bool = null,
    /// When set, assert the exact derived-ref count produced by forward
    /// saturation. Pins the dedupe behavior (e.g. confluence collapsing two
    /// recipes to one surface fact).
    expect_derived_refs: ?usize = null,
};

const BenchOptions = struct {
    compact: bool = false,
    /// When set, only scenarios whose name contains this substring are run.
    /// In frontier mode, filters theorem (block) names instead.
    filter: ?[]const u8 = null,
    /// Frontier analysis mode (META_STRESS.md workstream 1). When set, the
    /// scenario bench is skipped and the frontier runs over the corpus.
    frontier: ?FrontierMode = null,
    /// Extra/override frontier fixture pairs from `--files=MM0:AUF`.
    files: []const FixturePair = &.{},
    /// Search marker spliced into ablated lines (`auto?` by default).
    marker: []const u8 = "auto?",
    /// `max_depth` for frontier `auto?` generation.
    max_depth: usize = 6,
    /// Optional overrides for the generation budget (diagnostic; 0 = use the
    /// `GenerateOptions` defaults).
    gen_nodes: usize = 0,
    gen_fuel: usize = 0,
    /// Override for the constrained-backward-MP phase-5 fuel (0 = reuse gen_fuel).
    phase5_fuel: usize = 0,
    /// Cost-weighted per-call cap in weighted work ticks. Null = keep the
    /// `GenerateOptions` default; 0 = disable the cap (uncapped calibration
    /// runs); N = override.
    global_budget: ?u64 = null,
    /// Optional overrides for the forward-saturation bounds (diagnostic; 0 =
    /// use the `ForwardOptions` defaults). Lets a depth-frontier run separate
    /// forward-saturation *incompleteness* from a *budget* floor.
    fwd_facts: usize = 0,
    fwd_layers: usize = 0,
    fwd_attempts: usize = 0,
    fwd_tuples: usize = 0,
    /// Print every frontier line result, not just misses/slow lines.
    verbose: bool = false,
    /// Breadth lines whose warm search exceeds this are flagged SLOW.
    slow_ms: u64 = 2,
    /// Print a key-counter line (tryCandidate calls, rejects, top rules by
    /// validation attempts) under each MISS/SLOW breadth row.
    counters: bool = false,
    /// Enable per-call-site live-byte attribution in the bench allocator
    /// (`addr2line`-able leak hunting). Heavy: distorts timing numbers.
    track_sites: bool = false,
    /// Nonzero: panic (with stack trace) once live bytes exceed this many
    /// MiB. Diagnostic for attributing transient memory peaks to their real
    /// call chain.
    alloc_trap_mib: u64 = 0,
    /// Exit nonzero if a breadth frontier run has any MISS or ERR. Used to
    /// wire a filtered breadth run into `zig build test` as a regression
    /// guard for matcher gaps the corpus has no other automated coverage of.
    require_no_miss: bool = false,
    /// A/B switch for the Driver-owned search-reuse memos (reject-verdict memo +
    /// re-pin prune), default on (matches production). `--no-search-memo` turns
    /// them off to measure their effect.
    search_memo: bool = true,
    /// Lever E: deep-unfold ACUI member prune (default on, matches production).
    /// `--no-deep-member-prune` turns it off to measure its effect.
    deep_member_prune: bool = true,
    /// `--no-persist-negative` turns off cross-cell persisted failure memos
    /// to measure their effect.
    persist_negative: bool = true,
    /// Content-keyed query-shape cache (Lever M-content); `--no-shape-cache`
    /// turns it off to measure its effect.
    shape_cache: bool = true,
    /// Discrimination/scaling sweep (META_STRESS.md theory #4). When set, the
    /// scenario/frontier benches are skipped and the sweep runs instead.
    sweep: ?SweepSpec = null,
};

/// Frontier analysis (see META_STRESS.md):
/// - `breadth`: per-line ablation — replace each proof line's application
///   with the search marker and ask whether search recovers it from the
///   preceding pool. Misses are matcher/witness gaps with a known-good
///   human answer attached.
/// - `depth`: suffix truncation — target each theorem's final line and
///   remove the k lines immediately preceding it, growing k until the proof
///   is no longer found. The max successful k is the theorem's frontier
///   depth (how much proof tail generation can rebuild).
const FrontierMode = enum { breadth, depth };

const FixturePair = struct {
    name: []const u8,
    mm0_path: []const u8,
    proof_path: []const u8,
};

/// Discrimination/scaling sweep (META_STRESS.md bespoke theory #4). Each family
/// synthesizes a distractor theory parametrized by N and isolates one
/// candidate-discrimination path; the goal is deliberately unprovable so the
/// full candidate set is always exhausted (a clean no-result scaling probe, like
/// `forward_stress`). See `runSweep`/`generateSweep`.
const SweepFamily = enum {
    /// N rules with DISTINCT conclusion heads (plus one real `Goal` rule).
    /// `rule_index.lookupGoal` should filter all N → search time flat in N.
    head_distinct,
    /// N rules all concluding the goal head with distinct unprovable hyps. They
    /// share the goal's bucket, so each is a candidate that must be rejected →
    /// linear in N. Superlinear = a candidate-loop blowup.
    head_shared,
    /// One rule whose first hyp has a wildcard argument matching all N pool refs
    /// (`Inner C_i`) and a second hyp (`Tag a`) that no ref satisfies → every
    /// fanned-out ref is looked up then rejected → linear in N.
    ref_fanout,
};

const SweepSpec = struct {
    family: SweepFamily,
    points: []const usize,
};

/// The major real developments. Frontier runs are read-only analysis, so
/// pointing at shared `tests/proof_cases/` fixtures is fine here (unlike
/// scenario fixtures, which must be bench-local copies).
const default_frontier_corpus = [_]FixturePair{
    .{
        // search-only @auto-annotated copy of proof_cases/euclid (annotations
        // are search research; the general proof_cases fixture is left clean).
        .name = "euclid",
        .mm0_path = "tests/search_bench_cases/euclid_frontier.mm0",
        .proof_path = "tests/search_bench_cases/euclid_frontier.auf",
    },
    .{
        // search-only @auto-annotated copy (see euclid note above). Also
        // carries `@auto trigger` patterns on `ax` (phase-6 seeding): the
        // measured effect is exactly nd_exists_elim_const 4/6 -> FULL
        // (guarded in build.zig) at +2.4% miss-side wall; every other
        // theorem's frontier fraction is unchanged.
        .name = "zermelo",
        .mm0_path = "tests/search_bench_cases/zermelo_frontier.mm0",
        .proof_path = "tests/search_bench_cases/zermelo_frontier.auf",
    },
    .{
        // search-only @auto-annotated copy (see euclid note above): `@auto
        // forward` on MP + eqTR1/eqTR2 only. Measured (2026-07-13, task #120,
        // docs/design_notes/church_forward_enrollment.md): +6 frontier gains
        // / 0 losses (DISJ_CASES 1->2, OR_DEF 3->14 FULL, IMP_TRANS 2->3) at
        // +13% wall. The old "church does NOT respond to @auto" note only
        // swept forward eqmp/iff_mp + backward ded — the wrong rules; the
        // depth misses were missing forward MP joins. Do NOT enroll
        // trans/sym/reflt (equational closure squares the pool: 24 losses),
        // DISCH (CONJ_ASSOC 2->1), or thmR (CHOOSE 1->0).
        .name = "church",
        .mm0_path = "tests/search_bench_cases/church_frontier.mm0",
        .proof_path = "tests/search_bench_cases/church_frontier.auf",
    },
    .{
        // search-only @auto-annotated copy (see euclid note above).
        .name = "peano",
        .mm0_path = "tests/search_bench_cases/peano_frontier.mm0",
        .proof_path = "tests/search_bench_cases/peano_frontier.auf",
    },
    .{
        // search-only @auto-annotated copy (see euclid note above).
        .name = "martin_lof",
        .mm0_path = "tests/search_bench_cases/martin_lof_frontier.mm0",
        .proof_path = "tests/search_bench_cases/martin_lof_frontier.auf",
    },
    .{
        // search-only @auto copy. This Hilbert theory does NOT want the ND
        // recipe: backward intros (and_intro/all_intro/ex_intro) gave 0–2 FULL at
        // +43–71% wall AND stole budget that suppressed forward gains. Isolation
        // found `and_elim_l/r` FORWARD is the whole FULL win: 91→96 (+5) at +23%
        // wall. `mp`/`mpbi` FORWARD are kept too: 0 extra FULL but free partial
        // progress (mean frontier 1.21→1.28) at no wall cost. Forward elims only.
        .name = "zermelo_hilbert",
        .mm0_path = "tests/search_bench_cases/zermelo_hilbert_frontier.mm0",
        .proof_path = "tests/search_bench_cases/zermelo_hilbert_frontier.auf",
    },
};

const scenarios = [_]Scenario{
    .{
        .name = "simple exact zero-hypothesis axiom",
        .mm0_path = "tests/search_bench_cases/simple_exact.mm0",
        .proof_path = "tests/search_bench_cases/simple_exact.auf",
        .marker = "exact?",
        .expected_replacement = "p",
    },
    .{
        .name = "simple apply with unresolved hypotheses",
        .mm0_path = "tests/search_bench_cases/simple_apply.mm0",
        .proof_path = "tests/search_bench_cases/simple_apply.auf",
        .marker = "apply?",
        .expected_replacement = "mp [ref1, ref2]",
    },
    .{
        .name = "multi-hyp exact with many refs",
        .mm0_path = "tests/search_bench_cases/multi_ref_exact.mm0",
        .proof_path = "tests/search_bench_cases/multi_ref_exact.auf",
        .marker = "exact?",
        .expected_replacement = "use_three [l07, l13, l19]",
    },
    .{
        .name = "homogeneous nd-style ref pool",
        .mm0_path = "tests/search_bench_cases/homogeneous_ref_pool.mm0",
        .proof_path = "tests/search_bench_cases/homogeneous_ref_pool.auf",
        .marker = "exact?",
        .expected_replacement = "use_wrapped [l03, l08, l11]",
    },
    .{
        .name = "transparent definition-heavy exact",
        .mm0_path = "tests/search_bench_cases/transparent_defs.mm0",
        .proof_path = "tests/search_bench_cases/transparent_defs.auf",
        .marker = "exact?",
        .expected_replacement = "use_d3 [l1]",
    },
    .{
        .name = "view lookup with different raw head",
        .mm0_path = "tests/search_bench_cases/view_head_apply.mm0",
        .proof_path = "tests/search_bench_cases/view_head_apply.auf",
        .marker = "apply?",
        .expected_replacement = "ax_subst",
    },
    .{
        .name = "zermelo cb_bijection_surj_body exact?",
        .mm0_path = "tests/search_bench_cases/zermelo_cb_surj_body.mm0",
        .proof_path = "tests/search_bench_cases/zermelo_cb_surj_body.auf",
        .marker = "exact?",
        .expected_replacement = "cb_bijection_surj_body [#1, #2]",
    },
    .{
        .name = "peano ax_mp implication exact?",
        .mm0_path = "tests/search_bench_cases/peano.mm0",
        .proof_path = "tests/search_bench_cases/peano_ax_mp_implication.auf",
        .marker = "exact?",
        .expected_replacement = "ax_mp [l1, #1]",
    },
    .{
        .name = "peano successor congruence exact?",
        .mm0_path = "tests/search_bench_cases/peano.mm0",
        .proof_path = "tests/search_bench_cases/peano_successor_congruence_axmp.auf",
        .marker = "exact?",
        .expected_replacement = "ax_mp [l3, l2]",
    },
    .{
        .name = "peano multiplication transitive exact?",
        .mm0_path = "tests/search_bench_cases/peano.mm0",
        .proof_path = "tests/search_bench_cases/peano_mul_transitive_chain.auf",
        .marker = "exact?",
        .expected_replacement = "eq_trans3 [l14, l17, l20]",
    },
    .{
        .name = "peano distributivity transitive exact?",
        .mm0_path = "tests/search_bench_cases/peano.mm0",
        .proof_path = "tests/search_bench_cases/peano_distributivity_transitive.auf",
        .marker = "exact?",
        .expected_replacement = "eq_trans4 [l1, l2, l5, l8]",
    },
    .{
        .name = "euclid successor no fixed point exact?",
        .mm0_path = "tests/search_bench_cases/euclid.mm0",
        .proof_path = "tests/search_bench_cases/euclid_successor_no_fixed_point.auf",
        .marker = "exact?",
        .expected_replacement = "imp_elim [l4, l3]",
    },
    .{
        .name = "euclid final existential exact?",
        .mm0_path = "tests/search_bench_cases/euclid.mm0",
        .proof_path = "tests/search_bench_cases/euclid_final_existential.auf",
        .marker = "exact?",
        // l21 names the opened witness (`y`) differently from the `∃` binder, so
        // the substitution form `ex_elim_sub` is the rule that actually applies.
        .expected_replacement = "ex_elim_sub [l3, l21]",
    },
    .{
        .name = "euclid prime factor or-elim exact?",
        .mm0_path = "tests/search_bench_cases/euclid.mm0",
        .proof_path = "tests/search_bench_cases/euclid_prime_factor_or_elim.auf",
        .marker = "exact?",
        .expected_replacement = "or_elim [l7, l11, l42]",
    },
    .{
        .name = "euclid final generalization exact?",
        .mm0_path = "tests/search_bench_cases/euclid.mm0",
        .proof_path = "tests/search_bench_cases/euclid_final_generalization.auf",
        .marker = "exact?",
        // l22 proves the body naming the eigenvariable (`y`) differently from the
        // `∀` binder (`n`), so the substitution form `all_intro_sub` applies.
        .expected_replacement = "all_intro_sub [l22]",
    },
    .{
        .name = "church beta conversion exact?",
        .mm0_path = "tests/search_bench_cases/church.mm0",
        .proof_path = "tests/search_bench_cases/church_beta_conversion.auf",
        .marker = "exact?",
        .expected_replacement = "inst [l5, #2, l14]",
    },
    .{
        .name = "church and definition refl exact?",
        .mm0_path = "tests/search_bench_cases/church.mm0",
        .proof_path = "tests/search_bench_cases/church_and_definition_refl.auf",
        .marker = "exact?",
        .expected_replacement = "reflt [l14]",
    },
    .{
        .name = "church not definition trans exact?",
        .mm0_path = "tests/search_bench_cases/church.mm0",
        .proof_path = "tests/search_bench_cases/church_not_definition_trans.auf",
        .marker = "exact?",
        .expected_replacement = "DISCH [l1, l2, l5]",
    },
    .{
        .name = "zermelo function intro exact?",
        .mm0_path = "tests/search_bench_cases/zermelo_cb_surj_body.mm0",
        .proof_path = "tests/search_bench_cases/zermelo_function_from_injections.auf",
        .marker = "exact?",
        .expected_replacement = "function_intro [l1, l2, l3]",
    },
    .{
        .name = "zermelo image preimage exact?",
        .mm0_path = "tests/search_bench_cases/zermelo_cb_surj_body.mm0",
        .proof_path = "tests/search_bench_cases/zermelo_preimage_from_image.auf",
        .marker = "exact?",
        .expected_replacement = "ex_elim [l1, l8]",
    },
    .{
        .name = "zermelo cb surjection exact?",
        .mm0_path = "tests/search_bench_cases/zermelo_cb_surj_body.mm0",
        .proof_path = "tests/search_bench_cases/zermelo_cb_surjection_body.auf",
        .marker = "exact?",
        .expected_replacement = "cb_bijection_surj_body [#1, #2]",
    },
    .{
        .name = "zermelo hilbert cantor body exact?",
        .mm0_path = "tests/search_bench_cases/zermelo_hilbert.mm0",
        .proof_path = "tests/search_bench_cases/zermelo_hilbert_cantor_body.auf",
        .marker = "exact?",
        .expected_replacement = "cantor_witness [#1, l3, l4]",
    },
    .{
        .name = "auto depth-2 chain auto?",
        .mm0_path = "tests/search_bench_cases/auto_depth2.mm0",
        .proof_path = "tests/search_bench_cases/auto_depth2.auf",
        .marker = "auto?",
        .expected_replacement = "qr [pq [p []]]",
        .generate = .{ .enabled = true },
    },
    .{
        // Depth-3 concrete chain (toy): exercises iterative deepening to depth 3
        // and deep generated nesting. Deterministic deep-generation latency gate.
        .name = "auto depth-3 chain auto?",
        .mm0_path = "tests/search_bench_cases/auto_depth3.mm0",
        .proof_path = "tests/search_bench_cases/auto_depth3.auf",
        .marker = "auto?",
        .expected_replacement = "rs [qr [pq [p []]]]",
        .generate = .{ .enabled = true },
    },
    .{
        // Two-hyp rule with a hyp-only binder: one hyp is filled from the pool
        // (pinning the binder), the other has no ref and must be generated. The
        // generate-only slot has zero initial refs, so a naive most-constrained-
        // first order visits it before the pinning sibling and fails to pin its
        // binder. Gates the generator-aware slot ordering.
        .name = "auto two-hyp binder pinning auto?",
        .mm0_path = "tests/search_bench_cases/auto_two_hyp_pin.mm0",
        .proof_path = "tests/search_bench_cases/auto_two_hyp_pin.auf",
        .marker = "auto?",
        .expected_replacement = "r [l1, nk []]",
        .generate = .{ .enabled = true },
    },
    .{
        // Conclusion binder hidden behind a first-order def fold. The goal
        // `W K` is `N K` after one unfold; the rule conclusion is `N a`, so `a`
        // is pinnable only if the conclusion-side seed unfolds the goal's
        // transparent def. Once `a := K` is pinned the hyp `P a` is concrete and
        // generated via `pk`. Gates conclusion-side def-unfold pinning for the
        // generator (Lever C, non-view first-order case).
        .name = "auto def-conclusion binder pinning auto?",
        .mm0_path = "tests/search_bench_cases/auto_def_concl_pin.mm0",
        .proof_path = "tests/search_bench_cases/auto_def_concl_pin.auf",
        .marker = "auto?",
        .expected_replacement = "r [pk []]",
        .generate = .{ .enabled = true },
    },
    .{
        // Zermelo ND tautology, depth-2 chain: `imp_intro [ax]` for `p -> p`.
        .name = "zermelo nd_imp_id auto?",
        .mm0_path = "tests/proof_cases/zermelo.mm0",
        .proof_path = "tests/search_bench_cases/nd_imp_id.auf",
        .marker = "auto?",
        .expected_replacement = "imp_intro [ax []]",
        .generate = .{ .enabled = true },
    },
    .{
        // Zermelo ND tautology, depth-3 chain: `imp_intro [bot_elim [ax]]`.
        .name = "zermelo nd_explosion auto?",
        .mm0_path = "tests/proof_cases/zermelo.mm0",
        .proof_path = "tests/search_bench_cases/nd_explosion.auf",
        .marker = "auto?",
        .expected_replacement = "imp_intro [bot_elim [ax []]]",
        .generate = .{ .enabled = true },
    },
    .{
        // Zermelo ND tautology (now SUPPORTED via phase-5 constrained backward
        // MP). Needs ACUI context *splitting* (`and_intro`'s `G,H ⊢ p∧q`
        // against a single goal context, collapsing `G=H={p∧q}` by idempotency)
        // from an EMPTY pool under an `imp_intro`. Was an unfound probe until
        // constrained backward MP (256e05d) let the split's minors generate.
        // Same proof as `nd_and_comm_split` but with no pooled `l1`.
        .name = "zermelo nd_and_comm auto?",
        .mm0_path = "tests/proof_cases/zermelo.mm0",
        .proof_path = "tests/search_bench_cases/nd_and_comm.auf",
        .marker = "auto?",
        .expected_replacement = "imp_intro [and_intro " ++
            "(G := $ p ∧ q $, H := $ p ∧ q $, p := $ q $, q := $ p $) " ++
            "[and_elim_r (p := $ p $) [ax []], and_elim_l (q := $ q $) [ax []]]]",
        .generate = .{ .enabled = true },
    },
    .{
        // Zermelo ND tautology over equality (probe): deep chain with eq rules.
        .name = "zermelo nd_eq_symm auto?",
        .mm0_path = "tests/proof_cases/zermelo.mm0",
        .proof_path = "tests/search_bench_cases/nd_eq_symm.auf",
        .marker = "auto?",
        .expected_replacement = "",
        .generate = .{ .enabled = true },
        .expect_result = false,
        .expected_suggestion_count = 0,
    },
    .{
        // GENUINE context-split win: `and_intro` (`G,H ⊢ q∧p`) on the goal
        // `p∧q ⊢ q∧p` with only `l1: p∧q ⊢ p∧q` in the pool. Both context halves
        // `G`,`H` are open and must be guessed by splitting the goal context — here
        // a *contraction* split `G=H={p∧q}` (the single member used in both
        // branches). The minors are generated as `and_elim_r [l1]`/`and_elim_l
        // [l1]`; their dropped-conjunct binders are pinned by the pooled `l1`, so
        // no conclusion-only-binder gap, and no witness binder. Unsolvable without
        // speculative ACUI context splitting (search/backward/split.zig).
        .name = "zermelo nd_and_comm split auto?",
        .mm0_path = "tests/proof_cases/zermelo.mm0",
        .proof_path = "tests/search_bench_cases/nd_and_comm_split.auf",
        .marker = "auto?",
        .expected_replacement = "and_intro [and_elim_r [l1], and_elim_l [l1]]",
        .generate = .{ .enabled = true },
    },
    .{
        // DEEP split (full theorem, empty pool): two `imp_intro`s then an `ext`
        // context split (`G={A⊆B}`, `H={B⊆A}`) with `ax` minors.
        .name = "zermelo nd_ext_imp split auto?",
        .mm0_path = "tests/proof_cases/zermelo.mm0",
        .proof_path = "tests/search_bench_cases/nd_ext_imp.auf",
        .marker = "auto?",
        .expected_replacement = "imp_intro [imp_intro [ext [ax [], ax []]]]",
        .generate = .{ .enabled = true },
    },
    .{
        // DEEP split (full theorem, empty pool): two `imp_intro`s then a
        // `sep_intro` context split with a substitution wff and `ax` minors.
        .name = "zermelo nd_sep_intro_imp split auto?",
        .mm0_path = "tests/proof_cases/zermelo.mm0",
        .proof_path = "tests/search_bench_cases/nd_sep_intro_imp.auf",
        .marker = "auto?",
        .expected_replacement = "imp_intro [imp_intro [sep_intro [ax [], ax []]]]",
        .generate = .{ .enabled = true },
    },
    .{
        // Multiplicative `or_elim` (`G,H,K ⊢ r`) with a populated pool (l1/l2/l4
        // ax lines). Speculative ACUI context splitting (search/backward/split.zig)
        // grounds the major `G ⊢ p∨q` from l1, collapses the minor contexts
        // `H`,`K` to `emp`, and *generates* the minors `or_intro_r`/`or_intro_l`.
        // The assembled `or_elim` is validated via the context-holey inline hint
        // (`fillHoleyInlineHints` in `compiler/check.zig`): the sibling/ACUI-aware
        // probe pins `p,q,r` from `l1` and the goal, then renders the residual
        // open context binder as a placeholder, so the generated `or_intro_r`'s
        // conclusion-only disjunct gets pinned from the concrete wff `q∨p`.
        // See `docs/design_notes/nd_or_comm_validation_gap`.
        .name = "zermelo nd_or_comm auto? (split, validation gap)",
        .mm0_path = "tests/proof_cases/zermelo.mm0",
        .proof_path = "tests/search_bench_cases/nd_or_comm.auf",
        .marker = "auto?",
        .expected_replacement = "or_elim [l1, or_intro_r [l2], or_intro_l [l4]]",
        .generate = .{ .enabled = true },
    },
    .{
        // STAGE 5 flagship (ACUI member witness — SUPPORTED). Stage 4 builds
        // the recover-shaped `ex_intro` target `A ∈ A ⊢ ?t ∈ A`; no child
        // conclusion can solve `?t` structurally (`ax []` needs the witness
        // already solved to apply at all). Stage 5 enumerates the target's own
        // concrete ACUI context members as the finite witness domain: matching
        // the fragment `?t ∈ A` against the member `A ∈ A` assigns `?t := A`,
        // the concrete target is closed by `ax []`, and the witness renders as
        // an explicit binding. Was the "no result, Stage 5" probe before
        // member enumeration landed.
        .name = "zermelo nd_exists_intro_mem auto? (Stage 5 ACUI witness)",
        .mm0_path = "tests/search_bench_cases/zermelo_exists_intro_stage5.mm0",
        .proof_path = "tests/search_bench_cases/nd_exists_intro_mem_auto.auf",
        .marker = "auto?",
        // The witness `t` AND the `@recover` pattern binder `p` both render as
        // explicit bindings: the inline assembly is re-validated bottom-up and
        // the principal `∃ x p` can't be reconstructed from `t` alone.
        .expected_replacement = "imp_intro [ex_intro (t := $ A $, p := $ x e. A $) [ax []]]",
        .generate = .{ .enabled = true, .max_depth = 6 },
    },
    .{
        // STAGE 5 toy (repeated meta from one ACUI member). The recover
        // target is `A ∈ A ⊢ ?t ∈ ?t` — the same hash-consed meta leaf at two
        // positions — so the member match against `A ∈ A` must solve both
        // occurrences consistently (`?t := A`).
        .name = "stage5 repeated meta from member auto?",
        .mm0_path = "tests/search_bench_cases/zermelo_exists_intro_stage5.mm0",
        .proof_path = "tests/search_bench_cases/nd_exists_intro_self_auto.auf",
        .marker = "auto?",
        // Witness `t` plus the rendered `@recover` pattern binder `p` (the
        // repeated-meta body `?t ∈ ?t` → `x ∈ x`).
        .expected_replacement = "imp_intro [ex_intro (t := $ A $, p := $ x e. x $) [ax []]]",
        .generate = .{ .enabled = true, .max_depth = 6 },
    },
    .{
        // STAGE 5 negative control: the fragment `?t ∈ B` matches no member
        // of the context `A ∈ A`, so enumeration proposes nothing and the
        // search ends in a clean bounded no-result.
        .name = "stage5 no valid member auto? (no result)",
        .mm0_path = "tests/search_bench_cases/zermelo_exists_intro_stage5.mm0",
        .proof_path = "tests/search_bench_cases/nd_exists_intro_no_member_auto.auf",
        .marker = "auto?",
        .expected_replacement = "",
        .generate = .{ .enabled = true, .max_depth = 6 },
        .expect_result = false,
        .expected_suggestion_count = 0,
    },
    .{
        // STAGE 5 toy (ambiguous member choices, deterministic order).
        // Both context members in the tagged finite domain fill the repeated
        // fragment `?t ∈ ?t`. The open hint is too broad to return a concrete
        // child conclusion, so Stage 5 enumerates both concrete witnesses;
        // the suggestions are ranked in context-member order.
        .name = "stage5 ambiguous members auto? (deterministic order)",
        .mm0_path = "tests/search_bench_cases/zermelo_exists_intro_stage5.mm0",
        .proof_path = "tests/search_bench_cases/nd_exists_intro_ambiguous_auto.auf",
        .marker = "auto?",
        // Meta-solved witness `t` also renders the `@recover` pattern binder `p`
        // (the tagged finite domain + repeated-meta body `mem x x`).
        .expected_replacement = "ex_intro (t := $ A $, p := $ tag (A e. A , B e. B) (x e. x) $) [tag_member []]",
        .generate = .{ .enabled = true, .max_depth = 6 },
        .expected_suggestion_count = 2,
    },
    .{
        // STAGE 5 negative control (ACUI unit). The empty context is the
        // combiner's unit element, which is never a domain member, so the
        // open witness has no finite domain and the result stays clean.
        .name = "stage5 unit context auto? (no result)",
        .mm0_path = "tests/search_bench_cases/zermelo_exists_intro_stage5.mm0",
        .proof_path = "tests/search_bench_cases/nd_exists_intro_unit_auto.auf",
        .marker = "auto?",
        .expected_replacement = "",
        .generate = .{ .enabled = true, .max_depth = 6 },
        .expect_result = false,
        .expected_suggestion_count = 0,
    },
    .{
        // STAGE 5 real win (split + member witness — SUPPORTED). `union_intro`
        // (`G,H ⊢ x∈union A`, now `@auto backward`) with an empty pool: the
        // ACUI context split pins `G := x∈y`, the minor `G ⊢ x∈?y` defers the
        // hypothesis-only witness `y` as an existential meta, and Stage 5
        // member enumeration solves it from the split context's own member
        // (`x∈y` shows `?y := y`). This is the case where context splitting
        // and witness extraction interact; it was an open-witness no-result
        // probe before Stage 5.
        .name = "zermelo nd_union_intro_imp auto? (Stage 5 split + witness)",
        .mm0_path = "tests/proof_cases/zermelo.mm0",
        .proof_path = "tests/search_bench_cases/nd_union_intro_imp.auf",
        .marker = "auto?",
        .expected_replacement = "union_intro (y := $ y $) [ax [], ax []]",
        .generate = .{ .enabled = true },
    },
    .{
        // Multiplicative `ex_elim` with a non-trivial complement: the major
        // `G ⊢ ∃x p` grounds from l1 (`G = ∃x p`), leaving the minor context
        // `H = p→q` as the forced-but-still-enumerated complement; its subproof
        // `p→q, p ⊢ q` is generated via `imp_elim [l2, l3]`. Distinct from
        // nd_exists_elim_const (which keeps `l5` in the pool); here l4/l5 are
        // generated through a context split.
        .name = "zermelo nd_exists_elim_split auto?",
        .mm0_path = "tests/proof_cases/zermelo.mm0",
        .proof_path = "tests/search_bench_cases/nd_exists_elim_split.auf",
        .marker = "auto?",
        .expected_replacement = "imp_intro [imp_elim [l2, ex_elim [l1, l3]]]",
        .generate = .{ .enabled = true },
    },
    .{
        // Populated pool (l1-l5 refs) on a heavy theory: the goal is solved by a
        // depth-2, fully-pinned chain that now references the existing line `l5`
        // directly. (Before ACUI-unit normalization the innermost ACUI slot
        // carried a redundant `emp` so `l5` didn't match and generation
        // re-derived `ex_elim [l1, l4]`; normalizing the generated target lets
        // the ref match.) Real worst-case latency probe over a non-empty pool.
        .name = "zermelo nd_exists_elim_const auto?",
        .mm0_path = "tests/proof_cases/zermelo.mm0",
        .proof_path = "tests/search_bench_cases/nd_exists_elim_const.auf",
        .marker = "auto?",
        .expected_replacement = "imp_intro [imp_intro [l5]]",
        .generate = .{ .enabled = true },
    },
    // Feature-rich sites from later in real developments, run under `auto?`
    // (so generation's two-phase runs on top of direct search). Each gates on
    // the development's own proof, which the direct (phase-1) search still finds;
    // the value is measuring auto?'s overhead where it entangles with def
    // unfolding, @view/@recover, and ACUI contexts.
    .{
        // Def unfolding: church β-reduction via `inst`.
        .name = "auto church beta conversion auto?",
        .mm0_path = "tests/search_bench_cases/church.mm0",
        .proof_path = "tests/search_bench_cases/church_beta_conversion_auto.auf",
        .marker = "auto?",
        .expected_replacement = "inst [l5, #2, l14]",
        .generate = .{ .enabled = true },
    },
    .{
        // Def unfolding: church `≃` reflexivity recovered through a def.
        .name = "auto church and definition refl auto?",
        .mm0_path = "tests/search_bench_cases/church.mm0",
        .proof_path = "tests/search_bench_cases/church_and_definition_refl_auto.auf",
        .marker = "auto?",
        .expected_replacement = "reflt [l14]",
        .generate = .{ .enabled = true },
    },
    .{
        // Def unfolding + transport: church `not` definition via `DISCH`.
        .name = "auto church not definition trans auto?",
        .mm0_path = "tests/search_bench_cases/church.mm0",
        .proof_path = "tests/search_bench_cases/church_not_definition_trans_auto.auf",
        .marker = "auto?",
        .expected_replacement = "DISCH [l1, l2, l5]",
        .generate = .{ .enabled = true },
    },
    .{
        // @view / @recover: euclid universal generalization via `all_intro_sub`.
        .name = "auto euclid final generalization auto?",
        .mm0_path = "tests/search_bench_cases/euclid.mm0",
        .proof_path = "tests/search_bench_cases/euclid_final_generalization_auto.auf",
        .marker = "auto?",
        .expected_replacement = "all_intro_sub [l22]",
        .generate = .{ .enabled = true },
    },
    .{
        // ACUI context + existential elimination: zermelo image/preimage.
        .name = "auto zermelo image preimage auto?",
        .mm0_path = "tests/search_bench_cases/zermelo_cb_surj_body.mm0",
        .proof_path = "tests/search_bench_cases/zermelo_preimage_from_image_auto.auf",
        .marker = "auto?",
        .expected_replacement = "ex_elim [l1, l8]",
        .generate = .{ .enabled = true },
    },
    .{
        // The cb case that gave trouble before: cb_bijection surjection body.
        .name = "auto zermelo cb surjection auto?",
        .mm0_path = "tests/search_bench_cases/zermelo_cb_surj_body.mm0",
        .proof_path = "tests/search_bench_cases/zermelo_cb_surjection_body_auto.auf",
        .marker = "auto?",
        .expected_replacement = "cb_bijection_surj_body [#1, #2]",
        .generate = .{ .enabled = true },
    },
    // ============================================================
    // Depth-6 generation stress sites drawn from the full developments
    // (martin_lof, zermelo). These run the realistic rule environment
    // (the dev's whole prior rule set) under `auto?` with `max_depth = 6`,
    // so they exercise deep iterative deepening and where generation
    // entangles with type-theory motives, @view binders, and ACUI contexts.
    // ============================================================
    .{
        // martin_lof addition commutativity: rebuild the `id_trans` chain
        // step (l20) from a full sibling pool. The transitivity midpoint is
        // pinned by the sibling refs (l14, l19), so the binders are concrete
        // and the step is regenerable. Realistic large-mm0 generation gate.
        .name = "auto martin_lof add_comm id_trans auto?",
        .mm0_path = "tests/proof_cases/martin_lof.mm0",
        .proof_path = "tests/search_bench_cases/ml_add_comm_idtrans_auto.auf",
        .marker = "auto?",
        .expected_replacement = "id_trans_ty [l14, l19]",
        .generate = .{ .enabled = true, .max_depth = 6 },
    },
    .{
        // martin_lof add_comm capstone: `nat_ind_elim` whose induction motive
        // is not pinned by the conclusion (higher-order).
        .name = "auto martin_lof add_comm capstone auto? (no result)",
        .mm0_path = "tests/proof_cases/martin_lof.mm0",
        .proof_path = "tests/search_bench_cases/ml_add_comm_capstone_auto.auf",
        .marker = "auto?",
        .expected_replacement = "",
        .generate = .{ .enabled = true, .max_depth = 6 },
        .expect_result = false,
        .expected_suggestion_count = 2,
    },
    .{
        // martin_lof add_comm: rebuild the WHOLE tail of the `id_trans` DAG
        // (l14, l16, l17, l18, l19) from a trimmed pool, then close l20. A
        // multi-step concrete regeneration that drives iterative deepening
        // toward its depth-6 ceiling. Deep-rebuild latency probe.
        .name = "auto martin_lof add_comm id_trans deep auto?",
        .mm0_path = "tests/proof_cases/martin_lof.mm0",
        .proof_path = "tests/search_bench_cases/ml_add_comm_idtrans_deep_auto.auf",
        .marker = "auto?",
        .expected_replacement = "",
        .generate = .{ .enabled = true, .max_depth = 6 },
        .expect_result = false,
    },
    .{
        // martin_lof id_sym_ty: `J_elim` (path induction) whose large motive
        // and eigenvariables are not conclusion-pinned.
        .name = "auto martin_lof id_sym_ty J_elim auto? (no result)",
        .mm0_path = "tests/proof_cases/martin_lof.mm0",
        .proof_path = "tests/search_bench_cases/ml_id_sym_ty_auto.auf",
        .marker = "auto?",
        .expected_replacement = "",
        .generate = .{ .enabled = true, .max_depth = 6 },
        .expect_result = false,
        .expected_suggestion_count = 4,
    },
    .{
        // zermelo cb_bijection functional-from-injections: rebuild the nested
        // `∀∀∀` introduction `all_intro [all_intro [all_intro [l4]]]` (depth-3
        // recursive generation) from a sibling pool, over the full zermelo rule
        // env. `all_intro`'s hypothesis is conclusion-pinned, so concrete auto
        // CAN regenerate the chain. Regression guard for the `defer_generate`
        // slot-ordering bug (90ef168): deferring bystander rules' bare-binder
        // hyps used to misdirect generation and lose this proof entirely.
        .name = "auto zermelo nested all_intro auto?",
        .mm0_path = "tests/proof_cases/zermelo.mm0",
        .proof_path = "tests/search_bench_cases/zermelo_functional_all_intro_auto.auf",
        .marker = "auto?",
        .expected_replacement = "all_intro [all_intro [all_intro [l4]]]",
        .generate = .{ .enabled = true, .max_depth = 6 },
    },
    .{
        // zermelo_hilbert imp_id: `p → p` from an EMPTY pool. The Hilbert
        // h1/h2/mp route stays unreachable (every `mp` antecedent is unpinned
        // by the conclusion), but phase-5 constrained backward MP (256e05d)
        // finds the biconditional route: `bi1 : (p↔p)→(p→p)` and `biid : p↔p`
        // discharge `mp` to give `p → p`. Was a "nothing pinned, cheap reject"
        // negative control before phase 5 reached this proof.
        .name = "auto zermelo_hilbert imp_id auto? (phase 5 constrained MP)",
        .mm0_path = "tests/proof_cases/zermelo_hilbert.mm0",
        .proof_path = "tests/search_bench_cases/zh_imp_id_auto.auf",
        .marker = "auto?",
        .expected_replacement = "mp (p := $ p <-> p $) [bi1 [], biid []]",
        .generate = .{ .enabled = true, .max_depth = 6 },
    },
    .{
        // Double `imp_intro` over an `emp ⊢ …` goal: the first `imp_intro`
        // introduces an `emp, a=b` context, so the SECOND's hypothesis sub-goal
        // is `emp, a=b, a∈a ⊢ b∈a`. The generated target carries a redundant
        // `emp` (ACUI unit) that strict `matchTemplate` couldn't equate with
        // unit-free `l3`; `normalizeAcuiUnits` on the generation target closes
        // that. Regression guard for ACUI-unit canonicalization in generation.
        .name = "auto nd_eq_subst_mem double imp_intro auto?",
        .mm0_path = "tests/proof_cases/zermelo.mm0",
        .proof_path = "tests/search_bench_cases/nd_eq_subst_mem.auf",
        .marker = "auto?",
        .expected_replacement = "imp_intro [imp_intro [l3]]",
        .generate = .{ .enabled = true, .max_depth = 6 },
    },
    // ============================================================
    // META.md capability fixtures. Stage 4 open backward generation and
    // Stages 7–8 forward saturation are now supported for the cases below;
    // the remaining `expect_result = false` entries are negative controls
    // and still-unsolved gaps. Existing probes elsewhere in this file cover
    // other gap categories and are cross-referenced below.
    // ============================================================
    .{
        // STAGE 4 flagship (existential regular meta — SUPPORTED). The open
        // backward path defers `hyp_only_use`'s hyp-only witness x as an
        // existential meta, the child search solves the structured target
        // `P ?x` with `pred_K`, and the match-back pins x := K, rendered as
        // an explicit binding. Was the "no result, Stage 4" probe before the
        // open path landed.
        .name = "hyp-only witness auto? (Stage 4 open backward)",
        .mm0_path = "tests/search_bench_cases/metavariable_capabilities.mm0",
        .proof_path = "tests/search_bench_cases/meta_hyp_only_witness.auf",
        .marker = "auto?",
        .expected_replacement = "hyp_only_use (x := $ K $) [pred_K []]",
        .generate = .{ .enabled = true, .max_depth = 6 },
    },
    .{
        // STAGE 4 (generated child pins parent meta — SUPPORTED). Solving `C`
        // opens `N ?x` under `generated_child_parent`; the recursive child
        // opens `M ?x'` under `child_from_mark`, closes it with `mark_K`, and
        // the nested match-backs propagate K upward into both bindings.
        .name = "generated child pins parent auto? (Stage 4 open backward)",
        .mm0_path = "tests/search_bench_cases/metavariable_capabilities.mm0",
        .proof_path = "tests/search_bench_cases/meta_child_pins_parent.auf",
        .marker = "auto?",
        .expected_replacement = "generated_child_parent (x := $ K $) " ++
            "[child_from_mark (x := $ K $) [mark_K []]]",
        .generate = .{ .enabled = true, .max_depth = 6 },
    },
    .{
        // STAGE 4 (same meta reused in sibling hypotheses — SUPPORTED). The
        // first open sibling `L ?x` solves x := K via `left_K`; the second
        // sibling is then the concrete `R K`, closed by `right_K`.
        .name = "repeated unknown auto? (Stage 4 open backward)",
        .mm0_path = "tests/search_bench_cases/metavariable_capabilities.mm0",
        .proof_path = "tests/search_bench_cases/meta_repeated_unknown.auf",
        .marker = "auto?",
        .expected_replacement = "repeated_unknown_use (x := $ K $) " ++
            "[left_K [], right_K []]",
        .generate = .{ .enabled = true, .max_depth = 6 },
    },
    .{
        // STAGE 4 negative control: the same existential occurs in two
        // generated siblings, but the only children solve it inconsistently
        // (x := K versus x := J). The branch must reject cleanly.
        .name = "inconsistent repeated unknown auto? (no result, Stage 4)",
        .mm0_path = "tests/search_bench_cases/metavariable_capabilities.mm0",
        .proof_path = "tests/search_bench_cases/meta_inconsistent_repeated.auf",
        .marker = "auto?",
        .expected_replacement = "",
        .generate = .{ .enabled = true, .max_depth = 6 },
        .expect_result = false,
        .expected_suggestion_count = 0,
    },
    .{
        // STAGE 4 (bound_choice from @vars — SUPPORTED). The hidden bound x in
        // `bound_choice_use` has no surface occurrence in the conclusion `B`, so
        // its witness is genuinely free. The open walk defers x to a
        // `.bound_choice` meta (`P ?x`); no concrete/coupled member forces it,
        // so the phase-3 `@vars`-pool invention grounds `?x` to the first pool
        // dummy (X before Y, sorted), closing `P X` with `pred_any`. The wrong
        // witness `x := K` (a constant, via `pred_K`) is rejected at validation
        // because a bound binder requires a variable.
        .name = "bound @vars choice auto? (Stage 4 open backward)",
        .mm0_path = "tests/search_bench_cases/metavariable_capabilities.mm0",
        .proof_path = "tests/search_bench_cases/meta_bound_vars_choice.auf",
        .marker = "auto?",
        .expected_replacement = "bound_choice_use (x := $ X $) [pred_any []]",
        .generate = .{ .enabled = true, .max_depth = 6 },
    },
    .{
        // STAGE 4 negative control: a hidden bound witness of a sort with no
        // `@vars` pool entry must be a clean no-result, not an implicit dummy
        // allocation.
        .name = "missing @vars witness auto? (no result, Stage 4)",
        .mm0_path = "tests/search_bench_cases/metavariable_capabilities.mm0",
        .proof_path = "tests/search_bench_cases/meta_missing_bound_vars.auf",
        .marker = "auto?",
        .expected_replacement = "",
        .generate = .{ .enabled = true, .max_depth = 6 },
        .expect_result = false,
        .expected_suggestion_count = 0,
    },
    .{
        // STAGE 4 real flagship (`@recover`-shaped open target — SUPPORTED).
        // The goal `emp ⊢ ∃ n (n = 0)` opens `ex_intro`'s hypothesis as the
        // recover-shaped surface `emp ⊢ ?t = 0` (matrix with one leaf swap,
        // NOT the raw `[x/?t]`-headed template); the generated child
        // `eq_intro_nd` proves `emp ⊢ 0 = 0`, and the match-back reads the
        // witness t := 0 off the child conclusion. The explicit bindings now
        // render with notation (`0` for the term `d0`, `n = 0` for `eq n d0`)
        // via the notation-aware pretty-printer (a059e67).
        .name = "euclid ex_intro open witness auto? (Stage 4 open backward)",
        .mm0_path = "tests/search_bench_cases/euclid.mm0",
        .proof_path = "tests/search_bench_cases/euclid_ex_intro_open_auto.auf",
        .marker = "auto?",
        // Meta-solved witness `t` also renders the `@recover` pattern binder `p`
        // (the matrix `n = 0`), same as the Stage 5 ACUI-witness suggestions.
        .expected_replacement = "ex_intro (t := $ 0 $, p := $ n = 0 $) [eq_intro_nd []]",
        .generate = .{ .enabled = true, .max_depth = 6 },
    },
    .{
        // PHASE 5 (constrained backward MP) reclassification. Before 256e05d a
        // rule WITHOUT `@auto backward` never entered the open path, so this was
        // a Stage-4-gate zero-result. Phase 5 relaxes the gate for ANY backward
        // candidate whose hyp-only witness is pinned by a child conclusion (no
        // invention): the open walk defers `plain_only_use`'s `x`, the child
        // `pred_K` closes `P K`, and the match-back pins `x := K`. The
        // `@auto backward` annotation is therefore no longer load-bearing for
        // child-pinned open witnesses in the final retry phase.
        .name = "unannotated rule auto? (phase 5 constrained MP)",
        .mm0_path = "tests/search_bench_cases/metavariable_capabilities.mm0",
        .proof_path = "tests/search_bench_cases/meta_plain_hyp_only.auf",
        .marker = "auto?",
        .expected_replacement = "plain_only_use (x := $ K $) [pred_K []]",
        .generate = .{ .enabled = true, .max_depth = 6 },
    },
    .{
        // STAGE 4 negative control: an annotated rule whose deferred
        // hypothesis is a bare meta (`?p`) is rejected by the rigid-root
        // (absorber) guard — open targets need a useful concrete shape.
        .name = "bare-meta target auto? (no result, Stage 4 guard)",
        .mm0_path = "tests/search_bench_cases/metavariable_capabilities.mm0",
        .proof_path = "tests/search_bench_cases/meta_bare_meta_target.auf",
        .marker = "auto?",
        .expected_replacement = "",
        .generate = .{ .enabled = true, .max_depth = 6 },
        .expect_result = false,
        .expected_suggestion_count = 0,
    },
    .{
        // STAGE 4 negative control: recover-owned binders are not generic
        // fallback metas when the recover law cannot fire (pattern/hole
        // unbound). This should stay a clean no-result.
        .name = "recover-owned fallback auto? (no result, Stage 4)",
        .mm0_path = "tests/search_bench_cases/metavariable_capabilities.mm0",
        .proof_path = "tests/search_bench_cases/meta_recover_owned_no_fallback.auf",
        .marker = "auto?",
        .expected_replacement = "",
        .generate = .{ .enabled = true, .max_depth = 6 },
        .expect_result = false,
        .expected_suggestion_count = 0,
    },
    .{
        // STAGE 4 negative control: `exact?` has no generation hook and must
        // ignore `@auto backward`, so the open hyp-only witness remains
        // unsolved here even though `auto?` can synthesize it.
        .name = "auto backward exact? ignored (no result, Stage 4)",
        .mm0_path = "tests/search_bench_cases/metavariable_capabilities.mm0",
        .proof_path = "tests/search_bench_cases/meta_hyp_only_exact.auf",
        .marker = "exact?",
        .expected_replacement = "",
        .expect_result = false,
        .expected_suggestion_count = 0,
    },
    .{
        // STAGE 4 negative control: `apply?` may suggest the annotated rule,
        // but it must remain a one-step application with a ref hole rather
        // than entering open backward generation.
        .name = "auto backward apply? stays one-step (Stage 4)",
        .mm0_path = "tests/search_bench_cases/metavariable_capabilities.mm0",
        .proof_path = "tests/search_bench_cases/meta_hyp_only_apply.auf",
        .marker = "apply?",
        .expected_replacement = "hyp_only_use [ref1]",
    },
    .{
        // STAGE 7 flagship (forward universal instantiation — SUPPORTED). Goal
        // `(pair f u = pair f v) → (u = v)` from the hypothesis `mono f`
        // (= `∀ a ∀ b ((pair f a = pair f b) → (a = b))`). The forward layer
        // fires `all_elim` on `mono f` (one transparent-def unfold), deferring
        // the witness as a universal meta; the derived ref's goal-shaped
        // surface `∀ b ((pair f ?t = pair f b) → (?t = b))` then fills the
        // backward `all_elim` premise slot, the `@recover` correspondence
        // solves `?t := u` from the goal, and the materialized recipe renders
        // explicit bindings (hidden unfold dummies named from the theorem's
        // bound vars). This was the "no result, Stage 7" probe before the
        // forward layer landed.
        .name = "all_elim forward instantiation auto? (Stage 7 forward)",
        .mm0_path = "tests/search_bench_cases/all_elim_forward.mm0",
        .proof_path = "tests/search_bench_cases/all_elim_forward.auf",
        .marker = "auto?",
        .expected_replacement = "all_elim [all_elim (x := $ a $, t := $ u $, " ++
            "p := $ ∀ b (pair f a = pair f b → a = b) $) [#1]]",
        .generate = .{ .enabled = true, .max_depth = 6 },
    },
    .{
        // Boundary guard (SUPPORTED, marks the edge of the Stage 7 gap above).
        // Single-step `all_elim` whose witness `u` the goal reveals: backward
        // `@recover` reads it off and `auto?` emits `all_elim [#1]`. Kept as a
        // passing case so we can see exactly where current support stops.
        .name = "all_elim single-step instantiation auto? (supported boundary)",
        .mm0_path = "tests/search_bench_cases/all_elim_forward.mm0",
        .proof_path = "tests/search_bench_cases/all_elim_single.auf",
        .marker = "auto?",
        .expected_replacement = "all_elim [#1]",
        .generate = .{ .enabled = true, .max_depth = 6 },
    },
    .{
        // STAGE 8 two-layer chain (SUPPORTED). Same flagship goal, but solved
        // by the multi-layer forward pool alone: layer 2 fires `all_elim` on
        // the layer-1 shape `∀ b ((pair f ?t = pair f b) → (?t = b))`,
        // deriving the two-hole surface `(pair f ?t = pair f ?t2) → (?t = ?t2)`
        // with the layer-1 hole shared. The goal matches the surface directly,
        // and ONE solve instantiates both layers of the nested recipe
        // consistently (?t := u, ?t2 := v).
        .name = "all_elim two-layer derived direct auto? (Stage 8 forward)",
        .mm0_path = "tests/search_bench_cases/all_elim_forward.mm0",
        .proof_path = "tests/search_bench_cases/all_elim_forward.auf",
        .marker = "auto?",
        .expected_replacement = "all_elim (x := $ a $, t := $ v $, " ++
            "p := $ pair f u = pair f a → u = a $) " ++
            "[all_elim (x := $ b $, t := $ u $, " ++
            "p := $ ∀ a (pair f b = pair f a → b = a) $) [#1]]",
        .generate = .{ .enabled = true, .max_depth = 6 },
    },
    .{
        // STAGE 8 richer chain (SUPPORTED). `mono3 g` is a triple-nested
        // universal behind a transparent def; three forward layers (unfold
        // fire, then two derived-from-derived fires) build the three-hole
        // surface, and the goal-direct match solves all three witnesses in
        // one walk, materializing a three-deep nested recipe.
        .name = "all_elim three-layer chain auto? (Stage 8 forward)",
        .mm0_path = "tests/search_bench_cases/all_elim_forward.mm0",
        .proof_path = "tests/search_bench_cases/all_elim_forward3.auf",
        .marker = "auto?",
        .expected_replacement = "all_elim (x := $ a $, t := $ w $, " ++
            "p := $ pair (pair g u) v = pair v a → u = a $) " ++
            "[all_elim (x := $ b $, t := $ v $, " ++
            "p := $ ∀ a (pair (pair g u) b = pair b a → u = a) $) " ++
            "[all_elim (x := $ c $, t := $ u $, " ++
            "p := $ ∀ b ∀ a (pair (pair g c) b = pair b a → c = a) $) [#1]]]",
        .generate = .{ .enabled = true, .max_depth = 6 },
    },
    .{
        // STAGE 8 realistic two-layer chain in the full euclid theory: the
        // goal is an instance of the ∀i∀j totality fact with the
        // intermediate single-instantiation line omitted, so both witnesses
        // must come from the forward layer's shared-hole two-layer recipe.
        .name = "euclid le_total two-layer instantiation auto? (Stage 8)",
        .mm0_path = "tests/search_bench_cases/euclid.mm0",
        .proof_path = "tests/search_bench_cases/euclid_le_total_auto.auf",
        .marker = "auto?",
        .expected_replacement = "all_elim (x := $ j $, g := $ _ $, " ++
            "t := $ b $, p := $ a <= j ∨ j <= a $) " ++
            "[all_elim (x := $ i $, g := $ _ $, t := $ a $, " ++
            "p := $ A. j (i <= j ∨ j <= i) $) [l1]]",
        .generate = .{ .enabled = true, .max_depth = 6 },
    },
    .{
        // STAGE 8 realistic single-step instantiation with a large matrix
        // (implication + existential + conjunction) in the full euclid
        // theory; measures the forward layer + @recover walk on real-size
        // terms with the full rule environment loaded.
        .name = "euclid prime-factor instance auto? (Stage 8 forward)",
        .mm0_path = "tests/search_bench_cases/euclid.mm0",
        .proof_path = "tests/search_bench_cases/euclid_prime_factor_inst_auto.auf",
        .marker = "auto?",
        .expected_replacement = "all_elim [l1]",
        .generate = .{ .enabled = true, .max_depth = 6 },
    },
    .{
        // STAGE 8 recover-free concrete forward chain: the conjunct
        // extraction steps toward the additive witness are omitted, so the
        // goal needs a chain through the ∧ line; @auto forward and_elim_l/r
        // pre-derive the conjuncts concretely (no universal metas).
        .name = "euclid dvd_fact and_elim chain auto? (Stage 8 forward)",
        .mm0_path = "tests/search_bench_cases/euclid.mm0",
        .proof_path = "tests/search_bench_cases/euclid_dvd_fact_chain_auto.auf",
        .marker = "auto?",
        .expected_replacement = "le_iff_add [lt_implies_le_ax " ++
            "[and_elim_l (g := $ suc 0 < d ∧ d <= 0 $, " ++
            "a := $ suc 0 < d $, b := $ d <= 0 $) [l1]]]",
        .generate = .{ .enabled = true, .max_depth = 6 },
    },
    .{
        // STAGES 4+7 composition, Hilbert style (minor premise in the pool):
        // hypotheses `∀ x (P x → Q x)` and `P K`, goal `Q K`. The forward
        // layer derives the family fact `P ?t → Q ?t` (universal meta) from
        // the ∀ hypothesis; backward `mp` (@auto backward) opens its major
        // premise as the existential target `?a → Q K`, the derived fact
        // discharges it (the hint match solves ?t := K from the concrete
        // overlap `Q K` vs `Q ?t`), and the match-back pins ?a := P K — the
        // existential is only ever bound to a concrete term, never to a
        // meta-bearing one. The minor slot is then the pool ref `P K`.
        .name = "fwd/bwd compose hilbert minor-in-pool auto? (Stage 4+7)",
        .mm0_path = "tests/search_bench_cases/forward_backward_compose.mm0",
        .proof_path = "tests/search_bench_cases/fwd_bwd_minor_in_pool.auf",
        .marker = "auto?",
        // The branchfactor hyp ordering pins the app-structured minor `P K` from
        // the pool first, so `mp`'s bindings are inferred — the clean nested
        // suggestion with no explicit `(a := …)` / `all_elim (x := …)` bindings.
        .expected_replacement = "mp [all_elim [#1], #2]",
        .generate = .{ .enabled = true, .max_depth = 6 },
    },
    .{
        // STAGES 4+7 composition, Hilbert style (open route): same as above
        // but `P K` is NOT in the pool, so after the open major premise is
        // discharged by the derived family fact, the pinned minor `P K` must
        // itself be a generated child closed by the axiom `P_K []`.
        .name = "fwd/bwd compose hilbert open-minor auto? (Stage 4+7)",
        .mm0_path = "tests/search_bench_cases/forward_backward_compose.mm0",
        .proof_path = "tests/search_bench_cases/fwd_bwd_minor_generated.auf",
        .marker = "auto?",
        // As above, but `P K` is not in the pool. Under the branchfactor order the
        // earlier-proved lemma `fwd_bwd_minor_in_pool` now matches first and is
        // reused directly (with the minor generated from `P_K []`) — a valid
        // lemma-reuse suggestion in place of the re-derived `mp [all_elim …]`.
        .expected_replacement = "fwd_bwd_minor_in_pool [#1, P_K []]",
        .generate = .{ .enabled = true, .max_depth = 6 },
    },
    .{
        // Forward-layer boundary guard for the composition theory: the
        // derived family fact's materialized recipe closes `P K → Q K`
        // directly (the backward `@recover` route `all_elim [#1]` is also
        // offered). Declared LAST in the .mm0 so it cannot serve as a lemma
        // for the composition theorems.
        .name = "fwd/bwd compose hilbert forward-direct auto? (Stage 7)",
        .mm0_path = "tests/search_bench_cases/forward_backward_compose.mm0",
        .proof_path = "tests/search_bench_cases/fwd_direct_probe.auf",
        .marker = "auto?",
        .expected_replacement = "all_elim (x := $ x $, t := $ K $, " ++
            "p := $ P x → Q x $) [#1]",
        .generate = .{ .enabled = true, .max_depth = 6 },
    },
    .{
        // STAGES 4+7 composition, ND style (minor premise in the pool). Same
        // shape as the Hilbert case but over sequents with ACUI contexts.
        // Here the slot plan pins the app-structured minor `emp ⊢ P K` from
        // the pool first, so the major becomes the concrete `emp ⊢ P K → Q K`
        // and the child resolves through backward `@recover` — the clean
        // nested suggestion with no explicit bindings.
        .name = "fwd/bwd compose nd minor-in-pool auto? (Stage 4+7)",
        .mm0_path = "tests/search_bench_cases/nd_forward_backward.mm0",
        .proof_path = "tests/search_bench_cases/nd_fwd_bwd_minor_in_pool.auf",
        .marker = "auto?",
        .expected_replacement = "imp_elim [all_elim [#1], #2]",
        .generate = .{ .enabled = true, .max_depth = 6 },
    },
    .{
        // STAGES 4+7 composition, ND style (open route): with `emp ⊢ P K`
        // not in the pool, imp_elim's major premise opens as the existential
        // `emp ⊢ ?a → Q K`. The child (backward all_elim, witness read off
        // the hint through the meta wildcard) concludes through its @view, so
        // this pins the recover-surface match-back (the raw `[x/K]p` line
        // expr would conflict structurally); the pinned minor is generated
        // from `P_K_nd []`.
        .name = "fwd/bwd compose nd open-minor auto? (Stage 4+7)",
        .mm0_path = "tests/search_bench_cases/nd_forward_backward.mm0",
        .proof_path = "tests/search_bench_cases/nd_fwd_bwd_minor_generated.auf",
        .marker = "auto?",
        .expected_replacement = "imp_elim (a := $ P K $) " ++
            "[all_elim [#1], P_K_nd []]",
        .generate = .{ .enabled = true, .max_depth = 6 },
    },
    .{
        // STAGE 8 saturation-loop stress (bounded, no result). `step` and
        // `join` feed on their own output, so the derived pool grows until
        // the fact budget stops it; the goal `R` is unprovable. Asserts the
        // loop stays bounded (budget exhaustion reported, no suggestion
        // invented) and the backward side stays cheap.
        .name = "forward saturation loop stress auto? (bounded, no result)",
        .mm0_path = "tests/search_bench_cases/forward_stress.mm0",
        .proof_path = "tests/search_bench_cases/forward_stress.auf",
        .marker = "auto?",
        .expected_replacement = "",
        .generate = .{ .enabled = true, .max_depth = 6 },
        .expect_result = false,
        .expected_suggestion_count = 0,
    },
    .{
        // META_STRESS theory #5 (adversarial saturation). A commutativity loop:
        // `comm` swaps `g`'s args, regenerating from its own output. The shape
        // key drops the swapped-back fact and the recipe key blocks re-firing,
        // so saturation reaches a FIXPOINT (exhausted = false) at one derived
        // fact (`P (g K2 K1)`), never spinning to the budget. Goal unprovable.
        .name = "adversarial commutativity loop auto? (fixpoint, no result)",
        .mm0_path = "tests/search_bench_cases/adversarial_saturation.mm0",
        .proof_path = "tests/search_bench_cases/adversarial_comm_loop.auf",
        .marker = "auto?",
        .expected_replacement = "",
        .generate = .{ .enabled = true, .max_depth = 6 },
        .expect_result = false,
        .expected_suggestion_count = 0,
        .expect_saturation_exhausted = false,
        .expect_derived_refs = 1,
    },
    .{
        // META_STRESS theory #5. Mutual regeneration: `ping`/`pong` build an
        // unbounded `h`-tower, so the frontier stays productive at every layer
        // and saturation must stop on the budget with exhaustion REPORTED
        // (exhausted = true) rather than looping forever. Goal unprovable.
        .name = "adversarial mutual regeneration auto? (exhausts, no result)",
        .mm0_path = "tests/search_bench_cases/adversarial_saturation.mm0",
        .proof_path = "tests/search_bench_cases/adversarial_mutual_regen.auf",
        .marker = "auto?",
        .expected_replacement = "",
        .generate = .{ .enabled = true, .max_depth = 6 },
        .expect_result = false,
        .expected_suggestion_count = 0,
        .expect_saturation_exhausted = true,
    },
    .{
        // META_STRESS theory #5. Confluence: `viaA`/`viaB` derive the identical
        // fact `C K1` by distinct recipes. The recipe keys differ, so the
        // canonical SURFACE shape key is what must collapse them to a single
        // derived ref (exhausted = false, one derived fact). Goal unprovable.
        .name = "adversarial confluence dedupe auto? (collapses, no result)",
        .mm0_path = "tests/search_bench_cases/adversarial_saturation.mm0",
        .proof_path = "tests/search_bench_cases/adversarial_confluence.auf",
        .marker = "auto?",
        .expected_replacement = "",
        .generate = .{ .enabled = true, .max_depth = 6 },
        .expect_result = false,
        .expected_suggestion_count = 0,
        .expect_saturation_exhausted = false,
        .expect_derived_refs = 1,
    },
};

pub fn main() !void {
    const allocator = counting_allocator.allocator();
    const options = try parseOptions(allocator);
    counting_allocator.track_sites = options.track_sites;
    counting_allocator.trap_bytes = options.alloc_trap_mib << 20;

    var stdout_buf: [4096]u8 = undefined;
    var stdout_writer = std.fs.File.stdout().writer(&stdout_buf);
    const stdout = &stdout_writer.interface;

    if (options.sweep != null) {
        try runSweep(allocator, stdout, options);
        try stdout.flush();
        return;
    }

    if (options.frontier) |mode| {
        const failed = try runFrontier(allocator, stdout, mode, options);
        try stdout.flush();
        if (options.require_no_miss and failed) std.process.exit(1);
        return;
    }

    if (options.compact) {
        try stdout.print("search benchmark scenarios: {}\n", .{scenarios.len});
        try stdout.print(
            "{s:<46} {s:>10} {s:>10} {s:>10}\n",
            .{ "scenario", "total", "setup", "search" },
        );
    } else {
        try stdout.print("search benchmark scenarios: {}\n", .{scenarios.len});
    }
    for (scenarios) |scenario| {
        if (options.filter) |needle| {
            if (std.mem.indexOf(u8, scenario.name, needle) == null) continue;
        }
        try runScenario(allocator, stdout, scenario, options);
        try stdout.flush();
    }
}

fn parseOptions(allocator: std.mem.Allocator) !BenchOptions {
    const args = try std.process.argsAlloc(allocator);
    defer std.process.argsFree(allocator, args);

    var options = BenchOptions{};
    var files = std.ArrayListUnmanaged(FixturePair){};
    for (args[1..]) |arg| {
        if (std.mem.eql(u8, arg, "--compact") or
            std.mem.eql(u8, arg, "-c"))
        {
            options.compact = true;
            continue;
        }
        if (std.mem.startsWith(u8, arg, "--filter=")) {
            options.filter = try allocator.dupe(u8, arg["--filter=".len..]);
            continue;
        }
        if (std.mem.startsWith(u8, arg, "--frontier=")) {
            const mode = arg["--frontier=".len..];
            options.frontier = std.meta.stringToEnum(FrontierMode, mode) orelse {
                std.debug.print("unknown frontier mode: {s}\n", .{mode});
                try printUsage();
                return error.InvalidArgument;
            };
            continue;
        }
        if (std.mem.startsWith(u8, arg, "--files=")) {
            const spec = arg["--files=".len..];
            const colon = std.mem.indexOfScalar(u8, spec, ':') orelse {
                std.debug.print("--files expects MM0:AUF, got: {s}\n", .{spec});
                try printUsage();
                return error.InvalidArgument;
            };
            const mm0_path = try allocator.dupe(u8, spec[0..colon]);
            const proof_path = try allocator.dupe(u8, spec[colon + 1 ..]);
            try files.append(allocator, .{
                .name = std.fs.path.stem(proof_path),
                .mm0_path = mm0_path,
                .proof_path = proof_path,
            });
            continue;
        }
        if (std.mem.startsWith(u8, arg, "--marker=")) {
            options.marker = try allocator.dupe(u8, arg["--marker=".len..]);
            continue;
        }
        if (std.mem.startsWith(u8, arg, "--max-depth=")) {
            options.max_depth = try std.fmt.parseInt(
                usize,
                arg["--max-depth=".len..],
                10,
            );
            continue;
        }
        if (std.mem.startsWith(u8, arg, "--slow-ms=")) {
            options.slow_ms = try std.fmt.parseInt(
                u64,
                arg["--slow-ms=".len..],
                10,
            );
            continue;
        }
        if (std.mem.startsWith(u8, arg, "--gen-nodes=")) {
            options.gen_nodes = try std.fmt.parseInt(usize, arg["--gen-nodes=".len..], 10);
            continue;
        }
        if (std.mem.startsWith(u8, arg, "--gen-fuel=")) {
            options.gen_fuel = try std.fmt.parseInt(usize, arg["--gen-fuel=".len..], 10);
            continue;
        }
        if (std.mem.startsWith(u8, arg, "--global-budget=")) {
            options.global_budget = try std.fmt.parseInt(u64, arg["--global-budget=".len..], 10);
            continue;
        }
        if (std.mem.startsWith(u8, arg, "--phase5-fuel=")) {
            options.phase5_fuel = try std.fmt.parseInt(usize, arg["--phase5-fuel=".len..], 10);
            continue;
        }
        if (std.mem.startsWith(u8, arg, "--fwd-facts=")) {
            options.fwd_facts = try std.fmt.parseInt(usize, arg["--fwd-facts=".len..], 10);
            continue;
        }
        if (std.mem.startsWith(u8, arg, "--fwd-layers=")) {
            options.fwd_layers = try std.fmt.parseInt(usize, arg["--fwd-layers=".len..], 10);
            continue;
        }
        if (std.mem.startsWith(u8, arg, "--fwd-attempts=")) {
            options.fwd_attempts = try std.fmt.parseInt(usize, arg["--fwd-attempts=".len..], 10);
            continue;
        }
        if (std.mem.startsWith(u8, arg, "--fwd-tuples=")) {
            options.fwd_tuples = try std.fmt.parseInt(usize, arg["--fwd-tuples=".len..], 10);
            continue;
        }
        if (std.mem.eql(u8, arg, "--verbose") or std.mem.eql(u8, arg, "-v")) {
            options.verbose = true;
            continue;
        }
        if (std.mem.eql(u8, arg, "--track-sites")) {
            options.track_sites = true;
            continue;
        }
        if (std.mem.startsWith(u8, arg, "--alloc-trap=")) {
            options.alloc_trap_mib = try std.fmt.parseInt(
                u64,
                arg["--alloc-trap=".len..],
                10,
            );
            continue;
        }
        if (std.mem.eql(u8, arg, "--require-no-miss")) {
            options.require_no_miss = true;
            continue;
        }
        if (std.mem.eql(u8, arg, "--no-search-memo")) {
            options.search_memo = false;
            continue;
        }
        if (std.mem.eql(u8, arg, "--no-shape-cache")) {
            options.shape_cache = false;
            continue;
        }
        if (std.mem.eql(u8, arg, "--no-deep-member-prune")) {
            options.deep_member_prune = false;
            continue;
        }
        if (std.mem.eql(u8, arg, "--no-persist-negative")) {
            options.persist_negative = false;
            continue;
        }
        if (std.mem.eql(u8, arg, "--counters")) {
            options.counters = true;
            continue;
        }
        if (std.mem.startsWith(u8, arg, "--sweep=")) {
            options.sweep = try parseSweepSpec(allocator, arg["--sweep=".len..]);
            continue;
        }
        if (std.mem.eql(u8, arg, "--help") or
            std.mem.eql(u8, arg, "-h"))
        {
            try printUsage();
            std.process.exit(0);
        }
        std.debug.print("unknown search-bench option: {s}\n", .{arg});
        try printUsage();
        return error.InvalidArgument;
    }
    options.files = try files.toOwnedSlice(allocator);
    return options;
}

fn printUsage() !void {
    var stderr_buf: [1024]u8 = undefined;
    var stderr_writer = std.fs.File.stderr().writer(&stderr_buf);
    const stderr = &stderr_writer.interface;
    try stderr.writeAll(
        "usage: zig build bench-search -- [--compact|-c] [--filter=TEXT]\n" ++
            "       [--frontier=breadth|depth] [--files=MM0:AUF]...\n" ++
            "       [--marker=auto?|exact?|apply?] [--max-depth=N]\n" ++
            "       [--slow-ms=N] [--verbose|-v] [--counters] [--track-sites]\n" ++
            "       [--require-no-miss] [--no-search-memo] [--no-deep-member-prune]\n" ++
            "       [--no-persist-negative]\n" ++
            "       [--no-shape-cache]\n" ++
            "       [--gen-nodes=N] [--gen-fuel=N] [--global-budget=TICKS]\n" ++
            "       [--fwd-facts=N] [--fwd-layers=N] [--fwd-attempts=N]\n" ++
            "       [--sweep=FAMILY[:N1,N2,...]]\n" ++
            "\n" ++
            "frontier modes (META_STRESS.md): per-line ablation (breadth)\n" ++
            "or proof-tail truncation (depth) over the real developments;\n" ++
            "default corpus is the major tests/proof_cases/ pairs and\n" ++
            "--filter matches theorem names.\n" ++
            "\n" ++
            "sweep mode (META_STRESS.md theory #4): synthesize a distractor\n" ++
            "theory parametrized by N and plot search time vs N to catch\n" ++
            "superlinear blowups. FAMILY is head_distinct|head_shared|\n" ++
            "ref_fanout; points default to 8..512. Honors --marker.\n",
    );
    try stderr.flush();
}

fn runScenario(
    allocator: std.mem.Allocator,
    writer: anytype,
    scenario: Scenario,
    options: BenchOptions,
) !void {
    const scenario_start = std.time.nanoTimestamp();
    const mm0_src = try std.fs.cwd().readFileAlloc(
        allocator,
        scenario.mm0_path,
        std.math.maxInt(usize),
    );
    defer allocator.free(mm0_src);
    const proof_src = try std.fs.cwd().readFileAlloc(
        allocator,
        scenario.proof_path,
        std.math.maxInt(usize),
    );
    defer allocator.free(proof_src);
    const offset = std.mem.indexOf(u8, proof_src, scenario.marker) orelse {
        return error.MissingBenchmarkMarker;
    };

    var counters = Search.SearchCounters{};
    var suggestions = try Search.suggestionsAtSourceOffset(
        allocator,
        mm0_src,
        proof_src,
        offset,
        .{
            .max_results = scenario.max_results,
            .exact_result_limit = scenario.exact_result_limit,
            .counters = &counters,
            .generate = scenario.generate,
        },
    );
    defer suggestions.deinit();

    if (scenario.expect_result and
        !containsReplacement(suggestions.items, scenario.expected_replacement))
    {
        try writer.print(
            "\n{s}: expected suggestion not found: {s}\n",
            .{ scenario.name, scenario.expected_replacement },
        );
        try printSuggestions(writer, suggestions.items);
        try writer.flush();
        return error.MissingExpectedBenchmarkSuggestion;
    }

    if (scenario.expected_suggestion_count) |expected_count| {
        if (suggestions.items.len != expected_count) {
            try writer.print(
                "\n{s}: expected {} suggestions, found {}\n",
                .{ scenario.name, expected_count, suggestions.items.len },
            );
            try printSuggestions(writer, suggestions.items);
            try writer.flush();
            return error.UnexpectedBenchmarkSuggestionCount;
        }
    }

    if (scenario.expect_saturation_exhausted) |expected_exhausted| {
        if (counters.forward_saturation_exhausted != expected_exhausted) {
            try writer.print(
                "\n{s}: expected saturation exhausted = {}, got {}\n",
                .{
                    scenario.name,
                    expected_exhausted,
                    counters.forward_saturation_exhausted,
                },
            );
            try writer.flush();
            return error.UnexpectedSaturationExhaustion;
        }
    }

    if (scenario.expect_derived_refs) |expected_derived| {
        if (counters.derived_ref_count != expected_derived) {
            try writer.print(
                "\n{s}: expected {} derived refs, got {}\n",
                .{ scenario.name, expected_derived, counters.derived_ref_count },
            );
            try writer.flush();
            return error.UnexpectedDerivedRefCount;
        }
    }

    const total_ns = elapsedSince(scenario_start);
    if (options.compact) {
        try writer.print("{s:<46} ", .{scenario.name});
        try printDurationCompact(writer, total_ns);
        try writer.writeAll(" ");
        try printDurationCompact(writer, counters.cold_setup_ns);
        try writer.writeAll(" ");
        try printDurationCompact(writer, counters.warm_search_ns);
        try writer.writeAll("\n");
        return;
    }

    try writer.print("\n{s}\n", .{scenario.name});
    try writer.print("  suggestions: {}\n", .{suggestions.items.len});
    try printDuration(writer, "total wall", total_ns);
    try printDuration(writer, "cold setup", counters.cold_setup_ns);
    try printDuration(writer, "warm search", counters.warm_search_ns);
    try printDuration(writer, "rule index build", counters.rule_index_build_ns);
    try printDuration(writer, "ref index build", counters.ref_index_build_ns);
    try printDuration(writer, "shape emission", counters.shape_emission_ns);
    try printDuration(writer, "rule lookup", counters.rule_lookup_ns);
    try printDuration(writer, "ref lookup", counters.ref_lookup_ns);
    try printDuration(writer, "tc clone", counters.tc_clone_ns);
    try printDuration(writer, "tc apply", counters.tc_apply_ns);
    try writer.print(
        "  candidate rules before conclusion validation: {}\n",
        .{counters.candidate_rules_before_conclusion_validation},
    );
    try writer.print(
        "  conclusion member prunes: {}\n",
        .{counters.conclusion_member_prunes},
    );
    try writer.print(
        "  final conclusion prunes: {}\n",
        .{counters.final_conclusion_prunes},
    );
    try writer.print(
        "  conclusion probes: {}\n",
        .{counters.conclusion_probes},
    );
    try writer.print("  ref pool size: {}\n", .{counters.ref_pool_size});
    try writer.print(
        "  per-hyp filtered ref list total: {}\n",
        .{counters.per_hyp_filtered_ref_list_total},
    );
    try writer.print(
        "  ref tuple count after filtering: {}\n",
        .{counters.ref_tuple_count_after_filtering},
    );
    try writer.print(
        "  full tryCandidate calls: {}\n",
        .{counters.full_try_candidate_calls},
    );
    try writer.print(
        "  accepted candidates: {}\n",
        .{counters.accepted_candidates},
    );
    try writer.print(
        "  generated chain attempts: {}\n",
        .{counters.generated_chain_attempts},
    );
    try writer.print(
        "  recursive apply calls: {}\n",
        .{counters.recursive_apply_calls},
    );
    try writer.print(
        "  rejected candidates after validation: {}\n",
        .{counters.rejected_candidates_after_validation},
    );
    try writer.print(
        "  hyp syntactic matches: {}\n",
        .{counters.hyp_match_syntactic},
    );
    try writer.print(
        "  hyp definite mismatches: {}\n",
        .{counters.hyp_match_definite_mismatch},
    );
    try writer.print(
        "  hyp unknown matches: {}\n",
        .{counters.hyp_match_unknown},
    );
    try writer.print(
        "  recover member injections: {}\n",
        .{counters.recover_member_injections},
    );
    try writer.print(
        "  split context guard rejects: {}\n",
        .{counters.split_context_guard_rejects},
    );
    try writer.print(
        "  acui witness attempts: {}\n",
        .{counters.acui_witness_attempts},
    );
    try writer.print(
        "  recover guard rejects (match/extract): {}/{}\n",
        .{ counters.recover_guard_match_rejects, counters.recover_guard_extract_rejects },
    );
    try writer.print(
        "  metas created (wild/exist/univ/bound): {}/{}/{}/{}\n",
        .{
            counters.wildcard_metas_created,
            counters.existential_metas_created,
            counters.universal_metas_created,
            counters.bound_choice_metas_created,
        },
    );
    try writer.print(
        "  meta assignments: {}\n",
        .{counters.meta_assignments},
    );
    try writer.print(
        "  meta rollbacks: {}\n",
        .{counters.meta_rollbacks},
    );
    try writer.print(
        "  derived refs: {}\n",
        .{counters.derived_ref_count},
    );
    try writer.print(
        "  forward rule attempts: {}\n",
        .{counters.forward_rule_attempts},
    );
    try writer.print(
        "  forward match tuples: {}\n",
        .{counters.forward_match_tuples},
    );
    try writer.print(
        "  forward layers run: {}\n",
        .{counters.forward_layers_run},
    );
    try writer.print(
        "  forward saturation exhausted: {}\n",
        .{counters.forward_saturation_exhausted},
    );
    try printHypLookupDiagnostics(writer, &counters);
    try printRuleAttemptDiagnostics(writer, &counters);
}

fn elapsedSince(start: i128) u64 {
    const elapsed = std.time.nanoTimestamp() - start;
    if (elapsed <= 0) return 0;
    return @intCast(elapsed);
}

fn containsReplacement(
    suggestions: []const Search.SourceSuggestion,
    expected: []const u8,
) bool {
    for (suggestions) |item| {
        if (std.mem.eql(u8, item.replacement, expected)) return true;
    }
    return false;
}

fn printSuggestions(
    writer: anytype,
    suggestions: []const Search.SourceSuggestion,
) !void {
    for (suggestions) |item| {
        try writer.print("  suggestion: {s}\n", .{item.replacement});
    }
}

fn printHypLookupDiagnostics(
    writer: anytype,
    counters: *const Search.SearchCounters,
) !void {
    if (counters.hyp_lookup_diagnostics_len == 0) return;
    try writer.writeAll("  hyp lookup diagnostics:\n");
    for (
        counters.hyp_lookup_diagnostics[0..counters.hyp_lookup_diagnostics_len],
    ) |diagnostic| {
        try writer.print(
            "    {s} hyp={} phase={s} depth={} refs={} fallback={s}\n",
            .{
                diagnostic.rule_name.slice(),
                diagnostic.hyp_index,
                hypLookupPhaseName(diagnostic.phase),
                diagnostic.depth,
                diagnostic.filtered_len,
                hypLookupFallbackName(diagnostic.fallback),
            },
        );
    }
}

fn printRuleAttemptDiagnostics(
    writer: anytype,
    counters: *const Search.SearchCounters,
) !void {
    if (counters.rule_attempt_diagnostics_len == 0) return;
    try writer.writeAll("  full validation attempts by rule:\n");
    for (
        counters.rule_attempt_diagnostics[0..counters.rule_attempt_diagnostics_len],
    ) |diagnostic| {
        try writer.print(
            "    {s}: attempts={} accepted={} rejected={}\n",
            .{
                diagnostic.rule_name.slice(),
                diagnostic.attempts,
                diagnostic.accepted,
                diagnostic.rejected,
            },
        );
    }
}

fn hypLookupPhaseName(phase: Search.HypLookupPhase) []const u8 {
    return switch (phase) {
        .initial => "initial",
        .dynamic => "dynamic",
    };
}

fn hypLookupFallbackName(fallback: Search.HypLookupFallback) []const u8 {
    return switch (fallback) {
        .none => "none",
        .template_error => "template_error",
        .broad_shape => "broad_shape",
    };
}

fn printDuration(writer: anytype, label: []const u8, ns: u64) !void {
    const ms = ns / std.time.ns_per_ms;
    const micros = (ns / std.time.ns_per_us) % 1000;
    try writer.print("  {s}: {}.{d:0>3} ms\n", .{ label, ms, micros });
}

fn printDurationCompact(writer: anytype, ns: u64) !void {
    const ms = ns / std.time.ns_per_ms;
    const micros = (ns / std.time.ns_per_us) % 1000;
    try writer.print("{d:>6}.{d:0>3}ms", .{ ms, micros });
}

/// Raw per-call cost counts for one run, in the order `weightedTicks` takes
/// them: intern ticks, symbolic ticks, shape ticks, `tryCandidate` count.
const RunTicks = struct {
    intern: u64 = 0,
    sym: u64 = 0,
    shape: u64 = 0,
    candidates: u64 = 0,

    fn of(counters: *const Search.SearchCounters) RunTicks {
        return .{
            .intern = counters.gen_work_ticks,
            .sym = counters.gen_sym_ticks,
            .shape = counters.gen_walk_ticks,
            .candidates = counters.full_try_candidate_calls,
        };
    }

    fn weighted(self: RunTicks) u64 {
        return Search.weightedTicks(
            self.intern,
            self.sym,
            self.shape,
            self.candidates,
        );
    }
};

/// Work ticks in millions: the weighted per-call `GlobalBudget` cost plus the
/// raw counts behind it, printed alongside the latency they proxy for budget
/// calibration/weight fitting.
fn printTicksCompact(writer: anytype, ticks: RunTicks) !void {
    const weighted = @as(f64, @floatFromInt(ticks.weighted())) / 1e6;
    const intern = @as(f64, @floatFromInt(ticks.intern)) / 1e6;
    const sym = @as(f64, @floatFromInt(ticks.sym)) / 1e6;
    const shape = @as(f64, @floatFromInt(ticks.shape)) / 1e6;
    try writer.print(
        " t={d:>7.2}M (i={d:.2} s={d:.2} sh={d:.2} tc={d})",
        .{ weighted, intern, sym, shape, ticks.candidates },
    );
}

// ===========================================================================
// Frontier analysis (META_STRESS.md workstream 1)
// ===========================================================================

const Spliced = struct {
    text: []const u8,
    /// Byte offset of the spliced marker in `text`.
    offset: usize,
};

/// Rebuild `src` with `removed_lines` excised (their spans include the
/// trailing newline, so block-separating blank lines survive) and the
/// application at `app_span` replaced by `marker`. Removed lines must
/// precede `app_span` in source order.
fn spliceSource(
    arena: std.mem.Allocator,
    src: []const u8,
    removed_lines: []const ProofScript.ProofLine,
    app_span: ProofScript.Span,
    marker: []const u8,
) !Spliced {
    var out = std.ArrayListUnmanaged(u8){};
    var pos: usize = 0;
    for (removed_lines) |line| {
        try out.appendSlice(arena, src[pos..line.span.start]);
        pos = line.span.end;
    }
    try out.appendSlice(arena, src[pos..app_span.start]);
    const offset = out.items.len;
    try out.appendSlice(arena, marker);
    try out.appendSlice(arena, src[app_span.end..]);
    return .{ .text = out.items, .offset = offset };
}

/// Collapse whitespace runs to single spaces and trim, so a multi-line human
/// application compares against a single-line suggestion replacement.
fn normalizeWhitespace(
    arena: std.mem.Allocator,
    text: []const u8,
) ![]const u8 {
    var out = std.ArrayListUnmanaged(u8){};
    var in_ws = true;
    for (text) |c| {
        if (c == ' ' or c == '\t' or c == '\n' or c == '\r') {
            if (!in_ws) try out.append(arena, ' ');
            in_ws = true;
        } else {
            try out.append(arena, c);
            in_ws = false;
        }
    }
    while (out.items.len > 0 and out.items[out.items.len - 1] == ' ') {
        _ = out.pop();
    }
    return out.items;
}

fn truncateForRow(text: []const u8, max: usize) []const u8 {
    if (text.len <= max) return text;
    // Avoid splitting a UTF-8 sequence.
    var end = max;
    while (end > 0 and text[end] & 0xC0 == 0x80) end -= 1;
    return text[0..end];
}

fn frontierGenerateOptions(options: BenchOptions) Search.GenerateOptions {
    if (std.mem.eql(u8, options.marker, "auto?")) {
        var gen = Search.GenerateOptions{ .enabled = true, .max_depth = options.max_depth };
        gen.search_memo = options.search_memo;
        gen.deep_member_prune = options.deep_member_prune;
        gen.shape_cache = options.shape_cache;
        gen.persist_negative = options.persist_negative;
        if (options.gen_nodes != 0) gen.max_nodes = options.gen_nodes;
        if (options.gen_fuel != 0) gen.fuel = options.gen_fuel;
        if (options.phase5_fuel != 0) gen.phase5_fuel = options.phase5_fuel;
        if (options.global_budget) |budget| {
            gen.global_budget = if (budget == 0) null else budget;
        }
        if (options.fwd_facts != 0) gen.forward.max_forward_facts = options.fwd_facts;
        if (options.fwd_layers != 0) gen.forward.max_forward_layers = options.fwd_layers;
        if (options.fwd_attempts != 0) gen.forward.max_forward_rule_attempts = options.fwd_attempts;
        if (options.fwd_tuples != 0) gen.forward.max_forward_match_tuples = options.fwd_tuples;
        return gen;
    }
    return .{ .shape_cache = options.shape_cache };
}

const FrontierRun = struct {
    found: bool,
    top1_match: bool,
    search_ns: u64,
    wall_ns: u64,
    err: ?anyerror = null,
    counters: Search.SearchCounters = .{},
};

/// Byte-exact live/peak tracking around the backing allocator, to split
/// "still live" (true retention) from "freed but cached by the allocator"
/// when RSS stays high (META_STRESS.md open thread 1).
const CountingAllocator = struct {
    child: std.mem.Allocator,
    live: std.atomic.Value(u64) = .init(0),
    peak: std.atomic.Value(u64) = .init(0),
    /// Per-site attribution is opt-in (`--track-sites`): the mutex + map
    /// upkeep is heavy enough (~2.4x on allocation-bound searches) to
    /// distort the timing numbers the bench exists to measure. The atomic
    /// live/peak counters above are always on (negligible).
    track_sites: bool = false,
    /// Nonzero: panic once live bytes exceed this (see `add`).
    trap_bytes: u64 = 0,
    /// Per-site live-byte attribution (keyed by the allocation `ret_addr`,
    /// symbolized offline with addr2line). Maps allocate straight from the
    /// child allocator so tracking never recurses into itself.
    mutex: std.Thread.Mutex = .{},
    sites: std.AutoHashMapUnmanaged(usize, Site) = .{},
    ptr_site: std.AutoHashMapUnmanaged(usize, usize) = .{},
    /// Snapshot of `sites` taken the last time `live` crossed a new 256 MiB
    /// high-water step (only with `--track-sites`). A doomed search frees
    /// everything on unwind, so the post-run live table attributes nothing;
    /// the snapshot is what attributes a *transient* peak (who held the
    /// bytes when memory was highest).
    peak_sites: std.AutoHashMapUnmanaged(usize, Site) = .{},
    peak_sites_live: u64 = 0,

    const snapshot_step: u64 = 256 << 20;

    const Site = struct {
        live: u64 = 0,
        allocs: u64 = 0,
    };

    fn allocator(self: *CountingAllocator) std.mem.Allocator {
        return .{
            .ptr = self,
            .vtable = &.{
                .alloc = alloc,
                .resize = resize,
                .remap = remap,
                .free = free,
            },
        };
    }

    fn add(self: *CountingAllocator, n: u64) void {
        const now = self.live.fetchAdd(n, .monotonic) + n;
        // Diagnostic tripwire (`--alloc-trap=MIB`): panic with a stack trace
        // the moment live bytes cross the threshold, to attribute a transient
        // peak to its real call chain (ret_addr attribution stops at the
        // ICF-folded ArrayList growth shims).
        if (self.trap_bytes != 0 and now > self.trap_bytes) {
            @panic("alloc trap: live bytes crossed --alloc-trap threshold");
        }
        var peak = self.peak.load(.monotonic);
        while (now > peak) {
            peak = self.peak.cmpxchgWeak(
                peak,
                now,
                .monotonic,
                .monotonic,
            ) orelse break;
        }
    }

    fn trackAlloc(
        self: *CountingAllocator,
        ptr: usize,
        len: usize,
        ret_addr: usize,
    ) void {
        if (!self.track_sites) return;
        self.mutex.lock();
        defer self.mutex.unlock();
        self.ptr_site.put(self.child, ptr, ret_addr) catch return;
        const entry = self.sites.getOrPutValue(
            self.child,
            ret_addr,
            .{},
        ) catch return;
        entry.value_ptr.live += len;
        entry.value_ptr.allocs += 1;
        const live_now = self.live.load(.monotonic);
        if (live_now >= self.peak_sites_live + snapshot_step) {
            self.snapshotPeakSites(live_now);
        }
    }

    /// Copy `sites` into `peak_sites` (mutex already held by the caller).
    fn snapshotPeakSites(self: *CountingAllocator, live_now: u64) void {
        self.peak_sites_live = live_now;
        self.peak_sites.clearRetainingCapacity();
        var iter = self.sites.iterator();
        while (iter.next()) |entry| {
            self.peak_sites.put(
                self.child,
                entry.key_ptr.*,
                entry.value_ptr.*,
            ) catch return;
        }
    }

    fn trackFree(self: *CountingAllocator, ptr: usize, len: usize) void {
        if (!self.track_sites) return;
        self.mutex.lock();
        defer self.mutex.unlock();
        const kv = self.ptr_site.fetchRemove(ptr) orelse return;
        if (self.sites.getPtr(kv.value)) |site| {
            site.live -|= len;
        }
    }

    fn trackResize(
        self: *CountingAllocator,
        old_ptr: usize,
        new_ptr: usize,
        old_len: usize,
        new_len: usize,
    ) void {
        if (!self.track_sites) return;
        self.mutex.lock();
        defer self.mutex.unlock();
        const kv = self.ptr_site.fetchRemove(old_ptr) orelse return;
        self.ptr_site.put(self.child, new_ptr, kv.value) catch return;
        if (self.sites.getPtr(kv.value)) |site| {
            site.live -|= old_len;
            site.live += new_len;
        }
    }

    /// Print the top sites by live bytes (call-site return addresses;
    /// symbolize with `addr2line -f -e search-bench ADDR...`).
    fn reportTopSites(self: *CountingAllocator, writer: anytype, n: usize) !void {
        self.mutex.lock();
        defer self.mutex.unlock();
        try reportSitesLocked(&self.sites, writer, n);
    }

    /// Print the top sites of the last peak snapshot (see `peak_sites`).
    fn reportPeakSites(self: *CountingAllocator, writer: anytype, n: usize) !void {
        self.mutex.lock();
        defer self.mutex.unlock();
        if (self.peak_sites_live == 0) return;
        try writer.print(
            "      -- sites at live snapshot {d} MiB --\n",
            .{self.peak_sites_live >> 20},
        );
        try reportSitesLocked(&self.peak_sites, writer, n);
    }

    fn reportSitesLocked(
        sites: *const std.AutoHashMapUnmanaged(usize, Site),
        writer: anytype,
        n: usize,
    ) !void {
        var shown: usize = 0;
        var threshold: u64 = std.math.maxInt(u64);
        while (shown < n) {
            var best_addr: usize = 0;
            var best: Site = .{};
            var iter = sites.iterator();
            while (iter.next()) |entry| {
                if (entry.value_ptr.live >= threshold) continue;
                if (best_addr == 0 or entry.value_ptr.live > best.live) {
                    best_addr = entry.key_ptr.*;
                    best = entry.value_ptr.*;
                }
            }
            if (best_addr == 0 or best.live == 0) break;
            try writer.print(
                "      site 0x{x}  live {d} MiB  allocs {d}\n",
                .{ best_addr, best.live >> 20, best.allocs },
            );
            threshold = best.live;
            shown += 1;
        }
        try writer.flush();
    }

    fn alloc(
        ctx: *anyopaque,
        len: usize,
        alignment: std.mem.Alignment,
        ret_addr: usize,
    ) ?[*]u8 {
        const self: *CountingAllocator = @ptrCast(@alignCast(ctx));
        const result = self.child.rawAlloc(len, alignment, ret_addr);
        if (result) |ptr| {
            self.add(len);
            self.trackAlloc(@intFromPtr(ptr), len, ret_addr);
        }
        return result;
    }

    fn resize(
        ctx: *anyopaque,
        memory: []u8,
        alignment: std.mem.Alignment,
        new_len: usize,
        ret_addr: usize,
    ) bool {
        const self: *CountingAllocator = @ptrCast(@alignCast(ctx));
        if (!self.child.rawResize(memory, alignment, new_len, ret_addr)) {
            return false;
        }
        if (new_len >= memory.len) {
            self.add(new_len - memory.len);
        } else {
            _ = self.live.fetchSub(memory.len - new_len, .monotonic);
        }
        self.trackResize(
            @intFromPtr(memory.ptr),
            @intFromPtr(memory.ptr),
            memory.len,
            new_len,
        );
        return true;
    }

    fn remap(
        ctx: *anyopaque,
        memory: []u8,
        alignment: std.mem.Alignment,
        new_len: usize,
        ret_addr: usize,
    ) ?[*]u8 {
        const self: *CountingAllocator = @ptrCast(@alignCast(ctx));
        const result =
            self.child.rawRemap(memory, alignment, new_len, ret_addr) orelse
            return null;
        if (new_len >= memory.len) {
            self.add(new_len - memory.len);
        } else {
            _ = self.live.fetchSub(memory.len - new_len, .monotonic);
        }
        self.trackResize(
            @intFromPtr(memory.ptr),
            @intFromPtr(result),
            memory.len,
            new_len,
        );
        return result;
    }

    fn free(
        ctx: *anyopaque,
        memory: []u8,
        alignment: std.mem.Alignment,
        ret_addr: usize,
    ) void {
        const self: *CountingAllocator = @ptrCast(@alignCast(ctx));
        self.child.rawFree(memory, alignment, ret_addr);
        _ = self.live.fetchSub(memory.len, .monotonic);
        self.trackFree(@intFromPtr(memory.ptr), memory.len);
    }
};

var counting_allocator = CountingAllocator{
    .child = std.heap.smp_allocator,
};

/// Current and peak resident set size from /proc/self/status (Linux only;
/// zeros elsewhere). Used to attribute depth-mode memory growth to per-call
/// peaks vs. cross-call accumulation (META_STRESS.md open thread 1).
const RssSample = struct {
    rss_kib: u64 = 0,
    hwm_kib: u64 = 0,
};

fn sampleRss() RssSample {
    var sample = RssSample{};
    var buf: [4096]u8 = undefined;
    const data = std.fs.cwd().readFile("/proc/self/status", &buf) catch
        return sample;
    var lines = std.mem.splitScalar(u8, data, '\n');
    while (lines.next()) |line| {
        if (std.mem.startsWith(u8, line, "VmRSS:")) {
            sample.rss_kib = parseStatusKib(line);
        } else if (std.mem.startsWith(u8, line, "VmHWM:")) {
            sample.hwm_kib = parseStatusKib(line);
        }
    }
    return sample;
}

fn parseStatusKib(line: []const u8) u64 {
    var it = std.mem.tokenizeAny(u8, line, " \t");
    _ = it.next();
    const num = it.next() orelse return 0;
    return std.fmt.parseInt(u64, num, 10) catch 0;
}

/// One ablated search invocation. `human` is the normalized original
/// application text (for the top-1 ranking signal); errors are reported as
/// outcomes, not failures of the harness.
fn runFrontierSearch(
    allocator: std.mem.Allocator,
    arena: std.mem.Allocator,
    mm0_src: []const u8,
    spliced: Spliced,
    human: []const u8,
    options: BenchOptions,
) FrontierRun {
    // The search-reuse memos are Driver-owned now (see `generateTopLevel`); the
    // Driver attaches its memo to this counters block and snapshots its stats
    // back into the scalar fields before returning, so we just read them after.
    // `collect` turns on the per-candidate diagnostics the bench reports (off in
    // production, where the counters block exists only as the memo carrier).
    var counters = Search.SearchCounters{ .collect = true };
    const run_start = std.time.nanoTimestamp();
    var suggestions = Search.suggestionsAtSourceOffset(
        allocator,
        mm0_src,
        spliced.text,
        spliced.offset,
        .{
            .max_results = 3,
            .exact_result_limit = 1,
            .counters = &counters,
            .generate = frontierGenerateOptions(options),
        },
    ) catch |err| {
        return .{
            .found = false,
            .top1_match = false,
            .search_ns = counters.warm_search_ns,
            .wall_ns = elapsedSince(run_start),
            .err = err,
            .counters = counters,
        };
    };
    defer suggestions.deinit();
    const wall_ns = elapsedSince(run_start);

    var top1_match = false;
    if (suggestions.items.len > 0) {
        const top = normalizeWhitespace(
            arena,
            suggestions.items[0].replacement,
        ) catch "";
        top1_match = std.mem.eql(u8, top, human);
    }
    return .{
        .found = suggestions.items.len > 0,
        .top1_match = top1_match,
        .search_ns = counters.warm_search_ns,
        .wall_ns = wall_ns,
        .counters = counters,
    };
}

/// One-line key-counter summary for a MISS/SLOW breadth row, plus the top
/// rules by full-validation attempts — the data the major/minor premise
/// policy question needs (META_STRESS.md workstream 2).
fn printRunCounters(writer: anytype, counters: *const Search.SearchCounters) !void {
    try writer.print(
        "       tc={} acc={} rej={} chain={} pool={} derived={} " ++
            "fwd_attempts={} abstract_prune={} context_prune={} hyp_ref_prune={} acui_rb={}/{} tc_apply=",
        .{
            counters.full_try_candidate_calls,
            counters.accepted_candidates,
            counters.rejected_candidates_after_validation,
            counters.generated_chain_attempts,
            counters.ref_pool_size,
            counters.derived_ref_count,
            counters.forward_rule_attempts,
            counters.abstract_prunes,
            counters.context_prunes,
            counters.hyp_ref_prunes,
            counters.readback_acui_recovered,
            counters.readback_acui_misalign,
        },
    );
    try printDurationCompact(writer, counters.tc_apply_ns);
    try writer.print("  shape_emit={}(rule {}) cache(hit={} miss={}) in ", .{
        counters.shape_emissions,
        counters.rule_shape_emissions,
        counters.shape_cache_hits,
        counters.shape_cache_misses,
    });
    try printDurationCompact(writer, counters.shape_emission_ns);
    try writer.writeAll(" ref_lookup ");
    try printDurationCompact(writer, counters.ref_lookup_ns);
    try writer.writeAll(" idx_build ");
    try printDurationCompact(writer, counters.ref_index_build_ns);
    try writer.writeAll("  top rules: ");
    const diags =
        counters.rule_attempt_diagnostics[0..counters.rule_attempt_diagnostics_len];
    var shown: usize = 0;
    var threshold: usize = std.math.maxInt(usize);
    while (shown < 3) {
        var best: ?usize = null;
        var best_attempts: usize = 0;
        for (diags, 0..) |diag, i| {
            if (diag.attempts >= threshold) continue;
            if (best == null or diag.attempts > best_attempts) {
                best = i;
                best_attempts = diag.attempts;
            }
        }
        const idx = best orelse break;
        try writer.print("{s}={}/{} ", .{
            diags[idx].rule_name.slice(),
            diags[idx].attempts,
            diags[idx].rejected,
        });
        threshold = diags[idx].attempts;
        shown += 1;
    }
    const vt = counters.verdict_reject_total;
    const vd = counters.verdict_reject_distinct;
    const repeat_pct: u64 = if (vt == 0) 0 else (vt - vd) * 100 / vt;
    try writer.print(
        "\n       verdict: rej_total={} distinct={} repeat={}% skips={}",
        .{ vt, vd, repeat_pct, counters.verdict_skips },
    );
    try writer.print(
        "  repin: would_prune={} prunes={}",
        .{ counters.repin_would_prune, counters.repin_prunes },
    );
    try writer.print(
        "  deep_member: calls={} would_prune={} prunes={} cache(hit={} miss={})",
        .{
            counters.deep_member_calls,
            counters.deep_member_would_prune,
            counters.deep_member_prunes,
            counters.deep_cache_hits,
            counters.deep_cache_misses,
        },
    );
    try writer.print(
        "  persist_skips: conc={} open={}",
        .{
            counters.persist_concrete_skips,
            counters.persist_open_skips,
        },
    );
    try writer.writeAll("\n");
}

const BreadthStats = struct {
    tried: usize = 0,
    found: usize = 0,
    matched: usize = 0,
    errors: usize = 0,
    slow: usize = 0,
    search_ns_sum: u64 = 0,
    search_ns_max: u64 = 0,
    wall_ns_sum: u64 = 0,

    fn add(self: *BreadthStats, other: BreadthStats) void {
        self.tried += other.tried;
        self.found += other.found;
        self.matched += other.matched;
        self.errors += other.errors;
        self.slow += other.slow;
        self.search_ns_sum += other.search_ns_sum;
        self.search_ns_max = @max(self.search_ns_max, other.search_ns_max);
        self.wall_ns_sum += other.wall_ns_sum;
    }
};

/// Outcome of a single depth-frontier search at one k. The terminating
/// `.miss`/`.err` run at each theorem's frontier+1 is the worst-case `auto?`
/// *failure* latency — the search that burns the full budget proving nothing.
const DepthRunStatus = enum { found, miss, err };

const DepthStats = struct {
    theorems: usize = 0,
    frontier_sum: usize = 0,
    /// Theorems whose whole tail (every line before the last) regenerates.
    full: usize = 0,
    /// Theorems whose final line is unfound even with the full pool (k=0).
    zero: usize = 0,
    runs: usize = 0,
    max_frontier: usize = 0,
    wall_ns_sum: u64 = 0,
    /// Slowest single search across ALL runs, regardless of outcome. The
    /// per-theorem report only ever showed the slowest *successful* search, so
    /// a slow MISS/ERR was invisible without `--verbose`; this surfaces it.
    search_ns_max: u64 = 0,
    /// Auto-FAILURE latency: the terminating MISS/ERR search of each non-FULL
    /// theorem. Separated from success cost because this is the latency a user
    /// actually waits through when `auto?` cannot close the goal.
    fail_runs: usize = 0,
    fail_ns_sum: u64 = 0,
    fail_ns_max: u64 = 0,
    /// Attribution of the single slowest search (any outcome) for the report.
    /// `slowest_label` is owned by the caller's long-lived allocator (the
    /// per-fixture arena that produced `block.name` is freed before the
    /// fixture stats are merged into the totals).
    slowest_ns: u64 = 0,
    slowest_k: usize = 0,
    slowest_status: DepthRunStatus = .found,
    slowest_label: []const u8 = "",
    /// Slowest *successful* search — the load-bearing number for any global
    /// per-call budget/latency cap (a FOUND search must not be truncated), and
    /// the frontier-preserving floor when triaging outliers.
    slowest_found_ns: u64 = 0,
    slowest_found_k: usize = 0,
    slowest_found_label: []const u8 = "",
    /// Cost-budget calibration: the largest tick consumption of any FOUND
    /// search (the floor a per-call `GlobalBudget` must clear to preserve the
    /// frontier) and of any failing search (what the budget would cut).
    found_ticks_max: u64 = 0,
    found_ticks_k: usize = 0,
    found_ticks_label: []const u8 = "",
    fail_ticks_max: u64 = 0,

    /// Fold one search outcome into the per-fixture stats. `label` may point
    /// into the fixture arena; it is only retained as a borrowed slice and
    /// must be duplicated into a long-lived allocator before the arena dies.
    fn observe(
        self: *DepthStats,
        label: []const u8,
        k: usize,
        status: DepthRunStatus,
        search_ns: u64,
        ticks: u64,
    ) void {
        self.runs += 1;
        self.search_ns_max = @max(self.search_ns_max, search_ns);
        if (status != .found) {
            self.fail_runs += 1;
            self.fail_ns_sum += search_ns;
            self.fail_ns_max = @max(self.fail_ns_max, search_ns);
            self.fail_ticks_max = @max(self.fail_ticks_max, ticks);
        }
        if (search_ns > self.slowest_ns) {
            self.slowest_ns = search_ns;
            self.slowest_k = k;
            self.slowest_status = status;
            self.slowest_label = label;
        }
        if (status == .found and search_ns > self.slowest_found_ns) {
            self.slowest_found_ns = search_ns;
            self.slowest_found_k = k;
            self.slowest_found_label = label;
        }
        if (status == .found and ticks > self.found_ticks_max) {
            self.found_ticks_max = ticks;
            self.found_ticks_k = k;
            self.found_ticks_label = label;
        }
    }

    fn add(self: *DepthStats, other: DepthStats) void {
        self.theorems += other.theorems;
        self.frontier_sum += other.frontier_sum;
        self.full += other.full;
        self.zero += other.zero;
        self.runs += other.runs;
        self.max_frontier = @max(self.max_frontier, other.max_frontier);
        self.wall_ns_sum += other.wall_ns_sum;
        self.search_ns_max = @max(self.search_ns_max, other.search_ns_max);
        self.fail_runs += other.fail_runs;
        self.fail_ns_sum += other.fail_ns_sum;
        self.fail_ns_max = @max(self.fail_ns_max, other.fail_ns_max);
        if (other.slowest_ns > self.slowest_ns) {
            self.slowest_ns = other.slowest_ns;
            self.slowest_k = other.slowest_k;
            self.slowest_status = other.slowest_status;
            self.slowest_label = other.slowest_label;
        }
        if (other.slowest_found_ns > self.slowest_found_ns) {
            self.slowest_found_ns = other.slowest_found_ns;
            self.slowest_found_k = other.slowest_found_k;
            self.slowest_found_label = other.slowest_found_label;
        }
        if (other.found_ticks_max > self.found_ticks_max) {
            self.found_ticks_max = other.found_ticks_max;
            self.found_ticks_k = other.found_ticks_k;
            self.found_ticks_label = other.found_ticks_label;
        }
        self.fail_ticks_max = @max(self.fail_ticks_max, other.fail_ticks_max);
    }
};

/// Returns `true` if a breadth run is not clean: a MISS, an ERR, or nothing
/// exercised at all (`tried == 0`, which means a `--filter`/`--files` typo
/// selected no lines — caught here so a misconfigured `--require-no-miss`
/// guard can't pass vacuously). Depth mode has no pass/fail notion and always
/// returns `false`.
// ===========================================================================
// Discrimination / scaling sweep (META_STRESS.md bespoke theory #4)
// ===========================================================================

/// Parse `--sweep=FAMILY[:N1,N2,...]`. Omitting the point list uses a default
/// geometric ladder so a quick run still shows the curve.
fn parseSweepSpec(allocator: std.mem.Allocator, spec: []const u8) !SweepSpec {
    const colon = std.mem.indexOfScalar(u8, spec, ':');
    const family_text = if (colon) |c| spec[0..c] else spec;
    const family = std.meta.stringToEnum(SweepFamily, family_text) orelse {
        std.debug.print("unknown sweep family: {s}\n", .{family_text});
        try printUsage();
        return error.InvalidArgument;
    };
    var points = std.ArrayListUnmanaged(usize){};
    if (colon) |c| {
        var it = std.mem.splitScalar(u8, spec[c + 1 ..], ',');
        while (it.next()) |tok| {
            if (tok.len == 0) continue;
            try points.append(allocator, try std.fmt.parseInt(usize, tok, 10));
        }
    }
    if (points.items.len == 0) {
        try points.appendSlice(allocator, &.{ 8, 16, 32, 64, 128, 256, 512 });
    }
    return .{ .family = family, .points = try points.toOwnedSlice(allocator) };
}

const GeneratedSweep = struct {
    mm0: []const u8,
    spliced: Spliced,
};

/// Build a synthetic distractor theory with `n` distractors and a fixed,
/// deliberately-unprovable probe goal, plus the spliced single-line proof with
/// the search marker. Returned text is owned by `arena`; reuses the ordinary
/// `runFrontierSearch` path so timing/counters are measured identically to the
/// real corpus.
fn generateSweep(
    arena: std.mem.Allocator,
    family: SweepFamily,
    n: usize,
    marker: []const u8,
) !GeneratedSweep {
    var mm0_buf = std.ArrayListUnmanaged(u8){};
    const w = mm0_buf.writer(arena);
    try w.writeAll(
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\sort obj;
        \\term Goal (x: obj): wff;
        \\term K: obj;
        \\
    );
    switch (family) {
        .head_distinct => {
            // One real rule for the goal head (so the index returns exactly it,
            // proving the N distractors are filtered, not merely absent); its
            // hyp `Pre K` is unprovable, keeping the probe unsolvable.
            try w.writeAll("term Pre (x: obj): wff;\n");
            try w.writeAll("axiom real (x: obj): $ Pre x $ > $ Goal x $;\n");
            var i: usize = 0;
            while (i < n) : (i += 1) {
                try w.print("term D{d} (x: obj): wff;\n", .{i});
                try w.print(
                    "axiom dist{d} (x: obj): $ Goal x $ > $ D{d} x $;\n",
                    .{ i, i },
                );
            }
        },
        .head_shared => {
            var i: usize = 0;
            while (i < n) : (i += 1) {
                try w.print("term Q{d} (x: obj): wff;\n", .{i});
                try w.print(
                    "axiom share{d} (x: obj): $ Q{d} x $ > $ Goal x $;\n",
                    .{ i, i },
                );
            }
        },
        .ref_fanout => {
            try w.writeAll("term Inner (x: obj): wff;\n");
            try w.writeAll("term Tag (x: obj): wff;\n");
            var i: usize = 0;
            while (i < n) : (i += 1) {
                try w.print("term C{d}: obj;\n", .{i});
            }
            // `a` is open in hyp 1 (wildcard arg → all N `Inner C_i` refs bucket
            // together), then hyp 2 `Tag a` has no satisfying ref → reject.
            try w.writeAll(
                "axiom use (a: obj): $ Inner a $ > $ Tag a $ > $ Goal K $;\n",
            );
        },
    }

    // Probe theorem last, so all distractors precede it in the pool.
    if (family == .ref_fanout) {
        try w.writeAll("theorem probe:");
        var i: usize = 0;
        while (i < n) : (i += 1) try w.print(" $ Inner C{d} $ >", .{i});
        try w.writeAll(" $ Goal K $;\n");
    } else {
        try w.writeAll("theorem probe: $ Goal K $;\n");
    }

    var auf = std.ArrayListUnmanaged(u8){};
    const aw = auf.writer(arena);
    try aw.writeAll("probe\n-----\nl1: $ Goal K $ by ");
    const offset = auf.items.len;
    try aw.writeAll(marker);
    try aw.writeAll("\n");

    return .{
        .mm0 = mm0_buf.items,
        .spliced = .{ .text = auf.items, .offset = offset },
    };
}

/// Run the sweep: for each N, time the probe search (min of a few repeats to
/// damp noise) and print the time-vs-N curve alongside the discrimination
/// counters that explain its shape. Catches superlinear blowups a fixed corpus
/// hides (META_STRESS.md theory #4).
fn runSweep(
    allocator: std.mem.Allocator,
    writer: anytype,
    options: BenchOptions,
) !void {
    const spec = options.sweep.?;
    try writer.print(
        "sweep family={s} marker={s} points={d}\n",
        .{ @tagName(spec.family), options.marker, spec.points.len },
    );
    try writer.print(
        "{s:>7} {s:>11} {s:>8} {s:>5} {s:>10} {s:>8} {s:>9} {s:>6} {s:>6}\n",
        .{ "N", "search", "growth", "found", "candRules", "refRefs", "genChain", "tc", "rej" },
    );
    try writer.flush();

    const repeats: usize = 5;
    var prev_n: usize = 0;
    var prev_ns: u64 = 0;
    for (spec.points) |n| {
        var arena_state = std.heap.ArenaAllocator.init(allocator);
        defer arena_state.deinit();
        const arena = arena_state.allocator();

        var best_ns: u64 = std.math.maxInt(u64);
        var last: FrontierRun = undefined;
        var r: usize = 0;
        while (r < repeats) : (r += 1) {
            const gen = try generateSweep(arena, spec.family, n, options.marker);
            const run = runFrontierSearch(
                allocator,
                arena,
                gen.mm0,
                gen.spliced,
                "",
                options,
            );
            if (run.err) |err| {
                try writer.print(
                    "{d:>7}  ERR {s}\n",
                    .{ n, @errorName(err) },
                );
                try writer.flush();
                best_ns = 0;
                last = run;
                break;
            }
            best_ns = @min(best_ns, run.search_ns);
            last = run;
        }
        if (last.err != null) continue;

        // Growth factor vs the previous point, normalized to N's growth: ~1.0 is
        // linear, <1 sublinear/flat, >1 superlinear. (Blank on the first row.)
        var growth_buf: [16]u8 = undefined;
        const growth: []const u8 = if (prev_n != 0 and prev_ns != 0) blk: {
            const time_ratio = @as(f64, @floatFromInt(best_ns)) /
                @as(f64, @floatFromInt(prev_ns));
            const n_ratio = @as(f64, @floatFromInt(n)) /
                @as(f64, @floatFromInt(prev_n));
            const norm = time_ratio / n_ratio;
            break :blk std.fmt.bufPrint(&growth_buf, "{d:.2}x", .{norm}) catch "?";
        } else "-";

        const c = last.counters;
        try writer.print("{d:>7} ", .{n});
        try printDurationCompact(writer, best_ns);
        try writer.print(
            " {s:>8} {s:>5} {d:>10} {d:>8} {d:>9} {d:>6} {d:>6}\n",
            .{
                growth,
                if (last.found) "yes" else "no",
                c.candidate_rules_before_conclusion_validation,
                c.per_hyp_filtered_ref_list_total,
                c.generated_chain_attempts,
                c.full_try_candidate_calls,
                c.rejected_candidates_after_validation,
            },
        );
        try writer.flush();
        prev_n = n;
        prev_ns = best_ns;
    }
}

fn runFrontier(
    allocator: std.mem.Allocator,
    writer: anytype,
    mode: FrontierMode,
    options: BenchOptions,
) !bool {
    const corpus: []const FixturePair = if (options.files.len > 0)
        options.files
    else
        &default_frontier_corpus;

    try writer.print(
        "frontier {s}: marker={s} max_depth={} fixtures={}\n",
        .{ @tagName(mode), options.marker, options.max_depth, corpus.len },
    );
    try writer.flush();

    switch (mode) {
        .breadth => {
            var totals = BreadthStats{};
            for (corpus) |fixture| {
                const stats = runBreadthFixture(
                    allocator,
                    writer,
                    fixture,
                    options,
                ) catch |err| {
                    try writer.print(
                        "{s}: fixture error: {s}\n",
                        .{ fixture.name, @errorName(err) },
                    );
                    continue;
                };
                totals.add(stats);
            }
            try writer.writeAll("\n");
            try printBreadthSummary(writer, "TOTAL", totals, options);
            return totals.found != totals.tried or totals.errors != 0 or
                totals.tried == 0;
        },
        .depth => {
            var totals = DepthStats{};
            for (corpus) |fixture| {
                const stats = runDepthFixture(
                    allocator,
                    writer,
                    fixture,
                    options,
                ) catch |err| {
                    try writer.print(
                        "{s}: fixture error: {s}\n",
                        .{ fixture.name, @errorName(err) },
                    );
                    continue;
                };
                totals.add(stats);
            }
            try writer.writeAll("\n");
            try printDepthSummary(writer, "TOTAL", totals);
            // Under `--require-no-miss`, a depth guard demands every selected
            // theorem regenerate its *whole* proof (frontier == max_k, i.e.
            // FULL). Default runs (flag unset) never fail, matching prior
            // behaviour.
            return options.require_no_miss and
                (totals.theorems == 0 or totals.full != totals.theorems);
        },
    }
}

/// Iterate the proof blocks of a parsed .auf, skipping defs and recovering
/// from parse errors at item boundaries.
const BlockIterator = struct {
    parser: ProofScript.Parser,

    fn init(arena: std.mem.Allocator, src: []const u8) BlockIterator {
        return .{ .parser = ProofScript.Parser.init(arena, src) };
    }

    fn next(self: *BlockIterator) ?ProofScript.ProofBlock {
        while (true) {
            const item = self.parser.nextItem() catch {
                if (!self.parser.recoverToNextItemBoundary()) return null;
                continue;
            } orelse return null;
            switch (item) {
                .block => |block| return block,
                .def => continue,
            }
        }
    }
};

fn runBreadthFixture(
    allocator: std.mem.Allocator,
    writer: anytype,
    fixture: FixturePair,
    options: BenchOptions,
) !BreadthStats {
    const mm0_src = try std.fs.cwd().readFileAlloc(
        allocator,
        fixture.mm0_path,
        std.math.maxInt(usize),
    );
    defer allocator.free(mm0_src);
    const proof_src = try std.fs.cwd().readFileAlloc(
        allocator,
        fixture.proof_path,
        std.math.maxInt(usize),
    );
    defer allocator.free(proof_src);

    var stats = BreadthStats{};
    var arena_state = std.heap.ArenaAllocator.init(allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();

    var blocks = BlockIterator.init(arena, proof_src);
    while (blocks.next()) |block| {
        if (options.filter) |needle| {
            if (std.mem.indexOf(u8, block.name, needle) == null) continue;
        }
        for (block.lines) |line| {
            if (ProofScript.applicationHasSearchPlaceholder(
                line.application,
            )) continue;

            const app_span = line.application.span;
            const spliced = try spliceSource(
                arena,
                proof_src,
                &.{},
                app_span,
                options.marker,
            );
            const human = try normalizeWhitespace(
                arena,
                proof_src[app_span.start..app_span.end],
            );
            const run = runFrontierSearch(
                allocator,
                arena,
                mm0_src,
                spliced,
                human,
                options,
            );

            stats.tried += 1;
            stats.search_ns_sum += run.search_ns;
            stats.search_ns_max = @max(stats.search_ns_max, run.search_ns);
            stats.wall_ns_sum += run.wall_ns;
            if (run.found) stats.found += 1;
            if (run.top1_match) stats.matched += 1;
            const slow =
                run.search_ns > options.slow_ms * std.time.ns_per_ms;
            if (slow) stats.slow += 1;

            if (run.err) |err| {
                stats.errors += 1;
                try writer.print(
                    "  ERR  {s}/{s} {s}: {s}\n",
                    .{ fixture.name, block.name, line.label, @errorName(err) },
                );
            } else if (!run.found or slow or options.verbose) {
                const tag = if (!run.found)
                    "MISS"
                else if (slow)
                    "SLOW"
                else if (run.top1_match)
                    "ok  "
                else
                    "ok* ";
                try writer.print("  {s} {s}/{s} {s} ", .{
                    tag,
                    fixture.name,
                    block.name,
                    line.label,
                });
                try printDurationCompact(writer, run.search_ns);
                try writer.print(
                    "  by {s}\n",
                    .{truncateForRow(human, 70)},
                );
                if (options.counters and (!run.found or slow)) {
                    try printRunCounters(writer, &run.counters);
                }
            }
            try writer.flush();
        }
    }
    try printBreadthSummary(writer, fixture.name, stats, options);
    return stats;
}

fn printBreadthSummary(
    writer: anytype,
    label: []const u8,
    stats: BreadthStats,
    options: BenchOptions,
) !void {
    if (stats.tried == 0) {
        try writer.print("{s:<16} no lines tried\n", .{label});
        try writer.flush();
        return;
    }
    const found_pct =
        @as(f64, @floatFromInt(stats.found)) * 100.0 /
        @as(f64, @floatFromInt(stats.tried));
    const avg_ns = stats.search_ns_sum / stats.tried;
    try writer.print(
        "{s:<16} lines {d:>4}  found {d:>4} ({d:>5.1}%)  top1 {d:>4}  " ++
            "miss {d:>3}  err {d:>2}  slow>{d}ms {d:>3}  avg ",
        .{
            label,
            stats.tried,
            stats.found,
            found_pct,
            stats.matched,
            stats.tried - stats.found - stats.errors,
            stats.errors,
            options.slow_ms,
            stats.slow,
        },
    );
    try printDurationCompact(writer, avg_ns);
    try writer.writeAll("  max ");
    try printDurationCompact(writer, stats.search_ns_max);
    try writer.writeAll("  wall ");
    try printDurationCompact(writer, stats.wall_ns_sum);
    try writer.writeAll("\n");
    try writer.flush();
}

fn runDepthFixture(
    allocator: std.mem.Allocator,
    writer: anytype,
    fixture: FixturePair,
    options: BenchOptions,
) !DepthStats {
    const mm0_src = try std.fs.cwd().readFileAlloc(
        allocator,
        fixture.mm0_path,
        std.math.maxInt(usize),
    );
    defer allocator.free(mm0_src);
    const proof_src = try std.fs.cwd().readFileAlloc(
        allocator,
        fixture.proof_path,
        std.math.maxInt(usize),
    );
    defer allocator.free(proof_src);

    var stats = DepthStats{};
    var arena_state = std.heap.ArenaAllocator.init(allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();

    var blocks = BlockIterator.init(arena, proof_src);
    block_loop: while (blocks.next()) |block| {
        if (options.filter) |needle| {
            if (std.mem.indexOf(u8, block.name, needle) == null) continue;
        }
        if (block.lines.len == 0) continue;
        for (block.lines) |line| {
            if (ProofScript.applicationHasSearchPlaceholder(
                line.application,
            )) continue :block_loop;
        }

        const n = block.lines.len;
        const target = block.lines[n - 1];
        const max_k = n - 1;
        const human = try normalizeWhitespace(
            arena,
            proof_src[target.application.span.start..target.application.span.end],
        );

        var frontier: ?usize = null;
        var frontier_ns: u64 = 0;
        var last_err: ?anyerror = null;
        // The terminating MISS/ERR run: the worst-case `auto?` failure latency
        // for this theorem (`0` when the proof is FULL and never fails).
        var fail_ns: u64 = 0;
        var fail_status: DepthRunStatus = .found;
        var frontier_ticks: RunTicks = .{};
        var fail_ticks: RunTicks = .{};
        var k: usize = 0;
        while (k <= max_k) : (k += 1) {
            const removed = block.lines[n - 1 - k .. n - 1];
            const spliced = try spliceSource(
                arena,
                proof_src,
                removed,
                target.application.span,
                "auto?",
            );
            const run = runFrontierSearch(
                allocator,
                arena,
                mm0_src,
                spliced,
                human,
                options,
            );
            const status: DepthRunStatus = if (run.err != null)
                .err
            else if (run.found)
                .found
            else
                .miss;
            stats.observe(
                block.name,
                k,
                status,
                run.search_ns,
                RunTicks.of(&run.counters).weighted(),
            );
            stats.wall_ns_sum += run.wall_ns;
            if (options.verbose) {
                const rss = sampleRss();
                try writer.print(
                    "    {s} k={d:<2} {s} ",
                    .{
                        block.name,
                        k,
                        if (run.err != null)
                            "ERR  "
                        else if (run.found)
                            "found"
                        else
                            "MISS ",
                    },
                );
                try printDurationCompact(writer, run.search_ns);
                try printTicksCompact(writer, RunTicks.of(&run.counters));
                try writer.print(
                    "  rss {d} MiB  hwm {d} MiB  live {d} MiB  " ++
                        "live-peak {d} MiB\n",
                    .{
                        rss.rss_kib / 1024,
                        rss.hwm_kib / 1024,
                        counting_allocator.live.load(.monotonic) >> 20,
                        counting_allocator.peak.load(.monotonic) >> 20,
                    },
                );
                if (options.track_sites) {
                    try counting_allocator.reportTopSites(writer, 12);
                    try counting_allocator.reportPeakSites(writer, 12);
                }
                if (options.counters) {
                    try printRunCounters(writer, &run.counters);
                }
                try writer.flush();
            }
            if (run.err) |err| {
                last_err = err;
                fail_ns = run.search_ns;
                fail_ticks = RunTicks.of(&run.counters);
                fail_status = .err;
                break;
            }
            if (!run.found) {
                fail_ns = run.search_ns;
                fail_ticks = RunTicks.of(&run.counters);
                fail_status = .miss;
                break;
            }
            frontier = k;
            frontier_ns = run.search_ns;
            frontier_ticks = RunTicks.of(&run.counters);
        }

        stats.theorems += 1;
        if (frontier) |best| {
            stats.frontier_sum += best;
            stats.max_frontier = @max(stats.max_frontier, best);
            if (best == max_k) stats.full += 1;
        } else {
            stats.zero += 1;
        }

        // A zero frontier on a multi-line proof is still useful: k=0 means
        // the final application is recoverable from the full pool, but k=1
        // fails. Do not hide those cases from the non-verbose report.
        const zero_tail_gap = if (frontier) |best|
            best == 0 and max_k > 0
        else
            false;
        const interesting = frontier == null or frontier.? > 0 or
            zero_tail_gap;
        if (options.verbose or interesting) {
            if (frontier) |best| {
                try writer.print(
                    "  {s}/{s:<28} frontier {d:>2}/{d:<3}{s} ",
                    .{
                        fixture.name,
                        block.name,
                        best,
                        max_k,
                        if (best == max_k) " FULL" else "",
                    },
                );
                try printDurationCompact(writer, frontier_ns);
                try printTicksCompact(writer, frontier_ticks);
                // The frontier+1 MISS/ERR is the failure a user waits through;
                // show it so a slow failure is not hidden behind the (fast)
                // last success. FULL theorems never fail, so there is none.
                if (fail_status != .found) {
                    try writer.print("  fail({s} k={d}) ", .{
                        @tagName(fail_status),
                        best + 1,
                    });
                    try printDurationCompact(writer, fail_ns);
                    try printTicksCompact(writer, fail_ticks);
                }
                try writer.writeAll("\n");
            } else {
                try writer.print(
                    "  {s}/{s:<28} UNFOUND at k=0 ({s}) fail ",
                    .{
                        fixture.name,
                        block.name,
                        if (last_err) |err| @errorName(err) else "no proof",
                    },
                );
                try printDurationCompact(writer, fail_ns);
                try printTicksCompact(writer, fail_ticks);
                try writer.writeAll("\n");
            }
            try writer.flush();
        }
    }
    // `stats.slowest_label` currently borrows `block.name` from `arena`, which
    // is freed when this function returns (before the totals merge). Re-root it
    // in the long-lived `allocator` so the global summary can name it.
    if (stats.slowest_label.len > 0) {
        stats.slowest_label = try allocator.dupe(u8, stats.slowest_label);
    }
    if (stats.slowest_found_label.len > 0) {
        stats.slowest_found_label = try allocator.dupe(u8, stats.slowest_found_label);
    }
    if (stats.found_ticks_label.len > 0) {
        stats.found_ticks_label = try allocator.dupe(u8, stats.found_ticks_label);
    }
    try printDepthSummary(writer, fixture.name, stats);
    return stats;
}

fn printDepthSummary(
    writer: anytype,
    label: []const u8,
    stats: DepthStats,
) !void {
    if (stats.theorems == 0) {
        try writer.print("{s:<16} no theorems tried\n", .{label});
        try writer.flush();
        return;
    }
    const mean =
        @as(f64, @floatFromInt(stats.frontier_sum)) /
        @as(f64, @floatFromInt(stats.theorems));
    try writer.print(
        "{s:<16} theorems {d:>3}  mean frontier {d:.2}  max {d}  " ++
            "full {d}  unfound@0 {d}  runs {d}  wall ",
        .{
            label,
            stats.theorems,
            mean,
            stats.max_frontier,
            stats.full,
            stats.zero,
            stats.runs,
        },
    );
    try printDurationCompact(writer, stats.wall_ns_sum);
    try writer.writeAll("\n");

    // Failure latency: the cost a user actually waits through when `auto?`
    // gives up. Reported separately from the success/frontier numbers above
    // because the depth report otherwise only ever shows successful searches.
    try writer.print("{s:<16} fail runs {d:>3}  fail-mean ", .{
        label,
        stats.fail_runs,
    });
    const fail_mean = if (stats.fail_runs == 0)
        0
    else
        stats.fail_ns_sum / stats.fail_runs;
    try printDurationCompact(writer, fail_mean);
    try writer.writeAll("  fail-max ");
    try printDurationCompact(writer, stats.fail_ns_max);
    try writer.writeAll("  slowest-search ");
    try printDurationCompact(writer, stats.slowest_ns);
    if (stats.slowest_label.len > 0) {
        try writer.print(" ({s} {s} k={d})", .{
            stats.slowest_label,
            @tagName(stats.slowest_status),
            stats.slowest_k,
        });
    }
    try writer.writeAll("  slowest-found ");
    try printDurationCompact(writer, stats.slowest_found_ns);
    if (stats.slowest_found_label.len > 0) {
        try writer.print(" ({s} k={d})", .{
            stats.slowest_found_label,
            stats.slowest_found_k,
        });
    }
    try writer.writeAll("\n");

    // Budget calibration: the found-ticks max is the floor a per-call
    // `GlobalBudget` must clear to preserve this fixture's frontier; the
    // fail-ticks max is what an uncapped failing search burns.
    try writer.print("{s:<16} found-ticks-max t={d:>7.2}M", .{
        label,
        @as(f64, @floatFromInt(stats.found_ticks_max)) / 1e6,
    });
    if (stats.found_ticks_label.len > 0) {
        try writer.print(" ({s} k={d})", .{
            stats.found_ticks_label,
            stats.found_ticks_k,
        });
    }
    try writer.print("  fail-ticks-max t={d:>7.2}M\n", .{
        @as(f64, @floatFromInt(stats.fail_ticks_max)) / 1e6,
    });
    try writer.flush();
}
