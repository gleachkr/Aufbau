//! Proof-search scenarios: one search marker in a small fixture each, and
//! what its search must return. `src/frontend/tests/search_scenarios.zig`
//! runs every scenario as a unit test (part of `zig build test-unit`), and
//! `zig build bench-search` times them. Fixtures live in
//! `tests/search_bench_cases/`.

const std = @import("std");
const Search = @import("mm0").CompilerSupport.Search;

pub const Scenario = struct {
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

pub const scenarios = [_]Scenario{
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
            "(G := $ p ∧ q $, H := $ p ∧ q $) " ++
            "[and_elim_r [ax []], and_elim_l [ax []]]]",
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
        // the concrete target is closed by `ax []`, and the witness is printed
        // as an explicit binding. Was the "no result, Stage 5" probe before
        // member enumeration landed.
        .name = "zermelo nd_exists_intro_mem auto? (Stage 5 ACUI witness)",
        .mm0_path = "tests/search_bench_cases/zermelo_exists_intro_stage5.mm0",
        .proof_path = "tests/search_bench_cases/nd_exists_intro_mem_auto.auf",
        .marker = "auto?",
        // The search validates the inline `ex_intro` with its `@recover`
        // pattern binder `p` given (bottom-up, `∃ x p` can't be rebuilt from
        // `t` alone), but the whole line re-infers `p` from the goal, and the
        // checker recovers the witness from `ax []`, so no binding is printed.
        .expected_replacement = "imp_intro [ex_intro [ax []]]",
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
        // No binding is printed: the whole line re-infers the repeated-meta
        // body `?t ∈ ?t` → `x ∈ x` from the goal, and the witness from `ax []`.
        .expected_replacement = "imp_intro [ex_intro [ax []]]",
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
        .expected_replacement = "ex_intro (t := $ A $) [tag_member []]",
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
        .mm0_path = "tests/search_bench_cases/martin_lof_regular.mm0",
        .proof_path = "tests/search_bench_cases/ml_add_comm_idtrans_auto.auf",
        .marker = "auto?",
        .expected_replacement = "id_trans_ty [l14, l19]",
        .generate = .{ .enabled = true, .max_depth = 6 },
    },
    .{
        // martin_lof add_comm capstone: `nat_ind_elim` whose induction motive
        // is not pinned by the conclusion (higher-order). Besides citing the
        // motive `l5`, the search also generates it (`Id_form [l3, l4]`),
        // opening the def's hidden `k` at that premise.
        .name = "auto martin_lof add_comm capstone auto? (no result)",
        .mm0_path = "tests/search_bench_cases/martin_lof_regular.mm0",
        .proof_path = "tests/search_bench_cases/ml_add_comm_capstone_auto.auf",
        .marker = "auto?",
        .expected_replacement = "",
        .generate = .{ .enabled = true, .max_depth = 6 },
        .expect_result = false,
        .expected_suggestion_count = 4,
    },
    .{
        // martin_lof add_comm with the step case's last nine lines removed
        // (the depth frontier's k=9 cut). `nat_ind_elim`'s base premise
        // `g ⊢ z : [k/zero] C` opens the def's hidden `k`, which the
        // substitution reduces away, so the pool rung names it at once
        // (the fully-solved check in `open_slot.emitOpenTarget`). A child
        // search there first,
        // which never names it, spends the budget the step case needs.
        .name = "auto martin_lof add_comm base case auto?",
        .mm0_path = "tests/search_bench_cases/martin_lof_frontier.mm0",
        .proof_path = "tests/search_bench_cases/ml_add_comm_base_case_auto.auf",
        .marker = "auto?",
        .expected_replacement = "nat_ind_elim [l7, l14, id_trans_ty [l18, l20, suc_intro [l23], " ++
            "add_ty [l15, l17, l19], l21, id_trans_ty [l18, suc_intro " ++
            "[l23], weaken [l7, suc_intro [l6]], add_ty [l15, l17, l19], " ++
            "ap_suc_ty [l15, l23, add_ty [l15, l17, l16], l22], id_sym_ty [l18, " ++
            "add_ty [l15, l17, l19], weaken [l7, suc_intro [l6]], " ++
            "add_suc_right [l15, l17, l16]]]], #2]",
        .generate = .{ .enabled = true, .max_depth = 6 },
    },
    .{
        // add_comm with only the `g , k : Nat ⊢ …` lines left. The step
        // premise opens both `k` and `ih`; the first free `@vars` names
        // (sorted, `ih` before `k`) would swap them, and no line would fit.
        // The pool rung names them after the lines instead
        // (`open_slot.assignRefNames`).
        .name = "auto martin_lof add_comm step names auto?",
        .mm0_path = "tests/search_bench_cases/martin_lof_frontier.mm0",
        .proof_path = "tests/search_bench_cases/ml_add_comm_step_names_auto.auf",
        .marker = "auto?",
        .expected_replacement = "nat_ind_elim [Id_form [l5, l6], id_trans_ty [l1, add_ty [#1, " ++
            "zero_intro [#1], #3], #3, add_ty [#1, #3, zero_intro [#1]], " ++
            "add_zero_left_path [#1, #3], id_sym_ty [l1, add_ty [#1, #3, " ++
            "zero_intro [#1]], #3, add_zero_right [#1, #3]]], id_trans_ty " ++
            "[nat_form [ext_ok [l2, Id_form [l5, l6]]], add_ty [ext_ok [l2, " ++
            "Id_form [l5, l6]], weaken [Id_form [l5, l6], suc_intro [l3]], " ++
            "weaken [Id_form [l5, l6], l4]], weaken [Id_form [l5, l6], " ++
            "suc_intro [l5]], add_ty [ext_ok [l2, Id_form [l5, l6]], weaken " ++
            "[Id_form [l5, l6], l4], weaken [Id_form [l5, l6], suc_intro " ++
            "[l3]]], add_suc_left_path [ext_ok [l2, Id_form [l5, l6]], " ++
            "var_wk [l1, Id_form [l5, l6]], weaken [Id_form [l5, l6], l4]], " ++
            "id_trans_ty [nat_form [ext_ok [l2, Id_form [l5, l6]]], weaken " ++
            "[Id_form [l5, l6], suc_intro [l5]], weaken [Id_form [l5, l6], " ++
            "suc_intro [l6]], add_ty [ext_ok [l2, Id_form [l5, l6]], weaken " ++
            "[Id_form [l5, l6], l4], weaken [Id_form [l5, l6], suc_intro " ++
            "[l3]]], ap_suc_ty [ext_ok [l2, Id_form [l5, l6]], add_ty " ++
            "[ext_ok [l2, Id_form [l5, l6]], var_wk [l1, Id_form [l5, l6]], " ++
            "weaken [Id_form [l5, l6], l4]], add_ty [ext_ok [l2, Id_form " ++
            "[l5, l6]], weaken [Id_form [l5, l6], l4], var_wk [l1, Id_form " ++
            "[l5, l6]]], var [Id_form [l5, l6]]], id_sym_ty [nat_form " ++
            "[ext_ok [l2, Id_form [l5, l6]]], add_ty [ext_ok [l2, Id_form " ++
            "[l5, l6]], weaken [Id_form [l5, l6], l4], weaken [Id_form [l5, " ++
            "l6], suc_intro [l3]]], weaken [Id_form [l5, l6], suc_intro " ++
            "[l6]], weaken [Id_form [l5, l6], add_suc_right [l2, l4, " ++
            "l3]]]]], #2]",
        .generate = .{ .enabled = true, .max_depth = 6 },
    },
    .{
        // martin_lof add_comm: rebuild the WHOLE tail of the `id_trans` DAG
        // (l14, l16, l17, l18, l19) from a trimmed pool, then close l20. A
        // multi-step concrete regeneration that drives iterative deepening
        // toward its depth-6 ceiling. Deep-rebuild latency probe.
        .name = "auto martin_lof add_comm id_trans deep auto?",
        .mm0_path = "tests/search_bench_cases/martin_lof_regular.mm0",
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
        .mm0_path = "tests/search_bench_cases/martin_lof_regular.mm0",
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
        .expected_replacement = "mp [bi1 [], biid []]",
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
        // `P ?x` with `pred_K`, and the match-back pins x := K, which the
        // printed line leaves to the checker (it reads x off `pred_K`). Was the
        // "no result, Stage 4" probe before the open path landed.
        .name = "hyp-only witness auto? (Stage 4 open backward)",
        .mm0_path = "tests/search_bench_cases/metavariable_capabilities.mm0",
        .proof_path = "tests/search_bench_cases/meta_hyp_only_witness.auf",
        .marker = "auto?",
        .expected_replacement = "hyp_only_use [pred_K []]",
        .generate = .{ .enabled = true, .max_depth = 6 },
    },
    .{
        // STAGE 4 (generated child pins parent meta — SUPPORTED). Solving `C`
        // opens `N ?x` under `generated_child_parent`; the recursive child
        // opens `M ?x'` under `child_from_mark`, closes it with `mark_K`, and
        // the nested match-backs propagate K upward into both bindings (which
        // the printed line leaves to the checker).
        .name = "generated child pins parent auto? (Stage 4 open backward)",
        .mm0_path = "tests/search_bench_cases/metavariable_capabilities.mm0",
        .proof_path = "tests/search_bench_cases/meta_child_pins_parent.auf",
        .marker = "auto?",
        .expected_replacement = "generated_child_parent [child_from_mark [mark_K []]]",
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
        .expected_replacement = "repeated_unknown_use [left_K [], right_K []]",
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
        // witness t := 0 off the child conclusion. The printed witness uses
        // notation (`0` for the term `d0`) via the notation-aware
        // pretty-printer (a059e67).
        .name = "euclid ex_intro open witness auto? (Stage 4 open backward)",
        .mm0_path = "tests/search_bench_cases/euclid.mm0",
        .proof_path = "tests/search_bench_cases/euclid_ex_intro_open_auto.auf",
        .marker = "auto?",
        .expected_replacement = "ex_intro (t := $ 0 $) [eq_intro_nd []]",
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
        .expected_replacement = "plain_only_use [pred_K []]",
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
        // bound vars), of which the printed line keeps the inner `t` and `p`.
        // This was the "no result, Stage 7" probe before the forward layer
        // landed.
        .name = "all_elim forward instantiation auto? (Stage 7 forward)",
        .mm0_path = "tests/search_bench_cases/all_elim_forward.mm0",
        .proof_path = "tests/search_bench_cases/all_elim_forward.auf",
        .marker = "auto?",
        .expected_replacement = "all_elim [all_elim (t := $ u $, p := $ ∀ b (pair f a = pair f " ++
            "b → a = b) $) [#1]]",
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
        // consistently (?t := u, ?t2 := v). Printed with only the bindings
        // the checker needs, it reads the same as the Stage 7 proof.
        .name = "all_elim two-layer derived direct auto? (Stage 8 forward)",
        .mm0_path = "tests/search_bench_cases/all_elim_forward.mm0",
        .proof_path = "tests/search_bench_cases/all_elim_forward.auf",
        .marker = "auto?",
        .expected_replacement = "all_elim [all_elim (t := $ u $, p := $ ∀ b (pair f a = pair f " ++
            "b → a = b) $) [#1]]",
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
        .expected_replacement = "all_elim [all_elim (t := $ v $) [all_elim (t := $ u $, p := $ " ++
            "∀ a ∀ b (pair (pair g c) a = pair a b → c = b) $) [#1]]]",
        .generate = .{ .enabled = true, .max_depth = 6 },
    },
    .{
        // STAGE 8 realistic two-layer chain in the full euclid theory: the
        // goal is an instance of the ∀i∀j totality fact with the
        // intermediate single-instantiation line omitted, so both witnesses
        // must come from the forward layer's shared-hole two-layer recipe.
        // The inner `(t := $ a $)` form checks only with `sb_f_congr`: the
        // outer `all_elim` reads its `∀` through the unreduced substitution.
        .name = "euclid le_total two-layer instantiation auto? (Stage 8)",
        .mm0_path = "tests/search_bench_cases/euclid.mm0",
        .proof_path = "tests/search_bench_cases/euclid_le_total_auto.auf",
        .marker = "auto?",
        .expected_replacement = "all_elim [all_elim (t := $ a $) [l1]]",
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
        .expected_replacement = "le_iff_add [lt_implies_le_ax [and_elim_l [l1]]]",
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
        // directly; printed with only the bindings the checker needs, it reads
        // the same as the backward `@recover` route. Declared LAST in the .mm0 so it cannot serve as a lemma
        // for the composition theorems.
        .name = "fwd/bwd compose hilbert forward-direct auto? (Stage 7)",
        .mm0_path = "tests/search_bench_cases/forward_backward_compose.mm0",
        .proof_path = "tests/search_bench_cases/fwd_direct_probe.auf",
        .marker = "auto?",
        .expected_replacement = "all_elim [#1]",
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
        // STAGE 8 nested re-grounding guard. A six-fact transitivity chain
        // under a triple-nested ∀ hypothesis: every family fact derived from
        // the ∀ shares one universal meta per binder, so the goal's recipe
        // grounds the same `?z` at several nested layers (`… at z := j`
        // wrapping a minor premise that was itself `… at z := i`). The goal
        // fact is in the derived pool either way; the recipe only validates
        // when each layer's own pin wins over its ancestors' (innermost-wins
        // overlay in `forward.resolveRecipeValues`). The deeper forward budget
        // is what a chain this long needs (two layers per hop); five facts
        // succeed through a shallower route even without the fix.
        .name = "forward nested re-grounding chain auto? (Stage 8 recipe pins)",
        .mm0_path = "tests/search_bench_cases/forward_chain.mm0",
        .proof_path = "tests/search_bench_cases/forward_chain.auf",
        .marker = "auto?",
        .expected_replacement = "imp_elim [imp_elim [all_elim (t := $ j $) [all_elim (t := $ b " ++
            "$) [all_elim (t := $ a $) [#1]]], #2], imp_elim [imp_elim " ++
            "[all_elim (t := $ j $) [all_elim (t := $ d $) [all_elim (t := " ++
            "$ b $) [#1]]], imp_elim [imp_elim [all_elim (t := $ d $) " ++
            "[all_elim (t := $ c $) [all_elim (t := $ b $) [#1]]], #3], " ++
            "#4]], imp_elim [imp_elim [all_elim (t := $ j $) [all_elim (t " ++
            ":= $ e $) [all_elim (t := $ d $) [#1]]], #5], imp_elim " ++
            "[imp_elim [all_elim (t := $ j $) [all_elim (t := $ i $) " ++
            "[all_elim (t := $ e $) [#1]]], #6], #7]]]]",
        .generate = .{
            .enabled = true,
            .max_depth = 6,
            .forward = .{
                .max_forward_layers = 9,
                .max_forward_rule_attempts = 4096,
            },
        },
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

/// Runs the scenario's search. `counters` receives the search statistics.
pub fn run(
    allocator: std.mem.Allocator,
    io: std.Io,
    scenario: *const Scenario,
    counters: *Search.SearchCounters,
) !Search.SourceSuggestions {
    const cwd = std.Io.Dir.cwd();
    const mm0_src = try cwd.readFileAlloc(io, scenario.mm0_path, allocator, .unlimited);
    defer allocator.free(mm0_src);
    const proof_src = try cwd.readFileAlloc(io, scenario.proof_path, allocator, .unlimited);
    defer allocator.free(proof_src);
    const offset = std.mem.indexOf(u8, proof_src, scenario.marker) orelse {
        return error.MissingScenarioMarker;
    };
    return try Search.suggestionsAtSourceOffset(
        allocator,
        mm0_src,
        proof_src,
        offset,
        .{
            .max_results = scenario.max_results,
            .exact_result_limit = scenario.exact_result_limit,
            .counters = counters,
            .generate = scenario.generate,
        },
    );
}

/// Whether a search's result meets the scenario's expectations. On a miss,
/// writes why to `w` and returns false. A suggestion the binding oracle could
/// not trim is a miss too.
pub fn check(
    scenario: *const Scenario,
    suggestions: []const Search.SourceSuggestion,
    counters: *const Search.SearchCounters,
    w: *std.Io.Writer,
) std.Io.Writer.Error!bool {
    if (scenario.expect_result and
        !containsReplacement(suggestions, scenario.expected_replacement))
    {
        try w.print(
            "{s}: expected suggestion not found: {s}\n",
            .{ scenario.name, scenario.expected_replacement },
        );
        try printSuggestions(w, suggestions);
        return false;
    }
    if (scenario.expected_suggestion_count) |expected_count| {
        if (suggestions.len != expected_count) {
            try w.print(
                "{s}: expected {} suggestions, found {}\n",
                .{ scenario.name, expected_count, suggestions.len },
            );
            try printSuggestions(w, suggestions);
            return false;
        }
    }
    if (scenario.expect_saturation_exhausted) |expected_exhausted| {
        if (counters.forward_saturation_exhausted != expected_exhausted) {
            try w.print(
                "{s}: expected saturation exhausted = {}, got {}\n",
                .{ scenario.name, expected_exhausted, counters.forward_saturation_exhausted },
            );
            return false;
        }
    }
    if (scenario.expect_derived_refs) |expected_derived| {
        if (counters.derived_ref_count != expected_derived) {
            try w.print(
                "{s}: expected {} derived refs, got {}\n",
                .{ scenario.name, expected_derived, counters.derived_ref_count },
            );
            return false;
        }
    }
    if (counters.untrimmed != 0) {
        try w.print(
            "{s}: the binding oracle could not trim {} suggestion(s)\n",
            .{ scenario.name, counters.untrimmed },
        );
        return false;
    }
    return true;
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
    w: *std.Io.Writer,
    suggestions: []const Search.SourceSuggestion,
) std.Io.Writer.Error!void {
    for (suggestions) |item| {
        try w.print("  suggestion: {s}\n", .{item.replacement});
    }
}
