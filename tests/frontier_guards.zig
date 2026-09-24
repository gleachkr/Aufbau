//! Frontier regression guards run by `zig build test-frontier-smoke` (part of
//! `zig build test`). build.zig turns each entry into one `search-bench` run
//! with `--require-no-miss`, which exits nonzero on any MISS/ERR (or an empty
//! selection), failing the build. Several fixes (the `matchOneHypViaView`
//! ACUI split, the `shape.zig` index pre-filter) have no unit coverage; these
//! runs are their only automated check.
//!
//! Only current budgets and rationale live here. Dated measurements and
//! gap-closure history: docs/frontier_guard_history.md.

pub const FrontierGuard = struct {
    // null filter = run the WHOLE fixture (every theorem block). Used by the
    // fixture-total guards below, which lock in the FULL count across an
    // entire bespoke-stress fixture, not just one hand-picked line.
    filter: ?[]const u8 = null,
    files: []const u8,
    mode: []const u8 = "breadth",
    // Per-guard budget overrides (null = use the bench default). A guard for
    // a genuinely deep proof can raise these without affecting the global
    // search defaults (which must stay low — raising the global `max_depth`
    // destroys corpus wall-clock on doomed searches for no found-ness gain).
    max_depth: ?usize = null,
    gen_nodes: ?usize = null,
    gen_fuel: ?usize = null,
    global_budget: ?u64 = null,
    // Per-guard forward-saturation budget overrides (null = bench default).
    // Same rationale as the generation budgets: a guard for a genuinely deep
    // forward chain can raise these without touching the conservative global
    // forward defaults (which bound the no-result `forward_stress` case).
    fwd_facts: ?usize = null,
    fwd_attempts: ?usize = null,
    fwd_layers: ?usize = null,
};

pub const guards = [_]FrontierGuard{
    .{
        .filter = "exists_prime_factor",
        .files = "tests/proof_cases/euclid.mm0:tests/proof_cases/euclid.auf",
    },
    .{
        .filter = "cb_branch_fg_injective_mixed",
        .files = "tests/proof_cases/zermelo.mm0:tests/proof_cases/zermelo.auf",
    },
    // Additive two-sided sequent calculus: guards the ACUI bound-binder
    // slot-count fix (`imp_trans l6`, `de_morgan l5` were the breadth misses
    // it repaired) and the forced-member conclusion seed.
    .{
        .filter = "imp_trans",
        .files = "tests/search_bench_cases/additive_fol.mm0:tests/search_bench_cases/additive_fol.auf",
    },
    .{
        .filter = "de_morgan",
        .files = "tests/search_bench_cases/additive_fol.mm0:tests/search_bench_cases/additive_fol.auf",
    },
    // Depth guard: `de_morgan` must regenerate its WHOLE proof from the bare
    // goal (frontier FULL), which is the only automated check for
    // `tryPrincipalEnumerate` — the breadth guard above finds `de_morgan`
    // through the pool ref and never exercises principal enumeration.
    .{
        .filter = "de_morgan",
        .files = "tests/search_bench_cases/additive_fol.mm0:tests/search_bench_cases/additive_fol.auf",
        .mode = "depth",
    },
    // Depth guard for principal-formula fan-out
    // (`exact_acui.findAmbiguousPrincipal`): `shared_subgoal` must regenerate
    // its WHOLE proof from the bare goal at the default budget. Without
    // fan-out the loose two-premise `lim` search burns its fuel on doomed
    // tuples and stalls at frontier 4/9 — this is the only end-to-end guard
    // that the multi-premise principal selection stays effective.
    .{
        .filter = "shared_subgoal",
        .files = "tests/search_bench_cases/additive_fol.mm0:tests/search_bench_cases/additive_fol.auf",
        .mode = "depth",
    },
    // Depth guard for the idempotent principal-retention pass (phase 4,
    // `GenerationHook.allow_retain_principal` / `exact_split.buildEnumerator`).
    // This goal is provable ONLY by keeping the conjunction `A∧B` in `lan`'s
    // premise (a non-minimal ACUI complement `g , g = g`); minimal-complement
    // pinning dead-ends. The only automated check that generation explores the
    // non-minimal complement — breadth finds it through the pool ref and never
    // exercises the split enumerator's retention path.
    .{
        .filter = "idem_complement_probe",
        .files = "tests/search_bench_cases/idem_complement_probe.mm0:" ++
            "tests/search_bench_cases/idem_complement_probe.auf",
        .mode = "depth",
    },
    // Depth guard for carrying an open witness through generated steps
    // (`backtrack.carriesAncestorWitness`): `ex_intro`'s child search must
    // close `imp_intro`/`all_intro` premises that carry its witness meta.
    // Before the fix those premises went to the concrete solver, which
    // drops placeholders, so only a pool line fitting `imp_intro`'s
    // premise directly could close the chain.
    .{
        .filter = "witness_carry_probe",
        .files = "tests/search_bench_cases/witness_carry_probe.mm0:" ++
            "tests/search_bench_cases/witness_carry_probe.auf",
        .mode = "depth",
    },
    // Depth guard for open targets with several child proofs
    // (`generate.hookSolveOpen` offers each to the slot in turn): the first
    // child proof pins the witness to `all_intro`'s eigenvariable and the
    // parent must fall through to the next. At depth 3 it also needs the
    // eager steps on the open chain (`imp_intro`, `all_intro`) to keep
    // their parent's depth, as `hookSolve` does on a concrete one.
    .{
        .filter = "witness_retry_probe",
        .files = "tests/search_bench_cases/witness_retry_probe.mm0:" ++
            "tests/search_bench_cases/witness_retry_probe.auf",
        .mode = "depth",
        .max_depth = 3,
    },
    // Depth guard for carried-meta dependency bans
    // (`backtrack.banCarriedMetaDeps`, `MetaStore.dep_bans`): `all_intro`
    // carries `ex_intro`'s witness in its context, so the witness may not
    // mention the eigenvariable anywhere in that scope. Without the ban a
    // member pass deep inside pins it to the eigenvariable and stops.
    .{
        .filter = "eigenvariable_ban_probe",
        .files = "tests/search_bench_cases/eigenvariable_ban_probe.mm0:" ++
            "tests/search_bench_cases/eigenvariable_ban_probe.auf",
        .mode = "depth",
    },
    // Depth guard for the eager cut's eigenvariable check
    // (`backtrack.bindingsBreakRuleDeps`): an eager `all_intro` over a
    // context that mentions `y` free can never validate, and must not arm
    // the cut that would skip `raa`.
    .{
        .filter = "eager_cut_dep_probe",
        .files = "tests/search_bench_cases/eager_cut_dep_probe.mm0:" ++
            "tests/search_bench_cases/eager_cut_dep_probe.auf",
        .mode = "depth",
    },
    // Depth guard for additive split ordering (`split.conclusionIsSplit`):
    // `not_left`'s `g , ¬ a` has one context binder, so the eager rule
    // sorts ahead of `raa` and its cut applies. Counted as multiplicative,
    // `raa`'s `¬ ⊥` detours spend the node budget and the empty-pool
    // drinker (k=9) misses.
    .{
        .filter = "empty_pool_witness_probe",
        .files = "tests/search_bench_cases/empty_pool_witness_probe.mm0:" ++
            "tests/search_bench_cases/empty_pool_witness_probe.auf",
        .mode = "depth",
    },
    // Depth guards for the success transposition memo (`generate.zig`
    // `Driver.concrete_ok`). `branch_converge` and `fan_in` are the convergent
    // (DAG-shaped) additive proofs whose shared subgoals the memo collapses;
    // without it they need ~40× the node/fuel budget. The memo keys subgoals
    // by an ACUI-canonical form, so commuted-context subgoals share a slot too.
    // They are genuinely deep (proof depth ≥ 9), so the global default
    // (`max_depth = 6`) cannot reach them — and must not be raised globally
    // (doing so 10×'s corpus wall-clock on doomed searches for zero gain).
    // These guards raise the budget *only* for these two lines, pinning them
    // FULL as the memo's regression check (breadth finds them through the pool
    // and never exercises deep generation). The budgets are pinned just above
    // each theorem's measured floor (2026-06-24) so a budget regression trips
    // the guard: `branch_converge` is fuel-bound (FULL ≥ f=2048, n≤64);
    // `fan_in` is node-bound (FULL ≥ n=124, f≥512). These are far below the
    // pre-tightening 384/10000 — the witness-unification/eigenvariable-ordering
    // work since the memo landed dropped the floors substantially.
    .{
        .filter = "branch_converge",
        .files = "tests/search_bench_cases/additive_fol.mm0:" ++
            "tests/search_bench_cases/additive_fol.auf",
        .mode = "depth",
        .max_depth = 10,
        .gen_nodes = 128,
        .gen_fuel = 3072,
    },
    .{
        .filter = "fan_in",
        .files = "tests/search_bench_cases/additive_fol.mm0:" ++
            "tests/search_bench_cases/additive_fol.auf",
        .mode = "depth",
        .max_depth = 10,
        .gen_nodes = 192,
        .gen_fuel = 1024,
    },
    // Backward hyp-ordering depth guard (branchfactor + relation-transport
    // screen, `exact.zig` `hypSlotCost` / `isRelationTransport`). `eq_euclid`
    // is a multi-line Hilbert-style modus-ponens chain that regenerates its
    // WHOLE proof from the bare goal ONLY when the generate-only slot is
    // costed (so a well-constrained ref premise leads) — it is unfound at
    // frontier 4 without the cost. The additive total guard above is the dual
    // check (it traps the transport screen: without it, the same cost reorders
    // `mpbi`'s premises and additive collapses). Default budget: the gain is
    // not budget-bound. See `project_premise_ordering_shared_pin`.
    .{
        .filter = "eq_euclid",
        .files = "tests/search_bench_cases/peano_frontier.mm0:" ++
            "tests/search_bench_cases/peano_frontier.auf",
        .mode = "depth",
    },
    // Forward-saturation depth guards (Horn-clause / transitive closure,
    // META_STRESS.md "Bespoke theory #2"). These are the only end-to-end
    // checks that `auto?` FORWARD-SATURATES a real multi-layer Horn
    // derivation: each goal `path v0 vN` must regenerate its WHOLE proof
    // from the edge hypotheses alone (frontier FULL), which exercises the
    // Stage 7/8 forward layer + derived-from-derived recipes (backward
    // search alone can't — the middle vertex is an open subgoal).
    //
    // `reach16` (a length-16 closure, 136 sub-paths) regenerates FULL at the
    // DEFAULT forward bounds — the forward-saturation capability floor; if a
    // change regresses forward derivation or its dedupe, it drops below FULL.
    // `skip_ladder` guards the dedupe path specifically (Fibonacci-many
    // shared-subpath routes). `reach24` regenerates FULL only with the
    // forward budget raised (attempts 1024→16384, facts 64→128, layers
    // untouched) — the completeness-at-budget check pinning the bound order
    // attempts→facts (raising facts alone does nothing). The global forward
    // defaults stay conservative (they bound the no-result `forward_stress`
    // case); the budget is scoped here, exactly as the additive guards above
    // scope generation budget.
    .{
        .filter = "reach16",
        .files = "tests/search_bench_cases/transitive_closure.mm0:" ++
            "tests/search_bench_cases/transitive_closure.auf",
        .mode = "depth",
    },
    .{
        .filter = "skip_ladder",
        .files = "tests/search_bench_cases/transitive_closure.mm0:" ++
            "tests/search_bench_cases/transitive_closure.auf",
        .mode = "depth",
    },
    .{
        .filter = "reach24",
        .files = "tests/search_bench_cases/transitive_closure.mm0:" ++
            "tests/search_bench_cases/transitive_closure.auf",
        .mode = "depth",
        .fwd_attempts = 16384,
        .fwd_facts = 128,
    },
    // `@auto trigger` seeding depth guards (phase 6; see
    // docs/design_notes/trigger_seeding.md). The minimal ND theory is the
    // pure repro of the elimination-major left-rule gap: both theorems
    // must regenerate their WHOLE proof from the bare goal and an EMPTY
    // ref pool, which is possible ONLY through the seeding retry —
    // `nd_mp_inner` (`p → q , p ⊢ q`) was a clean MISS at any budget
    // before it (imp_elim's `p` is premise-only; no ref pins it). These
    // pin the whole chain: annotation parsing → subterm harvest → seed
    // minting → seeded derived pool → the seed-aware slot cost
    // (`HypPlan.seeded_len`, which lets the seed-determined elimination
    // major lead its open minors). FULL at the default budget.
    .{
        .filter = "nd_mp_inner",
        .files = "tests/search_bench_cases/nd_minimal.mm0:" ++
            "tests/search_bench_cases/nd_minimal.auf",
        .mode = "depth",
    },
    .{
        .filter = "nd_or_comm_min",
        .files = "tests/search_bench_cases/nd_minimal.mm0:" ++
            "tests/search_bench_cases/nd_minimal.auf",
        .mode = "depth",
    },
    // The real-theory seeding win: zermelo_frontier's `ax` carries the
    // same triggers, and `nd_exists_elim_const` (4/6 before, capped at
    // the k where a truncated `ax` line had to be re-invented) is FULL
    // with them — the only zermelo per-theorem change from the
    // annotation. (`nd_or_comm` stays 2/6: its k=3 miss is the separate
    // phase-5 distractor-flood budget death, not the left-rule gap.)
    .{
        .filter = "nd_exists_elim_const",
        .files = "tests/search_bench_cases/zermelo_frontier.mm0:" ++
            "tests/search_bench_cases/zermelo_frontier.auf",
        .mode = "depth",
    },
    // Forward-enrollment depth guard for church (task #120,
    // docs/design_notes/church_forward_enrollment.md). church_frontier
    // carries `@auto forward` on MP + eqTR1/eqTR2 — the measured
    // zero-loss set. `OR_DEF` goes 3/14 -> FULL with it (the flagship
    // per-theorem change; DISJ_CASES 1->2 and IMP_TRANS 2->3 aren't
    // FULL-able so can't be pinned by a depth guard). FULL at the
    // default budget; trips if forward join enrollment, the eqTR typing
    // extraction, or the annotation parsing regresses.
    .{
        .filter = "OR_DEF",
        .files = "tests/search_bench_cases/church_frontier.mm0:" ++
            "tests/search_bench_cases/church_frontier.auf",
        .mode = "depth",
    },
    // Forward-JOIN depth guards (∀∃ quantifier alternation, META_STRESS.md
    // "Bespoke theory #3"). These pin the forward-join meta grounding: a
    // universal family fact (`P ?t → Q ?t`, from `all_elim`) joined with a
    // concrete fact (`P c`) by `mp @auto forward` must derive the concrete
    // fact (`Q c`), grounding `?t := c` at the join and baking it as a recipe
    // pin (`DerivedRef.pinned_metas`); the backward `ex_intro` then closes
    // the existential. Both regenerate their WHOLE proof from the bare goal
    // at the DEFAULT budget — the forward-join capability floor.
    //
    // `chain_ex` is the strongest end-to-end check: a TWO-LAYER join
    // (`Pc → Qc → Sc`) whose `S c` recipe nests `Q c`'s recipe, exercising
    // pin propagation across nested layers. `all_imp_ex_compound` pins the
    // COMPOUND-witness join (consequent `Q (f c)`, witness `f c`). If a
    // change regresses the join overlay, the pin baking, or the
    // required⊆shape gate, these drop below FULL. (The genuinely-free
    // witness-invention cells `free_instance_ex` / `compound_free_ex` ride
    // the pre-existing backward path and are covered by the bench corpus and
    // the negative unit test, not guarded here.)
    .{
        .filter = "chain_ex",
        .files = "tests/search_bench_cases/quantifier_alternation.mm0:" ++
            "tests/search_bench_cases/quantifier_alternation.auf",
        .mode = "depth",
    },
    .{
        .filter = "all_imp_ex_compound",
        .files = "tests/search_bench_cases/quantifier_alternation.mm0:" ++
            "tests/search_bench_cases/quantifier_alternation.auf",
        .mode = "depth",
    },
    // Sophisticated forward-join probes that must stay FULL: `diag_ex` grounds
    // the universal meta in TWO family positions (`R ?t ?t`) consistently from
    // one anchor; `nested_rel_ex` peels a nested `∀x∀y`, grounding the outer
    // meta at the join while the inner stays universal into the existential;
    // `ambiguous_anchor_ex` has two valid anchors and must pick one without
    // double-counting.
    .{
        .filter = "diag_ex",
        .files = "tests/search_bench_cases/quantifier_alternation.mm0:" ++
            "tests/search_bench_cases/quantifier_alternation.auf",
        .mode = "depth",
    },
    .{
        .filter = "nested_rel_ex",
        .files = "tests/search_bench_cases/quantifier_alternation.mm0:" ++
            "tests/search_bench_cases/quantifier_alternation.auf",
        .mode = "depth",
    },
    .{
        .filter = "ambiguous_anchor_ex",
        .files = "tests/search_bench_cases/quantifier_alternation.mm0:" ++
            "tests/search_bench_cases/quantifier_alternation.auf",
        .mode = "depth",
    },
    // Nested `ex_intro` composition: the inner introduction resolves a carried
    // ancestor witness from its concrete hyp (`solveCarriedViewMetas`) and
    // renders it explicitly so the outer reads the witness back.
    // `nested_concrete_ex` threads `R c d` two `∃` layers up;
    // `double_all_ex` invents both witnesses through a doubly-universal hyp.
    .{
        .filter = "nested_concrete_ex",
        .files = "tests/search_bench_cases/quantifier_alternation.mm0:" ++
            "tests/search_bench_cases/quantifier_alternation.auf",
        .mode = "depth",
    },
    .{
        .filter = "double_all_ex",
        .files = "tests/search_bench_cases/quantifier_alternation.mm0:" ++
            "tests/search_bench_cases/quantifier_alternation.auf",
        .mode = "depth",
    },
    // Two-layer same-predicate forward chain under a buried witness:
    // `∀x(Px→P(f x)), Pc ⊢ ∃y P(f(f y))`. The whole-proof regen from hyps
    // reuses the SAME family fact `P ?x→P(f ?x)` twice with DIFFERENT witnesses
    // (`?x=c` then `?x=f c`); guards the per-occurrence recipe materialization
    // (`forward.resolveRecipeValues` scoped pins + cursor render) that lets one
    // family fact carry distinct per-use witnesses.
    .{
        .filter = "deep_compound_ex",
        .files = "tests/search_bench_cases/quantifier_alternation.mm0:" ++
            "tests/search_bench_cases/quantifier_alternation.auf",
        .mode = "depth",
    },
    // Carried-witness COMPOUND guard (witness-unification migration): the
    // carried (outer) witness of a nested `ex_intro` must accept a COMPOUND
    // value end-to-end — `solveCarriedViewMetas` resolves `W := f c`, and
    // the `UnifyMismatch` holey-retry in `validateSelectedRefs` hands the
    // checker the value the inference solver's placeholder model cannot
    // absorb (wildcard-for-subtree). Matches all three `nested_compound_*`
    // variants (outer / inner / both); bare-witness `nested_concrete_ex`
    // above cannot catch this regression (wildcard-for-leaf survives
    // inference). FULL at the default budget.
    .{
        .filter = "nested_compound",
        .files = "tests/search_bench_cases/quantifier_alternation.mm0:" ++
            "tests/search_bench_cases/quantifier_alternation.auf",
        .mode = "depth",
    },
    // Deeper stress probes layered on the fixes above. `triple_compound_ex`
    // adds a THIRD same-family forward layer (witness under three `f`s):
    // capability is present but the third saturation layer needs
    // `fwd_layers=4` (default is 3 — enough for `deep_compound_ex`'s two
    // layers, not three). `diag_compound_ex` is `diag_ex` with a COMPOUND
    // diagonal witness (`f c` read consistently off both `R y y` slots).
    // `forward_nested_ex` feeds a FORWARD-derived relational fact (`R c d`,
    // no such hypothesis) into the nested-`ex_intro` carried-witness path,
    // combining forward join with carried-meta nested introduction.
    .{
        .filter = "triple_compound_ex",
        .files = "tests/search_bench_cases/quantifier_alternation.mm0:" ++
            "tests/search_bench_cases/quantifier_alternation.auf",
        .mode = "depth",
        .fwd_layers = 4,
    },
    .{
        .filter = "diag_compound_ex",
        .files = "tests/search_bench_cases/quantifier_alternation.mm0:" ++
            "tests/search_bench_cases/quantifier_alternation.auf",
        .mode = "depth",
    },
    .{
        .filter = "forward_nested_ex",
        .files = "tests/search_bench_cases/quantifier_alternation.mm0:" ++
            "tests/search_bench_cases/quantifier_alternation.auf",
        .mode = "depth",
    },
    // ── Fixture-TOTAL FULL guards (META_STRESS.md §3 bespoke theories #1–#3).
    // The per-line guards above pin specific theorems just above their budget
    // floor (catching *budget* regressions on those lines). These three pin
    // the FULL *total* of an ENTIRE fixture: with `--filter` omitted every
    // theorem block is selected, and depth + `--require-no-miss` fails unless
    // EVERY line regenerates its whole proof (`full == theorems`). This is the
    // completeness backstop — it catches a regression on any unguarded line
    // and forces any newly-added theorem to reach FULL (or be given coverage),
    // so the "100% FULL" claim for these fixtures can't silently rot.
    //
    // Each fixture uses the union of its own per-line budget overrides (the
    // max across its theorems), so the total guard is no looser than the
    // line guards it subsumes. Verified 2026-07-02: additive_fol 84/84,
    // transitive_closure 7/7, quantifier_alternation 23/23 FULL (18 + the
    // five compound-witness probes); each total trips (exit 1) if its
    // budget union is reduced below floor.
    .{
        // #1 additive sequent calculus (backward generation): branch_converge
        // is fuel-bound (3072), fan_in node-bound (192); both need depth 10.
        .files = "tests/search_bench_cases/additive_fol.mm0:" ++
            "tests/search_bench_cases/additive_fol.auf",
        .mode = "depth",
        .max_depth = 10,
        .gen_nodes = 192,
        .gen_fuel = 3072,
    },
    .{
        // #2 transitive closure (forward saturation): reach24/reach32 need the
        // forward budget raised (attempts 16384, facts 128); reach32 is NOT
        // individually guarded, so this total is its only FULL check.
        .files = "tests/search_bench_cases/transitive_closure.mm0:" ++
            "tests/search_bench_cases/transitive_closure.auf",
        .mode = "depth",
        .fwd_attempts = 16384,
        .fwd_facts = 128,
    },
    .{
        // #3 quantifier alternation (forward join): triple_compound_ex needs a
        // 4th saturation layer; everything else is FULL at the default budget.
        .files = "tests/search_bench_cases/quantifier_alternation.mm0:" ++
            "tests/search_bench_cases/quantifier_alternation.auf",
        .mode = "depth",
        .fwd_layers = 4,
    },
    // ── Tait one-sided (Schütte) sequent calculus: backward search over a
    // single ACUI succedent `⊢ Δ` (see tait.mm0's header). A classical FOL
    // stress fixture — every connective has a positive intro rule (ror / rand
    // / rim / rbi / rall / rex) plus an EXPLICIT De Morgan rule for its
    // negation (rdm_*), because binder inference (exact unify replay) runs
    // BEFORE @rewrite normalization and so cannot match a De-Morgan-normalized
    // ref line; the rdm_* rules keep the leaves structural.
    //
    // The fixture declares its invertible discipline: the non-branching
    // decomposition ladder (ror/rim/rdm_*) is `@auto eager`, the branching
    // rules (rand/rbi) `@auto eager 2`, and rex stays plain `@auto
    // backward`. Eager rules are tried first, committed to once applied, and
    // exempt from the depth budget, so counted depth is roughly the number
    // of genuine choice points and every theorem is FULL at the default
    // md=6. The worst theorem needs ~0.31G ticks (exists_mono), so the nets
    // below run at the pure default budget with >10x margin. How the old
    // per-theorem depth floors and budget overrides were closed:
    // docs/frontier_guard_history.md.
    .{
        // Completeness backstop: every one of the 385 proof lines must stay
        // breadth-found (and any newly-added line must be found) — at pure
        // defaults, with the eager cut live. This is also the teeth that
        // the eager annotations stay genuinely invertible: a wrong
        // annotation would make some hand-proof line unreachable through
        // the cut-honoring phases.
        .files = "tests/search_bench_cases/tait.mm0:" ++
            "tests/search_bench_cases/tait.auf",
        .mode = "breadth",
    },
    // Depth-completeness net at the DEFAULT md: every theorem (all 52,
    // core + extended battery) regenerates FULL from the bare goal at
    // md=6 — the headline property of the eager discipline. Pure
    // defaults, including the tick budget (see note above).
    .{
        .files = "tests/search_bench_cases/tait.mm0:" ++
            "tests/search_bench_cases/tait.auf",
        .mode = "depth",
    },
    // Monotonicity net at md=12: everything found at md=6 must stay found
    // when the depth budget is deep — the depth-major phase-ladder teeth
    // (drinker's old md≥8 flood: phase-major nesting put doomed deep
    // phase-1/2 passes in front of its shallow phase-3 witness proof).
    .{
        .files = "tests/search_bench_cases/tait.mm0:" ++
            "tests/search_bench_cases/tait.auf",
        .mode = "depth",
        .max_depth = 12,
    },
    // ── Analytic natural deduction (`nd_fol`): the tait battery read as
    // `∅ ⊢ φ`, searched through intro rules and derived left rules only
    // (eliminations are not enrolled; see nd_fol.mm0's header). The target
    // is parity with tait/additive_fol. Status (2026-09-23): depth FULL
    // 57/57 at defaults, mean frontier 5.96 (`--exclude=_left,or_right`
    // skips the derived-rule lemmas). The per-line depth guards below could
    // now become one whole-fixture total, once the guard table can pass
    // `--exclude`.
    .{
        // Every hand-proof line, derived-rule lemmas included, stays found.
        .files = "tests/search_bench_cases/nd_fol.mm0:" ++
            "tests/search_bench_cases/nd_fol.auf",
        .mode = "breadth",
    },
    // One FULL depth guard per search shape: eager intros with imp_left
    // chains (s_comb), raa + not_left (cases_classical), or_left splits
    // (resolution), and all_left/ex_left witnesses (exists_mono).
    .{
        .filter = "s_comb",
        .files = "tests/search_bench_cases/nd_fol.mm0:" ++
            "tests/search_bench_cases/nd_fol.auf",
        .mode = "depth",
    },
    .{
        .filter = "cases_classical",
        .files = "tests/search_bench_cases/nd_fol.mm0:" ++
            "tests/search_bench_cases/nd_fol.auf",
        .mode = "depth",
    },
    .{
        .filter = "resolution",
        .files = "tests/search_bench_cases/nd_fol.mm0:" ++
            "tests/search_bench_cases/nd_fol.auf",
        .mode = "depth",
    },
    .{
        .filter = "exists_mono",
        .files = "tests/search_bench_cases/nd_fol.mm0:" ++
            "tests/search_bench_cases/nd_fol.auf",
        .mode = "depth",
    },
    // The anchored coupled sweep (`witness.collectAnchorShapes`): the
    // all_left and ex_intro witnesses are forced only by the `ax` leaf,
    // which pairs a context member with the succedent. A clean miss
    // without it.
    .{
        .filter = "ex_all_to_all_ex",
        .files = "tests/search_bench_cases/nd_fol.mm0:" ++
            "tests/search_bench_cases/nd_fol.auf",
        .mode = "depth",
    },
    // Pool refs whose context differs from a bound context binder are
    // refuted before sibling generation (`acui.boundRegionRefEqualPlausible`);
    // without it the eliminations' ref-filled minors drown peirce.
    .{
        .filter = "peirce",
        .files = "tests/search_bench_cases/nd_fol.mm0:" ++
            "tests/search_bench_cases/nd_fol.auf",
        .mode = "depth",
    },
    // Eager `not_left` (classically invertible): dummett's two raa rounds
    // fit the default depth only when the negation steps cost none.
    .{
        .filter = "dummett",
        .files = "tests/search_bench_cases/nd_fol.mm0:" ++
            "tests/search_bench_cases/nd_fol.auf",
        .mode = "depth",
    },
    // Eager `or_right`: classical disjunction goals decompose instead of
    // guessing a disjunct under raa.
    .{
        .filter = "mat_cases",
        .files = "tests/search_bench_cases/nd_fol.mm0:" ++
            "tests/search_bench_cases/nd_fol.auf",
        .mode = "depth",
    },
};
