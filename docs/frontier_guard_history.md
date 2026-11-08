# Frontier guard history

Dated measurements behind the guards in `tests/frontier_guards.zig`. The
manifest keeps only current budgets and rationale; when a guard's floor
moves or a gap closes, record the measurement here rather than in the
manifest comment.

## Tait one-sided sequent calculus (`tests/search_bench_cases/tait.*`)

### Depth is tree height (2026-07-04)

The search depth a proof needs equals its proof-tree height (the longest
leaf→root rule chain), not its line count. `iff_comm` (15 lines) was FULL at
the default md=6 because it is a balanced tree of height 6, while `all_swap`
(8 lines) needed md=7 because it is a linear chain of height 7.

`drinker` flooded at md≥8 (its usable window was md∈[5,7]). The depth-major
phase ladder (`generate.zig` `runPhaseLadder`, 2026-07-05) fixed that; with
`forall_mono`'s node floor removed by the member-side capture check, the
fixture was 20/20 FULL at every md≥8 with no overrides.

### Gap closures (2026-07-04 dissection; `ex_swap` closed the same day, `forall_mono` on 2026-07-05)

- **resolution** was a doomed-reject flood: loose one-premise candidates
  (`ror`/`rdm_*`, principal binders unbound inside the ACUI succedent) swept
  the whole pool through full `tryCandidate`. The hyp-vs-ref
  member-consistency prune (`hypRefMembersPlausible`) kills the sweep; the
  internal-child enumeration cutoff dropped the budget floor 5.51G → 3.75G
  ticks (it was >10G before the prune); removing the redundant pre-clone COW
  chain level under every `tryCandidate` probe (now `candidate.probe`)
  dropped it again, 3.75G → 3.09G, under the 3.35G default cap. FULL 13/13
  at pure defaults, margin 1.08× (a change pushing the k=6 floor +8% trips
  the guard).
- **forall_mono** was node-bound, not fuel-bound (floor ∈ (384, 512]).
  Closed by the member-side witness capture check: the node budget had been
  going to scope-escaping member-witness fills, not to the honest carry
  recursion. FULL at pure defaults. The corpus-wide nodes=2048 sweep stays
  refuted (21 depth-FULL losses).
- **ex_swap** was the last capability gap: rex accepted-witness
  over-generation. `rex` keeps its principal, so every open node re-offered
  a fresh carry-metavar rex whose premise is itself a new ∃ member, a
  self-feeding cascade of valid one-step rederivations (about one accepted
  full validation per chain node). Closed by the internal-child enumeration
  cutoff (`ExactOptions.internal_open_child`) plus the witness-class
  candidate order (`witnessClass` in
  `src/frontend/compiler/search/backward/backtrack.zig`): FULL 7/7 at the
  default budget and nodes (worst row 1.68G, was 9.5G plus n=4096 floors).
- **ex_all_to_all_ex**, formerly the hardest of the set (its single `ax`
  leaf must co-solve two open rex witnesses in one complementary pair, with
  no rigid anchor), was closed by the complementary coupled sweep
  (`collectComplementShapes` / `unifyMembersThroughShape` in
  `src/frontend/compiler/search/backward/witness.zig`).

### `@auto eager` (2026-07-05)

The fixture gained its eager annotations (ror/rim/rdm_* `@auto eager`,
rand/rbi `@auto eager 2`). Every theorem became FULL at the default md=6
(most at md=1), and the per-theorem md floors (imp_trans, all_swap,
all_an_dist_fwd and ex_all_to_all_ex at md=7; forall_mono and ex_swap at
md=12; drinker's md≥8 flood) collapsed into the default-md whole-fixture
net.

The nested-inline binder-extraction residual (task #93) closed at the same
time: accepted `@auto eager` candidates inside internal generation child
solves carry their resolved bindings rendered on the spliced application
(`internal_child` in `src/frontend/compiler/search/backward/validate.zig`),
so the parent re-check never re-infers them from an ACUI-reassociated hint. The old resolution churn
(k≥6 rows at ~3.4G ticks, over the 3.35G default cap) collapsed to ~58M;
the worst theorem became ~0.31G (exists_mono).

## Zermelo (`tests/search_bench_cases/zermelo_frontier.*`)

### Sub-goal trigger re-seeding (2026-10-24)

`cb_bijection_maps_domain` went 6/8 → FULL when `auto?` started harvesting
`@auto trigger` seeds again at a sub-goal that names a variable free which
the root goal does not (task #512 piece 1; `generate.zig` `Reseed`). Its
k=7 cut is an `or_elim` over a derived disjunction whose branch member
`cb_g_branch A B f g x y` is no subterm of the goal, so the root harvest
cannot seed the `ax` instance the branch's `and_elim_r` minor needs; the
harvest at the case-split sub-goal can. Same change: `range_sub_intro`
5/7 → 6/7, `setdiff_antitone_right` 4/5 → FULL, `image_mono` 5/9 → 6/9,
`cb_core_prefixed` 4/7 → FULL, `cb_bijection_maps_range` 5/7 → FULL,
`cb_bijection_domain_on_from_injections` 3/9 → 4/9,
`cb_bijection_range_sub_from_injections` 3/4 → FULL; corpus FULL 468 → 474
at −0.6% ticks; nd_fol 57/57 at +10.7%. Re-seeding from every new member
(not only those naming a fresh variable) found the same rows and widened
nd_fol's search by 63%; rebuilding the pool per sub-goal versus extending
it incrementally measured within 1% (task #512).

## Martin-Löf type theory (`tests/search_bench_cases/martin_lof_frontier.*`)

### Guards move to the bench copy (2026-09-27)

The `arr_` guard ran on `tests/proof_cases/martin_lof`, the living example,
so any tidy-up of the example changed what it tested; and `arr_` was a
substring filter that also picked up `arr_beta`, which depends on neither
fix. It became three exact-name guards on the bench copy, which matches
the example plus eight `@auto` lines. With each fix reverted, the same rows
miss at k=1 on both files: `arr_form` and `arr_elim` without
`tryFreshBoundGenerate`, `arr_intro` without `seedValueIsLoose`'s
placeholder arm.

The `nat_rec_step_ty` guard (added with the ACUI multiplicity reject,
now `acuiRequiredMembersPlausible`, on 2026-09-25) was retired. With the reject
disabled the theorem stays FULL 5/5 on both files; the cost rises from
21.8M to 84.9M ticks (48 to 312 candidate tries) but never reaches a miss,
so the depth run no longer caught the regression. The unit test "ACUI
member prune counts distinct members without idempotence" (prune_tests.zig)
fails without the reject and is now its check.

## Search core budget (2026-10-29)

When the search core learned to split a context between premises (task
#549), three depth guards stopped reaching the end of their proofs and
were capped at their frontier: `lt_trans_ax` (euclid) at 4/7,
`range_sub_elim` (zermelo) at 1/2 and `cb_bijection_maps_domain`
(zermelo) at 5/8. In each the core tries an elimination rule whose minor
premise `G ⊢ ?p` it closes from every fact in turn, the search fails, and
the generation search gets too little of the 6.3G budget for the cut it
used to find (`cb_bijection_maps_domain`'s k=6 cut alone took the whole
budget in the core). A check that the major premise can still be proved
before trying the minor recovered the first two but cost the core alone
59 depth rows net, mostly Hilbert-style modus ponens steps, which need
the same guess.

When the core began passing a goal's open cut through a rule to premises
that facts close, and inventing cuts for binders a narrowing leaves
unbound (2026-11-01), `cb_bijection_maps_domain`'s k=4 and k=5 cuts went
from 5.9G to 6.9G ticks, past the 6.3G default: the core tries more cut
values before the generation search gets its turn. The guard keeps its
k=5 cap with an 8G budget.

When the work budget began charging the core's matching and walks
(2026-11-06), the older weights were divided by 4 to keep a unit near one
nanosecond, and the default went from 6.3G to 2.3G. Figures above this
paragraph are in the old units. `cb_bijection_maps_domain`'s k=4 and k=5
cuts now take 3.3G, past the default, and the guard's budget is 3.6G.

When `exact?` moved to the search core and `auto?` lost its separate
one-step pass (2026-11-08), five lines missed that the old pass had found.
`euclid` `exists_prime_factor` l41 is `ex_elim` with a `@recover` witness
that a premise fixes, which the core does not read back. `nd_fol`
`not_all_left` and `not_ex_left` l2 and l6 need a substitution into a
schematic formula (`[x/t] (¬ p)` against `¬ [x/u] p`), which the core does
not match; it spends the budget before the generation search, which finds
them, runs. The guards pin these lines with `expect_miss`, which fails once
a pinned line is found.

The `nd_fol` lines came back the same day. The core built a quantifier
rule's premise by putting the witness in place of the bound variable, and a
schematic `p: wff x` holds `x` only by its dependency, so the premise lost
the substitution. Such an instance now takes its premise from a fact and
reads the witness off it as the checker reads the `@recover`; the four pins
are gone. `exists_prime_factor` l41 stays pinned.
