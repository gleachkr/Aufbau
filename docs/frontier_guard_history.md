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
  candidate order (`witnessClass` in `exact.zig`): FULL 7/7 at the default
  budget and nodes (worst row 1.68G, was 9.5G plus n=4096 floors).
- **ex_all_to_all_ex**, formerly the hardest of the set (its single `ax`
  leaf must co-solve two open rex witnesses in one complementary pair, with
  no rigid anchor), was closed by the complementary coupled sweep
  (`collectComplementShapes` / `unifyMembersThroughShape` in
  `exact_witness.zig`).

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
(`internal_child` in `exact_validate.zig`), so the parent re-check never
re-infers them from an ACUI-reassociated hint. The old resolution churn
(k≥6 rows at ~3.4G ticks, over the 3.35G default cap) collapsed to ~58M;
the worst theorem became ~0.31G (exists_mono).
