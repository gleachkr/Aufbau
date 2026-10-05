# Search subsystem architecture

This directory is the **proof search** behind `exact?`, `apply?`, and `auto?`.
Given a goal and the ambient theory it produces candidate `RuleApplication`s
(source-proof lines) that, when checked, close the goal. It is untrusted
frontend automation: every suggestion is re-validated by the checker, so a bug
here yields a rejected or missing suggestion, never an unsound proof.

This file is the map. The global structure spans backward generation and
conversion search; the largest modules are now `egraph.zig`,
`egraph/explain.zig`, `backward/backtrack.zig`, and `conversion/lowerer.zig`.
The mechanisms below are **specialized by rule-class and phase, not
redundant**. Read their contracts before merging similar-looking routines.

Checker validation here means frontend elaboration, not trusted MM0/MMB
verification. Complete generated proofs still need the trusted verifier;
a search result or successful compilation alone is not that guarantee.

`src/frontend/inference_solver.zig` is a *different* engine (last-resort
omitted-binder inference for a single rule application); it is not part of this
subsystem.

## Backward-search entry points

All three live behind `root.zig` and share `SearchSession` (`session.zig`),
which lazily builds and caches the three indices (rule index, reference pool,
ref index) so repeated queries in one theorem amortize.

- **`exact?` / `apply?`** → `backward/backtrack.zig:exact` / `exactWithSession`. One-shot:
  find rules whose conclusion matches the goal and whose hypotheses are
  discharged by existing proof references (the *reference pool*). No sub-proof
  synthesis. `apply.zig` is the thin `apply?` variant.
- **`auto?`** → `generate.zig:generateTopLevel`. Recursive: drives
  `exactWithSession` under a `generator` hook that can *synthesize* sub-proofs
  for unmet hypotheses, with iterative deepening and a global fuel budget.

The key relationship: **`auto?` is `exact?` plus a hook**. `generateTopLevel`
sets up a `Driver` whose `hook.solveFn` recursively re-enters the same
`exactWithSession` for each open hypothesis. Almost every code path is shared;
the generation-only behavior is gated on `options.generator != null` (in
`exact`) or on the `hook` flags (`allow_split`, `allow_invent_witness`). When
reading `backward/backtrack.zig`, "is `generator` null?" is the single most important branch
to track — it separates plain `exact?` (must stay untouched) from `auto?`.

Inside the search, validation renders every binder the search chose
(existential metas, bound witnesses, ACUI split and principal choices) as an
explicit binding, so the checker never has to re-derive a choice
(`backward/validate.zig`). The suggestion text is a separate matter:
`source.zig:trimBindings` keeps only the bindings the checker cannot infer.
It tries the suggestion with no bindings first. Failing that, it checks the
line with every binding withheld behind a `BindingOracle`
(`compiler/context.zig`), and the checker (`check/apply.zig`) takes from it
what it needs:

- where an application's inference fails, or lands on something other than
  the search's value up to ACUI, the search's values, less each one
  inference still reproduces;
- where an inline sub-proof fails on the hint its parent gave it, the
  parent's binders that the sub-proof's premise mentions and the goal leaves
  open (failing that, all it mentions; failing that, all);
- where an inline sub-proof checks against a weak hint but proves something
  other than its parent's premise (the premise mismatches, or the parent's
  inference fails even with every value supplied), the binders that premise
  mentions, supplied up front from then on; when the parent's inference
  failed and that forces nothing new, the bindings of the nearest level of
  sub-proofs below (the check reruns, forcing more each time, if it already
  failed).

The bindings taken are kept, and one more check validates the result. A
binder the source states can change how the checker reads the line (it
decides which hints an inline sub-proof gets), so if that check fails the
oracle checks again with the kept bindings stated, keeping whatever more it
takes. Forcing and the widest retry over-approximate, so each binding they
supplied is then dropped if the line still checks without it (one check
each; the other paths cost none). Should an oracle check fail, the
suggestion is offered untrimmed and counted in `SearchCounters.untrimmed`;
the bench, and search tests that go through `tests/helpers.zig`, fail on
any, so every corpus line must trim.
Trimming costs checker runs per surfaced suggestion only, never search ticks
(`SearchCounters.trim_ns` times it, and the bench's `-v` rows print it as
`trim=`), and cannot change what is found.

**Holey goals (type inference).** A line whose assertion has proof holes
(`g ⊢ t : _ty`) reaches `generateTopLevel` as `Goal.holey`. It interns the
assertion with a meta per hole (`mintNumberedMeta`, stable `meta_id`s from the
driver's counter) and every pass searches that as an open
`implicit_whole_conclusion` hint, so the ladder runs as for an open child
target and the proof found fills the holes. `Driver.open_root` /
`GenerationHook.open_root` mark such a search: phase-6 trigger seeding is
skipped (holes are not subterms), and a constrained open slot registers its
carried ancestor metas as a `.witness` slot does, so a hole's meta is
solvable at a leaf two open levels down (`f · x · y : _`; #331 is the
general-goal version, which costs ticks there). Search validates against the
hint, so `source.zig` surfaces a suggestion only if the holey line itself
checks with it.

## Conversion-search entry point

**`conversion?`** is a separate engine (`conversion.zig:run`, dispatched
from `source.zig` like the others). It does *not* share the pipeline below.
It saturates an e-graph (`egraph.zig`) over `@conversion`-enrolled rewrites
plus the pool's local ground equations, asks whether the goal's two sides
land in one class, and lowers the explanation to ordinary proof lines
(`conversion/lowerer.zig`). AC
operators declared via `@conversion assoc`/`comm` role tokens are absorbed
into the e-graph's bag-node interning instead of being enrolled as rules.
A stored bag node's member multiset is stable for life: when a member class
later denotes a same-head bag, rebuild mints the flattened form as a twin
node behind a `.splice` explanation edge rather than re-splicing in place —
explanation edges render against the shapes recorded at union time, and the
lowering crosses the twin with a pure AC re-tree (`.ac_flatten` step). The
same pair is minted at intern time when the canonical splice dissolves a
member class that also carries other structure (a leaf, an application, or a
bag of another head): the nested node is stored beside the flat one so
patterns and rule targets keep the member-level view, while a pure AC
regrouping still interns to the single flat node (`EGraph.nestedView`). The
matcher has the dual move: a structured pattern member that finds no member
of a bag may claim a sub-multiset of its members covering a same-head bag
of such a mixed class (`EGraph.assignSubBagMember`, candidates from the
graph's own bags), and the union then anchors on the regrouped twin the
claim folds the node back into (`EGraph.regroupTwin`) — a node the intern
would have kept had the class held that structure when the bag was seeded.
A node and its splice twins are one redex in different groupings, so the
`@compute` fold ledger is keyed by twin component (`EGraph.twinRoot`): the
node that fires consumes its twins with it, and a twin only fires a redex
its node cannot see (the expansion exposing `2 * inv 2` inside `2 * (q / 2)`).
Otherwise every twin would fire its own copy of the redex in a different
pair order, and each intermediate of a cancellation cascade would spawn a
second chain that is twinned in turn — the alternative-order closure the
ledger exists to refuse (the zero-class blow-up of #244).
Extraction (`egraph/explain.zig`) renders every class position as the
class's minimal representative and runs twice at most: a cancellation can
leave a class containing itself (`-(p/3)³ = (q/2)² + -(q/2)² + -(p/3)³`),
and that class's representative is the chain's own source, which inside a
route endpoint re-poses the alignment in flight until the active guard
kills every route. The second pass (`ExplainCtx.destination_mode`, taken
only when the default pass fails so every chain it can extract stays
identical) lets the outermost alignment on a self-containing class register
its destination, and every member of that class rendered while it is in
flight takes the destination instead (`memberTerm`; representatives built
under it are not memoized). The lowered chain then crosses a def opening
into a bag (`q / 2` beside `q` and `inv 2`), which the checker's ACUI
comparison closes by opening the uncovered def leaf
(`normalizer/acui/target.zig`; see `docs/transparent_defs.md`).
See `docs/rewrite_system.md` for the user-facing surface.

## The pipeline (one `exactWithSession` call)

```
goal + theorem
  │
  ├─ exactRuleCandidates           candidate rules whose conclusion could match
  │    │                           (rule_index pre-filter by goal shape)
  │    └─ makeExactRuleCandidate / appendRuleCandidates   (backward/seed.zig)
  │         └─ SEED: bind rule binders from the concrete goal      ◀── seed phase
  │
  ├─ [auto? only] nonSplitCandidateFirst   additive rules before multiplicative,
  │                                        then by witness class (see below)
  │
  ├─ for each candidate:
  │    ├─ conclusionMembersPlausible        cheap ACUI reject  (backward/seed.zig):
  │    │                                    each required member present, and
  │    │                                    distinct ones unless idempotent
  │    ├─ bindingsDepHit == .rigid          doomed eigenvariable reject
  │    └─ enumerateCandidateRefs            fill hyps from the ref pool (DFS over
  │         │                               one `SlotCtx`: the candidate's bindings,
  │         │                               snapshots and per-slot fills)
  │         ├─ lookupHypReferences          per-slot ref lookup (backward/lookup.zig)
  │         ├─ buildHypPlans                slot fill ordering   (backward/plan.zig)
  │         ├─ matchOneHypWithSnapshot      per-ref match        (backward/match.zig)
  │         ├─ prune: abstract_prune / context_prune        (broad-slot floods)
  │         ├─ [auto? only] tryGenerateSlot / trySplitGenerate / open targets
  │         │     └─ hook.solveFn → recurse into exactWithSession  ◀── gen phase
  │         └─ validateSelectedRefs         (backward/validate.zig)
  │              └─ finalConclusionPlausible (backward/plausible.zig)
  │                 + tryCandidate          full checker validation (candidate.zig)
  │
  └─ rank + truncate → ExactResults
```

Three phases matter for the discussion below:

- **seed** (`backward/seed.zig`): bind rule binders positionally/structurally from
  the *concrete goal* at candidate-construction time. Cheap, deterministic.
- **validation** (`candidate.zig:tryCandidate` + `finalConclusionPlausible`):
  re-derive the line through the real checker on a cloned theorem.
- **generation** (`auto?` only, in `backward/backtrack.zig` + `generate.zig`): synthesize
  sub-proofs for hypotheses the pool can't fill.

## ACUI conclusion matching — the three principal mechanisms

Additive sequent rules (and any rule with an ACUI/AC/AU context combinator)
pose the recurring hard problem: matching a rule conclusion containing one or
more **principal** members plus a **rest-binder** (e.g. `lan`'s context `g`)
against a concrete goal multiset. "Which member is principal, what absorbs the
rest" is decided by **three distinct mechanisms**. They look overlapping. They
are not. Each is specialized by **rule-class × phase**:

| mechanism | rule class | phase | file |
|---|---|---|---|
| seed fan-out (`detectPrincipalFanout` / `findAmbiguousPrincipal` / `findAmbiguousLeaf` / `cloneCandidateWithPrincipalPin`) | **non-view** | seed | `backward/seed.zig`, `backward/acui.zig` |
| `tryPrincipalEnumerate` | **any** (structural gates only; annotation-independent, like seed fan-out) | generation | `backward/backtrack.zig` |
| `trySplitGenerate` + `backward/split.zig` (`findSplitSite` / `buildEnumerator`) | **multiplicative** (2+ context binders that *partition*) | generation | `backward/backtrack.zig`, `backward/split.zig` |

Why they cannot collapse into one (verified empirically, 2026-06-24):

- **View rules must not be principal-pinned at seed time.** For a `@view` rule
  the goal aligns with the *view surface* conclusion, not the raw `rule.concl`,
  so positional seed-forcing mis-binds and prunes the witness solve. The seed
  mechanisms already `return null` on `context.views.contains(rule_id)` for
  exactly this reason. View/witness rules instead get their principal chosen at
  **generation** time by `tryPrincipalEnumerate`. Disabling it regresses 5
  additive_fol theorems (`all_swap`, `ex_swap`, `forall_mono`, …). Since the
  `OpenMode` pass (2026-08-01) the mechanism is annotation-independent —
  enrollment is not required; the structural preconditions (ACUI split site,
  exactly one unresolved structured principal, ≥2 genuinely competing concrete
  members, no metas minted) are the whole gate. The seed-time/generation-time
  pair differ by *phase*, not by author permission: un-annotated ambiguous-
  principal theorems (additive_fol `de_morgan`, `dummett`, …) regenerate FULL
  through this path.
- **Multiplicative partition is a different problem.** A genuinely
  multiplicative rule (euclid `or_elim` `g,h,k`; `ex_elim` `g,h`) *splits* the
  goal context between premises; that is a search over partitions
  (`backward/split.zig`), not a single rest-complement. It must stay separate.

A deletion-based unification (the abandoned `noble-squishing-falcon` /
`matchAcuiSide` plan) is therefore **unreachable**: there is no redundant
duplicate to delete. If you want to reduce the special-casing, the lever is
*shared helpers* (`backward/bag.zig`: `flatten`, `lawOf`, `isCommutative`,
`unitOf`; `backward/acui.zig`: `templateMatchesExprReadOnly`,
`principalChoices`, `consumeBoundLeafMembers`), not merging the three drivers.

### ACUI subset soundness

`bag.isCommutative` gates every force-the-rest / fan-out step.
Under a non-commutative subset (AU; `StructuralCombiner.comm_name == null`) the
leftover is an *order-constrained remainder*, not a free multiset complement, so
committing a rest-binding is unsound — keep the conservative path. The
underlying-set invariant is fine for *discrimination/candidacy*, only unsound
for *committing*. See the `@acui can be a subset` note.

## Generation: the six-phase retry in `auto?`

`generateTopLevel` runs **five** retry phases over single-depth passes
(`runDepthPass`) inside `runPhaseLadder`, and a sixth outer retry against a
seeded derived pool. The phases' capabilities and gates are a table
(`ladder_phases`), and the order the ladder visits its (depth, phase) cells is
a list built from it (`buildSchedule`), so a schedule change is a change to
that list. Since 2026-07-05 the ladder is a **hybrid nesting**, and since
2026-10-02 (#300) every phase first searches depth 1:

- **Phases 1–3 form a depth-major core** — outer iterative deepening
  1..`max_depth`, inner phases per depth, stopping at the first
  (depth, phase) cell that yields. Depth-major makes `max_depth`
  monotone: a higher `max_depth`'s cell sequence is a strict
  prefix-extension of a lower one's, so raising it can never lose a finding
  under the same global budget. (Phase-major reordered the sequence as
  `max_depth` grew — a shallow later-phase proof was reachable only after
  the earlier phases exhausted ALL depths, so the budget died inside doomed
  deep passes: the tait `drinker` md≥8 flood, now fixed and guarded.) Any
  phase whose own fuel runs dry is *retired* (its remaining cells skipped)
  without ending the ladder; a retired core phase also skips the remaining
  tail cells. Only the global budget or the stack guard aborts.
- **Phases 4–5 run at depth 1 right after the core's depth 1, then as
  phase-major tails from depth 2**, each only while no core phase has
  retired. Reason: depth-major's
  cost ordering assumes fixed-depth cost is roughly phase-uniform, which
  holds for phases 1–3 (their extra mechanisms fire only at split sites /
  open witness slots) but not for retention and constrained MP, which
  broaden EVERY additive split node / implication-shaped goal — interleaved
  below a core find they inflated found cost ~3x (measured, tait
  ex_swap/all_an_dist_fwd). At depth 1 their larger branching has not
  compounded yet. The md-monotonicity guarantee covers phase-1–3 proofs and
  depth-1 proofs of phases 4–5; deeper phase-4/5 proofs keep the old
  behavior.

The ordering is load-bearing: within a core depth an anchored proof still
wins (split-free beats split at equal height, and within any single
application an anchored witness beats an invented one — invention is the
last rung of the slot-local witness ladder, not a phase capability), and
phases 4–5 go past depth 1 only after the core missed at every depth with no
core phase retired, and phase 6 runs only on misses that
did not stop the search, so they can only *add* found-ness. What the reorder changed is the cross-depth preference within
the core — a shallow invented-witness proof now beats a deeper split-free
one (measured impact: none — breadth corpus byte-identical). Flag sets are
monotone along the ladder (phase 3 carries the same flags as phase 2),
which the persisted-memo covering rule requires:

1. **Phase 1 — non-splitting.** `hook.allow_split = false`. Goals provable
   without a speculative ACUI context split are found here and never pay split
   cost.
2. **Phase 2 — context splitting** (`allow_split = true`). Per core depth,
   only after phase 1 missed at that depth. Enables `trySplitGenerate` for
   multiplicative rules whose hypothesis context halves must be guessed.
3. **Phase 3 — pool retry** (capability-identical to phase 2). Per core
   depth, only after phase 2 missed at that depth, and only if the theory
   has a witness-deferring `@auto backward` rule and a non-empty `@vars`.
   (The pool dummies themselves are materialized whenever `@vars` is
   non-empty, since hidden-variable generation below also draws on them.)
   A re-run with its own fuel pool and persisted-memo lineage;
   deep open-witness theories need it (peano `mul_eq_*_all` at depth 6 are
   found by this cell and by nothing else — #174: neither 4x fuel nor
   `max_depth` 10 recovers them without it). Witness invention itself —
   grounding an open existential whose witness *nothing forces* to a reused
   pool dummy — is not a phase capability: `allow_invent_witness` is on in
   every core phase whenever the pool exists, and invention stays the last
   rung of the slot-local witness ladder (`emitOpenTarget`), a single
   deterministic continuation per slot (measured outcome-identical to the
   historical phase-3 gating).
4. **Phase 4 — principal retention** (`allow_retain_principal = true`). At
   depth 1 right after the core's depth-1 cells; deeper only as a tail (see
   above). Only when the theory declares an **idempotent**
   structural combiner (`AcuiBag.anyLaw(…, Law.isIdempotent)`). Lets the ACUI split enumerator
   keep a member already claimed by a fixed principal in the open rest binder of
   a set combiner — the non-minimal complement `g , g = g` permits — and lets an
   ordered idempotent combiner's rest overlap its neighbours, as any contiguous
   run (`split.buildEnumerator`).
   Needed when a proof must retain the principal *and* its decomposition (a
   `lan`/`lim` premise that keeps `a∧b` alongside `a , b`) and the principal
   cannot be rebuilt. Broadens every additive split node, hence last and gated;
   the minimal-complement majority never pays. Guarded by the
   `idem_complement_probe` depth-frontier regression test. An `@auto eager`
   rule never retains: it is declared invertible, so the premises without
   the principal suffice. On tait this halves depth-frontier ticks.
5. **Phase 5 — constrained backward modus ponens** (`allow_constrained_mp =
   true`). At depth 1 after phase 4's depth-1 cell; deeper only as the last
   tail. Lets the open-generation path
   (`tryOpenGenerateSlot`) fire for **any** backward candidate, not just `@auto
   backward` rules: a binder the goal does not pin (e.g. `ax_mp`'s cut `a`) is
   opened as a meta, and the child search must close that hypothesis with a rule
   whose conclusion *pins* the meta — the non-`@auto` branch of `emitOpenTarget`
   is child-search-first and never invents a witness, so no existential is
   propagated or guessed. This recovers proofs that go *through* a modus ponens
   whose cut is structurally determined by a congruence/implication rule (e.g.
   `suc_chain` = `ax_mp [peano2r, …]`), which the forward/backward annotation
   discipline otherwise leaves unreachable. It opens every implication-shaped
   goal, so it goes past depth 1 only as the last tail. Its
   fuel is `GenerateOptions.phase5_fuel` (defaults to the main `fuel`); phase 5
   is intrinsically cheap (the gains solve shallow), so a tighter budget caps
   the doomed-miss exploration with little loss. ⚠ The high *worst-case*
   `auto?` latency on a hard miss (~2 min on deep church goals) is **not**
   phase 5 — it is the normal phases exhausting per-phase `fuel` at church's
   expensive per-validation cost, a pre-existing condition phase 5 only makes
   visible (a hard miss that used to fail slowly now succeeds slowly). The fix
   is the global per-call budget below.

   Three pieces let the child search pin the cut when a definition hides it
   (zermelo `range_sub_elim`: `imp_elim [all_elim [#1], ex_intro [#2]]`,
   where `#1` is `range_sub f B`):
   - **Premise order.** `buildHypPlans` sorts a *wildcard sequent* premise
     (every argument a bare unpinned binder, `imp_elim`'s minor `?H ⊢ ?p`)
     after a sibling holding one of those binders under rigid structure (the
     major `?G ⊢ ?p → y ∈ B`), phase 5 only (`HypPlan.defer_wildcard`). Filled
     first, the minor matches every pool ref and pins `p` to each hypothesis
     in turn; the cut the proof needs exists only as what the major's child
     search proves.
   - **Recover from the goal hint.** The major's child tries `all_elim [#1]`
     against `?G ⊢ ?p → y ∈ B`. `all_elim`'s `@recover` source is its
     conclusion, and the checker treats the hint's metas as rigid, so its
     view match fails and `t` stays unbound. The explicit-binding retry in
     `validateSelectedRefs` reads the law off the hint instead, skipping the
     open subterms (`withRecoveredFromHint`): `y ∈ B` forces `t := y`.
   - **Read-back through definitions.** A view rule's conclusion `q` matches
     any target, so a child can prove `in_all_subsets S x` for the open
     `∀ ?x ?p`, equal only after unfolding. `readBackOpen`'s fourth pass
     (`forward.solveCorrespondenceUnfolding`) unfolds the child's def where
     the heads disagree. It walks the def body as a template and mints each
     hidden variable only after the whole match succeeds: minting spends a
     dependency slot of the parent theorem, and read-backs fail far more
     often than they succeed.
6. **Phase 6 — `@auto trigger` seeding** (`trigger.zig`; design:
   `docs/design_notes/trigger_seeding.md`). Only on a miss of the whole
   phase-1–5 ladder that did not stop the search (a phase's own fuel running
   dry does not block it; the global tick budget and the stack guard do),
   and only when the theory declares `@auto trigger`
   patterns (registry `trigger_by_rule`). Each pattern is e-matched against
   the *original goal's* subterms; every match mints a ground instance of the
   annotated rule (for `ax`: `φ ⊢ φ` per harvested formula) as a **seed** — a
   sourceless `DerivedRef` (empty recipe, concrete shape, rendered as a bare
   rule application whose binders the checker infers from the slot). Seeds
   enter a rebuilt derived pool (re-saturated with them as depth-0 sources
   when the theory has `@auto forward` rules, `trigger.seedOnlyPool`
   otherwise), and the ladder re-runs against it with fresh fuel. This closes
   the **elimination-major left-rule gap**: backward search cannot pin an
   elim rule's premise-only binder (imp_elim's `p`) from nothing, but a seed
   is a ref, and refs pin binders. It operationalizes the subformula
   property — the author's patterns enumerate the analytic leaf set (context
   members via `(hyp p)`, implication antecedents via `(im p _)`, …).
   Two supporting pieces: `DerivedPool.has_seeds` gates a seed-aware slot
   cost in `plan.buildHypPlans` (`HypPlan.seeded_len`: a pool-empty but
   seed-fillable slot costs like a ref slot, not generate-only — otherwise
   the seed-determined elimination major sorts after its wide open minors and
   is never reached), so pre-seeding phases plan exactly as before; and
   breadth stays byte-identical by construction (phase 6 runs only where
   the ladder missed). Guarded by the `nd_minimal` depth
   frontier tests in `tests/frontier_guards.zig`.

### How a miss is classified (`miss.zig`)

"Clean miss" means two different things, and the difference is deliberate:

- **Ladder gating** (`LadderOutcome` in `generate.zig`) decides whether the
  tails and the phase-6 retry run. A node-capped cell still ends as a plain
  `miss`. A retired core phase skips the remaining tail cells; phase 6 still
  runs after any retirement. The global budget or the stack guard
  (`stopped`) blocks it.
- **The failure report** (`miss.MissReport`, read by `source.zig`'s status and
  detail, the retry code action, and the bench's miss causes) calls a miss
  *truncated* when any limit cut it short: the global budget, the stack guard,
  a phase's fuel, forward saturation, or a node-capped pass
  (`SearchCounters.gen_node_capped_passes`). A truncated miss reports
  `budget_exhausted` status; only an untruncated one reads as exhausted.

`SearchCounters.gen_core_depth_done` records the deepest depth at which every
core phase finished with no find, exhaustion or node cap. When it reaches
`max_depth - 1`, the report says every depth below the limit was searched and
`miss.retryFor` raises depth; a node cap in the core keeps it lower on
purpose (see `searchedBelowDepthLimit`). `retryFor` doubles every limit that
was hit and the budget with them, and returns null when nothing can help (the
stack guard, no generation, or every hit limit already at its maximum).

### The cost-weighted per-call budget (`GlobalBudget`)

Per-phase fuel counts `tryCandidate`s, but per-candidate cost varies ~100x, so
fuel alone cannot bound wall-clock latency; a doomed miss used to burn up to
~12s across the five phases. `GenerateOptions.global_budget` (default 6.3e9,
null = off) caps the **whole call** — forward saturation plus all five phases
— in *weighted work ticks*: deterministic, machine-independent op counts
(`expr.zig` threadlocals) taken at four chokepoints with wall-calibrated
weights (`types.zig`): intern probe levels (COW base-chain hops, x600),
def-eq symbolic-node allocations (x190), non-interning tree-walk node visits
(shape builder / meta walks / suggestion rendering, x110), and a fixed
per-`tryCandidate` charge (x100k) for the clone/session overhead no per-node
tick sees. Units ≈ ns of calibrated wall, so the default reads as "≈6s of
work". Checked at candidate granularity (`Fuel.spend` + the generation node
entries), so a candidate mid-validation always completes; exhaustion unwinds
as `error.SearchBudgetExhausted`, exactly like per-phase fuel. Because tick
counts are deterministic, any cap above the corpus's most expensive FOUND
search provably preserves the frontier. The original 5e9 cap cut the depth
corpus fail-max 12.4s -> 4.9s (fails >3s: 151 -> 18) with breadth and depth
byte-identical; the memo plus the then-3.35e9 default brought fail-max to
~3.2s. The found-ceiling anchor drifts as the cost profile shifts: each
interner-scope extension adds one COW base-chain hop — the x600 tick
population — per intern inside a scope. After the `hookSolveOpen` scope the
ceiling was `add_suc_right` k=1 at 3.06e9 (~1.09x margin under 3.35e9); after
the `solveProof` scope (one hop per *generation level*, so every generation
path pays) it was `surj_wit_maps` k=1 at **3.34e9**, widening the default to
**3.85e9**; after `persist_negative` (the cross-cell failure memos spend no
per-phase fuel on skips, so each cell tries more distinct candidates and the
ladder burns more ticks before the finding cell) it is `surj_wit_maps` k=1 at
**5.48e9**, so the default is now **6.3e9** (~1.15x). The wall cost of each
raise has been flat-to-negative: the same profile shifts that inflate ticks
cut wall-per-tick (scope hops are near-free; memo skips avoid whole doomed
subtrees), so fail-max *dropped* at each wider cap. A further profile shift
that raises the ceiling past the default would silently drop budget-marginal
FOUND searches, so **re-measure this anchor and widen the cap (or refit
weights) before shipping any change that deepens scope chains or frees
fuel.**
Calibrate with
`bench-search --frontier=depth --verbose --global-budget=0` (per-run
`t=…M (i=… s=… sh=… tc=…)` columns) and refit the weights if the engine's
cost profile shifts.

Forward saturation (`forward.zig`, Stages 7–8) runs *before* backward search
when the theory declares `@auto forward` rules: bounded multi-layer forward
chaining over the ref pool produces a `DerivedPool` of derived facts, indexed
so backward search pre-filters them per slot. A derived fact that matches the
goal is itself a candidate (`validate.appendDerivedDirectCandidates`). When the
positional match conflicts, it retries member-wise through
`witness.solveCorrespondenceAcui`, so a context meta that no premise fixed
(`valid_elim`'s `?G` in `?G , p ⊢ q`) takes the goal members the fact leaves
over, `∅` when there are none.

### Metas must reach a solvable leaf

`@auto backward` rules (`rex`, `lall`, …) introduce **existential metas** for
binders the goal does not determine. A meta may not appear in the goal at seed
time — it is introduced *downstream* by the `@view`/`@recover` open-target solve
(`tryOpenGenerateSlot`, `emitOpenTarget`, `tryAcuiMemberWitnesses` in
`backward/backtrack.zig`; `backward/witness.zig`). Therefore:

> **Do not add a prune or forced binding that could clobber a slot a meta lives
> in (or could come to live in).** A "no meta in the goal container" check is
> *necessary but not sufficient*. Prefer to abstain. Route witness-bearing
> rules (`context.views.contains(rule_id)`) away from positional
> forcing/member reasoning on the raw `rule.concl`.

A carried meta must also survive the steps between its slot and its leaf. Inside
an open target's child search, a generated slot whose premise has no unknowns of
its own but still carries an ancestor meta (`imp_intro`'s `Γ , P ?t ⊢ ∀y P y`
under `ex_intro`) is routed to the open path (`carriesAncestorWitness`), not
the concrete one — `hook.solve` lifts only placeholder-free targets.
`emitOpenTarget` registers ancestor metas before its fully-solved check for the
same reason. Guard: `witness_carry_probe`.

Two more rules keep that path on a par with the concrete one. An eager rule's
open subgoal keeps its parent's depth (`solveOpen`'s `eager_step`, the
`hookSolve` exemption). And an open target's child proofs are not
interchangeable the way a concrete target's are: each fixes the witnesses
differently, and the parent can reject one assignment (a witness equal to
`all_intro`'s eigenvariable) yet accept the next. So `hookSolveOpen` collects
every child proof that reads back and offers them to the slot in turn
(`OpenProofSink`), after its interner scope has closed. Guard:
`witness_retry_probe`.

The eigenvariable condition itself is enforced where the search makes its
choices, not only by the final checker. It is read off the rule's own binder
dependencies: a non-bound binder whose `ArgInfo.deps` omits bound arg `x` may
not depend on `x`'s value. Two checks follow from it:

- `bindingsDepHit` classifies how a conclusion binding mentions such a
  value. Occurrences under a term with alpha rules don't count, since
  `@freshen` could rename them away. A `.rigid` hit is reached through
  rigid heads only (ACUI combiners count as rigid, since rearrangement
  never drops a member); a `.soft` hit passes through a def, a `@rewrite`
  head or an unavailable term, which conversion might remove. A `.rigid`
  hit on a rule with no view, `@fresh` or `@freshen` is pruned at seed
  time, before ref lookup: every assembly would fail the checker's
  DepViolation. Anything else is still tried, because a view may re-choose
  the bound binder at validation (martin_lof's `app_elim`), but only a
  candidate with no hit arms the eager cut. Otherwise a dead `all_intro`
  would hide `raa`. Guard: `eager_cut_dep_probe`.
- `banCarriedMetaDeps` handles a binder that still holds carried metas. On
  entry to an open slot it bans the value's dep bits from those metas, keyed
  by stable `meta_id` in the driver's `MetaDepBans`, and rolls the ban back
  on exit. `MetaStore.registerAncestorMeta` turns the ban into `allowed_deps`,
  so any pass that tries to fill the witness with the eigenvariable fails in
  `assign`. The ban is part of `canonicalOpenKey`, because it changes which
  fills are legal. Guard: `eigenvariable_ban_probe`.

The eager cut relies on the eager band being contiguous, and
`nonSplitCandidateFirst` sorts on split-ness before class. So
`split.conclusionIsSplit` counts only distinct *bare* binders on an ACUI
spine: `weak`'s `g , h` is multiplicative, but `not_left`'s `g , ¬ a` is
additive, because the `a` inside `¬ a` is a principal formula, not a context.
When `not_left` counted as multiplicative it sorted behind `raa`, so its cut
came too late. `raa`'s `Γ , ¬ ⊥ ⊢ ⊥` detours then spent the per-cell node
budget, and the empty-pool drinker missed. Guard: `empty_pool_witness_probe`.

This is a hard-won constraint (Stage 1 `forceAcuiRestBinder` regressed `drinker`
5/5→1/5 by over-constraining a witness slot). See `feedback_let_metas_propagate`
and `feedback_forced_not_heuristic` — the project preference is solid, forced,
explainable deductions over completeness-trading guesses.

### Eliminator seed metas (the one controlled seed-time exception)

The rule above ("a meta may not appear at seed time") has one deliberate,
tightly-scoped exception: **eliminator reconciliation metas**. Seeding a
dependent eliminator (`nat_ind_elim`) against a transparent-def-unfolded goal
(`add_comm_p m n`) exposes the def's bound variables as fresh *standard*
placeholders that land on the rule's binders. A variable threaded across more
than one hypothesis (an induction variable, a motive) must keep its occurrences
identified; scrubbing it to null (the legacy behaviour) both floods and loses it.
Instead (`backward/seed.zig:partitionSeedBindings`, keyed on `multiHypBinderMask`):

- a binder holding a **term** that mentions dummies is kept, with every
  occurrence of one dummy (in any kept binding) rewritten to ONE shared
  `.meta` leaf flagged `reconciliation_meta`
  (`addReconciliationMetaPlaceholderResolved`). The term fixes its premise's
  subject (`nat_ind_elim`'s step term `s` over `k` and `ih`), where scrubbing
  leaves a hole that induction floods. A dummy no binder holds (the `λ`
  variable in `id_trans`'s unfolded `J` term) can only be pinned by a ref;
  keeping such terms measured neutral against scrubbing them (#297), so they
  get no special case;
- a binder holding a **bare dummy** keeps it when the binder occurs in
  **>1 hypothesis** (an induction variable) or a kept term mentions the dummy
  (`ih` under `s`), so the meta stays shared;
- any other bare dummy (a single hypothesis's witness/output) is scrubbed to
  null and reconciles at its own generated slot via the open path;
- a *bare* meta leaf is always scrubbed — it constrains nothing.

A scrubbed dummy on a **bound** binder is a variable the def hid (`A → B`
unfolds to `Π x : A. B`, so `pi_form`'s premise `g , x : A ⊢ Ty B` needs an
`x` the goal never names). A ref can still supply it, and at k=0 one does.
When none matches, `backtrack.tryFreshBoundGenerate` generates the premise
in every phase, not only phase 5. It also takes a bare unfold placeholder
left on a bound binder by ref-side extraction (`app_elim`'s `f : A → B`), and
an intro rule's eigenvariable (`subset_intro`'s `x` in `G , x ∈ A ⊢ x ∈ B`):
a bound binder absent from the conclusion, where the goal fixes every other
binder of the premise and no fixed binding may mention the variable. These
criteria exclude two shapes. `inst`'s `x` may be a variable its fixed
`a : term x` already mentions, so a fresh fill is a wrong guess (church
`SPEC`). `dvd_elim`'s `k` sits in an elim-shaped premise whose other binders
come from a sibling ref, so fills are mostly doomed (euclid). The
binders open as `.bound_choice` metas in a `fresh_bound` open slot, which
runs the constrained child-search-first ladder, so a proof below can still
name the variable however deep its ref sits. Only when the child search
leaves one unsolved (`weaken`'s conclusion just echoes it back) does
`tryPoolWitnesses(.fresh)` give it a variable that occurs in no binding, and
generate the now-concrete premise. The slot's later open fallbacks skip a
premise opened this way. Every fresh choice gives the same instance
up to renaming, since the variable must avoid every variable of the instance,
but not the same refs: MM0 has no alpha-equivalence. So `assignRefNames`
first tries the bound variables the refs put in the same place (matching
each part of the target that mentions the variable against same-headed ref
subterms), and only then the first free `@vars` names, which would give
`nat_ind_elim`'s step `k` the name `ih` because `ih` sorts first. Guard: the
`add_comm step names` scenario. Picking a name before the child search is
equally complete (the open path is still the fallback) but slower: each miss
costs a doomed concrete child search first. The exception is a variable the
premise substitutes away (`nat_ind_elim`'s base case `g ⊢ z : [k/zero] C`).
A `.bound_choice` meta reads as a bound variable with its own dep bit, so the
substitution reduces and the variable leaves the target while the bindings
(`C`) still hold it. No proof of the premise can name it, so the
fully-solved check in `emitOpenTarget` sends the slot straight to the pool
rung, whose ref names come from the bindings. Guard: the `add_comm base case`
scenario. Guards for the fresh premise itself: the `arr_form` and `arr_elim`
depth rows of `martin_lof_frontier`.

A hidden variable inside a fixed binding of the premise qualifies the same
way: a kept seed meta a bound binder still holds (`ih`, when no ref pinned
it), or one inside a kept term (`reflt`'s `t := λ x. x` when the goal `G ⊩ T`
unfolds `T`'s hidden `.x`). `rebindHiddenVars` replaces it, in every binding
that mentions it, with a `.bound_choice` meta of the slot's store, and a
solved fill materializes those bindings (`OpenSlot.rebound`). The child
search names the variable (`lamT` below `reflt`), or the pool rung does. Only
hidden variables in the generated premise's own binders are rebound: this
slot's solve cannot fill another premise's. A seed meta keeps its dummy's dep bit and reads as a
bound variable (`TheoremContext.leafInfoWithArgs`), so a substitution over
it reduces as over the dummy: `sep_intro`'s `[x/t] p` under `image` must
reduce before its premise can be generated. Guards: the `add_zero_right`
depth rows of `martin_lof_regular`, and church `TRUTH`.

The dual case is a bound binder of a child-search candidate with an
occurrence strictly inside what a goal meta stands for. In phase 5, `eqTR1`
opens its cut `b`, so the child target is `G ⊩ ≃[𝔹] T = ?b`. `T_DEF`
matches it, but its `{x}` lies inside `?b`'s value `(λ x. x) = (λ x. x)`,
so the checker cannot infer it (`MissingBinderAssignment`). Likewise
`fact_pos`'s `n` against `all_elim`'s `⊢ ∀ ?x ?p` lies inside `?p` as well
as on `?x`. Whatever names such a variable must also build the meta's
value, and only this candidate does. So the explicit-binding retry in
`validateSelectedRefs` gives it a `@vars` variable that occurs nowhere in
the bindings or the goal (`withFreshBoundVars`), and the read-back
carries that choice into the metas. A binder that only bare metas match
(`var`'s `x` in `g , ?x : A ⊢ ?x : A`) says no more than that the meta is a
variable. That is the minting slot's to name. Naming it at every such leaf
as well turned doomed child searches into candidates and cost martin_lof
`suc_eq` and `ap_motive` their node budget. Guards: church `TT`, euclid
`fact_pos_inst`.

These seed metas are resolved by a **meta-aware ref match**
(`backward/match.zig:tryMetaAwareHypMatch`, gated by
`TheoremContext.hasReconciliationMetas()`): it `solveCorrespondence`s the
instantiated hypothesis against a matched ref and derefs the solved metas back
into the bindings, so a ref-match on one hypothesis (the motive) pins the shared
variable for the sibling slots. It is **scoped to the `reconciliation_meta` flag
precisely so it never touches the downstream carry-to-leaf/witness metas above** —
those must stay deferred to leaf forcing (the invariant is preserved, not
broken). Soundness still rests on `tryCandidate` revalidation: a positional
mis-resolution under a commutative ACUI context yields a wrong binding that fails
validation, never an unsound proof (so no pre-guard is applied — see the ACUI
note in `tryMetaAwareHypMatch`).

Two supporting pieces: the step hypothesis's bound binder (`ih`) is opened *in
place* inside its ACUI context combiner rather than hard-blocked — via
`OpenInstantiateOptions.open_bound_in_combiner`, set to
`slot.mode != .witness` (see `OpenMode` below) so the witness path (which
resolves such binders by enumeration) keeps the old block; and the substitution
redexes in a generated target (`[k/n] C` = `sb_ty …`) are reduced for emission by
`backward/redex.zig:reduceRedexOnly` (structural recursion that reduces only
`rewrites_by_head`-rooted subtrees, leaving ACUI association byte-identical to the
pool refs). It descends only through heads with a `@congr` rule: the checker can
convert a line only along such a path, so a redex under any other head (a
relation without a `@congr`, say) stays as the rule states it. Full rationale + benchmarks:
`docs/design_notes/induction_eliminator_metavar.md`.

## `@auto` rule annotations

`auto?`/`apply?` do not enrich a rule with forward/backward automation unless the
theory **opts that rule in** with a doc-comment immediately before its
declaration:

```
--| @auto forward
term all_elim ...     -- enroll for forward saturation
--| @auto backward
term ex_intro ...     -- enroll for open backward generation
--| @auto eager
axiom rim ...         -- invertible: front band + set-commit cut + depth-free
--| @auto eager 2
axiom rand ...        -- same, lower intra-band priority (branching rules)
--| @auto trigger (hyp p)
axiom ax ...          -- seed φ⊢φ per goal context member (phase 6)
```

Exactly one mode is required (`error.InvalidAutoAnnotation` otherwise; `eager`
takes an optional priority ≥ 1). Parsing lands in
`RewriteRegistry.processAuto` (`rewrite_registry.zig`), which stores the
rule id in one of the mode sets (`trigger` additionally stores its pattern in
`trigger_by_rule`; `eager` stores its priority in `auto_eager_rules` and also
enrolls the rule backward); the search engine queries them via
`isAutoForwardRule` / `isAutoBackwardRule` / `eagerPriority` /
`autoForwardRuleCount` / `triggerRuleCount`. **There is
no shape-based auto-classifier** — enrollment is entirely manual. An un-annotated
rule stays concrete-only, which is what keeps un-annotated theories byte-identical
to pre-automation search. Annotating a rule never changes *validity* (every
assembly still re-validates through `tryCandidate`); it only widens the *search*
— except `@auto eager`, whose set-commit cut deliberately *narrows* it under
the user's invertibility declaration, which the search trusts (see
"`@auto eager`" below).

### `@auto eager [N]` — user-declared invertible rules

An eager rule is a user-declared **invertible** ("don't-care") backward step:
conclusion provable ⟺ premises provable, so backward application is a
decomposition, never a choice. The annotation is validated at parse time to be
*invertible-shaped* — every hypothesis binder conclusion-determined
(`error.EagerRuleDefersWitness` otherwise; a premise-only witness binder like
`rex`'s `t` would make a depth-free eager step a self-feeding contraction).
Three coupled effects (docs/design_notes/eager_rule_scheduling.md has the full
rationale):

- **Band ordering** (`generationOrderClass`, refining `witnessClass` below):
  within equal split-ness, class 0 < eager (by priority 1..255) < class 1 <
  class 2. Closing rules stay first; the user's invertible ladder runs ahead
  of its unannotated class-1 peers, alpha (non-branching, priority 1) before
  beta (branching, priority 2) if the theory says so. Within a band,
  candidates sort by `match_specificity` (rigid conclusion application
  nodes that meet the same head in the goal), higher first, so `t_lam`
  goes before an elimination whose conclusion fits any judgment.
- **Set-commit cut** (`exactWithSession`): once an eager candidate *applies*
  — reaches a child solve (`ApplyCandidate.reached_child_solve`, set at
  `emitGeneratedSlot`'s hook call) or yields a validated result — the
  remaining non-eager candidates at that node are skipped. All eager
  candidates (other bag members, other eager rules) are still tried. The
  trigger is application-reached-children, NOT enumeration: a candidate
  rejected at conclusion assembly never arms the cut. There is no cut-free
  retry: a mis-annotated (non-invertible) eager rule can lose proofs. Until
  2026-10 a clean miss re-ran the whole ladder without the cut; it never
  recovered a proof on the benchmarks and cost tait-style misses ~15×.
- **Depth exemption** (`hookSolve`): an eager application's subgoal is solved
  at the parent's remaining depth (the level is added back), so counted depth
  ≈ number of genuine choice points, and tall deterministic ladders fit the
  default `max_depth`. Eager steps still pay nodes, per-phase fuel, and
  global ticks — a wrong annotation burns budget, never diverges — and the
  `visited` path guard catches cycles. `genDepth` mirrors the exemption
  (eager edges cost 0) so `concrete_ok` replays stay consistent with the new
  depth semantics.
- **Nested binding handoff** (`ApplyCandidate.internal_child`, set from
  `ExactOptions.internal_open_child`; render at the accept point in
  `backward/validate.zig`): an accepted eager candidate inside an internal
  generation child solve becomes a NESTED inline node of a parent assembly,
  where the checker would have to re-infer its binders top-down from an
  ACUI-reassociated hint — and a bag with two same-shaped members is
  genuinely ambiguous from the hint alone, so deep eager ladders rejected at
  validation and the find fell into the expensive phase tails. The search
  already resolved the binders, so validation renders them all as explicit
  bindings on the spliced application; every level of a generated ladder
  carries its own values and the parent re-check never guesses.
  Suggestions surfaced directly to the user are untouched (top-level
  candidates are not `internal_child`).

Theories without eager annotations take none of these paths (every gate checks
`autoEagerRuleCount() > 0` or an absent `eagerPriority`), which keeps the
corpus byte-identity contract intact by construction.

### `@auto trigger PATTERN` — ground seeds from goal subterms (phase 6)

Only on **hypothesis-free** rules (`ax`-style; a seed has no premise recipe).
The pattern is a parenthesized prefix tree over term *names*, the rule's own
binder names (captures), and `_` (wildcard) — `(hyp p)`, `(im p _)`. A rule
binder the pattern does not name must be a non-bound binder of an
ACUI-combiner sort (it defaults to the unit at harvest, then
`normalizeAcuiUnits` cleans the instantiated conclusion); anything else is an
annotation error, so every seed is ground by construction. Validation checks
term availability, arity (derived from the term declaration), capture/nested
sorts, and that bound argument positions carry only `_`. See the phase-6
entry above and `docs/design_notes/trigger_seeding.md` for what the patterns
should enumerate (the analytic leaf set: context members, implication
antecedents, disjuncts — the connectives your elim rules move into context).

### `@auto forward` — enrich the fact pool before backward search

Gated by `autoForwardRuleCount() > 0` in `generate.zig`; `forward.zig fireRule`
fires only enrolled rules. A forward rule matches its **hypotheses** against the
ref pool (transparent-def unfolding allowed), solves the ordinary binders, leaves
any binder the premises don't determine as a **universal metavariable** (a
*family* fact, not a concrete conclusion), and materializes a goal-shaped
(`@recover`-derived) derived ref that is indexed for per-slot pre-filtering.
Bounded by `ForwardOptions` (`max_forward_layers/facts/rule_attempts/
match_tuples`).

Use forward on **elimination / destructor rules** — the ones that consume a
hypothesis and emit something smaller or more concrete:

- universal elimination / instantiation (`all_elim`: ∀-fact + witness → instance),
- conjunction / pair destructors (peel a member out),
- range-restricted, "decreasing" rules whose forward closure stays bounded.

Forward earns its keep through **joins and layer composition**: a universal family
fact joined against a concrete fact yields a new concrete fact, and successive
layers compose buried witnesses the backward search would otherwise have to guess.
A forward rule with no usable `@recover` surface simply derives nothing (silently
inert, not an error), so a bad annotation wastes budget rather than corrupting
results.

### `@auto backward` — open existential sub-goals

The open-generation policy is computed once per candidate slot as
`OpenMode {none, constrained, witness}` (`openMode()` in
`backward/backtrack.zig`): `.witness` is exactly `@auto backward` enrollment;
`.constrained` is the phase-5 constrained-backward-MP concession for
un-enrolled rules (child proof must determine every meta by read-back, no
carrying, no invention; `@abstract` motive inference rides this branch);
`.none` means no open generation. The mode gates `tryOpenGenerateSlot`'s
entry and split re-entry, `open_bound_in_combiner`, `registerAncestorMetas`,
and the force-first witness ladder — scheduling (`witnessClass` /
`generationOrderClass`) deliberately keeps reading enrollment directly
(ordering and capability are separate axes; see task #88). Principal
enumeration (`tryPrincipalEnumerate`) is NOT mode-gated: it is structural
(see the three-mechanism table above).

When a hypothesis cannot be closed by the pool or by an
ACUI context split, a `.witness` rule instantiates the binders the goal does not
determine as **existential metas**, turning the hypothesis into a sub-goal the
generation hook solves. Witnesses are committed in a deliberate order: forced from
a concrete ACUI member first, then a generated sub-proof, then coupled/invented
last (invention needs a `@vars` pool; it is slot-local, not a retry phase — see
the phase ladder above).

The member-force pass cross-matches every meta-bearing fragment of the open
target (innermost first) against every concrete region member, descending
through the member's subterms so a wff fragment can meet a coercion-wrapped
member. That descent is **binder-aware** (`matchFragmentAt` in
`backward/witness.zig`): a witness value read off a match under a member's
still-intact binder would let that bound variable escape into a sibling
member, so any assignment mentioning a crossed binder's variable is rejected
at match time — the same capture discipline `solveBound` applies to
fragment-side binders. Without it, every such scope-escaping fill launched a
full doomed child search (this was tait forall_mono's "node-bound" floor: the
node budget was being spent on capture-garbage, not on the honest carry
recursion).

The generated-sub-proof path reads the witness back by matching the child's
checker-accepted conclusion against the open target (`generate.zig
hookSolveOpen`), in **four passes**: plain positional `solveCorrespondence`;
the ACUI-unit-normalized retry (a stray `emp` in the child conclusion); and a
**member-wise ACUI-aware pass** (`witness.solveCorrespondenceAcui`) for
conclusions that are ACUI-equal but reordered/reassociated — the checker
bridges conclusion-vs-hint modulo ACUI, but the checked line keeps the child
rule's own association, so an unlucky rule-conclusion shape defeats the
positional passes. The third pass matches commutative combiner regions as
multisets (identical members cancel; structured members unify with
deterministic backtracking; one whole-member meta absorbs the re-joined
complement) and **relabels** the returned conclusion to the materialized
target, letting the recompile insert the ACUI reorder bridge (the transposition
memo's discipline). It abstains on non-commutative subsets, multi-meta
partitions, region overflow, and a deterministic member-trial cap; only OOM
propagates, and the pass is skipped entirely when no commutative combiner is
registered. The unit-normalized second pass is NOT subsumed: it alone covers
non-commutative (AU) subsets. Diagnostics: `acui_rb=recovered/plausibly-missed`
(disjoint outcomes) in the bench `--counters` dump.

The fourth pass (`forward.solveCorrespondenceUnfolding`) matches up to
transparent def unfolding, on either side, and relabels as the third does
(`unfold_rb=` in the `--counters` dump). A hidden variable of an unfolded def
must stand for a bound variable the def's arguments do not mention, distinct
from its siblings'; one met against a meta is minted as a placeholder (a
dependency slot of the parent theorem) only after every other check, the
solve of the whole target, and a check that enough slots remain have
succeeded. A body subtree over a hidden variable met by an open meta waits
until the rest of the body is walked; if something else solved the meta
meanwhile, the subtree is walked against that value like any other.

The coupled pass has three sweeps. The equal-unify sweep pairs meta-bearing
region members that unify *equal* (`witness.unifyMembers`). On its
clean miss, the **complementary sweep** derives *complement shapes* from the
visible hypothesis-free rules (`collectComplementShapes`): a rule whose ACUI
conclusion repeats one binder across two distinct members (tait `ax`'s
`⊢ a , (¬ a) , d` — coercion-wrapped as `hyp(a)`/`hyp(¬ a)`) declares that
the two members it closes are the same formula under the wrapper, so two
meta-bearing goal members with *different heads* (`¬ R ?x y` vs `R z ?w`,
both `rex` outputs with no rigid anchor) are co-solved through the template
pair (`unifyMembersThroughShape`: hole occurrences capture-then-unify). This
is what closes a one-sided calculus' both-witnesses-open leaf, where no left
rule ever produces a rigid anchor. Theory-agnostic by construction — the
shapes come from rule templates, never from knowing `¬` is negation — and
ordered after the equal sweep so theories without such rules (or goals the
equal sweep already solves) are byte-identical.

The **anchored sweep** is the two-sided counterpart, run when both region
sweeps emit nothing. A hypothesis-free rule may repeat a binder as a region
member and as a bare position *outside* every region: ND `ax`'s `g , a ⊢ a`
pairs the context member `hyp(a)` with the succedent (`collectAnchorShapes`
records the member template and the argument path to the outside site). A
meta-bearing context member (`R ?t y`, an `all_left` instance) is then
co-solved with the formula at that path (`R z ?w`, an `ex_intro` premise) by
`unifyMemberWithAnchor`. Only one meta-bearing member is needed, since the
other side is not a region member at all. Without it the analytic ND proof of
`∀x R x y ⊢ ∃w R z w` is unreachable (the `nd_fol` ex_all_to_all_ex gap).
Theories whose `ax` pairs lie inside regions (tait, additive_fol) derive no
anchor shapes and are unaffected.

Use backward on **introduction / witness rules** — the ones that build a goal up
from sub-goals:

- existential / disjunction / conjunction introduction,
- `@view` + `@recover` rules carrying an existential witness,
- rules where proving a child pins a binder in the parent.

> **Discipline (the load-bearing hazard).** *Backward ⟺ intro/witness; forward ⟺
> elim/destructor.* Do **not** put `@auto backward` on a **multiplicative
> elimination** rule (`or_elim`, `ax_mp`, `ex_elim`): opening the eliminated
> formula spawns an intro fan-out that exhausts the node budget, and the ordinary
> ref-discharge path already handles those rules. (`bot_elim` is the
> backward-safe exception.) Mirror-image: forward on an intro rule produces
> family facts nothing will consume. See `project_auto_annotation_discipline`.

## Backward hypothesis ordering and candidate screening

Two narrow heuristics shape *which* backward work the engine does, both validated
breadth-byte-identical (they never change a one-shot suggestion; they only move
the multi-line **depth frontier** — how much of a real proof `auto?` can
regenerate from the bare goal).

**Generate-only slot cost (`hypSlotCost`, `backward/plan.zig`).** When a rule has several
unresolved hypotheses, `buildHypPlans` orders them most-constrained-first
(`hypPlanLessThan`). A slot's cost is its initial ref-pool size — *except* a
**generate-only** slot (`initial_len == 0`, no pool ref fits it at seed time) is
**not** cheapest: it matches the whole generation space, an enormous branching
factor. Ranking it by `0` would sort it first; instead it is costed as
`generate_only_cost` (= 4) refs, so it sorts after a well-constrained ref slot
(cost 1–3) but ahead of a loose bare-binder one (cost > 4). This generalizes the
`defer_generate` `!is_app` guard to the whole comparator. The value 4 is the
swept optimum on the depth frontier; higher costs defer gen-only behind loose
refs and plateau lower. In phase 5 one key ranks above cost:
`defer_wildcard` (see phase 5 above) sorts a wildcard-sequent premise after
the rigid occurrences of its shared binders, including after a
`defer_generate` major, which is the occurrence that must pin them.

**Relation-transport screen (`RewriteRegistry.isRelationTransport`, applied in `backward/backtrack.zig`).** A `@relation`
bundle's *transport* rule (e.g. `mpbi`: `a ↔ b, a ⊢ b`) has a **bare binder
conclusion**, so backward it is a candidate for *every* goal — yet it is a
rewrite/congruence tool, never a backward proof step. Left unscreened it floods
backward search with thousands of doomed attempts per line (and the gen-only cost
above makes each one more expensive, because its ref-fillable premise gets pulled
ahead of its open premise). `exactRuleCandidates` skips it. The screen is
deliberately narrow — keyed on the registered `transport_name`, **not** on the
bare-conclusion shape alone — so a plain modus-ponens axiom (`ax_mp`/`mp`), which
shares the shape but is *not* a relation member, stays a backward candidate (it is
load-bearing in Hilbert-style proofs). This is what lets the gen-only cost help
`mp`-chains (peano, zermelo_hilbert) without breaking the additive ACUI proofs,
where the same cost would otherwise reorder `mpbi`'s premises destructively. See
`project_premise_ordering_shared_pin`.

## The COW interner invariant

`TheoremContext.clone()` (`expr.zig`) is **O(1) copy-on-write**: the clone
borrows its parent's `ExprInterner` as an immutable base prefix
(`base`, `base_count`); `node(id)` delegates to the base for `id < base_count`.
This makes the per-candidate clones in the hot search loop cheap.

The soundness invariant: **every clone is short-lived scratch whose parent
outlives it and does not move or free while the clone is alive.** Violating it
is a use-after-free that ReleaseFast *masks* (corrupt reads land on "no
opinion", so results look stable) and debug catches as a corrupt-tag crash.

`flatten()` materializes a clone into a standalone interner (deep-copies the
base nodes, preserving every `ExprId`). **Any "clone a candidate theorem, then
free/replace the source" pattern must `flatten()` the clone first.** Current
flatten sites: `candidate.zig:commit`, `check/apply.zig:SpeculativeAttempt.promote`
and `backward/seed.zig:cloneCandidateWithPrincipalPin` (the fan-out
variant outlives the `base` candidate that `appendRuleCandidates` frees). See
`project_cow_interner` and `project_cow_fanout_dangling_base`.

Two cost corollaries (2026-07-05, the tait `resolution` budget fix):

- The global budget's intern ticks count **probe levels of the base chain**,
  so every extra clone layer between the work theorem and the validation
  clone multiplies the tick cost of the whole validation. `candidate.zig`
  therefore splits validation into `probe` (const theorem/vars; returns a
  `Probe` whose theorem is a COW clone BORROWING the caller's, so it must be
  deinitialized first) and `commit` (flattens and swaps the attempt into the
  caller's state; returns the line index). Callers never pre-clone. Removing
  the three pre-clone sites cut resolution's k=6 floor 3.75G→3.09G (under
  the default cap) with byte-identical corpus frontiers.
- Only `commit` pays a whole-interner `flatten()`; `flatten`'s contract
  reserves that cost for committed lines (rare). A probe never flattens.
- A probe drops any inline-conclusion sink entries it recorded and restores
  the caller's diagnostic, whether it succeeds or fails.

## Indices and pruning (performance, completeness-neutral)

These narrow the search without dropping proofs. Each must be a *sound*
over-approximation (never reject a provable candidate):

- **`rule_index.zig`** — goal-shape → candidate rule ids.
- **`refs.zig` + `ref_index.zig`** — the reference pool (proof lines + theorem
  hyps usable as hypothesis fillers), shape-indexed per slot. `shape.zig` is
  the shared shape-extraction/indexing core; `clipper.zig` the discrimination
  structure.
- **`abstract_prune.zig`** — for `@abstract` (Leibniz `eq_replace`-style) rules,
  a one-hole-context feasibility prefilter on the broad whole-pool slot
  (`abstractDefiniteMismatch`), killing the O(pool²) tuple flood.
- **`context_prune.zig`** — discharge-aware ACUI context prefilter: rejects a
  hypothesis context contributing more rigid members absent from the goal than
  the view discharges.
- **`finalConclusionPlausible`** (`backward/plausible.zig`) — last cheap reject
  before the full checker re-derivation. Includes a **re-pin strengthening**
  (`repinConclusionPlausible` / `pinRigidBinders`): copy the bindings, fill any
  unbound conclusion binder the goal forces at a rigid (non-ACUI) position, and
  re-run the check — so a binder shared between a rigid position and a repeated
  occurrence or ACUI member (e.g. `ax`'s `P` in `G , P ⊩ P`) can be required
  present and reject `W ∉ Γ` early. Gated by `repin_prune_enabled` (the Driver
  sets it on for `auto?`); the re-check is skipped when re-pinning adds nothing.
  `pinRigidBinders` descends only into args the head determines
  (`argDetermined`, see "Which arguments a head determines" below), so a def
  that drops an argument (the const trap), a `@rewrite` head, or an ACUI spine
  never yields a pin.
- **deep-unfold ACUI member prune** (`backward/plausible.zig` `deepMemberWouldPrune`
  → `acui.acuiBoundMembersDeepMismatch`) — strengthens the member check
  for def-dense theories. The plain member check abstains the moment a
  transparent-def head differs, so church's `ax`/membership reject-flood (every
  leaf/member pair involves a def) never prunes. This variant instantiates each
  fully-bound required context-member leaf concretely and requires *some* goal
  member to survive a COMPLETE (to-fixpoint) def-unfold comparison
  (`unfoldedExprMismatch`, injected as a comptime fn to break the
  plausible↔acui import cycle); it rejects when a required leaf
  matches no member. Cracks church choose_eq (42.5s→1.9s) while leaving the
  `eqmp` open-cut flood (DISJ_CASES) untouched (a cut isn't a membership
  question). Its re-pin shares `pinRigidBinders`, so it pins only what the
  goal forces. Gated by
  `deep_member_prune_enabled` (Driver default-on for `auto?`;
  `--no-deep-member-prune` for A/B). Completeness-neutral: breadth byte-identical
  + depth TOTAL preserved.
- **hyp-vs-ref member consistency** (`backward/plausible.zig`
  `hypRefMembersPlausible`, called from `validateSelectedRefs` after
  `finalConclusionPlausible`; counter `hyp_ref_prunes`) — refutes a
  (candidate, refs) tuple when no conclusion-vs-goal binder assignment makes
  every pool-ref conclusion ACUI-member-consistent with its instantiated
  hypothesis. This is the loose-candidate killer for one-sided sequent
  theories: with the whole conclusion inside one ACUI region, seeding pins
  nothing (`partialMatchTemplate` never descends ACUI spines) and 1-premise
  rules are excluded from principal fan-out, so a `ror`-style candidate's
  premise slot is a fully-wildcard sequent that would otherwise sweep the
  entire pool through full `tryCandidate` (tait resolution: 579 → 14
  full-validation rejects, budget-to-FULL floor >10G → 5.51G ticks). Three
  necessary conditions per assignment (enumerated by strict
  `matchTemplate` over the region's goal members, DFS with shared-binder
  propagation, ≤32 leaves): every determined hyp member must possibly appear
  in the ref; every ref member must be a determined member or reachable
  through a rest binder's goal-member pool; and every goal member the
  conclusion's non-rest members do not consume must appear in any ref whose
  hypothesis carries that region's full rest. All uncertainty abstains
  (transparent-def heads, placeholder members, hyp-only binders, member
  templates embedding ACUI or def heads, cap overflows, generated refs), so
  a winnable tuple is never pruned. Corpus-validated: breadth byte-identical,
  depth per-theorem fractions identical.
- **bound-binder slot equality** (`acui.boundRegionRefEqualPlausible`, the
  `.binder` case of `acuiClosedRegionPlausible`, run per fill in
  `matchOneHypWithSnapshot`) — a bare ACUI binder already bound (an ND rule's
  `g`, pinned by the conclusion) is a closed one-summand region, so the ref at
  that position must hold exactly the bound value's members. Without it such a
  fill classifies `.unknown`, and a pool line proved under a different context
  pins an elimination's minor-premise binder, after which the whole major
  premise is generated before validation rejects the context (nd_fol: the
  `bi_elim` tower flood). Abstains on opaque members and on any member
  conversion could change. Corpus-validated: breadth and depth identical.
- **conclusion member check** (`seed.conclusionMembersPlausible` →
  `acui.acuiBoundMembersPlausible`, counter `conclusion_member_prunes`) — every
  fully-bound required member of an ACUI conclusion must have a candidate in
  the goal. Presence needs only associativity, so it holds for every
  combiner. Without idempotence each required member needs a goal member of
  its own (one bipartite matching, `acuiRequiredMembersPlausible`): a rule
  needing two distinct entries after `g` cannot match a context holding one.
  An open meta in the goal (the rest of a context a premise left unresolved)
  may hold any member, so it never refutes one.
- **redex conclusion prune** (`plausible.redexConclusionMismatch`, called from
  `validateSelectedRefs`; counter `redex_conclusion_prunes`) — a `@rewrite`
  head in the conclusion gives the plain checks no opinion. Once the refs are
  chosen, it binds what they force, fills every other ordinary binder with a
  placeholder, reduces each redex in a scratch clone, and rejects the tuple
  when the result cannot match the goal subterm at that position. A
  placeholder never mismatches, so it rejects only what no choice of the
  unbound binders could match.

### Which arguments a head determines (`argDetermined`)

`head_class.zig` classifies every term head once for all of matching
(`HeadClass`: rigid, def, acui, rewrite, unavailable). A rigid head is a
primitive term or a def without a body: no conversion changes it.

A lockstep walk of a template against an expression may compare, pin, or
descend into argument `i` of head `h` only when `h(a) ≡ h(b)` forces the two
arguments equal (`head_class.argDetermined`, reached through
`semantic.argDetermined`). A rigid head determines all its arguments. A
transparent def determines an argument only when its body places it at a path
of such heads, so a def that drops an argument (`def K (a b) = a`, the const
trap) does not; a binder-introducing def is no exception, since its dummies are
fresh on both sides. An ACUI combiner, a `@rewrite` head and an unavailable
term determine none.

The prunes, seeds and extractors take their argument pairs from
`backward/lockstep.zig` (`templateArgs`, `exprArgs`), which pairs only determined arguments of
applications with the same head and arity. That covers the conclusion and hyp
prunes (`templateDefiniteMismatch`, `rigidExprMismatch`, the member, redex,
closed-region and recover checks), the seeds and extractors
(`partialMatchTemplate`, `extractHypPartialBindings`, `pinRigidBinders`), and
the fan-out locator, so every pin they make is forced by the goal for any
provable candidate and every mismatch they report is real. The walks that only
stop at binders and combiner regions (the re-pin, the repeated-binder conflict,
the closed-region and hyp-ref region collectors, the fan-out locator) share
`lockstep.walk`, and both seeds read through a template-side def unfolding
with `def_match.walkDefBody`. Walks outside `lockstep.zig` either descend
only rigid heads, which determine every argument (`abstract_prune`'s
`matchTemplateStructural` and `abstractDefiniteMismatch`), or build a solution
the validator re-checks: `forward.solveCorrespondence*`, `witness.zig`'s
read-back and anchor walks, `trigger.matchTriggerPattern`, and the split-site
locator (`split.findSplitSite`), which descends every argument of a same-head
application because the split pass only adds candidates.

### Contexts that are ordered, and where a split can happen

- **Ordered-context extraction** (`def_match.extractOrderedSpineBindings`) — a
  combiner declared with neither commutativity nor idempotence is a sequence
  (`acuiIsOrdered`). Seeding flattens both sides to their unit-free member
  lists and aligns them from each end, never along the binary spines, whose
  association is arbitrary. With one multi-member leaf (an unbound bare
  binder) between the aligned ends, that binder is forced to the members in
  between. martin_lof's `var` (`g , x : A ⊢ x : A`) against
  `g , k : Nat , ih : Nat` in any association pins `x : A := ih : Nat` and
  `g := g , k : Nat`. Commutative combiners use the multiset extractor
  (`acui.extractAcuiMemberBindings`) instead. Under idempotence a member a
  bound sibling holds may serve another leaf as well, so that extractor (and
  the principal fan-out) consumes nothing there.
- **Split sites** (`split.findSplitSite`) — only a bare spine binder of an
  ACUI conclusion distributes context members. A binder inside a fixed summand
  (the `A` of `g , x : A`) is not a context, and enumerating contexts for it
  would be ill-sorted, so it is never a split site.
- **Split candidates** (`split.buildEnumerator`) follow the combiner's laws
  (`bag.lawOf`). A set (ACUI) offers sub-sets of the distinct members, since
  siblings may overlap. A multiset (ACU) offers sub-multisets of what the
  principals and bound siblings leave (so `a , a` is a candidate), forced when
  no sibling is open. A sequence (AU, or AUI) offers contiguous runs, each end
  pinned when the summands on that side have a known member count:
  `g , x : A` against a three-entry context offers only the first two entries.
  A bound sibling holding a meta or a def may stand for any number of entries,
  so it leaves its end open, and in a set or multiset split it counts as an
  open sibling.

Every flattening of a combiner application in the search goes through
`backward/bag.zig`, the search's handle on `acui_bag.zig`, which the checker
shares: `flatten` splices nested applications, drops the combiner's own unit
(never another combiner's) and keeps duplicates in order, returning null on
overflow so callers abstain rather than read a truncated bag. The exception is
`witness.flattenRegion`, which also dereferences solved metas.

The same `finalConclusionPlausible`/`tryCandidate` path also carries the
**reject-verdict memo** (`candidate.zig`, `types.VerdictMemo`): a `tryCandidate`
verdict is a pure function of the concrete assembly + goal + base theorem, so a
*terminal* reject is memoized and re-encounters of the identical assembly
short-circuit to `error.MemoizedReject` instead of re-running the checker. It
spans `generateTopLevel`'s retry phases, keyed by `applicationSignature` over
the assembly's source syntax plus the goal's canonical content
(`types.hashCanonicalContent`). **Soundness rule:** key on the full concrete assembly, never
the subgoal (subgoal-provability is non-monotone across phases); and do **not**
memoize a *retry-eligible* reject (`MissingBinderAssignment` / holey
`HypothesisMismatch` on a bare assembly), because `validateSelectedRefs` retries
those with explicit bindings and may succeed — memoizing the bare reject would
skip that retry. Holey goals are excluded (pointer-keyed, ABA-unstable). The
memo + re-pin are owned by the generation call, which threads them (with the
Lever E policy and its verdict cache) as a `types.SearchRuntime` beside the
value-only `SearchCounters` sink — behaviour never depends on whether anyone
is observing, and a reused observer block carries no policy over. Both are
default-on for `auto?`; `--no-search-memo` disables both for A/B.

**Interner-scope caveat (id stability).** Raw `ExprId`s are stable only while
the work-theorem interner is append-only. That is *no longer true for the
whole search*: BOTH child-solve seams (`hookSolveOpen` for open targets and
`solveProof` for concrete ones) run each child search against a discardable
COW clone of the work theorem (`generate.zig`), so ids minted inside a scope
are re-minted with different content after the scope is discarded (ABA), and
only root-level interning (pass goal, pool-var dummies, trigger seeds,
forward saturation, plus each sub-solve's own lifted target / canonical key /
read-back conclusion in its parent) persists. Every persistent memo that
outlives a scope therefore keys
expressions by scope-stable canonical CONTENT, never a raw id:
`concrete_ok`/`concrete_fail` (`contentKey`), the reject-verdict memo
(`applicationSignature` → `hashCanonicalContent`), the deep-verdict cache,
and `open_fail`/`visited_open` (canonical byte strings). Content keys make
scope exits free — nothing to evict, and successes first proved inside an
open scope stay reusable afterward (the transposition memo works across
open-chain boundaries with no re-keying). Leaf identities are chosen so
hash-equal ⟹ interchangeable even across a discard: theorem vars by index,
dummies by (index, sort), placeholders by (pid, class, sort, deps, meta_id) —
see `hashCanonicalContent`'s doc comment. **Any new persistent cache on the
Driver or `SearchRuntime` must follow the same rule: canonical content keys,
or a strictly scope-local lifetime.** A raw-id key replays a stale verdict
against a reused id (a completeness bug visible only as corpus drift).

Pruning is the dominant perf lever in this subsystem, and the dominant *risk*:
a too-aggressive prune silently turns a proof into a miss. Every prune change
must clear the byte-identical corpus gate (below). Several memory notes record
prunes that were unsound in subtle ACUI/eigenvariable cases — check them before
touching a prune.

## Verification contract (read before any change)

The corpus is the oracle. **Every change must keep the breadth corpus
byte-identical** unless it is a deliberate, separately-justified completeness
gain.

```bash
# breadth: per-line ablation against the byte-identical oracle
zig build bench-search -Doptimize=ReleaseFast -- --frontier=breadth > new.txt
#   diff found/miss/top1 + suggestions vs tests/search_bench_cases/BASELINE.md

zig build test-frontier-smoke                    # fast guard
zig build test-unit -Doptimize=ReleaseFast

# depth: completeness target (suffix-truncation regeneration). Allowed to improve.
zig build bench-search -Doptimize=ReleaseFast -- --frontier=depth \
  --files=tests/search_bench_cases/additive_fol.mm0:tests/search_bench_cases/additive_fol.auf
```

Notes:

- In the sandbox, add the following flags before `--` in each build command:
  `--cache-dir .cache/zig-local --global-cache-dir .cache/zig-global`.
- For ownership/COW changes, also run safety-enabled tests (Debug or
  ReleaseSafe). The ReleaseFast corpus gate does not replace lifetime checks.
- **Always run ReleaseFast and use a freshly built binary.** Debug is slow;
  stale binaries give garbage. The breadth result is the stable oracle.
- Metrics: breadth reports `found` / `miss` / `top1` (rank of the oracle
  suggestion); depth reports per-theorem frontier `k` / `FULL`.
- Defaults: `max_depth=6`, gen-nodes (`max_nodes`)=256, gen-fuel=4096,
  global-budget=6.3e9 weighted ticks (`--global-budget=0` disables for
  uncapped calibration runs).
- Determinism is required: candidate/fan-out ordering is observable through
  `top1` and the byte-identical suggestions, so preserve enumeration order
  (member-pool, then declaration order) and the `nonSplitCandidateFirst` sort.

## Internal-child enumeration cutoff + witness-class candidate order

Two coupled generation-path rules kill the contraction-cascade cost a
one-sided (Tait/Schütte) calculus otherwise pays at every node. The problem
shape: `rex` KEEPS its principal (`⊢ [x/t]p , ∃x p , d` proves `⊢ ∃x p , d`),
so at every open node the search can re-apply it with a fresh carry-metavar
witness, and the minted instance is itself a new ∃ member — a self-feeding
cascade of VALID one-step rederivations. Exhaustive candidate enumeration then
validates ~one accepted rex per chain node (each a full `tryCandidate`), and
the per-truncation cost multiplies ~3.7× per regen level.

- **Internal-child enumeration cutoff** (`ExactOptions.internal_open_child`,
  set only by the generation driver's own child searches — `solveProof` and
  `hookSolveOpen`): stop enumerating apply candidates once as many results
  exist as the caller keeps (`max_results` = 1 concrete / 4 open). The child
  keeps the first N results in enumeration order instead of the best N by
  declaration order — semantically a different (still valid) sub-proof choice,
  in exchange for not exploring every speculative subtree at every node.
  Top-level searches (line suggestions, inline slots) never set the flag;
  their ranked result lists stay exhaustive and byte-identical.
- **Witness-class order** (`witnessClass`, refining the old annotation-trust
  `defersWitness`): within equal split-ness, class 0 = rules not enrolled in
  `@auto backward` (unchanged front class), class 1 = enrolled rules whose
  every hypothesis binder is conclusion-determined (the invertible-style
  De Morgan/intro ladder), class 2 = enrolled rules with a premise-only
  binder (a deferred witness — `rex`/`lall`). The 1-vs-2 split is what orders
  a one-sided theory, where EVERY rule is enrolled and the annotation alone
  distinguishes nothing. (`generationOrderClass` now layers the declarative
  `@auto eager` band between class 0 and class 1 — see the eager section —
  without changing the class 0/1/2 structure for unannotated rules.)
  Class 0 is deliberately NOT structural: demoting
  un-enrolled hyp-only-binder rules (transitivity/cut shapes) behind the
  ladder swaps euclid/zermelo frontier rows for church/zh ones (measured
  +6 FULL / −3 rows) — a separate trade, not taken.

Effect: tait `ex_swap` FULL 7/7 at DEFAULT budget/nodes (was 4/7; k=6 cost
9.5G ticks and k=7 needed gen-nodes≈4096 before), `resolution` floor 5.51G →
3.75G. Corpus: breadth byte-identical (4149/3764/0), depth 0 losses / 4
frontier-row gains, wall −4%.

The cutoff also surfaced (and forced the fix of) a latent escape in the
`hookSolveOpen` interner scope: dummy INDEXES are a second id-space the
ExprId reintern does not translate, so a child conclusion referencing a
scope-minted dummy read back as a dangling or colliding index in the parent
(`error.UnknownDummyVar`, or silent misbinding). Guarded twice now: a
`scope_dummy_base` escape check in `hookSolveOpen` plus a per-index
existence/sort check in `reinternConcrete`.

## Convergent-proof efficiency: the success transposition memo

`additive_fol` depth has two convergent (DAG-shaped) proofs, `branch_converge`
and `fan_in`, that are genuinely deep (proof depth ≥ 9) and branch heavily:
nested *additive* backward `lim` where the cut formula is not read off the goal
(`branch_converge`: `¬ P c` manufactured by `rnot`; `fan_in`: `Q c ∧ Q d`
assembled by `ran` across two branches). They are **not** a completeness gap —
the engine proves all 77 theorems given enough budget — only an efficiency one.

`generate.zig`'s `Driver` holds the relevant memos for the concrete sub-solve
(`solveProof`):

Both memos are keyed by an **ACUI-canonical form** of the target
(`canonicalKey` → `acui.canonicalizeAcui`): two ACUI-equal subgoals
(same multiset, different association/order) are equi-provable, so they share a
slot. The canonicalizer is conservative — it flattens association, drops units,
and only sorts/dedups members when the registered combiner subset is actually
commutative/idempotent (`comm_name`/`idem_name`) — so it never collides two
genuinely-unequal expressions (worst case: a missed reuse). On a non-ACUI theory
it is the identity, gated by `has_acui` so those theories pay nothing.

- `concrete_fail` — per-pass **failure** memo keyed `(canonical target, depth)`.
  A failure is depth-relative (unprovable in d levels may be provable in d+1), so
  depth is part of the key. Only written for *exhaustive* failures (gated on
  `node_cap_trips`/`path_prunes` unchanged across the subtree), and cleared each
  iterative-deepening pass. An exhausted failure for one ACUI variant skips them
  all. It reuses `concrete_ok`'s already-computed canonical key, so it costs
  nothing beyond the success memo. Legacy path: only written when
  `persist_negative` is off.
- `persist_concrete_fail` / `persist_open_fail` — **cross-cell persisted**
  failure memos (`GenerateOptions.persist_negative`, default on). Same
  exhaustiveness guards, but each verdict is tagged with the phase it was
  recorded under (values: per-phase max failed depth / per-phase depth
  bitset) and survives the whole retry ladder. Sound because a
  genuinely-exhaustive fail at (target, depth d, phase p) is a pure semantic
  fact — no proof of gen-depth ≤ d exists under phase-p capabilities and
  this pool — and the phase flag sets are monotone and linearly ordered
  (phase 3 equals phase 2; the rest strictly grow): the verdict covers any
  re-encounter at (depth ≤ d, phase ≤ p), which the depth-major core hits
  constantly (phases 1–2 re-run at every new depth after phase 3 already
  failed the same targets at the previous one). Depth-0 solves carry no hook, so ANY recorded fail covers
  depth-0 re-encounters at every phase. Open verdicts persist only when the
  child enumeration was NOT truncated by `open_child_max_results` (a
  truncated fail can flip when `concrete_ok` growth changes which child
  candidates surface — observed on euclid `dvd_add`); truncated open fails
  keep their per-cell lifetime in `open_fail`. Both maps clear at the
  ladder rerun whose inputs genuinely change (the phase-6 seeded pool). `concrete_ok` replay is checked BEFORE the
  persisted fail (an ok entry found under stronger flags is consistent with
  a persisted weaker-phase fail and must win). Shadow-validated before
  landing: zero contradicted verdicts across ~550k would-skip re-solves;
  ~17-21% of generation ticks had been re-deriving already-known failures.
  Skips spend no per-phase fuel, so cells explore more distinct candidates —
  this raised the found-ticks ceiling and re-anchored `global_budget` (see
  the budget section).
- `concrete_ok` — **success transposition table**. A found proof is a complete
  valid tree whose validity is depth-independent, so it is not keyed on depth;
  instead each entry stores the proof's actual generation depth (`genDepth`, the
  longest chain of nested inline applications) and is replayed only when the
  current remaining budget admits it. Persisted across passes (a success is valid
  in every later pass; `nodes` resets per pass, so the deep pass replays shallow
  sub-solves for free). This collapses the re-proof of shared subgoals in
  convergent proofs and of goals reached via commuting invertible-rule orderings.

**Replay relabels to the caller's exact target.** A success hit on an ACUI
variant `T2` returns `T1`'s cached application, but that application *concludes
`T1`'s `ExprId`* (≠ `T2`). The replay is therefore returned with its conclusion
**relabeled to `T2`**: `emitGeneratedSlot`'s strict `proof.conclusion != target`
gate then passes, and when `tryCandidate` recompiles the spliced assembly the
proof compiler inserts the ACUI reorder bridge — the same matching that lets
`exact?` fire against a reordered ref. (An earlier attempt that kept the cached
`T1` conclusion poisoned the slot: the gate rejected it, yet `solveProof` had
returned non-null so the slot was never re-searched. Relabeling is the fix; it is
sound because the recompile validates the bridged proof.)

**Budget policy.** These two proofs need depth ≥ 9, so reaching them requires
`max_depth > 6` — but **the global default must stay at 6**: raising it to 10
roughly 10×'s corpus wall-clock on the 385 doomed generic-corpus searches for
zero found-ness gain. The higher budget is scoped to the depth-frontier
regression guards in `tests/frontier_guards.zig`, which double as the memo's only automated check
— breadth finds these lines through the pool and never exercises deep generation.
Each guard's budget is pinned just above the theorem's measured floor (2026-06-24)
so a budget regression trips it: `branch_converge` is fuel-bound (`max_depth=10,
gen_nodes=128, gen_fuel=3072`; FULL needs f≥2048, n≤64) and `fan_in` is node-bound
(`max_depth=10, gen_nodes=192, gen_fuel=1024`; FULL needs n≥124, f≥512). These
floors are far below the memo's original 384/10000 — the witness-unification and
eigenvariable-ordering work since the memo landed dropped them substantially. The
ACUI keying still helps `fan_in` by sharing its commuted-context subgoals; the
`Q c` / `Q d` branches are genuinely distinct (not ACUI-equal), so the residual
width is real.

## File index

| file | role |
|---|---|
| `root.zig` | public surface / re-exports |
| `session.zig` | `SearchSession`: lazy index + pool caching |
| `types.zig` | `Goal`, `Context`, `ApplyCandidate`, `ExactCandidate`, options, counters |
| `backward/backtrack.zig` | `exact?` driver + the `backtrackRefs` ⇄ generation/open/witness engine (one mutually-recursive component) |
| `backward/match.zig` | per-ref hypothesis matching + `@view`/`@recover` seeding + eliminator meta-aware match (`tryMetaAwareHypMatch`) |
| `backward/lookup.zig` | reference-index lookup for a hypothesis slot |
| `backward/plan.zig` | per-slot fill ordering (cost/strength) + template-binder masks |
| `backward/plausible.zig` | conclusion-contradiction prune + ACUI split-member reasoning |
| `backward/validate.zig` | candidate validation, binding rendering, ranking, derived-direct |
| `generate.zig` | `auto?` driver: hybrid depth-major/phase-major retry ladder, forward saturation wiring |
| `trigger.zig` | `@auto trigger` seed harvest (phase 6): goal-subterm e-match → sourceless ground `DerivedRef`s |
| `tunables.zig` | `auto?` per-call parameters: names, ranges, validation, and applying them to `GenerateOptions` |
| `candidate.zig` | `probe`/`commit` over `tryCandidate`: full checker re-validation on a cloned theorem |
| `apply.zig` | `apply?` thin variant |
| `backward/seed.zig` | seed-phase binder extraction + non-view principal fan-out + eliminator reconciliation seed (`partitionSeedBindings`) |
| `backward/bag.zig` | the search's handle on `acui_bag.zig` (one flattening of an ACUI combiner application: members, unit, laws, rebuild), with the combiner looked up from the search context |
| `backward/acui.zig` | ACUI member math (shared by all three principal mechanisms) |
| `backward/split.zig` | multiplicative context-partition search |
| `backward/witness.zig` | ACUI member-witness enumeration for open existentials |
| `backward/def_match.zig` | transparent-def-aware matching: the rigid mismatch probes, one-layer unfolding (`unfoldAppOnce`), the def-body walk (`walkDefBody`), hyp-side extraction |
| `backward/lockstep.zig` | the determined argument pairs of a template/goal walk, and `walk` over them |
| `backward/redex.zig` | reduce `@rewrite` redexes in generated emit targets, under `@congr` heads only, leaving ACUI context structure as the pool writes it |
| `backward/semantic.zig` | the search's view of `../../head_class.zig` (head classes, determined arguments) plus strict-comparability helpers |
| `abstract_prune.zig` / `context_prune.zig` | broad-slot prefilters |
| `forward.zig` | forward saturation (`@auto forward`) |
| `shape.zig` / `clipper.zig` | shape extraction + discrimination index |
| `ref_index.zig` / `refs.zig` / `rule_index.zig` | candidate/ref indexing |
| `fixture.zig` | theorem-prefix preparation and test setup (walks the `.mm0` through `pipeline/common.zig`'s shared statement helpers, recovering from broken earlier declarations like the analysis) |
| `source.zig` | `suggestionsAtSourceOffset` (LSP entry; reports a `SearchStatus` outcome) + `searchPlaceholders` (placeholder enumeration for the LSP status diagnostics) |
| `miss.zig` | `MissReport` (which limits cut a failed search short, read once from its counters) + `retryFor` (the `auto?` parameters the failure report and its **Retry with …** code action suggest) |
| `rank.zig` | candidate ranking |
| `egraph.zig` | `conversion?` e-graph core: hashcons + congruence closure, AC bag nodes, dep-safety gate, saturation |
| `egraph/alpha.zig` | alpha pairing scheduler (`collectAlphaMatches`): pairs `@conversion alpha` rule instances under a lexical renaming; its settled cache and watermarks live on the `EGraph` |
| `egraph/explain.zig` | explanation extraction (`ExplainCtx`) + the `Term`/`Step` vocabulary, re-exported through `egraph.zig` |
| `egraph/tests.zig` | egraph unit tests (public-API only) |
| `conversion.zig` | `conversion?` driver: `@conversion` enrollment, pool/goal seeding, absorbed AC certificates, forced-negative reporting |
| `conversion/lowerer.zig` | `Lowerer`: explanation chain → proof-script lines (AC re-treeing seams, congruence descent, pool-equation citation) |
| `tests/` | subsystem unit tests, split by topic (`source`, `auto`, `apply`, `prune`, `forward`, `tunables`, `conversion`, `compute`, `alpha`); shared fixtures in `tests/helpers.zig` |
