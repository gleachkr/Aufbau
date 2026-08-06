# `@auto eager` — user-scheduled invertible-rule application

Status: IMPLEMENTED 2026-07-05 (see "Implementation outcome" at the end).

## Problem

The Tait fixture showed that a one-sided sequent calculus has a natural
search discipline the engine cannot currently express: apply the invertible
decomposition rules (`rim`, `ror`, `rdm_*`, `rand`, …) unconditionally and
immediately, and spend real search effort only on the genuine choice points
(`rex` witnesses, closing `ax` instances). Today every backward application
costs one depth level, so a theorem whose proof is a tall-but-deterministic
De Morgan ladder plus one witness step misses at the default `max_depth=6`
purely on proof *height* (e.g. `cases_classical`, `s_comb`, `exists_mono`
need md≤12), even though its search-relevant *choice depth* is 1–2.

## Prior art already in-tree

`witnessClass` (`search/exact.zig`, commit e69e443) already computes an
*implicit, structural* invertibility class and uses it for candidate
ordering inside `nonSplitCandidateFirst`:

- class 0 — not enrolled in `@auto backward` (closing/structural rules:
  `ax`, the eigenvariable rules `rall`/`lex`);
- class 1 — enrolled, every hypothesis binder conclusion-determined (the
  invertible-shaped De Morgan/intro ladder);
- class 2 — enrolled with a premise-only witness binder (`rex`/`lall`).

So the engine already *orders* invertible-shaped rules ahead of
witness-deferring ones. What it does not do: let the user declare the
discipline, distinguish priorities within the invertible ladder, or exempt
those applications from the depth limit. `@auto eager` is the declarative,
stronger version of witnessClass — and class 1's shape test is exactly the
annotation-time validation predicate we need.

## Proposal

### Syntax

```
@auto eager           -- priority 1 (highest)
@auto eager 2         -- lower priority
```

`eager` rather than `invertible`: the engine cannot verify semantic
invertibility, so the keyword names the *scheduling behavior the user
requests*, not a semantic claim the engine would be pretending to check.
Parsed in `rewrite_registry.zig` `processAuto` (currently accepts exactly
one bare mode token; extend to allow an optional integer after `eager`).
Stored as `auto_eager_rules: AutoHashMap(u32, u8)` (rule_id → priority).

Semantics of the annotation itself:

- Implies `@auto backward` enrollment (also inserted into
  `auto_backward_rules`) — an eager rule is a backward rule.
- **Validation (annotation error otherwise): the rule must be
  witness-class-1-shaped** — every hypothesis binder appears in the
  conclusion (`templateBinderMask` logic). This statically blocks the
  catastrophic case: `rex` marked eager would be a depth-free self-feeding
  contraction. The mask computation is small; run it at annotation
  processing (env + rule templates are in scope) or lazily at search setup
  with a diagnostic.
- Eigenvariable rules (`rall`/`lex`) are *excluded* by this validation
  (their fresh premise binder is premise-only) even though they are
  genuinely invertible. First cut: leave them class 0 (already tried
  first). Revisit only if a fixture demonstrably needs eigenvariable steps
  depth-exempt; that would require teaching the validation to recognize the
  fresh-binder case specifically.

### Scheduling (modification 2: priorities)

Extend the `nonSplitCandidateFirst` ordering key from
(split-ness, witness-class) to:

```
(split-ness, order-class)
  order-class:  class 0  <  eager pri 1 < eager pri 2 < …  <  class 1  <  class 2
```

Eager rules slot **between class 0 and class 1**, ordered among themselves
by priority. Class 0 stays first deliberately: `ax` closes goals at
near-zero cost, and the classic tableau discipline is *close first, then
alpha (non-branching), then beta (branching), then witness*. A user encodes
that as: `rim`/`ror`/`rdm_*` `@auto eager` (pri 1), `rand`/`rbi`
`@auto eager 2`, `rex` plain `@auto backward`. Rules without annotations
keep byte-identical ordering — the eager band is empty for them.

This is ordering-within-enumeration, not a literal apply-to-fixpoint
pre-pass at each node. A dedicated phase-0-style saturation pre-pass would
be closer to the DFS ideal but is a much larger structural change and has
to reproduce the ACUI goal-bag matching machinery; the ordering route
reuses `tryCandidate` wholesale and captures most of the value. Start
there.

### Depth exemption (modification 3)

Backward applications of eager rules do not consume `max_depth`. Depth is
already a cleanly threaded parameter: `solveProof` / `hookSolveOpen` set
`driver.current_depth = depth - 1` for children (`generate.zig` ~1362/~897).
The change: when the candidate whose hypothesis slot is being generated is
an eager rule, the child solve receives `depth`, not `depth - 1`. Plumbing:
the applying rule's eagerness must reach the decrement site — pass it
through the hook call (`emitGeneratedSlot` → `hook.solve`,
`tryOpenGenerateSlot` → `hook.solveOpenFn`) or as driver state set around
the child solve.

Rationale for not counting them: eager steps are "don't-care"
determinism — they don't multiply the search space the way "don't-know"
choices do, so charging them the same currency conflates proof height with
search difficulty. With the Tait ladder exempt, counted depth ≈ number of
`rex`/choice steps ≈ 0–2, so the whole fixture should go FULL at default
settings (plausibly md=2), and the per-theorem md=7/md=12 floor guards can
collapse to defaults.

**Termination stays externally bounded.** Eager steps are exempt from
*depth only* — they still consume nodes (`max_nodes` 256/cell), fuel
(4096/phase), and GlobalBudget ticks, and the `visited` DFS path guard
catches same-goal cycles. A mis-annotated looping rule burns budget, never
diverges. This is the same posture as forward saturation: structural
termination (invertible rules strictly decrease formula weight) is the
user's claim; the engine only guarantees boundedness. Note the parse-time
validation checks only that every hypothesis binder is
conclusion-determined (`ruleDefersWitness` /
`rules.hasPremiseOnlyBinder`) — it does *not* verify weight decrease,
so a conclusion-determined but non-decreasing eager rule (e.g. premise
`P (s x)` from conclusion `P x`) passes validation and descends
depth-free until the node/tick budget stops it. That is the budget-bound
miss the boundedness guarantee covers, not a hang.

**Memo audit** (the interactions that must be handled):

- `concrete_fail` keyed `(target, depth)` and `open_fail`'s depth bitset:
  both use the actual recursion-depth parameter — still correct as-is.
- `concrete_ok` replay gate compares the *request* depth against the cached
  proof's `gen_depth` (longest nested-application chain, computed post-hoc
  in `genDepth`, `generate.zig` ~1426). **`genDepth` must skip eager rule
  applications** when measuring the chain, or cached ladder-heavy proofs
  report inflated depth and refuse to replay at the shallow budgets the
  exemption makes sufficient — silently defeating the feature.
- `VerdictMemo`/`DeepVerdictCache` are depth-free — unaffected.

### Cut (commit) semantics — required, not optional

An earlier draft proposed shipping ordering + exemption *without* cut, on
the grounds that a wrong annotation would then cost performance, never
proofs. That underestimated the interaction with iterative deepening:
without cut, at every node where an eager rule matched, backtracking still
falls through to the non-eager alternatives (e.g. trying `rex` on
`⊢ (a→b), Δ` before the implication is decomposed). Those reach genuinely
*different* goal bags, so the ACUI-canonical memos do not collapse them —
and with depth exemption, each such alternative branch grows its own
arbitrarily tall eager-exempt subtree, at **every** ID layer. Today ID
keeps those wasted branches cheap by truncating them at the current
depth_limit; exemption-without-cut converts the failing low-depth cells
from cheap shallow scans into full node-budget burns on space cut would
prune. Budget-capped, but a bad trade. (What memos *do* absorb:
permutations of the ladder itself — different eager orderings reach the
same canonical goal bag with the same remaining depth, since eager steps
don't decrement, so `concrete_fail`/`concrete_ok` hit.)

So eager carries cut semantics from the start — that is what makes the
depth exemption coherent:

- **Set-commit, not first-match-commit.** If any eager candidate at a node
  *matched* — actually applied and produced subgoals, i.e. reached the
  child-solve stage — then once the eager band is exhausted without a
  proof, skip the class-1/class-2 bands entirely. All eager matches and
  orderings are still tried (an eager rule may match several bag members:
  `⊢ (a→b), (c→d), Δ` gives two `rim` candidates; memos make exploring
  them cheap). Class 0 (`ax`) sorts *before* the eager band, so closing
  is never sacrificed to the cut.
- **The cut trigger must be application-reached-children, not
  enumeration.** A candidate rejected at the matching/assembly stage (the
  rule simply doesn't fit this goal) must not arm the cut, or a stray
  eager annotation on a rule that never fits would suppress the whole
  search at every node.
- **Completeness safety valve via the phase ladder** — the engine's
  existing idiom for accumulating permissiveness: a clean miss through the
  cut-honoring phases triggers a no-cut retry (phase-6-style, or a
  per-pass flag dropped in a late tail phase). A mis-annotation then costs
  miss-side latency (bounded by the global budget), not lost proofs. The
  annotated fixture's breadth gate (hand proofs must stay re-discoverable)
  is the regression teeth that catches a genuinely wrong annotation.
  *Precisely:* the no-cut retry fires only on a **clean** miss — the
  ladder found nothing *and* no phase retired its fuel
  (`generate.zig` gates the retry on `!budget_exhausted`, the same gate
  the trigger-seeding valve uses, which is what keeps non-annotated
  breadth byte-identical). If the cut-honoring ladder *exhausts* fuel or
  the global budget on a mis-annotated rule, the retry is skipped and the
  proof can be lost. This is deliberate — a budget-exhausted miss means
  the no-cut retry (strictly more candidates) would only exhaust sooner —
  so the guarantee is "a mis-annotation never loses proofs *on a clean
  miss*," not unconditionally.

## Regression posture

- Annotations are per-theory opt-in. Every existing corpus has zero eager
  annotations → candidate ordering and depth accounting are untouched →
  **breadth and depth byte-identity holds trivially for all non-annotated
  corpora**; that stays the gate.
- The tait fixture gains annotations and its baselines *move on purpose*:
  expected outcome is 52/52 depth-FULL at defaults; re-baseline its
  build.zig guards (whole-fixture net can drop from md=12 toward default;
  per-theorem floors likely collapse).
- Watch item: with exemption, depth-major cell `depth_limit=1` does the
  ladder work that previously spread across levels — more work per cell
  for annotated theories, capped by the 256-node cell budget. Tait proofs
  are 5–20 lines; not a concern at this scale, but check node-budget trips
  (`--counters`) when re-baselining.

## Implementation sketch (surgical, in order)

1. `rewrite_registry.zig`: parse `eager [N]` in `processAuto`; store
   priority map; imply backward enrollment; class-1-shape validation.
2. `search/exact.zig`: extend `nonSplitCandidateFirst` with the eager band
   (between class 0 and class 1, priority-ordered).
3. Depth plumbing: thread the applying rule's eagerness to the child-solve
   depth assignment in `generate.zig` (`solveProof`, `hookSolveOpen`).
4. `genDepth`: skip eager applications in the chain-length walk.
5. Bench: annotate `tait.mm0`, verify 52/52 FULL at defaults + all other
   corpora byte-identical (breadth and depth), re-baseline tait guards.

Steps 1–2 alone (ordering only) are independently landable and already
byte-identical-safe; step 3–4 is where the md=6 wins come from.

## Knob decomposition — the wider annotation surface

`@auto eager` bundles three orthogonal things: ordering (where in the
try-order a rule sits), commit (stop trying alternatives once it applied),
and depth accounting (applications don't consume `max_depth`). The bundle
is right for eager itself — exemption-without-cut burns budget (above),
and cut-without-exemption still pays a depth level per rung so tall
deterministic ladders keep missing; neither half is useful alone. But two
*other* knobs deserve standalone exposure, giving a five-annotation
surface (rules may carry multiple `@auto` lines, so these compose):

| Knob | Meaning | Cost |
|---|---|---|
| `@auto backward` / `forward` / `trigger` | participation (exists) | — |
| `@auto eager [N]` | don't-care: front band + cut + depth-free | this note |
| `@auto priority N` | within-band ordering hint, any rule | comparator key + one map |
| `@auto limit N` | ≤N applications per search path | per-rule path counters |
| `@auto exclude` | never a backward candidate | keyword + set + one check |

- **`@auto priority N`** — a tie-breaker *within* the existing bands
  (split-ness and witness-class band structure stays primary: it is
  load-bearing — the `ex_swap`/`resolution` fixes — and a user annotation
  must not be able to invert class-1-before-class-2 by accident). Both
  promote and demote; demotion is independently valuable (the transport
  screen exists because one promiscuous rule, `mpbi`, cost exactly G
  frontier levels of candidate-order pollution). Standalone rather than an
  argument on `backward` because ordering and capability are entangled
  through enrollment today: demoting a promiscuous *non-enrolled* rule
  must not require enrolling it (which would also grant open-witness
  generation).
- **`@auto limit N`** — at most N applications of the rule along any one
  search path: the classic contraction-bounding discipline, and exactly
  what `rex` wants (Tait proofs use it once, occasionally twice; today the
  cascade is tamed only indirectly via witness-class order and budgets).
  Deterministic and explainable — a structural commitment, not a weight.
  Implementation: per-rule path counters saved/restored around candidate
  tries (the trail machinery is the existing idiom). Distinct from the
  REFUTED engine-wide per-(rule,goal) cap experiment: that was a global
  quantitative heuristic; this is per-rule opt-in with user-declared
  semantics.

- **`@auto exclude`** — never a backward candidate: the declarative
  generalization of the transport screen (`isRelationTransport`, which
  hardcodes exactly this skip for relation-bundle transport rules). The
  rule stays available for explicit `by` use, pool refs, and forward
  saturation unless separately annotated. A dedicated keyword, NOT
  `priority 0`: with the lower-is-earlier convention (`eager 1` before
  `eager 2`), priority 0 would naturally read as *highest* priority; and
  exclusion is a capability change, which must not hide inside a knob
  deliberately constrained to within-band tie-breaking. Participation
  knobs are keywords; ordering knobs are numbers.

Deliberately NOT exposed: phase indices (engine-internal and semi-stable —
annotations coupling to them would rot), per-rule fuel/node weights (fuzzy
scores, not disciplines), anything adaptive (known tarpit).

Re-baselining metric: `--counters` ticks (found-floor / cap-margin), not
wall-clock — deterministic across runs.

## Open questions

- Eigenvariable rules under eager (excluded for now; needs fresh-binder-
  aware validation if ever wanted).
- Priority range: two levels (alpha/beta) cover the sequent-calculus use
  case; is a full u8 range worth documenting, or cap at a small band?
- Cut semantics (`@auto eager!`) — deferred until reject-flood evidence.
- Should the eager band also apply on the *breadth* (validation/ablation)
  path's candidate ordering, or only the generation path where
  `nonSplitCandidateFirst` runs today? (Generation-path-only preserves
  breadth byte-identity even for annotated theories.)

## Implementation outcome (2026-07-05)

Landed as designed — ordering band + set-commit cut + depth exemption +
no-cut clean-miss retry — plus one addition discovered during validation.

- Registry: `@auto eager [N]` parsed in `processAuto` (implies backward
  enrollment; class-1-shape validated, `error.EagerRuleDefersWitness`).
- Ordering: `generationOrderClass` layers the eager band between witness
  classes 0 and 1.
- Cut: armed in `exactWithSession` by `ApplyCandidate.reached_child_solve`
  (set at `emitGeneratedSlot`'s hook call) or a validated result; a clean
  miss retries the whole ladder with `GenerationHook.honor_eager_cut` off.
- Depth exemption: `hookSolve` re-adds the level for eager steps; `genDepth`
  charges eager edges 0 so `concrete_ok` replays stay consistent.
- **Eager UnifyMismatch retry** (the addition): the eager ladder freely
  reorders ACUI members, and the ACUI-blind strict replay then fails to
  recover binders from reassociated inline premises. The explicit-bindings
  retry arm in `exact_validate.zig` now also covers eager-rule candidates
  (population bounded by the annotation, so the vetoed blanket-retry cost
  does not apply). Halved tait `resolution`'s churn (6.3G → 3.4G ticks).

Measured on the annotated tait fixture (ror/rim/rdm_* eager 1, rand/rbi
eager 2, rex plain backward): **52/52 depth-FULL at the default md=6**
(most theorems FULL at md=1); the old per-theorem floors (md=7 chains,
forall_mono/ex_swap md=12, drinker's flood window) all collapsed. Breadth
385/385 found at pure defaults with the cut live. Corpus (no annotations):
breadth AND depth byte-identical, tick-exact.

Residual CLOSED (2026-07-05, follow-up task): `resolution` k>=6 churned
~3.4G ticks (default cap 3.35G) because its eager-ladder inline assemblies
rejected at validation on the nested-inline ACUI binder-extraction gap.
The traced failure chain: the checker's top-down hint decomposition
(`inferExpectedRefsForInlineApplications`) is strict/ACUI-blind, so one
extra ladder level reassociates the context bag, the hint dies mid-chain
(at `rdm_not` in the traced case), the hintless `ax` leaf raises
`MissingBinderAssignment`, phase 1 closes appless, and the find fell to a
~3.9G phase-4 retention cell. A checker-side ACUI-aware fallback was
prototyped and REJECTED: bags with two same-shaped members (`resolution`'s
double `¬(_∨_)`) are genuinely ambiguous from the hint alone — no forced
unique decomposition exists. The landed fix is the search-side binding
handoff instead: an accepted `@auto eager` candidate inside an internal
generation child solve (`ApplyCandidate.internal_child`, set from
`ExactOptions.internal_open_child`) gets ALL its resolved binders rendered
as explicit bindings on the spliced application
(`renderAllResolvedBindings` at the accept point in `exact_validate.zig`),
so the parent's re-check never re-infers a nested eager node's binders
from a reassociated hint. Result: resolution worst-k 4.09G → 58M ticks
(70x), every k found in the phase-1 cell at 12 nodes; whole-fixture worst
theorem 313M (exists_mono); the tait depth nets run at the pure DEFAULT
budget. Non-internal suggestions and non-eager theories are untouched by
construction (the render is gated on both), and the full corpus (breadth
4149 lines, depth 637 theorems) verified tick-exact.
