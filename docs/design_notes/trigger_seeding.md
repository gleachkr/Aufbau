# Trigger seeding — analytic `ax`-instance seeds from goal subterms

Status: **IMPLEMENTED** (2026-07-03) — phase 6 in `generate.zig`, harvest in
`search/trigger.zig`, annotation parsing in `rewrite_registry.zig`; guarded
by the `nd_minimal` depth-frontier tests in `build.zig`. Two findings from
implementation are folded in below and marked **[impl]**: the seed-aware
slot cost (a fourth new piece the design missed), and the disjunct triggers
(the two headline patterns were not sufficient for `or_comm`). Background in
the memory notes `project_trigger_seeding_design` and
`project_elim_major_ax_invention_gap`.

## The problem

Backward search cannot invent an elimination major. Purest repro (15-rule
minimal propositional theory): goal `p→q , p ⊢ q`, empty ref pool → MISS at
tc=11 / 1.7ms — a cheap give-up, not budget (8× nodes/fuel and
`--global-budget=0` don't help). Adding one `ax` ref (`p ⊢ p`) makes it found:
the ref pins `imp_elim`'s premise-only binder `p` via the minor, and the major
`⊢ p→q` then generates concrete and closes by invented `ax`.

Mechanism: conclusion matching can't pin a premise-only binder;
`tryGenerateSlot` needs concrete targets; elim rules deliberately have no
`@auto backward` (per the annotation discipline — backward ⟺ intro/witness);
and phase-5 constrained backward MP can't pin from goal-*context* members
either. The missing move is a sequent **left rule**: eliminations keyed on
the ∨/→/∃ sitting *in* the goal context. This is what caps zermelo
`nd_exists_elim_const` at k=5 and `nd_or_comm` at k≥6 on the depth frontier.

## The idea

A declarative per-rule `@auto trigger` annotation. Each trigger is a pattern
e-matched against the subterms of the original goal; every match grounds the
named rule binders, and the engine mints the resulting **ground instance** of
the rule (for `ax`: `φ ⊢ φ` per harvested formula φ) as a *seed* — an
ordinary ref in the pool and a depth-0 fact in the forward-saturation
frontier. Backward search then closes elimination majors by seeded refs: the
measured gap was literally "no ref to pin the eliminated formula", and seeds
ARE refs.

**Why this is principled, not benchmark-shaped:** it operationalizes the
**subformula property** — cut-free proofs use only subformulas of the
end-sequent, so seeding identity axioms over goal subformulas enumerates
exactly the analytic leaf set. It is forced and finite (bounded by goal
size), sound by construction (every seed instance validates through the
ordinary `tryCandidate`/checker path; a useless seed is just a pool entry
nobody selects). It stays theory-agnostic: the engine only pattern-matches
subterms; the theory author encodes the connective/sequent knowledge in the
patterns. This fits the forced-not-heuristic discipline: subterm harvest is a
finite syntactic enumeration, not a guess.

**Why triggers instead of a backward left rule:** better altitude. A native
left-rule candidate generator would be new backward control flow keyed on
context members. Seeding reuses the existing refs-pin-binders discipline —
derived refs, recipes, explicit bindings, the shape index, and the forward
frontier all exist. NEW code = annotation parsing, subterm harvest +
template e-match, and one seeding hook.

## Verified against the pure-repro misses

Fixtures described in `project_elim_major_ax_invention_gap` (throwaway
`/tmp/claude/ndminimal/nd_min*.{mm0,auf}`; rebuild from that note's recipe):

- `nd_mp_inner` (`p→q, p ⊢ q`, empty pool): seeds `p→q ⊢ p→q` and `p ⊢ p`
  (both context members). With `imp_elim` forward-enrolled they forward-JOIN
  to `p→q, p ⊢ q` — closes with no backward elim at all.
- `or_comm` k=6: needs `p∨q ⊢ p∨q` (context member), `p ⊢ p`, `q ⊢ q`
  (disjuncts of a context member).
- `exists_elim_const` k=5: needs `∃x p ⊢ ∃x p`, `p→q ⊢ p→q` (context
  members), `p ⊢ p` (antecedent of a context member).

All are subformula seeds; all are covered by the two patterns below.

## Annotation surface syntax

Doc-comment annotation on the rule, namespaced under `@auto` next to
`@auto backward`/`@auto forward` (parsed in `rewrite_registry.zig`
`processOneAnnotation`, currently `rewrite_registry.zig:162`). Grammar:

```
@auto trigger PATTERN
PATTERN ::= ( IDENT PATTERN* )  -- term (by name) applied to sub-patterns
          | BINDER-NAME         -- capture position: binds the rule's binder
          | _                   -- wildcard
```

Prefix form with term *names* (identifiers), exactly the `@acui` precedent —
no math-string/notation parsing needed; names resolve against the
environment when the registry is built. Pattern variables are the rule's own
binder names (by `arg_names`); `_` is anonymous. One `@auto trigger` line per
pattern; a rule may carry several.

The annotations on `ax`
(`axiom ax (G: ctx) (p: wff): $ G , p ⊢ p $` in the minimal theory; the
zermelo/euclid analogues are shaped the same):

```
--| @auto trigger (hyp p)
--| @auto trigger (im p _)
--| @auto trigger (or p _)
--| @auto trigger (or _ p)
axiom ax ...
```

- `(hyp p)`: for every `hyp φ` subterm of the goal — i.e. every member of
  the goal context — seed `φ ⊢ φ`. This is the left-rule reading, and it
  gets whole-formula capture for free: contexts wrap formulas in `hyp(·)`,
  so no special "capture the whole match" syntax is needed.
- `(im p _)`: for every implication subterm, seed its antecedent — the
  formula `imp_intro` will move into context.
- **[impl]** `(or p _)` / `(or _ p)`: the disjunct seeds. The design's
  claim that the first two patterns close every verified repro was wrong
  for `or_comm`: `or_elim`'s minors need `p ⊢ p` / `q ⊢ q`, and the
  disjuncts are not context members of the *original* goal (v1 does not
  re-trigger on generated subgoals, where they would be). The general
  authoring rule: one trigger per position an elimination rule moves into
  its minors' contexts.

Explicit patterns, not blanket harvest, is Z3's core lesson: seeding *all*
wff subformulas on big zermelo/euclid goals means 30–80 pool refs and
quadratic fan at 2-slot rules. The author tunes patterns per theory.

**Semantic rules:**
- A binder named in a pattern must be a term binder (`()` var) of the rule;
  its sort must match the matched subterm's position sort (checked at
  registry build for the pattern shape, and again by ordinary validation at
  seed time).
- Rule binders NOT named by the pattern: a context-sorted binder (the
  ACUI-combiner sort, `G` in `ax`) defaults to the combiner's **unit**
  (`acuiUnitIdForHead`), with `normalizeAcuiUnits` applied to the instantiated
  conclusion so `emp`-noise never enters the pool. Any other unnamed binder
  makes the instance non-ground → **registry-build error** (the annotation is
  malformed for that rule).
- Duplicate groundings across patterns/subterms dedupe by (rule, binding
  tuple).

## Mechanism

### 1. Registry (parse + store)

`rewrite_registry.zig`: new case in `processOneAnnotation`. Store per rule as
`trigger_patterns: std.AutoHashMap(u32, []TriggerPattern)` where a
`TriggerPattern` is a small prefix tree over `{term_id, binder_index,
wildcard}` — or reuse `TemplateExpr` (`rules.zig`) directly with binder
indices into the rule's binders, which lets the harvest reuse the existing
template-match machinery. Resolution of term names happens where `@acui`
resolves its names; unknown name → diagnostic, annotation dropped.

### 2. Harvest (once per `auto?` call, original goal only)

Walk the goal expression's subterms once (the generic expr-walk helper from
task #53 / `collectAcuiMembers`-style descent in `exact_acui.zig`). For each
subterm × each registered trigger pattern, structural template match
(`matchTemplate`-family; a plain structural walk suffices — ACUI-modulo
matching is *not* needed here, the subterms are already the goal's own
syntax). Collect distinct groundings. Skip any match that embeds a search
placeholder. Cost: O(goal size × patterns) — trivially bounded.

V1 triggers on the ORIGINAL goal only. No re-triggering on generated
subgoals — that is the full e-matching loop, to be costed separately later.
V1 cannot matching-loop: instances are ground, built only from existing
subterms, minted once per call.

### 3. Seed minting

Each grounding becomes a synthetic `DerivedRef` (`types.zig:855`):
`rule_id` = the annotated rule, `sources = &.{}` (no premises — this is the
one new shape: today's derived refs always have sources), `shape` = the
rule's conclusion instantiated with the grounding (context binders → ACUI
unit, then `normalizeAcuiUnits`), `bindings` = the grounding,
`pinned_metas = &.{}`, `has_universal_meta = false`, `source_depth = 0`.

Injection chokepoint is `generateTopLevel` (`generate.zig:279–321`), where
the ref pool, ref index, and forward saturation are built: hand the seed
list to `forward.saturate` as extra depth-0 sources (next to the pool-seed
loop at `forward.zig:109–122`) so forward joins fire over them, and append
the seed `DerivedRef`s to the derived pool before indexing so backward
search sees them as ordinary derived refs.

### 4. Gating — a clean-miss retry phase

Phase **6**, following the established ladder in `generateTopLevel`
(`generate.zig:401–480`): runs only when phase 5 ends in a *clean miss*
(`applications.len == 0 and !budget_exhausted`). On entry: harvest + mint
seeds; if the seed set is empty, skip. Otherwise rebuild the derived
pool/index and re-run saturation with seeds included, then re-run the
backward ladder over the augmented pool with fresh fuel.

Recommended v1: phase 6 re-runs the full phase-1→5 ladder over the augmented
pool (the pure repro closes with default phases once the ax ref exists, so
this is known-sufficient; semantically it is "retry with the analytic leaf
set available"). Alternative to measure: a single most-permissive pass.
Either way the phase is capped by its own fuel like phase 5
(`options.phase5_fuel` precedent).

**Breadth is byte-identical BY CONSTRUCTION**: phases 1–5 are untouched and
phase 6 only runs where today's answer is a clean miss — depth/frontier can
only add. This is the established landing pattern. (Verified at landing:
breadth 4149/4149, top1 3764, miss 0; depth TOTAL full 325, both unchanged.)

### 4a. **[impl]** The seed-aware slot cost (the piece the design missed)

Seeds in the pool are necessary but not sufficient: with an empty ref pool
every hypothesis slot of an elim candidate is generate-only (cost 4 in
`exact_plan.hypSlotCost`), the tiebreak falls to constraint *strength*, and
`or_elim`'s conclusion-pinned minors out-rank the determining major — the
slot the seed would fill is never reached, and the minors (whose disjunct
binders are unpinned) dead-end first. This is the same wildcard-vs-rigid
inversion diagnosed for phase 5 in `project_phase5_occurrence_ordering`,
surfacing through slot cost instead of open-slot ordering. Fix: a seed is a
ref for planning purposes. `DerivedPool.has_seeds` (set only by the phase-6
pool builders) gates `HypPlan.seeded_len`: a pool-empty slot with derived
slot candidates in a *seeded* pool costs like a ref slot of that width
instead of generate-only. Every pre-phase-6 search plans exactly as before
(the flag is never set), preserving byte-identity; ordering-change history
has teeth, so the containment matters.

### 5. Ranking and rendering

- Seeds rank **after** real pool refs and after genuinely-derived facts
  (`reference_rank` ordering, `rank.zig:15`; deterministic tiebreak by
  pattern order then subterm traversal order). Real proof-line refs must
  keep winning wherever they suffice — seeds are a last resort by
  construction (phase 6) *and* by rank within the phase.
- A seed closing a goal materializes through the existing derived-ref path
  (`exact_validate.zig` `buildRuleApplication` / forward
  `materializeApplication` with empty sources): the emitted line is a bare
  `by ax` (binding inferable from the stated sequent), or `by ax (p := …)`
  where inference wouldn't pin it — the explicit-binding renderer already
  exists.

## What this does and does not buy — measured at landing

- **Buys:** the capability misses. `nd_minimal` (the pure repros): both
  theorems FULL from an EMPTY pool at default budgets — `nd_mp_inner` k=2
  found at tc=8/1.6ms (was a clean MISS at any budget), `nd_or_comm_min`
  k=5 at tc=20/6.3ms. Real theory: `zermelo_frontier` with the four
  triggers on `ax` goes `nd_exists_elim_const` 4/6 → **6/6 FULL** — the
  only per-theorem change across all 136 zermelo theorems (full 97→98,
  wall +2.4% on the miss side; every clean miss now pays one harvest +
  re-ladder, bounded by the per-call global budget).
- **Does not buy alone (confirmed):** zermelo `nd_or_comm` stays 2/6. Its
  k=3 miss is a separate phases-1–4 distractor-pool budget death (each
  generation layer ≈ 12× cost in zermelo); seeds shorten chains but don't
  shrink the fan. The complementary cost fix is the phase-5 occurrence
  ordering design (`project_phase5_occurrence_ordering`) — independent,
  land separately.
- **Where NOT to annotate (measured):** triggers pay only where the misses
  are elimination-pin-shaped. The same four patterns on **euclid_frontier**
  (identical ND prelude) changed ZERO of its 63 per-theorem fractions while
  adding ~17% depth wall — its misses are existential/equational — so
  euclid stays clean (note in its `ax`). **peano** / **zermelo_hilbert**
  are Hilbert-style (no context layer; nothing to seed from).
  **martin_lof**'s `var` analog has a bound binder `{x: tm}`, which v1
  validation deliberately rejects (a ground seed cannot capture a
  variable). The corpus survey: zermelo is the one theory where the
  annotation ships.

## Validation campaign (the dominant cost — plan it, don't wing it)

1. Promote the throwaway minimal-theory repros into a bench theory
   (`nd_minimal.{mm0,auf}` alongside `quantifier_alternation`/
   `transitive_closure`), annotated with the two triggers; add build.zig
   depth guards for `nd_mp_inner` / `or_comm` / `exists_elim_const` at their
   previously-missing k.
2. Breadth corpus byte-diff (expect 4149/4149, top1 3764, miss 0 —
   byte-identical by construction; verify anyway).
3. Depth frontier per-theorem fractions, not just TOTAL (the fuel-curve
   lesson): expect zermelo nd_* improvements; watch for phase-6 cost on
   *unrelated* clean-miss theorems (every clean miss now pays a harvest +
   possible re-ladder — measure fail-latency distribution against the
   `project_auto_failure_latency` baselines, worst-miss and >5s counts).
4. additive_fol guards, frontier smoke, scenario suite, global-budget margin
   (found-floor vs cap per `project_pure_representative_memo`).
5. Negative test: a theory with no `@auto trigger` annotations must skip phase 6
   entirely (zero cost on the annotation-free corpus).

## Open questions (settle before/while implementing)

1. ~~**Syntax blessing**~~ — SETTLED 2026-07-03: Graham blessed the prefix
   form, namespaced as `@auto trigger (hyp p)` / `@auto trigger (im p _)`.
2. Phase 6 = full re-ladder vs single permissive pass (measure both if
   cheap).
3. Should triggers on rules other than `ax` be allowed in v1? The mechanism
   is rule-agnostic and nothing above restricts it; suggest: allow, since
   the ground-instance + unnamed-binder rules already force well-formedness.
4. Whether the harvest should also walk pool-ref statements (not just the
   goal). The subformula property says end-sequent; the goal here carries
   its context, so goal-only is the principled v1 answer — revisit only with
   a concrete miss in hand.

## V2 direction — universal-meta positions in `ax` seeds (Graham 2026-07-03)

Ground seeds are analytic by construction, which is also their limit — and
church makes the limit precise. Measured: `(hyp P)` on church's
`ax (G: ctx) (P: wff): G , P ⊩ P` changes ZERO of 96 per-theorem fractions
(+4.6% wall). One concrete reason: the sub-proofs under `lamT` / `betat` /
`inst` need typing-assumption closings `x : A ⊩ x : A` — `ax` instances at
`P := (x : A)` — where `x` is a **bound variable freshly minted by
generation** (a dummy that does not occur anywhere in the original goal).
No ground harvest over goal subterms can ever name it. But the *type* `A`
IS harvestable (from `λ x: A. t` and typing subterms of the goal).

The v2 idea: let a trigger pattern mark a position as **wildcard at
harvest, fresh universal metavariable in the instance**. On church's `ax`
(`ty` is the `t : A` typing term):

```
--| @auto trigger (hyp (ty ? A))
axiom ax (G: ctx) (P: wff): $ G , P ⊩ P $;
```

matches every typing subterm `t : A` of the goal (any `t`), captures `A`,
and mints the seed `?x : A ⊩ ?x : A` — the shape
`nd(hyp(ty ?m A), ty ?m A)` with ONE store meta at both occurrences (the
hash-consed shared leaf, so the family-fact contract `required ⊆ shape`
holds for free). At use time the slot shows the concrete fresh dummy and
`solveCorrespondence` solves `?m` to it — the ordinary derived-ref
discipline, per-use instantiation, rollback after.

Why this is cheap where the naive family seed is not: the shape stays rigid
everywhere except the variable leaf (`A` ground, both judgment heads
fixed), so it is *narrower* than existing forward family facts like
`g ⊢ ?a` (bot_elim), nothing like the absorber `?P ⊩ ?P` would be. The
same mechanism also covers martin_lof's
`var (g: ctx) {x: tm} (A: ty): g, x:A ⊢ x:A` — there the bound binder is a
*rule* binder, so the annotation reads `@auto trigger (ty_asm x A)`-style
with the unnamed bound `x` deferred instead of v1's hard error.

Design points (unsettled):
- Syntax: `?` as the defer-marker (v1 rejects it today, so it is free), vs
  deferring unnamed *bound* rule binders implicitly (backward-compatible —
  v1 errors on them, no annotation exists to change meaning).
- Meta kind: these are variable-position metas. `deferConclusionBinders`
  deliberately never defers bound binders ("a hidden binder needs a
  variable witness, not an arbitrary term"); the seed path relaxes that
  with a use-time solve that should prefer/require a variable (or
  unfold-dummy placeholder) leaf — validation arbitrates regardless, so a
  term-valued solve can only fail, never leak. The store's bound-choice
  meta machinery (`meta_bound_vars_choice`) is the likely carrier.
- Rendering: a seed whose solved `?m` is a generated dummy must render
  through the existing `Namer` placeholder path (theorem vars, then `@vars`
  pool) — the same discipline as unfold dummies in recipes.
- Ranking/cost: still phase-6-gated; meta-bearing seeds should rank after
  ground seeds, and plausibly be excluded from the `seeded_len` slot-cost
  nudge (a meta leaf widens the slot-match set).
- The more aggressive cousin — deferring a whole *formula* binder
  (`?P ⊩ ?P`, a true absorber that composes with the sibling-pin
  discipline like phase-5 cut determination) — is noted as a separate,
  costlier variant; Graham's target is the bound-variable version above.
