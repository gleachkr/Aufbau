# Reconciling eliminator bound binders via metavariables (martin_lof induction depth)

Status: **Productionized (A + C + B landed; D deferred).** The generalized
version is implemented and corpus-validated: breadth byte-identical (4149 found /
miss 0 / top1 3764), depth **TOTAL 324 → 325** (zermelo +1), target martin_lof
`add_comm` k=1 **MISS 41.6s → FOUND 11.4s**, global worst-case latency 41.6s →
31.9s (now the pre-existing church `DISJ_CASES`), and `test-frontier-smoke` /
`test-search-scenarios` / `test-unit` all green. See **"As-built"** below for the
two scoping fixes the original plan missed. Background + full lever history in the
memory file `project_def_unfold_dummies_as_metavars`.

## The two ingredients

Stripped to essentials, the fix is two ideas:

1. **Propagate vars exposed by def-unfolding as metavariables**, so they resolve
   against the variables that actually occur in the references, instead of being
   scrubbed to null (loses sharing) or kept as inert def-dummies (can't match).
2. **Normalize inferred goals where appropriate** (reduce substitution redexes)
   so a generated slot matches the upstream refs and rules.

Everything below is the grounding for those two ideas and how to land them
cleanly. The prototype implemented them as six entangled pieces; the
**Productionization plan** section re-factors them into four (A–D) along a single
spine.

## The scenario

`tests/search_bench_cases/martin_lof_frontier.{mm0,auf}`, theorem `add_comm`,
depth bench **k=1**: the bench removes the second-to-last proof line `l20` (the
induction *step*) and replaces the final line with `auto?`, so the search must
regenerate

```
l21: g ⊢ add_comm_p m n : Id Nat (m+n)(n+m)
     by nat_ind_elim [l5(motive), l10(base), l20(step), #1(n)]
```

with `l20 = id_trans_ty [l14, l19]` (both refs still present) generated **inline**
as `nat_ind_elim`'s third argument. Baseline: a 37–41s MISS (the global
worst-case `auto?` latency in the whole bench).

The eliminator (`martin_lof_frontier.mm0:508`):

```
axiom nat_ind_elim (g: ctx) {k ih: tm} (C: ty k) (z: tm) (s: tm k ih) (n: tm):
    g , k : Nat ⊢ Ty C                       -- hyp0 motive
  > g ⊢ z : [k/zero] C                        -- hyp1 base
  > g , k : Nat , ih : C ⊢ s : [k/suc k] C    -- hyp2 step
  > g ⊢ n : Nat                               -- hyp3
  > g ⊢ nat_ind k ih C z s n : [k/n] C;       -- conclusion
```

`nat_ind_elim` is **not** `@auto`-backward; it is reached as a backward candidate
via **constrained backward MP** (generate.zig phase 5, `allow_constrained_mp`),
because its conclusion subject `nat_ind …` matches the goal subject `add_comm_p m
n` after def-unfolding.

## Why baseline misses (root cause)

Seeding `nat_ind_elim` against the concrete goal matches the conclusion's
**subject** (`nat_ind k ih C z s n`) against the unfolded `add_comm_p`, whose def
body is `nat_ind k ih (Id Nat (k+n)(n+k)) <base> <step> m` with curly dummies
`{.k .ih}`. The unfold mints fresh dummies for `.k`/`.ih`, so the seed pins
`k(arg1)`, `ih(arg2)`, `C(arg3)`, `s(arg5)` to def-dummy-laden values. (The
conclusion *type* `[k/n]C` = `sb_ty k n C` is an un-invertible rewrite redex, so
the type side pins nothing — everything comes from the subject.)

The baseline scrub then drops every placeholder-laden binding to null. With the
motive `C` null, hyp0 `Ty C` matches every `Ty`-judgment ref → a flood of doomed
motives. Even with the motive recovered, two further obstacles block the step
(hyp2):

1. **Bound-binder identity.** The step's context/type use the def-unfold dummies
   `.k`/`.ih`; the refs `l14`/`l19` use the proof's own `k`/`ih`. They must be
   reconciled (they are *the same* induction variables, different atoms).
2. **Unreduced substitution redex.** The step type `[k/suc k]C` = `sb_ty(...)` is
   not reduced to `Id Nat (...)`, so `id_trans_ty` (which concludes `Id`) is
   neither applicable to nor identity-equal to the generation target.

Key asymmetry between the two bound binders — **this is the heart of the design**:
- `k` appears in the **motive hyp0** (`Ty C`), which is *ref-matched* against
  `l5`, so its reconciling ref exists *early*.
- `ih` appears **only in the step hyp2** (`ih:C` context) — the slot being
  generated — so it has no earlier ref-match; its reconciling ref appears *late*,
  via the open-target *readback* against the generated child's conclusion.

## The unifying mechanism

The two binder reconciliations look different in the prototype but are **the same
operation**. `solveCorrespondence` (forward.zig:1216) treats an interner
placeholder as a unifiable meta **iff it is registered in the meta store**
(`store.info(pid) != null`); an unregistered def-dummy is inert (`.ok`, "no
opinion"). Both reconciliation sites call `solveCorrespondence`. So:

> Reconciling either bound binder is one `solveCorrespondence` of a **ref**
> against a **pattern**, into **one shared meta store**. The binders differ only
> in *when* the reconciling ref appears: `k`'s ref (`l5`, hyp0) exists at match
> time; `ih`'s ref (the generated `l20`, hyp2) appears only at open-target
> readback.

That asymmetry is also the decision rule for *how each unfold-exposed binder is
seeded*:

> Seed a unfold-exposed binder as a **shared meta** (registered in the candidate
> store) when its reconciling ref already exists — i.e. it occurs in a hypothesis
> that gets ref-matched (the motive class). Leave it **null/open** when its only
> occurrence is a to-be-generated slot, so it routes to the open path and
> reconciles by readback.

The pitfall the prototype hit — `instantiateTemplateConcrete` treats a meta-bound
binder as concrete and dead-ends the target — is just the other face of this same
rule: a binder whose ref is a *generated* slot must stay null, never meta-bound.

Sharing is load-bearing: the `k` in `arg1`, the `k` inside `C`, and the `k`
inside the step term `s` must map to **one** meta. Use a single
def-dummy-id → meta map applied across all bindings; per-occurrence minting
breaks the sharing and re-floods.

([[reference_mm0_variable_model]]: this is plain variable identity, not alpha —
no canonical-dummy / de-Bruijn overhaul is needed.)

## Benchmarks (prototype vs baseline `37e9de3`, full depth bench)

**Breadth:** byte-identical — found 4149/4149, miss 0, top1 3764.

**Target case:** martin_lof `add_comm` k=1 **MISS (37–41s) → FOUND (9.3s)**;
worst-case for this theorem moved to k=2 (24.2s MISS, was k=1's 41.6s).

**Frontier (mean depth reached) — up across the board, nothing regressed:**

| theory | base | proto | Δ | FULL |
|---|---|---|---|---|
| euclid | 1.12 | 1.17 | +0.05 | 21→21 |
| zermelo | 1.18 | 1.21 | +0.03 | 96→**97** |
| church | 2.02 | 2.05 | +0.03 | 39→39 |
| peano | 1.68 | 1.76 | +0.08 | 38→38 |
| martin_lof | 1.71 | 1.90 | +0.19 | 10→10 |
| zermelo_hilbert | 1.49 | 1.49 | 0.00 | 120→120 |
| **TOTAL** | **1.50** | **1.54** | **+0.04** | **324→325** |

(zermelo +1 FULL comes from the structural open-binder fix (**A**) alone — some
other rule whose hypothesis has a bound binder inside an ACUI context that the old
guard hard-blocked. This is why **A** is independently valuable and lands first.)

**Wall clock — net −4.2%, one regression:**

| theory | base | proto | Δ |
|---|---|---|---|
| euclid | 60.8s | 72.4s | **+19.0%** ⚠ |
| zermelo | 267.8s | 245.4s | −8.4% |
| church | 234.1s | 229.8s | −1.8% |
| peano | 45.3s | 43.4s | −4.1% |
| martin_lof | 105.8s | 76.6s | −27.6% |
| zermelo_hilbert | 481.0s | 477.1s | −0.8% |
| **TOTAL** | **1194.7s** | **1144.7s** | **−4.2%** |

**Global worst-case latency: 41.6s → 31.2s** (−25%). The old worst (martin_lof
`add_comm` k=1) is gone; the new global worst is the *pre-existing* church
`DISJ_CASES` k=2 (31.2s, ~unchanged from baseline 31.3s).

**The euclid +19% regression is entirely the normalization step (C).** It runs on
*every* generation target, constructing a `Canonicalizer` and walking even when
the target has no substitution redex; euclid's generation is rewrite-heavy, so it
pays the pass repeatedly. fail-mean 1.20s→1.45s (+20%); slowest search shifted
`euclid` k=1 (4.5s) → `dvd_fact` k=4 (5.5s). The has-redex pre-walk (see **C**)
is the fix. The open-binder fix (**A**) only fires on bound-binders-in-ACUI
contexts and is *not* the euclid cost.

## Productionization plan (A–D)

The prototype's six pieces re-factor into four along the single spine "seed →
shared store; reconcile by `solveCorrespondence`; reduce for emission." Land in
the order **A → C → B → D**: A and C are independently corpus-positive and bank
early wins before the riskier seed/store work; each step is A/B-gated and
**depth-checked** (breadth-clean is *not* sufficient for generation changes).

### A. Open openable bound binders through ACUI combiners *(structural; land first, own gate)*

Prototype piece #6, and the only piece that is **not about metas** — it fixes the
open *target construction*, independent of the rest. `instantiateTemplateOpen`
(`open_terms.zig` `instantiateTemplateOpenInner`, the `.app` structural-combiner
branch) currently, when a structural combiner holds an unresolved binder, either
collapses the whole combiner subtree to one context meta or hard-blocks (returns
null). The step's context `join(join(g, k:Nat), ih:C)` has `ih` (bound,
unresolved) inside the `join`, so it returned null → the open target never built
→ the step never generated.

Split the single `templateHasBlockedUnresolvedBinder` guard into:
- `templateHasExcludedUnresolvedBinder` — hard-block **only** on recover-owned
  (`excluded`) / out-of-range binders.
- `templateHasOpenableUnresolvedBinder` — bound-class **or** (subterm) conclusion
  binders.

Branch: excluded → null; else if an openable binder is present → **recurse** (open
it in place via the `.binder` arm as a `bound_choice` meta, preserving the
combiner structure); else (pure context-split binders only) → collapse to one
context meta as before.

Banks zermelo +1 FULL on its own and is general — verify it standalone (breadth
byte-identical, depth ≥ 325, no per-theory regression) before layering B on top.

### C. Reduce substitution redexes for emission, gated by a has-redex pre-walk *(normalization)*

Prototype piece #5. The emitted line needs the reduced `Id Nat(...)` form for the
verifier (the rule's conclusion is `Id`, not `sb_ty …`), so reduction at emit time
is genuinely required — it **cannot** be pushed lazily to a match-time
def-equality check. Reduce only subtrees rooted at a `registry.rewrites_by_head`
head (`sb_ty`/`sb_tm` → `Id`/…) via the existing `Canonicalizer`; recurse
`join`/`nd`/`has_ty` structurally so the context join association stays
byte-identical to the pool refs (a full `canonicalize` re-associates the `@acui`
`join` and breaks the positional readback — see Pitfalls).

**Recover the euclid +19%:** add a cheap O(depth) structural pre-walk — "does any
subtree head sit in `rewrites_by_head`?" — and **skip the `Canonicalizer` init +
walk entirely** when none is present (return the target unchanged). Apply at the
generation target in both `emitGeneratedSlot` and `emitOpenTarget`. If
memoization is still wanted after the pre-walk, key into the existing
transparent-match / def-eq memo (`project_transparent_match_memo`,
`project_inner_matcher_memo`) — do **not** add a fourth cache. Confirm euclid wall
returns toward baseline while the frontier/worst-case wins hold.

### B. Seed unfold-exposed binders as shared metas in the candidate store *(the keystone)*

Folds prototype pieces #1 + #2 + #3 into one spine, dropping the parallel store
and the parallel match branch.

1. **Seed (exact_seed.zig `makeExactRuleCandidate`).** Instead of scrubbing every
   placeholder-laden binding, build a single def-dummy-id → meta map: one fresh
   `.meta` per distinct def-unfold dummy id, **registered in the candidate's own
   `ApplyCandidate.store`** (types.zig:741), applied across all bindings so all
   occurrences of a given dummy share one meta. Keep a placeholder-laden binding
   as metas iff its binder occurs in a hypothesis that will be ref-matched (the
   motive class); scrub binders occurring only in to-be-generated slots to null
   (they reconcile via the open path — A). Derive the keep/scrub partition from
   the rule's hyp templates (which binders a ref-matched hyp determines vs. which
   only a generated slot determines), **not** from the rule name.

   - *Drop the ephemeral single-interner store + `registerLocalMeta` (#1)
     entirely.* The seed metas are already first-class in the candidate store; no
     parallel store is needed.

2. **Match (exact_match.zig `matchOneHypWithSnapshot`).** Make the normal hyp
   match **meta-aware when the candidate store is non-empty**: when the bindings
   embed a registered meta, instantiate the hyp template and
   `solveCorrespondence(&candidate.store, theorem, ref_expr, pattern, null)`
   against the ref, then deref-writeback so `C`/`k` become concrete and ride into
   the sibling-slot lookups. This is the *same* `solveCorrespondence` the open
   path uses for `ih` — fold it into the existing match path rather than a
   parallel `tryMetaAwareMatch` branch. It must fall through (no rejection) on
   no-live-meta or structural conflict.

After A + B, both binders reconcile through the one shared store:
`k` at the hyp0 ref-match, `ih` at the open-target readback against the generated
`id_trans_ty[l14,l19]` conclusion.

### D. Prune undetermined-motive generation goals *(perf guard)*

Prototype piece #4. Complementary to B, not redundant: B covers the concrete-goal
entry (motive seeded as a meta); D covers the **generation-goal (`iwc`) entry**
where the motive is genuinely unpinned and would flood `Ty ?C` against the whole
ref pool. Skip such a candidate. Generalize the predicate to "undetermined
conclusion motive on a generation goal," **not** `nat_ind_elim` by name.

### Final gates

- **Gating:** A and C are general and corpus-positive — consider default-on with
  the usual A/B flag. B's keep/scrub and D's prune gate behind their structural
  predicates, not a rule name.
- **Scenario test:** the prototype build's `MissingExpectedBenchmarkSuggestion`
  guard fired (≥1 scenario's expected suggestion changed). Identify and update.
- **Re-run all gates:** breadth (found 4149 / miss 0; top1 may shift, report),
  depth (TOTAL ≥ 325, no per-theory regression), test-frontier-smoke,
  test-search-scenarios. ⚠ depth-check is mandatory at *every* step.

## As-built (deviations from the plan above)

The plan's A and B were both **too broad as written** and regressed a fixture the
prototype's "corpus-clean" claim never covered: `additive_fol` (a stress fixture
wired into `test-frontier-smoke`, *not* part of the 6-theory depth corpus). Two
scoping fixes were required, plus one latent bug:

1. **A must be gated to non-`@auto`-backward rules.** Opening every openable
   bound binder in place inside an ACUI combiner broke the `@auto`-backward
   *witness* rules (`drinker`, `fan_in`, `branch_converge`, …): they resolve such
   binders through the force-first / enumeration machinery, which the *old*
   hard-block routes to, and opening in place derails it. The eliminator
   (`nat_ind_elim`) is reached via constrained-MP and is **not** `@auto`-backward,
   so the distinction is exact. Implemented as
   `OpenInstantiateOptions.open_bound_in_combiner`, set at both `emitOpen` call
   sites to `!registry.isAutoBackwardRule(rule_id)`. Bisection: with A reverted,
   `additive_fol` is clean but the target misses; with A gated, both hold.

2. **B's meta-aware match must be scoped to the eliminator seed metas.** Firing it
   whenever the bindings carry *any* `.meta` leaf hijacked **carry-to-leaf**
   witness metas (`rim`/`rex`/`drinker`'s `P ?t`), which baseline defers to leaf
   forcing (`.unknown`) — the meta-aware path prematurely resolved them and
   returned `.matched`. Fixed by marking the seed metas distinctly: they are
   minted via `addReconciliationMetaPlaceholderResolved`, which sets
   `PlaceholderInfo.reconciliation_meta` on the leaf, and `tryMetaAwareHypMatch`
   targets exactly those (`exprMentionsReconciliationMeta` /
   `registerReconciliationMetaLeaves`). The flag travels with the leaf across
   `clone()`, so the marker needs no candidate-side bookkeeping or signature
   threading (it sits on `PlaceholderInfo` alongside the existing `meta_id`, an
   analogous search-store concern). A pure carry-to-leaf candidate has no
   reconciliation metas, so it skips the meta path entirely and is byte-identical
   to baseline.

3. **Dep-slot exhaustion (latent bug).** The meta-aware match re-instantiates the
   hypothesis per ref attempt; the holey instantiation's default factory mints
   *standard* placeholders, each consuming a scarce u55 dependency bit →
   `DependencySlotExhausted` at k=2. Fixed with a dep-free `.meta`-class factory
   (`mintMetaPlaceholder`) for the holey open binders (they only need to be
   wildcards for `solveCorrespondence`).

**D was deferred, not implemented.** With A+C+B the global worst-case latency is
already fixed (the `add_comm` flood is gone; the pre-existing, unrelated
`DISJ_CASES` k=2 at ~32s dominates), and A+C+B reaches *higher* martin_lof
completeness than the prototype (mean frontier 1.94 vs 1.90). D is a perf-only
prune of doomed iwc-motive floods whose only cost today is ~20s of martin_lof
wall on searches that genuinely miss; implementing it risks trading completeness
for speed (against the project's forced-not-heuristic stance) for no worst-case
benefit. Left as an optional follow-up; revisit only if total wall regresses.

**Build-process note.** Default `zig build` does not rebuild the `search-bench`
exe and its cache is content-addressed, so `ls -t .../search-bench` can silently
return a stale binary after an edit. Always build/run the bench via
`zig build bench-search -- …` (or check the build exit code) before trusting a
result — several confusing measurements this session traced to a stale binary.

## Final benchmarks (as-built, full depth bench)

| theory | base full | as-built full | mean frontier |
|---|---|---|---|
| euclid | 21 | 21 | 1.17 |
| zermelo | 96 | **97** | 1.21 |
| church | 39 | 39 | 2.07 |
| peano | 38 | 38 | 1.76 |
| martin_lof | 10 | 10 | 1.94 |
| zermelo_hilbert | 120 | 120 | 1.49 |
| **TOTAL** | **324** | **325** | **1.54** |

Breadth byte-identical (4149 / miss 0 / top1 3764). Target `add_comm` k=1
MISS 41.6s → FOUND 11.4s; global worst-case 41.6s → 31.9s (DISJ_CASES k=2,
pre-existing). euclid wall flat vs baseline (the has-redex pre-walk eliminated
the prototype's +19% euclid regression).

## Pitfalls (learned in the prototype)

- **Don't full-`canonicalize` the generation target** — it ACUI-re-associates the
  context `join` (`@acui eq_raw_ctx_assoc _ emp _`, left-assoc parse) away from the
  raw pool refs, breaking the positional `solveCorrespondence` readback. Reduce
  only rewrite-rooted subtrees (**C**).
- **Per-occurrence meta minting breaks sharing** — the `k` in `arg1`, in `C`, and
  in `s` must map to ONE meta; use a shared def-dummy-id → meta map.
- **The open path is phase-5-only for `nat_ind_elim`** (constrained-MP), since it
  is not `@auto`-backward; that is why k=1 only succeeds in the last phase.
- **`instantiateTemplateConcrete` treats a meta-bound binder as "concrete"**
  (returns it, metas included) — a meta-laden target then dead-ends on the
  concrete path's identity `conclusion == target` check. A binder that must
  reconcile at a *generated* slot must be left *null* (open), not meta-bound — the
  decision rule in "The unifying mechanism."

## Key files / anchors (as-built)

- `src/frontend/compiler/inference/open_terms.zig` — `instantiateTemplateOpenInner`
  `.app` combiner branch; `templateHasExcludedUnresolvedBinder` /
  `templateHasOpenableUnresolvedBinder` split; `OpenInstantiateOptions
  .open_bound_in_combiner` gate (**A**).
- `src/frontend/compiler/search/exact.zig` — the `open_bound_in_combiner` is set
  to `!isAutoBackwardRule(rule_id)` at both `emitOpen*` option sites (**A**);
  `reduceRedexOnly` + `containsRewriteRedex` pre-walk applied in
  `emitGeneratedSlot` / `emitOpenTarget` (**C**).
- `src/frontend/compiler/search/forward.zig` — `solveCorrespondence` (the shared
  reconciliation primitive; treats a placeholder as a meta iff registered in the
  passed store, :1216).
- `src/frontend/compiler/search/exact_seed.zig` — `partitionSeedBindings`
  (`multiHypBinderMask` keep-rule) + `rewriteDummiesToSharedMetas` (**B**).
- `src/frontend/compiler/search/exact_match.zig` — `tryMetaAwareHypMatch` folded
  into `matchOneHypWithSnapshot`; scoped via `reconciliation_meta` (**B**).
- `src/frontend/compiler/inference/meta_store.zig` — `registerLocalMeta` (registers
  a `.meta` leaf by local pid so `solveCorrespondence` will unify it).
- `src/frontend/expr.zig` — `PlaceholderInfo.reconciliation_meta` +
  `addReconciliationMetaPlaceholderResolved` (the seed-meta marker, clone-safe).
- `tests/search_bench_cases/martin_lof_frontier.{mm0,auf}` — the bench case;
  `tests/search_bench_cases/additive_fol.{mm0,auf}` — the smoke fixture whose
  carry-to-leaf/witness rules forced the two scoping fixes above.
