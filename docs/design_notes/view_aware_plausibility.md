# View-aware conclusion plausibility (unblunt the view-rule bail)

Status: **LANDED (first cut, conclusion side).** Grounded in `docs/view_recover.md` +
`src/frontend/views.zig` + `exact_plausible.zig`. Background: the
`auto?` worst-case latency thread ([[project_latency_budget_floor]],
[[project_symbolic_interning]]) — after the interning/hash levers took the worst
case 31.9s→20s, the remaining worst cases are doomed reject-*floods*, and the
global worst (`zermelo/cb_bijection_maps_domain` k=1 ~20s) is a `sep_intro`
view-rule flood that dodges all plausibility filtering.

**Result (2026-07-01):** `cb_bijection_maps_domain` k=1 **~20s → 8.5s** isolated;
`sep_intro` attempts **5020/5020 → 1346/1346** (the view refuter prunes ~3674
doomed candidates before `tryCandidate`), total `tc` 16198 → 7690. Breadth
byte-identical (found 4149/4149, miss 0, err 0, top1 3764); depth **TOTAL 325**
unchanged (euclid 21, zermelo 97, church 39, peano 38, martin_lof 10,
zermelo_hilbert 120); `test-unit` + `test-frontier-smoke` green. The empirical
question below is answered: a *large* share of the `sep_intro` flood is
rigid-RHS and gets caught (the abstained def-RHS remainder is the residual 1346).
The new global worst case is church `DISJ_CASES` (~18s, def-eq-bound, unrelated
to views).

## The problem

`finalConclusionPlausible` (search/exact_plausible.zig) is a sound
*necessary-condition* pre-check run before the expensive `tryCandidate`: it
prunes a candidate only when it can *prove* the rule's conclusion can't match
the goal. It is the filter that catches most doomed candidates.

For **view rules** it bails immediately:

```zig
if (context.views.contains(candidate.rule_id)) return true;   // line ~192
```

That's why `sep_intro` floods: on `cb_bijection_maps_domain` k=1 the counters show
`sep_intro = 5020/5020` (all rejected), `and_intro = 2114/0` (fan-out over a giant
conjunction), `rej_total 6672 / distinct 6672` (**0% repeat**, so the reject-memo
catches nothing). Every doomed candidate is unique and reaches full validation.

The bail exists for a real reason: a view rule's goal matches its **view
conclusion**, not the raw `rule.concl`. Checking `rule.concl` against the goal
would falsely reject (e.g. `ax_inst`: raw `A.x p -> sb t x p` vs the line
`A.x p -> P u`, which only matches the view `A.x p -> q`). So the *blunt* fix
(run the existing check on `rule.concl` for views) is unsound. The *right* fix is
to run it on the **view conclusion**.

## Why the view conclusion is the correct, sound template

From `docs/view_recover.md` (Elaboration pipeline step 3; "Unfold/rewrite
behavior" §2):

- **The view conclusion is the true matching template.** View matching unifies
  `view.concl` against the user's line; if that fails, the rule cannot apply. So
  "goal can't match `view.concl`" ⟹ "rule can't apply" — a valid necessary
  condition (unlike `rule.concl`).
- **`view.concl` is an over-approximation.** Phantom view binders (names not in
  the rule, e.g. `q`) and any unbound mapped binder are unconstrained. A looser
  template prunes strictly *less* → never a false prune. This is the soundness
  key the user flagged: over-approximate hyps/conclusion are fine for a
  one-sided (necessary-condition) filter.
- **The refuter only fires on irreconcilable rigid structure.**
  `templateDefiniteMismatch` abstains on def / `@rewrite` / ACUI heads. View
  matching is itself def-aware and may take semantic rewrite/ACUI steps (§2), the
  *same* moves the refuter already accounts for — so anything the refuter prunes,
  the view matcher also can't bridge.

## The change

In `finalConclusionPlausible`, replace the blunt bail with a view-aware check:

```zig
if (context.views.get(candidate.rule_id)) |view| {
    const goal_expr = /* same extraction as the non-view path;
                         abstain (return true) for holey / implicit-null goals */;
    // Remap rule bindings into view-binder space via binder_map.
    // Phantom binders (binder_map[vi] == null) and unbound mapped binders → null
    // ("matches anything") — the over-approximation that keeps it sound.
    var view_bindings: [N]?ExprId = …;  // N = view.num_binders (stack buf + heap fallback)
    for (view.binder_map, 0..) |mapping, vi|
        view_bindings[vi] = if (mapping) |rule_arg| bindings[rule_arg] else null;
    return conclusionTemplatePlausible(
        context, &candidate.theorem, view.concl, goal_expr, view_bindings);
}
```

Data (confirmed in `views.zig`): `ViewDecl { concl: TemplateExpr,
num_binders: usize, binder_map: []const ?usize (view-binder → rule-arg, null =
phantom), … }`; reachable via `context.views.get(rule_id)`. `view.concl` is a
`TemplateExpr` whose `.binder idx` are **view**-binder indices, so it must be
paired with a **view-space** bindings array — hence the `binder_map` remap.

## Scope for the first cut (keep it minimal / safe)

- Use **only** the base `conclusionTemplatePlausible`, NOT the Lever B (repin) or
  Lever E (deep-member) strengthenings, for views. Those call `pinRigidBinders`,
  which has the documented non-injective-def const-trap latent edge
  (exact_plausible.zig:321 comment). The base refuter is trap-free.
- Non-view path is untouched (keep existing flow byte-identical).
- Extend to hyp-side view plausibility only later, if the conclusion side pays
  off.

## Expected effect on `sep_intro` (view succedent `t ∈ {x∈A|p}`)

- goal `t ∈ (plain var / rigid non-def head)` → rigid clash → **pruned** (sound).
- goal `t ∈ image…/(A∖B)…` → `image`/`setdiff` are comprehension **defs**
  (`image f X B = {y∈B|has_preimage..}`, `setdiff A B = {x∈A|x∉B}`), so the
  refuter compares one unfold layer, sees a comprehension head, and **abstains**
  (correct — `sep_intro` legitimately applies there via unfold).

## The open empirical question (decides the payoff)

Unknown until measured: what fraction of the 5020 doomed `sep_intro` are
rigid-RHS (caught) vs def-RHS (correctly abstained)? The top goal `x ∈ A` is
rigid-RHS (caught); many subgoals after unfolding `injective`/`maps`/`cb_bijection`
are membership in `image…`/`setdiff…` (abstained). Measure via the
`final_conclusion_prunes` counter + maps_domain wall time. If it prunes a
meaningful share → extend (hyp side, more view rules); if it abstains on nearly
all → we've cheaply confirmed "RHS is all comprehension-defs" and stop.

## Guards / kill-switch

- breadth byte-identical: found 4149/4149, miss 0, top1 3764.
- depth TOTAL 325 (per-theory: euclid 21, zermelo 97, church 39, peano 38,
  martin_lof 10, zermelo_hilbert 120).
- `test-unit` + `test-frontier-smoke` green.

A view false-prune surfaces immediately as miss>0 or a dropped frontier → roll
back. View soundness is the historically dangerous area (see the repeated
cautions around view rules), so the corpus is the non-negotiable net, not an
afterthought.

## Risk read

The approach is principled — an over-approximate template + a one-sided refuter
is the theory-correct version of what the code already does for non-view rules.
Residual risk is an implementation slip (binder remap; an unmodeled view-matcher
move); both are caught by the corpus. Latency-only change to the *doomed* path;
it does not aim to find new proofs.

## Key files

- `src/frontend/compiler/search/exact_plausible.zig` — `finalConclusionPlausible`
  (the bail at ~192), `conclusionTemplatePlausible`, `templateDefiniteMismatch`.
- `src/frontend/views.zig` — `ViewDecl` (`concl`, `binder_map`,
  `num_binders`).
- `tests/search_bench_cases/zermelo_frontier.mm0` — `sep_intro` (@view @recover,
  ~590), the comprehension defs `setdiff`/`image`/`diag`, `cb_bijection_maps_domain`.
- Measure: `bench-search --frontier=depth --filter=cb_bijection_maps_domain
  --verbose --counters` (watch `final_conclusion_prunes`, wall); guards via
  `--frontier=breadth` and full `--frontier=depth`.
