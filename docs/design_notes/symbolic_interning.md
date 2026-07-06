# Hash-consing the symbolic-def-eq engine (`SymbolicExpr` interning)

Status: **Phases 1, 1a, 1b, and 3 (expansion memo) landed**; Phase 2
(up-to-alpha fingerprint) tried and reverted (see below). All landed phases:
breadth byte-identical (4149 found / miss 0 / top1 3764), depth **TOTAL 325
unchanged**, `test-unit` / `test-frontier-smoke` green — pure perf. Cumulative
worst-case movement: church `DISJ_CASES` k=2 miss ~31.9s → ~8.6s; martin_lof
`add_suc_right` k=1 found ~8.9s → ~2.9s (the frontier's slowest successful
search). This is task #43; background in the memory files
`project_inner_matcher_memo`, `project_representative_memo_unsound`,
`reference_mm0_variable_model`.

## The cost driver

`perf` on the worst case (church `DISJ_CASES`, depth k=2, an unprovable goal that
exhausts the `max_depth=6` iterative-deepening budget: 9088 `tryCandidate`
calls, ~95% of wall inside `applyRuleApplication`) is almost entirely in
`def_ops/symbolic_engine` — the transparent-def symbolic matcher. Church's rules
(`eqmpr`, `eqmp`, `CONJ`) are defined through lambdas/defs (`F`, `not`, `and`,
`or`), so every conclusion match forces deep def-unfolding + higher-order
symbolic matching, reached via `check/matching.zig`'s transparent-normalization
step during validation.

Pre-interning self-time split (~30s run):

| Bucket | ~% | Symbols |
|---|---|---|
| Materializing symbolic trees | ~30% | `allocSymbolic`, `ArenaAllocator.alloc`, `memcpy` |
| Memo-key hashing | ~20% | `Wyhash.update/.final`, `hashMatchSessionForSearch`, `hashWitnessMapForSearch` |
| Matching | ~15% | `symbolicFromTemplateSubst`, `matchSymbolicToSymbolicState`, `expandSymbolicApp` |

Root cause (durable, from `project_inner_matcher_memo`): `allocSymbolic` did **not
intern**, so structurally-equal re-expansions of a def produce *distinct
pointers* — the same subtree is rebuilt (and re-hashed, re-matched) exponentially.
`symbolicFromTemplateSubst` was measured at 77M calls on a related church case.

## Phase 1 — context-level structural interning (hash-consing)

`SymbolicExpr` is an immutable, index-based value:

```
binder: usize        // positional binder index (de-Bruijn-ish)
dummy:  usize         // slot into the *current session's* symbolic_dummy_infos
fixed:  ExprId        // stable interner id
app:    { term_id, args: []*const SymbolicExpr, hash }  // cached structural hash
```

`allocSymbolic` now delegates to `SharedContext.internSymbolic`: compute the
cached structural hash, probe a hash-cons table (`getOrPutAdapted`, so a hit
costs zero arena bytes), and on a miss allocate the node in the same per-context
scratch arena as before. Structural equality compares `app` children by
*pointer* — exact when children are interned (guaranteed in the common bottom-up
case), and merely under-deduping (never a false merge) when a child was cloned in
from a seed. The table's backing lives on the caller allocator; interned nodes
live in `scratch_arena`. **Intern lifetime == arena lifetime** (both reclaimed at
`Context.deinit`), so it adds only pointer-sized overhead to a budget already
accepted as bounded.

### Why this is sound across match sessions (the crux)

Multiple `MatchSession`s share one `SharedContext` (one arena, one intern table),
and `dummy` slots are **per-session**, so a naive read fears cross-session
conflation of `.dummy N`. It is nonetheless sound: a `SymbolicExpr` node carries
**no session-specific identity**. `.dummy N` / `.binder N` are bare indices
*resolved against whichever session is currently matching*; `.fixed` is a stable
interner id; `.app` is `term_id` + child pointers. Sharing a `{.dummy=0}` node
between sessions is fine because each session interprets slot 0 via *its own*
`symbolic_dummy_infos`. Nodes are also never mutated after construction (returned
`*const`; the only `.app.hash`/`.args` writes are struct-literal *constructions*).

Contrast `chooseRepresentative`'s **materialized** cache, which was unsound
(`project_representative_memo_unsound`): it caches concrete `ExprId`s that embed
*freshly minted theorem atoms*, so replaying one aliases stale identities. That
is the materialization boundary — symbolic nodes are upstream of it and safe.
This is the [[reference_mm0_variable_model]] lesson: the hazard is *variable
identity*, not alpha; interning symbolic nodes touches neither.

### Result

`tc_apply` 28.5s → 22.2s (−22%) on the isolated worst case; arena `alloc`
9.4%→3.4%. `allocSymbolic` self-time *rises* (13.7%→23.3%) because it now carries
the probe, but the downstream savings dominate. Candidate counts, breadth
output, and depth frontiers are all identical.

## What Phase 1 does *not* fix (the next levers)

1. **The `args` slice leaks on an intern hit** — *fixed (Phase 1b, landed).*
   `symbolicFromTemplateSubst` (the hottest node builder) now builds children into
   a per-frame stack buffer and calls `SharedContext.internSymbolicApp`, which
   copies args into the arena *only on a miss*. Recursion gives each level its own
   stack frame, so buffers never clobber; arities above the inline cap (16) fall
   back to the old arena path. Result: martin_lof `add_suc_right` k=1 8.9s → 7.8s
   isolated (~13%), `add_comm` 7.0s → 6.1s; breadth byte-identical, depth
   TOTAL 325. (Helps the def-eq-tree-building cluster; the global worst case —
   the zermelo bijection family, ~20s — is a different bottleneck.)

2. **`symbolicFromTemplateSubst` / `expandSymbolicApp` still re-run per call**
   — *fixed (Phase 3, the expansion memo — landed).* See the dedicated section
   below.

3. **`hashMatchSessionForSearch` still walks all bindings** (addressed in
   Phase 1a below). The *walk* is unavoidable without incremental hashing, but
   the per-element *mixer* was needlessly expensive.

## Phase 1a — cheap-mixer session hash (landed)

The negative memo (`sym_match_neg`) is consulted at the top of *every*
`matchSymbolicToSymbolicState` call (the hottest path), and each consultation
computes `hashMatchSessionForSearch`. That function used a streaming
`std.hash.Wyhash` — with a *nested* Wyhash per map entry — even though every
field it folds is an integer or a short byte string, and the lhs/rhs hashes
beside it already use the cheap inline `mixHash`. A `lhs==.app` gate to consult
the memo *less* was measured (`project_inner_matcher_memo`) at **+26% worse** on
church — the memo is load-bearing there — so the lever is a cheaper *key*, not
fewer probes.

Converted the whole `hashMatchSessionForSearch` family (bound values, the four
witness/alias maps, the dummy-info sort names) and the 3-way memo-key combine to
`Types.mixHash` integer mixing. Coverage is identical (same fields, same
order-independent xor+sum map accumulation); only the mixer changed, so the key
stays a deterministic function of state. Soundness rests on the same standard as
before: the memo already stored only a 64-bit key (unverified), so a hash swap
keeps the (negligible, per-session-scoped) collision risk — and the
byte-identical corpus confirms no collision flipped a verdict.

Result: `DISJ_CASES` k=2 **22.2s → 18.8s** isolated (−15% on top of Phase 1),
breadth byte-identical, depth TOTAL 325, whole depth corpus wall −5%.

## Phase 2 — up-to-alpha negative-memo fingerprint (TRIED, REVERTED: not impactful)

The idea: widen the inner matcher's negative memo (`sym_match_neg`) by keying
lhs/rhs on an up-to-alpha fingerprint (canonicalize `dummy` slots by
first-occurrence order, preserving the distinct-vs-repeated sharing pattern) so
that alpha-variant re-expansions — which differ only by which fresh dummy slots
were minted — collapse to one key and hit the "fails" cache. Because MM0 has no
built-in alpha ([[reference_mm0_variable_model]]), such a fingerprint is sound
only as a *negative*/inequality signal, never an equality/interning key.

Implemented `alphaFingerprint` (O(tree) walk with a small inline first-occurrence
rename map) and swapped it into the memo key in place of the O(1) cached
`symbolicHash`. **Result: `DISJ_CASES` k=2 18.8s → 19.6s (~4% *slower*), with
identical candidate counts (tc=9088) — i.e. zero new memo hits.** Reverted.

Why it bought nothing: `restoreMatchSnapshot` truncates `symbolic_dummy_infos`
back to the snapshot length, so the next expansion **reuses the same slot
numbers**. Slots already recur across the bidirectional-unfold's constant
save/restore, so the *structural* hash already aligns the alpha-variants the
fingerprint targeted — leaving only the added O(tree) walk cost. (This is the
same slot-recurrence that makes Phase 1's dummy interning load-bearing; see the
refuted dummy-bypass note in [[project_symbolic_interning]].) A separate note:
the naive first-occurrence canonicalization is also *unsound* when a dummy is
bound in the state (it collapses `f(d3,d5)`/`f(d5,d3)` under an identical
state-hash even if only `d3` is bound) — so even a productive variant would need
a state-aware canonicalization. Not worth pursuing given the zero measured upside.

## Phase 3 — whole-template expansion memo (landed)

Post-1b profiling on martin_lof `add_suc_right` k=1 (the frontier's slowest
*successful* search) showed ~70% of wall in the expansion pipeline: the intern
probe `getOrPutAdapted` 31.8%, `symbolicFromTemplateSubst` 25.1%,
`allocSymbolic` 12.6% — i.e. the engine spent most of its time rebuilding
structurally identical def expansions bottom-up just to find every node already
interned. (The session-hash walk was down to 2.3%, killing the "incremental
hash" lever.)

The fix memoizes the *whole call*: `SharedContext.template_subst_memo` maps
`(template app-node identity, subst pointer contents)` → the interned result
node, consulted by `symbolicFromStableTemplateSubst` and wired into the four
top-level expansion sites (the three def-body opens in `transparent_match.zig`,
`rewrite_application.zig`'s rule-RHS instantiation) plus `symbolicFromTemplate`.

Why this is exact (not up-to-alpha, not heuristic):

- `symbolicFromTemplateSubst` is a **pure function of (template structure,
  subst pointers)**. It reads no session state — the fresh-dummy minting that
  blocked a naive expansion memo happens in its *callers*, before the subst is
  built, and lands *in* the subst as interned `.dummy` nodes. So the key
  captures it.
- Slot recurrence (the same `restoreMatchSnapshot` truncation that refuted
  Phase 2) means recurring expansions carry the *same* `.dummy` subst pointers
  → memo hits. Diverging slots change the key → miss and rebuild. Alpha never
  enters.
- The memoized value is the canonical interned node, so a hit returns the
  *pointer-identical* result a rebuild would produce — behavior is unchanged by
  construction.
- Template identity is `(args.ptr, args.len, term_id)`, sound because every
  `TemplateExpr` is built into env/registry/view storage
  (`TemplateExpr.fromExpr` call sites: `env.zig`, `views.zig`) and lives for
  the context lifetime. A future *transient* template must use the plain
  `symbolicFromTemplateSubst` (documented on the function). Zero-arity apps and
  bare binders bypass the memo (already as cheap as the probe).

Result: `add_suc_right` k=1 **7.65s → 2.89s** (2.64×), its k=2 miss
10.1s → 4.2s; `DISJ_CASES` k=2 miss **14.7s → 8.6s** (on top of the
query-shape cache); breadth byte-identical, depth TOTAL 325.

## Key files

- `src/frontend/def_ops/shared_context.zig` — intern table + `internSymbolic` +
  the soundness comment; `TemplateSubstMemoKey` + `template_subst_memo`
  (Phase 3).
- `src/frontend/def_ops/symbolic_engine.zig` — `allocSymbolic` delegates to it.
- `src/frontend/def_ops/symbolic_engine/transparent_match.zig` —
  `symbolicFromStableTemplateSubst` (Phase 3 entry point) + the def-open sites.
- `src/frontend/def_ops/types.zig` — `SymbolicExpr`, `symbolicHash`,
  `computeAppHash`.
