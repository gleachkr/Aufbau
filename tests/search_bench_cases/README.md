# Search benchmark (`bench-search`)

Latency + capability harness for the proof-search engine that backs the
`exact?`, `apply?`, and `auto?` editor actions. The driver is
[`src/search_bench.zig`](../../src/search_bench.zig); the fixtures it runs live
in this directory.

It is **not** a unit test — it is run on demand to (a) catch latency
regressions in search and (b) keep the current capability frontier visible: a
fixed list of goals we can solve, plus a fixed list of goals we cannot solve
*yet* (the work tracked in [`META.md`](../../META.md)).

## Running

```bash
zig build bench-search -Doptimize=ReleaseFast \
  --cache-dir .zig-cache-local/ --global-cache-dir .zig-cache-global/ -- --compact
```

Flags (after `--`):

| Flag | Meaning |
|------|---------|
| `--compact`, `-c` | One line per scenario: `name  total  setup  search` timings. |
| `--filter=TEXT`   | Run only scenarios whose name contains `TEXT` (substring). In frontier mode, filters theorem (block) names instead. |
| `--frontier=MODE` | Skip the scenario bench and run frontier analysis (`breadth` or `depth`, below). |
| `--files=MM0:AUF` | Frontier fixture pair (repeatable). Default: the major `tests/proof_cases/` developments. |
| `--marker=TEXT`   | Frontier search marker (`auto?` default; `exact?`/`apply?` disable generation). |
| `--max-depth=N`   | Frontier `auto?` generation depth (default 6). |
| `--slow-ms=N`     | Breadth lines slower than this (warm search) are flagged SLOW (default 2). |
| `--verbose`, `-v` | Print every frontier line/theorem, not just misses, SLOW lines, and nonzero frontiers. |
| `--counters`      | Under each breadth MISS/SLOW row, print key counters (tryCandidate calls/rejects, pool sizes, top rules by validation attempts). |
| `--sweep=FAMILY[:N1,N2,...]` | Discrimination/scaling sweep (below). Synthesize a distractor theory parametrized by N and plot search time vs N. |
| `--help`, `-h`    | Usage. |

Without `--compact` each scenario prints a full counter dump (tryCandidate
calls, prune counts, per-rule attempt diagnostics, etc.) — use it when
investigating a single scenario, usually together with `--filter=`.

Always build `-Doptimize=ReleaseFast`; debug timings are meaningless and slow.

## Frontier analysis (`--frontier=`)

On-demand corpus analysis over the real developments (see `META_STRESS.md`),
not part of the bench gate — a full run is thousands of search invocations
and takes minutes.

- **`--frontier=breadth`** — per-line ablation: every labeled proof line in
  the corpus has its `by <application>` replaced with the marker and is
  re-searched against the preceding pool (the engine ignores later lines).
  Reports found%, top-1 human-match (conservative: normalized string
  equality), misses, and SLOW lines. A miss is a concrete capability gap
  with the human answer attached.
- **`--frontier=depth`** — suffix truncation: each theorem's final line is
  targeted with `auto?` while the k lines immediately preceding it are
  removed, k growing until search fails. The frontier (max successful k) is
  how much proof tail generation can rebuild; `FULL` marks theorems whose
  entire body regenerates from the hypotheses alone. Success is monotone in
  k (removing lines only shrinks the pool), so first-failure is the
  frontier.

Frontier runs are read-only analysis, so they point at the shared
`tests/proof_cases/` fixtures directly; the bench-local-copy convention
applies only to scenario fixtures.

### Regression guards (`zig build test-frontier-smoke`, wired into `zig build test`)

`--require-no-miss` exits nonzero on any MISS/ERR (breadth) or any non-`FULL`
theorem (depth). `build.zig`'s `frontier_guards` array wires a set of these into
the test gate, each with per-guard budget overrides (`max_depth`, `gen_nodes`,
`gen_fuel`, `fwd_facts`, `fwd_attempts`, `fwd_layers`) so a deep proof can raise
its own budget without loosening the conservative global search defaults.

Two flavors:

- **Per-line guards** (`filter` set) pin one hand-picked theorem just above its
  measured budget floor — they catch a *budget* regression on that line.
- **Fixture-total guards** (`filter` omitted → whole fixture) pin the FULL
  *total* of an entire bespoke-stress fixture (META_STRESS.md §3): depth +
  `--require-no-miss` over every block fails unless `full == theorems`. These are
  the completeness backstop for theories #1–#3 — they catch a regression on any
  *unguarded* line and force any newly-added theorem to reach FULL (or be given
  coverage). Current totals (2026-06-25): `additive_fol` 84/84,
  `transitive_closure` 7/7, `quantifier_alternation` 18/18. Each total uses the
  union of its own per-line budget overrides, so it is no looser than the line
  guards it subsumes, and trips if that union drops below floor.

## Discrimination/scaling sweep (`--sweep=`)

META_STRESS.md bespoke theory #4. Where the frontier modes measure *capability*
over a fixed corpus, the sweep measures *how search cost scales* as the
candidate pool grows. It synthesizes a distractor theory in memory at each N
(no fixture files) with a deliberately **unprovable** goal — so the full
candidate set is always exhausted (a clean no-result probe, like
`forward_stress`) — runs the probe search at each N, and prints the time-vs-N
curve plus the discrimination counters that explain its shape. The `growth`
column is the per-point time ratio normalized to N's growth: `~1.0` is linear,
`<1` flat/sublinear, `>1` superlinear (a blowup).

Three families, each isolating one candidate-discrimination path:

- **`head_distinct`** — N rules with *distinct* conclusion heads (plus one real
  goal rule). `rule_index.lookupGoal` must filter all N → `candRules` stays
  constant, search **flat**. Rising `candRules`/time means the index stopped
  discriminating.
- **`head_shared`** — N rules all concluding the goal head with distinct
  unprovable hypotheses. They share the goal's bucket, so each is a candidate
  that must be rejected → `candRules ≈ N`, search **linear**. Superlinear = a
  candidate-loop blowup.
- **`ref_fanout`** — one rule whose first hypothesis has a wildcard argument
  matching all N pool refs and a second hypothesis no ref satisfies → every
  fanned-out ref is looked up then rejected → `refRefs ≈ N`, search **linear**.

```bash
zig build bench-search -Doptimize=ReleaseFast -- --sweep=head_shared
zig build bench-search -Doptimize=ReleaseFast -- --sweep=ref_fanout:512,1024,2048,4096
zig build bench-search -Doptimize=ReleaseFast -- --sweep=head_shared --marker=exact?   # isolate search from generation
```

`--marker` applies (default `auto?`; `exact?` disables generation, isolating the
core matcher from the generation path). Points default to `8..512` if omitted.

## How a scenario works

Each `Scenario` (see the struct in `search_bench.zig`) pairs an `.mm0` theory
with an `.auf` proof that contains a search marker:

```
<theorem-name>
--------------
l1: $ <goal> $ by auto?      <- marker is one of: exact?  apply?  auto?
```

The harness reads the `.mm0` for the theorem signature, finds the marker offset
in the `.auf`, and calls the same `suggestionsAtSourceOffset` entry point the
LSP uses. Key fields:

| Field | Meaning |
|-------|---------|
| `marker` | Which action to invoke (`exact?` / `apply?` / `auto?`). Must appear in the `.auf`. |
| `expected_replacement` | The suggestion string the run must produce. |
| `expect_result` | `true` (default): the run FAILS if `expected_replacement` is not among the suggestions. `false`: a capability/latency probe with no required replacement. |
| `expected_suggestion_count` | Optional exact suggestion count. Use `0` for unsupported probes that should stay unsolved until intentionally reclassified. |
| `expect_saturation_exhausted` | Optional assertion on the forward-saturation exhaustion flag (`forward_saturation_exhausted`). `false` = the loop reached a fixpoint; `true` = it stopped on the budget. Guards the adversarial-saturation probes against dedupe-key regressions. |
| `expect_derived_refs` | Optional assertion on the exact derived-ref count (`derived_ref_count`). Pins forward-dedupe behavior (e.g. confluence collapsing two recipes to one fact). |
| `generate` | `auto?` generation options (`enabled`, `max_depth`, …). Leave default for `exact?`/`apply?`. |
| `exact_result_limit` | Mirrors the LSP single-proof cap; `null` keeps every result visible. |

`expect_result = false` records a probe: the benchmark still runs it for
latency and stability, but does not require a particular replacement string.
For deliberately unsupported goals, also set `expected_suggestion_count = 0`;
that makes an unexpected new suggestion fail the bench until the scenario is
intentionally reclassified. When a later stage teaches the engine to solve the
goal, flip `expect_result` to `true`, remove the zero-count assertion, and pin
the proof in `expected_replacement`.

### Diagnosing what a goal actually returns

The harness prints every suggestion when an `expect_result = true` scenario
*fails*. To see what `auto?` produces for a new goal, temporarily set
`expected_replacement` to a sentinel that cannot match (e.g.
`"__PRINT__"`), run with `--filter=`, and read the printed `suggestion:` lines.
Then set the real expectation (or `expect_result = false`).

## Fixture file convention (important)

**Bench fixtures must be self-contained copies in this directory** — both the
`.mm0` and the `.auf`. Do not point a scenario at a `tests/proof_cases/*` file:
those are shared with the proof-case suite **and bundled into the web demo**
(`build.zig` copies `tests/proof_cases/{fixture}.{mm0,auf}` into
`web-demo/fixtures/`). A shared file edited for a proof-case or demo reason can
silently break or skew a benchmark.

Known exception / drift risk: several existing `auto?` scenarios still reference
`tests/proof_cases/zermelo.mm0`, `martin_lof.mm0`, and `zermelo_hilbert.mm0`
(~3000 lines of shared theory). These predate this convention and are candidates
for migration to bench-only copies. New cases should not add to that list.

## Baseline

[`BASELINE.md`](BASELINE.md) records the Stage 0 compact timing table and the
full counter dumps for the `auto?` scenarios. Later stages should update it
when they intentionally change the scenario set or the capability frontier.

## Capability status

The `expect_result = false` probes below are currently-unsolved goals or
negative controls. They are deliberately failing-to-find, not bugs. Stage 4
open backward generation, Stage 5 ACUI member-witness enumeration, and
Stage 7/8 forward saturation are now supported for the positive cases listed
after this table.

| Scenario | Purpose | META.md stage |
|----------|---------|---------------|
| `stage5 no valid member auto? (no result)` | Confirms enumeration proposes nothing when no ACUI member matches the meta fragment. | 5 guard |
| `stage5 unit context auto? (no result)` | Confirms the ACUI unit element is never a witness domain member. | 5 guard |
| `inconsistent repeated unknown auto? (no result, Stage 4)` | Confirms repeated existential occurrences reject inconsistent child proofs. | 4 guard |
| `missing @vars witness auto? (no result, Stage 4)` | Confirms hidden bound witnesses are not allocated without an explicit `@vars` pool entry. | 4 guard |
| `unannotated rule auto? (no result, Stage 4 gate)` | Confirms the open backward path is opt-in via `@auto backward`. | 4 guard |
| `bare-meta target auto? (no result, Stage 4 guard)` | Confirms a target with no rigid root is not explored. | 4 guard |
| `recover-owned fallback auto? (no result, Stage 4)` | Confirms an unfired `@recover` law prevents generic fallback deferral. | 4 guard |
| `auto backward exact? ignored (no result, Stage 4)` | Confirms `exact?` does not use open backward generation. | 4 guard |
| `auto martin_lof add_comm capstone auto? (no result)` | Higher-order induction motive not pinned by the conclusion. | beyond Stage 7 |
| `auto martin_lof id_sym_ty J_elim auto? (no result)` | Path-induction motive plus eigenvariables not conclusion-pinned. | beyond Stage 7 |
| `auto zermelo_hilbert imp_id auto? (no result)` | Nothing conclusion-pinned, so the desirable behavior is cheap bounded failure. | termination / fuel guard |
| `zermelo nd_and_comm auto?` / `zermelo nd_eq_symm auto?` | Need an ACUI idempotency cascade or deep equality chains, not member witnesses. | beyond Stage 5 |

Mode-boundary guards:

| Scenario | What it checks |
|----------|----------------|
| `auto backward exact? ignored (no result, Stage 4)` | `exact?` has no generation hook, so open backward search is unavailable. |
| `auto backward apply? stays one-step (Stage 4)` | `apply?` may list the annotated rule, but only as `hyp_only_use [ref1]`. |

Supported open-backward cases:

| Scenario | What it pins |
|----------|--------------|
| `hyp-only witness auto? (Stage 4 open backward)` | A regular witness that appears only in a generated hypothesis. |
| `generated child pins parent auto? (Stage 4 open backward)` | A generated child conclusion propagates a witness back to the parent. |
| `repeated unknown auto? (Stage 4 open backward)` | Two sibling hypotheses share one existential assignment. |
| `bound @vars choice auto? (Stage 4 open backward)` | A hidden bound witness is drawn from the explicit `@vars` pool. |
| `euclid ex_intro open witness auto? (Stage 4 open backward)` | `@recover` builds the reduced hypothesis surface and recovers the witness. |

Supported ACUI member-witness cases (META.md Stage 5):

| Scenario | What it pins |
|----------|--------------|
| `zermelo nd_exists_intro_mem auto? (Stage 5 ACUI witness)` | The flagship: `ex_intro`'s recover target `A ∈ A ⊢ ?t ∈ A` solves `?t := A` from the context's own member. |
| `stage5 repeated meta from member auto?` | One member match solves the same hash-consed meta at two positions consistently (`?t ∈ ?t`). |
| `stage5 ambiguous members auto? (deterministic order)` | Two tagged-domain members fill the repeated fragment; both suggestions are emitted in deterministic context-member order. |
| `zermelo nd_union_intro_imp auto? (Stage 5 split + witness)` | Context splitting and witness extraction interact: the split pins `G`, then the hypothesis-only witness `y` is read off `G`'s member. |

Supported forward-instantiation cases:

| Scenario | What it pins |
|----------|--------------|
| `all_elim forward instantiation auto? (Stage 7 forward)` | Nested universal instantiation (`mono f` → ∀∀ → instantiate twice) now succeeds via one forward saturation layer. |
| `all_elim single-step instantiation auto? (supported boundary)` | Single-step `all_elim [#1]` with a goal-recoverable witness already works via `@recover`. |
| `all_elim two-layer derived direct auto? (Stage 8 forward)` | A two-layer derived ref solves shared universal holes in one goal match. |
| `all_elim three-layer chain auto? (Stage 8 forward)` | A three-layer forward chain materializes a nested recipe. |

Adversarial-saturation cases (META_STRESS theory #5, `adversarial_saturation.mm0`).
These are no-result probes (goal `R` unprovable) that pressure the two saturation
guards — the *recipe* key (rule + source tuple) and the canonical *surface shape*
key — and assert the exhaustion flag plus derived-ref count, so a dedupe-key
regression fails the bench even though the no-result outcome is unchanged. The
predicate families are disjoint so each loop class fires in isolation.

| Scenario | What it checks |
|----------|----------------|
| `adversarial commutativity loop auto? (fixpoint, no result)` | `comm` swaps `g`'s args, regenerating from its own output; the shape key drops the swapped-back fact and the recipe key blocks re-firing, so saturation reaches a fixpoint (`exhausted = false`, 1 derived fact) instead of spinning to the budget. |
| `adversarial mutual regeneration auto? (exhausts, no result)` | `ping`/`pong` build an unbounded `h`-tower; the frontier stays productive every layer, so saturation must stop on the budget with exhaustion reported (`exhausted = true`). |
| `adversarial confluence dedupe auto? (collapses, no result)` | `viaA`/`viaB` derive the identical fact by distinct recipes; the surface shape key must collapse them to a single derived ref (`exhausted = false`, 1 derived fact). |

When adding a gap probe: author a bench-only `.mm0`+`.auf`, confirm
`auto?` currently returns nothing (or the wrong thing) via the diagnostic trick
above, add the scenario with `expect_result = false` and a name that states the
missing feature. If it should produce no suggestions, set
`expected_suggestion_count = 0`. Then list it here with its stage and update
`BASELINE.md`.
