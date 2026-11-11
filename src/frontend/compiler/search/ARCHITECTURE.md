# Search subsystem architecture

This directory is the **proof search** behind `exact?`, `apply?`, `auto?` and
`conversion?`. Given a goal and the ambient theory it produces candidate
`RuleApplication`s (source-proof lines) that, when checked, close the goal. It
is untrusted frontend automation: every suggestion is re-validated by the
checker, so a bug here yields a rejected or missing suggestion, never an
unsound proof.

This file is the map. `exact?` and `auto?` run the search core (`core/`);
`apply?` probes rules one at a time; `conversion?` is a separate e-graph
engine. The largest modules are `core/prover.zig`, `core/terms.zig`,
`egraph.zig`, `egraph/explain.zig` and `conversion/lowerer.zig`. The core's
files carry their design in their header comments; read those before
changing it.

Checker validation here means frontend elaboration, not trusted MM0/MMB
verification. Complete generated proofs still need the trusted verifier;
a search result or successful compilation alone is not that guarantee.

`src/frontend/inference_solver.zig` is a *different* engine (last-resort
omitted-binder inference for a single rule application); it is not part of this
subsystem.

## Entry points

All of them live behind `root.zig` and dispatch from `source.zig`. They share
`SearchSession` (`session.zig`), which lazily builds and caches the rule
index, the reference pool and the ref index, so repeated queries in one
theorem amortize.

- **`exact?`** → `entry.zig:exactTopLevel`. One step of the search core
  (`core/root.zig`, `Request.one_step`): any rule at the root, its premises
  closed by facts (the *reference pool*) or by rules with no premises. Every
  proof is collected (`Request.collect`) and ranked: fewest nested steps
  first, then by rule declaration order, then fewer premises.
- **`apply?`** → `apply.zig`: the rules whose conclusion matches the goal
  (`rule_index.zig` pre-filter, relation transports screened out), each
  probed against the checker (`Check.probeRuleConclusion`) and ranked by
  `rank.zig`.
- **`auto?`** → `entry.zig:generateTopLevel`. The search core on a concrete
  or holey goal, after the call's setup (see "The search core" below). A
  concrete inline slot goal is searched the same way; an inline slot whose
  goal still has unknowns gets `exact?` only.
- **`conversion?`** → `conversion.zig:run` (below).

The core's close-out renders every binder the search chose (witnesses,
eigenvariable names, shares) as an explicit binding, so the checker never has
to re-derive a choice (`core/root.zig` `CloseOut`). The suggestion text is a
separate matter: `source/trim.zig:trimBindings` keeps only the bindings the
checker cannot infer. It tries the suggestion with no bindings first. Failing
that, it checks the line with every binding withheld behind a `BindingOracle`
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
(`g ⊢ t : _ty`) reaches `generateTopLevel` as `Goal.holey`. Each hole is a
hole wvar (`core/wvars.zig`) that the proof fills, and the close-out
validates against the line as written, holes and all.

## The search core

`entry.zig` sets up one call on a clone of the theorem:

1. the `@vars` pool tokens, named as dummies of the clone in sorted order
   (`poolVarsClone`), from which the close-out names leftover
   eigenvariables and witnesses;
2. when the theory has `@auto forward` rules, bounded forward saturation
   over the ref pool (`saturateForward`);
3. `runCore`: `core.run`, recording how it ended (`SearchCounters.core_ran`,
   `core_end`, `gen_last_depth`), and copying a found proof out of the
   core's transient state (`cloneApplication`).

`core.run` (`core/root.zig`) works in a further clone, discarded at the end.
It abstains on a goal outside what it searches (`Result.abstained`), builds
the rule catalog (`core/catalog.zig`) and the facts (pool refs, plus the
derived facts that have sources and hold no universal meta, each standing
for its recipe), then:

- tries the proofs of one step first (`Prover.one_step`); `exact?` stops
  there;
- deepens from depth 1. With no `depth:` it goes on until the budget runs
  out or a pass cuts no goal at the limit (`Prover.depth_cut`);
  `GenerateOptions.coreDepth` gives `default_depth` (6) only to a call with
  neither a depth nor a budget;
- when a pass runs out of alternatives without cutting a goal short, runs
  once more from depth 1 without the limits on passed cuts
  (`Prover.relaxed`), and only then reports the goal exhausted.

The prover (`core/prover.zig`) keeps one agenda of open goals in
continuation-passing style and one proof record. A goal is tried with the
facts that state it and the closers, then the safe rules, and only when no
safe rule applies, the unsafe rules one depth lower. A goal with an
`@rewrite` normal form is tried in that form too, and one headed by a
definition with the rules for each head its unfoldings reach. The finished
record is rendered with every binding explicit and checked once
(`candidate.probe`): the checker stays the only authority on what the core
returns.

Rule roles and the binders a conclusion leaves open (γ/δ witnesses read off a
`@view`/`@recover`, cuts, shares, `@abstract` views) are defined in
`core/catalog.zig`'s header. The catalog leaves out relation transports
(`mpbi`), rules with `@fresh` variables, and bare-binder conclusions of a
bound binder or of a view rule.

### Memos

Every memo lives for one `core.run`, in one interner, so raw `ExprId`s are
stable across it and canonical bag order (`ExprId` order) is too
(`core/terms.zig`). Failures at a depth and W9 successes are memoized under
the goal when it is ground and under its `core/keys.zig` key, up to renaming
its witness variables, when not; goals holding shares are keyed with their
splits (`sharedKey`); exact proof sets of a goal's own witness variables are
kept as `Answers`. The deepening after the one-step pass, and the relaxed
run, each start without the memos made before them (`Prover.forget`), which
held only under the limits then in force. The prover header gives the conditions under which each is written; any new memo
must hold for the whole run or say why it does not.

### How a miss is classified (`miss.zig`)

`miss.MissReport` reads a failed search's counters once; `source/report.zig`'s
status and detail, the retry code action, and the bench's miss causes all use
it. A miss is *truncated* when a limit cut it short: the global budget, the
stack guard (`CoreEnd.stack`), or forward saturation stopping at its bounds
(`SearchCounters.forward_saturation_exhausted`). A truncated miss reports
`budget_exhausted` status; only an untruncated one reads as a miss.

`core_depth_done` is derived from `core_end`: the last depth started when the
core stopped at its depth limit, one less otherwise. When the call set a
`depth:` and the core searched every depth below it
(`searchedBelowDepthLimit`), or nothing cut the miss short, `miss.retryFor`
raises depth by 2. It doubles every limit that was hit and the budget with
them, and returns null when nothing can help: the stack guard stopped it, the
core never ran (`exact?`, or an `auto?` the core abstained on), the core
exhausted its space (`CoreEnd.exhausted`), or every hit limit is already at
its maximum.

### The cost-weighted per-call budget (`GlobalBudget`)

`GenerateOptions.global_budget` (default 2.3e9, null = off; the `budget:`
parameter in units of 1e9) caps the whole call, forward saturation and the
core; `exact?` and `apply?` draw from the same kind of budget. The unit is
*weighted work ticks*: deterministic, machine-independent op counts
(`expr.zig` threadlocals) with wall-calibrated weights (`types.zig`): intern
probe levels (one per copy-on-write base-chain hop), def-eq symbolic-node
allocations, non-interning tree-walk node visits, a fixed charge per
`spendCandidate` (the clone and setup overhead of one checker attempt), and
the core's own comparisons, matcher steps and walks, which add their weights
to `work_ticks_core` directly. Units ≈ ns of calibrated wall, so the default
reads as "≈2.3 s of work".

The budget is checked at each goal the core expands (`Prover.charge`) and at
each `spendCandidate` (the core's close-out probe, each `apply?` probe, each
pool ref tried in an inline slot); exhaustion unwinds as
`error.SearchBudgetExhausted`. The one sub-candidate poll is the inference
solver's (`expr.zig` `WorkBudget`). `exact?` and `apply?` stop there with the
proofs they have found. `source.zig` `CallBudgets` holds the call's budget and
a second of the same size for checking and trimming the results found, each
charged only for its own work (`GlobalBudget.pause`), so a search that spent
its budget still has its results checked.

The default is set by latency, not by the corpus's most expensive proof: a
few proofs cost more and need a raised `budget:`, which the miss report
suggests. Calibrate with
`bench-search --frontier=depth --verbose --global-budget=0` (per-run
`t=…M (i=… s=… sh=… tc=…)` columns) and refit the weights if the engine's
cost profile shifts.

## Conversion-search entry point

**`conversion?`** is a separate engine (`conversion.zig:run`, dispatched
from `source.zig` like the others). It does *not* share the core.
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

## `@auto` rule annotations

The core applies every rule its catalog admits, annotated or not; a rule's
role comes from its shape and annotations (`core/catalog.zig`): a rule with
no premises is a closer, `@auto bridge` makes a bridge, `@auto eager` a safe
rule, and every other rule is unsafe. `@auto forward` feeds the facts
instead. The annotation is a doc-comment immediately before
the rule's declaration:

```
--| @auto forward
term all_elim ...     -- enroll for forward saturation
--| @auto eager
axiom rim ...         -- invertible: a safe rule, depth-free
--| @auto eager 2
axiom rand ...        -- same, tried after priority 1
--| @auto bridge
axiom weak ...        -- premises closed by facts only
```

Exactly one mode is required (`error.InvalidAutoAnnotation` otherwise; `eager`
takes an optional priority ≥ 1). Parsing lands in
`RewriteRegistry.processAuto` (`rewrite_registry.zig`); the search queries
`isAutoForwardRule` / `eagerPriority` / `isAutoBridgeRule` /
`autoForwardRuleCount`. Annotating a rule never
changes *validity* (every proof still re-validates through the checker); it
only changes the *search*, and `@auto eager` narrows it under the user's
invertibility declaration, which the search trusts.

### `@auto eager [N]` — user-declared invertible rules

An eager rule is a user-declared **invertible** ("don't-care") backward step:
conclusion provable ⟺ premises provable, so backward application is a
decomposition, never a choice. The annotation is validated at parse time to be
*invertible-shaped* — every hypothesis binder conclusion-determined
(`error.EagerRuleDefersWitness` otherwise; a premise-only witness binder like
`rex`'s `t` would make a depth-free step a self-feeding contraction).
A premise-only *eigenvariable* is exempt (`rules.isEigenvariable`: a bound
binder no non-bound binder may depend on, `all_intro {x y}`'s `y`): every
value of it gives the same instance up to renaming, so the step still chooses
nothing.

In the core an eager rule is **safe**: tried after the facts and closers, by
priority then declaration order, at the goal's own depth (so at depth 0
too). Once a safe rule's conclusion matches a goal, the goal's unsafe rules
are not tried. There is no retry without that commitment: a mis-annotated
(non-invertible) eager rule can lose proofs. In the one-step pass a safe rule
does not commit the goal, since its premises may need more than one step.

### `@auto bridge` — premises from facts in hand only

A bridge rule (`auto_bridge_rules`; `weak`: `g ⊢ a > g , h ⊢ a`) needs a
hypothesis (`error.BridgeRuleHasNoHypotheses`). The annotation, not a shape
test, chooses the rule: the compiler cannot check that weakening is
admissible in the theory.

The core gives a bridge its own role (`catalog.Role.bridge`): it is
tried with the closers, at no depth, and its premise goals carry the
bridge's goal (`Goal.bridged`): `Prover.expand` tries the facts, skipping
one that states the bridge's goal (it closed that goal directly), and
stops; a premise no fact closes is not memoized as failed, and `apply`
does not take a bridge step whose premise no fact might close. `weak`'s two
rest binders are shares, so the fact a premise is closed by binds `g` to the
part of the context it states and the settle step hands `h` the rest.
Opening the premise to rules would not terminate: the step costs no depth
and its premise, with a fresh share, is a new goal each time.

### `@auto forward` — enrich the fact pool before the search

Gated by `autoForwardRuleCount() > 0` in `entry.zig`; `forward.zig` fires
only enrolled rules. A forward rule matches its **hypotheses** against the
ref pool and earlier layers (transparent-def unfolding allowed), solves the
ordinary binders, leaves any binder the premises don't determine as a
**universal metavariable** (a *family* fact), and records a
`@recover`-derived shape. Bounded by `ForwardOptions`
(`max_forward_layers/facts/rule_attempts/match_tuples`); stopping at a bound
is reported (`forward_saturation_exhausted`) and makes a miss truncated. The
core takes the derived facts that hold no universal meta, each standing for
its materialized recipe (`forward.materializeApplication`); a family fact is
not one of its facts.

Use forward on **elimination / destructor rules** — the ones that consume a
hypothesis and emit something smaller or more concrete: universal
instantiation (`all_elim`), conjunction or pair destructors, range-restricted
rules whose forward closure stays bounded. A forward rule with no usable
`@recover` surface derives nothing (silently inert, not an error), so a bad
annotation wastes budget rather than corrupting results.

## Bags, ordered contexts, and determined arguments

### Bags in the core

`core/terms.zig` keeps every expression canonical: a commutative `@acui` bag
lists its members in `ExprId` order, once per occurrence its law counts; a
sequence (associative with a unit, nothing more) keeps its order. Matching
gives each template member a distinct goal member (each choice an
alternative); a rest binder takes the minimal complement (a set law's
non-minimal complements are not tried); a sequence matches in order, a rest
binder taking a run. A conclusion bag with more than one rest binder needs a
commutative law: the binders are shares that split the context between the
premises (`Prover.Split`, `catalog.zig`). Without a set law, a rule's node
facing a share another premise has yet to bind takes the members it names from
what the share may hold, and its own rest binder becomes a fresh wvar in the
share's value: a part of the split, settled to what the others leave like a
share (`Matcher.growShare`, `Prover.openParts`); members are counted, so no two
shares hold one copy.

### ACUI subset soundness

Treating a combiner's arguments as a multiset assumes commutativity. The
core sorts and keys members only under a commutative law (`core/terms.zig`,
`core/keys.zig`), and the hypothesis-side binder extraction used for inline
slot goals (`def_match.extractHypPartialBindings`, `source/inline_target.zig`)
reads members as a multiset only when `bag.isCommutative`. Under a
non-commutative subset (AU) the leftover is an *order-constrained remainder*,
not a free multiset complement, so committing a rest-binding there is
unsound.

### Which arguments a head determines (`argDetermined`)

`head_class.zig` classifies every term head once for all of matching
(`HeadClass`: rigid, def, acui, rewrite, unavailable). A rigid head is a
primitive term or a def without a body: no conversion changes it.

A walk of a template against an expression may compare, pin, or descend into
argument `i` of head `h` only when `h(a) ≡ h(b)` forces the two arguments
equal (`head_class.argDetermined`, reached through `semantic.argDetermined`).
A rigid head determines all its arguments. A transparent def determines an
argument only when its body places it at a path of such heads, so a def that
drops an argument (`def K (a b) = a`, the const trap) does not; a
binder-introducing def is no exception, since its dummies are fresh on both
sides. An ACUI combiner, a `@rewrite` head and an unavailable term determine
none. The core compares two applications of a def with an undetermined
argument unfolded (`Terms.lossy`); `def_match.zig`'s `templateArgs` pairs
only determined arguments of same-head applications for the extraction.

### Ordered-context extraction

`def_match.extractOrderedSpineBindings`: a combiner declared with neither
commutativity nor idempotence is a sequence (`acuiIsOrdered`). The
extraction flattens both sides to their unit-free member lists and aligns
them from each end, never along the binary spines, whose association is
arbitrary. With one multi-member leaf (an unbound bare binder) between the
aligned ends, that binder is forced to the members in between. martin_lof's
`var` (`g , x : A ⊢ x : A`) against `g , k : Nat , ih : Nat` in any
association pins `x : A := ih : Nat` and `g := g , k : Nat`. Commutative
combiners use the multiset extractor (`acui.extractAcuiMemberBindings`)
instead.

Every flattening of a combiner application outside the core goes through
`bag.zig`, the search's handle on `acui_bag.zig`, which the checker shares:
`flatten` splices nested applications, drops the combiner's own unit (never
another combiner's) and keeps duplicates in order, returning null on overflow
so callers abstain rather than read a truncated bag. The core reads bags
through `acui_bag.zig` directly.

## The COW interner invariant

`TheoremContext.clone()` (`expr.zig`) is **O(1) copy-on-write**: the clone
borrows its parent's `ExprInterner` as an immutable base prefix
(`base`, `base_count`); `node(id)` delegates to the base for `id < base_count`.
This makes the per-call and per-probe clones cheap.

The soundness invariant: **every clone is short-lived scratch whose parent
outlives it and does not move or free while the clone is alive.** Violating it
is a use-after-free that ReleaseFast *masks* (corrupt reads land on "no
opinion", so results look stable) and debug catches as a corrupt-tag crash.

`flatten()` materializes a clone into a standalone interner (deep-copies the
base nodes, preserving every `ExprId`). **Any "clone a theorem, then
free/replace the source" pattern must `flatten()` the clone first.** Current
flatten sites: `TheoremContext.promote` (used by `candidate.zig:commit` and
`check/apply.zig:SpeculativeAttempt.promote`) and `apply.zig`, whose
accepted candidates keep their attempt theorems.

Cost corollaries:

- The global budget's intern ticks count **probe levels of the base chain**,
  so every extra clone layer between the work theorem and the validation
  clone multiplies the tick cost of the whole validation. `candidate.zig`
  therefore splits validation into `probe` (const theorem/vars; returns a
  `Probe` whose theorem is a COW clone BORROWING the caller's, so it must be
  deinitialized first) and `commit` (flattens and swaps the attempt into the
  caller's state; returns the line index). Callers never pre-clone.
- Only `commit` pays a whole-interner `flatten()`. A probe never flattens.
- A probe drops any inline-conclusion sink entries it recorded and restores
  the caller's diagnostic, whether it succeeds or fails.

## Indices

These narrow the search without dropping proofs. Each must be a *sound*
over-approximation (never drop a match):

- **`rule_index.zig`** — goal-shape → candidate rule ids, for `apply?`.
- **`refs.zig` + `ref_index.zig`** — the reference pool (proof lines +
  theorem hyps usable as facts) and its shape index, used by forward
  saturation and by the pool refs offered in an inline slot. `shape.zig` is
  the shared shape-extraction/indexing core; `clipper.zig` the discrimination
  structure.
- **`core/term_index.zig`** — the core's path index (after `clipper.zig`)
  over its facts and each head's rule conclusions. Every item a query drops
  clashes with the goal (`Terms.clash`, `Terms.conclusionClash`) or cannot
  equal it (`Terms.mightEqual`), so the search is unchanged.

A pruning or indexing change is the dominant perf lever and the dominant
*risk*: a too-aggressive one silently turns a proof into a miss. Every such
change must clear the corpus gate below.

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

- In the sandbox, add `--cache-dir .cache/zig-local` before `--` in each
  build command and set `ZIG_GLOBAL_CACHE_DIR=.cache/zig-global`.
- For ownership/COW changes, also run safety-enabled tests (Debug or
  ReleaseSafe). The ReleaseFast corpus gate does not replace lifetime checks.
- **Always run ReleaseFast and use a freshly built binary.** Debug is slow;
  stale binaries give garbage. The breadth result is the stable oracle.
- Metrics: breadth reports `found` / `miss` / `top1` (rank of the oracle
  suggestion); depth reports per-theorem frontier `k` / `FULL`.
- Defaults: no `max_depth` (the core deepens until the budget runs out or a
  pass cuts nothing), global-budget=2.3e9 weighted ticks
  (`--global-budget=0` disables it for uncapped calibration runs, and the
  depth limit is then 6).
- Determinism is required: the order of rules and alternatives is observable
  through `top1` and the byte-identical suggestions, so preserve the
  catalog order (closers, safe rules by priority, unsafe rules, each in
  declaration order), the unsafe alternatives' sort (`Alt.lessThan`: fewer
  premises no fact might close, then `specificity`, then declaration order),
  and `exact?`'s ranking.

## File index

| file | role |
|---|---|
| `root.zig` | public surface / re-exports |
| `session.zig` | `SearchSession`: lazy index + pool caching |
| `types.zig` | `Goal`, `Context`, `ApplyCandidate`, options, counters, `GlobalBudget` and tick weights, `DerivedRef`/`DerivedPool` |
| `entry.zig` | `auto?` and `exact?` entries (`generateTopLevel`, `exactTopLevel`): the `@vars` pool clone, forward saturation, `runCore`/`endCore`, copying the proof out |
| `core/root.zig` | the search core, in a discarded clone of the work theorem: entry, abstention, facts, the one-step pass and deepening, close-out (name leftover eigenvariables, then witnesses, from `@vars`, render every binding explicitly, one `probe`) |
| `core/catalog.zig` | the rules the core applies, by role (closer, bridge = `@auto bridge`, safe = `@auto eager`, unsafe), indexed by conclusion head; quantifier rules' witnesses (γ, δ) read off their `@view`/`@recover`; cuts, shares, abstractions |
| `core/terms.zig` | canonical ACUI bags, conclusion matching and unification through witness variables (bag members as choice points), unfolding and normal forms, premise building, the view's leaf swap (none where the pattern holds a variable that depends on the hole, or while a premise is still to fix the pattern: the core then reads the witness off the closed premise with the checker's `@recover`) |
| `core/wvars.zig` | witness variables (σ, one undo log) and eigenvariables, named only when a binding or the close-out needs one: level, capture and occurs checks at binding; the W5 signature of a goal's effect on older witnesses |
| `core/keys.zig` | failure-memo keys for goals holding witness variables, up to renaming them |
| `core/term_index.zig` | path index over the core's facts and rule conclusions |
| `core/prover.zig` | the agenda in continuation-passing style, the proof record, γ/δ steps, splits, the W5 prune and dedupe, the relaxed run, and the failure/success memos |
| `meta_store.zig` | the meta store forward saturation's universal metas live in (`DerivedPool.store`); the leaf kinds live in `../inference/open_terms.zig` |
| `forward.zig` | forward saturation (`@auto forward`), recipe materialization, the binding `Namer` |
| `tunables.zig` | per-call search parameters: names, ranges, validation, and applying them to `GenerateOptions` |
| `candidate.zig` | `probe`/`commit` over `tryCandidate`: full checker re-validation on a cloned theorem |
| `apply.zig` | `apply?`: rule-index candidates probed against the checker |
| `rank.zig` | `apply?` candidate ranking |
| `bag.zig` | the search's handle on `acui_bag.zig` (one flattening of an ACUI combiner application: members, unit, laws, rebuild), with the combiner looked up from the search context |
| `acui.zig` | ACUI member extraction, unit normalization and canonicalization outside the core |
| `def_match.zig` | transparent-def-aware matching: one-layer unfolding (`unfoldAppOnce`), the def-body walk (`walkDefBody`), hyp-side binder extraction (`extractHypPartialBindings`, with ordered-spine and ACUI member extraction) |
| `semantic.zig` | the search's view of `../../head_class.zig` (head classes, determined arguments) |
| `shape.zig` / `clipper.zig` | shape extraction + discrimination index |
| `ref_index.zig` / `refs.zig` / `rule_index.zig` | candidate/ref indexing |
| `fixture.zig` | theorem-prefix preparation and test setup (walks the `.mm0` through `pipeline/common.zig`'s shared statement helpers, recovering from broken earlier declarations like the analysis) |
| `source.zig` | `suggestionsAtSourceOffset` (LSP entry; reports a `SearchStatus` outcome): runs the search for one placeholder and renders its suggestions; `CallBudgets` |
| `source/placeholders.zig` | `searchPlaceholders` (placeholder enumeration for the LSP status diagnostics and the search CLI) + the placeholder at a source offset |
| `source/inline_target.zig` | the expected goal of a placeholder nested inside an application |
| `source/trim.zig` | `trimBindings`: keep only the bindings the checker cannot infer |
| `source/report.zig` | status, `conversion?` and retry-advice detail text |
| `miss.zig` | `MissReport` (which limits cut a failed search short, read once from its counters) + `retryFor` (the `auto?` parameters the failure report and its **Retry with …** code action suggest) |
| `egraph.zig` | `conversion?` e-graph core: hashcons + congruence closure, AC bag nodes, dep-safety gate, saturation |
| `egraph/alpha.zig` | alpha pairing scheduler (`collectAlphaMatches`): pairs `@conversion alpha` rule instances under a lexical renaming; its settled cache and watermarks live on the `EGraph` |
| `egraph/explain.zig` | explanation extraction (`ExplainCtx`) + the `Term`/`Step` vocabulary, re-exported through `egraph.zig` |
| `egraph/tests.zig` | egraph unit tests (public-API only) |
| `conversion.zig` | `conversion?` driver: `@conversion` enrollment, pool/goal seeding, absorbed AC certificates, forced-negative reporting |
| `conversion/lowerer.zig` | `Lowerer`: explanation chain → proof-script lines (AC re-treeing seams, congruence descent, pool-equation citation) |
| `tests/` | subsystem unit tests, split by topic; shared fixtures in `tests/helpers.zig` |
