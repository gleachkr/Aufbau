# Changelog

This file records notable user-facing changes to Aufbau. The project follows
[Semantic Versioning](https://semver.org/).

## [Unreleased]

### Changed

- `conversion?` emits substantially shorter proof chains. Extraction
  now prefers routes that traverse directed rules (`@compute`, or a
  theorem enrolled in one direction) along their reducing direction;
  the lowering reorders commuting steps so a rule's rewrite cascade is
  not split by a sibling subtree's reduction, letting big-step groups
  absorb whole cascades; a line identical to one already emitted
  cites the earlier label instead of restating it; and once the
  `@compute` fold reaches fixpoint, a redex whose operand was
  meanwhile out-reduced re-fires on the reduced form (gated to
  half-size-or-smaller redexes, so Y-style cyclic classes never
  churn), giving the recorded graph forward routes where it previously
  forced backward detours. The transport frame is compressed too:
  instead of lifting every step to the formula root and joining with
  the formula relation's `trans` there, consecutive steps compose
  with their own sort's `trans` at the deepest position they share,
  and each composed run lifts through the enclosing congruences once
  — the way a person composes equalities with `eq_trans` and
  transports the result once. On the manual's lambda-calculus
  examples: the Y-combinator fixpoint chain drops from 35 lines to 12
  (the hand-written proof's shape), Church `2·succ` application from
  ~185 to 16 (a pure forward evaluation), Church `1 + 1 = 2` from
  ~2160 to ~100, and the 16-digit carry cascade from ~1670 to ~600.

## [0.0.4] - 2026-08-06

### Added

- The Aufbau Manual, at <https://gleachkr.github.io/Aufbau/manual/>: a
  book-length guide with live proof-editor cells throughout, so the
  examples compile in the browser as you edit them. It runs from a
  first proof through the MM0 and `.auf` languages and a section on
  designing theories (equality and normalization, ergonomics, views
  and recovery, powering search, computation), to five worked theories
  — a Hilbert calculus, natural deduction, Peano arithmetic, the
  lambda calculus, and program correctness — plus embedding guidance
  and reference appendices for the annotations, search parameters, and
  grammars. CI compiles every live cell and diffs the outcome against
  a recorded baseline, so the manual's examples cannot silently rot.

- Named hypothesis references: `#h` cites the hypothesis declared by a
  named binder in a theorem or lemma header (`(h: $ a $)`), anywhere a
  positional reference like `#2` is legal. Arrow-form hypotheses have
  no name and stay positional. A reference matching no hypothesis
  binder is an error, as is an ambiguous one — duplicate hypothesis
  names are rejected only when actually cited by name. The language
  server validates, hovers, and completes named references like
  positional ones.

- `conversion?` proves equation goals directly. When the goal line is
  itself `rel(lhs, rhs)` for a registered `@relation`, the two sides
  are seeded as terms in their own right, and joining them proves the
  line with no reference at all: the chain rewrites `lhs` into `rhs`
  and the goal is restated as `trans [refl, chain]` (one `symm`
  instead when the chain lowers in the reverse orientation). A
  computation like `$ 2 + 2 = 4 $ by conversion?` no longer needs a
  grounding `$ 4 = 4 $ by refl` line — and since no transport is
  involved, the form works even for sorts whose relation bundle
  declares no transport rule.

- Big-step lowering for computational conversion chains. When the
  theory also enrolls `@rewrite` rules, a fold step whose result
  spawns a rewrite cascade — a `beta` whose conclusion is a
  substitution redex — is emitted as one line stating its conclusion
  in rewrite-normalized form, and line-check conclusion normalization
  re-derives the absorbed cascade: the same mechanism that lets a
  hand-written proof cite `beta` with the reduced conclusion. Steps
  the `@rewrite` registry cannot re-derive (`@conversion` citations,
  pool equations, groups whose driving rule is itself a `@rewrite`)
  keep the elementary stanza form, and a group that fails to
  re-derive at lowering time falls back to elementary steps instead
  of failing the extraction. The same directed normalization also
  runs as a semantic step of the `auto?` ladder, so goals blocked
  behind an unreduced redex can match after normalizing.

- The language server offers `auto?`, `exact?`, `apply?`, and
  `conversion?` as completions wherever a rule name is legal — the rule
  position after `by`, and argument slots — so the tactics are
  discoverable from the editor rather than only from these docs. They
  sort ahead of the theory's own rules, and they are exempt from the
  applicable-rule filter that narrows rule completions to what the
  search can actually offer, since no rule filter can vouch for a
  placeholder.

### Changed

- `auto?` witness invention is now standing policy rather than a gated
  retry. An `@auto`-enrolled rule may be applied with the binders the
  goal does not determine opened as existential metavariables — in the
  main phases, at every depth, with the metavariable carried into
  nested sub-goals. Un-enrolled rules get a constrained form of
  opening as a last-resort retry after the ordinary candidates miss:
  the child proof must fully determine the unknown by read-back,
  nothing carries into nested openings, and nothing is invented.
  Principal enumeration — trying each concrete goal member as an
  ambiguous rule's principal formula — is now purely structural and
  runs for any rule as a final split fallback, no annotation required.

- Diagnostics were reworked against a graded battery of beginner
  mistakes. Citing a term or definition as a rule, citing a proof-line
  label as a rule, citing a line that comes later, and leaving a
  search placeholder in a finished proof each name the
  misunderstanding ("this name is a term or definition; it can appear
  inside formulas but cannot justify a proof line"). A conclusion
  mismatch states both sides — "the theorem concludes: …" against
  "the last line proves: …" — and says when the two fail to match even
  with definitions unfolded and after normalization. Math-string parse
  failures are sort-aware: an assignment or statement that does parse
  under a different sort is reported as exactly that ("the assignment
  parses, but as sort 'wff'; this binder expects sort 'nat'"), a
  statement of a non-provable sort is named directly, and a token that
  is neither a variable of the theorem nor a notation of the theory is
  said to be that, with a missing-semicolon hint for the classic
  run-on declaration.

### Fixed

- More than 55 bound variables in scope is now an explicit error, in
  both the MM0 parser and the MMB verifier. 55 is the dependency
  bitmask's limit; beyond it, dependency bits were silently truncated,
  so a proof violating a dependency condition on a later bound
  variable could pass verification. (mm0-c's corresponding guard has
  an off-by-one that admits a 56th; the strict cap is deliberate.)

- MMB dependency masks for definitions are emitted in the spec's
  bound-variable index space. MMB numbers dummies after all arguments,
  but the writer indexed masks in source binder order, so a definition
  declaring a dummy before a bound binder emitted masks that mm0-c
  rejects ("bad binder deps"). The writer now emits spec-space masks,
  definition-body checking and the cross-checker compare in matched
  spaces, and a regular argument depending on a dummy — unrepresentable
  in MMB — is an emit-time error instead of a corrupt mask. The
  regression fixture is verified by abc, mm0-zig, and mm0-c; MMBs
  compiled by earlier releases from such definitions should be
  recompiled.

- Result-sort dependency lists (`term fresh {x: tm} (e: tm): tm x`)
  are honored end-to-end. They were previously discarded after
  parsing, so a definition whose body kept `x` free could declare a
  result type that hid it — laundering a real dependency away. The
  parser keeps them, definition-body checking enforces that the body's
  free variables are among the declared ones (superset declarations
  remain legal, mirroring the verifier), the MMB writer emits them,
  and the cross-checker compares them. Verified against mm0-rs and
  mm0-c in the accepting and both rejecting directions.

- `prefix` and `notation` declarations whose final argument parses at
  the operator's own precedence now register that precedence level as
  right-associative, as mm0-c does. Such an operator plus an `infixl`
  at the same level is an ambiguous grammar that abc previously
  accepted — and could then parse math strings differently from mm0-rs
  and mm0-c.

- Alpha-freshening repair handles several blocked binders at once. A
  cited rule that needed multiple bound variables renamed
  simultaneously previously failed after repairing only the first.

- Binder inference can bind a rule binder to a definition's hidden
  dummy variable when the written term exposes it only through a
  transparent unfolding; such lines previously failed to infer.

- The symbolic search engine no longer leaks a small buffer on every
  rewrite-rule instantiation.

- Language-server hover and completion for annotations list the full
  current set; annotations added after 0.0.1 (`@conversion`,
  `@compute`, and others) were missing.

- Hypothesis references resolve correctly through multi-name binder
  groups. A group like `(h1 h2: $ a $)` declares one formula for two
  hypotheses, but the language server paired hypotheses with formulas
  one for one, so every name after the first in a group took the
  following formula — and the last took the conclusion. Hovering `#h2`
  showed the wrong statement and go-to-definition jumped to the wrong
  place, for named and positional references alike. Named references
  now also jump to their own binder token rather than the group's last
  name, and both hover and completion resolve through the same
  resolver the compiler applies to a written proof, so the editor
  accepts and rejects exactly what a proof does. The compiler was
  never affected.

- Completion responses are now a `CompletionList` with
  `isIncomplete: true` rather than a bare item array. The server has
  always filtered rule completions by what the proof search can actually
  apply at the cursor, so `by a` and `by m` yield genuinely different
  rule sets — not two filterings of one list. Returning a bare array
  told clients the opposite: that the list was complete and could be
  narrowed locally as you kept typing, which could leave a stale or
  empty popup with no follow-up request. Clients now re-query per
  keystroke, which measures at under 55 ms across the fixture corpus
  (55 ms on a 145 KB proof, single digits on a small one). Typing a
  placeholder skips the applicability search altogether, since a list of
  search tactics has nothing the search could filter out.

- Typing `?` now narrows completion to the four search tactics instead of
  listing every rule in the theory alongside them. No rule name can
  contain a `?`, so once the token holds one the reader has committed to
  a placeholder. This is done on the server rather than left to the
  client: editors disagree about whether `?` belongs to a word, and the
  ones that say it does not were showing the whole unfiltered list.

- The language server now declares `?` as a completion trigger
  character. Clients only open the completion popup on identifier
  characters unless the server says otherwise, and some close it as soon
  as a non-word character lands in the token — which is exactly the
  keystroke that finishes `auto?`.

- A proof line that does not parse no longer costs the reader the rest
  of its block. The language server indexed a proof block all or
  nothing, so a single half-typed line — the normal state of a file
  being edited — left the whole block with no completions, no hover, no
  outline entries, and no go-to-definition, right when they are most
  wanted. The indexer now recovers line by line, keeping the broken
  line's label and goal so the lines after it can still cite it. The
  analysis path recovers the same way, so code actions and searches
  survive a broken sibling line. The compiler is unchanged: a broken
  line is still an error there.

- Completing a proof rule over an existing search placeholder now
  replaces the placeholder's trailing `?` too. Accepting `exact?` over
  `auto?` previously left `exact??`, because the completion token
  stopped at the `?`.

- `@aufbau/lsp` can now be loaded straight from a CDN. Browsers refuse
  to construct a Web Worker from a cross-origin script, and CORS does
  not lift that, so `loadLspServerWorker()` previously threw a
  `SecurityError` whenever the package was served from somewhere other
  than the page's own origin — an embedding page got a plain editor with
  no hover, completion, or proof search, and had to supply its own
  worker to get them back. It now detects the cross-origin case and
  boots the worker from a same-origin `blob:` URL that imports the real
  module, which leaves `import.meta.url` (and so the sibling
  `lsp.wasm`) pointing at the CDN. Pages with a Content-Security-Policy
  need `worker-src blob:`; callers who pass their own `options.worker`
  or `options.workerUrl` are unaffected.

## [0.0.3] - 2026-07-23

### Added

- `@compute` annotation: enrolls a hypothesis-free `rel(lhs, rhs)`
  theorem (one direction token, `ltr` or `rtl`) as a computational rule
  for `conversion?`. Compute rules are excluded from
  general equality saturation and applied by a directed fold scheduler
  inside the same egraph: each e-node reduces its designated redex once
  (first fresh match in rule declaration order), and the fold runs to
  fixpoint before each saturation iteration under its own round budget.
  Theorem variables of the enclosing theorem are inert constants to the
  fold, so `x + 0` reduces by an enrolled zero law just like a
  constant sum does. Rules with bound binders enroll too, provided the
  chosen direction binds every binder from the matched term (a fold may
  consume a quantifier, never invent one); their variable-dependency
  side conditions are enforced by the same match-admission gate as
  `@conversion` rules.
  This makes terminating computations — digit-addition tables with
  carries are the motivating case — cost linearly many folds instead of
  the exponential closure undirected saturation explores: the
  carry-cascade table that previously ground a widened search to a
  budget-limited fixpoint now folds 16-digit sums to a found, verified
  chain at plain defaults. Fold steps lower as ordinary rule citations.
  Because the fold commits to one reduction order, a saturated miss
  with `@compute` rules enrolled is reported as NOT a forced negative.
  See `docs/rewrite_system.md`.

### Fixed

- `conversion?`'s dependency gate now honors DECLARED variable
  dependencies. A theorem variable such as `(m: tm y)` depends on the
  bound variable `y` through its binder declaration alone, with no
  structural occurrence the egraph could see, so a rule match whose
  side condition required avoiding `y` was admitted anyway — the search
  could claim a capture-unsound goal proven and emit a chain the
  verifier rejects with a dependency violation. Both match admission
  and extraction's representative selection now consult declared
  dependencies, so such matches defer honestly (the lambda-calculus
  test battery's capture case pins the behavior).
- `conversion?` proof extraction no longer fails or miscites rule
  instances on self-containing classes minted by vacuous rewrites
  (`x + 0 = x`, vacuous quantifier drops, vacuous substitutions —
  any rule that unions a node with its own child class). Rendering a
  rule edge's bindings from class representatives could pick a member
  from elsewhere in the chain being explained (a circular obligation
  the alignment guard then kills) or pair endpoint renderings from two
  different members of one class (a citation that is not an instance
  of the cited rule). Edge rendering now pins bindings to the chain's
  in-hand subterms when they denote the recorded classes, retries a
  failed alignment once preferring the newest member for
  self-referential bindings, and never overwrites a pinned binding
  during endpoint anchoring.
- `conversion?` proof extraction no longer gives up when re-deriving a
  rule instance whose nested sum canonicalized differently at
  explanation time than when the rule fired (a class that later folded
  to a value stops splicing into enclosing bags, so re-instantiating
  the rule's target lands in a class its union never touched — carry
  rules that mint nested sums hit this on every chain). Bag-member
  claiming now falls back to structure-matching the rule pattern
  against the recorded members themselves.

- `conversion?` no longer exhausts memory (or grinds for minutes) when
  `@conversion` rules build nested results on top of AC-absorbed
  operators — a hex digit-addition table whose carry rules produce
  `((a + b) + 1) :x d` is the canonical case. Flattening a bag member
  expanded every reference to a shared class independently (the cycle
  guard only tracks the current path), so chains of nested sum classes
  made flat forms exponentially longer than the e-graph itself: the
  process died allocating tens of gigabytes at a few hundred e-nodes.
  Three bounds now contain the corner, each reported through the usual
  "NOT a forced negative" honesty note: a flat form longer than 256
  members is abandoned whole (the node keeps its unspliced shape), one
  iteration's rule matching shares a total enumeration budget instead
  of only per-call budgets, and a budget-capped iteration that changes
  nothing ends the search as a budget-limited fixpoint — the failure
  report says outright that raising `iters:` cannot help, instead of
  suggesting a larger value that would burn minutes to reach the same
  place. The pathological table now degrades to a capped miss in
  seconds even at `(iters: 80, nodes: 100000)`.
- `conversion?` no longer stalls permanently when an unrelated dense
  equation cluster floods rule matching. Saturation runs one iteration at
  a time (so a converted goal can stop the search early), but the ledger
  of already-applied matches was rebuilt from scratch every iteration: on
  hypothesis pools whose associativity/commutativity closure exceeds the
  per-iteration match budget — a handful of chained sums over symbolic
  variables suffices — each iteration re-collected the same
  already-applied rewrites, spent the whole budget re-confirming them,
  and never reached the matches that prove the goal. The search reported
  an iteration cap that raising `iters:` could never satisfy, with the
  e-graph frozen at a fixpoint. The ledger now persists across
  iterations, so each iteration's budget goes to new work: the
  interference case converges in a few iterations, and saturated misses
  are reported as such again.
- `conversion?` explanation extraction no longer diverges on
  self-containing e-classes. Rule sets that derive ground sums
  transitively (digit-addition chains over zero-padded numerals, or
  absorption/idempotence laws) can merge a class with a same-head
  compound of itself (`00 + 00 = 00`); extraction previously recursed
  without bound on such classes, so a provably convertible goal was
  reported as *"a proof chain could not be extracted from it (missing
  @congr coverage or a missing @relation transport)"* — with neither
  missing — and large instances crashed the language server
  (stack overflow) mid-session. Extraction now anchors rendered rule
  endpoints at each explanation edge's exact recorded nodes, keeps the
  redundant unions and congruent duplicates the explanation forest used
  to drop, and — when the forest's unique tree route through a cyclic
  class is inherently circular (an edge on the path re-poses the path's
  own endpoints as its child obligation) — retries the alignment over
  the shortest recorded detour. Already-extracting chains are unchanged
  (the tree route stays primary); the cyclic cases now emit ordinary
  verified chains; and pathological inputs degrade to a fast honest miss
  under explicit route/depth budgets instead of hanging or crashing.

## [0.0.2] - 2026-07-21

### Added

- `unpack` code action: the language server offers to rewrite a proof line
  containing inline rule applications into separate labeled lines, one per
  hidden application, with each new line's assertion filled in from the
  checked conclusion. Offered only when the document checks cleanly and the
  rewritten document does too.
- `auto?` failure reports: a failed search's placeholder diagnostic now
  explains how it failed — a definitive exhaustion of the space up to the
  depth limit vs. a truncation by the work budget or per-phase fuel (with
  the ladder phase and depth it died in), how many candidates were
  validated vs. accepted, the most-tried rules with their accept counts,
  and the concrete parameter to try next.
- Per-call `auto?` tuning parameters: `auto? (depth: 8, nodes: 512,
  fuel: 8192, budget: 13)` widens one search without moving the engine
  defaults (`budget` is in units of ≈1s of calibrated work; `0` uncaps).
  Invalid names/values get their own error diagnostics and are ignored.
  See `docs/proof_search.md`.
- `@conversion` annotation: enrolls a hypothesis-free theorem concluding
  `rel(lhs, rhs)` (for a registered `@relation`) as an equality-saturation
  rewrite, with an explicit direction token (`ltr`, `rtl`, or `both`).
  See `docs/rewrite_system.md`.
- `conversion?` search placeholder: builds an egraph from the goal and the
  reference pool, saturates the `@conversion` rules under `@congr`-gated
  congruence, and — when the goal is convertible to a hypothesis or an
  earlier line — replaces the line with an ordinary proof: the rewrite
  chain (rule instances, congruence lifts, `refl`/`trans`/`symm`) and a
  final transport citing the reference. A saturated miss is reported as a
  forced negative; capped runs suggest `conversion? (iters: N, nodes: M)`.
  See `docs/proof_search.md`.
- `conversion?` local equations: a hypothesis or earlier line whose formula
  is `rel(lhs, rhs)` for a registered `@relation` acts as a ground rewrite
  between its sides (the `simp [h]` analogue), cited directly in the
  emitted chain — no annotation needed. With no `@conversion` rules at all,
  `conversion?` degrades gracefully to a congruence-closure prover over
  the local equations.
- `conversion?` dependency safety: `@conversion` rules with bound binders
  (quantifier rules of passage, vacuous-quantifier drops) now respect their
  variable-dependency side conditions by construction. A rule match is
  admitted into the egraph only when the verifier's disjointness conditions
  have a satisfiable instantiation, and the emitted chain cites a
  representative that satisfies them — a local equation in scope can
  discharge a side condition. Misses caused by dependency constraints are
  called out in the failure report. Enrollment now also rejects `@congr`
  rules whose before/after binders under-declare the head term's
  dependencies, and `@relation` bundle rules with bound binders.
- `herbrand` demo fixture: Herbrand's rules of passage as `@conversion`
  axioms, with a battery of prenexifications and reverse prenexifications
  whose proofs were each generated by a single `conversion?` search —
  including a generalization that is only legal because a local
  equivalence certifies the formula is independent of the bound variable.
  Wired into the web demo's example picker.
- `@conversion assoc` / `@conversion comm` role tokens: instead of a
  direction, a `@conversion` annotation can certify that its theorem IS
  the operator's associativity or commutativity law (the exact shape is
  validated at annotation time). An operator certified both laws (with
  `@congr` coverage) is absorbed into `conversion?`'s term representation:
  applications intern as flattened, sorted multisets, so the AC laws cost
  zero saturation work and large conjunctions stay tractable — the tree
  representation's AC closure grows as `3^n` e-nodes and stops reporting
  forced negatives around seven atoms, where the absorbed representation
  stays linear. Emitted proof chains cite the certificate theorems in
  explicit re-treeing steps wherever a canonical form meets a written
  formula. See `docs/rewrite_system.md`.
- `@conversion unfold` / `fold` / `both` orientation tokens on definitions:
  a def can enroll its own equation `rel(definiens, head args)` for
  `conversion?` saturation, so goals separated by a definition boundary
  (one side folded, one side expanded) close without a hand-written bridge.
  Defs with hidden dummy binders may only enroll `fold` (`unfold`/`both`
  is an enrollment-time error): the fold direction binds the dummy to a
  variable already written in the matched term and is admitted only when
  that variable avoids every argument instantiation, while unfolding would
  have to invent a fresh witness at every match. Each def step lowers as a
  single `refl` line closed by transparent-definition unfolding. Defs are
  never enrolled implicitly. See `docs/rewrite_system.md`.

### Changed

- Diagnostics for failed rule applications now explain the failure in logical
  terms. When omitted rule arguments cannot be inferred, the report names the
  specific mismatch — which region (a hypothesis by index, or the conclusion)
  failed to line up, and the expected versus found shapes, pretty-printed with
  the theory's notation — instead of a single generic "could not infer"
  headline.
- When the structural/ACUI solver cannot complete a match, the report names the
  constraint that ruled out every remaining possibility, states that no way of
  filling in the rule's variables makes the premises match, and shows what the
  cited premise actually proves.
- Dependency-violation diagnostics are now phrased as logical constraints rather
  than raw dependency bitmasks. A clash between two bound variables reads "bound
  variables x and y must be assigned distinct variables"; an illegal occurrence
  reads "the rule does not allow p to mention the variable assigned to x", each
  followed by the offending assignments rendered in the theory's notation.

### Fixed

- The WebAssembly compiler now emits a valid JSON result buffer even when a
  diagnostic echoes a source token containing a JSON-special character. A bad
  math token such as `t\p` was previously copied verbatim into the diagnostic
  detail's `token` field, producing `"token":"t\p"` — an invalid JSON escape —
  so the `@aufbau/compiler` npm package's `JSON.parse` of the result threw and
  `compile()` failed on otherwise ordinary erroneous input. All string values
  in the result JSON (tokens, identifiers, messages) are now escaped.
- `conversion?` tree-mode matching is now memory-bounded. AC-style laws
  enrolled as plain rewrites (a `comm`/`assoc` role token without its
  partner law or `@congr` coverage falls back to ordinary both-way
  rewrites) could drive pattern matching combinatorial against
  merge-heavy e-classes, growing memory without limit until the process
  was killed. The per-match enumeration budget and the per-iteration
  retained-match budget now cover tree matching as well as AC bags, so a
  pathological rule set terminates as a capped miss with the usual
  honesty note ("NOT a forced negative") instead of exhausting memory.
- Capture-unfolding of hidden-dummy defs is now rejected at compile time.
  A stated unfolding whose dummy witness variable also occurs in one of the
  def's argument instantiations (e.g. `ex u (eq u u)` written for
  `somesame u` where `def somesame {.w} (a) = $ ex w (eq w a) $`) is not a
  definitional equality — MMB `UDummy` requires the witness to be disjoint
  from every argument substitution — but the compiler previously accepted
  it and emitted a proof the verifier rejected with `DepViolation`. The
  transparent-def matcher now tracks each expansion's argument dependencies
  and treats a captured witness as an ordinary mismatch, on both the
  written-line and binder-inference paths. See `docs/transparent_defs.md`.

## [0.0.1] - 2026-07-16

### Added

- Initial experimental release of the `abc` proof compiler and `mm0-zig`
  verifier.
- WebAssembly compiler and verifier packages for browsers and Node.
- Browser packages for the language server and embeddable proof editor.
- Hosted web demo.

See the [0.0.1 release notes](RELEASE_NOTES.md) for further details.

[0.0.4]: https://github.com/gleachkr/Aufbau/compare/v0.0.3...v0.0.4
[0.0.3]: https://github.com/gleachkr/Aufbau/compare/v0.0.2...v0.0.3
[0.0.2]: https://github.com/gleachkr/Aufbau/compare/v0.0.1...v0.0.2
[0.0.1]: https://github.com/gleachkr/Aufbau/releases/tag/v0.0.1
