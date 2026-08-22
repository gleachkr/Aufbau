# Aufbau 0.0.7

Aufbau 0.0.7 adds alpha renaming to `conversion?`, closes the
last places where a binder had to be supplied by hand in a theory that
distinguishes variables from names, and publishes the manual. The
verifier is unchanged; the MM0 parser is stricter in one respect, noted
under compatibility.

## Highlights

### `conversion?` renames bound variables

A `@conversion` annotation takes a third role token, `alpha`, which enrolls
an alpha-renaming lemma:

```
--| @conversion alpha
axiom all_alpha {x y: nat} (p: wff x): $ (all x p) <-> (all y (sb x y p)) $;
```

A pairing scheduler compares same-head binder instances already in the egraph 
and, when one denotes the other under a lexical renaming of bound atoms, fires 
the lemma with `y` instantiated to the partner's atom. `y` always comes from an 
instance already present, so the egraph doesn't blow up too badly. Renamings 
nested several binders deep close outside-in, as substitution rules push each 
image through the next binder; alpha closure is only as complete as the 
enrolled substitution calculus, and where the image stalls the search reports a 
saturated miss rather than a forced negative. The `herbrand` fixture now proves 
bound-variable renamings next to its rules of passage, each from a one-line 
`conversion?` goal.

### Variables and names as separate sorts

A theory can keep quantifiable variables and proper names in distinct sorts
that both coerce into terms. `@recover` and `@abstract` hoist terms through the 
coercion: the recovery walk compares a quantifier body on the variable side 
against a concrete instance on the name side and re-sorts what it finds through 
the coercion graph. And the eigenvariable of a two-premise elimination, which 
occurs only in the discharged premise and never in the conclusion, is recovered 
from the premise's context split rather than guessed.

The new `zach` theory demonstrates this capability: first-order natural 
deduction after *forallx: Calgary*, which distinguished bound and eigenvariable 
sorts.

### The manual is online

The user manual is published at <https://grahamlk.me/Aufbau/manual>. 

## Compatibility

The MM0 parser is slightly stricter: hypothesis binders must now
follow all variable binders. This follows a convention that mm0-c enforces.

Everything else is additive: `@conversion alpha` is a new role token, and
the coercion-aware recovery and eigenvariable inference only supply
bindings that previously had to be written out — proofs that write them
still compile. Source builds still require Zig 0.15.2.

Aufbau remains pre-1.0 software; APIs and proof syntax may still change.

---

# Aufbau 0.0.6

Aufbau 0.0.6 is a small release with two `auto?` fixes and two new demo
theories. The verifier and the trusted kernel are unchanged.

## Highlights

### `auto?` finds witnesses the instance erases

A vacuous quantifier elimination, e.g. `⊢ (∀ x s0) → s0`, where the bound
variable does not occur in the body, needs a witness term, and nothing
about the goal can determine which one, precisely because substituting it
changes nothing. The search minted the witness metavariable, observed that
the resulting goal was already fully solved without it, and then carried
every branch into a validation failure for the binder it had never
assigned; the goal missed at any budget. Such a witness is now recognized
as genuinely underdetermined and taken from the theory's `@vars` pool. 

### Searches cannot take down the WebAssembly instance

The three wasm executables link with an 8 MiB stack, matching a native
thread, and the search's recursive descent carries a call-stack guard: a
branch that recurses close to the limit is abandoned and reported as an
exhaustion, naming the ladder phase and depth it stopped in and advising a
smaller goal or an intermediate lemma, since no search parameter raises
this bound. Previously a branching search could overrun the much smaller
default wasm stack. The guard is set above what real proofs reach; the deepest 
corpus in the test suite peaks at roughly a tenth of it.

### Linear logic and System F join the demos

`girard` is intuitionistic linear logic. It turns on the contrast the other 
sequent demos leave implicit: leaving the context's idempotence slot empty 
makes a context a multiset rather than a set, so every hypothesis is consumed 
exactly once, weakening and contraction are inadmissible, and they come back 
only under `!`. `reynolds` is System F as typing rules. Both are in the browser 
demo's theory picker, as is `diaconescu` (choice implies excluded middle), 
which the corpus already carried.

See the [changelog](CHANGELOG.md) for the complete list.

## Compatibility

The verifier and trusted kernel are unchanged; MMB files from earlier
releases verify as before, and existing `.mm0`/`.auf` sources compile
unchanged. The `auto?` change only adds proofs where the search
previously reported a miss, and a search stopped by the new call-stack
guard reports a budget-style exhaustion rather than a definitive negative.
Source builds still require Zig 0.15.2.

Aufbau remains pre-1.0 software; APIs and proof syntax may still change.

---

# Aufbau 0.0.5

Aufbau 0.0.5 makes `conversion?` write proofs the way a person would —
chains that ran to hundreds of lines now come out at hand-written length —
and teaches the compiler to speak German. The verifier and the trusted
kernel are unchanged: everything new lowers through ordinary proof lines
the 0.0.1 verifier already accepts.

## Highlights

### `conversion?` writes short chains

Emitted conversion chains are dramatically shorter. Extraction prefers
routes that traverse directed rules in their reducing direction; big-step
groups absorb whole rewrite cascades instead of being split mid-cascade by
a sibling subtree's reduction; a line identical to one already emitted
cites the earlier label; consecutive steps compose with their own sort's
transitivity at the deepest position they share and transport through the
enclosing congruences once, the way a person composes equalities with
`eq_trans`; and when an AC operator is also declared `@acui`, pure
rearrangement steps are elided outright — the line check's normalized
validation re-derives them. On the manual's lambda-calculus examples: the
Y-combinator fixpoint chain drops from 35 lines to 12 (the hand-written
proof's shape), Church `2·succ` application from ~185 to 16, Church
`1 + 1 = 2` from ~2160 to ~100, and the 16-digit carry cascade from ~1670
to ~120.

### Diagnostics in German

One binary embeds a complete message catalogue per language. Select with
`--lang de` (or the `ABC_LANG` environment variable) on the CLI, or pass
`locale: "de"` to `loadCompiler`, `loadLspServer`, or
`loadLspServerWorker` in the WebAssembly packages; `setLocale` switches at
runtime. Everything the compiler says is localized — error and note
prose, context lines, and the error/warning/note framing labels. A
missing translation is a compile error, so a locale cannot ship partially
translated.

Underneath, the diagnostic pipeline was reworked for the purpose: one
renderer and one catalogue serve the CLI, the language server, and the
WebAssembly compiler; the web compiler's JSON `message` field carries the
fully rendered diagnostic (it was summary-only, so detail lines never
reached the web editor); and every error that can reach a diagnostic now
has written prose — raw Zig error identifiers no longer leak.

### Fixes

- A normalizer failure inside `conversion?`'s big-step commit gate no
  longer kills the whole search: the gate declines the group and falls
  back to elementary proof steps, and its acceptance test now replays the
  checker's exactly.
- Big-step `@rewrite` normalization opens redexes buried inside
  already-concrete subtrees instead of reporting "no reduction" on
  expressions it could reduce.
- An equation goal whose sides converge during seeding no longer stops
  saturation for good when the direct proof cannot be lowered, and a
  degraded extraction is reported as "conversion found, proof not
  extracted" rather than a flat miss.
- The def_ops unit-test suite runs under `zig build test` again — it had
  silently run zero times since an April test reorganization — with its
  accumulated rot repaired.

See the [changelog](CHANGELOG.md) for the complete list.

## Compatibility

The verifier and trusted kernel are unchanged; MMB files from earlier
releases verify as before, and existing `.mm0`/`.auf` sources compile
unchanged. Locale selection is opt-in and defaults to English. Embedders
that display the WebAssembly compiler's JSON `message` field now receive
the full rendered diagnostic rather than the summary line alone.
`@aufbau/lsp`'s worker protocol gained a `locale` message type, backward
compatibly. Source builds still require Zig 0.15.2.

Aufbau remains pre-1.0 software; APIs and proof syntax may still change.

---

# Aufbau 0.0.4

Aufbau 0.0.4 ships the Aufbau Manual, lets proofs cite hypotheses by name,
teaches `conversion?` to prove equations outright and to take big steps
through computations, and makes `auto?`'s witness invention standing policy
rather than an annotation-gated retry. It is also the first release to
change the trusted kernel since 0.0.1 — three fixes, each making it
stricter.

## Highlights

### The Aufbau Manual

[The Aufbau Manual](https://gleachkr.github.io/Aufbau/manual/) is a
book-length guide with live proof-editor cells throughout: the examples
compile in the browser as you edit them. It runs from a first proof through
the MM0 and `.auf` languages and a section on designing theories, to five
worked theories — a Hilbert calculus, natural deduction, Peano arithmetic,
the lambda calculus, and program correctness — plus embedding guidance and
reference appendices for the annotations, search parameters, and grammars.
CI compiles every live cell and diffs the outcome against a recorded
baseline, so the examples cannot silently rot.

### Cite hypotheses by name

`#h` refers to the hypothesis declared by a named binder in a theorem or
lemma header (`(h: $ a $)`), anywhere a positional reference like `#2` is
legal, with language-server validation, hover, and completion. Positional
references keep working; arrow-form hypotheses have no name and stay
positional.

### `conversion?`: equation goals and big steps

A goal that is itself an equation — `$ 2 + 2 = 4 $ by conversion?` — now
proves itself. The search seeds both sides, rewrites one into the other,
and grounds the chain with `refl`: no reference line, and no transport rule
required of the sort's `@relation` bundle.

When the theory also enrolls `@rewrite` rules, emitted chains take big
steps: a fold step whose result sets off a rewrite cascade becomes one line
stating its conclusion in rewrite-normalized form, the same way a
hand-written proof cites `beta` with the reduced conclusion. Steps that
cannot be re-derived that way keep the elementary form, so mixed chains are
fine. The same directed normalization also runs as a semantic step inside
`auto?`, so goals blocked behind an unreduced redex can match after
normalizing.

### Witness invention as standing policy

An `@auto`-enrolled rule may now be applied with the binders the goal does
not determine opened as existential metavariables — in the main search
phases, at every depth, with the metavariable carried into nested
sub-goals. Un-enrolled rules get a constrained last-resort form that
invents nothing, and principal enumeration no longer needs an annotation
at all.

### Clearer diagnostics

Diagnostics were reworked against a graded battery of beginner mistakes.
Citing a term as a rule, citing a line label as a rule, citing a later
line, and leaving a search placeholder in a finished proof each name the
misunderstanding; a conclusion mismatch states what the theorem concludes
against what the last line proves; and math-string parse failures are
sort-aware — text that parses under a different sort is reported as
exactly that.

### Three strictness fixes in the trusted kernel

- More than 55 bound variables in scope is now an explicit error instead
  of silent dependency-bit truncation, which could let a
  dependency-violating proof verify.
- Definition dependency masks are emitted in the MMB spec's index space.
  Definitions declaring a dummy before a bound binder previously produced
  masks that mm0-c rejects; recompile MMBs built from such definitions.
- Result-sort dependency lists on `term` and `def` declarations are
  honored end-to-end, so a definition can no longer launder away a
  dependency its body actually has.

### Fixes

- `prefix` and `notation` declarations with a trailing argument at the
  operator's own precedence now register the level right-associative, as
  mm0-c does, rejecting a grammar ambiguity abc previously accepted.
- Alpha-freshening repair handles several blocked binders at once.
- Hypothesis references resolve correctly through multi-name binder groups
  (`(h1 h2: $ a $)`), which the language server previously paired one
  hypothesis per formula — sliding every name after the first onto the
  next formula.
- A proof line that does not parse no longer costs the rest of its block:
  the language server recovers line by line, in indexing and analysis
  both.
- `@aufbau/lsp` can be loaded straight from a CDN: the worker now boots
  through a same-origin `blob:` shim in the cross-origin case.
- The symbolic search engine no longer leaks memory on every rewrite-rule
  instantiation.

See the [changelog](CHANGELOG.md) for the complete list.

## Compatibility

This release tightens the trusted kernel; nothing previously rejected is
newly accepted. Now rejected: theories with more than 55 bound variables
in scope, grammars pairing a trailing-argument notation with an `infixl`
at the same precedence level, and definitions whose bodies have free
variables their result type does not declare. MMB files from earlier
releases verify unchanged with one exception: definitions declaring a
dummy before a bound binder produced off-spec dependency masks (mm0-c
always rejected them), and those files should be recompiled. Proof syntax
is additive — named hypothesis references are opt-in — and existing
`.mm0`/`.auf` sources compile unchanged unless they relied on a newly
rejected shape. Source builds still require Zig 0.15.2.

Aufbau remains pre-1.0 software; APIs and proof syntax may still change.

---

# Aufbau 0.0.3

Aufbau 0.0.3 teaches `conversion?` to compute, and makes it considerably
harder to break. It adds `@compute`, a directed-computation counterpart to the
`@conversion` equality-saturation rules, and a substantial batch of fixes to
saturation, proof extraction, and failure reporting. The verifier and the
trusted kernel are unchanged: everything new lowers through ordinary proof
lines that the 0.0.1 verifier already accepts.

## Highlights

### `@compute` — directed computation inside `conversion?`

A `@compute ltr` (or `rtl`) annotation enrolls a hypothesis-free theorem
concluding `rel(lhs, rhs)` as a *computational* rule. Compute rules are
excluded from general equality saturation; instead, a directed fold scheduler
inside the same egraph reduces each node's first fresh match once, running to
fixpoint before each saturation iteration. For a terminating rule set this
makes computation cost linearly many folds where undirected saturation
explores an exponential closure: the motivating digit-addition table with
carries folds 16-digit sums to a found, verified chain at plain defaults,
where the same rules as `@conversion` grind a widened search to a
budget-limited fixpoint.

Theorem variables are inert constants to the fold — `x + 0` reduces by an
enrolled zero law just as a constant sum does — and rules with bound binders
enroll too, provided the chosen direction binds every binder from the matched
term (a fold may consume a quantifier, never invent one), with their
variable-dependency side conditions enforced by the same match-admission gate
as `@conversion` rules. That combination is enough to run an equational
lambda calculus: the test suite evaluates beta-reduction through an explicit
object-level substitution operator, with capture avoidance falling out of the
dependency conditions, and folds applied lambda terms down to numerals.

Fold steps lower as ordinary rule citations, so the verifier sees nothing
new. Because the fold commits to one reduction order, a saturated miss with
compute rules enrolled is reported as *not* a forced negative, and
declaration order is the fold's redex priority — `docs/rewrite_system.md`
covers how to order a rule table.

### Sturdier saturation, extraction, and failure reports

Most of the release is `conversion?` keeping its promises under stress. The
search no longer stalls permanently when a dense equation cluster floods rule
matching (the applied-match ledger now persists across iterations), no longer
exhausts memory when rules build nested results over AC-absorbed operators,
and a budget-capped run that changes nothing now ends as a *budget-limited
fixpoint* — the report says outright that raising `iters:` cannot help,
instead of suggesting a larger value that would burn minutes reaching the
same place.

Proof extraction — the step that turns a convertible egraph into a verified
rewrite chain — was hardened against three classes of self-referential
structure: e-classes merged with compounds of themselves (which previously
recursed without bound and could crash the language server), classes that
contain their own children via vacuous rewrites like `x + 0 = x` (which
could fail to extract, or worse, miscite a rule instance), and rule
instances whose nested sums canonicalized differently at explanation time
than when the rule fired. Provably convertible goals in all three shapes now
emit ordinary verified chains.

### Fixes

- `conversion?`'s dependency gate now honors *declared* variable
  dependencies, not just structural ones: a theorem variable `(m: tm y)`
  depends on `y` through its binder declaration alone, and a rule match
  whose side condition required avoiding `y` was previously admitted anyway
  — the search could claim a capture-unsound goal proven and emit a chain
  the verifier rejects. Such matches now defer honestly, in both match
  admission and extraction.
- Explanation extraction terminates on cyclic ground-sum classes instead of
  overflowing the stack mid-session in the language server.
- Bag-member claiming falls back to structure-matching the rule pattern
  against recorded members when re-instantiation lands in a class the union
  never touched (carry rules hit this on every chain).

See the [changelog](CHANGELOG.md) for the complete list.

## Compatibility

MMB proof files produced by earlier releases remain valid. Proof syntax is
additive: `@compute` is opt-in, and existing `.mm0`/`.auf` sources compile
unchanged. Source builds still require Zig 0.15.2.

Aufbau remains pre-1.0 software; APIs and proof syntax may still change.

---

# Aufbau 0.0.2

Aufbau 0.0.2 is a feature release focused on proof automation. It adds an
equality-saturation tactic, richer feedback from the existing search, and a
substantial rework of the compiler's error messages. The verifier and the
trusted kernel are unchanged: everything new lowers through ordinary proof
lines that the 0.0.1 verifier already accepts.

## Highlights

### `conversion?` — an equality-saturation tactic

A new search placeholder, `conversion?`, proves a goal by rewriting. It builds
an egraph from the goal and the surrounding proof context, saturates a set of
rewrite rules under congruence, and — when the goal becomes convertible to a
hypothesis or an earlier line — replaces the placeholder with an ordinary
proof: the rewrite chain, its congruence lifts, and a final transport. A
saturated miss is reported as a genuine negative; a run stopped by its budget
says so and suggests wider limits.

Rules come from three places:

- `@conversion` annotations enroll a hypothesis-free theorem concluding
  `rel(lhs, rhs)` for a registered `@relation`, with a direction token.
- `@conversion assoc` / `comm` role tokens certify a theorem *is* an
  operator's associativity or commutativity law. An operator with both (and
  `@congr` coverage) is absorbed into the term representation itself:
  applications intern as flattened, sorted multisets, so AC reasoning costs no
  saturation work and large conjunctions stay tractable where a plain tree
  representation blows up exponentially.
- `@conversion unfold` / `fold` / `both` on a definition enrolls its own
  defining equation, so goals split across a definition boundary close without
  a hand-written bridge. Definitions with hidden dummy binders may enroll only
  `fold`, which is sound by construction.

Local equations participate automatically: a hypothesis or earlier line of the
form `rel(lhs, rhs)` acts as a ground rewrite between its sides (the `simp [h]`
analogue), no annotation needed. With no `@conversion` rules present at all,
`conversion?` degrades to a congruence-closure prover over those local
equations.

Rules with bound binders — quantifier rules of passage, vacuous-quantifier
drops — respect their variable-dependency side conditions by construction: a
match enters the egraph only when the verifier's disjointness conditions are
satisfiable, and the emitted chain cites a representative that satisfies them.
The new `herbrand` demo fixture exercises this end to end, with prenexification
proofs generated entirely by `conversion?`.

### Richer `auto?` feedback and per-call tuning

A failed `auto?` search now explains *how* it failed: a definitive exhaustion
of the space up to the depth limit versus a truncation by the work budget or
per-phase fuel (naming the ladder phase and depth it died in), how many
candidates were validated versus accepted, and the most-tried rules. Any
search placeholder accepts per-call parameters — `auto? (depth: 8, nodes: 512,
fuel: 8192, budget: 13)` — to widen one search without moving the engine
defaults.

### Logical error messages

The compiler's diagnostics for failed rule applications were reworked to
explain failures in logical terms — which premise or conclusion region does not
line up, expected versus found shapes pretty-printed in the theory's own
notation, which constraint ruled out every remaining match, and dependency
clashes stated as constraints on variables ("bound variables x and y must be
assigned distinct variables") rather than as raw dependency bitmasks.

### `unpack` code action

The language server offers to rewrite a proof line containing inline rule
applications into separate labeled lines, one per hidden application, with each
new assertion filled in from the checked conclusion.

### Fixes

- The WebAssembly compiler escapes all string values in its JSON result, so a
  diagnostic that echoes a source token containing a JSON-special character no
  longer produces output that `JSON.parse` rejects.
- `conversion?` tree-mode matching is memory-bounded: a pathological rule set
  terminates as a capped miss instead of exhausting memory.
- Capture-unfolding of a hidden-dummy definition is rejected at compile time
  rather than producing a proof the verifier later rejects with `DepViolation`.

See the [changelog](CHANGELOG.md) for the complete list.

## Compatibility

MMB proof files produced by 0.0.1 remain valid. Proof syntax is additive: the
new annotations and search placeholders are opt-in, and existing `.mm0`/`.auf`
sources compile unchanged. Source builds still require Zig 0.15.2.

Aufbau remains pre-1.0 software; APIs and proof syntax may still change.

---

# Aufbau 0.0.1

Aufbau 0.0.1 is the first experimental release of the Aufbau Metamath Zero
verifier and proof compiler.

## Included

- `abc`, a native compiler from MM0 source and Aufbau proof scripts to MMB.
- `mm0-zig`, a native verifier for MM0/MMB proof pairs.
- WebAssembly packages for the compiler, verifier, and language server:
  `@aufbau/compiler`, `@aufbau/verifier`, and `@aufbau/lsp`.
- `@aufbau/editor`, browser custom elements for editable theories, proofs, and
  statement indexes, with local compilation and optional language-server
  support.
- The hosted [web demo](https://gleachkr.github.io/Aufbau/).

The npm WebAssembly loaders support browsers and Node. The language server's
worker transport and `@aufbau/editor` require a browser environment.

Source builds require Zig 0.15.2. See the
[README](https://github.com/gleachkr/Aufbau#readme) for build and usage
instructions.

## Status and known limitations

This is pre-1.0 software. APIs and proof syntax may change in later releases.

Aufbau is licensed under the Apache License 2.0.
