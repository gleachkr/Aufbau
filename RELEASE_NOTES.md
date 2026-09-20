# Aufbau 0.0.11

Aufbau 0.0.11 lets proof-local definitions carry annotations and notation,
makes proof search work through coercions and past broken declarations, and
infers more rule binders without a `@view`.

## Highlights

### Annotations and notation on proof-local definitions

A `def` item with a return sort takes the same `--|` directives as an
`.mm0` term. A local operator can be declared `@acui` or `@conversion`,
with the laws the annotation names proved as lemmas beside it:

```
--| @acui cat_assoc cat_comm emp cat_idem
def cat (g h: ctx): ctx = $ g , h $

lemma cat_assoc (g h i: ctx): $ ctx_eq (cat (cat g h) i) (cat g (cat h i)) $
----
l1: $ ctx_eq (cat (cat g h) i) (cat g (cat h i)) $ by ctx_assoc
```

A local definition may also be given notation, declared in the proof file
exactly as it would be in the `.mm0` file and placed after the corresponding 
definition.

```
def limp (a b: wff): wff = $ a -> b $
infixr limp: $=>$ prec 25;

lemma limp_k (a b: wff): $ a => b => a $
----
l1: $ a => b => a $ by ax_k []
```

`prefix`, `infixl`, `infixr`, and general `notation` are accepted;
`coercion` and `delimiter` are not, since neither can be confined to the
proof file. Later proof lines, lemmas, and definitions may use the token,
and hovers, goal displays, and completions print with the new notation. The 
token and precedence tables are shared with the theory, so a local token should 
be one the theory does not use; a later `.mm0` declaration that collides with 
one is reported as an error.

The `.mm0` side is now checked as well. An `.mm0` statement, notation
declaration, or coercion that named a proof-local definition used to
compile, leaving an `.mm0` file that did not verify on its own. It is now
rejected at that statement. A public definition's filler body may still use 
local definitions; it is emitted only into the MMB.

### Proof search in more places

`auto?`, `exact?`, `apply?`, and the code actions built on them failed
outright in any theory whose `@recover` or `@abstract` crossed sorts
through a coercion, such as a two-sort first-order theory with separate
variable and name sorts. The search now sees the same coercions as the
compiler, and its candidate pre-filter no longer discards a recovery
through a coercion.

A broken declaration or lemma earlier in the file silently disabled search
for every theorem after it. The search now skips the broken item the way
the editor's analysis does, so only the target theorem has to be intact.
Search placeholder status, the search code actions, and the unpack action
also stopped at the first proof-local definition or notation in the file;
they now reach every block.

In the editor, a broken declaration could drop every `@conversion` and
`@compute` rule declared before it for the rest of the file, because the
registry snapshot restored after the failure did not include them. The
snapshot now copies every rule family.

### Fewer views

Three fixes to binder inference let rules whose premise or conclusion
contains an open substitution apply without a `@view`. Without a view, the
compiler binds omitted binders in this order: the cited premises in source
order, then the conclusion, then one retry of any premise that did not
match. Within a single formula the walk is left to right, except that a
subterm whose head has `@rewrite` rules, such as a substitution, and whose
binders are still open is set aside until the rest of the formula has been
matched, then instantiated and normalized against the concrete subterm.

So a separation rule stated as

```
axiom sep_intro {x: set} (t A: set) (p: wff x):
  $ t e. A $ > $ [x/t] p $ > $ t e. { x e. A | p } $;
```

now applies to a goal `a e. setdiff A B`, where `setdiff` unfolds to a
set comprehension with a hidden binder, without a `@view` or `@recover`. The 
implication form `[x/t] p -> t e. { x e. A | p }` also works, where the
substitution *precedes* the comprehension that fixes `x` and `p`. A `@view` is 
still needed when no premise or conclusion determines a binder except through 
the substitution itself, when a hidden definition dummy must be named and no
`@vars` pool is declared, or when two premises each wait on a binder the
other would provide. See `docs/view_recover.md`.

When a hidden binder can only be named from the sort's `@vars` pool and
the pool is exhausted, the compiler now says so instead of reporting a
later tier's generic "could not be determined".

### Packages

The `@aufbau/compiler`, `@aufbau/verifier`, and `@aufbau/lsp` packages
now share one host module for the WebAssembly instance. A call that could not
allocate its second input used to leak the first; every input a call
acquires is now released however the call ends.

## Compatibility

An `.mm0` statement, notation declaration, or coercion that names a proof-local 
definition is now an error. Such files never verified standalone, so nothing 
that was correct is affected. The remaining changes are additive. A `@view` 
that the compiler no longer needs is still honored, so existing annotated 
theories compile unchanged. The MMB format, the MM0 parser, and the package 
APIs are unchanged. Source builds still require Zig 0.15.2.

Aufbau remains pre-1.0 software; APIs and proof syntax may still change.

---

# Aufbau 0.0.10

Aufbau 0.0.10 adds doc comments, shows a declaration's annotations in full
when it is hovered, and fixes an ACUI canonicalization bug that could make
an `@abstract` pattern plug miss its site.

## Highlights

### Doc comments

A `--|` line that does not start with `@` is a doc comment for the associated
declaration:

```
--| Existential introduction: a formula proved of a particular term
--| `t` holds of something.
--| @auto backward
axiom ex_intro {x: obj} (g: ctx) (t: obj x) (p: wff x):
  $ g ⊢ [x := t] p $ > $ g ⊢ ∃ x p $;
```

Doc lines and annotations may be mixed in any order. Consecutive doc lines
form one paragraph, and an empty `--|` line starts a new paragraph. Backticks
mark code spans; other markdown is shown as written. The language server
shows the doc comment when the name is hovered and in completion lists,
and the editor's statement popover renders it above the signature.

### Annotations in hovers

Hovering a declaration now shows every `--|` annotation attached to it
ahead of its signature, where earlier releases echoed only `@view` lines
and reduced the rest to a list of names. The `@rewrite`, `@auto`,
`@abstract`, and `@fresh` lines that decide how a rule behaves under
search are visible at the point of use.

### ACUI canonicalization

The ACUI canonicalizer assumed its two operands were already canonical.
A right-associated but unsorted tree, such as the one an `@abstract`
view produces when its context split lands on a unit, could then
canonicalize to a non-canonical result. The representative comparison
that follows would fail, and the pattern-plug walk reported a missing
binder assignment for a site that was present. Both operands are now
canonicalized before they are merged.

### Releases

A `vX.Y.Z` tag now publishes a GitHub release with that version's
section of the release notes.

## Compatibility

Everything is additive. A `--|` line without a leading `@` was already
accepted silently, so existing files keep compiling, and any such lines
now appear as documentation. The MMB format, the MM0 parser, and the
package APIs are unchanged. Source builds still require Zig 0.15.2.

Aufbau remains pre-1.0 software; APIs and proof syntax may still change.

---

# Aufbau 0.0.9

Aufbau 0.0.9 adds `sorry!` for admitting a proof line, lets the plugs of an
`@abstract` annotation be patterns, and revises the manual's prose
throughout.

## Highlights

### Admitting a line with `sorry!`

A proof line may be justified by `sorry!` instead of a rule. Given
`theorem admitted (p q: wff): $ p $ > $ q $;`:

```
admitted
----
l1: $ p -> q $ by sorry!
l2: $ q $ by mp [#1, l1]
```

The goal is accepted without proof, and the block is otherwise checked as
usual: later lines may cite the admitted line, and the last line must
still match the declared conclusion. The compiler reports a warning at
each `sorry!`, so `-Werror` refuses the build, and `abc` exits with status
3 after writing the output. The MMB carries a `Sorry` instruction at that
line only, so the verifier checks every other step. `sorry!` takes no
bindings or references, and its goal may not contain holes.

The verifier no longer stops at the first admitted statement. It checks
every other statement, then names each admitted theorem and exits with
status 3, as mm0-c does. In the browser, a cell with an admitted line is
marked "admitted with sorry! · not verified" in place of its seal, and the
language server hovers `sorry!` and offers it alongside the search
tactics.

### Plugs as patterns

The two plug slots of `@abstract` accept a `$ … $` pattern over the view
binders in place of a bare binder name. A replacement rule with no
equivalence premise, such as De Morgan's law applied anywhere in a
formula, can then find its own site:

```
--| @view {x: wff} (A B: wff) (r: wff x) (p q: wff): $ p $ > $ q $
--| @abstract r p q x $ ¬ (A ∧ B) $ $ ¬ A ∨ ¬ B $
--| @fresh x
axiom DeM {x: wff} (A B: wff) (r: wff x):
  $ sb (¬ (A ∧ B)) x r $ > $ sb (¬ A ∨ ¬ B) x r $;
```

The walk tries the plug pair at each position before descending, so the
outermost site wins, and one substitution is shared by every site. The
binders the patterns solve are committed to the view state and carried
to the rule binders as usual. A bare name is the trivial pattern of one
already-solved binder, so existing `@abstract` rules behave as before.

### Manual

The manual's prose was revised throughout, and it documents `sorry!`
under "Admitting a line" and pattern plugs under "Plugs as patterns".

## Compatibility

Two exit statuses change. `abc` exits with status 3, after writing its
output, when a proof line is admitted with `sorry!`; a build without
`sorry!` is unaffected. `mm0-zig` exits with status 3 rather than 1 on an
MMB whose only defect is an admitted statement, and it now reports every
admitted theorem rather than the first. A malformed proof still exits 1.

The compiler package's result now includes warnings in `diagnostics` on a
successful compile, where the field was previously empty. The verifier
package reports an admitted statement as `ok: false` with `error:
"SorryUsed"` and a `sorry` count, where it previously reported the same
error without the count.

Everything else is additive. `!` is not an identifier character, so no
existing rule name is shadowed by `sorry!`, and a bare-name `@abstract`
plug is unchanged. The MMB format and the MM0 parser are unchanged. Source
builds still require Zig 0.15.2.

Aufbau remains pre-1.0 software; APIs and proof syntax may still change.

---

# Aufbau 0.0.8

Aufbau 0.0.8 closes three soundness holes in the verifier, makes
`@conversion` rules conditional, and adds Cardano's formula to the demo
zoo.

## Highlights

### The verifier checks the statement it was given

`verifyThm` ran a theorem's proof stream and confirmed the result was a
proof of *something*, but never replayed the theorem's own unify stream
against it. The conclusion was therefore never compared with the one the
`.mm0` file declares, and `Hyp`-introduced hypotheses were never
compared with the declared hypotheses. Both `verifyThm` and
`verifyAxiom` now run a statement-end unification pass mirroring mm0-c's
`UThmEnd` mode: `UHyp` pops the hypothesis list LIFO, `UDummy` is
rejected, and the stream must leave both the hypothesis list and the
unify stack empty.

Two smaller holes closed with it. A statement could cite itself, because the
loop passed the current term and theorem counts plus one as the
available count. mm0-c bumps its counters only after a statement verifies, and 
now so does this verifier. And `sorry` in a conversion position passed 
unrecorded: `ConvSorry` discharged its obligation without setting the flag that
fails the statement, so an admitted conversion could complete a proof
that then verified. The flag is now set before the stack is touched,
and `sorry` in a definition is rejected outright.

Each fix carries synthetic stream tests plus a hand-mutated MMB fixture
under `tests/mmb_mutants/`, paired with the `.mm0` it claims to prove
and with mm0-c as the oracle for the verdict.

### `@conversion` rules may be conditional

A direction-annotated theorem can now carry hypotheses:

```
--| @conversion ltr
axiom div_self (x: nat): $ x ≠ 0 $ > $ x / x = 1 $;
```

A match fires only once every premise is already established in the egraph, 
similar to egglog, so saturation stays a fixpoint computation rather than a 
proof search and a saturated miss is still a forced negative. An equational 
premise discharges when its two sides share an e-class, with the extracted 
chain as its proof. Any other premise discharges when its class is *proven*. 
`@congr` propagates provability, so under `a ≠ 0` and `a = b` the premise `b ≠ 
0` counts as proven once congruence on `≠` merges the two.

### Cardano's formula

The new `cardano` theory proves Cardano's formula for the depressed
cubic, with `conversion?` doing the algebra. There are no
root-extraction operations (the radicals are variables pinned by
hypotheses) so what the theorems check is the algebra behind the
formula: the sum of cubes, the resolvent product, and the formula
itself. Every proof body came from a one-line `conversion?` goal, which
each block keeps in a comment. The fixture ships in the web demo.

This showcases some low-level egraph improvements. Routes are now rendered 
through classes that contain themselves, def leaves open into ACUI bags during 
line checking, structured pattern members claim sub-bags of a seeded bag, and a 
bare-binder fold target is no longer misclassified as a self-loop that consumes 
its own redex.

### Annotations from other tools pass through

An unrecognized annotation is now a warning rather than an error. `@syntax` is 
accepted everywhere without being read, so grammar metadata for an external 
front end travels with the file. Only `@acui` and `@conversion` reach the
rewrite registry.

## Compatibility

Because of improvements to the verifier, an MMB file that a previous release 
accepted may in princple be rejected by this one. Proofs the compiler produced 
are not affected.

One source-level change: a token may be declared infix only once.  A `.mm0` 
file that reuses an infix token needs one of the two renamed — the `church` 
fixture's `bic` alias moved from `<->` to `<=>`. Constants shared between 
`notation` commands are unaffected, since interior constants are matched 
positionally rather than dispatched on.

Everything else is additive: conditional `@conversion` rules are a
relaxed enrollment check, and unrecognized annotations that were errors
are now warnings. Source builds still require Zig 0.15.2.

Aufbau remains pre-1.0 software; APIs and proof syntax may still change.

---

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
