# Proof search: `auto?`, `exact?`, `apply?`, `conversion?`, and the `@auto` annotations

Aufbau can fill in proof steps for you. Where you would normally write a
concrete rule application like

```text
l3: $ a -> a $ by ax_id (a := $ a $) []
```

you can instead write a **search placeholder** and let the compiler
propose the finished line:

```text
l3: $ a -> a $ by auto?
```

This document explains what the three placeholders do, how you use them
while editing, and how the `@auto` annotations let a theory teach the
search which of its rules to reach for.

Related docs:

- `docs/proof.md` — the `.auf` proof-script format (rule applications,
  references, inline applications)
- `docs/rewrite_system.md` — `@relation` / `@rewrite` / `@congr` and how
  the compiler infers omitted rule arguments
- `docs/view_recover.md` — `@view` / `@recover` / `@abstract`, which the
  search uses when a rule's written form differs from its raw conclusion

## What the search is (and is not)

The search is **untrusted automation**. It never proves anything by
fiat. Its only job is to *write a proof line for you* — an ordinary
`by RULE (...) [...]` application, exactly the kind you could have typed
yourself. That line is then checked by the normal compiler pipeline like
any other. So a bug in the search can only ever produce a *rejected* or a
*missing* suggestion; it can never produce an unsound proof.

Two consequences follow:

- **A placeholder is scaffolding, not a finished step.** The compiler
  will not emit MMB for a theorem whose proof still contains an `auto?`,
  `exact?`, or `apply?` line. You replace the placeholder with the
  concrete line the search proposes, and *that* line is what gets
  compiled and verified.
- **Anything the search can do, you could have written by hand.** The
  placeholders are a convenience for finding the right rule and its
  arguments, not a separate proof language.

## The three placeholders

All three are written with a trailing `?`, most often in the rule
position of a proof line (they can also go in an argument slot — see
*Placeholders in argument positions* below). They differ in how hard they
look.

### `exact?` — close the goal with rules already in reach

`exact?` looks for a single rule whose conclusion matches your goal and
whose hypotheses are all discharged by things you *already have* — the
theorem's hypotheses (`#1`, `#2`, …) and earlier proof lines (`l1`,
`l2`, …), collectively the *reference pool*. It does **not** invent
intermediate steps.

Use it when you know the goal follows in one step from facts on hand and
you just don't want to spell out the rule name and its argument bindings:

```text
l12: $ nd G Target $ by exact?
```

### `apply?` — like `exact?`, focused on applying one named-shaped rule

`apply?` is a thin variant of `exact?`. It is oriented toward "apply a
rule to what I have" and reports its candidates the same way. In day-to-day
use you can treat it as `exact?`; reach for it when you are thinking "apply
*a* rule here" rather than "close this goal outright".

### `auto?` — search for a multi-step proof

`auto?` is `exact?` plus the ability to **synthesize the missing
sub-proofs**. When a candidate rule needs a hypothesis that nothing in
the pool satisfies, `auto?` recursively tries to *prove that hypothesis
too*, and so on, with iterative deepening and a work budget. This is what
lets it discover proofs several steps deep from just the goal:

```text
l1: $ S $ by auto?
```

`auto?` is the most capable and the most expensive of the three. It is
bounded (see *Budgets and determinism* below), so on a goal it cannot
prove it will give up rather than run forever — but a hard goal can still
take a couple of seconds before it does.

**Which to reach for.** Start with `exact?` when you expect a one-step
close; it is fast and its answer is unambiguous. Use `auto?` when the
step is genuinely a small proof and you want the compiler to find the
chain.

### `conversion?` — rewrite the goal to an existing reference

`conversion?` answers a different question from the other three: is the
goal formula **convertible** — by a chain of enrolled `@conversion`
rewrites, applied anywhere, in any direction — to a hypothesis or an
earlier proof line? It builds an egraph seeded with the goal and every
pool formula, saturates it under the `@conversion` rules (with congruence
closure gated on `@congr` coverage), and on success replaces the line
with an *ordinary proof*: one line per rewrite step, `@congr` lines
lifting each step through the surrounding structure, `refl`/`trans`/
`symm` glue, and a final transport application citing the reference.

```text
goal: $ or r (an q p) $ by conversion?
```

with `h: $ or (an p q) r $` in scope and commutativity of `an`/`or`
enrolled `@conversion both` produces something like:

```text
goal_1: $ iff (or (an p q) r) (or r (an p q)) $ by or_comm
goal_2: $ iff (an p q) (an q p) $ by an_comm
goal_3: $ iff r r $ by iff_refl
goal_4: $ iff (or r (an p q)) (or r (an q p)) $ by or_congr [goal_3, goal_2]
goal_5: $ iff (or (an p q) r) (or r (an q p)) $ by iff_trans [goal_1, goal_4]
goal: $ or r (an q p) $ by mpbi [goal_5, #1]
```

Everything it emits is checked the ordinary way — the search is untrusted
and its output is just proof text.

Beyond the enrolled rules, **local equations rewrite too**: any
hypothesis or earlier line whose formula is `rel(lhs, rhs)` for a
registered `@relation` — an `iff` hypothesis, an `eq` fact proved three
lines up — acts as a ground rewrite between its two sides, no annotation
needed (the analogue of Lean's `simp [h]`). Such a step cites the
reference directly in the chain instead of emitting a rule line (through
one `symm` line when used right-to-left). With relation and congruence
coverage but no `@conversion` rules at all, `conversion?` still runs as a
pure congruence-closure prover over the local equations.

What it needs from the theory: a `@relation` bundle for the goal's sort
*with a transport rule*, `@congr` rules for the connectives the rewrites
must pass through, and `@conversion` annotations on the rewrite theorems
(see `docs/rewrite_system.md`). Three properties are worth knowing:

- **A saturated miss is a forced negative.** If the egraph reaches a
  fixpoint without connecting the goal to any reference, no chain of the
  enrolled rules exists at all — not "the search gave up", but "there is
  no such conversion". The failure report says which of the two happened,
  and hedges the claim honestly when the fixpoint itself was approximate:
  an AC bag-match enumeration that hit its budget, or a self-containing
  class (idempotence/absorption union) kept atomic during AC
  canonicalization, each append their own "NOT a forced negative" caveat.
- **Variable dependencies are respected by construction.** Rules with
  bound binders (quantifier rules of passage, vacuous-quantifier drops)
  only fire when their dependency side conditions have a satisfiable
  instantiation in the egraph — a rule requiring `x` not free in `a`
  never fires with an `a`-class that can only denote `x`-containing
  terms, and the extracted chain cites a representative the verifier
  accepts. A local equation can unlock such a match (an in-scope
  `iff (Pr x) p` lets `al x (Pr x)` leave the quantifier as `p`). When
  dependency constraints refused matches, the failure report says so.
- **Found chains return as soon as the goal converges.** Saturation stops
  the moment the goal shares a class with a reference, so a hit doesn't
  pay for the rest of the budget. This matters in theories whose rules
  keep generating — absorption laws like `x ∨ (x ∧ y) = x` make e-classes
  cyclic, after which the AC rules mint new nodes up to any cap — where a
  genuine miss uses the full iteration/node budget but a hit stays fast.
- **v1 restrictions**: top-level proof lines only (no argument-slot
  `conversion?`), concrete goals only (no holes).

### Placeholders in argument positions

A placeholder need not be the whole line's rule. You can also drop one
into an **argument slot** of a named rule application — the inline-
application syntax from `docs/proof.md` — to pin the outer rule and ask
the search to fill only the slot you left open:

```text
l3: $ b $ by mp [auto?, #1]
```

Here you have committed to `mp` and to discharging its second premise
with `#1`; the `auto?` fills just the first premise. The search works out
that slot's goal from the outer rule and the sibling references, then
searches for it exactly as it would a top-level placeholder. `exact?` and
`apply?` fill the slot with a single rule or reference; **`auto?`
additionally synthesizes a multi-step sub-proof for the slot**, the same
recursive generation it runs at the top level — so `mp [auto?, #1]` can
grow a whole chain in that first premise, and existential witnesses inside
that chain are grounded just as they are for a top-level goal.

One limitation is worth knowing. Inline `auto?` generates only when the
outer rule and its sibling references **determine the slot's goal** — which
is the usual case (`mp [auto?, #1]` pins the antecedent from `#1` and the
consequent from the line goal). If the outer rule leaves the slot's *own*
goal undetermined — a witness argument the rule's conclusion doesn't pin —
an inline `auto?` falls back to `exact?`-style direct matching for that
slot rather than generating. When you need generation there, lift the
sub-goal onto its own top-level `auto?` line and reference it. (See
`docs/design_notes/inline_auto_open_slot_existential_gap.md` for the
details of this boundary.)

## The editing workflow

The search runs in your editor through the language server. The loop is:

1. Write a placeholder line, e.g. `l1: $ a -> a $ by auto?`. The four
   tactics are offered by completion wherever a rule name is — in the
   rule position after `by`, and in an argument slot — so typing `au`
   and accepting gives you `auto?`. They lead the completion list, ahead
   of the theory's own rules, and completing over one replaces its
   trailing `?` as well (swapping `auto?` for `exact?` leaves one `?`).
   Typing the `?` itself narrows the list to just the four: no rule name
   contains one, so a token holding a `?` can only be a placeholder.
2. The editor shows a status on that line while the search runs, then a
   lightbulb (a code action) if it found something.
3. Open the code action. Each suggestion appears as
   **"Replace auto? with …"** (or `exact?` / `apply?`), showing the
   concrete rule application it found.
4. Accept one. The placeholder is rewritten to the real line, and the
   proof recompiles and re-verifies.

If the search finds nothing, the line reports that it has no suggestion
rather than silently doing nothing — so a failed search is
distinguishable from one still in progress. The failure diagnostic also
explains *how* the search failed and what to do about it — see the next
two sections.

> The web demo hosts the language server in a background worker, so even a
> slow `auto?` search never freezes the editor. A search in flight can't
> be interrupted mid-flight, but the page stays responsive and the search
> stops itself when it hits its budget.

## Reading a failure report

A failed `auto?` is not one thing. The placeholder diagnostic
distinguishes the cases, because they call for different responses:

- **"no proof found within depth N. The search space was exhausted
  (… validated: … accepted, … rejected) …"** — the search ran every
  candidate it had, to completion, up to its depth limit. Within that
  depth the answer is definitive: no proof exists over the current rules
  and references. Only two things can change it: search *deeper*
  (`auto? (depth: 8)` — see the next section), or make the space richer
  (prove an intermediate lemma line for the pool, or enroll rules with
  `@auto` annotations).
- **"stopped by the per-call work budget (~Ns of work) during
  `<phase>` at depth D of N …"** — the bounded work budget ran out
  before the search completed, so the empty result is *inconclusive*: a
  proof may exist just past where it stopped. The report names the
  ladder phase and depth the budget died in. Raise the budget for this
  one call (`auto? (budget: 13)`, roughly seconds of work; `budget: 0`
  removes the cap) — or reduce the space with better annotations.
- **"a search phase ran out of fuel (N candidate validations per
  phase) …"** — same inconclusiveness, but the bound that tripped was
  the per-phase validation budget rather than the global one; raise it
  per call with `auto? (fuel: 8192)`.
- **"forward saturation stopped at its bounds …"** — the theory's
  `@auto forward` rules derived facts up to a bound without reaching a
  fixpoint, so the derived-fact pool itself is incomplete.

Failure reports end with a **"Most-tried rules"** list — each entry
shows how many times a rule was *tried* against how many attempts were
*accepted*. A rule tried hundreds of times with zero accepts is a
reject-flood: the search is burning its budget disproving that rule over
and over. That is your cue to look at the rule's annotations (should it
really be enrolled backward?) or at the goal shape that keeps attracting
it.

`exact?` and `apply?` misses are simpler — they are single-shot, so a
miss just reports how many candidate rules and pool references were
considered, and reminds you that `auto?` can additionally synthesize
sub-proofs.

## Tuning a single search (per-call parameters)

`auto?` accepts per-call parameters in its parenthesized argument list,
written `name: INTEGER` (alongside any ordinary `name := $ … $`
bindings):

```text
l1: $ hard goal $ by auto? (depth: 8, budget: 13)
```

| parameter | default | meaning |
|---|---|---|
| `depth` | 6 | iterative-deepening limit: the maximum nesting of generated (synthesized) proof steps |
| `nodes` | 256 | distinct sub-goal solves per depth pass |
| `fuel` | 4096 | candidate validations per retry phase |
| `budget` | ≈6 | whole-call work cap, in units of ≈1 second of calibrated work; `0` disables the cap |

`conversion?` accepts its own pair, tuning the egraph instead of the
generator:

| parameter | default | meaning |
|---|---|---|
| `iters` | 16 | saturation iterations (match-all → instantiate → rebuild rounds) |
| `nodes` | 10000 | e-node cap: distinct term shapes the egraph may hold |

The parameters scope to **that one placeholder** — the engine defaults
never move. This is deliberate: the defaults are tuned so that the
common case (goals the search can crack) stays fast *and* the miss case
(goals it can't) fails quickly; raising them globally makes every doomed
search on every line pay the higher ceiling. A hard goal you are
actively working on is exactly the place to spend more, so you raise
the ceiling there and nowhere else.

Rules of thumb:

- Raise **`depth`** when the report says the space was *exhausted* — the
  proof, if any, is deeper than the ladder looked. Depth is the
  exponential knob; go up in small steps and expect the miss case to get
  slower.
- Raise **`budget`** (or `fuel`, if that is the bound the report named)
  when the report says the search was *truncated* — it never finished
  looking at the depth it was already exploring.
- `nodes` rarely needs touching; the report will steer you to the other
  three first.

A typo'd parameter name or an out-of-range value gets its own error
diagnostic immediately (no search needed), and is otherwise ignored —
it never silently changes what the search does. Parameters are
meaningful only on `auto?`; `exact?` and `apply?` are single-shot
searches with nothing to tune, and reject them with the same
diagnostic.

## The `@auto` rule annotations

Left alone, the search only ever chains rules against *concrete* goals
and *concrete* facts. That is enough for a great deal, but some proofs
need the engine to run a rule **forward** (deriving new facts before it
even looks at the goal) or **backward** through an existential (guessing a
witness). A theory opts specific rules into that richer behavior with an
`@auto` annotation — a `--|` doc-comment placed immediately before the
rule's declaration in the `.mm0` file:

```mm0
--| @auto forward
term all_elim ...          -- run this rule forward, before backward search

--| @auto backward
term ex_intro ...          -- open an existential sub-goal for this rule

--| @auto trigger (hyp p)
axiom ax ...               -- seed ground instances from the goal's subterms
```

Each `@auto` line names exactly one mode — `forward`, `backward`,
`eager` (with an optional priority), or `trigger …`; anything else on that
line is a compile error. The modes are
*per line*, not per rule, though: a rule may carry several `@auto` lines,
and the modes are stored independently with no mutual exclusion. So
in principle you can stack them — `--| @auto forward` and `--| @auto
backward` on the same rule enrolls it for both, and multiple `--| @auto
trigger` lines on one axiom are an ordinary pattern (each contributes
another seed pattern). (`eager` is the exception to "no mutual exclusion":
it *implies* `backward`, so annotating a rule `@auto eager` also enrolls
it backward automatically.) In practice a rule is usually one mode,
since a rule that reads well forward reads badly backward (see the
discipline below), and `trigger` only applies to hypothesis-free rules,
which have nothing for `forward`/`backward` to chew on — but nothing in
the compiler forbids the combination.

Enrollment is **entirely manual** — there is no automatic classifier that
guesses which rules to promote. A rule you don't annotate stays
concrete-only, which is exactly what keeps a plain theory's search results
unchanged. Annotating a rule never affects *validity* (every proposed line
is still re-checked); it only widens *what the search will try*.

### `@auto forward` — enrich the fact pool first

Put `@auto forward` on **elimination / destructor** rules: the ones that
*consume* a hypothesis and yield something smaller or more concrete —
universal instantiation, conjunction projections, and similar
"decreasing" rules. Before the backward search starts, the engine fires
these rules over your reference pool, deriving new facts and adding them
as extra references.

**Family facts (the metavariable part).** A forward rule often can't fully
determine its own output. Universal instantiation is the standard case:

```mm0
--| @auto forward
axiom all_elim {x: nat} (g: ctx x) (t: nat x) (p: wff x):
  $ g ⊢ ∀ x p $ > $ g ⊢ [x/t] p $;
```

Fired forward on a fact `g ⊢ ∀ x p` from the pool, this wants to produce
the instance `g ⊢ [x/t] p` — but the witness `t` appears *only in the
output*, so nothing in the premise pins it. Rather than guess a value,
forward saturation leaves `t` as a **universal metavariable** and stores a
*family* fact: not "P at some particular `t`" but the schematic "P at every
`t`", standing in for all of its instances at once.

The metavariable is filled in later, by a **join**. When some other fact —
or the goal — needs `P` at a specific value, it unifies against the family
and reads off exactly the matching instance; the meta is solved *at the
point of use*, not guessed up front. And because each layer of saturation
can join against the previous layer's families, forward chaining composes
buried witnesses that backward search would otherwise have to invent from
nothing. A forward rule that never joins anything is simply inert — it
wastes a little budget, it does not corrupt anything.

### `@auto backward` — open existential sub-goals

Reducing a goal to sub-goals is not what `@auto backward` adds — plain
`auto?` already does that for *any* rule: when the reference pool can't
discharge a hypothesis, the search tries to *prove* that hypothesis as a
sub-goal (this is the "`auto?` is `exact?` plus a hook" behavior from
earlier). That works as long as the goal determines all of the rule's
binders.

What `@auto backward` adds is the ability to apply a rule *even when the
goal doesn't determine all of the rule's binders*. The sharpest case is a
premise that names a **witness** appearing nowhere in the goal — the `t` in
existential introduction (below). More broadly, put it on the
**introduction / witness** rules that build a goal up from sub-goals:
existential introduction and instantiation (the genuine witness cases),
disjunction and conjunction introduction, and `@view`/`@recover` rules that
carry a witness.

**The unknown is an existential metavariable.** This is the mirror image of
the forward case. Where a forward rule leaves an undetermined binder as a
*universal* metavariable — a family standing for *every* instance, solved
later by whoever joins against it — a backward rule leaves it as an
**existential** metavariable: a witness hole standing for *some* value the
proof has yet to pin down. That ∀-vs-∃ split is exactly why forward suits
elimination rules (they emit universally-quantified families) and backward
suits introduction rules (they demand an existential witness).

Backward does a bit more than "leave the hole blank and guess", though.
Rather than solving the meta passively at use time the way a join does, it
actively tries to *determine* the witness, in descending order of
confidence:

1. **force it from the goal** — if the goal's context already contains the
   instance the rule needs, the witness is read off that member directly;
2. **read it back from the sub-proof** — otherwise, solve the premise
   sub-goal and recover the witness from the proof that closed it (this is
   what `@view`/`@recover` are for);
3. **invent it, last** — only for a witness *nothing* else determines, and
   only if the theory offers a pool of candidate variables (`@vars`) to
   draw from.

**Exactly what enrolling a rule `@auto backward` switches on.** To be
precise, the annotation gates four things, all in service of that
existential witness:

1. **Existential opening.** The rule may be applied with the binders the
   goal doesn't determine opened as existential metavariables — the only
   path that introduces one — which the commitment ladder above then
   solves.
2. **The `@vars` witness pool.** The theory's `@vars` dummies are prepared
   as invention candidates for step 3 of that ladder. (This setup happens
   at all only when the theory has at least one `@auto backward` rule.)
3. **Candidate ordering.** A backward (witness-deferring) rule is tried
   *after* the non-generating structural and eigenvariable rules, so a
   fresh eigenvariable is already in scope before a witness rule has to
   commit — which is precisely what lets step 1 of the ladder read a
   witness off an in-scope member.
4. **Witness-aware splitting.** When a context split leaves a witness
   binder open, or when several goal members compete to be a rule's
   principal, the backward path enumerates those choices.

Note the boundary in (4): plain context *splitting* — partitioning a
sequent context between a rule's premises — is *not* backward-gated;
`auto?` applies it to multiplicative rules whether or not they are `@auto
backward`. What backward adds is only the witness-aware refinement of it.

**Which rules — three cases.** The rule of thumb is *backward ⟺
introduction, forward ⟺ elimination*. Three rules from a natural-deduction
theory show why the boundary sits there.

*Good — an introduction rule.* Existential introduction is the textbook
backward rule:

```mm0
--| @auto backward
axiom ex_intro {x: nat} (g: ctx x) (t: nat x) (p: wff x):
  $ g ⊢ [x/t] p $ > $ g ⊢ ∃ x p $;
```

Goal `g ⊢ ∃ x p`. Nothing fixes the witness `t`, so backward opens it,
sets the sub-goal `g ⊢ [x/t] p`, and reads `t` back from whatever proof
closes it. Proving the child determines the parent — exactly the shape the
search wants.

*Bad — a multiplicative elimination rule.* Disjunction elimination is the
trap:

```mm0
-- (deliberately left unannotated)
axiom or_elim (g h k: ctx) (a b c: wff):
  $ g ⊢ a ∨ b $ > $ h , a ⊢ c $ > $ k , b ⊢ c $ > $ g , h , k ⊢ c $;
```

Read backward from a goal `… ⊢ c`, the disjunction `a ∨ b` appears *only*
in a premise — neither `a` nor `b` occurs in the conclusion. So the engine
would have to **invent** the cut formula out of nothing, and there are
unboundedly many candidates: a fan-out that drains the budget for no gain.
Leave rules like this concrete. The ordinary reference-discharge path
already uses them the useful way — when you *have* a disjunction on hand
and want to case-split on it. (`ax_mp` and `ex_elim` are the same story.)

*The exception — a safe elimination rule.* Ex-falso is an elimination rule
too, yet it is safe to run backward, and theories that lean on backward
search do annotate it:

```mm0
--| @auto backward
axiom bot_elim (g: ctx) (a: wff): $ g ⊢ ⊥ $ > $ g ⊢ a $;
```

Backward from `g ⊢ a` it just sets the sub-goal `g ⊢ ⊥`. Its single
premise is a *fixed, closed* formula — there is nothing to invent and
nothing to fan out over — so it is a clean narrowing, not an explosion.
`bot_elim` is the one elimination rule you can mark `@auto backward`.

The mirror mistake is `@auto forward` on an introduction rule: it just
manufactures family facts nothing will ever consume — inert, not harmful,
but wasted budget.

### `@auto eager [N]` — user-declared invertible rules

Some backward rules are **invertible**: their conclusion is provable *if
and only if* their premises are, so applying one backward is never a
guess — it is a "don't care" decomposition step, not a "don't know" choice
point. The one-sided sequent calculus is the model case: `⊢ (a → b), Δ`
holds exactly when `⊢ ¬a, b, Δ` does, so the `→`-introduction can fire
unconditionally. `@auto eager` lets a theory declare that discipline:

```mm0
--| @auto eager
axiom rim (d: ctx) (a b: wff):
  $ ⊢ (¬ a) , b , d $ > $ ⊢ (a → b) , d $;

--| @auto eager 2
axiom rand (d: ctx) (a b: wff):
  $ ⊢ a , d $ > $ ⊢ b , d $ > $ ⊢ (a ∧ b) , d $;
```

An eager rule (which is implicitly `@auto backward` too) gets three things:

1. **Scheduling.** Eager candidates are tried before all other enrolled
   rules, ordered by the optional priority `N` (1 = earliest, the
   default). The classic tableau discipline — close first, then
   non-branching rules, then branching ones, then witness rules — is
   spelled: closing rules unannotated (they already go first), the
   non-branching ladder `@auto eager`, the branching rules
   `@auto eager 2`, the witness rules plain `@auto backward`.
2. **Commitment (the cut).** Once an eager candidate has actually applied
   — matched the goal and reached its subgoals — the search does not fall
   back to non-eager rules at that node: invertibility means that if the
   decomposition fails, the goal fails. All *eager* alternatives (other
   matching formulas, other eager rules) are still tried.
3. **Depth exemption.** Eager applications don't consume the `max_depth`
   budget. A proof that is a tall deterministic decomposition ladder plus
   one real choice point costs one depth level, not fifteen — which is
   what lets such theories run at the default depth. Node, fuel, and
   global-tick budgets still apply, so a wrong annotation can waste time
   but can never diverge.

Because the engine cannot check invertibility, the keyword names the
*scheduling behavior you are requesting*, not a verified property — but
two guardrails keep a wrong annotation from costing proofs. Statically,
an eager rule must be **invertible-shaped**: every hypothesis binder has
to appear in the conclusion. A premise-only witness binder (an
existential-introduction `t`, a contraction rule like tait's `rex`) is
rejected at compile time — a depth-free self-feeding contraction would be
catastrophic. Dynamically, if the whole search misses cleanly with the
cut in force, the engine retries once with the cut disabled, so a
mis-declared non-invertible rule costs miss-side latency, never a proof.

### `@auto trigger PATTERN` — seed ground facts from the goal

Some proofs need a *leaf* fact that backward search can't reach from
nothing — classically, an axiom instance like `φ ⊢ φ` where `φ` is some
subformula of the goal. `@auto trigger` handles this. It applies only to
**hypothesis-free** rules (axiom-shaped), and it takes a pattern written
as a parenthesized prefix tree over term names, the rule's own binder
names, and `_` (wildcard):

```mm0
--| @auto trigger (hyp p)     -- for each `hyp p` in the goal, seed `p ⊢ p`
axiom ax: $ hyp p |- p $;

--| @auto trigger (im p _)    -- harvest every implication antecedent
axiom ...
```

As a last resort — after the ordinary search has otherwise come up empty —
the engine matches each trigger pattern against the *goal's* subterms and
mints a ground instance of the rule for every match. Those seeds become
extra references and the search runs once more. In effect the annotations
let the author enumerate the *analytic leaf set* of the theory — the
context members, implication antecedents, and disjuncts that its
elimination rules move around — so the search has the raw material it
needs. See `docs/design_notes/trigger_seeding.md` for guidance on what to
enumerate.

## A worked example

Given a Hilbert-style theory with `ax_id`, `ax_mp`, and friends, and a
goal you'd otherwise prove in a few steps, you can write:

```text
imp_refl
--------
l1: $ a -> a $ by auto?
```

Open the code action on `l1`, accept **"Replace auto? with …"**, and the
line becomes a concrete application (its exact form depends on the
theory), which then compiles and verifies normally. If instead you only
needed to combine two facts already proved above:

```text
l3: $ b $ by exact?      -- finds e.g.  ax_mp (a := $ a $, b := $ b $) [l1, l2]
```

## Budgets and determinism

- **`auto?` is bounded.** It runs under a work budget (roughly a few
  seconds of calibrated work) and an iterative-deepening depth limit, so
  it always terminates. A goal it can't crack within budget yields "no
  suggestion", not a hang. Very deep goals may approach the budget before
  giving up.
- **Results are deterministic.** The same goal, theory, and reference
  pool always produce the same suggestions in the same order — the search
  does not depend on wall-clock timing or randomness. This is what makes
  its output reproducible and testable.
- **It is not global proof search.** `auto?` searches locally from the
  goal and the facts in scope; it does not consult a global database of
  every theorem ever proved, and it does not backtrack across your
  hand-written proof structure. Its power comes from the reference pool
  you've built up and from the `@auto` rules the theory has enrolled.

## Where to go deeper

The search implementation and its internal design (the seed/generate
phases, ACUI context matching, the forward-saturation and open-generation
machinery, the work-budget calibration) are documented for maintainers in
`src/frontend/compiler/search/ARCHITECTURE.md`. This user-facing document
deliberately stops at the boundary of *how you use it*; that file picks up
where it leaves off.
