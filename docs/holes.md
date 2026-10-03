# Proof holes

Holes let an Aufbau proof line omit a subexpression that the compiler can
recover from the cited rule, refs, and surrounding context. They are a
frontend elaboration aid: the trusted MMB verifier never sees a hole, and
neither does the checked theorem IR. Successful elaboration always emits an
ordinary fully-concrete proof.

## Mental model

A hole is a placeholder for **one concrete theorem-local subexpression**.
The user writes a registered token in place of that subtree, and the
compiler fills it from whatever the selected rule application produces.

```mm0
--| @hole _wff
provable sort wff;
axiom and_elim (a b: wff): $ a ∧ b $ > $ b $;

theorem t (p r s: wff): $ p ∧ (r ∨ s) $ > $ r ∨ s $;
```

```proof
t
-

l1: $ _wff $ by and_elim [#1]
```

The user writes `_wff` in place of `r ∨ s`. After matching `and_elim`
against the cited reference `p ∧ (r ∨ s)`, the compiler binds `b` to
`r ∨ s`, instantiates the conclusion, and fills `_wff` from that concrete
subtree.

The same idea covers more interesting cases:

- a witness that `@view` / `@recover` / `@abstract` extract from a
  normalized rule shape;
- a context expression (`_ctx`) on every line of a natural-deduction
  derivation, so the user does not have to retype the context;
- ordered fallback rule chains, where the first candidate to fully
  succeed is the one that fills the holes.

Holes themselves are *not* a proof-search facility. Each hole is
filled by one selected rule application, by reading the concrete subtree
that the application's binders force into that position. For inline rule
applications, a parent passes each child an expected-conclusion hint built
from the binders the line's visible parts determine, but there is still no
global backtracking across parent and child choices. To have a proof
*found* that fills the holes, write `auto?` as the line's justification
(see [Proof search](proof_search.md)).

---

## `@hole`

Holes are opt-in per sort. Attach a `@hole` annotation to a sort
declaration with exactly one raw math token after the tag:

```mm0
--| @hole _wff
provable sort wff;

--| @hole _ctx
sort ctx;
```

The token is any single raw math token that does not collide with
existing syntax. It does not have to be derived from the sort name —
`?` would be valid if it is otherwise unused.

A sort without `@hole` does not have a hole token. `_wff` and `_ctx`
remain ordinary math tokens unless explicitly registered.

### Validity rules

- exactly one token follows `@hole` (errors: `InvalidHoleAnnotation`);
- at most one `@hole` per sort (`DuplicateHoleAnnotation`);
- the token must not already be claimed by another sort
  (`DuplicateHoleToken`);
- the token must not collide with a `@vars` token, term name,
  notation token, or formula marker (`HoleTokenNameCollision`).

### Anonymous identity

Each occurrence of a hole token is a **fresh, independent hole**. So:

```proof
$ _wff -> _wff $
```

is two holes, not one shared hole. There is no way to write a named
or shared hole in v1.

---

## Where holes may appear

### Allowed

- proof-line assertions in `.auf` files;
- ordinary expression positions, including subexpressions under an
  object-language binder (e.g. `sb a x _wff`);
- whole-context positions on sorts that have ACUI metadata
  (e.g. `_ctx ⊢ A`).

### Rejected

- inside `.mm0` source — holes are a proof-side feature only;
- in bound-variable positions of a binder (e.g. `sb a _wff x` where
  the second argument is a bound variable);
- in refs (only the assertion may contain holes);
- in explicit binding formulas like `(name := $ _wff $)`.

A line whose holes can be filled in more than one non-structural way is
rejected as ambiguous. Structural ACUI contexts have a ranked preference
order described below.

---

## Elaboration

### Parse once, fill late

A holey assertion is parsed once into a surface `Expr` tree (the trusted
parser exposes a hole-aware entry point that admits registered hole
tokens). Hole identity belongs to the user's line, not to any one
candidate rule, so the same parsed surface expression is shared across
the entire `@fallback` chain.

The checked lines stay concrete: a holey surface expression never
reaches the checked IR until every hole has been filled, so the checked
IR and MMB emitter remain unchanged. A holey expression is interned only
as something to match against, with a line hole for each hole: the line
itself during inference, and an inline sub-proof's expected goal
(below), which is only a hint.

### Hole-free fast path is preserved

If the parsed assertion has no holes, the compiler keeps using the
existing pipeline unchanged — including strict unify replay where it
already applies. Hole-aware machinery activates only when the assertion
actually contains a hole.

### Candidate-local fill

For a holey line, every candidate (the named rule plus any
`@fallback` rules) goes through this loop:

1. match the candidate's hypotheses against the cited refs;
2. match the visible (non-hole) structure of the user's assertion
   against the candidate's conclusion template, using `@view`,
   `@recover`, `@abstract`, and automatic normalized comparison where
   needed. A rule variable facing a part with a hole takes nothing from
   it, but the value it gets elsewhere must fit that part's visible
   structure: `$ p , p -> q |- _wff -> q $ by ax []` takes `a := p -> q`,
   not the smaller split `a := p`;
3. instantiate the candidate's concrete conclusion;
4. compare that concrete conclusion against the holey surface
   assertion: every visible position must match (exactly or via
   transparent-def conversion); each hole position records the
   concrete subtree it covers;
5. each hole's recorded sort must match the concrete subtree's sort
   (`HoleSortMismatch`);
6. if any hole is unresolved or any constraint disagrees, reject
   the candidate.

The first candidate that fully succeeds wins. Its concrete conclusion
is what the rest of the checked-line pipeline sees, and holes are
gone from that point on.

### Inline sub-proofs

An inline sub-proof gets the part of the line its rule's premise
covers as its expected goal. When that part has a hole in it, or a
rule variable the holes leave open, the sub-proof still gets it, with
an anonymous meta hole in each such place:

```text
l1: $ (Q \/ P _obj) /\ P c $ by and_intro [or_r [pc []], pc []]
```

Here `or_r` expects `Q \/ P ‹hole›`, reads `a := Q` from the visible
part, and its own premise `pc` gives `b := P c`. The sub-proof solves
against the goal as against a holey line, with the structural solver: a
rule variable facing a part with a hole takes nothing from it, though
the value it gets elsewhere must fit that part's visible structure, and
the hole-free parts match as usual. Meta holes spend no dependency slot,
so a theorem can hold any number of holey lines. A hole the proof does
not determine still fails: `or_l [q []]` in place of `or_r [pc []]`
leaves `or_l`'s `b` open (`MissingBinderAssignment`).

A rule variable that occurs more than once in the line takes what every
occurrence shows. Under `both (a): $ a $ > $ a /\ a $`, the line
`$ (Q \/ _wff) /\ (_wff \/ P c) $` gives `a := Q \/ P c`. Parts under
an ACUI combiner are not combined, since their order is not fixed; the
first occurrence stands there, unless a later one has no hole.

The rest of the hint (the refs to the sub-proof's left, explicit
bindings, fallback to plain inference) works as on a line without holes;
see `docs/proof.md`, "Chained rule applications".

### Diagnostics surface for failed lines

When no candidate succeeds, the compiler raises one of:

- `HoleyInferenceMismatch` — the visible structure of the line
  could not be reconciled with any candidate's conclusion or
  hypotheses;
- `HoleConclusionMismatch` — visible structure agreed, but the
  candidate's instantiated conclusion does not actually fit the
  holey assertion;
- a hole-specific failure such as `HoleSortMismatch`, recovered with
  enough span information to point at the offending hole token.

`@fallback` diagnostics still walk every candidate, so a failure
report includes which rule was attempted and where filling failed.

---

## Interaction with view/recover/abstract

Holes do not change how `@view`, `@recover`, or `@abstract` work; they
just give the matcher fewer concrete starting positions. The user's
visible structure still drives the view match, the cited refs still
provide concrete witness data, and derived bindings still consume the
resolved view state.

The new piece is that some surface positions are deferred. When the
candidate's concrete conclusion is finally instantiated, the holes are
filled from whatever subtree sits at each hole position — including
witnesses that `@recover` extracted from refs or that `@abstract` rebuilt
as a one-hole context.

Worked example with `@recover`:

```mm0
--| @hole _obj
sort obj;

term rel (a: obj): wff;
term all {x: obj} (p: wff x): wff;
prefix all: $A.$ prec 41;

def hidden_rel {.a: obj}: wff = $ A. a (rel a) $;
axiom hidden_rel_ax: $ hidden_rel $;

--| @view {x: obj} (t: obj) (p: wff x) (q: wff): $ A. x p $ > $ q $
--| @recover t q p x
axiom pick_hidden (t: obj) (q: wff):
  $ hidden_rel $ > $ q $;
```

```proof
l1: $ rel _obj $ by pick_hidden (q := $ rel u $) [#1]
```

`@view`/`@recover` recover `t = u` from the explicit binding for `q`
and the hidden body of `hidden_rel`. The hole `_obj` is then filled
from the resulting concrete conclusion `rel u`.

---

## Interaction with automatic normalization

Holey surface expressions are **not** normalized directly. The compiler
can normalize the candidate's instantiated conclusion during final
validation. Hypothesis references may also be transported by normalized
conversion when the checker can prove the expected and actual forms
equivalent. The holey assertion is then compared against the concrete
result chosen for the line.

If the visible, non-hole part of the assertion is already in the form the
user wants to write, but a hole covers a normalized position such as an
ACUI context, the compiler may fill the hole from the raw candidate and
then let the ordinary normalized conclusion check validate the filled
line. This keeps the normalized proof line user-shaped while still
requiring the final checked line to be a concrete, verifier-justified
rule application.

This avoids inventing rewrite semantics for `.hole`, and it lines up
with user intent: a hole means "fill whatever subtree belongs here
once the rule has been elaborated", not "normalize a placeholder".

## Interaction with definitions

A holey line may keep a definition folded where the rule's conclusion has
it unfolded. With `def img (f B: set) {.y: set}: set = $ sep y B (R f y) $`
and a rule concluding `t e. sep x A p`, both of these check:

```proof
l1: $ _wff -> c e. img f B $ by sep_in_imp [#1]
l2: $ c e. B -> c e. img f _set $ by sep_in_imp [#1]
```

Hole-free parts of the line are matched with definition unfolding, as on
a concrete line. When that walk fails, the line's holes are interned as
wildcards and the rule is matched against the whole line by transparent
matching: a hole matches anything, and a rule variable facing a part with
a hole in it stays unbound, so the other parts and the cited premises must
fix it. The rule's bound `x` takes `img`'s hidden `y`, which gets a fresh
variable from the `@vars` pool. The holes are then filled through the
definition: `img`'s body is matched against the instantiated conclusion,
and each argument is filled from the value its variable took. The filled
line must equal the conclusion up to unfolding.

The other direction works too: a line may write out a definition the
rule's conclusion keeps folded, as in `$ c e. sep x _set (R f x) $` for a
rule concluding `t e. img f B`. The fill matches the definition's body,
with the conclusion's arguments, against the line to name its hidden
variable (`x`), then fills from the unfolded conclusion.

An inline sub-proof whose expected goal has a hole under a definition
(`mp [sep_in_imp [#1], #1]` on `$ c e. img f _set $`) gets the same
wildcard matching when the structural solver cannot use its goal.

Hover and the **Fill in the holes** action report the line as written,
with only its holes filled: the checked conclusion may have a definition
unfolded where the line keeps it folded.

One limit: a rule variable that faces only parts with holes stays open,
even when a `@recover` could read it back from a cited premise. With
`has_preimage f X y` defined as `∃ x (x ∈ X ∧ maps f x y)`,
`$ has_preimage f _set y $ by ex_intro [l1]` fails: `ex_intro`'s `p` meets
`x ∈ _set ∧ maps f x y`, so it stays unbound, and the `@recover` that
would find `t` from `l1` needs `p`. Writing the line out in full works.

---

## Interaction with ACUI contexts

Context holes such as `_ctx` are especially convenient for
natural-deduction-style systems where the context combiner is annotated
with `@acui`. Each line can omit the context entirely:

```proof
l1: $ _ctx ==> _ctx $ by pair_cut [#1, #2]
l2: $ _ctx ==> a , b $ by discharge [#1]
```

A hole can also stand for part of a context, and the visible members need
not come in the order the rule builds the context in. When the line does
not match by position, the hole takes the members the visible ones leave
over: the fewest, under idempotence, and the unit when none are left. With
`dup (g): $ ok g $ > $ ok2 g g $` and a premise `ok (A , B)`,

```proof
l1: $ ok2 (A , _ctx) (_ctx , A) $ by dup [ok_ab []]
```

checks, with each `_ctx` standing for `B`. Order is ignored only under a
commutative combiner. Without commutativity the visible members must be the
context's first and last ones, in order, and the hole takes the run between
them. This takes exactly one hole among a context's members. A context with two holes, or with a hole inside
a member such as `wk _ctx`, is filled by position only; when the line then
fails, the error says which hole is in the way.

ACUI matching can sometimes admit more than one valid context
binding — for example, both `g = ∅` and `g = P` may satisfy
`g ⊢ P → Q` when the cited ref is `P ⊢ Q`. The compiler does not
treat that as ambiguity. Instead the matcher applies a preference
order to the *rule binder* before filling the hole:

1. prefer a subset-minimal residual context;
2. break ties by smaller canonical context size;
3. if multiple equally preferred fills remain, pick the first stable
   solver result and emit an ambiguity warning.

So `_ctx` ordinarily resolves to the discharged context the user
expects (e.g. `∅` for `imp_intro`), and an explicit user-written
binder can still override the chosen residual.

The same structural solver can run when the visible hole is not itself a
context. A whole-line `_wff` may hide a conclusion whose rule has an
omitted ACUI context binder; in that case the solver uses the rule's
hypotheses and conclusion shape to recover the minimal residual context.

This preserves the principle that holes do not introduce new ACUI
search beyond what the matcher already does for the rule itself.

---

## Interaction with `@fallback`

Holey lines respect declared fallback order. The compiler:

- tries the named rule first, with hole filling as part of "did this
  candidate fully succeed";
- on failure rolls back and tries each fallback in turn;
- accepts the first candidate whose elaboration succeeds end-to-end,
  including hole filling.

There is no separate "best candidate" search. Fallback order matters
more for holey lines than for hole-free lines, which is the right
semantics for ordered rule families such as

```text
$ Δ , q ⊢ p $ > $ Δ ⊢ q → p $
$ Δ ⊢ p $     > $ Δ ⊢ q → p $
```

where the first rule should always win when it applies and the second
should fill the holes only when the first cannot.

---

## Interaction with `@fresh` and hidden witnesses

A hole is not an existential theorem variable. The compiler does **not**
allocate a fresh theorem-local dummy merely because a hole is present.
When holey matching has produced enough information to instantiate a
candidate, hidden-witness finalization uses the same dependency-aware
`@vars`-pool path used by ordinary advanced inference.

For a holey line, freshness is computed from the visible surface
assertion, the cited refs, explicit bindings, and any concrete data
collected during matching. The holes themselves do not contribute dummy
variables or dependencies.

If a hidden witness escape genuinely needs a theorem-local variable,
that allocation goes through the same `@vars`-pool path used by
`@fresh` and view escape. Holes never silently turn into fresh vars.

---

## Editor support

The language server reports what each hole was filled with on hover. On
a holey line it also offers a **Fill in the holes** code action, which
replaces the whole assertion with the line's checked conclusion. It
reprints the whole assertion rather than splicing each filling, so the
printer adds whatever parentheses the surrounding notation needs. The
action is not offered when the conclusion mentions a variable with no
source name, such as an anonymous dummy, since no text would parse back
to it. Both come from `HoleInferenceSink`, which the check memo records
and replays with the block.

---

## What never sees a hole

The trust boundary holds:

- checked lines are concrete; a holey line or hint enters the theorem DAG
  only as a match target, with a meta line hole (no dependency slot) per
  hole;
- `checked_ir.zig` and `compiler/emit.zig` reject any leftover
  surface placeholder, so a bug that lets a hole survive surfaces as a
  loud frontend error rather than as suspect MMB output;
- the trusted MMB verifier and MM0/MMB cross-checker are unchanged.

Holes are an elaboration aid that disappears at the boundary between
checked IR and proof emission.

---

## Limits and non-goals

This is the v1 surface. The following are deliberately out of scope:

- holes in `.mm0` source;
- a generic untyped `_`;
- holes in bound-variable positions or in explicit binding formulas;
- named or shared holes;
- proof search during elaboration beyond existing inference, view,
  normalization, and fallback machinery (`auto?` searches, but only
  when asked, and its suggestion then elaborates like any other line);
- theorem-local dummy creation triggered by a hole.

These restrictions keep holes a local, line-scoped elaboration step
that fits the existing frontend without changing trusted proof
emission.
