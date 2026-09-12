# Powering search

[Proof search](proof-search.md) introduced `auto?` and `conversion?`. This
chapter describes the `@auto` annotations that control `auto?`. Unannotated
rules remain searchable; annotations opt particular rules into additional,
more expensive strategies.

## What the search does on its own

Ordinary `auto?` applies rules whose conclusions match the goal, discharges
their hypotheses from the reference pool if possible, and recursively proves
the remaining unsolved hypotheses. The search solves rule binders by
*matching*. This handles many cases, including nested eliminations on premises
already in scope:

```aufbau-proof prelude=nd-base,nd-rules
lemma proj (a b c: wff): $ _ ⊢ a ∧ (b ∧ c) $ > $ _ ⊢ c $
----
l1: $ _ ⊢ c $ by auto?
```

The suggestion is `and_elim_r (a := $ b $) [and_elim_r [#1]]`.

- Matching `and_elim_r`'s conclusion `g ⊢ b` against the goal determines `g
  := _` and `b := c`. Its premise becomes `_ ⊢ ?t ∧ c`, where `?t` stands
  for the still-unknown conjunct `a`.
- The pattern becomes a sub-goal.
- The inner `and_elim_r`, applied to `#1`, concludes `_ ⊢ b ∧ c`: it fits
  the pattern, and matching determines `a := b`.

Ordinary search prefers applications whose bindings it can determine
immediately. If those candidates fail, it may leave a binder unresolved
while searching for a premise. A *metavariable*, such as `?t`, represents
that unknown expression. The annotations below control when search uses this
strategy.

## `@auto backward`: witnesses as metavariables

Ordinary search handles rules such as ∃-introduction poorly. The witness may
be determined several steps below the introduction, so search must carry it as
a metavariable. Because unannotated search defers that strategy, earlier
attempts may consume the work budget first. Mark rules that normally require
such witnesses with `@auto backward`:

```mm0
--| @auto backward
axiom ex_intro {x: obj} (g: ctx) (t: obj x) (p: wff x):
  $ g ⊢ [x := t] p $ > $ g ⊢ ∃ x p $;
```

For an annotated rule, metavariable propagation becomes an ordinary search
step rather than a last resort. Several metavariables may coexist, and any
still undetermined after a proof is found receive witnesses from the `@vars`
pool. The latter case occurs when a witness is introduced and eliminated
entirely within the proof.

### Scheduling

Search runs in phases that use increasingly expensive strategies. Each phase
searches for a proof sequentially at increasing depths, iteratively deepening 
the search space and caching partial results for future phases. For unannotated 
rules, introducing metavariables is a last resort, available only in a late 
phase.

`@auto backward` makes metavariable introduction available in earlier
phases. At each depth, search still tries cheaper candidates first:
unannotated rules, then annotated rules whose conclusions determine all
their binders, then annotated rules with unresolved binders.

### Nested deferrals

Backward searches with metavariables may nest. Two `@auto backward` rules can
occur on one path while both metavariables remain open in the sub-goal pattern.

```aufbau-proof prelude=nd-base,nd-rules,fol-base,fol-rules
@@mm0
term Q (t: obj): wff;
prefix Q: $Q$ prec 50;
--| @rewrite
axiom sb_Q {x: obj} (t: obj x): $ [x := t] (Q x) ↔ Q t $;
@@auf
lemma nest {x y c d: obj}: $ _ ⊢ P c $ > $ _ ⊢ Q d $ > $ _ ⊢ ∃ x ∃ y (P x ∧ Q y) $
----
l1: $ _ ⊢ ∃ x ∃ y (P x ∧ Q y) $ by auto?
```

The suggestion is

```
ex_intro (t := $ c $, p := $ E. y (P x /\ Q y) $)
  [ex_intro (x := $ y $, g := $ _ $, t := $ d $, p := $ P c /\ Q y $)
    [and_intro [#1, #2]]]
```

Here's how we get there:

The outer `ex_intro` creates a metavariable `?s` and the subgoal `_ ⊢ ∃ y (P
?s ∧ Q y)`. The inner `ex_intro` creates another metavariable, `?t`, leaving
`_ ⊢ P ?s ∧ Q ?t`. Then `and_intro` splits the conjunction. Matching `#1`
determines `?s := c`, and matching `#2` determines `?t := d`. Search uses
these values to complete both `ex_intro` applications.

Opening `?t` with `?s` unsolved required `@auto backward`. Without the
annotation the proof hits the search limit, trying rules other than `ex_intro`
for the inner search.

### Choosing an arbitrary witness

Sometimes the proof does not determine a witness because any variable will
do.

```aufbau-proof prelude=nd-base,nd-rules,fol-base,fol-rules
lemma wit {x: obj}: $ _ ⊢ ∃ x (P x → P x) $
----
l1: $ _ ⊢ ∃ x (P x → P x) $ by auto?
```

The suggestion is

```
ex_intro (t := $ u $, p := $ P x -> P x $) [imp_intro [ax []]]
```

The search created a metavariable `?t`, proved the tautology `P ?t → P ?t`, and
took the pool variable `u` as the witness for `?t`. Without the annotation, the
same search fails:

```
auto? search failed: no proof found within depth 6. The search space was
exhausted (25 applications validated: 0 accepted, 25 rejected), so only a
deeper proof can exist — try 'auto? (depth: 8)'. Most-tried rules: ax
(25 tried, 0 accepted).
```

Use `@auto backward` for **introduction and witness** rules that build a goal
from sub-goals while leaving part of a hypothesis undetermined. Existential
introduction and similar generalization rules with a `@view` are typical.

Using `@auto backward` on a rule that matches very broadly can be harmful,
especially if the conclusion of that rule leaves its premises undetermined.
Consider

```mm0
axiom or_elim (g h i: ctx) (a b c: wff):
  $ g ⊢ a ∨ b $ > $ h , a ⊢ c $ > $ i , b ⊢ c $ > $ g , h , i ⊢ c $;
```

Any sequent goal can match `… ⊢ c`, but the goal does not determine `a` or
`b`. Applying this rule backward can create three poorly constrained
subgoals. Exploring them may use the budget before search reaches rules
better suited to the goal.

## `@auto forward`: enrich the pool first

Use `@auto forward` for **elimination rules** and other rules that extract
simpler facts from known ones. Before backward search begins, the engine
repeatedly applies these rules to the reference pool and adds the derived
facts as extra references, subject to its search limits.

A forward rule need not determine its entire output. Applying ∀-elimination
to `∀ x p` produces an instance of `p`, but the premise does not determine
the substituted term `t`. Rather than guess, search records `?t` as a
*universal metavariable*: it represents a family of instances. Another rule
can combine this family with a known fact to determine the needed instance.
This matching operation is called a *join*.

A Hilbert-style quantifier theory shows how it works:

```aufbau-proof
@@mm0
delimiter $ ( ) [ ] $;
provable sort wff;
sort obj;

term imp (a b: wff): wff; infixr imp: $→$ prec 25;
term iff (a b: wff): wff; infixr iff: $↔$ prec 20;
term all {x: obj} (p: wff x): wff; prefix all: $∀$ prec 41;
term ex {x: obj} (p: wff x): wff; prefix ex: $∃$ prec 41;
term P (a: obj): wff; prefix P: $P$ prec 50;
term Q (a: obj): wff; prefix Q: $Q$ prec 50;
term c: obj;
term sb {x: obj} (t: obj x) (p: wff x): wff;
notation sb {x: obj} (t: obj x) (p: wff x): wff =
  ($[$:41) x ($:=$:0) t ($]$:0) p;

--| @relation wff iff iff_refl iff_trans iff_sym iff_mp
axiom iff_refl (a: wff): $ a ↔ a $;
axiom iff_trans (a b c: wff): $ a ↔ b $ > $ b ↔ c $ > $ a ↔ c $;
axiom iff_sym (a b: wff): $ a ↔ b $ > $ b ↔ a $;
axiom iff_mp (a b: wff): $ a ↔ b $ > $ a $ > $ b $;
--| @congr
axiom imp_congr (a b c d: wff): $ a ↔ b $ > $ c ↔ d $ > $ (a → c) ↔ (b → d) $;
--| @congr
axiom all_congr {x: obj} (p q: wff x): $ p ↔ q $ > $ ∀ x p ↔ ∀ x q $;
--| @congr
axiom ex_congr {x: obj} (p q: wff x): $ p ↔ q $ > $ ∃ x p ↔ ∃ x q $;

--| @rewrite
axiom sb_vac {x: obj} (t: obj x) (p: wff): $ [x := t] p ↔ p $;
--| @rewrite
axiom sb_P {x: obj} (t: obj x): $ [x := t] (P x) ↔ P t $;
--| @rewrite
axiom sb_Q {x: obj} (t: obj x): $ [x := t] (Q x) ↔ Q t $;
--| @rewrite
axiom sb_imp {x: obj} (t: obj x) (p q: wff x):
  $ [x := t] (p → q) ↔ ([x := t] p → [x := t] q) $;

--| @auto forward
--| @view {x: obj} (t: obj x) (p: wff x) (q: wff): $ ∀ x p $ > $ q $
--| @recover t q p x
axiom all_elim {x: obj} (t: obj x) (p: wff x): $ ∀ x p $ > $ [x := t] p $;

--| @auto backward
--| @view {x: obj} (t: obj x) (p: wff x) (q: wff): $ q $ > $ ∃ x p $
--| @recover t q p x
axiom ex_intro {x: obj} (t: obj x) (p: wff x): $ [x := t] p $ > $ ∃ x p $;

--| @auto forward
--| @auto backward
axiom mp (a b: wff): $ a → b $ > $ a $ > $ b $;
@@auf
lemma anchor {x y: obj}: $ ∀ x (P x → Q x) $ > $ P c $ > $ ∃ y (Q y) $
----
l1: $ ∃ y (Q y) $ by auto?
```

The useful route to the existential goal is to derive `Q c` from `∀ x (P x →
Q x)` and `P c`. Forward saturation can find that route: `all_elim` turns
`#1` into the family `P ?t → Q ?t`, and `mp` (enrolled forward as well as
backward) joins the family with `P c`, instantiating `t := c`. The derived
`Q c` determines the metavariable introduced by backward `ex_intro`. Search
suggests a three-step chain:

```
ex_intro [mp (a := $ P c $, b := $ Q c $)
             [all_elim (x := $ x $, t := $ c $, p := $ P x → Q x $) [#1], #2]]
```

If you delete the two `@auto forward` lines, the same search reports an
exhausted space at depth 6 even though the proof we're looking for is only
three applications deep. Backward search reaches `mp` with two unresolved
premises, `?a → Q ?t` and `?a`. These patterns do not constrain the search
enough to find `t := c`. Forward search instead matches the derived
implication family against the known fact `P c`, which determines the
bindings.

By contrast, `∀ x (P x) > ∃ y (P y)` needs no join: any instance proves the
goal. Backward search alone can prove it by choosing a witness from the
sort's `@vars` pool. Joins help when the proof needs a specific instance
determined by another fact in the pool.

`@auto forward` does not belong on most introduction rules, since backward
search uses them more effectively and indiscriminate application wastes
budget and introduces noise into the reference pool.

## `@auto eager`: invertible rules

Some rules are **invertible**: their conclusion is provable exactly when their
premises are. Applying such a rule backward loses no search-relevant
information, so doing it immediately avoids repeating the decomposition on
several branches. `@auto eager` declares this strategy for tableau and
sequent-style theories. For example, in a one-sided Tait calculus:

```mm0
--| @auto eager
axiom rim (d: ctx) (a b: wff):
  $ ⊢ (¬ a) , b , d $ > $ ⊢ (a → b) , d $;

--| @auto eager 2
axiom rand (d: ctx) (a b: wff):
  $ ⊢ a , d $ > $ ⊢ b , d $ > $ ⊢ (a ∧ b) , d $;
```

An eager rule also has the effect of `@auto backward`. It is tried before
other registered rules, in priority order. Priority 1 is the default and
runs first.

Once an eager rule applies, search commits to it: if its premises cannot be
proved, search does not try non-eager alternatives at that node. Eager
applications do not count toward the search depth limit, so a long sequence
of these steps does not require a greater depth setting. So eager rules should 
generally be "invertible" rules that can safely be applied without producing 
unprovable goals.

The compiler cannot prove that a rule is invertible; the annotation is the
theory author's choice. It does reject `@auto eager` if a premise mentions a
binder absent from the conclusion. If search fails without reaching its
budget, it also retries once without committing to eager rules. Priority
ordering and the depth exemption still apply on that retry.

## `@auto trigger`: seed leaf facts

Some proofs need a leaf fact backward search cannot easily discover, typically
an axiom instance like `p ⊢ p` for some subformula `p` of the goal. `@auto
trigger` applies to hypothesis-free rules and takes a pattern over term names,
the rule's binders, and `_`:

```mm0
--| @auto trigger (hyp a)
axiom ax (g: ctx) (a: wff): $ g , a ⊢ a $;
```

When search would otherwise fail, the engine matches each trigger pattern
against the goal's subterms. It creates a rule instance for each match and
retries with those facts in the reference pool. The pattern has to name
every binder of the rule except those that default to the unit of an `@acui`
combiner. `g` above defaults to the empty context, and the annotation is
rejected if a binder is unresolvable.
