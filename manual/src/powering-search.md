# Powering search

[Proof search](proof-search.md) introduced `auto?` and `conversion?`. This
chapter describes the `@auto` annotations that control `auto?`. Every rule
is searchable without an annotation; annotations change how search uses
particular rules.

## What the search does on its own

Ordinary `auto?` applies rules whose conclusions match the goal, discharges
their hypotheses from the reference pool if possible, and recursively proves
the remaining unsolved hypotheses. The search solves rule binders by
*matching*. This handles many cases, including eliminations on premises
already in scope:

```aufbau-proof prelude=nd-base,nd-rules
lemma swap (a b: wff): $ _ ⊢ a ∧ b $ > $ _ ⊢ b ∧ a $
----
l1: $ _ ⊢ b ∧ a $ by auto?
```

The suggestion is `and_intro [and_elim_r [#1], and_elim_l [#1]]`.

- Matching `and_intro`'s conclusion against the goal leaves two sub-goals,
  `_ ⊢ b` and `_ ⊢ a`.
- Matching `and_elim_r`'s conclusion `g ⊢ b` against `_ ⊢ b` determines
  `g := _`. Its premise becomes `_ ⊢ ?t ∧ b`, where `?t` stands for the
  still-unknown conjunct `a`.
- `#1` concludes `_ ⊢ a ∧ b`: it fits the pattern, and matching determines
  `?t := a`.

A binder that matching does not determine, such as `?t` here, is a
*metavariable*: it stands for a still-unknown expression, and a later match
determines it.

### Witnesses as metavariables

Search applies ∃-introduction without any annotation, although the goal
does not determine its witness:

```mm0
axiom ex_intro {x: obj} (g: ctx) (t: obj x) (p: wff x):
  $ g ⊢ [x := t] p $ > $ g ⊢ ∃ x p $;
```

The witness `t` becomes a metavariable that the rest of the proof
determines. Several metavariables may coexist, and any still undetermined
after a proof is found receive witnesses from the `@vars` pool. The latter
case occurs when a witness is introduced and eliminated entirely within the
proof.

Metavariables may nest. Two `ex_intro` steps can occur on one path while
both metavariables remain open in the sub-goal pattern.

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
ex_intro [ex_intro (x := $ y $, p := $ P c ∧ Q y $) [and_intro [#1, #2]]]
```

Here's how we get there:

The outer `ex_intro` creates a metavariable `?s` and the subgoal `_ ⊢ ∃ y (P
?s ∧ Q y)`. The inner `ex_intro` creates another metavariable, `?t`, leaving
`_ ⊢ P ?s ∧ Q ?t`. Then `and_intro` splits the conjunction. Matching `#1`
determines `?s := c`, and matching `#2` determines `?t := d`. Search uses
these values to complete both `ex_intro` applications.

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
ex_intro [imp_intro [ax (g := $ _ $, a := $ P u $) []]]
```

The search created a metavariable `?t`, proved the tautology `P ?t → P ?t`,
and took the pool variable `u` as the witness for `?t`.

### Rules that leave a formula open

A metavariable for a formula, rather than a witness, is more constrained.
Consider

```mm0
axiom or_elim (g h i: ctx) (a b c: wff):
  $ g ⊢ a ∨ b $ > $ h , a ⊢ c $ > $ i , b ⊢ c $ > $ g , h , i ⊢ c $;
```

Any sequent goal can match `… ⊢ c`, but the goal does not determine `a` or
`b`. Search does not guess them: while a goal holds such a metavariable, only
a hypothesis, an axiom, or a rule whose conclusion determines it may prove
that goal. So `or_elim` splits on a disjunction already at hand. Only when
that search has run out of alternatives at every depth does search try once
more without this restriction.

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
term R (a: obj): wff; prefix R: $R$ prec 50;
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
axiom sb_R {x: obj} (t: obj x): $ [x := t] (R x) ↔ R t $;
--| @rewrite
axiom sb_imp {x: obj} (t: obj x) (p q: wff x):
  $ [x := t] (p → q) ↔ ([x := t] p → [x := t] q) $;

--| @auto forward
--| @view {x: obj} (t: obj x) (p: wff x) (q: wff): $ ∀ x p $ > $ q $
--| @recover t q p x
axiom all_elim {x: obj} (t: obj x) (p: wff x): $ ∀ x p $ > $ [x := t] p $;

--| @view {x: obj} (t: obj x) (p: wff x) (q: wff): $ q $ > $ ∃ x p $
--| @recover t q p x
axiom ex_intro {x: obj} (t: obj x) (p: wff x): $ [x := t] p $ > $ ∃ x p $;

--| @auto forward
axiom mp (a b: wff): $ a → b $ > $ a $ > $ b $;
@@auf
lemma anchor {x y: obj}:
  $ ∀ x (P x → Q x) $ > $ ∀ x (Q x → R x) $ > $ P c $ > $ ∃ y (R y) $
----
l1: $ ∃ y (R y) $ by auto?
```

The useful route to the existential goal is to derive `R c` from the two
universal facts and `P c`. Forward saturation finds that route: `all_elim`
turns `#1` into the family `P ?t → Q ?t`, and `mp` (enrolled forward, and
applied backward like every rule) joins the family with `P c`, instantiating
`t := c`. The derived `Q c` joins `#2`'s family the same way, giving `R c`,
which determines the metavariable introduced by backward `ex_intro`. Search
suggests:

```
ex_intro [mp (a := $ Q c $, b := $ R c $) [all_elim (t := $ c $) [#2], mp (a := $ P c $, b := $ Q c $) [all_elim (t := $ c $) [#1], #3]]]
```

If you delete the two `@auto forward` lines, the same search uses up its
work budget by depth 11, though the proof is only five applications deep.
Backward search reaches `mp` with two unresolved premises, `?a → R ?t` and
`?a`. These patterns do not constrain the search enough to find `t := c`. 
Forward search instead matches each derived implication family against a known 
fact, which determines the bindings.

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

An eager rule is tried before the other rules, in priority order. Priority 1 is the default and
runs first. One ordering comes before priority: a rule that splits the
context between its premises, eager or not, is tried after every rule
that does not.

Once an eager rule applies, search commits to it: if its premises cannot be
proved, search does not try non-eager alternatives at that node. Eager
applications do not count toward the search depth limit, so a long sequence
of these steps does not require a greater depth setting. So eager rules should 
generally be "invertible" rules that can safely be applied without producing 
unprovable goals.

The compiler cannot prove that a rule is invertible; the annotation is the
theory author's choice, and search trusts it. A rule marked eager that is
not invertible can make `auto?` miss proofs. The compiler does reject
`@auto eager` if a premise mentions a binder absent from the conclusion,
unless that binder is a fresh bound variable no other binder may depend on
(the eigenvariable of a `∀`-introduction), which the step does not choose.

## `@auto bridge`: close with a rule, never search through it

A structural rule such as weakening is cheap to close a goal with and
ruinous to search through. Applied backward, weakening must choose which
context members to forget, and every subset is a separate sub-search;
yet all it is needed for is bridging a fact stated for a smaller context
to a goal in a larger one.

```mm0
--| @auto bridge
axiom weak (g h: ctx) (a: wff): $ g ⊢ a $ > $ g , h ⊢ a $;
```

A bridge rule remains a backward candidate, but search fills its premises
only from the reference pool and from facts the forward pass derived; it
never generates a sub-proof for them. So `weak [#1]` still closes `Γ , q ⊢
p` from a hypothesis `Γ ⊢ p` wherever that sub-goal arises, while the
forgetting searches disappear. The annotation requires at least one
hypothesis. A proof that must forget a context member *before* applying a
rule with a bound binder (one that the member mentions) can no longer be
found through a bridge rule; such proofs are rare, and the bench shows
the trade.

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
