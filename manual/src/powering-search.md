# Powering search

Chapter 3 introduced search placeholders like `auto?` and `conversion?`. This 
chapter describes how `auto?` is controlled by `@auto` annotations. Search 
works without annotations; annotations enable additional, more expensive 
strategies.

## What the search does on its own

Ordinary `auto?` applies rules whose conclusions match the goal, discharges 
their hypotheses from the reference pool if possible, and recursively proves 
the remaining unsolved hypotheses. The binders in rule applications encountered 
during the search are solved by *matching*. That covers a lot, including nested 
eliminations on premises in scope:

```aufbau-proof prelude=nd-base,nd-rules
lemma proj (a b c: wff): $ _ ⊢ a ∧ (b ∧ c) $ > $ _ ⊢ c $
----
l1: $ _ ⊢ c $ by auto?
```

The suggestion is `and_elim_r (a := $ b $) [and_elim_r [#1]]`. 

- Backward from the goal, `and_elim_r`'s conclusion `g ⊢ b` pins the context `g 
  := _` and the wff `b := c`; the premise becomes the pattern `_ ⊢ ?t ∧ c`, 
  with the conjunct `a` undetermined, and `?t` an *existential metavariable* 
  that stands for the unknown `wff`. 
- The pattern becomes a sub-goal. 
- the inner `and_elim_r`, applied to `#1`, concludes `_ ⊢ b ∧ c`: it fits the 
  pattern, and the match pins `a := b`.

Ordinary search is primarily *concrete*. A binder need not be determined the 
instant its rule is applied (it can be carried into a sub-search as a 
metavariable) but only with some limitations (described below), and only as a 
late retry after the ordinary candidates have missed.

## `@auto backward`: witnesses as metavariables

The ordinary search policy handles a rule like ∃-introduction poorly, since 
that rule will usually involve generalizing on a term introduced several steps 
removed from the ∃-introduction application, which requires carrying a 
metavariable around during search. In an ordinary search, that only occurs as a 
last resort and sometimes not at all if earlier search attempts have already 
taken up most of the time budgeted for search. But it should be the normal 
case, not a last resort for ∃-introduction. This can be fixed by annotating the 
rule:

```mm0
--| @auto backward
axiom ex_intro {x: obj} (g: ctx) (t: obj x) (p: wff x):
  $ g ⊢ [x := t] p $ > $ g ⊢ ∃ x p $;
```

With this annotation, the handling of metavariables is made a bit more 
aggressive. Metavariable propagation is treated as a normal move, no longer a 
last resort, several metavariables are allowed to coexist in one search, and 
witnesses for underdetermined metavariables are drawn from the `@vars` pool as 
necessary. The last step is useful if a discovered proof actually fails to pin 
a witness to a particular value, for example if the witness is both introduced 
and eliminated internally to the proof.

### Scheduling

Ordinarily, search runs in several phases, each phase exploring the proof as 
deeply as it can with a different set of increasingly expensive strategies. 
Metavariable introduction only occurs in a late phase as a last resort. For an 
`@auto backward` rule, though, metavariable introduction is an ordinary move, 
and instead of being deferred by the phase structure, it's deferred only by 
ordinary rule scheduling within a phase at each depth. At each search depth 
(i.e. one rule application, two rule applications...), unannotated rules are 
tried first, then `@auto backward` rules whose conclusions determine all of 
their binders, and `@auto backward` rules with underdetermined binders last. So 
even with `@auto backward`, a metavariable is never created if there are 
cheaper approaches (at a given depth) remaining to explore.

### Nested deferrals

Backwards searches with metavariables can recursively nest: two `@auto 
backward` rules can be part of one backwards search path, each with its 
metavariable still open, and with both metavariables appearing in the sub-goal 
pattern.

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

- The outer `ex_intro` creates a metavariable `?s` and sets the sub-goal
`_ ⊢ ∃ y (P ?s ∧ Q y)`
- the inner one, applied to that pattern, creates a second `?t` and leaves `_ ⊢ 
  P ?s ∧ Q ?t`. 
- `and_intro` splits it, 
- `#1` pins `?s := c`, `#2` pins `?t := d`, and each value flows back up to the 
  rule that opened it. 

Opening `?t` with `?s` unsolved required `@auto backward`. Without the 
annotation the proof hits the search limit, trying rules other than `ex_intro` 
for the inner search. 

### Invention

Sometimes there is nothing to pin the witness: any instance will do.

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

`@auto backward` suits **introduction and witness** rules, and generally rules 
that build a goal from sub-goals and leave a part of a hypothesis undetermined: 
existential introduction, and similar generalization rules carrying a `@view`. 

Using `@auto backward` on a rule that matches very broadly can be harmful, 
especially if the conclusion of that rule leaves its premises undetermined.
Consider

```mm0
axiom or_elim (g h i: ctx) (a b c: wff):
  $ g ⊢ a ∨ b $ > $ h , a ⊢ c $ > $ i , b ⊢ c $ > $ g , h , i ⊢ c $;
```

Any concrete goal can match `… ⊢ c`, and `a, b` appear only in a premise. That 
potentially introduces three new goals with metavariables and very little 
discriminating structure, creating a fan-out that takes away time that would 
probably be better spent on rules that are actually indicated by the concrete 
goal you're trying to prove.

## `@auto forward`: enrich the pool first

`@auto forward` is the dual: put it on **elimination and destructor** rules, 
rules that consume facts and yield something smaller or more concrete.
Before backward search begins, the engine fires forward rules over the
reference pool, saturates, and adds everything derived as extra references.

A forward rule need not fully determine its own output. Fired forward on a pool
fact `∀ x p`, ∀-elimination produces an instance that depends on a `t` its
premise does not pin down. Forward saturation does not guess it: it records
`?t` as a universal metavariable, instantiated at the point of use, when 
another fact **joins** against the family and reads off the instance it needs. 
A Hilbert-style quantifier theory shows how this works:

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

Nothing concludes a `Q`-fact here, so the existential has exactly one route:
derive `Q c` from the universal and the anchor `P c`. Forward saturation
can find that route: `all_elim` turns `#1` into the family `P ?t → Q ?t`, and 
`mp` (enrolled forward as well as backward) joins the family with `P c`,
instantiating `t := c`. The derived `Q c` then pins the metavariable that 
backward `ex_intro` opened, and the suggestion comes back as a three-step 
chain:

```
ex_intro [mp (a := $ P c $, b := $ Q c $)
             [all_elim (x := $ x $, t := $ c $, p := $ P x → Q x $) [#1], #2]]
```

If you delete the two `@auto forward` lines, the same search reports an
exhausted space at depth 6 even though the proof we're looking for is only 
three applications deep. Backward, the route that uses `P c` runs through `mp` 
with both premises open: `?a → Q ?t` and a bare `?a`, which ends up too 
underdiscriminating to find `t := c`. Forward, the same step is a join of two 
concrete pool facts, and the match is forced.

Contrast a *free* witness: `∀ x (P x) > ∃ y (P y)` needs no join, because
any instance closes it. As a result backward search alone proves it, inventing 
the witness from the sort's `@vars` pool. A join is needed when a specific 
instance is needed and the evidence for the choice of instance exists in the 
reference pool.

`@auto forward` doesn't belong on most introduction rules, since backwards 
search can use those more effectively, and applying them blindly will waste 
budget and introduce noise into the reference pool.

## `@auto eager`: invertible rules

Some rules are **invertible**: the conclusion is provable exactly when the 
premises are, so applying the rule backward never loses search-relevant 
information. In this situation, it makes sense to apply the rule immediately so 
that you don't need to apply it several times on different search branches. 
`@auto eager` declares that strategy. This allows `@auto` to search efficiently 
over tableau and sequent-style theories. For example, in a one-sided Tait-style 
sequent calculus:

```mm0
--| @auto eager
axiom rim (d: ctx) (a b: wff):
  $ ⊢ (¬ a) , b , d $ > $ ⊢ (a → b) , d $;

--| @auto eager 2
axiom rand (d: ctx) (a b: wff):
  $ ⊢ a , d $ > $ ⊢ b , d $ > $ ⊢ (a ∧ b) , d $;
```

An eager rule (implicitly `@auto backward` as well) has three extra properties: 
it is *scheduled* ahead of all other enrolled rules, ordered by the optional
priority (1 is earliest and the default; the classic discipline puts the
non-branching rules at 1 and the branching ones at 2); once it has applied,
the search *commits*  (invertibility means that if the decomposition fails,
the goal fails, so non-eager alternatives are not retried at that node); and
its applications are *exempt from search depth limits*, so a tall deterministic
decomposition ladder costs one depth level rather than fifteen.

The compiler cannot check invertibility, so the invertible rules need to be 
annotated manually. The compiler does have two safety features though: a rule 
whose premises mention a binder its conclusion does not is rejected for `eager` 
outright, and if a search comes up empty without hitting its budget, it 
retries once with the commitment disabled (the scheduling and the depth 
exemption effects remain active).

## `@auto trigger`: seed leaf facts

Some proofs need a leaf fact backward search cannot easily discover, typically 
an axiom instance like `p ⊢ p` for some subformula `p` of the goal. `@auto 
trigger` applies to hypothesis-free rules and takes a pattern over term names, 
the rule's binders, and `_`:

```mm0
--| @auto trigger (hyp a)
axiom ax (g: ctx) (a: wff): $ g , a ⊢ a $;
```

When a search would otherwise come up empty, the engine matches each trigger 
pattern against the goal's subterms, mints an instance of the rule for every 
match, and retries with those seeds in the pool. The pattern has to name every 
binder of the rule except those that default to the unit of an `@acui` 
combiner. `g` above defaults to the empty context, and the annotation is 
rejected if a binder is unresolvable.
