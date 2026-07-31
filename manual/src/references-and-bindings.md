# References and bindings

Everything after `by` in a proof line is a rule application:

```
rule (bindings) [references]
```

The references supply proofs of the cited rule's hypotheses, and the bindings
instantiate its variables. This chapter describes both references and bindings, 
ending with inline applications — rule applications used as references.

## The reference list

The brackets hold one reference per hypothesis of the cited rule, in the order
the rule declares its hypotheses; a mismatched count is an error. Each
reference is either:

- a *hypothesis reference* `#n` or `#name`, citing a hypothesis of the theorem
  or lemma being proved;
- a *line reference*, a bare label citing an earlier line of the same block; or
- an *inline application*, a rule applied on the spot (described below).

A bare identifier is always read as a line reference, even when a rule has the
same name. Writing `h1` in a block with no line labeled `h1` reports an unknown
label; applying the axiom in place requires the inline-application syntax, at
minimum `h1 []`.

Labels are local to their block, you cannot refer to a line that is part of 
another proof block.

## Hypothesis references

Hypotheses are numbered `#1`, `#2`, … in the order they appear in the
theorem's header. A hypothesis declared as a named binder may also be cited by 
name.

```aufbau-proof doc=refs
@@mm0
delimiter $ ( ) $;
provable sort wff;
term imp (a b: wff): wff; infixr imp: $->$ prec 25;
axiom h1 (a b: wff): $ a -> (b -> a) $;
axiom mp (a b: wff): $ a $ > $ a -> b $ > $ b $;
theorem chain (a b c: wff) (hab: $ a -> b $) (hbc: $ b -> c $): $ a $ > $ c $;
@@auf
chain
----
l1: $ b $ by mp [#3, #hab]
l2: $ c $ by mp [l1, #hbc]
```

`#hab` and `#hbc` cite the two named hypotheses; `#1` and `#2` would be another 
way of referring to those hypotheses. The arrow-form hypothesis `$ a $` has no 
name and can only be cited as `#3`. A `#` name that matches no hypothesis 
binder is an error.

## Bindings

A binding assigns an expression to one of the cited rule's binders:

```
(name := $ expr $, ...)
```

Each name must be a binder of the rule, and each expression is written like
any other math string, using the variables of the current block. The order of
the bindings does not matter, but assigning the same binder twice or naming a
binder the rule does not have is an error.

```aufbau-proof doc=refs
lemma weaken (p q: wff): $ p $ > $ q -> p $
----
l1: $ p -> (q -> p) $ by h1 (b := $ q $, a := $ p $)
l2: $ q -> p $ by mp [#1, l1]
```

Bound binders are assigned the same way, but a `{x}` binder stands for a
variable, so it must be given a bare variable, not a compound expression.

```aufbau-proof doc=quant
@@mm0
delimiter $ ( ) $;
sort tm;
provable sort wff;
term all {x: tm} (p: wff x): wff;
term eq (a b: tm): wff;
axiom eq_refl (a: tm): $ eq a a $;
axiom gen {x: tm} (p: wff x): $ p $ > $ all x p $;
theorem all_refl {y: tm}: $ all y (eq y y) $;
@@auf
all_refl
----
l1: $ eq y y $ by eq_refl
l2: $ all y (eq y y) $ by gen (x := $ y $, p := $ eq y y $) [l1]
```

Instantiations remain subject to the dependency restrictions of Chapter 6,
enforced by occurrence as usual.

## Omitted bindings

Bindings are usually omitted. The compiler infers each missing binder by
matching the stated goal against the rule's conclusion and the references
against the rule's hypotheses. Both proofs above check with their binding
lists deleted, so you can hover a line once its cell checks to see what was 
inferred.

When the goal is written out and every reference is a hypothesis or an earlier
line, the match is against fully concrete formulas and ordinarily determines
every variable the rule mentions. Undetermined binders arise mainly with
inline applications, whose goals are not explicitly written down.

## Inline applications

A reference may itself be a rule application, written with the same syntax
that follows `by`. It behaves like an anonymous proof line inserted just
before the line that uses it: the rule is applied, and its conclusion becomes
the reference expression. The hidden line has no label and cannot be cited
later; a result needed more than once should get a labeled line of its own.

Because a bare identifier is always a line reference, an inline application
must carry a reference list or a binding list. A rule with no hypotheses is 
applied as `h1 []`; when a binding list is present, an empty reference list may 
be dropped.

```aufbau-proof doc=refs
lemma weaken_inline (p q: wff): $ p $ > $ q -> p $
----
l1: $ q -> p $ by mp [#1, h1 []]
```

This is `weaken` from above with the `h1` instance applied in place. Inline
applications nest, and mix freely with the other reference kinds.

An inline application has no written goal, so the compiler must infer its
entire conclusion. It is handed the hypothesis it is expected to prove,
computed from everything else the enclosing application knows: the stated
goal, any explicit bindings, and the other references. In `weaken_inline`,
the goal and `#1` fix both variables of `mp`, so `h1` is asked to prove
`p -> (q -> p)` and its own variables are forced.

The expected conclusion need not be complete. A variable of the enclosing
rule that is still unknown is left open in the hint, to be settled by the
inline application's own conclusion or by another reference — including one
further to the right. What is required is that every variable be determined
by *something* in the line. When one is not the line is rejected, and the fix 
is a binding list on the inline application itself:

```aufbau-proof doc=refs
lemma weaken_pinned (p q: wff): $ p $ > $ q -> p $
----
l1: $ q -> p $ by mp [#1, h1 (a := $ p $, b := $ q $)]
```

Each inline application must elaborate to a single concrete hidden line before 
the enclosing application can finish. The inline application mechanism does not 
attempt multiple disambiguations if it cannot resolve a binder.

The unpack action of Chapter 2 is the inverse of this notation: it rewrites a
line into separate labeled lines, one per inline application, with each new
goal filled in from the checked conclusion.
