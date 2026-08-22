# Your first proof

This chapter shows how proofs and theories work with a minimal theory 
containing *weakening* and *modus ponens* and a proof that applies these axioms 
to an assumed proposition.

## The theory

The theory sits in its own editable cell.

```aufbau-proof doc=hilbert
@@mm0
delimiter $ ( ) $;
provable sort wff;
term imp (a b: wff): wff; infixr imp: $->$ prec 25;
axiom h1 (a b: wff): $ a -> (b -> a) $;
axiom mp (a b: wff): $ a $ > $ a -> b $ > $ b $;
```

The first axiom is `h1`. It's a single proposition scheme that says any 
proposition of the form `a -> (b -> a)` is true. The second axiom is `mp`: 
given a proof of `a` and a proof of `a -> b`, you may conclude `b`. In a 
declaration, `>` separates hypotheses from what follows, so `mp` has two 
hypotheses and the conclusion `b`. The binder list `(a b: wff)` states the 
axiom for any two propositions.

## Using it

Now, a lemma. From a hypothesis `p`, we prove `q -> p`: first weaken with `h1`, 
then apply `mp`.

```aufbau-proof doc=hilbert
lemma weaken_under (p q: wff): $ p $ > $ q -> p $
----
l1: $ p -> (q -> p) $ by h1
l2: $ q -> p $ by mp [#1, l1]
```

Two kinds of reference appear on the last line. `#1` is the lemma's first
hypothesis, the incoming proof of `p`. `l1` is the previous line. The
brackets supply them to `mp` in the order its hypotheses were declared:
first the proof of `a`, then the proof of `a -> b`.

Applying `mp` here requires `a := p` and `b := q -> p`; applying `h1`
requires bindings for its `a` and `b` as well. The compiler infers them from
the formulas on the proof lines. Focus the cell and hover over a line to see
the inferred bindings.

## Spelling it out

You can make binding choices explicit with named bindings in parentheses. This
is the same lemma with nothing left to inference:

```aufbau-proof doc=hilbert
lemma weaken_explicit (p q: wff): $ p $ > $ q -> p $
----
l1: $ p -> (q -> p) $ by h1 (a := $ p $, b := $ q $)
l2: $ q -> p $ by mp (a := $ p $, b := $ q -> p $) [#1, l1]
```

Explicit bindings are rarely needed, but they are how you steer the
compiler when a rule's variables are not determined by the goal and
hypotheses.

Edits to the theory cell cause the proof cells to be checked again
immediately.
