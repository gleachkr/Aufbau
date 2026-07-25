# Your first proof

Let's write a proof that actually uses a hypothesis. We stay in the same
fragment of propositional logic as the introduction — implication and the
weakening axiom — and add *modus ponens*.

## The theory

This time the theory sits in its own editable cell.

```aufbau-proof doc=hilbert
@@mm0
delimiter $ ( ) $;
provable sort wff;
term imp (a b: wff): wff; infixr imp: $->$ prec 25;
axiom h1 (a b: wff): $ a -> (b -> a) $;
axiom mp (a b: wff): $ a $ > $ a -> b $ > $ b $;
```

The new axiom is `mp`: given a proof of `a` and a proof of `a -> b`, you may
conclude `b`. In a declaration, `>` separates hypotheses from what follows,
so `mp` has two hypotheses and the conclusion `b`. The binder list
`(a b: wff)` states the axiom for any two propositions.

## Using it

Now a lemma in that theory. Because the cell below is marked as part of the
same document as the theory cell, it is checked against those axioms. From a 
hypothesis `p`, we prove `q -> p`: first weaken with `h1`, then apply `mp`.

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

Notice what you did *not* have to write. Applying `mp` here means choosing
`a := p` and `b := q -> p`, and applying `h1` means choosing its `a` and
`b` too. The compiler inferred those bindings from the formulas you stated.
Hover a proof line, once the cell has focus, to see exactly what was inferred.

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

From here you can keep going: add more axioms to the theory cell above and
the proof cells will re-check against them live.
