# The Parts of a Proof Line

Proof lines look like this:
```
label: $ GOAL $ by rule (bindings) [references]
```
The label names the line. The goal, between `$` signs, is what the line
asserts. Everything after `by` is the justification for the line: the rule 
being applied, optional *bindings* in parentheses that pin down the rule's 
variables, and optional *references* in brackets that supply the rule's 
hypotheses.

We'll work in the Hilbert system from the last chapter, extended with the
distribution axiom `h2`:

```aufbau-proof doc=hilbert
@@mm0
delimiter $ ( ) $;
provable sort wff;
term imp (a b: wff): wff; infixr imp: $->$ prec 25;
axiom h1 (a b: wff): $ a -> (b -> a) $;
axiom h2 (a b c: wff):
  $ (a -> (b -> c)) -> ((a -> b) -> (a -> c)) $;
axiom mp (a b: wff): $ a $ > $ a -> b $ > $ b $;
```

## Three kinds of reference

A reference is a proof of one of the rule's hypotheses. References can be
supplied three ways:

- `#1`, `#2`, … indicate the hypotheses of the lemma or theorem being proved,
  in the order they were declared;
- a label like `l1` indicates an earlier line of the same proof;
- an **inline application** is a rule applied on the spot, inside the
  brackets, without a line of its own.

As a running example, here's the usual proof that `p -> p`, which needs 
instances of `h1`, an instance of `h2`, and two applications of `mp`.

```aufbau-proof doc=hilbert
lemma imp_refl (p: wff): $ p -> p $
----
l1: $ p -> ((p -> p) -> p) $ by h1
l2: $ p -> (p -> p) $ by h1
l3: $ (p -> ((p -> p) -> p)) -> ((p -> (p -> p)) -> (p -> p)) $ by h2
l4: $ (p -> (p -> p)) -> (p -> p) $ by mp [l1, l3]
l5: $ p -> p $ by mp [l2, l4]
```

It checks, but lines like `l3` are painful: you are transcribing an axiom
instance the compiler could have worked out itself.

## Inline applications

When a premise is a one-shot rule application, you can write it directly in
the reference list. For example:

```aufbau-proof doc=hilbert
lemma weaken_under (p q: wff): $ p $ > $ q -> p $
----
l1: $ q -> p $ by mp [#1, h1 []]
```

The second reference, `h1 []`, applies the axiom in place. The empty
brackets say it has no hypotheses of its own. A bare name in a reference list 
means a *line label*, so without the brackets `h1` would look for a line named 
`h1` rather than the axiom.

Inline applications can be nested, and mixed freely with the other reference
kinds. Here is `imp_refl` again, with the `h2` instance and the inner `mp`
folded into the final line:

```aufbau-proof doc=hilbert
lemma imp_refl_chained (p: wff): $ p -> p $
----
l1: $ p -> ((p -> p) -> p) $ by h1
l2: $ p -> (p -> p) $ by h1
l3: $ p -> p $ by mp [l2, mp [l1, h2 []]]
```

This lets us avoid the painful `l3` from the first version. 

## When chaining fails

So why not fold everything into one line? Try it — this cell is broken on
purpose:

```aufbau-proof
@@mm0
delimiter $ ( ) $;
provable sort wff;
term imp (a b: wff): wff; infixr imp: $->$ prec 25;
axiom h1 (a b: wff): $ a -> (b -> a) $;
axiom h2 (a b c: wff):
  $ (a -> (b -> c)) -> ((a -> b) -> (a -> c)) $;
axiom mp (a b: wff): $ a $ > $ a -> b $ > $ b $;
@@auf
lemma imp_refl_flat (p: wff): $ p -> p $
----
l1: $ p -> p $ by mp [h1 [], mp [h1 [], h2 []]]
```

The diagnostic says one of `h1`'s variables could not be determined. Aufbau can 
only infer what is forced by the goal and the references, and nothing here 
forces a choice of instance for the first `h1 []`.

If a variable cannot be determined, you can give the premise its own labeled
line, as in `imp_refl_chained` above, or state the instances yourself with
bindings, which work on inline applications the same way they work after
`by`. The one-liner does check with both `h1`s pinned down:

```
l1: $ p -> p $ by mp [h1 (a := $ p $, b := $ p $) [],
                      mp [h1 (a := $ p $, b := $ p -> p $) [], h2 []]]
```

## Packing and unpacking

Chains can be unpacked. Put your caret on the last line of `imp_refl_chained` 
and pause: the lightbulb offers an *unpack* action that rewrites the line as 
separate labeled lines, one per inline application, with each goal filled in 
from what the compiler checked. 
