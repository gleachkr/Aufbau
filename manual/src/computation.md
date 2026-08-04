# Computation: conversion? and folding

`conversion?` searches for a proof by looking for a sequence of conversions 
(specially annotated rules that represent some kind of equality or equivalence) 
that connect the goal to an earlier line or hypothesis, or, when the goal is 
itself an equation, that connect its two sides. This search is by saturation 
(using an [egraph](https://en.wikipedia.org/wiki/E-graph)), essentially just 
exploring all conversion paths until a connection is found. In Chapter 3 we 
used conversion to evaluate a lambda term. This chapter explains the conversion 
process in more detail.

## What comes back

The clearest way to see what `conversion?` does is to read the proof output.
In the lambda calculus theory:

```aufbau-proof prelude=lam-base,lam-rules
lemma lift (a b: tm): $ a = b $ > $ S a = S b $
----
l1: $ S a = S b $ by conversion?
```

Accepting the suggestion replaces `l1` with three lines:

```
l1_1: $ S a = S b $ by suc_congr [#1]
l1_2: $ S a = S a $ by eq_refl
l1: $ S a = S b $ by eq_trans [l1_2, l1_1]
```

Everything is the vocabulary of the Equality chapter: the hypothesis rewrites 
`a` to `b` under `S` through a congruence rule, and reflexivity and 
transitivity restate the goal from the chain. The goal above is itself an 
equation, so once its two sides meet in the search space the chain between them 
is the proof. A goal of any other shape instead has to convert to a hypothesis 
or an earlier line, and the emitted chain ends with a transport along the 
sort's relation, citing that reference. So that's what `conversion?` needs from 
a theory: a `@relation` bundle for the goal's sort (with a transport rule for 
the reference-anchored form), and `@congr` coverage for the connectives a 
rewrite must pass through.

Any existing reference pool member (prior line or hypothesis) whose formula is 
`rel lhs rhs` for a registered relation acts as a ground rewrite between its 
two sides, no annotation needed, and the emitted chain cites it directly 
(`suc_congr [#1]` above). So a pool of local equations and a goal to normalize 
is already enough for `conversion?` to run as a congruence-closure prover.

## Enrolling rewrite schemas: `@conversion`

Theorems join the rewrite set with `@conversion`. They carry a direction token:

```mm0
--| @conversion ltr
axiom contract (a: wff): $ (a ∧ a) ↔ a $;
```

The token (either `ltr`, `rtl`, or `both`) says which side is matched when 
searching for the conversion chain. This helps with search efficiency: if you 
enroll `(a ∧ a) ↔ a` left to right, the search space is naturally bounded, but 
in the other direction it will tend to fruitlessly explore lots of `p ∧ p` 
instances derived from existing formulas.

Enrollment is checked at annotation time. The conclusion must be `rel lhs rhs` 
for the operand sort's registered relation, the rule must have no hypotheses, 
and the matched side must be a term application that binds every binder the 
built side uses. Rules with bound binders and dependency restrictions are
fine, the search is sensitive to whether the dependency constraints of 
conversion rules can be satisfied.

## Associativity and commutativity: role certificates

The two structural laws from associativity and commutativity get special 
treatment, again for efficiency. Instead of a direction, you annotate the law 
itself:

```aufbau-proof prelude=nd-base,fol-base
@@mm0
--| @conversion comm
axiom and_comm (a b: wff): $ a ∧ b ↔ b ∧ a $;
--| @conversion assoc
axiom and_assoc (a b c: wff): $ (a ∧ b) ∧ c ↔ a ∧ (b ∧ c) $;
@@auf
lemma shuffle (a b c: wff): $ _ ⊢ (a ∧ b) ∧ c $ > $ _ ⊢ c ∧ (b ∧ a) $
----
l1: $ _ ⊢ c ∧ (b ∧ a) $ by conversion?
```

An operator certified with both structural rules and `@congr` is treated as a 
multiset join, so terms with that operator as their head are treated as 
flattened to multisets, avoiding the search cost connected to permutation and 
reassociation of that term. An operator with only one of the two certificates 
enrolls for ordinary both-ways saturation instead.

This is related to but not the same as `@acui`. `@acui` drives the normalizer's 
canonical forms during ordinary line checking, while the conversion annotations 
drive the term representation during search. The natural deduction context 
carries both kinds of metadata for exactly that reason.

## Definitions

A `def` can enroll its own defining equation, with an orientation:

```aufbau-proof prelude=lam-base,lam-rules
@@mm0
--| @conversion unfold
def double (a: tm): tm = $ a + a $;
@@auf
lemma zero_double: $ double 0 = 0 $
----
l1: $ double 0 = 0 $ by conversion?
```

`unfold` expands applications of the head, `fold` matches the definiens
shape and folds it up, `both` does both; an unannotated def is invisible to
`conversion?`. Here saturation unfolds `double 0` to `0 + 0`, the addition
rules finish, and the emitted chain crosses the definition with a single
reflexivity line (the `$ double 0 = 0 + 0 $ by eq_refl`) which the checker
closes through ordinary transparent unfolding.

For a def with hidden dummy binders only `fold` is legal: unfolding would
have to invent a variable, which would complicate search significantly. The 
fold direction binds the dummy to a variable already present in the matched 
term.

## Computation rules: `@compute`

Saturation is the wrong engine for actual computation. A terminating,
confluent rule set like beta reduction or a digit-addition table reaches its
value directly; exploring every application order and regrouping on the way is 
exponentially more work than just applying the reductions. The `@compute` 
annotation, which the lambda calculus theory puts on `beta`, the substitution 
equations, and the addition table, excludes a rule from general saturation and 
hands it to a directed fold that builds a straight-line path in the search 
space:

```mm0
--| @compute ltr
axiom beta {x: tm} (e: tm x) (a: tm x): $ (λ x. e) · a = [x := a] e $;
```

Exactly one direction token names the redex side. The fold reduces each
node's first fresh match in declaration order and cascades through the
results, so declaration order is the reduction priority; for a confluent
set the order doesn't change the value, and general-purpose cleanup laws
(the zero laws of the addition table) go after the main table so real
redexes reduce before debris clears. There is no groundness requirement —
`conversion?` never instantiates the goal, so a theorem variable is just an
inert constant to the fold, and `0 + a` reduces by the zero law exactly as
`0 + S0` does. Each rule is saturated or folded, never both, and fold steps
are ordinary unions with ordinary justifications, so the emitted chains
look the same.

## Reading a miss

A failed `conversion?` says how it failed, which sometimes conveys useful 
information. This cell asks for a conversion that does not exist:

```aufbau-proof prelude=nd-base,fol-base
@@mm0
--| @conversion comm
axiom and_comm (a b: wff): $ a ∧ b ↔ b ∧ a $;
--| @conversion assoc
axiom and_assoc (a b c: wff): $ (a ∧ b) ∧ c ↔ a ∧ (b ∧ c) $;
@@auf
lemma off (a b c: wff): $ _ ⊢ (a ∧ b) ∧ c $ > $ _ ⊢ c ∧ (b ∧ b) $
----
l1: $ _ ⊢ c ∧ (b ∧ b) $ by conversion?
```

```
conversion? search failed: the egraph saturated (8 e-classes, 8 e-nodes,
1 iterations, 0 rule orientations, 0 local equations): no chain of the
enrolled @conversion rewrites connects this goal to any of the 1 pool
references.
```

A *saturated* miss is a forced negative: the search space reached a fixed 
point, so no chain of the enrolled rules exists at all. In this case, the fix 
(assuming your goal is correct) is enrolling more equations or citing a 
reference to convert toward, not retrying. A miss that ran out of iterations or 
nodes is inconclusive, and those bounds can be raised for the one call via e.g.
`conversion? (iters: 32, nodes: 20000)`, the same way `auto?` takes its 
parameters. The report hedges if the fixpoint itself was approximate. For 
example any `@compute` rules enrolled prevent the search failure from being 
conclusive: the fold is a strategy committed to one reduction order, not a 
closure over all of them.
