# Computation: conversion? and folding

`conversion?` searches for a proof that can be constructed from a chain of
equalities or equivalences. For a general goal, the chain must reach an
earlier line or hypothesis. For an equation, it may instead connect the
equation's two sides. The search stores expressions in an
[e-graph](https://en.wikipedia.org/wiki/E-graph), a data structure that
groups expressions known to be equivalent. It repeatedly applies rules to
find more equivalences, a process called *saturation*. This chapter explains
saturation and an alternative mode for directed computation.

## Reading the suggested proof

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

The proof uses the rules introduced in [Equality and
normalization](equality-and-normalization.md): the hypothesis rewrites `a`
to `b` under `S` through a congruence rule, and reflexivity and transitivity
restate the goal from the chain. The goal above is itself an equation, so
once its two sides meet in the search space the chain between them is the
proof. A goal of any other shape instead has to convert to a hypothesis or
an earlier line, and the emitted chain ends with a transport along the
sort's relation, citing that reference. The theory therefore needs the
relevant `@relation` bundle and a `@congr` rule for each constructor a
rewrite must pass through. Converting a goal to an existing reference also
requires transport for the goal's sort.

A reference of the form `rel lhs rhs`, for a registered relation, can
rewrite between its two sides without an annotation. The emitted proof cites
the reference directly, as in `suc_congr [#1]` above. With relation and
congruence rules in place, `conversion?` can therefore use local equations
even when no general conversion rules are registered.

## Enrolling rewrite schemas: `@conversion`

Theorems join the rewrite set with `@conversion`. They carry a direction token:

```mm0
--| @conversion ltr
axiom contract (a: wff): $ (a ∧ a) ↔ a $;
```

The direction is `ltr` (left to right), `rtl` (right to left), or `both`. It
controls which side search matches and which expressions it creates. For
example, applying `(a ∧ a) ↔ a` left to right removes duplication. More
generally, rules that expand expressions can make search explore many
unnecessary terms. Prefer simplifying directions where possible.

The compiler checks the annotation when it registers the rule. The
conclusion must be `rel lhs rhs` for the operand sort's registered relation.
The matched side must be a term application that determines every binder
used on the other side. Rules may have bound binders and dependency
restrictions; search checks those restrictions before applying them.

A rule may have hypotheses. For example, `a / a = 1` might require `a ≠ 0`.
Search applies such a rule only when the e-graph already establishes every
hypothesis. An equation is established when its sides belong to the same
equivalence class. Any other formula must be equivalent to a theorem
hypothesis or an earlier proof line.

Search retries a match on later iterations if its hypotheses are not yet
established. The matched side must determine every binder used in a
hypothesis.

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

With both annotations and a `@congr` rule, search treats nested applications
of the operator as a *multiset*: an unordered collection that keeps
duplicates. This avoids exploring each ordering and grouping separately.
With only one of the two annotations, search instead applies that law in
both directions during ordinary saturation.

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

`unfold` replaces the defined term with its body. `fold` matches the body
and replaces it with the defined term. `both` allows either direction. An
unannotated definition is not expanded or folded by `conversion?`. Here
saturation unfolds `double 0` to `0 + 0`, the addition rules finish, and the
emitted chain crosses the definition with a single reflexivity line (the `$
double 0 = 0 + 0 $ by eq_refl`) which the checker closes through ordinary
transparent unfolding.

For a def with hidden dummy binders only `fold` is legal: unfolding would
have to invent a variable, which would complicate search significantly. The
fold direction binds the dummy to a variable already present in the matched
term.

## Computation rules: `@compute`

For computation, applying reductions in a fixed order can be much cheaper
than exploring all application orders. `@compute` registers a rule for this
directed process, called *folding*, instead of general saturation. The
lambda-calculus theory uses it for `beta`, substitution equations, and
addition rules.

This works particularly well for terminating, confluent rule sets: reduction
stops, and the result does not depend on the order of steps. Untyped
β-reduction is not always terminating, so computation still needs search
limits. For example:

```mm0
--| @compute ltr
axiom beta {x: tm} (e: tm x) (a: tm x): $ (λ x. e) · a = [x := a] e $;
```

Choose one direction, `ltr` or `rtl`, to identify the expression to reduce,
called the *redex*. Folding tries rules in declaration order, applies the
first new match at each node, and continues reducing the results. Put
specific computation rules before general simplification rules.

Goals may contain theorem variables. `conversion?` leaves those variables
unchanged: for example, a zero law can reduce `0 + a` to `a` just as it
reduces `0 + S0` to `S0`.

A rule can be registered for saturation or computation, but not both. Both
modes record justifications in the e-graph and emit ordinary proof steps.

## Reading a miss

A failed `conversion?` says how it failed, which sometimes conveys useful
information. This cell asks for a conversion that does not exist; put the
cursor on the `conversion?` to run the search, and the report appears under
the placeholder:

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

A fully *saturated* search has reached a fixed point: its rules produce no
new equivalences. Failure then means that no chain of the registered
conversion rules connects the goal's sides or reaches a reference. It does
not establish that the goal is unprovable. Add relevant equations or a
useful reference if the search lacks a needed connection.

Failure caused by an iteration or node limit is inconclusive. Try raising
the limits for that call, for example with `conversion? (iters: 32, nodes:
20000)`.

The diagnostic also notes when saturation was approximate. In particular,
failure with `@compute` rules is inconclusive: computation follows one
reduction order rather than exploring every possible chain.
