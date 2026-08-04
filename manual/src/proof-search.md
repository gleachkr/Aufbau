# Proof Search

Aufbau can perform a few kinds of proof search. Where a rule name would go, you 
can write a **search placeholder** and ask the compiler to work out the line 
for you:

```
l2: $ a ∧ b ⊢ b $ by exact?
```

There are four placeholders: `exact?` finishes a step from facts you already 
have, `apply?` finds rules that might be applicable to the line being proved, 
`auto?` performs backwards search, and `conversion?` performs equational 
reasoning using egraph saturation. 

## Example: search over natural deduction

`auto?` and `exact?` work by matching rule conclusions against a goal and
chaining backwards. 

Some theories are better suited for this kind of reasoning than others. So, for 
our running example in this chapter, we switch to natural deduction, where 
every connective has its own introduction and elimination rules. Introduction 
rules typically work well for backwards search, because their conclusions 
usually entirely determine what their premises must be. Here are the rules for 
our natural deduction fragment. The sorts, notation, and the bookkeeping that 
makes a context an unordered collection are already loaded.

```aufbau-listing prelude=nd-rules
```

A sequent `g ⊢ a` says that `a` follows from the hypotheses in `g`. The
context is built with `,`, and an empty context is written `_`. A formula
standing alone is a one-element context. If you would rather not hunt for the
symbols, `->`, `/\`, `\/`, `~`, and `|-` are accepted as alternative notation 
for `→`, `∧`, `∨`, `¬`, and `⊢`.

## Finishing a step: `exact?`

Put the caret on the `exact?` line below and wait a moment. A lightbulb
should appear. Open it and you are offered **"Replace exact? with and_elim_r 
[l1]"**. Accept, and the placeholder will be replaced with this justification.

```aufbau-proof prelude=nd-base,nd-rules
lemma and_comm (a b: wff): $ a ∧ b ⊢ b ∧ a $
----
l1: $ a ∧ b ⊢ a ∧ b $ by ax []
l2: $ a ∧ b ⊢ b $ by exact?
l3: $ a ∧ b ⊢ a $ by and_elim_l [l1]
l4: $ a ∧ b ⊢ b ∧ a $ by and_intro [l2, l3]
```

`exact?` looks for a *single* rule whose conclusion matches the goal and
whose hypotheses are discharged by assertions already in scope, i.e. the 
lemma's own hypotheses (`#1`, `#2`, …) and the earlier lines. That collection 
is the **reference pool**.

`apply?` is similar but discovers which rules can be used to produce the goal, 
without narrowing to rules that already have their hypotheses available in the 
reference pool.

## Finding a chain: `auto?`

`exact?` gives up when no single rule closes the goal. `auto?` keeps
going: when nothing in the pool discharges a rule's hypothesis, it tries
to *prove that hypothesis too*, and so on. It can complete this proof from 
scratch for example:

```aufbau-proof prelude=nd-base,nd-rules
lemma and_comm_imp (a b: wff): $ _ ⊢ (a ∧ b) → (b ∧ a) $
----
l1: $ _ ⊢ (a ∧ b) → (b ∧ a) $ by auto?
```

The whole proof comes back as one line, nested inline:

```
imp_intro [and_intro [and_elim_r (a := $ a $) [ax []],
                      and_elim_l (b := $ b $) [ax []]]]
```

`imp_intro` moves the antecedent into the context, `ax` takes it back out,
the two `and_elim`s pull it apart, and `and_intro` reassembles it in the
other order — six rule applications, from a goal and nothing else. The
explicit bindings are there because nothing else pins those variables, as
in the last chapter. If you would rather read the result as separate
lines, accept it and use the *unpack* action.

`auto?`'s search runs under a work budget and a depth limit, so it always 
stops. Its results are deterministic — the same goal, theory, and pool always 
produce the same suggestions in the same order.

## Placeholders in argument slots

Placeholders can be used in argument slots. For example:

```aufbau-proof prelude=nd-base,nd-rules
lemma and_comm_slots (a b: wff): $ a ∧ b ⊢ b ∧ a $
----
l1: $ a ∧ b ⊢ a ∧ b $ by ax []
l2: $ a ∧ b ⊢ b ∧ a $ by and_intro [exact?, and_elim_l [l1]]
```

The slot's goal is worked out from the outer rule and the rest of the line. 
`and_intro` splits `b ∧ a` into `b` and `a`; `a` is supplied by `and_elim`, and 
the remaining goal `b` is then searched for exactly as a whole line would be.
Putting placeholders in argument slots makes it possible to steer a search in a 
certain direction: start with the rule you know is right and leave open only 
the part you don't want to write.

## Search failure diagnostics

When a search fails, the diagnostic gives some information about how. If the 
space was **exhausted**, the answer is definitive as far as it looked: no proof 
exists at the configured search depth, so either search deeper or enrich the 
pool. If it ran out of **budget** or **fuel**, the empty result is 
inconclusive. The report also lists the most-tried rules, which is how you spot 
a rule the search keeps attempting and rejecting.

You can spend more on a single hard line by passing parameters to that call:

```
l4: $ a → b , ¬ b ⊢ ¬ a $ by auto? (depth: 8, budget: 13)
```

| parameter | default | meaning |
|---|---|---|
| `depth` | 6 | how deeply generated steps may nest |
| `nodes` | 256 | distinct sub-goals per depth pass |
| `fuel` | 4096 | candidate validations per phase |
| `budget` | ≈6 | whole-call work cap, in units of about a second; `0` removes it |

## Computation as search: `conversion?`

`conversion?` attempts to determine whether the goal is equal to something 
already in the ref pool or to a reflexivity law through some chain of rewriting 
steps the theory has enrolled. Rules can be enrolled for conversion as either 
pure conversion rules, or as computation rules. Computation rules run eagerly, 
and handle cases where the rewrites are intended to rapidly derive a normal 
form. Conversion rules saturate (every enrolled direction is explored at once) 
and are intended for general equational search.

Here is a small lambda calculus with explicit substitution and addition on
numerals. Beta reduction, the substitution equations, and the addition
table are enrolled as computation rules. The substitution equations carry a
second annotation, `@rewrite`, which lets the compiler apply them on its own
when it checks an ordinary proof line, in order to eliminate a lot of 
boilerplate:

```aufbau-listing prelude=lam-rules
```

`·` is application, `[x := a] e` is substitution, and the numerals are
unary: `0`, `S0`, `SS0`. Note that substitution is not a meta-level
operation here — `[x := a] e` is an ordinary term, and the equations above
are what say how it distributes. Now a lemma in that theory.

```aufbau-proof prelude=lam-base,lam-rules
lemma add_two {x y: tm}: $ (λ x. λ y. (x + y)) · S0 · SS0 = SSS0 $
----
l1: $ (λ x. λ y. (x + y)) · S0 · SS0 = SSS0 $ by conversion?
```

The goal says that `(λx. λy. x + y) 1 2` is `3`. `conversion?` reduces the
two beta redexes, pushes the substitutions through `+`, runs the addition
table, and the two sides of the goal meet at `SSS0`.

Rewriting is dependency-aware, so in the theory above a reduction that would 
capture a variable simply never fires. If the search stops without connecting 
the goal to anything, the diagnostics say how it ended: a fully saturated 
search rules the goal out, while a miss under a budget (or one involving 
computation rules, whose fold commits to one reduction order) is inconclusive.
