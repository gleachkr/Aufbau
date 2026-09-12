# Proof search

A **search placeholder** can replace a rule name and ask the language server to
find a justification:

```
l2: $ a ∧ b ⊢ b $ by exact?
```

The four placeholders serve different purposes: `exact?` closes a step from
available facts, `apply?` lists rules that could produce the goal, `auto?`
performs backward search, and `conversion?` looks for a chain of equalities
or equivalences.

## Example: search over natural deduction

`exact?` matches rule conclusions against a goal. `auto?` can also work
backward from that goal, treating a rule's premises as new goals to prove.

For this chapter, we switch to natural deduction. Each connective has
introduction rules that produce it and elimination rules that consume it.
Introduction rules often work well for backward search because the goal
determines their premises.

Here are the rules we will use. The sorts, notation, and rules that let us
treat contexts as unordered collections are already loaded. These shared
declarations form a *prelude*.

```aufbau-listing prelude=nd-rules
```

A sequent `g ⊢ a` says that `a` follows from the hypotheses in `g`. The
context is built with `,`, and an empty context is written `_`. A formula
standing alone is a one-element context. If you would rather not hunt for the
symbols, `->`, `/\`, `\/`, `~`, and `|-` are accepted as alternative notation
for `→`, `∧`, `∨`, `¬`, and `⊢`.

## Finishing a step: `exact?`

Place the text cursor on the `exact?` line below and wait a moment. Open the
lightbulb menu and choose **"Replace exact? with and_elim_r [l1]"**. The
editor replaces the placeholder with that justification.

```aufbau-proof prelude=nd-base,nd-rules
lemma and_comm (a b: wff): $ a ∧ b ⊢ b ∧ a $
----
l1: $ a ∧ b ⊢ a ∧ b $ by ax []
l2: $ a ∧ b ⊢ b $ by exact?
l3: $ a ∧ b ⊢ a $ by and_elim_l [l1]
l4: $ a ∧ b ⊢ b ∧ a $ by and_intro [l2, l3]
```

`exact?` looks for a *single* rule whose conclusion matches the goal and
whose hypotheses are supplied by available assertions: the lemma's own
hypotheses (`#1`, `#2`, …) and earlier proof lines. This collection is the
**reference pool**.

`apply?` lists rules whose conclusions match the goal, even if the reference
pool does not supply all their hypotheses.

## Finding a chain: `auto?`

`exact?` stops when no single rule proves the goal from the reference pool.
`auto?` goes further: if the pool cannot supply a hypothesis, it tries to
prove that hypothesis too. For example, it can find this entire proof:

```aufbau-proof prelude=nd-base,nd-rules
lemma and_comm_imp (a b: wff): $ _ ⊢ (a ∧ b) → (b ∧ a) $
----
l1: $ _ ⊢ (a ∧ b) → (b ∧ a) $ by auto?
```

The suggested justification uses nested inline applications:

```
imp_intro [and_intro [and_elim_r (a := $ a $) [ax []],
                      and_elim_l (b := $ b $) [ax []]]]
```

Working backward, `imp_intro` moves the antecedent into the context. `ax`
proves it from that context, the two elimination rules extract its
conjuncts, and `and_intro` combines them in the opposite order. These six
rule applications prove the goal without additional references. The explicit
bindings supply variables that inference cannot determine, as in the
previous chapter. If you would rather read the result as separate lines,
accept it and use the *unpack* action.

`auto?`'s search runs under a work budget and a depth limit, so it always
stops. Its results are deterministic — the same goal, theory, and pool always
produce the same suggestions in the same order.

## Placeholders in argument slots

`exact?`, `apply?`, and `auto?` can also appear in reference slots.
`conversion?` requires a whole proof line with a fully specified goal. For
example:

```aufbau-proof prelude=nd-base,nd-rules
lemma and_comm_slots (a b: wff): $ a ∧ b ⊢ b ∧ a $
----
l1: $ a ∧ b ⊢ a ∧ b $ by ax []
l2: $ a ∧ b ⊢ b ∧ a $ by and_intro [exact?, and_elim_l [l1]]
```

The compiler infers the slot's goal from the outer rule and the rest of the
line. Here `and_intro` needs proofs of `a ∧ b ⊢ b` and `a ∧ b ⊢ a`.
`and_elim_l [l1]` supplies the second; `exact?` searches for the first. Use
placeholders in reference slots to guide a search: specify the rule you want
and leave only the missing premises to search.

## Search failure diagnostics

When a search fails, the diagnostic explains why it stopped. **Exhausted**
means it finished exploring the candidates available to its search
strategies at the configured depth. It does not mean that the goal is
unprovable. Try a greater depth, add useful references, or adjust the
theory's search annotations. If search ran out of **budget** or **fuel**, it
stopped before finishing that exploration. The report also lists the
most-tried rules, which can reveal repeated unsuccessful attempts.

You can allow more search work on a single line by passing parameters to
that call:

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

`conversion?` looks for a rewrite chain from the goal to a member of the
reference pool or, for an equation, between its two sides. A theory can
register rules for general conversion or directed computation. General
conversion repeatedly applies rules to discover more equivalent expressions,
a process called *saturation*. Computation applies reductions in a fixed
order to simplify expressions.

Here is a small lambda calculus with explicit substitution and addition on
numerals. Beta reduction, the substitution equations, and the addition
table are enrolled as computation rules. The substitution equations carry a
second annotation, `@rewrite`, which lets the compiler apply them while
checking ordinary proof lines and avoids explicit substitution steps:

```aufbau-listing prelude=lam-rules
```

`·` is application, `[x := a] e` is substitution, and the numerals are
unary: `0`, `S0`, `SS0`. Substitution is not built into MM0: `[x := a] e` is
an ordinary term whose behavior is specified by the equations above. We can
now state a lemma in this theory.

```aufbau-proof prelude=lam-base,lam-rules
lemma add_two {x y: tm}: $ (λ x. λ y. (x + y)) · S0 · SS0 = SSS0 $
----
l1: $ (λ x. λ y. (x + y)) · S0 · SS0 = SSS0 $ by conversion?
```

The goal says that applying `(λ x. λ y. (x + y))` to `1` and `2` gives `3`.
`conversion?` applies β-reduction twice, carries out the substitutions
through `+`, and applies the addition rules. Both sides reduce to `SSS0`.

Rewriting respects variable dependencies: it does not apply a reduction that
would capture a variable. If search finds no connection, the diagnostic
explains why it stopped. Full saturation rules out a chain using the
registered conversion rules, not every possible proof of the goal. A search
stopped by a limit is inconclusive. Failure with computation rules is also
inconclusive because those rules follow only one reduction order.
