# Holes

A proof line often contains subexpressions already determined by its rule,
references, and remaining text. A **hole** omits such a subexpression and asks
the compiler to recover it.

Holes are opt-in per sort. A `@hole` annotation on a sort declaration registers
one token for it:

```mm0
--| @hole _wff
sort wff;
--| @hole _ctx
sort ctx;
```

The natural deduction theory from the last chapter includes both of these
annotations. So `_wff` stands for an omitted formula and `_ctx` for an omitted
context. Contexts are the tedious part of a natural deduction proof; you can
use holes to mostly leave them out.

```aufbau-proof prelude=nd-base,nd-rules
lemma dm1 (a b: wff): $ ¬ a ∧ ¬ b ⊢ ¬ (a ∨ b) $
----
l1: $ ¬ a ∧ ¬ b ⊢ ¬ a ∧ ¬ b $ by ax []
l2: $ _ctx ⊢ _wff $ by and_elim_l [l1]
l3: $ _ctx ⊢ ¬ b $ by and_elim_r [l1]
l4: $ a ∨ b ⊢ a ∨ b $ by ax []
l5: $ a ⊢ a $ by ax []
l6: $ _ctx ⊢ ⊥ $ by not_elim [l2, l5]
l7: $ b ⊢ b $ by ax []
l8: $ _ctx ⊢ ⊥ $ by not_elim [l3, l7]
l9: $ _ctx ⊢ ⊥ $ by or_elim [l4, l6, l8]
l10: $ _ctx ⊢ ¬ (a ∨ b) $ by not_intro [l9]
```

Each hole is filled from the rule application on its own line. `and_elim_l`
carries the context of `l1` down to `l2`, `not_elim` joins the contexts of its
two premises, and `or_elim` joins three contexts. You can hover a hole to see
what it was filled with: the `_ctx` on `l9` should become `a ∨ b , ¬ a ∧ ¬ b ,
¬ a ∧ ¬ b`.

Line `l2` shows that a line may have more than one hole, and that holes are not
restricted to contexts. Each occurrence of a hole token is a separate hole, so
`$ _wff → _wff $` indicates two holes rather than one used twice; there is no
way to require that two positions be filled the same way.

When the rule and the references do not determine what belongs in a hole, the
line fails:

```
l1: $ _ctx ⊢ _wff $ by ax []
```

`ax` concludes `g , a ⊢ a`, and with nothing cited there is nothing to fix `g`.
The diagnostic reports the undetermined variable, exactly as it would for a line
whose bindings could not be inferred for any other reason.

Holes are only allowed in the assertion of a proof line. They are rejected in
`.mm0` files, in reference lists, in explicit bindings, and in the
bound-variable position of a binder.

## Chains of equations

Holes are useful for equational reasoning. A chain of `eq_trans` steps, for
example, keeps its left-hand side fixed. A hole avoids repeating that side on
every line.

Here is the lambda calculus of the last chapter, with the goal `conversion?`
was asked to prove there, done by hand. `beta` and `add_s` are rules listed in
that chapter; `eq_trans` and the congruence rules that lift an equality into a
surrounding term come from the theory's equality bundle.

```aufbau-proof prelude=lam-base,lam-rules
lemma add_two {x y: tm}: $ (λ x. λ y. (x + y)) · S0 · SS0 = SSS0 $
----
s1: $ (λ x. λ y. (x + y)) · S0 = (λ y. (S0 + y)) $ by beta
s2: $ (λ y. (S0 + y)) · SS0 = S0 + SS0 $ by beta
s3: $ S0 + SS0 = S (0 + SS0) $ by add_s
s4: $ S (0 + SS0) = SSS0 $ by suc_congr [add_z []]

r1: $ SS0 = SS0 $ by eq_refl
c1: $ _tm = (λ y. (S0 + y)) · SS0 $ by app_congr [s1, r1]
c2: $ _tm = S0 + SS0 $ by eq_trans [c1, s2]
c3: $ _tm = S (0 + SS0) $ by eq_trans [c2, s3]
c4: $ _tm = SSS0 $ by eq_trans [c3, s4]
```

The `s` lines prove individual equalities. The last four chain them together,
with each line extending by one step and stating only the new right-hand side.
Every `_tm` is the goal's left-hand side, `(λ x. λ y. (x + y)) · S0 · SS0`,
which `eq_trans` recovers from the chain so far.

Substitution stays out of the proof entirely, although `beta` produces it:
`s1` cites a rule concluding `[x := S0] (λ y. (x + y))` but states the result
of carrying that substitution out. The substitution equations are registered as
rewrites, so the compiler applies them itself when it checks the line against
the rule.

This resembles a `calc` block in a proof assistant like Lean, but requires no
separate construct: these are ordinary proof lines using the same holes as the
context example above.
