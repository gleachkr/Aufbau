# Peano arithmetic

This chapter builds a small theory of first-order arithmetic, including 
classical propositional logic, equality and the successor axioms, quantifiers 
with explicit substitution, and induction, with the addition laws proved from 
the axioms. Unlike the sequent system of the previous chapter, this theory is 
in Hilbert style, so formulas are themselves the judgments and `wff` is the 
provable sort.

## The propositional skeleton

```aufbau-theory doc=peano
delimiter $ ( { ~ $  $ } ) , $;

strict provable sort wff;

term im (p q: wff): wff;
infixr im: $→$ prec 25;
infixr im: $->$ prec 25;

term not (p: wff): wff;
prefix not: $¬$ prec 41;
prefix not: $~$ prec 41;

axiom ax_1 (a b: wff): $ a → b → a $;
axiom ax_2 (a b c: wff): $ (a → b → c) → (a → b) → a → c $;
axiom ax_3 (a b: wff): $ (¬ a → ¬ b) → b → a $;
axiom ax_mp (a b: wff): $ a → b $ > $ a $ > $ b $;
```

This is the same Lukasiewicz system as the [Hilbert 
calculus](hilbert-calculus.md) chapter. 

Hilbert-style proofs lean constantly on a few small combinators, so we derive 
them once.

```aufbau-proof doc=peano
@@mm0
theorem a1i (a b: wff): $ b $ > $ a → b $;
theorem a2i (a b c: wff): $ a → b → c $ > $ (a → b) → a → c $;
theorem mpd (a b c: wff): $ a → b $ > $ a → b → c $ > $ a → c $;
theorem syl (a b c: wff): $ b → c $ > $ a → b $ > $ a → c $;
@@auf
a1i
---
l1: $ b → a → b $ by ax_1
l2: $ a → b $ by ax_mp [l1, #1]

a2i
---
l1: $ (a → b → c) → (a → b) → a → c $ by ax_2
l2: $ (a → b) → a → c $ by ax_mp [l1, #1]

mpd
---
l1: $ (a → b) → a → c $ by a2i [#2]
l2: $ a → c $ by ax_mp [l1, #1]

syl
---
l1: $ a → b → c $ by a1i [#1]
l2: $ a → c $ by mpd [#2, l1]
```

`a1i` weakens a theorem with an antecedent, and `syl` composes two 
implications.

## Numbers

```aufbau-theory doc=peano
--| @vars x y z
sort nat;

term d0: nat; prefix d0: $0$ prec max;
term suc (n: nat): nat;

term eq (a b: nat): wff; infixl eq: $=$ prec 50;

axiom peano1 (a: nat): $ ¬ suc a = 0 $;
axiom peano2 (a b: nat): $ suc a = suc b → a = b $;
axiom peano2r (a b: nat): $ a = b → suc a = suc b $;

axiom eq_refl (a: nat): $ a = a $;
axiom eq_sym (a b: nat): $ a = b → b = a $;
axiom eq_trans (a b c: nat): $ a = b → b = c → a = c $;
```

`peano1` says zero is not a successor and `peano2` says the successor is 
injective. `peano2r`, the converse of `peano2`, would ordinarily come from a 
congruence principle, but is simpler to just assert it here. Everything is 
stated with object-level implication rather than rule hypotheses, so applying 
an axiom generally takes an `ax_mp` step:

```aufbau-proof doc=peano
@@mm0
theorem suc_cancel (a b: nat):
  $ suc (suc a) = suc (suc b) $ > $ a = b $;
@@auf
suc_cancel
----------
l1: $ suc (suc a) = suc (suc b) → suc a = suc b $ by peano2
l2: $ suc a = suc b $ by ax_mp [l1, #1]
l3: $ suc a = suc b → a = b $ by peano2
l4: $ a = b $ by ax_mp [l3, l2]
```

## The equational layer

The  theory needs to say how equivalent formulas and equal terms may replace 
one another, in the format of the [Equality and 
normalization](equality-and-normalization.md) chapter:

```aufbau-theory doc=peano
term bi (a b: wff): wff;
infixl bi: $↔$ prec 20;
infixl bi: $<->$ prec 20;

--| @relation wff bi biid bitr bisym mpbi
axiom biid (a: wff): $ a ↔ a $;
axiom bitr (a b c: wff): $ a ↔ b $ > $ b ↔ c $ > $ a ↔ c $;
axiom bisym (a b: wff): $ a ↔ b $ > $ b ↔ a $;
axiom mpbi (a b: wff): $ a ↔ b $ > $ a $ > $ b $;

term nat_eq (a b: nat): wff;

--| @relation nat nat_eq nat_eq_refl nat_eq_trans nat_eq_sym _
axiom nat_eq_refl (a: nat): $ nat_eq a a $;
axiom nat_eq_trans (a b c: nat):
  $ nat_eq a b $ > $ nat_eq b c $ > $ nat_eq a c $;
axiom nat_eq_sym (a b: nat): $ nat_eq a b $ > $ nat_eq b a $;

--| @congr
axiom im_congr (a b c d: wff):
  $ a ↔ b $ > $ c ↔ d $ > $ (a → c) ↔ (b → d) $;
--| @congr
axiom not_congr (a b: wff):
  $ a ↔ b $ > $ ¬ a ↔ ¬ b $;
--| @congr
axiom eq_congr (a b c d: nat):
  $ nat_eq a b $ > $ nat_eq c d $ > $ (a = c) ↔ (b = d) $;
--| @congr
axiom suc_congr (a b: nat):
  $ nat_eq a b $ > $ nat_eq (suc a) (suc b) $;
```

A natural question: why introduce `nat_eq` when the theory already has `=`? 
A `@relation` bundle needs its members in rule form, and the equality axioms 
above are object-level implications — `eq_trans` is a formula about `→`, not 
a rule the normalizer can chain. Rather than derive rule-form counterparts, 
the theory keeps a separate judgment for the rewriting machinery; `eq_congr` 
connects it back to `=` formulas.

## Quantifiers

```aufbau-theory doc=peano
term all {x: nat} (p: wff x): wff;
prefix all: $∀$ prec 41;
prefix all: $A.$ prec 41;

--| @congr
axiom all_congr {x: nat} (p q: wff x):
  $ p ↔ q $ > $ ∀ x p ↔ ∀ x q $;

axiom ax_gen {x: nat} (p: wff x): $ p $ > $ ∀ x p $;
axiom ax_4 {x: nat} (p q: wff x):
  $ ∀ x (p → q) → ∀ x p → ∀ x q $;
axiom ax_5 {x: nat} (p: wff): $ p → ∀ x p $;
```

For quantifiers, we have generalization, distribution of `∀` over implication, 
and vacuous quantification (note that `ax_5`'s `p` does not depend on `x`). 
Generalization is the one rule-form member, since it must apply only to 
theorems, not hypotheses:

```aufbau-proof doc=peano
@@mm0
theorem gen_refl {x: nat}: $ ∀ x (x = x) $;
@@auf
gen_refl
--------
l1: $ x = x $ by eq_refl
l2: $ ∀ x (x = x) $ by ax_gen [l1]
```

## Substitution and instantiation

As in the last chapter, substitution is an ordinary term with `@rewrite` 
equations that push it through the syntax. Here it comes in two layers: 
`sb_f` substitutes in a formula and normalizes along `↔`, while `sb_t` 
substitutes in a number term and normalizes along `nat_eq`:

```aufbau-theory doc=peano
term sb_t {x: nat} (t: nat x) (a: nat x): nat;
term sb_f {x: nat} (t: nat x) (p: wff x): wff;

--| @rewrite
axiom sb_f_im {x: nat} (t: nat x) (p q: wff x):
  $ sb_f x t (p → q) ↔ (sb_f x t p → sb_f x t q) $;
--| @rewrite
axiom sb_f_not {x: nat} (t: nat x) (p: wff x):
  $ sb_f x t (¬ p) ↔ ¬ (sb_f x t p) $;
--| @rewrite
axiom sb_f_eq {x: nat} (t: nat x) (a b: nat x):
  $ sb_f x t (a = b) ↔ (sb_t x t a = sb_t x t b) $;
--| @rewrite
axiom sb_t_var {x: nat} (t: nat x): $ nat_eq (sb_t x t x) t $;
--| @rewrite
axiom sb_t_zer {x: nat} (t: nat x): $ nat_eq (sb_t x t 0) 0 $;
--| @rewrite
axiom sb_t_suc {x: nat} (t: nat x) (a: nat x):
  $ nat_eq (sb_t x t (suc a)) (suc (sb_t x t a)) $;
--| @rewrite
axiom sb_t_irrel {x: nat} (t: nat x) (a: nat):
  $ nat_eq (sb_t x t a) a $;

--| @view {x: nat} (t: nat x) (p: wff x) (q: wff): $ ∀ x p $ > $ q $
--| @recover t q p x
axiom ax_inst {x: nat} (t: nat x) (p: wff x):
  $ ∀ x p $ > $ sb_f x t p $;
```

`ax_inst` is instantiation. Its raw conclusion `sb_f x t p` is not intended to 
be user-facing syntax. Instead, the `@view` and `@recover` annotations (from 
[Views and recovery](views-and-recovery.md)) let a proof state the *normalized* 
instance, and let the compiler recover `t` and `p` from that shape:

```aufbau-proof doc=peano
@@mm0
theorem inst_suc_suc {x: nat}:
  $ ∀ x (suc x = suc x) $ > $ suc (suc 0) = suc (suc 0) $;
@@auf
inst_suc_suc
------------
l1: $ suc (suc 0) = suc (suc 0) $ by ax_inst [#1]
```

The rewrite rules push `sb_f` through `=`, then `sb_t` through `suc` and down 
to the variable, and the emitted proof carries the conversion.

## Addition and induction

```aufbau-theory doc=peano
term add (a b: nat): nat; infixl add: $+$ prec 60;

--| @congr
axiom add_congr (a b c d: nat):
  $ nat_eq a b $ > $ nat_eq c d $ > $ nat_eq (a + c) (b + d) $;
--| @rewrite
axiom sb_t_add {x: nat} (t: nat x) (a b: nat x):
  $ nat_eq (sb_t x t (a + b)) (sb_t x t a + sb_t x t b) $;

axiom add_0 (a: nat): $ a + 0 = a $;
axiom add_suc (a b: nat): $ a + suc b = suc (a + b) $;

--| @view {x: nat} (p: wff x) (base step: wff): $ base $ > $ ∀ x (p → step) $ > $ ∀ x p $
axiom peano5 {x: nat} (p: wff x):
  $ sb_f x 0 p $ >
  $ ∀ x (p → sb_f x (suc x) p) $ >
  $ ∀ x p $;
```

Addition is defined by recursion on the right argument. `peano5` is induction, 
stated with `sb_f` explicit in both hypotheses. The `@view` on the induction 
axiom uses two phantom binders, `base` and `step`, that absorb whatever the 
hypotheses normalize to: the user supplies the base case and inductive step in 
their already-substituted forms, and the rewrite rules reconcile them with the 
`sb_f` shapes.

The left identity law is a common first induction. Lines `l1`–`l7` build the 
base case and the generalized step, and `l8` closes:

```aufbau-proof doc=peano
@@mm0
theorem add_0_left {x: nat}: $ ∀ x (0 + x = x) $;
@@auf
add_0_left
----------
l1: $ 0 + 0 = 0 $ by add_0
l2: $ 0 + suc x = suc (0 + x) $ by add_suc
l3: $ 0 + suc x = suc (0 + x) → suc (0 + x) = suc x → 0 + suc x = suc x $ by eq_trans
l4: $ suc (0 + x) = suc x → 0 + suc x = suc x $ by ax_mp [l3, l2]
l5: $ 0 + x = x → suc (0 + x) = suc x $ by peano2r
l6: $ 0 + x = x → 0 + suc x = suc x $ by syl [l4, l5]
l7: $ ∀ x (0 + x = x → 0 + suc x = suc x) $ by ax_gen [l6]
l8: $ ∀ x (0 + x = x) $ by peano5 [l1, l7]
```

Note that the next theorem has no `{x: nat}` binder. The proof pulls `x` from 
the sort's `@vars` pool:

```aufbau-proof doc=peano
@@mm0
theorem add_0_left_inst (a: nat): $ 0 + a = a $;
@@auf
add_0_left_inst
---------------
l1: $ ∀ x (0 + x = x) $ by add_0_left
l2: $ 0 + a = a $ by ax_inst [l1]
```

## Two plus two

To close, here's a concrete computation: unfold with `add_suc` twice and 
`add_0` once, lifting through `suc` with `peano2r` at each stage:

```aufbau-proof doc=peano
@@mm0
theorem two_plus_two:
  $ suc (suc 0) + suc (suc 0) = suc (suc (suc (suc 0))) $;
@@auf
two_plus_two
------------
l1: $ suc (suc 0) + suc (suc 0) = suc (suc (suc 0) + suc 0) $ by add_suc
l2: $ suc (suc 0) + suc 0 = suc (suc (suc 0) + 0) $ by add_suc
l3: $ suc (suc 0) + 0 = suc (suc 0) $ by add_0
l4: $ suc (suc 0) + 0 = suc (suc 0) → suc (suc (suc 0) + 0) = suc (suc (suc 0)) $ by peano2r
l5: $ suc (suc (suc 0) + 0) = suc (suc (suc 0)) $ by ax_mp [l4, l3]
l6: $ suc (suc 0) + suc 0 = suc (suc (suc 0) + 0) → suc (suc (suc 0) + 0) = suc (suc (suc 0)) → suc (suc 0) + suc 0 = suc (suc (suc 0)) $ by eq_trans
l7: $ suc (suc (suc 0) + 0) = suc (suc (suc 0)) → suc (suc 0) + suc 0 = suc (suc (suc 0)) $ by ax_mp [l6, l2]
l8: $ suc (suc 0) + suc 0 = suc (suc (suc 0)) $ by ax_mp [l7, l5]
l9: $ suc (suc 0) + suc 0 = suc (suc (suc 0)) → suc (suc (suc 0) + suc 0) = suc (suc (suc (suc 0))) $ by peano2r
l10: $ suc (suc (suc 0) + suc 0) = suc (suc (suc (suc 0))) $ by ax_mp [l9, l8]
l11: $ suc (suc 0) + suc (suc 0) = suc (suc (suc 0) + suc 0) → suc (suc (suc 0) + suc 0) = suc (suc (suc (suc 0))) → suc (suc 0) + suc (suc 0) = suc (suc (suc (suc 0))) $ by eq_trans
l12: $ suc (suc (suc 0) + suc 0) = suc (suc (suc (suc 0))) → suc (suc 0) + suc (suc 0) = suc (suc (suc (suc 0))) $ by ax_mp [l11, l1]
l13: $ suc (suc 0) + suc (suc 0) = suc (suc (suc (suc 0))) $ by ax_mp [l12, l10]
```

That's a rather long proof (shorter than the Principia, but still). To avoid 
that kind of tedium, a theory that expects to compute can enroll its recursion 
equations as `@compute` rules and lets `conversion?` run them. The next chapter 
illustrates that pattern.

## The whole page

```aufbau-index doc=peano
```
