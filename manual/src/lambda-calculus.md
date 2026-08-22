# The lambda calculus

This chapter builds an equational theory of the untyped lambda calculus with
unary numerals. It extends the theory used in evaluation examples
during the [Proof search](proof-search.md) and [Computation](computation.md)
chapters. We end with the characteristic equation of the Y combinator.

## Syntax

```aufbau-theory doc=lam
delimiter $ ( ) [ ] . S $;
provable sort wff;
--| @hole _tm
--| @vars u v w
sort tm;

term iff (a b: wff): wff;
term eq (a b: tm): wff;
infixl eq: $=$ prec 20;

term lam {x: tm} (e: tm x): tm;
notation lam {x: tm} (e: tm x): tm = ($λ$:41) x ($.$:0) e;
term app (f a: tm): tm;
infixl app: $·$ prec 60;
term sb {x: tm} (e: tm x) (a: tm): tm;
notation sb {x: tm} (e: tm x) (a: tm): tm = ($[$:41) x ($:=$:0) a ($]$:0) e;

term zero: tm; notation zero: tm = ($0$:max);
term suc (n: tm): tm; prefix suc: $S$ prec 70;
term add (m n: tm): tm; infixl add: $+$ prec 30;
```

We have one syntactic sort of terms, with a `@vars` pool so proofs can invent
variables on demand. Abstractions are `λ x. e`, applications are `f · a`, and
explicit substitution is `[x := a] e`, governed by the reduction rules below.
The numerals are unary (`0`, `S0`, `SS0`, with `S` in the delimiter set so the
compact form parses), and `+` is their addition.

## The equational layer

The only judgments are term equations `a = b` and their `iff` equivalences,
bundled as in the [Equality and normalization](equality-and-normalization.md)
chapter:

```aufbau-theory doc=lam
--| @relation wff iff iff_refl iff_trans iff_symm mpbi
axiom iff_refl (a: wff): $ iff a a $;
axiom iff_trans (a b c: wff) (h1: $ iff a b $) (h2: $ iff b c $): $ iff a c $;
axiom iff_symm (a b: wff) (h: $ iff a b $): $ iff b a $;
axiom mpbi (a b: wff) (h1: $ iff a b $) (h2: $ a $): $ b $;
--| @relation tm eq eq_refl eq_trans eq_symm _
axiom eq_refl (a: tm): $ a = a $;
axiom eq_trans (a b c: tm) (h1: $ a = b $) (h2: $ b = c $): $ a = c $;
axiom eq_symm (a b: tm) (h: $ a = b $): $ b = a $;
--| @congr
axiom eq_congr (a b c d: tm) (h1: $ a = b $) (h2: $ c = d $): $ iff (a = c) (b = d) $;
--| @congr
axiom app_congr (a b c d: tm) (h1: $ a = b $) (h2: $ c = d $): $ a · c = b · d $;
--| @congr
axiom suc_congr (a b: tm) (h: $ a = b $): $ S a = S b $;
--| @congr
axiom add_congr (a b c d: tm) (h1: $ a = b $) (h2: $ c = d $): $ a + c = b + d $;
--| @congr
axiom lam_congr {x: tm} (a b: tm x) (h: $ a = b $): $ (λ x. a) = (λ x. b) $;
--| @congr
axiom sb_congr {x: tm} (e1 e2: tm x) (a1 a2: tm x) (h1: $ e1 = e2 $) (h2: $ a1 = a2 $):
  $ ([x := a1] e1) = ([x := a2] e2) $;
```

Note `lam_congr`: it lets an equation proved about a body `a`, possibly
mentioning the bound variable, lift to an equation between abstractions. This
is necessary to let rewriting descend under binders.

## Reduction

```aufbau-theory doc=lam
-- `a` replaces `x`, so it may mention `x`. In `sb_lam`, excluding `y` from
-- `a`'s dependencies prevents the binder from capturing a variable in `a`.

--| @compute ltr
axiom beta {x: tm} (e: tm x) (a: tm x): $ (λ x. e) · a = [x := a] e $;
--| @compute ltr
--| @rewrite
axiom sb_var {x: tm} (a: tm x): $ [x := a] x = a $;
--| @compute ltr
--| @rewrite
axiom sb_vac {x: tm} (e: tm) (a: tm x): $ [x := a] e = e $;
--| @compute ltr
--| @rewrite
axiom sb_app {x: tm} (f g: tm x) (a: tm x): $ [x := a] (f · g) = ([x := a] f) · ([x := a] g) $;
--| @compute ltr
--| @rewrite
axiom sb_suc {x: tm} (e: tm x) (a: tm x): $ [x := a] (S e) = S ([x := a] e) $;
--| @compute ltr
--| @rewrite
axiom sb_add {x: tm} (f g: tm x) (a: tm x): $ [x := a] (f + g) = ([x := a] f) + ([x := a] g) $;
--| @compute ltr
--| @rewrite
axiom sb_lam {x y: tm} (e: tm x y) (a: tm x): $ [x := a] (λ y. e) = (λ y. [x := a] e) $;
--| @compute ltr
axiom add_z (n: tm): $ 0 + n = n $;
--| @compute ltr
axiom add_s (m n: tm): $ S m + n = S (m + n) $;
```

Capture avoidance is via restriction on substitutions. In `sb_lam`, the
substituted term `a` is declared `(a: tm x)` (it may mention `x` but not `y`)
so a substitution only crosses a binder that cannot capture anything in the
substituted term.

The substitution rules carry two annotations. `@rewrite` lets the compiler run
substitutions whenever it checks an ordinary line, so a cited rule whose
conclusion contains a substitution can be stated in reduced form. `@compute`
enrolls the same equations, plus `beta` and the addition table, as directed
computation rules for `conversion?` (see [Computation](computation.md)).

## Single steps

`@rewrite` normalization alone is enough to make one beta step a one-line
proof. The raw conclusion of `beta` here is `[x := 0] (S x)`; the line states
the reduced form and the compiler emits the conversion:

```aufbau-proof doc=lam
@@mm0
theorem beta_step {x: tm}: $ (λ x. S x) · 0 = S 0 $;
@@auf
beta_step
---------
l1: $ (λ x. S x) · 0 = S 0 $ by beta
```

For anything longer than one step, equations are chained by hand with the
congruence and transitivity axioms. Here is the K combinator discarding its
second argument:

```aufbau-proof doc=lam
@@mm0
theorem k_reduce {x y: tm} (a b: tm): $ (λ x. λ y. x) · a · b = a $;
@@auf
k_reduce
--------
l1: $ (λ x. λ y. x) · a = λ y. a $ by beta
l2: $ b = b $ by eq_refl
l3: $ (λ x. λ y. x) · a · b = (λ y. a) · b $ by app_congr [l1, l2]
l4: $ (λ y. a) · b = a $ by beta
l5: $ (λ x. λ y. x) · a · b = a $ by eq_trans [l3, l4]
```

`l1` reduces under the binder through `sb_lam` (legal, since `a` doesn't
mention `y`), and `l4` discharges `[y := b] a` by `sb_vac`. Both capture facts
come straight from the binder declarations of the theorem.

## Evaluation

A Church numeral is a function iterator so applying one to the successor
function and `0` should evaluate it:

```aufbau-proof prelude=lam-base,lam-rules
lemma two_apply {f x w: tm}: $ (λ f. λ x. f · (f · x)) · (λ w. S w) · 0 = S S 0 $
----
l1: $ (λ f. λ x. f · (f · x)) · (λ w. S w) · 0 = S S 0 $ by conversion?
```

The goal is an equation, so `conversion?` only has to join its two sides: the
fold reduces the left side to `S S 0`. Church addition works the same way:
`plus` uses its first numeral to iterate `f` on top of the second's result, and
`1 + 1 = 2` is just evaluation.

```aufbau-proof prelude=lam-base,lam-rules
lemma one_plus_one {m n f x g y w: tm}:
  $ (λ m. λ n. λ f. λ x. m · f · (n · f · x)) · (λ g. λ y. g · y) · (λ g. λ y. g · y) · (λ w. S w) · 0 = S S 0 $
----
l1: $ (λ m. λ n. λ f. λ x. m · f · (n · f · x)) · (λ g. λ y. g · y) · (λ g. λ y. g · y) · (λ w. S w) · 0 = S S 0 $ by conversion?
```

The accepted suggestion expands to a long proof because every conversion step
is emitted explicitly.

## The Y combinator

The fixed-point combinator `Y = λ f. (λ x. f · (x · x)) · (λ x. f · (x · x))`
satisfies `Y · g = g · (Y · g)` for any `g`. Name it with a definition, whose
bound variables become dummy binders:

```aufbau-theory doc=lam
def Y {.f .x: tm}: tm = $ λ f. (λ x. f · (x · x)) · (λ x. f · (x · x)) $;
```

Writing `ω` for `λ u. g · (u · u)`, one beta step takes `Y · g` to `ω · ω`,
and one more takes `ω · ω` to `g · (ω · ω)`, so both sides of the fixed-point
equation reduce to a common term.

```aufbau-proof doc=lam
@@mm0
theorem y_reduce (g: tm): $ Y · g = g · (Y · g) $;
@@auf
y_reduce
--------
l1: $ Y · g = (λ u. g · (u · u)) · (λ u. g · (u · u)) $ by beta
l2: $ (λ u. g · (u · u)) · (λ u. g · (u · u)) = g · ((λ u. g · (u · u)) · (λ u. g · (u · u))) $ by beta
l3: $ g = g $ by eq_refl
l4: $ (λ u. g · (u · u)) · (λ u. g · (u · u)) = Y · g $ by eq_symm [l1]
l5: $ g · ((λ u. g · (u · u)) · (λ u. g · (u · u))) = g · (Y · g) $ by app_congr [l3, l4]
l6: $ Y · g = g · ((λ u. g · (u · u)) · (λ u. g · (u · u))) $ by eq_trans [l1, l2]
l7: $ Y · g = g · (Y · g) $ by eq_trans [l6, l5]
```

`l1` applies `beta` to a goal whose left side is `Y`, not a visible 
abstraction; the compiler unfolds the definition to find the redex.

`conversion?` can find this equation, but only when the definition of `Y` is 
used rather than the defined term `Y`. Only annotated definitions take part in 
conversion, and a definition with hidden dummy binders can be folded but never 
unfolded during conversion (see [Computation](computation.md)), so `Y` is 
opaque to that search method.

## The whole page

```aufbau-index doc=lam
```
