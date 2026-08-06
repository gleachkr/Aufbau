# Views and recovery

Every rule has a raw form, meaning its conclusion and hypotheses as literally
declared and used in the raw binary output, and the form that is used when 
writing down concrete inferences. For most rules these coincide. However, they 
can come apart when a rule is stated with a substitution term, because rewrite 
rules can remove the substitution. In this case, the user supplied line might 
not directly match the raw form, making it more complicated to recover the 
correct rule bindings from the user line. The `@view`, `@recover`, and 
`@abstract` annotations are used to recover bindings when it is not obvious how 
to read them off the surface form used in writing a proof. This chapter 
explains those annotations.

## The problem

Consider ∃-introduction:

```mm0
axiom ex_intro {x: obj} (g: ctx) (t: obj x) (p: wff x):
  $ g ⊢ [x := t] p $ > $ g ⊢ ∃ x p $;
```

To conclude `g ⊢ ∃ x p`, cite a proof of `p` with the witness `t` substituted
for `x`. Without annotations, this cell fails:

```aufbau-proof prelude=nd-base,nd-rules,fol-base,fol-rules
@@mm0
axiom ex_intro_raw {x: obj} (g: ctx) (t: obj x) (p: wff x):
  $ g ⊢ [x := t] p $ > $ g ⊢ ∃ x p $;
@@auf
lemma exists_wit {x y: obj}: $ P y ⊢ ∃ x (P x) $
----
l1: $ P y ⊢ P y $ by ax
l2: $ P y ⊢ ∃ x (P x) $ by ex_intro_raw [l1]
```

```
the statement and cited premises could not be matched against this rule
first unsolved binder: x
```

The goal determines `p := P x`. But the witness `t` occurs only inside
`[x := t] p`, which doesn't occur in the written line (instead, the cited line
shows the substitution already carried out: `P y`). The line does check with
the bindings spelled out, `(x := $ x $, t := $ y $, p := $ P x $)`, but a rule
that demands that on every application is painful, and the witness is sitting
right there in the cited line.

## `@view`: an alternative signature

A `@view` annotation gives the compiler a second signature for the rule, which 
should match what users are supposed to actually type out:

```mm0
--| @view {x: obj} (g: ctx) (t: obj x) (p: wff x) (q: wff): $ g ⊢ q $ > $ g ⊢ ∃ x p $
--| @recover t q p x
--| @freshen g x
axiom ex_intro {x: obj} (g: ctx) (t: obj x) (p: wff x):
  $ g ⊢ [x := t] p $ > $ g ⊢ ∃ x p $;
```

The text after `@view` is a theorem-like signature. It must declare exactly as
many hypotheses as the rule. The compiler matches the view's conclusion against
the proof line and its hypotheses against the cited references, getting
bindings from the user-supplied line.

View binders are matched to rule binders by name. `x`, `g`, `t`, and `p`
name real rule binders, so solving them in the view solves the rule. `q`
names no rule binder: it is a *phantom* binder, local to the view. Here it
captures what the cited line proves (`P y`). A phantom binder exists to feed
*recovery annotations*.

## `@recover`: extracting a buried witness

The view solves `p := P x` and `q := P y`, but nothing yet solves `t`. That's
what `@recover` is for:

```
--| @recover <target> <source> <pattern> <hole>
```

The four names should be view binders, read as: to solve `target`, walk
`source` and `pattern` in parallel, and wherever `pattern` reaches the value of
`hole`, take the corresponding subtree of `source`. For `ex_intro`, `@recover t
q p x` walks `P y` against `P x`; the hole `x` sits under `P`, the
corresponding subtree of the source is `y`, so `t := y`.

```aufbau-proof prelude=nd-base,nd-rules,fol-base,fol-rules
lemma exists_wit {x y: obj}: $ P y ⊢ ∃ x (P x) $
----
l1: $ P y ⊢ P y $ by ax
l2: $ P y ⊢ ∃ x (P x) $ by ex_intro [l1]
```

With `t` recovered, the compiler instantiates the raw rule, normalizes
`[x := y] (P x)` to `P y` with the substitution rewrites, and the application
closes.

The recovery walk is structural. If the hole occurs several times, all
extracted candidates must agree; an unchanged occurrence of the hole in a bound
argument slot is skipped rather than treated as a candidate, so the binder
parameter of a substitution term is not mistaken for its witness; and if source
and pattern are already identical, the target is bound to the hole itself — the
identity instantiation. If the walk diverges any other way, recovery fails and
the line is rejected as usual.

∀-elimination is the same pattern on the conclusion side:

```mm0
--| @view {x: obj} (g: ctx x) (t: obj x) (p: wff x) (q: wff): $ g ⊢ ∀ x p $ > $ g ⊢ q $
--| @recover t q p x
axiom all_elim {x: obj} (g: ctx x) (t: obj x) (p: wff x):
  $ g ⊢ ∀ x p $ > $ g ⊢ [x := t] p $;
```

Here the phantom `q` captures the stated goal, and the witness is recovered
from what the user wants to conclude:

```aufbau-proof prelude=nd-base,nd-rules,fol-base,fol-rules
lemma inst {x y: obj}: $ ∀ x (P x) ⊢ P y $
----
l1: $ ∀ x (P x) ⊢ ∀ x (P x) $ by ax
l2: $ ∀ x (P x) ⊢ P y $ by all_elim [l1]
```

## `@abstract`: recovering a context

`@recover` extracts a subtree. Its counterpart `@abstract` recovers the
dual component: the surrounding structure in common to the two expressions,
with a hole where they differ. The motivating shape is a replacement rule, for
example something like "from `a ↔ b`, rewrite `a` to `b` inside any formula":

```aufbau-proof
@@mm0
delimiter $ ( ) $;
--| @vars z
provable sort wff;
term imp (a b: wff): wff; infixr imp: $→$ prec 25;
term top: wff; notation top: wff = ($⊤$:max);
term iff (a b: wff): wff; infixr iff: $↔$ prec 20;
term sb (t: wff) {x: wff} (r: wff x): wff;

--| @relation wff iff iff_refl iff_trans iff_sym iff_mp
axiom iff_refl (a: wff): $ a ↔ a $;
axiom iff_trans (a b c: wff): $ a ↔ b $ > $ b ↔ c $ > $ a ↔ c $;
axiom iff_sym (a b: wff): $ a ↔ b $ > $ b ↔ a $;
axiom iff_mp (a b: wff): $ a ↔ b $ > $ a $ > $ b $;

--| @congr
axiom imp_congr (a b c d: wff): $ a ↔ b $ > $ c ↔ d $ > $ (a → c) ↔ (b → d) $;

--| @rewrite
axiom sb_var (t: wff) {x: wff}: $ sb t x x ↔ t $;
--| @rewrite
axiom sb_vac (t: wff) {x: wff} (a: wff): $ sb t x a ↔ a $;
--| @rewrite
axiom sb_imp (t: wff) {x: wff} (a b: wff x): $ sb t x (a → b) ↔ (sb t x a → sb t x b) $;

--| @view {x: wff} (a b: wff) (r: wff x) (p q: wff): $ a ↔ b $ > $ p $ > $ q $
--| @abstract r p q x a b
--| @fresh x
axiom replace {x: wff} (a b: wff) (r: wff x): $ a ↔ b $ > $ sb a x r $ > $ sb b x r $;

theorem repl_demo (a b: wff): $ a ↔ b $ > $ a → ⊤ $ > $ b → ⊤ $;
theorem repl_two (a b: wff): $ a ↔ b $ > $ a → a $ > $ b → b $;
@@auf
repl_demo
----
l1: $ b → ⊤ $ by replace [#1, #2]

repl_two
----
l1: $ b → b $ by replace [#1, #2]
```

This is a self-contained theory: `sb t x r` substitutes a formula for a
formula variable, and `replace` is substitution of equivalent formulas. Like
the quantifier rules, the substitution operator shouldn't appear in what users
have to write. But unlike quantifier rules, the term being substituted in is
already captured by the view annotation, but the context of substitution is not
similarly available. So we use:

```
--| @abstract <target> <left> <right> <hole> <left-plug> <right-plug>
```

The six names are view binders: walk `left` and `right` in parallel, and
wherever the pair is exactly `(left-plug, right-plug)`, put `hole`;
everything else must agree on both sides and is kept. In `repl_demo` the
walk of `a → ⊤` against `b → ⊤` finds the plug pair on the left-hand side of
the arrow and recovers `r := x → ⊤`. Several occurrences of the pair are fine.
`repl_two` recovers `r := x → x`, replacing both at once.

## `@fresh`, completing the picture

One binder in `replace` is still unaccounted for: the substitution variable
`x` itself. It appears nowhere in the written proof, so no structural walk can
recover it. Luckily, it can be chosen arbitrarily.

The `@fresh` annotation handles this case. `--| @fresh x` fills the binder from
the sort's `@vars` pool (here, the `z` registered at the top of the theory)
before matching the view. The `fol-rules` examples do not need it because their
bound binder is visible in the line's `∀` or `∃`.

## How a line is elaborated

With all the annotations in play, the compiler determines a rule
application's arguments in a fixed order:

1. explicit bindings from the line, which nothing may override;
2. `@fresh` binders, filled from their pools;
3. `@view` matching against the line and the cited references;
4. `@recover` and `@abstract`, run to a fixed point over the view state;
5. ordinary unification against the raw rule, starting from what the view
   solved;
6. validation of every binding, then instantiation and normalization.

A rule binder still unsolved after all of this is an error.
