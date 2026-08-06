# Ergonomics: variables, freshening, holes, fallbacks

This chapter covers four annotation families that help make proofs easier to
write: hole tokens, variable pools, freshness machinery that repairs binder
clashes, and rule fallbacks.

As a running example we extend the natural deduction theory with quantifiers.
The extension lives in two prelude files, `fol-base` (syntax, substitution,
and equality metadata) and `fol-rules` (the quantifier rules), loaded on top
of the propositional theory. This chapter uses the first file and one rule
from the second.

```aufbau-listing prelude=fol-base
```

There is nothing new in the second half of the file: `[x := t] p` is the
substitution operator of the last chapter, with `@congr` and `@rewrite`
supplying its normalization behavior. The `@vars` and `@alpha` annotations
are new, and the quantifier rules will lean on all of it.

## Hole tokens

`@hole` attaches to a sort. It registers a token that proof lines may use for
an omitted subexpression of that sort:

```mm0
--| @hole _wff
sort wff;
--| @hole _ctx
sort ctx;
```

Register holes for sorts whose expressions are routinely determined by the
rest of a proof line. In the natural-deduction theory, `ctx` is a good
candidate because contexts are large, repetitive, and usually fixed by the
cited rule.

A hole token may use any otherwise available token, including Unicode. This
manual follows the `_sort` convention.

## Variable pools

A `@vars` annotation on a sort registers tokens that proof lines may use as
variables.

```mm0
--| @vars u v w
sort obj;
```

When one of these tokens appears in proof math and is not otherwise known,
the compiler creates a theorem-local dummy variable of the annotated sort.

```aufbau-proof prelude=nd-base,nd-rules,fol-base,fol-rules
lemma pool_demo {x: obj}: $ _ ⊢ ∃ x (P x → P x) $
----
l1: $ P u ⊢ P u $ by ax
l2: $ _ ⊢ P u → P u $ by imp_intro [l1]
l3: $ _ ⊢ ∃ x (P x → P x) $ by ex_intro [l2]
```

The proof needs a name for the witness to `ex_intro`. The variable `u` comes
from the `@vars` pool.

Pool tokens work in proof line math only. Statement headers, including lemma
headers, must declare their variables as binders, and a pool token appearing
there is an unknown token. The annotation is rejected on `strict` and `free`
sorts, which forbid theorem-local dummies. A token that collides with another
pool, a term name, or a notation token is also rejected.

`@vars` pools are also where the compiler gets a variable when *it* needs one,
e.g. for witnesses that surface during definition unfolding and can't be
determined by the unfold target. A sort whose rules use these features needs a
`@vars` pool even if proof authors never write the tokens themselves.

## Freshness: `@freshen` and `@alpha`

[Variables, binders, and dependencies](variables-and-binders.md) introduced the
dependency check: if a rule declares `{x: obj}` and
an argument `(g: ctx)` without `x` in its dependency list, then whatever is
substituted for `g` may not mention the variable assigned to `x` anywhere,
even bound by a quantifier. For ∀-introduction this is stricter than the
textbook side condition. The rule

```mm0
axiom all_intro (g: ctx) {x: obj} (p: wff x):
  $ g ⊢ p $ > $ g ⊢ ∀ x p $;
```

demands that the context not mention `x` *at all*, while the textbook only
forbids *free* occurrences. A context that merely quantifies over the same
letter is rejected:

```aufbau-proof prelude=nd-base,nd-rules,fol-base,fol-rules
@@mm0
axiom all_intro_raw (g: ctx) {x: obj} (p: wff x):
  $ g ⊢ p $ > $ g ⊢ ∀ x p $;
@@auf
lemma vac_gen {a b: obj}: $ ∀ a (P a) , P b ⊢ ∀ a (P b) $
----
l1: $ ∀ a (P a) , P b ⊢ P b $ by ax
l2: $ ∀ a (P a) , P b ⊢ ∀ a (P b) $ by all_intro_raw [l1]
```

The generalization here is vacuous. `P b` does not mention `a` — and the `a`
inside the context is bound by its own `∀`. On paper this is fine. The line
still fails:

```
dependency violation: the rule does not allow g to mention the variable
assigned to x
```

Alpha-renaming repairs this case: `∀ a (P a)` and `∀ u (P u)` denote the same
hypothesis. MM0 has no built-in alpha-conversion, but the theory can prove a
renaming principle:

```mm0
--| @alpha x y
axiom all_alpha {x y: obj} (p: wff x y): $ ∀ x p ↔ ∀ y ([x := y] p) $;

--| @freshen g x
axiom all_intro (g: ctx) {x: obj} (p: wff x):
  $ g ⊢ p $ > $ g ⊢ ∀ x p $;
```

`@alpha old new` registers a proved renaming equivalence for one binding
constructor. `@freshen g x` names an alpha repair the compiler may attempt: if
applying the rule fails only because the value of `g` depends on the value of
`x`, rename the offending part of `g` to a fresh variable (chosen from the
`@vars` pool) using a registered `@alpha` rule, and retry. The renamed
application then proves an alpha-variant of the user's line, and the ordinary
congruence and transport machinery returns it to the stated form. With the
annotated rule from `fol-rules`, the same proof checks:

```aufbau-proof prelude=nd-base,nd-rules,fol-base,fol-rules
lemma vac_gen {a b: obj}: $ ∀ a (P a) , P b ⊢ ∀ a (P b) $
----
l1: $ ∀ a (P a) , P b ⊢ P b $ by ax
l2: $ ∀ a (P a) , P b ⊢ ∀ a (P b) $ by all_intro [l1]
```

The repair fires only for the declared argument pair, chooses one fresh
variable, and tries the registered alpha rules for the constructor at hand. It
is a targeted fix for the dependency check's over-approximation, not a general
modulo-alpha matching mode.

A `@freshen` repair requires: a `@vars` pool on the binder's sort, an `@alpha`
rule for each binding constructor that may head the offending subexpression,
and the substitution rewrites that reduce the renamed body.

## Fallbacks: `@fallback`

Some rules form families that should share one user-facing name. For example,
a theory may expose one `and_elim` rather than separate left and right
elimination names. `@fallback` connects the members of such a family:

```mm0
--| @fallback and_elim_r
axiom and_elim (g: ctx) (a b: wff): $ g ⊢ a ∧ b $ > $ g ⊢ a $;
```

When a proof line cites `and_elim` and the application fails the compiler
discards the attempt and retries the identical line with `and_elim_r`.

```aufbau-proof prelude=nd-base,nd-rules
@@mm0
--| @fallback and_elim_r
axiom and_elim (g: ctx) (a b: wff): $ g ⊢ a ∧ b $ > $ g ⊢ a $;
@@auf
lemma swap (a b: wff): $ _ ⊢ a ∧ b $ > $ _ ⊢ b ∧ a $
----
l1: $ _ ⊢ b $ by and_elim [#1]
l2: $ _ ⊢ a $ by and_elim [#1]
l3: $ _ ⊢ b ∧ a $ by and_intro [l1, l2]
```

`l2` is an ordinary `and_elim` application. `l1` checks through the
fallback: matching `and_elim`'s own conclusion against the line pins
`a := b`, after which `#1` cannot fill the premise, so the attempt fails and
the retry with `and_elim_r` proves the line.

Fallbacks chain: the target rule may carry a `@fallback` of its own. The
candidates are tried in chain order. When every candidate fails, the current
diagnostic comes from the first attempted rule, keeping the error
anchored to the rule name the line actually cites. A rule takes at most one
`@fallback`; the target must be declared earlier in the file.
