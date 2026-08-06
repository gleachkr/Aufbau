# Equality and normalization

Theories in earlier chapters used annotations to reorder contexts, normalize
substitutions, and reconcile concrete proof lines with the rules they cite.
This part explains how to add those features to a theory.

Annotations belong to the compiler frontend and do not extend the trusted
kernel. The compiler emits their effects as ordinary rule applications, which
the verifier checks against the unannotated MM0 theory. Annotations change how
the compiler constructs a binary proof certificate, not what the verifier
accepts.

This chapter covers `@relation`, `@congr`, `@rewrite`, and `@acui`. Each may be
attached to an `.mm0` declaration or, except for `@acui`, to a `lemma` block in
the `.auf` file, where it takes effect once the lemma is proved.

## Relation bundles

When the compiler reconciles two forms of an expression—a raw instantiated
conclusion against what the user wrote, say—it builds a proof that the two
are equivalent. To do that it has to know which relation plays the role of
equivalence for each sort, and which rules provide reflexivity, transitivity,
symmetry, and transport. A `@relation` annotation declares this bundle:

```
--| @relation <sort> <relation-term> <refl> <trans> <symm> <transport>
```

The natural deduction theory of the Proving chapters proves sequents, and
registers `⟚` as the equivalence on them:

```mm0
--| @relation seq seq_eq seq_refl seq_trans seq_sym seq_mp
axiom seq_refl (s: seq): $ s ⟚ s $;
axiom seq_trans (s t u: seq): $ s ⟚ t $ > $ t ⟚ u $ > $ s ⟚ u $;
axiom seq_sym (s t: seq): $ s ⟚ t $ > $ t ⟚ s $;
axiom seq_mp (s t: seq): $ s ⟚ t $ > $ s $ > $ t $;
```

The transport rule `seq_mp` is what makes the bundle useful on a provable
sort. After normalization by rewrite rules (see below), the compiler holds a
proof of the raw conclusion and a proof that the raw conclusion is equivalent
to the user's assertion; transport combines them into a proof of the assertion
itself.

For a non-provable sort there is no such thing as a proof of the sort's
expressions, so no transport rule is necessary. Write `_` in its place. The
same theory does this for its equivalences on formulas and on contexts:

```mm0
--| @relation wff iff iff_refl iff_trans iff_sym _
--| @relation ctx ctx_eq ctx_refl ctx_trans ctx_sym _
```

The four bundle rules must not have bound binders, since the compiler
instantiates them with arbitrary subexpressions when assembling a proof.

## Congruence rules

An equivalence can be discovered deep inside an expression (by rewrite rules or
proof search), and the compiler then needs to lift the resulting equivalence
through each surrounding constructor. A `@congr` annotation marks the rule that
justifies this for one constructor:

```mm0
--| @congr
axiom nd_congr (g h: ctx) (a b: wff):
  $ ctx_eq g h $ > $ a ↔ b $ > $ (g ⊢ a) ⟚ (h ⊢ b) $;
```

The binder layout follows a fixed convention: for each regular argument of the
constructor, a *before* and an *after* variable, in argument order, with one
hypothesis relating each pair. When an argument is unchanged the compiler
supplies a reflexivity proof itself, so one congruence rule per constructor
suffices.

Congruence rules may cross sorts. `nd_congr` lifts a context equivalence and
a formula equivalence into a sequent equivalence; in the lambda calculus
theory, `eq_congr` lifts two term equations into `↔`:

```mm0
--| @congr
axiom eq_congr (a b c d: tm) (h1: $ a = b $) (h2: $ c = d $):
  $ iff (a = c) (b = d) $;
```

The compiler picks the right relation for each hypothesis from the sort of
the corresponding argument. A sort with no registered relation is simply left
alone: children of that sort are never rewritten, and no congruence proof is
required for them.

For a binder-headed constructor, the changing argument appears once as a
bound binder and the before/after pair must declare every dependency the
constructor permits:

```mm0
--| @congr
axiom lam_congr {x: tm} (a b: tm x) (h: $ a = b $): $ (λ x. a) = (λ x. b) $;
```

Declaring `(a b: tm)` instead would reject the annotation: a congruence lift
plugs in arbitrary bodies, which may mention `x`.

## Rewrite rules

`@rewrite` marks an axiom or theorem as an oriented rewrite equation. The
conclusion must have the form `rel lhs rhs` for a registered relation. The
compiler reads it left to right. Wherever an expression matches the left-hand
side, replace it with the right-hand side. The substitution equations of the
lambda calculus chapter are an example of a useful set of rewrite rules:

```mm0
--| @rewrite
axiom sb_var {x: tm} (a: tm x): $ [x := a] x = a $;
--| @rewrite
axiom sb_vac {x: tm} (e: tm) (a: tm x): $ [x := a] e = e $;
--| @rewrite
axiom sb_add {x: tm} (f g: tm x) (a: tm x):
  $ [x := a] (f + g) = ([x := a] f) + ([x := a] g) $;
```

These fire during ordinary line checking. When a rule application's
instantiated conclusion or hypothesis does not match the corresponding
expression exactly, the compiler normalizes both sides with the registered
rewrites and compares the results, emitting every step it takes. That is why
a line can cite `beta` — whose right-hand side is a substitution term — and
state the substituted result:

```aufbau-proof prelude=lam-base,lam-rules
lemma push {x: tm}: $ (λ x. S (x + 0)) · S0 = S (S0 + 0) $
----
l1: $ (λ x. S (x + 0)) · S0 = S (S0 + 0) $ by beta
```

The raw right-hand side is `[x := S0] (S (x + 0))`. The compiler reduces it
with `sb_suc`, `sb_add`, `sb_var`, and `sb_vac`, lifts the steps through `S`
and `+` with the congruence rules, joins them with transitivity, and
transports the raw conclusion to the stated one. All of that lands in the
binary as ordinary rule applications.

Some mechanics worth knowing when curating a rewrite set:

- Rules are indexed by the head constructor of their left-hand side. When
  several rules share a head, they are tried in declaration order and the
  first match fires, with no backtracking — so put specific rules before
  general ones.
- Rewriting attempts to normalize expressions completely, and nothing stops
  you from registering a looping pair. A step limit cuts runaway
  normalization off, after which the line fails with an ordinary mismatch.
- Matching works on visible syntax. A rewrite does not fire inside a folded
  definition; transparent definitions are a separate mechanism.

Orientation matters: a rewrite set should reduce toward a normal form.
Equations that cannot be oriented, like commutativity, belong to
`conversion?`'s `@conversion` enrollment instead, covered later in the
manual.

## Substitution

The `beta` example above cited a rule whose conclusion contains a substitution
term:

```
axiom beta {x: tm} (e: tm x) (a: tm x): $ (λ x. e) · a = [x := a] e $;
```

The proof line states the reduced result

```
(λ x. S (x + 0)) · S0 = S (S0 + 0)
```

instead of the literal instance

```
(λ x. S (x + 0)) · S0 = [x := S0] (S (x + 0))
```

Rewrite rules perform the reduction between these forms.

The only way that a raw MM0 proof is allowed to perform substitution is by
instantiating the binders in a rule. Applying a rule assigns each of its
binders one expression, the same at every occurrence. There is no operation
that opens up an expression and replaces a variable inside that expression. So
there's no way, in the raw formalism, to write "p, with t in place of x" in a
statement. Many inferences nevertheless need this operation: β-reduction,
quantifier instantiation, Leibniz's law, and induction
schemes all need to talk about generic terms with a substitution applied to
them.

Following Metamath, an MM0 theory that needs substitution defines it *within
the logic*. The `fol-base` prelude extends the natural-deduction theory with
quantifiers and declares a substitution operator for formulas:

```mm0
term sb {x: obj} (t: obj x) (p: wff x): wff;
notation sb {x: obj} (t: obj x) (p: wff x): wff =
  ($[$:41) x ($:=$:0) t ($]$:0) p;
```

`sb` is an ordinary term constructor wearing a suggestive notation, not an
operation the compiler knows about: `[x := y] (P x)` and `P y` are distinct
expressions. The substitution relation is axiomatized:

```mm0
--| @rewrite
axiom sb_vac {x: obj} (t: obj x) (p: wff): $ [x := t] p ↔ p $;
--| @rewrite
axiom sb_P {x: obj} (t: obj x): $ [x := t] (P x) ↔ P t $;
--| @rewrite
axiom sb_imp {x: obj} (t: obj x) (p q: wff x):
  $ [x := t] (p → q) ↔ ([x := t] p → [x := t] q) $;
--| @rewrite
axiom sb_all {x y: obj} (t: obj x) (p: wff x y):
  $ [x := t] (∀ y p) ↔ ∀ y ([x := t] p) $;
```

Registering the substitution axioms as rewrite rules makes the operator
practical to use. Read together, the rules define its behavior:

- `sb_vac`: a vacuous substitution vanishes. Its proviso, "x not free in
  p", is expressed by the absence of `x` from the dependency list in
  `(p: wff)`.
- `sb_P`: at an atom, the replacement actually happens: assign `y` to `t` and
  the right-hand side reads `P y`. Each atomic predicate gets one such
  equation.
- `sb_imp`: substitution distributes through a constructor.
- `sb_all`: the substitution moves under another binder. The capture
  proviso, "t is free for x in p", is again captured by a dependency list: `(t:
  obj x)` may mention `x` but not `y`, so the term carried under `∀ y` can
  never contain the variable it binds.

With the operator and its equations in place, quantifier rules can be
stated, and (as with `beta`) used without `sb` ever needing to be written
explicitly. The compiler normalizes the instantiated conclusion before
comparing it against what the author wrote:

```aufbau-proof prelude=nd-base,nd-rules,fol-base
@@mm0
axiom all_elim {x: obj} (g: ctx x) (t: obj x) (p: wff x):
  $ g ⊢ ∀ x p $ > $ g ⊢ [x := t] p $;
@@auf
lemma inst {x y: obj}: $ ∀ x (P x → P x) ⊢ P y → P y $
----
l1: $ ∀ x (P x → P x) ⊢ ∀ x (P x → P x) $ by ax
l2: $ ∀ x (P x → P x) ⊢ P y → P y $ by all_elim [l1]
```

The raw conclusion of `l2` is `∀ x (P x → P x) ⊢ [x := y] (P x → P x)`:
`sb_imp` splits the substitution, `sb_P` finishes each side, congruence
lifts the steps through `→` and `⊢`, and transport lands on the stated
line. A complete equation set keeps `sb` confined to rule statements this
way, with proof lines stating only substituted results.[^1]

[^1]: The compiler recovers `y` as the substituted term through the `@view`
    annotations described in [Views and recovery](views-and-recovery.md).

The lambda calculus equations earlier in the chapter use the same approach for
substituting a term into a term: the recursion bottoms out at the variable
itself, `sb_var`, in place of the per-atom equations, and `sb_lam` plays
`sb_all`'s role, blocking capture the same way, by omitting `y` from the
dependency list of the replacement `a`.

## Structural combiners

The context `,` of the natural deduction theory is not governed by oriented
rewrites but by an `@acui` annotation on the combiner itself:

```mm0
--| @acui ctx_assoc ctx_comm emp ctx_idem
term join (g h: ctx): ctx; infixl join: $,$ prec 5;
```

The four fields are the associativity axiom, the commutativity axiom (or
`_`), the unit term, and the idempotence axiom (or `_`). The compiler
canonicalizes any expression built from the combiner (flattening nested
joins, dropping units, sorting members when commutativity is declared,
merging duplicates when idempotence is) and proves the canonical form equal
to the original using exactly the cited axioms. Two contexts that differ only
as collections are then interchangeable anywhere:

```aufbau-proof prelude=nd-base,nd-rules
lemma pick (a b c: wff): $ c , b , a ⊢ b $
----
l1: $ c , b , a ⊢ b $ by ax
```

`ax` concludes `g , a ⊢ a`; the compiler splits the stated context into
`g := c , a` and the principal formula `b` even though `b` sits in the
middle. Without the annotation the same theory rejects the line:

```aufbau-proof
@@mm0
delimiter $ ( ) , $;
provable sort wff;
sort ctx;
term join (g h: ctx): ctx; infixl join: $,$ prec 5;
term hyp (a: wff): ctx; coercion hyp: wff > ctx;
term nd (g: ctx) (a: wff): wff; infixl nd: $⊢$ prec 0;
axiom ax (g: ctx) (a: wff): $ g , a ⊢ a $;
@@auf
lemma pick (a b c: wff): $ c , b , a ⊢ b $
----
l1: $ c , b , a ⊢ b $ by ax
```

Here `g , a` can only match the raw tree `(c , b) , a`, so the rule proves
`c , b , a ⊢ a` and the line fails with a conclusion mismatch.

Associativity is mandatory; the other properties are independent. A
non-commutative monoid like function composition declares `--| @acui comp_assoc
_ id _` and gets flattening and unit elimination while preserving order. Unit
elimination additionally requires the matching unit laws (like `ctx_unit`
above) to be in scope, since each dropped unit must be justified by a proof.

An `@acui` combiner needs its companions: a `@relation` bundle for its sort,
and a `@congr` rule for the combiner, so the structural steps can be proved
and lifted like any other rewrite.
