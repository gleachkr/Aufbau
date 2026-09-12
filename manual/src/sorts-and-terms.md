# Sorts and terms

An `.mm0` file declares a theory: the syntax of its expressions, its axioms,
and the theorems to be proved. A verifier checks the compiled `.mmb` proof
against this declaration. The `.mm0` file is the specification that an `.auf` 
proof development must satisfy.

An `.mm0` file contains a sequence of statements, each ending in a semicolon.
This chapter explains the statements that declare a theory's syntax.

## Sorts

A sort is a syntactic category, declared with `sort`:

```mm0
sort tm;
```

Every expression belongs to exactly one sort.

Sort declarations can carry modifiers. The most common is `provable`:

```mm0
provable sort wff;
```

`provable` means expressions of this sort can be asserted: they may appear
between `$` signs as an axiom's conclusion, a theorem's statement, or a
proof line's goal. Most theories have exactly one provable sort. The opening
Hilbert theory used `wff` as its only sort. The natural deduction examples
also used sorts for contexts and sequents.

## Term constructors

A `term` statement declares a way to build expressions.

```mm0
term imp (a b: wff): wff;
```

`imp` takes two expressions of sort `wff` and produces another `wff`. Within
a *math string* (text between `$` signs), write the constructor before its
arguments. Parenthesize any argument that is itself an application:

```
$ imp a (imp b a) $
```

Constructors and variables are the only syntactic forms that MM0 supports.
The `->` in earlier chapters was notation for the `imp` constructor. Here is
the implication fragment from earlier chapters without that notation.

```aufbau-proof doc=prefix
@@mm0
delimiter $ ( ) $;
provable sort wff;
term imp (a b: wff): wff;
axiom h1 (a b: wff): $ imp a (imp b a) $;
```

Proofs using the notation-free syntax differ only in how their formulas are
written.

```aufbau-proof doc=prefix
lemma weaken (p q: wff): $ imp p (imp q p) $
----
l1: $ imp p (imp q p) $ by h1
```

Argument names are used only for dependencies between binders (the subject of
the next chapter). A constructor whose argument names are never referred to can
be declared with an arrow type instead:

```mm0
term imp: wff > wff > wff;
```

## Delimiters

Theories generally open with something like this:

```mm0
delimiter $ ( ) $;
```

The parser normally splits math strings into tokens at whitespace.
Characters listed in this form of `delimiter` also create token boundaries
wherever they occur. Without this declaration, `(imp` is one unknown token
rather than `(` followed by `imp`. [Notation](notation.md#delimiters)
explains the other delimiter options.

## Several sorts

A theory can declare as many sorts as it needs. A first-order theory usually has
two: one for the objects it talks about and one for the statements it makes
about them.

```aufbau-proof doc=arith
@@mm0
delimiter $ ( ) $;
sort tm;
provable sort wff;
term zero: tm;
term suc (n: tm): tm;
term add (m n: tm): tm;
term eq (m n: tm): wff;
axiom eq_refl (a: tm): $ eq a a $;
axiom add_zero (a: tm): $ eq (add a zero) a $;
axiom eq_suc (a b: tm) (h: $ eq a b $): $ eq (suc a) (suc b) $;
```

```aufbau-proof doc=arith
lemma add_zero_suc (n: tm): $ eq (suc (add n zero)) (suc n) $
----
l1: $ eq (suc (add n zero)) (suc n) $ by eq_suc [add_zero []]
```

`tm` is not provable, which is why a numeral is not a valid assertion. Add
`axiom bare (n: tm): $ suc n $;` to the theory cell and it reports that the
math string does not have a provable sort. In this theory the only assertions
available are equations.

Sorts also provide the signatures for constructors. For example `eq` takes two
`tm`s, so `eq a (eq a a)` is rejected — the inner equation is a `wff`, and a
`wff` is never a `tm`.

## Coercions

A *coercion* lets the parser convert an expression from one sort to another.
It names a one-argument constructor that the parser inserts when the
surrounding expression requires the target sort.

```aufbau-proof doc=coercion
@@mm0
delimiter $ ( ) $;
provable sort wff;
sort ctx;
term hyp (a: wff): ctx;
coercion hyp: wff > ctx;
term nd (g: ctx) (a: wff): wff;
axiom ax (a: wff): $ nd a a $;
```

`hyp` turns a formula into a one-element context. The coercion lets us omit
it: `ax` is written `nd a a`, although `nd` requires a `ctx` as its first
argument. After the parser inserts the coercion, this is `nd (hyp a) a`.
Writing the constructor out gives the same expression:

```aufbau-proof doc=coercion
lemma trivial (p: wff): $ nd p p $
----
l1: $ nd (hyp p) p $ by ax
```

These declarations make a formula by itself denote a one-element context in
the natural-deduction theory used in [Proof search](proof-search.md).

A coercion may also be what makes a sort assertable. If the arithmetic theory
above declared `term holds (t: tm): wff;` and coerced `tm > wff`, then `$ suc
zero $` would be a statement after all, meaning `holds (suc zero)`.

The parser can chain coercions when several conversions are needed. To
prevent ambiguity, there must be at most one path between any two sorts,
even when the direction of each coercion is ignored.

## Sort modifiers

MM0 provides three other sort modifiers.

| modifier | meaning |
|---|---|
| `provable` | expressions of this sort can be asserted |
| `pure` | no term constructor may target this sort |
| `strict` | no variable of this sort may be bound, and it may not appear in another variable's dependencies |
| `free` | definitions and proofs may not introduce dummy variables of this sort |

Modifiers are written before `sort` and can be combined. Most theories need only
`provable`. The other three govern how the sort interacts with variables;
[Variables, binders, and dependencies](variables-and-binders.md) gives the
details.
