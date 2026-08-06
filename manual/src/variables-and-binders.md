# Variables, binders, and dependencies

Term declarations require a binder list, like `(a b: wff)`, `{x: tm}` and `(e:
tm x)`.

## Regular variables

A binder in parentheses declares a **regular variable**, standing for an
arbitrary expression of its sort.

```mm0
axiom h1 (a b: wff): $ imp a (imp b a) $;
```

## Bound variables

A binder in curly braces declares a **bound variable** (this is perhaps 
regrettable terminology on the part of the metamath zero standard. It might be 
more helpful to think of it as a schematic *bindable* variable, as 
distinguished from a regular variable which is more like an ordinary schematic 
variable).

Bound variables are, for example, how a theory declares that a constructor is  
variable-binding:

```mm0
term lam {x: tm} (e: tm x): tm;
```

`lam` takes a variable `x` and a body `e`, both of sort `tm`, with the curly
braces indicating that `x` is a variable. A bound variable slot can only ever
be filled by a bound variable: `lam (app u u) e` is not well formed. An
abstraction is therefore never over a compound term.

These variables are also the object language's variables. A theory needs no
separate constructor for a variable standing as a term: in `lam x x` the body
is the bound variable itself.

## Dependencies

The sort in a regular binder may be followed by the names of bound variables.

```mm0
axiom sb_lam {x y: tm} (e: tm x y) (a: tm x):
  $ eq (sb x (lam y e) a) (lam y (sb x e a)) $;
```

`sb x e a` substitutes `a` for `x` in `e`; this axiom pushes that
substitution under a lambda. `e: tm x y` says that the body may mention either
variable. `a: tm x` says that `a` may mention `x` but not `y`.

More generally, if a bound binder is absent from a regular binder's dependency
list, the expression assigned to the regular binder must not mention the
variable assigned to the bound binder. Dependency lists encode side
conditions such as freshness and capture avoidance.

```aufbau-proof doc=binders
@@mm0
delimiter $ ( ) $;
provable sort wff;
sort tm;
term eq (a b: tm): wff;
term lam {x: tm} (e: tm x): tm;
term sb {x: tm} (e: tm x) (a: tm): tm;
axiom sb_lam {x y: tm} (e: tm x y) (a: tm x):
  $ eq (sb x (lam y e) a) (lam y (sb x e a)) $;
```

```aufbau-proof doc=binders
lemma push {x y u: tm}: $ eq (sb x (lam y x) u) (lam y (sb x x u)) $
----
l1: $ eq (sb x (lam y x) u) (lam y (sb x x u)) $ by sb_lam
```

The rule applies because `u` is a different variable from `y`. Substituting `x`
itself would be accepted too, since `a: tm x` allows it. Replace the two `u`s on
the proof line with `y`, though, so that the term being substituted in is the
lambda's own variable, and the line fails:

```
dependency violation: the rule does not allow a to mention the variable
assigned to y
```

This is the capture that the rule must exclude. Substituting `y` for `x` in
`lam y x` should leave `y` free, but the right-hand side places it under the
binder. MM0 does not rename variables automatically, so the binder list states
the restriction and the verifier enforces it. Aufbau can perform selected
alpha-renaming through annotations described in
[Ergonomics](ergonomics.md).

Distinct bound binders must stand for distinct variables. A rule declaring `{x
y: tm}`, as `sb_lam` does, cannot be applied with both slots filled by one
variable, and reports that `x` and `y` must be assigned distinct variables.

A constructor's result sort can carry dependencies as well: `term fresh {x: tm}
(e: tm): tm x;` declares that `fresh x e` mentions `x` however `e` is
instantiated. This affects which variables a compound expression counts as
mentioning, which is relevant to how it can function in a definition.

## Dummy variables

A **dummy variable** appears in a definition's body, or in a proof, without
being one of the arguments. In a binder list a dot marks it:

```mm0
def uniq {x .y: tm} (p: wff x): wff = $ ex y (all x (iff p (eq x y))) $;
```

`uniq` takes two arguments, `x` and `p`. Its `y` is internal to the body, and a
proof that unfolds `uniq` is free to instantiate it with any variable that does
not clash. Proofs introduce dummies of their own in the same way.

Definitions are covered in
[Axioms, theorems, and definitions](axioms-theorems-definitions.md). For now,
dummy variables are the third way that variables enter declarations. The
`free` sort modifier forbids dummies of that sort. The `strict` modifier
forbids bound binders, dummies, and appearances in dependency lists.
