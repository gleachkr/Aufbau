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

`sb x e a` substitutes `a` for `x` in `e`. This axiom pushes a substitution 
under a lambda. `e: tm x y` says the body may mention either variable. `a: tm 
x` says that `a` can mention `x`, but not `y`: whatever `a` is instantiated 
with may not mention the variable `y` stands for. In general, if a bound binder 
occurs in theorem or axiom signature, but does not appear as a dependency of a 
regular binder in the same signature, then whatever is slotted in for the bound 
binder may not appear in whatever is slotted in for the regular binder. A 
variety of side conditions, for example freshness and accidental capture 
avoidance, can be encoded using this style of dependency declaration.

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

That is precisely the capture the rule has to rule out. Substituting `y` for `x`
in `lam y x` should leave that `y` free, but on the right-hand side it lands
under the binder, and the two sides stop agreeing. MM0 does not automatically 
rename variables to avoid this so the author states the condition in the binder 
list and the verifier enforces it at every application (however, the `abc` 
compiler does support some alpha-renaming, via special annotations discussed 
later in this manual).

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

Definitions are the subject of chapter 8. What matters here is that dummies are
the third way a variable enters a declaration, and that the two sort modifiers
left hanging in the last chapter are about the material of this one: `free`
forbids dummy variables of a sort, and `strict` forbids binding it at all — no
bound binder, no dummy, and no appearance in a dependency list.
