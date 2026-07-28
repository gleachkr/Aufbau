# Notation

The last two chapters wrote expressions by applying constructors, as in `imp a
(imp b a)`. A notation declaration lets that same expression be written `a -> (b
-> a)`.

Notation is used for parsing, and (in `abc`) for formatting strings when 
displaying them to a user. It changes how a math string may be written, but the 
result is still a tree of term constructors. In a theory that declares a 
notation, the notation and constructor-application forms are interchangeable 
everywhere.

## Infix operators

`infixl` and `infixr` make a two-argument constructor into an infix operator at
a given precedence.

```aufbau-proof doc=notation
@@mm0
delimiter $ ( ) $;
provable sort wff;
term imp (a b: wff): wff;
term and (a b: wff): wff;
term not (a: wff): wff;
term iff (a b: wff): wff;
infixr imp: $->$ prec 25;
infixl and: $/\$ prec 30;
prefix not: $~$ prec 40;
infixl iff: $<->$ prec 20;
axiom iff_refl (a: wff): $ a <-> a $;
```

A higher precedence binds more tightly, so `/\` at 30 groups before `->` at 25.
`infixr` associates to the right and `infixl` to the left. Each lemma below
states one spelling against the other and closes with `iff_refl`, which
succeeds only if the two are the same expression.

```aufbau-proof doc=notation
lemma right_assoc (a b: wff): $ (a -> b -> a) <-> (imp a (imp b a)) $
----
l1: $ (a -> b -> a) <-> (imp a (imp b a)) $ by iff_refl

lemma left_assoc (a b c: wff): $ (a /\ b /\ c) <-> (and (and a b) c) $
----
l1: $ (a /\ b /\ c) <-> (and (and a b) c) $ by iff_refl

lemma tighter_binds_first (a b c: wff): $ (a /\ b -> c) <-> (imp (and a b) c) $
----
l1: $ (a /\ b -> c) <-> (imp (and a b) c) $ by iff_refl
```

An infix precedence must be below max, and a token may be declared at only one 
precedence. If two infix operators have the same precedence, they must 
associate the same way. An `infixl` and an `infixr` declared at the same 
precedence will be rejected. Operators sharing an associativity and precidence 
level can be mixed freely, so with `/\` and `\/` both `infixl` at 30, `a /\ b 
\/ c` is `(a /\ b) \/ c`.

## Prefix operators

`prefix` creates an operator whose token comes ahead of its argument. Prefix 
operators also get a precedence, so `~` at 40 outranks `/\` at 30 and applies 
only to the formula immediately next to it.

```aufbau-proof doc=notation
lemma prefix_is_tight (a b: wff): $ (~ a /\ b) <-> (and (not a) b) $
----
l1: $ (~ a /\ b) <-> (and (not a) b) $ by iff_refl

lemma repeated_prefix (a: wff): $ (~ ~ a) <-> (not (not a)) $
----
l1: $ (~ ~ a) <-> (not (not a)) $ by iff_refl
```

Precedence also decides whether a prefix operator's argument needs parentheses 
around it. Repeated application of a prefix operator never needs parentheses.

## Delimiters

Delimiters were introduced in Chapter 5. Math strings are split on whitespace 
first; delimiter characters then split the pieces further. The delimiter 
characters can be given as one list or as two.

```mm0
delimiter $ ( ) $;          -- both
delimiter $ ( $ $ ) $;      -- left, then right
```

A left delimiter splits *after* itself and a right delimiter *before* itself; a
character in the one-list form does both. Grouping therefore needs `(` on the
left and `)` on the right. Declaring them the other way round leaves something 
like `(imp` a single token.

Delimiters must be a single byte. `delimiter $ ( ) λ $;` is rejected, which is
why a lambda is written `λ x. e` and not `λx. e` — `λ` cannot be made to split
a token it is glued to.

## Notation for everything else

`notation` covers more complicated notations: bare constants, mixfix operators, 
and binders. It lists the declaration's variables interleaved with constants, 
each constant written `(token:prec)`.

```aufbau-proof doc=lambda
@@mm0
delimiter $ ( ) . $;
provable sort wff;
sort tm;
term eq (a b: tm): wff;
term lam {x: tm} (e: tm x): tm;
notation lam {x: tm} (e: tm x): tm = ($λ$:41) x ($.$:0) e;
term add (a b: tm): tm;
infixl add: $+$ prec 30;
axiom eq_refl (a: tm): $ eq a a $;
```

The first literal must be a constant, and it may not be shared with any other
notation. `.` is listed as a delimiter so that `x.` splits into two tokens.

## When a string parses as something else

A binder notation's trailing slot is parsed with the precedence declared on the 
leading constant, so `λ x. x + x` is `(λ x. x) + x` in the small theory above:

```aufbau-proof doc=lambda
lemma body_stops_early {x: tm}: $ eq (λ x. x + x) (add (lam x x) x) $
----
l1: $ eq (λ x. x + x) (add (lam x x) x) $ by eq_refl
```

`+` has precedence 30, which is less than the leading constant's 41, so the 
body is just `x` and the sum is formed around the lambda rather than inside it. 
The `($.$:0)` in the declaration is the precedence of the `.` token and does 
not make the body greedy. Parentheses give the intended reading:

```aufbau-proof doc=lambda
lemma parens_fix {x: tm}: $ eq (λ x. (x + x)) (lam x (add x x)) $
----
l1: $ eq (λ x. (x + x)) (lam x (add x x)) $ by eq_refl
```

## Alternative notations

A constructor can carry more than one notation. The theories in this manual
declare an ASCII and a Unicode form of each operator at the same precedence:

```mm0
infixr imp: $->$ prec 25;
infixr imp: $→$ prec 25;
```

Both parse to `imp`, so a proof may use whichever reads better or is easier to 
type. A rule stated with one applies to a goal written with the other.
