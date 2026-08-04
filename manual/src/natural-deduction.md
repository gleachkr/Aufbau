# Natural deduction

This chapter builds a sequent-style natural deduction system for intuitionistic 
logic, with quantifiers. Each annotation that appears here was introduced in one 
of the design chapters.

## Formulas

```aufbau-theory doc=nd
delimiter $ ( ) , $;
--| @hole _wff
sort wff;
--| @hole _ctx
sort ctx;
provable sort seq;

term imp (a b: wff): wff;
infixr imp: $→$ prec 25;
infixr imp: $->$ prec 25;
term and (a b: wff): wff;
infixr and: $∧$ prec 30;
infixr and: $/\$ prec 30;
term or (a b: wff): wff;
infixr or: $∨$ prec 28;
infixr or: $\/$ prec 28;
term not (a: wff): wff;
prefix not: $¬$ prec 40;
prefix not: $~$ prec 40;
term bot: wff; notation bot: wff = ($⊥$:max);
```

This theory has three sorts. Only `seq`, the sort of sequents,
is provable. Formulas and contexts are pure syntax: nothing ever proves a bare 
`wff`. Ungrammatical combinations like the conjunction of two sequents will not 
parse. Each connective carries an ASCII alias alongside its unicode notation.

## Sequents and contexts

```aufbau-theory doc=nd
term iff (a b: wff): seq;
infixr iff: $↔$ prec 20;
infixr iff: $<->$ prec 20;
term ctx_eq (g h: ctx): seq;
term emp: ctx; notation emp: ctx = ($_$:max);

--| @acui ctx_assoc ctx_comm emp ctx_idem
term join (g h: ctx): ctx; infixl join: $,$ prec 5;
term hyp (a: wff): ctx; coercion hyp: wff > ctx;
term nd (g: ctx) (a: wff): seq;
infixl nd: $⊢$ prec 0;
infixl nd: $|-$ prec 0;
term seq_eq (s t: seq): seq;
infixl seq_eq: $⟚$ prec 1;
infixl seq_eq: $<==>$ prec 1;
```

This cell declares judgment forms. A sequent like `g ⊢ a` is what deduction 
rules actually derive. The other three are equivalence judgments — `↔` on
formulas, `ctx_eq` on contexts, `⟚` on sequents — that exist to carry the
equational layer. Since `↔` produces a judgment (of sort `seq`) rather than a 
formula, an equivalence can never be embedded under a connective: it is 
metatheory, not object language.

Contexts are built from single formulas (hence the coercion from `wff` to 
`ctx`) with the join `,`, whose `@acui` annotation makes them behave as sets: 
order, grouping, and duplication are normalized when lines are checked. The 
empty context is written `_`.

## The equational layer

```aufbau-theory doc=nd
--| @relation wff iff iff_refl iff_trans iff_sym _
axiom iff_refl (a: wff): $ a ↔ a $;
axiom iff_trans (a b c: wff): $ a ↔ b $ > $ b ↔ c $ > $ a ↔ c $;
axiom iff_sym (a b: wff): $ a ↔ b $ > $ b ↔ a $;

--| @relation ctx ctx_eq ctx_refl ctx_trans ctx_sym _
axiom ctx_refl (g: ctx): $ ctx_eq g g $;
axiom ctx_trans (g h i: ctx): $ ctx_eq g h $ > $ ctx_eq h i $ > $ ctx_eq g i $;
axiom ctx_sym (g h: ctx): $ ctx_eq g h $ > $ ctx_eq h g $;
axiom ctx_assoc (g h i: ctx): $ ctx_eq ((g , h) , i) (g , (h , i)) $;
axiom ctx_comm (g h: ctx): $ ctx_eq (g , h) (h , g) $;
axiom ctx_idem (g: ctx): $ ctx_eq (g , g) g $;
axiom ctx_unit (g: ctx): $ ctx_eq (emp , g) g $;

--| @relation seq seq_eq seq_refl seq_trans seq_sym seq_mp
axiom seq_refl (s: seq): $ s ⟚ s $;
axiom seq_trans (s t u: seq): $ s ⟚ t $ > $ t ⟚ u $ > $ s ⟚ u $;
axiom seq_sym (s t: seq): $ s ⟚ t $ > $ t ⟚ s $;
axiom seq_mp (s t: seq): $ s ⟚ t $ > $ s $ > $ t $;

--| @congr
axiom join_congr (g1 g2 h1 h2: ctx):
  $ ctx_eq g1 g2 $ > $ ctx_eq h1 h2 $ > $ ctx_eq (g1 , h1) (g2 , h2) $;
--| @congr
axiom hyp_congr (a b: wff): $ a ↔ b $ > $ ctx_eq (hyp a) (hyp b) $;
--| @congr
axiom nd_congr (g h: ctx) (a b: wff):
  $ ctx_eq g h $ > $ a ↔ b $ > $ (g ⊢ a) ⟚ (h ⊢ b) $;
```

This follows the pattern of the [Equality and 
normalization](equality-and-normalization.md) chapter: a `@relation` bundle for 
each equivalence judgment, plus the context laws the `@acui` annotation cited. 
Only the sequent bundle carries a transport member, since `seq` is the only 
provable sort. The `@congr` axioms assist with deeply nested rewrites: a 
rewrite inside a formula lifts through `hyp_congr` and `nd_congr` to a `⟚` that 
the transport can use.

## The rules

```aufbau-theory doc=nd
axiom ax (g: ctx) (a: wff): $ g , a ⊢ a $;

axiom imp_intro (g: ctx) (a b: wff): $ g , a ⊢ b $ > $ g ⊢ a → b $;
axiom imp_elim (g h: ctx) (a b: wff): $ g ⊢ a → b $ > $ h ⊢ a $ > $ g , h ⊢ b $;

axiom and_intro (g: ctx) (a b: wff): $ g ⊢ a $ > $ g ⊢ b $ > $ g ⊢ a ∧ b $;
axiom and_elim_l (g: ctx) (a b: wff): $ g ⊢ a ∧ b $ > $ g ⊢ a $;
axiom and_elim_r (g: ctx) (a b: wff): $ g ⊢ a ∧ b $ > $ g ⊢ b $;

axiom or_intro_l (g: ctx) (a b: wff): $ g ⊢ a $ > $ g ⊢ a ∨ b $;
axiom or_intro_r (g: ctx) (a b: wff): $ g ⊢ b $ > $ g ⊢ a ∨ b $;
axiom or_elim (g h i: ctx) (a b c: wff):
  $ g ⊢ a ∨ b $ > $ h , a ⊢ c $ > $ i , b ⊢ c $ > $ g , h , i ⊢ c $;

axiom not_intro (g: ctx) (a: wff): $ g , a ⊢ ⊥ $ > $ g ⊢ ¬ a $;
axiom not_elim (g h: ctx) (a: wff): $ g ⊢ ¬ a $ > $ h ⊢ a $ > $ g , h ⊢ ⊥ $;
axiom bot_elim (g: ctx) (a: wff): $ g ⊢ ⊥ $ > $ g ⊢ a $;
```

The system is intuitionistic. Rules with two major premises join their contexts 
multiplicatively in the conclusion. The `ax` axiom is the only "leaf" axiom 
with no hypotheses. Since the `g` in `ax` is arbitrary, weakening happens at 
the leaves rather than by a structural rule.

A first proof, elimination followed by re-introduction:

```aufbau-proof doc=nd
@@mm0
theorem and_swap (a b: wff): $ a ∧ b ⊢ b ∧ a $;
@@auf
and_swap
--------
l1: $ a ∧ b ⊢ a ∧ b $ by ax
l2: $ a ∧ b ⊢ b $ by and_elim_r [l1]
l3: $ a ∧ b ⊢ a $ by and_elim_l [l1]
l4: $ a ∧ b ⊢ b ∧ a $ by and_intro [l2, l3]
```

Currying shows the context machinery working. The `ax` leaves on `l2` and
`l3` build in the needed weakening, and the three-part context that
`imp_elim` produces on `l5` is peeled back off one hypothesis at a time:

```aufbau-proof doc=nd
@@mm0
theorem curry (a b c: wff): $ a ∧ b → c ⊢ a → b → c $;
@@auf
curry
-----
l1: $ a ∧ b → c ⊢ a ∧ b → c $ by ax
l2: $ a , b ⊢ a $ by ax
l3: $ a , b ⊢ b $ by ax
l4: $ a , b ⊢ a ∧ b $ by and_intro [l2, l3]
l5: $ a ∧ b → c , a , b ⊢ c $ by imp_elim [l1, l4]
l6: $ a ∧ b → c , a ⊢ b → c $ by imp_intro [l5]
l7: $ a ∧ b → c ⊢ a → b → c $ by imp_intro [l6]
```

Excluded middle is not provable here, but its double negation is. Note `l7`:
`not_elim` concludes `g , h ⊢ ⊥` where `g` and `h` are the *same*
hypothesis. Idempotence collapses the join, so the line can state the
context once:

```aufbau-proof doc=nd
@@mm0
theorem lem_stable (a: wff): $ _ ⊢ ¬ ¬ (a ∨ ¬ a) $;
@@auf
lem_stable
----------
l1: $ ¬ (a ∨ ¬ a) ⊢ ¬ (a ∨ ¬ a) $ by ax
l2: $ a ⊢ a $ by ax
l3: $ a ⊢ a ∨ ¬ a $ by or_intro_l [l2]
l4: $ ¬ (a ∨ ¬ a) , a ⊢ ⊥ $ by not_elim [l1, l3]
l5: $ ¬ (a ∨ ¬ a) ⊢ ¬ a $ by not_intro [l4]
l6: $ ¬ (a ∨ ¬ a) ⊢ a ∨ ¬ a $ by or_intro_r [l5]
l7: $ ¬ (a ∨ ¬ a) ⊢ ⊥ $ by not_elim [l1, l6]
l8: $ _ ⊢ ¬ ¬ (a ∨ ¬ a) $ by not_intro [l7]
```

## Quantifiers

The quantifier layer adds a sort of objects, with a variable pool, and the
binding syntax:

```aufbau-theory doc=nd
delimiter $ [ ] $;

--| @vars u v w
sort obj;

term all {x: obj} (p: wff x): wff;
prefix all: $∀$ prec 41;
prefix all: $A.$ prec 41;
term ex {x: obj} (p: wff x): wff;
prefix ex: $∃$ prec 41;
prefix ex: $E.$ prec 41;

term P (t: obj): wff;
prefix P: $P$ prec 50;

term sb {x: obj} (t: obj x) (p: wff x): wff;
notation sb {x: obj} (t: obj x) (p: wff x): wff =
  ($[$:41) x ($:=$:0) t ($]$:0) p;
```

The substitution operator `[x := t] p` is just a normal term with no built-in
meaning. But some designated `@rewrite` equations let us automatically push it 
through each connective and discharge it at atoms, so the normalizer can 
compute substitutions whenever a rule application calls for one. The `@alpha` 
axioms at the end are the proved renaming principles that the freshness 
machinery of the [Ergonomics](ergonomics.md) chapter describes.

```aufbau-theory doc=nd
--| @congr
axiom imp_congr (a b c d: wff):
  $ a ↔ b $ > $ c ↔ d $ > $ (a → c) ↔ (b → d) $;
--| @congr
axiom and_congr (a b c d: wff):
  $ a ↔ b $ > $ c ↔ d $ > $ (a ∧ c) ↔ (b ∧ d) $;
--| @congr
axiom or_congr (a b c d: wff):
  $ a ↔ b $ > $ c ↔ d $ > $ (a ∨ c) ↔ (b ∨ d) $;
--| @congr
axiom not_congr (a b: wff): $ a ↔ b $ > $ ¬ a ↔ ¬ b $;
--| @congr
axiom all_congr {x: obj} (p q: wff x): $ p ↔ q $ > $ ∀ x p ↔ ∀ x q $;
--| @congr
axiom ex_congr {x: obj} (p q: wff x): $ p ↔ q $ > $ ∃ x p ↔ ∃ x q $;

--| @rewrite
axiom sb_vac {x: obj} (t: obj x) (p: wff): $ [x := t] p ↔ p $;
--| @rewrite
axiom sb_P {x: obj} (t: obj x): $ [x := t] (P x) ↔ P t $;
--| @rewrite
axiom sb_imp {x: obj} (t: obj x) (p q: wff x):
  $ [x := t] (p → q) ↔ ([x := t] p → [x := t] q) $;
--| @rewrite
axiom sb_and {x: obj} (t: obj x) (p q: wff x):
  $ [x := t] (p ∧ q) ↔ ([x := t] p ∧ [x := t] q) $;
--| @rewrite
axiom sb_or {x: obj} (t: obj x) (p q: wff x):
  $ [x := t] (p ∨ q) ↔ ([x := t] p ∨ [x := t] q) $;
--| @rewrite
axiom sb_not {x: obj} (t: obj x) (p: wff x):
  $ [x := t] (¬ p) ↔ ¬ ([x := t] p) $;
--| @rewrite
axiom sb_all {x y: obj} (t: obj x) (p: wff x y):
  $ [x := t] (∀ y p) ↔ ∀ y ([x := t] p) $;
--| @rewrite
axiom sb_ex {x y: obj} (t: obj x) (p: wff x y):
  $ [x := t] (∃ y p) ↔ ∃ y ([x := t] p) $;

--| @alpha x y
axiom all_alpha {x y: obj} (p: wff x y): $ ∀ x p ↔ ∀ y ([x := y] p) $;
--| @alpha x y
axiom ex_alpha {x y: obj} (p: wff x y): $ ∃ x p ↔ ∃ y ([x := y] p) $;
```

The four quantifier rules have several additional annotations: `@freshen` 
repairs from [Ergonomics](ergonomics.md), `@view`/`@recover` pairs from [Views 
and recovery](views-and-recovery.md), and `@auto` enrollments from [Powering 
search](powering-search.md):

```aufbau-theory doc=nd
--| @freshen g x
axiom all_intro (g: ctx) {x: obj} (p: wff x):
  $ g ⊢ p $ > $ g ⊢ ∀ x p $;

--| @auto forward
--| @view {x: obj} (g: ctx x) (t: obj x) (p: wff x) (q: wff): $ g ⊢ ∀ x p $ > $ g ⊢ q $
--| @recover t q p x
axiom all_elim {x: obj} (g: ctx x) (t: obj x) (p: wff x):
  $ g ⊢ ∀ x p $ > $ g ⊢ [x := t] p $;

--| @auto backward
--| @view {x: obj} (g: ctx) (t: obj x) (p: wff x) (q: wff): $ g ⊢ q $ > $ g ⊢ ∃ x p $
--| @recover t q p x
--| @freshen g x
axiom ex_intro {x: obj} (g: ctx) (t: obj x) (p: wff x):
  $ g ⊢ [x := t] p $ > $ g ⊢ ∃ x p $;

--| @freshen h x
--| @freshen c x
axiom ex_elim {x: obj} (g: ctx x) (h: ctx) (p: wff x) (c: wff):
  $ g ⊢ ∃ x p $ > $ h , p ⊢ c $ > $ g , h ⊢ c $;
```

Here `all_elim`'s conclusion is `[x := u] (P x)`, but `l2` states the 
normalized form `P u`, with a witness `u` from the `@vars` pool:

```aufbau-proof doc=nd
@@mm0
theorem all_to_ex {x: obj}: $ ∀ x (P x) ⊢ ∃ x (P x) $;
@@auf
all_to_ex
---------
l1: $ ∀ x (P x) ⊢ ∀ x (P x) $ by ax
l2: $ ∀ x (P x) ⊢ P u $ by all_elim [l1]
l3: $ ∀ x (P x) ⊢ ∃ x (P x) $ by ex_intro [l2]
```

Existential elimination can uses the bound `x` itself as the fresh name, and 
the rule's dependency constraints guarantee that neither the conclusion `c` nor 
the side context `h` can mention it that variable. Because of the alpha 
freshening, cases where an inference mentions `x` *bound* in `h` or `c` will be 
alpha-renamed behind the scenes before the rule is applied, and then 
alpha-renamed back in a way that is transparent to the user.

```aufbau-proof doc=nd
@@mm0
theorem const_wit {x: obj} (p: wff): $ ∃ x (P x ∧ p) ⊢ p $;
@@auf
const_wit
---------
l1: $ ∃ x (P x ∧ p) ⊢ ∃ x (P x ∧ p) $ by ax
l2: $ P x ∧ p ⊢ P x ∧ p $ by ax
l3: $ P x ∧ p ⊢ p $ by and_elim_r [l2]
l4: $ ∃ x (P x ∧ p) ⊢ p $ by ex_elim [l1, l3]
```

## The whole page

```aufbau-index doc=nd
```
