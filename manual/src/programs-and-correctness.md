# Programs and correctness

This chapter shows how to verify small imperative programs. It builds
first-order dynamic logic in a world-labelled sequent calculus, derives the
rules of Hoare logic as theorems, and then verifies an assignment sequence and
a while loop. The Floyd assignment axiom is used as a `@rewrite`, so the
rewrite engine computes weakest preconditions and no substitution step is ever
written by hand.

## Formulas and programs

```aufbau-theory doc=hoare
delimiter $ ( ) [ / ] $;

provable sort wff;
sort ctx;
--| @vars u v s
sort world;
sort form;
sort prog;
--| @vars z
sort obj;

term zero: obj;
notation zero: obj = ($0$:max);
term pred (a: obj): obj;

term imp (p q: form): form;
infixr imp: $→$ prec 25;
term an (p q: form): form;
infixr an: $∧$ prec 35;
term neg (p: form): form;
prefix neg: $¬$ prec 40;
term tt: form;
notation tt: form = ($⊤$:max);
term bot: form;
notation bot: form = ($⊥$:max);
term eq (a b: obj): form;
infixl eq: $=$ prec 50;
```

There are two base sorts of data: `obj` for the values program variables hold
(with just `0` and `pred` — deliberately, almost no arithmetic), and `world`
for program states. Formulas are a separate syntactic sort `form`, since the
provable sort `wff` is reserved for judgments about them.

```aufbau-theory doc=hoare
term sq (a b: prog): prog;
infixr sq: $⨟$ prec 32;
term star (a: prog): prog;
prefix star: $⋆$ prec 45;
term test (p: form): prog;
prefix test: $?$ prec 45;

term assign {x: obj} (e: obj x): prog;
notation assign {x: obj} (e: obj x): prog =
  ($⟨$:45) x ($≔$:0) e ($⟩$:0);

term box (a: prog) (p: form): form;
notation box (a: prog) (p: form): form = ($[$:41) a ($]$:0) p;

term sb_f {x: obj} (t: obj x) (p: form x): form;
notation sb_f {x: obj} (t: obj x) (p: form x): form =
  ($⌊$:41) x ($/$:0) t ($⌋$:0) p;
term sb_t {x: obj} (t: obj x) (a: obj x): obj;
notation sb_t {x: obj} (t: obj x) (a: obj x): obj =
  ($subst$:41) x ($/$:0) t a;
```

Programs are: sequencing `a ⨟ b`, iteration `⋆ a`, tests `? p`, and assignment.
`[ a ] p` says `p` holds after every terminating run of the program `a`.
Finally `⟨ x ≔ e ⟩` is assignment of the value of the expression `e` to the
variable `x`.

## Judgments

```aufbau-theory doc=hoare
term iff (a b: wff): wff;
infixr iff: $↔$ prec 20;
term feq (p q: form): wff;
infixr feq: $≃$ prec 20;
term peq (a b: prog): wff;
infixr peq: $≡$ prec 20;
term weq (w v: world): wff;
infixl weq: $≈$ prec 50;
term oeq (a b: obj): wff;
infixl oeq: $≐$ prec 50;

term at (w: world) (p: form): wff;
infixl at: $:$ prec 24;
term step (w: world) (a: prog) (v: world): wff;
notation step (w: world) (a: prog) (v: world): wff = ($step$:35) w a v;

term ctx_eq (g h: ctx): wff;
term emp: ctx;
notation emp: ctx = ($∅$:max);

--| @acui ctx_assoc ctx_comm emp ctx_idem
term join (g h: ctx): ctx;
infixl join: $,$ prec 5;
term hyp (a: wff): ctx;
coercion hyp: wff > ctx;
term nd (g: ctx) (a: wff): wff;
infixl nd: $⊢$ prec 0;

term valid (p: form): wff;
prefix valid: $⊨$ prec 3;

term ht (p: form) (a: prog) (q: form): wff;
notation ht (p: form) (a: prog) (q: form): wff =
  ($⦃$:35) p ($⦄$:0) a ($⟦$:35) q ($⟧$:0);
```

The basic judgment is world-labelled truth: `w : p` says the formula `p`
holds at state `w`, and `step w a v` says program `a` can move state `w` to
state `v`. Sequents `g ⊢ w : p` carry labelled facts in an ACUI context, as
in the [Natural deduction](natural-deduction.md) chapter. We also have validity
`⊨ p` (truth at every state) and the Hoare triple `⦃ p ⦄ a ⟦ q ⟧`.

## Equivalence infrastructure

Each sort gets its equivalence, bundled for the normalizer as in [Equality
and normalization](equality-and-normalization.md).

```aufbau-theory doc=hoare
--| @relation wff iff iff_refl iff_trans iff_sym iff_mp
axiom iff_refl (a: wff): $ a ↔ a $;
axiom iff_trans (a b c: wff):
  $ a ↔ b $ > $ b ↔ c $ > $ a ↔ c $;
axiom iff_sym (a b: wff): $ a ↔ b $ > $ b ↔ a $;
axiom iff_mp (a b: wff): $ a ↔ b $ > $ a $ > $ b $;

--| @relation form feq feq_refl feq_trans feq_sym _
axiom feq_refl (p: form): $ p ≃ p $;
axiom feq_trans (p q r: form):
  $ p ≃ q $ > $ q ≃ r $ > $ p ≃ r $;
axiom feq_sym (p q: form): $ p ≃ q $ > $ q ≃ p $;

--| @relation prog peq peq_refl peq_trans peq_sym _
axiom peq_refl (a: prog): $ a ≡ a $;
axiom peq_trans (a b c: prog):
  $ a ≡ b $ > $ b ≡ c $ > $ a ≡ c $;
axiom peq_sym (a b: prog): $ a ≡ b $ > $ b ≡ a $;

--| @relation world weq weq_refl weq_trans weq_sym _
axiom weq_refl (w: world): $ w ≈ w $;
axiom weq_trans (w v u: world):
  $ w ≈ v $ > $ v ≈ u $ > $ w ≈ u $;
axiom weq_sym (w v: world): $ w ≈ v $ > $ v ≈ w $;

--| @relation obj oeq oeq_refl oeq_trans oeq_sym _
axiom oeq_refl (a: obj): $ a ≐ a $;
axiom oeq_trans (a b c: obj):
  $ a ≐ b $ > $ b ≐ c $ > $ a ≐ c $;
axiom oeq_sym (a b: obj): $ a ≐ b $ > $ b ≐ a $;

--| @relation ctx ctx_eq ctx_refl ctx_trans ctx_sym _
axiom ctx_refl (g: ctx): $ ctx_eq g g $;
axiom ctx_trans (g h i: ctx):
  $ ctx_eq g h $ > $ ctx_eq h i $ > $ ctx_eq g i $;
axiom ctx_sym (g h: ctx): $ ctx_eq g h $ > $ ctx_eq h g $;
axiom ctx_assoc (g h i: ctx):
  $ ctx_eq ((g , h) , i) (g , (h , i)) $;
axiom ctx_comm (g h: ctx): $ ctx_eq (g , h) (h , g) $;
axiom ctx_idem (g: ctx): $ ctx_eq (g , g) g $;
axiom ctx_unit (g: ctx): $ ctx_eq (∅ , g) g $;
```

Every constructor gets a congruence, so rewriting can reach any position.

```aufbau-theory doc=hoare
--| @congr
axiom join_congr (g1 g2 h1 h2: ctx):
  $ ctx_eq g1 g2 $ > $ ctx_eq h1 h2 $ >
  $ ctx_eq (g1 , h1) (g2 , h2) $;
--| @congr
axiom hyp_congr (a b: wff): $ a ↔ b $ > $ ctx_eq (hyp a) (hyp b) $;
--| @congr
axiom nd_congr (g h: ctx) (a b: wff):
  $ ctx_eq g h $ > $ a ↔ b $ > $ (g ⊢ a) ↔ (h ⊢ b) $;

--| @congr
axiom imp_congr (p1 p2 q1 q2: form):
  $ p1 ≃ p2 $ > $ q1 ≃ q2 $ > $ (p1 → q1) ≃ (p2 → q2) $;
--| @congr
axiom an_congr (p1 p2 q1 q2: form):
  $ p1 ≃ p2 $ > $ q1 ≃ q2 $ > $ (p1 ∧ q1) ≃ (p2 ∧ q2) $;
--| @congr
axiom neg_congr (p q: form): $ p ≃ q $ > $ ¬ p ≃ ¬ q $;
--| @congr
axiom eq_congr (a b c d: obj):
  $ a ≐ b $ > $ c ≐ d $ > $ (a = c) ≃ (b = d) $;
--| @congr
axiom pred_congr (a b: obj): $ a ≐ b $ > $ pred a ≐ pred b $;
--| @congr
axiom box_congr (a1 a2: prog) (p q: form):
  $ a1 ≡ a2 $ > $ p ≃ q $ > $ [ a1 ] p ≃ [ a2 ] q $;

--| @congr
axiom sq_congr (a1 a2 b1 b2: prog):
  $ a1 ≡ a2 $ > $ b1 ≡ b2 $ > $ (a1 ⨟ b1) ≡ (a2 ⨟ b2) $;
--| @congr
axiom star_congr (a b: prog): $ a ≡ b $ > $ ⋆ a ≡ ⋆ b $;
--| @congr
axiom test_congr (p q: form): $ p ≃ q $ > $ ? p ≡ ? q $;

--| @congr
axiom at_congr (w1 w2: world) (p q: form):
  $ w1 ≈ w2 $ > $ p ≃ q $ > $ (w1 : p) ↔ (w2 : q) $;
--| @congr
axiom step_congr (w1 w2: world) (a1 a2: prog) (v1 v2: world):
  $ w1 ≈ w2 $ > $ a1 ≡ a2 $ > $ v1 ≈ v2 $ >
  $ (step w1 a1 v1) ↔ (step w2 a2 v2) $;
--| @congr
axiom valid_congr (p q: form): $ p ≃ q $ > $ (⊨ p) ↔ (⊨ q) $;
--| @congr
axiom ht_congr (p1 p2: form) (a1 a2: prog) (q1 q2: form):
  $ p1 ≃ p2 $ > $ a1 ≡ a2 $ > $ q1 ≃ q2 $ >
  $ (⦃ p1 ⦄ a1 ⟦ q1 ⟧) ↔ (⦃ p2 ⦄ a2 ⟦ q2 ⟧) $;
```

## Substitution as computation

The substitution operators get the standard `@rewrite` annotations, as in the
[Peano](peano.md) and [lambda calculus](lambda-calculus.md) chapters:

```aufbau-theory doc=hoare
--| @rewrite
axiom sb_t_var {x: obj} (t: obj x): $ (subst x / t x) ≐ t $;
--| @rewrite
axiom sb_t_other {x y: obj} (t: obj x): $ (subst x / t y) ≐ y $;
--| @rewrite
axiom sb_t_irrel {x: obj} (t: obj x) (a: obj): $ (subst x / t a) ≐ a $;
--| @rewrite
axiom sb_t_pred {x: obj} (t: obj x) (a: obj x):
  $ (subst x / t (pred a)) ≐ pred (subst x / t a) $;
--| @rewrite
axiom sb_f_irrel {x: obj} (t: obj x) (p: form): $ (⌊ x / t ⌋ p) ≃ p $;
--| @rewrite
axiom sb_f_eq {x: obj} (t: obj x) (a b: obj x):
  $ (⌊ x / t ⌋ (a = b)) ≃ ((subst x / t a) = (subst x / t b)) $;
--| @rewrite
axiom sb_f_an {x: obj} (t: obj x) (p q: form x):
  $ (⌊ x / t ⌋ (p ∧ q)) ≃ ((⌊ x / t ⌋ p) ∧ (⌊ x / t ⌋ q)) $;
--| @rewrite
axiom sb_f_imp {x: obj} (t: obj x) (p q: form x):
  $ (⌊ x / t ⌋ (p → q)) ≃ ((⌊ x / t ⌋ p) → (⌊ x / t ⌋ q)) $;
--| @rewrite
axiom sb_f_neg {x: obj} (t: obj x) (p: form x):
  $ (⌊ x / t ⌋ (¬ p)) ≃ (¬ (⌊ x / t ⌋ p)) $;
```

## The logic

The propositional core is a labelled natural deduction system. These are the
rules of the [Natural deduction](natural-deduction.md) chapter, with world
indices.

```aufbau-theory doc=hoare
axiom ax (g: ctx) (a: wff): $ g , a ⊢ a $;

--| @auto eager
axiom imp_intro (g: ctx) (w: world) (p q: form):
  $ g , w : p ⊢ w : q $ > $ g ⊢ w : (p → q) $;
--| @auto forward
axiom imp_elim (g h: ctx) (w: world) (p q: form):
  $ g ⊢ w : (p → q) $ > $ h ⊢ w : p $ > $ g , h ⊢ w : q $;

--| @auto eager 2
axiom an_intro (g: ctx) (w: world) (p q: form):
  $ g ⊢ w : p $ > $ g ⊢ w : q $ > $ g ⊢ w : (p ∧ q) $;
--| @auto forward
axiom an_elim_l (g: ctx) (w: world) (p q: form):
  $ g ⊢ w : (p ∧ q) $ > $ g ⊢ w : p $;
--| @auto forward
axiom an_elim_r (g: ctx) (w: world) (p q: form):
  $ g ⊢ w : (p ∧ q) $ > $ g ⊢ w : q $;

--| @auto eager
axiom neg_intro (g: ctx) (w: world) (p: form):
  $ g , w : p ⊢ w : ⊥ $ > $ g ⊢ w : (¬ p) $;
--| @auto forward
axiom neg_elim (g h: ctx) (w: world) (p: form):
  $ g ⊢ w : (¬ p) $ > $ h ⊢ w : p $ > $ g , h ⊢ w : ⊥ $;
axiom bot_elim (g: ctx) (w v: world) (p: form):
  $ g ⊢ w : ⊥ $ > $ g ⊢ v : p $;
axiom tt_intro (g: ctx) (w: world): $ g ⊢ w : ⊤ $;

axiom pbc (g: ctx) (w: world) (p: form):
  $ g , w : (¬ p) ⊢ w : ⊥ $ > $ g ⊢ w : p $;

axiom eq_refl_nd (g: ctx) (w: world) (a: obj): $ g ⊢ w : (a = a) $;

axiom at_mp (g: ctx) (w: world) (p q: form):
  $ g ⊢ w : p $ > $ p ≃ q $ > $ g ⊢ w : q $;
```

`pbc` makes the base logic classical.

The modality needs only two rules. K and necessitation are derivable:

```aufbau-theory doc=hoare
axiom box_intro (g: ctx) (w: world) {v: world} (a: prog) (p: form):
  $ g , step w a v ⊢ v : p $ > $ g ⊢ w : ([ a ] p) $;
--| @auto forward
axiom box_elim (g h: ctx) (w v: world) (a: prog) (p: form):
  $ g ⊢ w : ([ a ] p) $ > $ h ⊢ step w a v $ > $ g , h ⊢ v : p $;
```

`box_intro` is the labelled introduction rule: to show `[ a ] p` at `w`,
assume an arbitrary state `v` reached by `a` — the binder `{v: world}` makes
`v` an eigenvariable — and show `p` there.

## Reduction axioms

Compound programs reduce to their parts. Sequencing and test are genuine
rewrites; the box over a compound program *is* the simpler formula:

```aufbau-theory doc=hoare
--| @rewrite
axiom red_seq (a b: prog) (p: form):
  $ [ a ⨟ b ] p ≃ [ a ] ([ b ] p) $;
--| @rewrite
axiom red_test (q p: form):
  $ [ ? q ] p ≃ (q → p) $;

--| @rewrite
axiom red_assign {x: obj} (e: obj x) (p: form x):
  $ [ ⟨ x ≔ e ⟩ ] p ≃ (⌊ x / e ⌋ p) $;

axiom star_fix (a: prog) (p: form):
  $ [ ⋆ a ] p ≃ (p ∧ ([ a ] ([ ⋆ a ] p))) $;
axiom star_ind (g: ctx) (w: world) (a: prog) (p: form):
  $ g ⊢ w : p $ >
  $ g ⊢ w : ([ ⋆ a ] (p → ([ a ] p))) $ >
  $ g ⊢ w : ([ ⋆ a ] p) $;
```

`red_assign` is the Floyd assignment axiom: the box over an assignment is the
substitution instance. Because it is a `@rewrite`, and the substitution
operators push through the formula language by rewrites too, checking any line
against a boxed assignment computes the weakest precondition.

Iteration is different: `star_fix` is *not* a rewrite. Its right-hand side
mentions `[ ⋆ a ]` again, so normalizing with it would loop. Unfolding a loop
is a deliberate proof step. `star_ind` is the corresponding induction rule.

## Validity and Hoare triples

```aufbau-theory doc=hoare
axiom valid_intro {w: world} (p: form):
  $ ∅ ⊢ w : p $ > $ ⊨ p $;
--| @auto backward
axiom valid_elim (g: ctx) (w: world) (p: form):
  $ ⊨ p $ > $ g ⊢ w : p $;

--| @auto eager
axiom ht_intro (p q: form) (a: prog):
  $ ⊨ (p → ([ a ] q)) $ > $ ⦃ p ⦄ a ⟦ q ⟧ $;
--| @auto forward
axiom ht_elim (p q: form) (a: prog):
  $ ⦃ p ⦄ a ⟦ q ⟧ $ > $ ⊨ (p → ([ a ] q)) $;

def while (b: form) (a: prog): prog = $ ⋆ (? b ⨟ a) ⨟ ? (¬ b) $;
```

A formula is valid when it is provable at an eigenstate from no assumptions,
and `⦃ p ⦄ a ⟦ q ⟧` is interconvertible with `⊨ (p → ([ a ] q))`. The while
loop is a definition, not a primitive: iterate the guarded body, then exit
through the failed guard.

## The modal toolkit

A few validity-level lemmas are useful. `box_k` is the K axiom.

```aufbau-proof doc=hoare
@@mm0
theorem red_seq_sym (a b: prog) (p: form):
  $ ([ a ] ([ b ] p)) ≃ ([ a ⨟ b ] p) $;
theorem red_test_sym (q p: form):
  $ (q → p) ≃ ([ ? q ] p) $;
theorem red_assign_sym {x: obj} (e: obj x) (p: form x):
  $ (⌊ x / e ⌋ p) ≃ ([ ⟨ x ≔ e ⟩ ] p) $;
@@auf
red_seq_sym
-----------
l1: $ ([ a ] ([ b ] p)) ≃ ([ a ⨟ b ] p) $ by feq_sym [red_seq []]

red_test_sym
------------
l1: $ (q → p) ≃ ([ ? q ] p) $ by feq_sym [red_test []]

red_assign_sym
--------------
l1: $ (⌊ x / e ⌋ p) ≃ ([ ⟨ x ≔ e ⟩ ] p) $ by feq_sym [red_assign []]
```

The reduction axioms rewrite left to right, so proofs that need to *build* a
box (introducing `[ a ⨟ b ] p` from its reduct) cite these symmetric forms
through `at_mp`.

```aufbau-proof doc=hoare
@@mm0
theorem imp_refl_valid (p: form): $ ⊨ (p → p) $;
theorem valid_mp (p q: form): $ ⊨ (p → q) $ > $ ⊨ p $ > $ ⊨ q $;
theorem valid_nec (a: prog) (p: form): $ ⊨ p $ > $ ⊨ ([ a ] p) $;
theorem box_k (a: prog) (p q: form):
  $ ⊨ (([ a ] (p → q)) → (([ a ] p) → ([ a ] q))) $;
theorem box_mono (a: prog) (p q: form):
  $ ⊨ (p → q) $ > $ ⊨ (([ a ] p) → ([ a ] q)) $;
@@auf
imp_refl_valid
--------------
l1: $ u : p ⊢ u : p $ by ax []
l2: $ ∅ ⊢ u : (p → p) $ by imp_intro [l1]
l3: $ ⊨ (p → p) $ by valid_intro [l2]

valid_mp
--------
l1: $ ∅ ⊢ u : (p → q) $ by valid_elim [#1]
l2: $ ∅ ⊢ u : p $ by valid_elim [#2]
l3: $ ∅ ⊢ u : q $ by imp_elim [l1, l2]
l4: $ ⊨ q $ by valid_intro [l3]

valid_nec
---------
l1: $ step u a v ⊢ v : p $ by valid_elim [#1]
l2: $ ∅ ⊢ u : ([ a ] p) $ by box_intro [l1]
l3: $ ⊨ ([ a ] p) $ by valid_intro [l2]

box_k
-----
l1: $ u : ([ a ] (p → q)) , u : ([ a ] p) , step u a v ⊢ u : ([ a ] (p → q)) $ by ax []
l2: $ u : ([ a ] (p → q)) , u : ([ a ] p) , step u a v ⊢ u : ([ a ] p) $ by ax []
l3: $ u : ([ a ] (p → q)) , u : ([ a ] p) , step u a v ⊢ step u a v $ by ax []
l4: $ u : ([ a ] (p → q)) , u : ([ a ] p) , step u a v ⊢ v : (p → q) $ by box_elim [l1, l3]
l5: $ u : ([ a ] (p → q)) , u : ([ a ] p) , step u a v ⊢ v : p $ by box_elim [l2, l3]
l6: $ u : ([ a ] (p → q)) , u : ([ a ] p) , step u a v ⊢ v : q $ by imp_elim [l4, l5]
l7: $ u : ([ a ] (p → q)) , u : ([ a ] p) ⊢ u : ([ a ] q) $ by box_intro [l6]
l8: $ u : ([ a ] (p → q)) ⊢ u : (([ a ] p) → ([ a ] q)) $ by imp_intro [l7]
l9: $ ∅ ⊢ u : (([ a ] (p → q)) → (([ a ] p) → ([ a ] q))) $ by imp_intro [l8]
l10: $ ⊨ (([ a ] (p → q)) → (([ a ] p) → ([ a ] q))) $ by valid_intro [l9]

box_mono
--------
l1: $ ⊨ ([ a ] (p → q)) $ by valid_nec [#1]
l2: $ ⊨ (([ a ] p) → ([ a ] q)) $ by valid_mp [box_k [], l1]
```

Note the pool worlds: `imp_refl_valid` has no `world` binder of its own, so
`u` and `v` come from the sort's `@vars` pool and become the eigenstates that
`valid_intro` and `box_intro` discharge.

## Hoare logic, derived

Every rule of Hoare logic is now a theorem.

```aufbau-proof doc=hoare
@@mm0
theorem hoare_conseq (a: prog) (p p2 q q2: form):
  $ ⊨ (p2 → p) $ >
  $ ⦃ p ⦄ a ⟦ q ⟧ $ >
  $ ⊨ (q → q2) $ >
  $ ⦃ p2 ⦄ a ⟦ q2 ⟧ $;
theorem hoare_seq (a b: prog) (p q r: form):
  $ ⦃ p ⦄ a ⟦ q ⟧ $ >
  $ ⦃ q ⦄ b ⟦ r ⟧ $ >
  $ ⦃ p ⦄ (a ⨟ b) ⟦ r ⟧ $;
@@auf
hoare_conseq
------------
l1: $ u : p2 ⊢ u : p2 $ by ax []
l2: $ u : p2 ⊢ u : p $ by imp_elim [valid_elim [#1], l1]
l3: $ u : p2 ⊢ u : ([ a ] q) $ by imp_elim [valid_elim [ht_elim [#2]], l2]
l4: $ u : p2 ⊢ u : ([ a ] q2) $ by imp_elim [valid_elim [box_mono [#3]], l3]
l5: $ ∅ ⊢ u : (p2 → ([ a ] q2)) $ by imp_intro [l4]
l6: $ ⊨ (p2 → ([ a ] q2)) $ by valid_intro [l5]
l7: $ ⦃ p2 ⦄ a ⟦ q2 ⟧ $ by ht_intro [l6]

hoare_seq
---------
l1: $ u : p ⊢ u : p $ by ax []
l2: $ u : p ⊢ u : ([ a ] q) $ by imp_elim [valid_elim [ht_elim [#1]], l1]
l3: $ u : p ⊢ u : ([ a ] ([ b ] r)) $
  by imp_elim [valid_elim [box_mono [ht_elim [#2]]], l2]
l4: $ u : p ⊢ u : ([ a ⨟ b ] r) $ by at_mp [l3, red_seq_sym []]
l5: $ ∅ ⊢ u : (p → ([ a ⨟ b ] r)) $ by imp_intro [l4]
l6: $ ⊨ (p → ([ a ⨟ b ] r)) $ by valid_intro [l5]
l7: $ ⦃ p ⦄ (a ⨟ b) ⟦ r ⟧ $ by ht_intro [l6]
```

Assignment comes in two forms. The Floyd/Hoare rule falls out of `red_assign`
in five lines:

```aufbau-proof doc=hoare
@@mm0
--| @view {x: obj} (e: obj x) (p: form x) (q: form x): $ ⦃ q ⦄ ⟨ x ≔ e ⟩ ⟦ p ⟧ $
theorem hoare_assign {x: obj} (e: obj x) (p: form x):
  $ ⦃ ⌊ x / e ⌋ p ⦄ ⟨ x ≔ e ⟩ ⟦ p ⟧ $;
--| @view {x: obj} (e: obj x) (p: form x) (q: form x) (r: form x): $ ⊨ (q → r) $ > $ ⦃ q ⦄ ⟨ x ≔ e ⟩ ⟦ p ⟧ $
theorem hoare_assign_wp {x: obj} (e: obj x) (p: form x) (q: form x):
  $ ⊨ (q → (⌊ x / e ⌋ p)) $ >
  $ ⦃ q ⦄ ⟨ x ≔ e ⟩ ⟦ p ⟧ $;
@@auf
hoare_assign
------------
l1: $ u : (⌊ x / e ⌋ p) ⊢ u : (⌊ x / e ⌋ p) $ by ax []
l2: $ u : (⌊ x / e ⌋ p) ⊢ u : ([ ⟨ x ≔ e ⟩ ] p) $ by at_mp [l1, red_assign_sym []]
l3: $ ∅ ⊢ u : ((⌊ x / e ⌋ p) → ([ ⟨ x ≔ e ⟩ ] p)) $ by imp_intro [l2]
l4: $ ⊨ ((⌊ x / e ⌋ p) → ([ ⟨ x ≔ e ⟩ ] p)) $ by valid_intro [l3]
l5: $ ⦃ ⌊ x / e ⌋ p ⦄ ⟨ x ≔ e ⟩ ⟦ p ⟧ $ by ht_intro [l4]

hoare_assign_wp
---------------
l1: $ u : q ⊢ u : q $ by ax []
l2: $ u : q ⊢ u : (⌊ x / e ⌋ p) $ by imp_elim [valid_elim [#1], l1]
l3: $ u : q ⊢ u : ([ ⟨ x ≔ e ⟩ ] p) $ by at_mp [l2, red_assign_sym []]
l4: $ ∅ ⊢ u : (q → ([ ⟨ x ≔ e ⟩ ] p)) $ by imp_intro [l3]
l5: $ ⊨ (q → ([ ⟨ x ≔ e ⟩ ] p)) $ by valid_intro [l4]
l6: $ ⦃ q ⦄ ⟨ x ≔ e ⟩ ⟦ p ⟧ $ by ht_intro [l5]
```

The `@view` described in
[Views and recovery](views-and-recovery.md) avoids writing
`⌊ x / b ⌋ (x = b)`. Its phantom binder `q` occupies the precondition, while
the assignment and postcondition determine `x`, `e`, and `p`. The rewrite rules
then compute the substitution `⌊ x / e ⌋ p`.

`hoare_assign_wp` builds in precondition *strengthening*. Read its
hypothesis as "`q` implies the weakest precondition". Its view again lets us
lean on the rewrite rules to handle substitutions. The phantom `r` stands where
`⌊ x / e ⌋ p` sits in the raw rule, so the cited verification condition can be
written with the substitutions fully evaluated.

```aufbau-proof doc=hoare
@@mm0
theorem hoare_while (a: prog) (b p: form):
  $ ⦃ p ∧ b ⦄ a ⟦ p ⟧ $ >
  $ ⦃ p ⦄ while b a ⟦ p ∧ (¬ b) ⟧ $;
@@auf
hoare_while
-----------
l1: $ u : p , u : b ⊢ u : (p ∧ b) $ by an_intro [ax [], ax []]
l2: $ u : p , u : b ⊢ u : ([ a ] p) $ by imp_elim [valid_elim (g := $ ∅ $, w := $ u $) [ht_elim [#1]], l1]
l3: $ u : p ⊢ u : (b → ([ a ] p)) $ by imp_intro [l2]
l4: $ u : p ⊢ u : ([ ? b ] ([ a ] p)) $ by at_mp [l3, red_test_sym []]
l5: $ u : p ⊢ u : ([ ? b ⨟ a ] p) $ by at_mp [l4, red_seq_sym []]
l6: $ ∅ ⊢ u : (p → ([ ? b ⨟ a ] p)) $ by imp_intro [l5]
l7: $ ⊨ (p → ([ ? b ⨟ a ] p)) $ by valid_intro [l6]
l8: $ v : p , v : (¬ b) ⊢ v : (p ∧ (¬ b)) $ by an_intro [ax [], ax []]
l9: $ v : p ⊢ v : ((¬ b) → (p ∧ (¬ b))) $ by imp_intro [l8]
l10: $ v : p ⊢ v : ([ ? (¬ b) ] (p ∧ (¬ b))) $ by at_mp [l9, red_test_sym []]
l11: $ ∅ ⊢ v : (p → ([ ? (¬ b) ] (p ∧ (¬ b)))) $ by imp_intro [l10]
l12: $ ⊨ (p → ([ ? (¬ b) ] (p ∧ (¬ b)))) $ by valid_intro [l11]
l13: $ s : p ⊢ s : p $ by ax []
l14: $ s : p ⊢ s : ([ ⋆ (? b ⨟ a) ] (p → ([ ? b ⨟ a ] p))) $
  by valid_elim [valid_nec [l7]]
l15: $ s : p ⊢ s : ([ ⋆ (? b ⨟ a) ] p) $ by star_ind [l13, l14]
l16: $ s : p ⊢ s : (([ ⋆ (? b ⨟ a) ] p) → ([ ⋆ (? b ⨟ a) ] ([ ? (¬ b) ] (p ∧ (¬ b))))) $
  by valid_elim [box_mono [l12]]
l17: $ s : p ⊢ s : ([ ⋆ (? b ⨟ a) ] ([ ? (¬ b) ] (p ∧ (¬ b)))) $ by imp_elim [l16, l15]
l18: $ s : p ⊢ s : ([ ⋆ (? b ⨟ a) ⨟ ? (¬ b) ] (p ∧ (¬ b))) $ by at_mp [l17, red_seq_sym []]
l19: $ ∅ ⊢ s : (p → ([ ⋆ (? b ⨟ a) ⨟ ? (¬ b) ] (p ∧ (¬ b)))) $ by imp_intro [l18]
l20: $ ⊨ (p → ([ ⋆ (? b ⨟ a) ⨟ ? (¬ b) ] (p ∧ (¬ b)))) $ by valid_intro [l19]
l21: $ ⦃ p ⦄ while b a ⟦ p ∧ (¬ b) ⟧ $ by ht_intro [l20]
```

The last line states the triple with `while b a`; the compiler matches it
against `l20`'s unfolded form through the definition.

## Verified programs

First, last write wins. Note the first write's verification condition is just
reflexivity, the formal trace of the write being dead:

```aufbau-proof doc=hoare
@@mm0
theorem overwrite {x: obj} (a b: obj):
  $ ⦃ ⊤ ⦄ (⟨ x ≔ a ⟩ ⨟ ⟨ x ≔ b ⟩) ⟦ x = b ⟧ $;
@@auf
overwrite
---------
l1: $ ⦃ b = b ⦄ ⟨ x ≔ b ⟩ ⟦ x = b ⟧ $ by hoare_assign []
l2: $ u : ⊤ ⊢ u : (b = b) $ by eq_refl_nd []
l3: $ ∅ ⊢ u : (⊤ → (b = b)) $ by imp_intro [l2]
l4: $ ⊨ (⊤ → (b = b)) $ by valid_intro [l3]
l5: $ ⦃ ⊤ ⦄ ⟨ x ≔ a ⟩ ⟦ b = b ⟧ $ by hoare_assign_wp [l4]
l6: $ ⦃ ⊤ ⦄ (⟨ x ≔ a ⟩ ⨟ ⟨ x ≔ b ⟩) ⟦ x = b ⟧ $ by hoare_seq [l5, l1]
```

Finally, a loop: decrement `x` until it hits zero. The invariant is the
trivial `⊤`; `hoare_while` returns the invariant conjoined with the failed
guard `¬ ¬ (x = 0)`, and `hoare_conseq` cleans up the double
negation classically:

```aufbau-proof doc=hoare
@@mm0
theorem countdown {x: obj}:
  $ ⦃ ⊤ ⦄ while (¬ (x = 0)) (⟨ x ≔ pred x ⟩) ⟦ x = 0 ⟧ $;
@@auf
countdown
---------
l1: $ u : (⊤ ∧ (¬ (x = 0))) ⊢ u : ⊤ $ by tt_intro []
l2: $ ∅ ⊢ u : ((⊤ ∧ (¬ (x = 0))) → ⊤) $ by imp_intro [l1]
l3: $ ⊨ ((⊤ ∧ (¬ (x = 0))) → ⊤) $ by valid_intro [l2]
l5: $ ⦃ ⊤ ∧ (¬ (x = 0)) ⦄ ⟨ x ≔ pred x ⟩ ⟦ ⊤ ⟧ $ by hoare_assign_wp [l3]
l6: $ ⦃ ⊤ ⦄ while (¬ (x = 0)) (⟨ x ≔ pred x ⟩) ⟦ ⊤ ∧ (¬ (¬ (x = 0))) ⟧ $ by hoare_while [l5]
l7: $ u : (⊤ ∧ (¬ (¬ (x = 0)))) , u : (¬ (x = 0)) ⊢ u : (⊤ ∧ (¬ (¬ (x = 0)))) $ by ax []
l8: $ u : (⊤ ∧ (¬ (¬ (x = 0)))) , u : (¬ (x = 0)) ⊢ u : (¬ (¬ (x = 0))) $ by an_elim_r [l7]
l9: $ u : (⊤ ∧ (¬ (¬ (x = 0)))) , u : (¬ (x = 0)) ⊢ u : (¬ (x = 0)) $ by ax []
l10: $ u : (⊤ ∧ (¬ (¬ (x = 0)))) , u : (¬ (x = 0)) ⊢ u : ⊥ $ by neg_elim [l8, l9]
l11: $ u : (⊤ ∧ (¬ (¬ (x = 0)))) ⊢ u : (x = 0) $ by pbc [l10]
l12: $ ∅ ⊢ u : ((⊤ ∧ (¬ (¬ (x = 0)))) → (x = 0)) $ by imp_intro [l11]
l13: $ ⊨ ((⊤ ∧ (¬ (¬ (x = 0)))) → (x = 0)) $ by valid_intro [l12]
l14: $ ⦃ ⊤ ⦄ while (¬ (x = 0)) (⟨ x ≔ pred x ⟩) ⟦ x = 0 ⟧ $
  by hoare_conseq [imp_refl_valid (p := $ ⊤ $), l6, l13]
```

## The whole page

```aufbau-index doc=hoare
```
