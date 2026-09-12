# A Hilbert calculus

Each chapter in this part develops a theory, alternating declarations and
proofs with explanations. Cells with the same document name share one
theory: theory cells add MM0 declarations, and proof cells add theorems and
proofs. Editing a cell rechecks its document. Later cells can use earlier
declarations in that document.

We start with a small classical system: a Hilbert calculus for propositional
logic.

## The signature

Two connectives suffice, implication and negation:

```aufbau-theory doc=hilbert
delimiter $ ( ) $;
provable sort wff;
term imp (a b: wff): wff;
infixr imp: $→$ prec 25;
infixr imp: $->$ prec 25;
term not (a: wff): wff;
prefix not: $¬$ prec 40;
prefix not: $~$ prec 40;
```

Each connective registers its notation twice, giving every Unicode token an
ASCII alias that can be typed easily. Negation binds tighter than implication,
and implication associates to the right.

## The axioms

A Hilbert calculus uses axiom schemes with few inference rules. This theory
has three schemes with no hypotheses and one inference rule:

```aufbau-theory doc=hilbert
axiom h1 (a b: wff): $ a → (b → a) $;
axiom h2 (a b c: wff):
  $ (a → (b → c)) → ((a → b) → (a → c)) $;
axiom h3 (a b: wff): $ (¬ a → ¬ b) → (b → a) $;
axiom mp (a b: wff): $ a $ > $ a → b $ > $ b $;
```

`h1` and `h2` are the K and S schemes, and `h3` is classical contraposition.
Modus ponens is the only inference rule. MM0 represents it as an axiom with
hypotheses.

## Implication is reflexive

Here's a classic proof of a simple tautology:

```aufbau-proof doc=hilbert
@@mm0
theorem imp_refl (a: wff): $ a → a $;
@@auf
imp_refl
--------
l1: $ a → ((a → a) → a) $ by h1
l2: $ a → (a → a) $ by h1
l3: $ (a → ((a → a) → a)) → ((a → (a → a)) → (a → a)) $ by h2
l4: $ (a → (a → a)) → (a → a) $ by mp [l1, l3]
l5: $ a → a $ by mp [l2, l4]
```

## Hypothetical syllogism

A theorem's hypotheses are cited as `#1`, `#2`, ... like any other reference:

```aufbau-proof doc=hilbert
@@mm0
theorem hs (a b c: wff): $ a → b $ > $ b → c $ > $ a → c $;
@@auf
hs
----
l1: $ (b → c) → (a → (b → c)) $ by h1
l2: $ a → (b → c) $ by mp [#2, l1]
l3: $ (a → (b → c)) → ((a → b) → (a → c)) $ by h2
l4: $ (a → b) → (a → c) $ by mp [l2, l3]
l5: $ a → c $ by mp [#1, l4]
```

## Negation

To shorten the double-negation proofs, we add one more axiom scheme:

```aufbau-theory doc=hilbert
axiom con2 (a b: wff): $ (a → ¬ b) → (b → ¬ a) $;
```

`con2` is derivable from the three schemes above, but this small development
assumes it to keep the example short. Double-negation introduction then takes
three lines:

```aufbau-proof doc=hilbert
@@mm0
theorem notnot1 (p: wff): $ p → ¬ ¬ p $;
@@auf
notnot1
-------
l1: $ ¬ p → ¬ p $ by imp_refl
l2: $ (¬ p → ¬ p) → (p → ¬ ¬ p) $ by con2
l3: $ p → ¬ ¬ p $ by mp [l1, l2]
```

The first line cites `imp_refl` from earlier on the page. Elimination uses the
same pattern with `h3`:

```aufbau-proof doc=hilbert
@@mm0
theorem dne (p: wff): $ ¬ ¬ p → p $;
@@auf
dne
----
l1: $ ¬ p → ¬ ¬ ¬ p $ by notnot1
l2: $ (¬ p → ¬ ¬ ¬ p) → (¬ ¬ p → p) $ by h3
l3: $ ¬ ¬ p → p $ by mp [l1, l2]
```

## The whole page

```aufbau-index doc=hilbert
```

The index lists every statement the page has built, in order, with a marker
for each proof obligation. The document behind it is an ordinary
`.mm0`/`.auf` pair, and everything on the page is live, so you can edit any of
the theorems, axioms, or proofs.
