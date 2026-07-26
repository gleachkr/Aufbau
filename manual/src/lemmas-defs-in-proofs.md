# Lemmas and definitions in proofs

An `.auf` file is a sequence of top-level items: proof blocks, `lemma` blocks,
and `def` items. Proof blocks discharge the theorems declared in the `.mm0`
file. `lemma`s and `defs` allow you to extend the theory in a logically-safe 
way from within the `.auf` file.

## Proof blocks

A theorem declared in the `.mm0` file is proved by a block consisting of the 
name of the theorem, an underline of at least three dashes, and the proof 
lines.

```aufbau-proof prelude=nd-base,nd-rules
@@mm0
theorem and_comm (g: ctx) (a b: wff): $ g ⊢ a ∧ b $ > $ g ⊢ b ∧ a $;
@@auf
and_comm
----
l1: $ g ⊢ b $ by and_elim_r [#1]
l2: $ g ⊢ a $ by and_elim_l [#1]
l3: $ g ⊢ b ∧ a $ by and_intro [l1, l2]
```

Blocks appear in the order of the declarations they discharge. The compiler
streams through the `.mm0` and `.auf` files together rather than building a
global proof database, so each block must match the next public declaration,
and forward references are rejected.

## Lemma blocks

A `lemma` block declares a proof-local rule. It carries its own signature, 
written like an MM0 axiom:

```
lemma NAME (binders): $ hypothesis $ > $ conclusion $
----
proof lines
```

Once proved, a lemma is cited exactly like an axiom or a public theorem: by
name, with its hypotheses in brackets and its variables inferred from the goal
and the references.

```aufbau-proof prelude=nd-base,nd-rules
lemma and_comm (g: ctx) (a b: wff): $ g ⊢ a ∧ b $ > $ g ⊢ b ∧ a $
----
l1: $ g ⊢ b $ by and_elim_r [#1]
l2: $ g ⊢ a $ by and_elim_l [#1]
l3: $ g ⊢ b ∧ a $ by and_intro [l1, l2]

lemma and_comm_imp (a b: wff): $ _ ⊢ (a ∧ b) → (b ∧ a) $
----
l1: $ a ∧ b ⊢ a ∧ b $ by ax []
l2: $ a ∧ b ⊢ b ∧ a $ by and_comm [l1]
l3: $ _ ⊢ (a ∧ b) → (b ∧ a) $ by imp_intro [l2]
```

`and_comm` is a derived rule: from a proof of `g ⊢ a ∧ b` it produces one of
`g ⊢ b ∧ a`, for any context and any two formulas. Line `l2` of `and_comm_imp`
applies it with `g` bound to `a ∧ b`.

Lemmas are not part of the theory's `.mm0` interface, and nothing outside the
proof file can cite them. In the compiled `.mmb` binary they are emitted as 
local theorems.

## Definitions with hidden bodies

A definition declared in the `.mm0` file may omit its body. An omitted body can 
then be supplied by the proof file:

```aufbau-proof prelude=nd-base,nd-rules
@@mm0
def nand (a b: wff): wff;
infixr nand: $⊼$ prec 30;
@@auf
def nand = $ ¬ (a ∧ b) $

lemma nand_intro (g: ctx) (a b: wff): $ g , a ∧ b ⊢ ⊥ $ > $ g ⊢ a ⊼ b $
----
l1: $ g ⊢ a ⊼ b $ by not_intro [#1]

lemma nand_elim (g h: ctx) (a b: wff):
  $ g ⊢ a ⊼ b $ > $ h ⊢ a $ > $ h ⊢ b $ > $ g , h ⊢ ⊥ $
----
l1: $ h ⊢ a ∧ b $ by and_intro [#2, #3]
l2: $ g , h ⊢ ⊥ $ by not_elim [#1, l1]
```

A body filler has no return sort, which is what distinguishes it from the local
definitions below, and it must appear at the point in the proof file where the
bodyless declaration is reached. The definition it fills is public: it is
emitted as an ordinary term definition and checked against the `.mm0`
declaration, so it can carry notation, and `a ⊼ b` is available in proofs.

Leaving the body out of the `.mm0` file means the interface commits only to the
connective existing. The `.mm0` file can still include theorems that involve 
the defined term. Bodiless definitions are intended to provide a mechanism for 
"constructive implicit definitions", where a term is defined by a set of 
theorems that are provable about it, but the precise definition is left open by 
the theory and instead supplied by the proof development.


## Proof-local definitions

A `def` item with a return sort declares a definition local to the proof file:

```
def NAME (binders): sort = $ body $
```

Like a lemma, it is a top-level item rather than a proof line. It takes no
underline, and is available to later proof lines, lemmas, and definitions but
not before its own declaration.

```aufbau-proof prelude=nd-base,nd-rules
def nand (a b: wff): wff = $ ¬ (a ∧ b) $

lemma nand_intro (g: ctx) (a b: wff): $ g , a ∧ b ⊢ ⊥ $ > $ g ⊢ nand a b $
----
l1: $ g ⊢ nand a b $ by not_intro [#1]

lemma nand_elim (g h: ctx) (a b: wff):
  $ g ⊢ nand a b $ > $ h ⊢ a $ > $ h ⊢ b $ > $ g , h ⊢ ⊥ $
----
l1: $ h ⊢ a ∧ b $ by and_intro [#2, #3]
l2: $ g , h ⊢ ⊥ $ by not_elim [#1, l1]
```

Proof-side definitions cannot carry notation yet, which is why `nand a b` here
is written in application form where the previous version could write `a ⊼ b`.

Like ordinary definitions, proof local definitions are transparent at rule 
applications: the folded and unfolded forms are interchangeable, and each line 
can be stated in whichever form is clearer. A defined connective can be 
introduced and its rules derived without writing the expanded form anywhere but 
the definition itself.
