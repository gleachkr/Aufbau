# Proof blocks and lines

An `.auf` file supplies the proofs for the theorems declared in an `.mm0`
file. The Proving chapters introduced proof scripts by example; this part of
the manual describes the format itself. An `.auf` file is a sequence of
top-level items: *proof blocks*, which prove the declared theorems, plus the
`lemma` blocks and `def` items described in [Lemmas and definitions in
proofs](lemmas-defs-in-proofs.md). This chapter covers proof blocks and the
exact form of a proof line.

## Declaration and proof ordering

The compiler reads the `.mm0` and `.auf` files together, in statement order.
Each theorem declaration in the `.mm0` file must be proved by the next
theorem proof block in the `.auf` file.

```aufbau-proof doc=blocks
@@mm0
delimiter $ ( ) $;
provable sort wff;
term imp (a b: wff): wff; infixr imp: $->$ prec 25;
axiom h1 (a b: wff): $ a -> (b -> a) $;
axiom mp (a b: wff): $ a $ > $ a -> b $ > $ b $;
theorem weaken (p q: wff): $ p $ > $ q -> p $;
theorem weaken_twice (p q r: wff): $ p $ > $ q -> (r -> p) $;
@@auf
weaken
----
l1: $ p -> (q -> p) $ by h1
l2: $ q -> p $ by mp [#1, l1]

weaken_twice
----
l1: $ r -> p $ by weaken [#1]
l2: $ (r -> p) -> (q -> (r -> p)) $ by h1
l3: $ q -> (r -> p) $ by mp [l1, l2]
```

Proof blocks must appear in the same order as the corresponding theorem 
declarations. If the two blocks above are swapped, the compiler finds 
`weaken_twice` where it expects `weaken` and rejects the file.

Declaration order also determines what a proof may cite: any axiom, any public
theorem already proved, and any earlier lemma or proof-local definition.
`weaken_twice` cites `weaken` this way. Later declarations in either file are
not visible, so forward references are rejected.

## Proof blocks

A proof block is the theorem's name, an underline, and the proof lines. The
underline appears on the line immediately after the name and consists of at
least three dashes, with nothing else on it. The block extends to the next
top-level item or to the end of the file. Blank lines within a block are
ignored.

## Proof lines

Each line has the form introduced in
[The parts of a proof line](proof-line.md):

```
label: $ GOAL $ by rule (bindings) [references]
```

Lines are checked in order. Each line is an application of the cited rule. Once
a line checks, its label names the proved goal for the rest of the block.
Labels must be unique within their block.

Each rule must be an axiom, public theorem, or lemma in scope, and the
bracketed list must supply exactly as many references as the rule has
hypotheses — omitting the brackets is the same as writing `[]`. Rule references
and bindings are the subject of the next chapter.

## Admitting a line

A line may be justified by `sorry!` instead of a rule. The goal is accepted
without proof, and the block is otherwise checked as usual: later lines may
cite the admitted line, and the last line must still match the declared
conclusion.

```aufbau-proof
@@mm0
delimiter $ ( ) $;
provable sort wff;
term imp (a b: wff): wff; infixr imp: $->$ prec 25;
axiom mp (a b: wff): $ a $ > $ a -> b $ > $ b $;
theorem admitted (p q: wff): $ p $ > $ q $;
@@auf
admitted
----
l1: $ p -> q $ by sorry!
l2: $ q $ by mp [#1, l1]
```

The compiler reports a warning at each `sorry!` and, from the command line,
exits with status 3 after writing the output. The MMB carries a `Sorry`
instruction at that line only, so the verifier checks every other step; it
names each admitted theorem and exits with status 3 as well. `sorry!` takes
no bindings or references, and its goal may not contain holes.

## Layout and comments

Within a proof line, line breaks may fall before or after `by`, inside binding
and reference lists, or inside math strings. A new proof line must begin on a
fresh line with its label.

A `--` comment runs to the end of the line. Comments may stand alone between
blocks and between proof lines, follow a header or a proof line, and interrupt
a line that spans several physical lines. The underline is the exception: it
must include nothing but dashes.

```aufbau-proof doc=blocks
lemma spread (p q r: wff): $ p $ > $ q -> (r -> p) $
----
-- A standalone comment between lines.
l1: $ r -> p $
  by weaken [#1]
l2: $ (r -> p) -> (q -> (r -> p)) $ by h1  -- trailing on a line
l3: $ q -> (r -> p) $
  -- a comment may interrupt a line
  by mp [l1, l2]
```

Comments beginning with `--|` are *annotation comments*. They can be used to
attach rule metadata — `@rewrite`, `@view`, and the annotations in the
[annotation reference](appendix-annotations.md) — to the item that follows, just
as in an `.mm0` file. In an `.auf` file they
may only precede `lemma` blocks; a public theorem's metadata belongs on its
`.mm0` declaration, not on its proof block. A `--|` line that does not start
with `@` is a doc comment, shown when the item's name is hovered; those may
precede any item. A standalone `--|` line also ends
the current block, so it may be written directly after the last line of the
preceding proof.

## Proof conclusions

A block is accepted only if its final line proves the theorem's declared
conclusion. Proving that conclusion on an earlier line is not enough. The
final line need not use exactly the same expression as the declaration: the
compiler can expand definitions and apply registered normalization rules to
match them. It includes the necessary conversion steps in the binary proof.
Lemma blocks are checked against their headers in the same way.
