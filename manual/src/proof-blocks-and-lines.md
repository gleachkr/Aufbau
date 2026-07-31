# Proof blocks and lines

An `.auf` file supplies the proofs for the theorems declared in an `.mm0`
file. The Proving chapters introduced proof scripts by example; this part of
the manual describes the format itself. An `.auf` file is a sequence of
top-level items: *proof blocks*, which discharge the declared theorems, plus
the `lemma` blocks and `def` items of Chapter 11. This chapter covers proof
blocks and the exact shape of a proof line.

## Declaration and proof ordering

The compiler reads the `.mm0` and `.auf` files together, in statement order.
Each theorem declaration it reaches in the `.mm0` file must be discharged by
the next proof block in the `.auf` file.

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

Because checking is a single pass over both files, blocks must appear in the
order of the declarations they discharge. If you swap the two blocks above, the
the first will be rejected, because you've changed the ordering by putting a 
block named `weaken_twice` where `weaken` was expected.

The declaration order determins what a proof may cite: any axiom, any public 
theorem that has already been proved, and any earlier lemma or proof-local
definition. `weaken_twice` cites `weaken` this way. Nothing later in either
file is visible, and forward references are rejected.

## Proof blocks

A proof block is the theorem's name, an underline, and the proof lines. The
underline appears on the line immediately after the name and consists of at
least three dashes, with nothing else on it. The block extends to the next
top-level item or to the end of the file. Blank lines within a block are 
ignored.

## Proof lines

Each line has the form introduced in Chapter 2:

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

## Layout and comments

Within a proof line, line breaks may fall before or after `by`, inside binding 
and reference lists, and even inside math strings. However, new proof line must 
begin on a fresh line with its label.

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
attach rule metadata — `@rewrite`, `@view`, and the other annotations of Part 5 
— to the item that follows, just as in an `.mm0` file. In an `.auf` file they 
may only precede `lemma` blocks; a public theorem's metadata belongs on its 
`.mm0` declaration, not on its proof block. A standalone `--|` line also ends 
the current block, so it may be written directly after the last line of the 
preceding proof.

## Proof conclusions

A block is accepted only if its final line proves the theorem's declared
conclusion, so a conclusion proved on an earlier line must still be the last
line's goal. The match need not be verbatim: a final line that differs from
the declaration only by transparent definitions or by registered normalization 
is reconciled automatically, with the compiler emitting the bridging conversion 
steps itself. Lemma blocks are checked the same way against their own headers.
