# Introduction

Aufbau is a verifier and compiler for Metamath Zero (MM0), a language for
formally checked mathematics. An MM0 theory declares its sorts, term
constructors, and axioms. Proofs state what follows from that theory, and a
small verification kernel checks each result.

This manual is interactive. Its proof cells are not screenshots: each one runs
the Aufbau compiler in WebAssembly and checks edits as you type.

Here is a complete, checked proof to start with. It works in a tiny fragment
of propositional logic: implication, and the *weakening* axiom `h1`, which
says that a true statement is implied by anything.

```aufbau-proof
@@mm0
delimiter $ ( ) $;
provable sort wff;
term imp (a b: wff): wff; infixr imp: $->$ prec 25;
axiom h1 (a b: wff): $ a -> (b -> a) $;
@@auf
lemma weaken (p q: wff): $ p -> (q -> p) $
----
l1: $ p -> (q -> p) $ by h1
```

The theory this cell is checked against declares a sort `wff` of
propositions, an implication constructor written infix as `->`, and the
axiom `h1`, stated for any two propositions `a` and `b`. The proof is a
lemma named `weaken` with one line: it states the goal between `$` signs
and cites the axiom with `by h1`. The compiler works out for itself that
the axiom's `a` must be our `p` and its `b` our `q`.

Try changing the last `p` on the proof line to `q`. The line will claim
`p -> (q -> q)`, which no longer matches the axiom, and the cell will report
an error. Restore the `p` to make the proof check again.

The opening chapters cover proof lines, built-in search, and larger proofs.
The next two parts describe MM0, the theory language, and `.auf`, Aufbau's
proof language. Later parts explain theory design, develop several worked
theories, and document the command-line and embedding tools.
