# Introduction

Aufbau is a verifier and compiler for Metamath Zero (MM0), a language for
writing formally checked mathematics. You write a theory — sorts, term
constructors, axioms — and then proofs against it. A small, auditable kernel
checks that every proof really does follow from the axioms.

This manual is interactive. The proof editor is embedded directly in the page: 
the boxes below are not screenshots. They are the real editor running the 
Aufbau compiler in WebAssembly and checking as you type.

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

Try breaking it. Change the last `p` on the proof line to `q`, so the line
claims `p -> (q -> q)` — the axiom no longer fits that shape, and the cell
will tell you so. Put it back and it checks cleanly again.

The rest of this manual builds from here. The first part stays in the browser 
and demonstrates basic proof writing: reading and writing proof lines, 
letting the built-in search fill in steps, and organizing larger proofs. The 
two parts after that teach the languages properly — MM0, the theory language, 
and `.auf`, the proof language — assuming no prior acquaintance with either. 
Later parts cover designing your own theories, the automation in depth, a tour 
of worked theories, and the command-line and embedding tools.
