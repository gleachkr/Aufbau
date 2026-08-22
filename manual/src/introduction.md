# Introduction

Aufbau is a verifier and compiler for Metamath Zero (MM0), a language for
formally checked mathematics. An MM0 theory declares its sorts, term
constructors, and axioms. Proofs state what follows from that theory, and a
small verification kernel checks each result.

This manual is interactive. Each proof cell runs the Aufbau compiler in 
WebAssembly and checks edits as you type. The opening chapters cover proof 
lines, built-in search, and larger proofs. The next two parts describe MM0, the 
theory language, and `.auf`, Aufbau's proof language. Later parts explain 
theory design, develop several worked theories, and document the command-line 
and embedding tools.
