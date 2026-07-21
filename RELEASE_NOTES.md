# Aufbau 0.0.2

Aufbau 0.0.2 is a feature release focused on proof automation. It adds an
equality-saturation tactic, richer feedback from the existing search, and a
substantial rework of the compiler's error messages. The verifier and the
trusted kernel are unchanged: everything new lowers through ordinary proof
lines that the 0.0.1 verifier already accepts.

## Highlights

### `conversion?` — an equality-saturation tactic

A new search placeholder, `conversion?`, proves a goal by rewriting. It builds
an egraph from the goal and the surrounding proof context, saturates a set of
rewrite rules under congruence, and — when the goal becomes convertible to a
hypothesis or an earlier line — replaces the placeholder with an ordinary
proof: the rewrite chain, its congruence lifts, and a final transport. A
saturated miss is reported as a genuine negative; a run stopped by its budget
says so and suggests wider limits.

Rules come from three places:

- `@conversion` annotations enroll a hypothesis-free theorem concluding
  `rel(lhs, rhs)` for a registered `@relation`, with a direction token.
- `@conversion assoc` / `comm` role tokens certify a theorem *is* an
  operator's associativity or commutativity law. An operator with both (and
  `@congr` coverage) is absorbed into the term representation itself:
  applications intern as flattened, sorted multisets, so AC reasoning costs no
  saturation work and large conjunctions stay tractable where a plain tree
  representation blows up exponentially.
- `@conversion unfold` / `fold` / `both` on a definition enrolls its own
  defining equation, so goals split across a definition boundary close without
  a hand-written bridge. Definitions with hidden dummy binders may enroll only
  `fold`, which is sound by construction.

Local equations participate automatically: a hypothesis or earlier line of the
form `rel(lhs, rhs)` acts as a ground rewrite between its sides (the `simp [h]`
analogue), no annotation needed. With no `@conversion` rules present at all,
`conversion?` degrades to a congruence-closure prover over those local
equations.

Rules with bound binders — quantifier rules of passage, vacuous-quantifier
drops — respect their variable-dependency side conditions by construction: a
match enters the egraph only when the verifier's disjointness conditions are
satisfiable, and the emitted chain cites a representative that satisfies them.
The new `herbrand` demo fixture exercises this end to end, with prenexification
proofs generated entirely by `conversion?`.

### Richer `auto?` feedback and per-call tuning

A failed `auto?` search now explains *how* it failed: a definitive exhaustion
of the space up to the depth limit versus a truncation by the work budget or
per-phase fuel (naming the ladder phase and depth it died in), how many
candidates were validated versus accepted, and the most-tried rules. Any
search placeholder accepts per-call parameters — `auto? (depth: 8, nodes: 512,
fuel: 8192, budget: 13)` — to widen one search without moving the engine
defaults.

### Logical error messages

The compiler's diagnostics for failed rule applications were reworked to
explain failures in logical terms — which premise or conclusion region does not
line up, expected versus found shapes pretty-printed in the theory's own
notation, which constraint ruled out every remaining match, and dependency
clashes stated as constraints on variables ("bound variables x and y must be
assigned distinct variables") rather than as raw dependency bitmasks.

### `unpack` code action

The language server offers to rewrite a proof line containing inline rule
applications into separate labeled lines, one per hidden application, with each
new assertion filled in from the checked conclusion.

### Fixes

- The WebAssembly compiler escapes all string values in its JSON result, so a
  diagnostic that echoes a source token containing a JSON-special character no
  longer produces output that `JSON.parse` rejects.
- `conversion?` tree-mode matching is memory-bounded: a pathological rule set
  terminates as a capped miss instead of exhausting memory.
- Capture-unfolding of a hidden-dummy definition is rejected at compile time
  rather than producing a proof the verifier later rejects with `DepViolation`.

See the [changelog](CHANGELOG.md) for the complete list.

## Compatibility

MMB proof files produced by 0.0.1 remain valid. Proof syntax is additive: the
new annotations and search placeholders are opt-in, and existing `.mm0`/`.auf`
sources compile unchanged. Source builds still require Zig 0.15.2.

Aufbau remains pre-1.0 software; APIs and proof syntax may still change.

---

# Aufbau 0.0.1

Aufbau 0.0.1 is the first experimental release of the Aufbau Metamath Zero
verifier and proof compiler.

## Included

- `abc`, a native compiler from MM0 source and Aufbau proof scripts to MMB.
- `mm0-zig`, a native verifier for MM0/MMB proof pairs.
- WebAssembly packages for the compiler, verifier, and language server:
  `@aufbau/compiler`, `@aufbau/verifier`, and `@aufbau/lsp`.
- `@aufbau/editor`, browser custom elements for editable theories, proofs, and
  statement indexes, with local compilation and optional language-server
  support.
- The hosted [web demo](https://gleachkr.github.io/Aufbau/).

The npm WebAssembly loaders support browsers and Node. The language server's
worker transport and `@aufbau/editor` require a browser environment.

Source builds require Zig 0.15.2. See the
[README](https://github.com/gleachkr/Aufbau#readme) for build and usage
instructions.

## Status and known limitations

This is pre-1.0 software. APIs and proof syntax may change in later releases.

Aufbau is licensed under the Apache License 2.0.
