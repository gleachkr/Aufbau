# Inline `auto?` generation: the open-slot-goal existential gap

Status: **known limitation, intentionally deferred.** Inline `auto?` generation
is implemented for *concrete* slot goals
(`appendInlineGeneratedApplications` in `src/frontend/compiler/search/source.zig`).
A slot whose *own goal* is an undetermined rule argument stays exact-only.

## Background: what inline `auto?` generation does

An `auto?` in an argument position — e.g. `mp [auto?, #1]` — used to degrade to
`exact?` for that slot: it would find a single rule/ref matching the slot goal
but never synthesize a sub-proof for an unmet hypothesis. It now layers the same
bounded recursive generation the top-level path uses on top of the direct
results, so `qr [auto?]` (slot goal `Q`) can generate `pq [p []]`, and deeper
chains compose (`rx [auto?]` → `qr [pq [p []]]`).

This includes the existential-metavar path **when the existential arises inside
the generated sub-proof**. If the slot goal `R` is concrete and is proved by a
rule with an argument the conclusion does not pin — `r2 (a: wff): a > Q > R` —
`generateTopLevel` opens `a` as an existential meta and grounds it internally
(from a ref or the `@vars` pool), exactly as it does for a top-level goal. The
slot goal being concrete is all that is required. Covered by the unit test
`inline auto grounds an existential meta inside a slot`.

## The gap: an open *slot goal*

The unsupported case is different: the **slot's own goal** is a bare metavar,
because the outer rule leaves that argument undetermined by its conclusion and
its sibling refs. Concretely:

```
r2 [auto?, #1]
```

Here the first slot is `r2`'s hypothesis `a`, and `a` is not pinned by `R` (the
line goal) or by the sibling `#1` (which fills `Q`). So the slot goal is the
metavar `a` itself — "prove *any* fact and use it as `a`". This is exactly the
`has_placeholder == true` branch of `expectedGoalForInlineTarget`: the query
built for the slot embeds a placeholder leaf for the unbound argument.

Inline generation skips this case. The gate in `inlineExactSuggestions` runs
generation only when `!expected.has_placeholder`; an open slot goal falls back
to the direct exact search alone.

## Why it is gated off

`generateTopLevel` accepts only `.concrete` goals — `.holey` and
`.implicit_whole_conclusion` return empty (the "Step 4" deferral in
`src/frontend/compiler/search/generate.zig`). The placeholder that
`instantiateTemplateQuery` mints for an unbound slot argument is a `.standard`
(rigid) placeholder, not a solvable `.meta`/`.existential` one, so even if it
were handed to the generator it would match nothing.

Closing the gap is therefore not a one-line change: it requires building the
slot goal with **one shared `.existential` meta per unbound binder** — the same
representation the top-level open-backward path uses
(`instantiateTemplateHoleyState` / `placeholder_factory` in
`src/frontend/compiler/inference/open_terms.zig`, "one shared existential meta
per binder") — and passing it as a `.concrete` goal that embeds those metas,
which `generateTopLevel` currently would need to be taught to accept and search.
It is **not** the `.holey`/`@hole` representation (a trusted `Expr` with `.hole`
leaves); that is a separate mechanism that the generation path does not consume.

Soundness is not the blocker — every generated candidate is validated against
the reconstructed whole line (`validateReplacementApplication`) before it is
offered, which would reject any inconsistent grounding — so this is a
completeness/plumbing gap, not a correctness one.

## Deciding whether to close it

The open-slot-goal pattern (`[auto?, …]` on a slot the outer rule leaves free)
is a rare authoring shape, and the change is more speculative than the concrete
case (meta-in-goal generation, rendering the grounded witness). Deferred until
there is a concrete use for it.

## Pointers

- Gate + implementation: `appendInlineGeneratedApplications` and its caller in
  `src/frontend/compiler/search/source.zig`.
- Tests: `src/frontend/compiler/search/tests.zig` — `auto_inline_mm0` fixture and
  the `inline auto …` tests.
- Related: the top-level open path in `auto_open_mm0`
  (`auto grounds an open hypothesis from a ref and generates a sibling`).
