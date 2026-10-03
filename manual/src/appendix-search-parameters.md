# Appendix: search parameters

This appendix lists proof-search commands and their parameters. [Proof
search](proof-search.md) explains how to use them;
[Computation](computation.md) covers `conversion?` in detail.

## The search commands

| Command | What it does |
|---|---|
| `exact?` | Close the goal with **one** rule application whose hypotheses are all discharged by existing references (theorem hypotheses, earlier lines). |
| `apply?` | List rules whose conclusions match the goal, even if some hypotheses are not available. |
| `auto?` | `exact?` plus recursive generation of missing sub-proofs, under iterative deepening and a work budget. Builds proofs from rule applications. |
| `conversion?` | Equality saturation: is the goal convertible, by `@conversion`/`@compute` rewrites and local equations, to a hypothesis, earlier line, or instance of a reflexivity law? |

A search command can be used on a proof line after `by`, or inside a reference
slot (`by mp [auto?, #1]`). `conversion?` can only be accepted on top-level
proof lines, and only with a concrete goal (no holes).

Search commands run in the editor and language server, which report the found
proof as a suggestion. Batch compilation (`abc compile`) rejects proof scripts
that contain unexpanded search commands.

## Parameter syntax

Parameters go in the same parenthesized list as explicit bindings, as `name:
INTEGER` entries (a plain colon, rather than `:=` for bindings). The two
kinds can be mixed:

```
l1: $ c $ by auto? (depth: 8, fuel: 8192)
l2: $ c $ by rule1 [auto? (t := $ k $, nodes: 400)]
```

Unknown names and out-of-range values are reported and skipped. If a name is
repeated, the last occurrence wins.

## `auto?` parameters

| Parameter | Default | Range | Meaning |
|---|---|---|---|
| `depth` | 6 | 1–64 | Iterative-deepening limit: maximum nesting of *generated* proof steps. `@auto eager` steps are exempt. Deepening stops at the shallowest depth that closes the goal, but the most expensive search phases go past depth 1 only after every depth has missed, so a higher limit can spend the work budget before they find a deeper proof. |
| `nodes` | 256 | 1–1 000 000 | Budget of distinct generated sub-goal solves per pass (one depth of one search phase), reset at each pass. |
| `fuel` | 4096 | 1–100 000 000 | Candidate-validation budget per search phase |
| `budget` | ≈6 | 0–100 000 | Whole-call cap on cost-weighted work, in units of roughly one second of search effort (the default is 6.3 units). `budget: 0` is legal and disables the cap entirely. |

When `auto?` fails, the failure report names every limit it hit and suggests
one retry that raises them together with the budget, e.g.
`auto? (nodes: 512, fuel: 8192, budget: 14)`. Editors offer the same retry as a
**Retry with …** code action. Start from that suggestion: the limits share one
work budget, so raising one of them alone rarely helps.

## `conversion?` parameters

| Parameter | Default | Range | Meaning |
|---|---|---|---|
| `iters` | 16 | 1–10 000 | Saturation rounds (match → instantiate → rebuild). Saturation stops early the moment the goal joins a reference's class, so a hit does not pay the full count. |
| `nodes` | 10 000 | 1–1 000 000 | Cap on distinct term shapes the e-graph may hold. |

`nodes` has command-specific units: sub-goals for `auto?`, and e-graph nodes
for `conversion?`.

## `exact?` and `apply?`

`exact?` and `apply?` take no search parameters.

## What search reads from the theory

The searches can be controlled by annotations in the `.mm0` file: `@auto
forward` / `backward` / `eager` / `trigger` enroll rules for `auto?` (see
[Powering search](powering-search.md)), `@conversion` and `@compute` enroll
equations for `conversion?` (see [Computation](computation.md)), and `@vars`
supplies a witness pool. The per-invocation parameters above only decide how
much work those enrollments are allowed to do.
