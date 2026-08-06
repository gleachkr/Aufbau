# Appendix: annotation reference

Annotations are `--|` comment lines immediately before a declaration. Each
annotation occupies exactly one line, and only one annotation is allowed per
line. In `.mm0` files they attach to the next statement; in `.auf` files they
may precede a `lemma` block, giving the local rule the same metadata as an
ordinary assertion. (Annotations on proof-side `def` items are currently
rejected.)

| Annotation | Attaches to | Purpose | Chapter |
|---|---|---|---|
| `@relation` | assertion | register an equivalence bundle for a sort | [Equality and normalization](equality-and-normalization.md) |
| `@rewrite` | assertion | enroll an oriented rewrite for the normalizer | [Equality and normalization](equality-and-normalization.md) |
| `@congr` | assertion | congruence rule for a constructor | [Equality and normalization](equality-and-normalization.md) |
| `@acui` | term | canonicalize a combiner (assoc/comm/unit/idem) | [Equality and normalization](equality-and-normalization.md) |
| `@conversion` | assertion or def | enroll an equation for `conversion?` | [Computation](computation.md) |
| `@compute` | assertion | enroll a directed computation rule for `conversion?` | [Computation](computation.md) |
| `@auto` | assertion | enroll a rule for `auto?` search | [Powering search](powering-search.md) |
| `@view` / `@recover` / `@abstract` | assertion | alternative surface shape + binder recovery | [Views and recovery](views-and-recovery.md) |
| `@vars` | sort | pool of on-demand proof variables | [Ergonomics](ergonomics.md) |
| `@fresh` / `@freshen` / `@alpha` | assertion | fresh-binder selection and alpha repair | [Ergonomics](ergonomics.md) |
| `@hole` | sort | hole token for that sort | [Holes](holes.md) |
| `@fallback` | assertion | retry a failed application with another rule | [Ergonomics](ergonomics.md) |

## Equality and normalization

### `@relation`

```text
--| @relation SORT REL REFL TRANS SYMM TRANSPORT
```

The fields name the sort, relation term, and its reflexivity, transitivity,
symmetry, and transport rules, in that order. `_` marks a missing symmetry or
transport member. The declarative annotation may sit on any assertion; by
convention it sits on the reflexivity axiom. Bundle members must use rule-form
hypotheses (`>`, not object-level implications) and have no bound binders.

```text
--| @relation wff bi biid bitr bisym mpbi
--| @relation nat nat_eq nat_eq_refl nat_eq_trans nat_eq_sym _
```

### `@rewrite`

```text
--| @rewrite
```

No arguments. The associated assertion's conclusion must be `rel lhs rhs` for a
registered relation; it is indexed by the head term of `lhs` and applied left
to right during normalization. Rules sharing a head fire in declaration
order, first match wins.

### `@congr`

```text
--| @congr
```

No arguments. Registers an assertion as the congruence rule for the head
term of its conclusion, letting normalization rewrite inside that
constructor. Binders must pair up as `old new` for each regular argument
(bound arguments appear once), and the conclusion must relate the two
applications.

### `@acui`

```text
--| @acui ASSOC COMM UNIT IDEM
```

Applied to a `term` declaration (the combiner). The four positions name the
associativity axiom, commutativity axiom, unit *term*, and idempotence
axiom; `_` marks an absent law, and the trailing `IDEM` may be omitted.
Arguments of the combiner are flattened, units dropped, sorted (when
commutative), deduplicated (when idempotent), and rebuilt, with a relation
proof emitted during `.auf` compilation for every step. Requires a `@relation`
for the result sort and a `@congr` rule for the combiner.

```text
--| @acui ctx_assoc ctx_comm emp ctx_idem
term join (g h: ctx): ctx;
```

## Computation

### `@conversion` on an assertion

```text
--| @conversion ltr|rtl|both|comm|assoc
```

Enrolls a hypothesis-free equation `rel lhs rhs` as a saturation rule for
`conversion?`. A direction token `rtl|ltr|both` picks which side is matched
(and so which new terms the e-graph may build). `comm` and `assoc` are role
certificates instead: the conclusion must be exactly that law, and an operator
certified both (with `@congr` coverage) is absorbed into the e-graph's AC
representation at no saturation cost. A rule cannot carry both `@conversion`
and `@compute`.

### `@conversion` on a definition

```text
--| @conversion fold|unfold|both
```

Enrolls the definition's own equation for `conversion?`: `fold` matches the
definiens and folds it to the head, `unfold` expands applications of the
head. Unannotated definitions are invisible to `conversion?`. A definition
with hidden dummy binders may enroll `fold` only. (Ordinary transparent-def
unfolding during line checking needs no annotation at all.)

### `@compute`

```text
--| @compute ltr|rtl
```

Enrolls a hypothesis-free equation in `conversion?`'s *directed* scheduler —
applied as a terminating, in-order fold rather than undirected saturation. This
is the appropriate enrollment for recursion equations and arithmetic tables;
see the evaluation examples in [Computation](computation.md) and [The lambda
calculus](lambda-calculus.md).

## Search

### `@auto`

```text
--| @auto forward
--| @auto backward
--| @auto eager      -- optionally: @auto eager N
--| @auto trigger (TERM child ...)
```

One mode per line; a rule may carry several lines. `forward` runs the rule
over the reference pool before backward search (elimination rules);
`backward` lets the rule apply when the goal leaves binders undetermined,
opening them as witnesses drawn from the `@vars` pool (introduction rules).
`eager` declares the rule invertible: scheduled first (priority `N` ≥ 1,
default 1, lower is earlier), committed to once applied, exempt from the
depth budget; it implies `backward` and statically requires an invertible
shape. `trigger` attaches a pattern (a parenthesized prefix tree over term
names, the rule's binder names, and `_`) matched against the goal's
subterms as a last resort to mint ground instances of a hypothesis-free
rule.

More details are available in [Powering search](powering-search.md).

## Views and binder recovery

### `@view`

```text
--| @view BINDERS : $ HYP $ > ... > $ CONCLUSION $
```

A theorem-like signature, on one line, declaring an alternative surface
shape for the rule: binders in the usual `(a: s)` / `{x: s}` forms,
hypotheses and conclusion separated by `>`. Binders whose names match rule
arguments map back to the rule arguments; the rest are phantom, view-local
slots. At most one `@view` may appear on a rule.

### `@recover`

```text
--| @recover TARGET SOURCE PATTERN HOLE
```

Four view-binder names; must follow the `@view` it refines. Walks `SOURCE`
and `PATTERN` in parallel and, where `PATTERN` reaches the resolved `HOLE`,
reads the corresponding `SOURCE` subtree off as the value of `TARGET`.

### `@abstract`

```text
--| @abstract TARGET LEFT RIGHT HOLE LEFT-PLUG RIGHT-PLUG
```

Six view-binder names; must follow a `@view`. Recovers a one-hole *context*:
walks `LEFT` and `RIGHT` in parallel, replacing occurrences of the plug pair
by `HOLE`, and binds the resulting context to `TARGET`. Several `@recover`
and `@abstract` lines may follow one `@view`; they run to a fixed point.

## Variables, freshness, and repair

### `@vars`

```text
--| @vars TOKEN TOKEN ...
sort obj;
```

On a sort declaration. Declares a pool of variable names that proofs may use
on demand. These variables are used by `@fresh`, `@freshen`, backward-search
witness invention, and hidden-dummy matching. Multiple `@vars` lines
accumulate. Not allowed on `strict` or `free` sorts.

### `@fresh`

```text
--| @fresh BINDER
```

`BINDER` is a *bound* binder of the rule. When the binder is omitted at a
citation, the compiler selects a variable from the binder sort's `@vars`
pool (preferring one that does not occur in the goal) before inference runs.
An explicit binding always overrides it.

### `@freshen`

```text
--| @freshen TARGET-ARG BLOCKER-BINDER
```

`TARGET-ARG` is a regular argument and `BLOCKER-BINDER` is a bound binder of
the rule. Marks the pair as eligible for alpha-renaming repair when a
dependency (capture) check blocks the application; the repair renames the
blocker inside the target via a matching `@alpha` rule and a `@vars` pool
variable.

### `@alpha`

```text
--| @alpha OLD NEW
axiom all_alpha {x y: obj} (p: wff x y): $ ∀ x p ↔ ∀ y ([x/y] p) $;
```

`OLD` and `NEW` are bound binders of the same sort on a hypothesis-free
equivalence. Registers the rule as the alpha-renaming lemma for its head term,
consumed only by the `@freshen` repair path.

## Holes and fallbacks

### `@hole`

```text
--| @hole TOKEN
provable sort wff;
```

Occurs on a sort declaration, at most one per sort. Registers `TOKEN` as the
hole marker for that sort: each occurrence in proof math is a fresh,
independent hole that inference must solve. See [Holes](holes.md).

### `@fallback`

```text
--| @fallback RULE
```

`RULE` names an earlier rule. At most one `@fallback` may appear on a rule. If
the annotated rule's application fails, the compiler retries the entire
application with the named rule and follows fallback chains recursively. A
theory can therefore expose one name for a family of rule variants.
