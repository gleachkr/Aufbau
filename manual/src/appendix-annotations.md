# Appendix: annotation reference

Annotations are `--|` comment lines immediately before a declaration. Each
annotation occupies exactly one line, and only one annotation is allowed per
line. In `.mm0` files they attach to the next statement; in `.auf` files they
may precede a `lemma` block, giving the local rule the same metadata as an
ordinary assertion. (Annotations on proof-side `def` items are currently
rejected.)

A `--|` line that does not start with `@` is a *doc comment*. Doc lines and
annotations may be mixed in any order; consecutive doc lines form one
paragraph, and an empty `--|` line starts a new one. The doc comment is shown
when the declaration's name is hovered, and in completion lists. Backticks
mark code spans; other markdown is shown as written.

```text
--| Existential introduction: a formula proved of a particular term
--| `t` holds of something.
--| @auto backward
axiom ex_intro {x: obj} (g: ctx) (t: obj x) (p: wff x):
  $ g ⊢ [x := t] p $ > $ g ⊢ ∃ x p $;
```

This is the same doc-comment convention as mm0-rs, so tools that read MM0
files without Aufbau's annotations still show the text.

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

No arguments. The associated assertion's conclusion must be `rel lhs rhs`
for a registered relation; it is indexed by the head term of `lhs` and
applied left to right during normalization. Rules with the same head are
tried in declaration order; the first matching rule applies.

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
--| @conversion ltr|rtl|both|comm|assoc|alpha
```

Registers an equation `rel lhs rhs` for saturation in `conversion?`. `ltr`,
`rtl`, and `both` select the direction of matching. A rule may have
hypotheses, which must already be established in the e-graph before it
applies. The matched side must determine every binder used in the other side
or in a hypothesis.

`comm` and `assoc` identify commutativity and associativity laws. With both
annotations and a `@congr` rule, search represents nested applications as
multisets rather than exploring each ordering and grouping.

`alpha` registers a renaming equation such as `rel (all x p) (all y (sb x y
p))`. Search applies it between existing expressions with the same binding
constructor, taking the new binder from the other expression. The
substitution rules needed to reduce the renamed body must also be registered
for conversion. Nested renaming proceeds from the outside inward and needs
substitution rules that move under each relevant binder, such as `sb x a
(all y p)` to `all y (sb x a p)`.

A rule cannot carry both `@conversion` and `@compute`.

### `@conversion` on a definition

```text
--| @conversion fold|unfold|both
```

Enrolls the definition's own equation for `conversion?`: `fold` replaces an
instance of the body with the defined term; `unfold` replaces the defined
term with its body. Unannotated definitions are invisible to `conversion?`.
A definition with hidden dummy binders may enroll `fold` only. (Ordinary
transparent-def unfolding during line checking needs no annotation at all.)

### `@compute`

```text
--| @compute ltr|rtl
```

Registers a hypothesis-free equation for directed computation in
`conversion?`. Rules apply in declaration order rather than by general
saturation. The annotation does not guarantee termination. This is the
appropriate enrollment for recursion equations and arithmetic tables; see
the evaluation examples in [Computation](computation.md) and [The lambda
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
`backward` allows unresolved binders to remain as metavariables while search
proves premises. If a successful proof still needs an arbitrary witness,
search chooses one from the `@vars` pool.

`eager` marks a rule as invertible. Search tries it first, commits to it
once applied, and does not count its applications toward the depth limit.
The optional priority `N` is at least 1, defaults to 1, and runs earlier
when smaller. It implies `backward`. The compiler checks that premises use
only binders present in the conclusion, but cannot verify invertibility.

`trigger` supplies a parenthesized prefix pattern over term names, rule
binders, and `_`. As a last resort, search matches it against subterms of
the goal to create fully instantiated facts from a hypothesis-free rule.

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

Four view-binder names and two plugs; must follow a `@view`. Each plug is
a view-binder name or a `$ … $` pattern over the view binders. Recovers a
surrounding expression, or *context*, with one variable marking replacement
positions. It compares `LEFT` and `RIGHT`, replaces each occurrence of the
plug pair with `HOLE`, and assigns the result to `TARGET`; binders solved by
a pattern are assigned as well. Several `@recover` and `@abstract` lines may
follow one `@view`; they run to a fixed point.

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
