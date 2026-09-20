# Appendix: grammar summaries

Condensed grammars for the two source languages. The MM0 grammar is fixed by
the upstream [Metamath Zero
specification](https://github.com/digama0/mm0/blob/master/mm0.md); the `.auf`
grammar is this project's proof-script format.

## MM0 lexical structure

```text
file          ::= (lexeme | whitespace)*
line-comment  ::= '--' [^\n]* '\n'
lexeme        ::= symbol | identifier | number | math-string
symbol        ::= '*' | '.' | ':' | ';' | '(' | ')' | '>' | '{' | '}' | '=' | '_'
identifier    ::= [a-zA-Z_][a-zA-Z0-9_]*
number        ::= 0 | [1-9][0-9]*
math-string   ::= '$' [^\$]* '$'
```

Comments starting `--|` are *annotation comments*: Aufbau attaches them to the
next statement, as metadata when the line starts with `@` (`@relation`,
`@rewrite`, `@auto`, …) and as a doc comment otherwise. See the
[annotation reference](appendix-annotations.md).

## MM0 statements

```text
mm0-file      ::= (statement)*
statement     ::= sort-stmt | term-stmt | assert-stmt | def-stmt
                | notation-stmt

sort-stmt     ::= ('pure')? ('strict')? ('provable')? ('free')?
                  'sort' identifier ';'

term-stmt     ::= 'term' identifier (type-binder)* ':' arrow-type ';'
type          ::= identifier (identifier)*
type-binder   ::= '{' (identifier)* ':' type '}'
              |   '(' (identifier_)* ':' type ')'
arrow-type    ::= type | type '>' arrow-type

assert-stmt   ::= ('axiom' | 'theorem') identifier
                  (formula-type-binder)* ':' formula-arrow-type ';'
formula-type-binder ::= '{' (identifier)* ':' type '}'
                      | '(' (identifier_)* ':' (type | formula) ')'
formula-arrow-type ::= formula | (type | formula) '>' formula-arrow-type
formula       ::= math-string

def-stmt      ::= 'def' identifier (dummy-binder)* ':' type
                  ('=' formula)? ';'
dummy-binder  ::= '{' (dummy-identifier)* ':' type '}'
              |   '(' (dummy-identifier)* ':' type ')'
dummy-identifier ::= '.' identifier | identifier_
```

Curly binders `{x: s}` are bound (binding) variables; parenthesized binders
`(a: s)` are regular variables, with trailing identifiers in the type naming
the bound variables the term may depend on. `.`-prefixed binders on a `def`
are hidden dummy variables. A `def` without `= $ ... $` leaves its body to
be supplied by the `.auf` file. See [Sorts and terms](sorts-and-terms.md)
and [Variables, binders, and dependencies](variables-and-binders.md).

```text
notation-stmt        ::= delimiter-stmt | simple-notation-stmt
                       | coercion-stmt | gen-notation-stmt
delimiter-stmt       ::= 'delimiter' math-string math-string? ';'
simple-notation-stmt ::= ('infixl' | 'infixr' | 'prefix') identifier ':'
                         constant 'prec' precedence-lvl ';'
precedence-lvl       ::= number | 'max'
coercion-stmt        ::= 'coercion' identifier ':' identifier '>' identifier ';'
gen-notation-stmt    ::= 'notation' identifier (type-binder)* ':' type '='
                         (notation-literal)+ ';'
notation-literal     ::= '(' constant ':' precedence-lvl ')' | identifier
```

See [Notation](notation.md) for how precedence and delimiters interact.

## The .auf language

An Aufbau script is a sequence of theorem blocks, lemma blocks, def items,
notation items, and include statements, in the same order as the 
corresponding `.mm0` declarations (see [Proof blocks and 
lines](proof-blocks-and-lines.md)):

```text
aufbau-script ::= (theorem-block | lemma-block | def-item | notation-item
                  | include | blank | comment)*

include       ::= 'include' '"' path '"' ';'     -- at the start of a line

theorem-block ::= theorem-name newline underline newline* proof-line*
underline     ::= '-' '-' '-'* newline          -- at least 3 dashes

lemma-block   ::= annotation-comment* 'lemma' identifier lemma-binders? ':'
                  formula ('>' formula)* newline underline newline*
                  proof-line*

def-item      ::= public-body-filler | local-def
public-body-filler ::= 'def' identifier dummy-group* '=' math-string
dummy-group   ::= '(' ('.' identifier)+ ':' sort ')'
local-def     ::= 'def' identifier binder* ':' sort '=' math-string

notation-item ::= prefix-stmt | infix-stmt | notation-stmt   -- MM0 syntax, ';' included
```

Lemma binders use the same syntax as MM0 assertions. The presence of a
top-level `: sort` return annotation is what distinguishes a proof-local
definition from a public body filler ([Lemmas and definitions in
proofs](lemmas-defs-in-proofs.md)). A notation item is an MM0 `prefix`,
`infixl`, `infixr`, or `notation` statement naming a proof-local
definition. `coercion` and `delimiter` statements are not accepted. An
include statement is replaced by the text of the designated file before parsing 
([Theories in several
files](install-and-run.md#theories-in-several-files)).

## Proof lines

```text
proof-line   ::= label ':' formula 'by' rule-application newline*

rule-application ::= rule-name ('(' arg-bindings ')')? ('[' refs ']')?

arg-bindings ::= empty | arg-binding (',' arg-binding)*
arg-binding  ::= binder-name ':=' formula
             |   param-name ':' number        -- search parameters only

refs         ::= empty | ref (',' ref)*
ref          ::= hyp-ref | line-ref | inline-application
hyp-ref      ::= '#' number | '#' identifier
line-ref     ::= identifier
inline-application ::= rule-application
```

Notes:

- Whitespace, newlines, and `--` comments are interchangeable separators
  inside a proof line; a new line must still start with its label.
- An omitted `[...]` is an empty reference list; the reference count must
  match the cited rule's hypothesis count.
- A bare identifier in a reference list is always a line reference, so a
  zero-hypothesis inline application needs its delimiter: `keep [top_i []]`.
- `rule-name` may also be a search command (`exact?`, `apply?`, `auto?`,
  `conversion?`); the `name: number` parameter form is accepted only there
  ([search parameters](appendix-search-parameters.md)).
- On a proof line, `rule-name` may be `sorry!`, which admits the goal with no
  bindings or references ([Admitting a
  line](proof-blocks-and-lines.md#admitting-a-line)). It is not accepted as
  an inline application.
- `$ ... $` formulas may contain `@hole` tokens where the theory declares
  them ([Holes](holes.md)).
