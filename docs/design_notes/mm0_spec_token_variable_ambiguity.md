# MM0 spec: token-vs-variable resolution is underspecified (issue draft)

Draft text for a GitHub issue against the MM0 spec (`metamath/mm0`, `mm0.md`).
Not part of the Aufbau build; kept here so it can be copied out and posted.

---

**Title:** Secondary parsing is ambiguous when a notation constant token equals an in-scope variable name

**Summary.** The "Secondary parsing" grammar does not specify how a math-string
token is resolved when it is *both* a declared notation constant token *and* the
name of an in-scope variable (binder). Two `expression(max)` productions apply,
and the notation-unambiguity rules only rule out constant-vs-constant clashes —
not constant-vs-variable. Independent verifiers resolve it in opposite
directions (one rejects a file the other accepts), so the well-formedness of
such a file is implementation-defined.

**Minimal example.**
```
provable sort wff;
sort obj;
term bi (a b: wff): wff;
infixl bi: $<->$ prec 20;
term cc: obj;
notation cc: obj = ($c$:max);   -- declares `c` as a token for the constant `cc`
axiom biid (a: wff): $ a <-> a $;
axiom bitr (a b c: wff):        -- binder `c` (a wff) has the same name as token `c`
  $ a <-> b $ > $ b <-> c $ > $ a <-> c $;
```
In `bitr`'s formulas, does `c` denote the **binder** `c` (sort `wff`) or the
**constant** `cc` (sort `obj`)?

**Where the grammar is silent.** The relevant `expression(max)` productions are:
```
expression(max) -> VAR      (if VAR is a variable in scope)
expression(max) -> c        (nullary notation: notation cc: obj = ($c$:max))
```
Both are applicable to the token `c` here. The unambiguity rules under
"Notations" constrain only constants relative to *other constants* ("the first
token of a `notation` must be a constant, and must not be shared with any other
prefix constant or infixy constant"); nothing forbids a constant token from
coinciding with a **variable name**, nor states a precedence between the two
productions. The lexer rule `math-symbol ::= OP (if OP appears in a
infix/prefix/notation declaration)` and `math-lexeme ::= math-symbol |
identifier` likewise don't state a tiebreak for a token that is simultaneously a
declared symbol and a valid identifier naming an in-scope variable.

**Observed divergence.**
- **mm0-c** treats `c` as the constant `cc` → `bi(a, cc)` is ill-typed (an `obj`
  in a `wff` position) → **rejects** the file.
- **mm0-zig** (Aufbau) checks in-scope variables first → treats `c` as the
  binder → **accepts** the file (and emits a well-typed proof object that mm0-c,
  fed a source with the token renamed, then accepts — i.e. the emitted object is
  fine; only the source parse differs).

So the same `.mm0` is well-formed for one verifier and ill-formed for another.

**Proposed resolutions (pick one, please clarify in the spec):**
1. **Ill-formed:** a declared notation token must not coincide with the name of
   any variable in scope where it could be parsed. Verifiers must reject. (This
   is the least surprising — it turns a silent divergence into an error.)
2. **Token wins:** a declared token is always lexed as the constant, shadowing
   any same-named variable (the variable becomes unreferenceable). Matches the
   two-phase lexer reading and mm0-c's current behavior.
3. **Variable wins:** an in-scope variable name takes precedence over a
   same-named constant token.

Either explicit rule removes the ambiguity; (1) or (2) match the conventional
"declared operators shadow identifiers" behavior of two-phase notation lexers.
