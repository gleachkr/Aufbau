# Fuzzing

The fuzz targets live in `tests/fuzz/` and run on Zig's built-in fuzzer.
Each target turns the fuzzer's choices into an input for one part of the
toolchain and checks what comes back:

| Target | Input | Must hold |
|---|---|---|
| `compile` | a proof case with edits to its `.mm0`, its `.auf`, or both: tokens, lines, statements and blocks, brackets wrapped around runs | whatever compiles passes the trusted verifier, which admits exactly the statements `by sorry!` warned about; a failed compile has a diagnostic for its error; the editor's analysis reports an error exactly when the compile fails |
| `kernel` | a proof case's `.mm0` with the binary this compiler makes for it, or the upstream tutorial pair (built by mm0-rs); the binary gets raw edits (bytes, words, cuts, copies) or structured ones (a header or table field, or one proof or unify command: its opcode, its operand, dropped or repeated), and the spec may get token edits | the verifier rejects bad input with an error; a changed pair it accepts must pass mm0-c too, when `mm0-c` is on PATH |
| `lsp` | a language-server session over lsp-kit's own message loop: initialize with a random position encoding, open a proof case (maybe edited), then up to 32 events (insertions, deletions, whole-document replacements, typing a token a character at a time, hover, completion, definition, implementation, references, symbols, code actions, applying a returned code action's edit, closing, reopening, malformed messages) | every server message is JSON; a well-formed request never fails; every returned range lies inside its document, on a code-point boundary of the negotiated encoding |
| `search` | a proof case that compiles cleanly, with up to three proof steps (whole lines or inline sub-proofs, on lines without holes) replaced by `auto?`, `exact?`, `apply?` or `conversion?`, searched by the driver behind `abc search` with a small work budget | no marker's search fails; every suggestion comes back trimmed; each found proof in place of its marker, and the original proof back where none was found, compiles and verifies |
| `shapes` | a generated pair of one shape at a fuzzer-chosen size: deep inline proofs, parentheses, prefix operators, conclusions grown behind holes, nested definitions, doubling chains (on holes, holey shapes, inline, through a definition), an ACU context of identical members | the `compile` oracles; too deep is a diagnostic, never a signal; time and memory stay within the limits at any size; a shape valid by construction compiles while it is small |
| `theory` | a generated theory: sorts, terms with random arities and infix or prefix notations, definitions, axioms with hypotheses, and theorems that are substitution instances of the axioms, proved in one step with some bindings left to inference | the `compile` oracles, and every pair compiles, since each is valid by construction; the binary also passes mm0-c when it is on PATH |

Every target must also not panic, leak, write after free, run longer than
10 seconds on one input, or hold more than 1 GiB at once. The fuzzer checks
the first three. `tests/fuzz/harness.zig` adds a watchdog thread and a
capped allocator for the last two, and both panic so the fuzzer saves the
input like any other crash. A few known costs would trip the time limit at
large sizes; the `shapes` target keeps those shapes small until the tasks
named in `tests/fuzz/shapes.zig` fix them.

The targets that edit proof cases seed from every case under
`tests/proof_cases/` that joins, with `import`s and `include`s already
joined into single texts.

## Running

```text
zig build fuzz                       # each target once, as a smoke check
zig build fuzz --fuzz=100K           # fuzz for 100K inputs per target
zig build fuzz --fuzz                # fuzz until stopped, with a web UI
zig build fuzz --fuzz -Dfuzz-target=compile
```

`zig build test-unit` runs the same smoke check.

Fuzz at Debug (the default), ReleaseSafe or ReleaseFast. Debug and
ReleaseSafe keep the safety checks and run at about the same speed, roughly
30–35 inputs a second on `compile`. ReleaseFast is about twice as fast but
cannot catch out-of-bounds or overflow. The fuzz build uses LLVM even at
Debug, because the self-hosted backend has no fuzzing instrumentation.

A ReleaseSafe fuzz build on Zig 0.17 can hang in LLVM's CodeGen Prepare
pass on a long unrolled chain of string compares, such as an `inline for`
over a large error set that compares `@errorName`s. Compare the error
values instead, as `narrowDiagnosticError` in `src/frontend/diag.zig` does.

## Crashes

A crashing input is saved to `<cache dir>/f/crash` and the panic is
printed with a stack trace, but the build **still exits 0**. Check for the
file:

```text
test -e .zig-cache/f/crash && echo crashed
```

The saved file is the byte stream the target read, not source text, and it
only means something to the target and harness version that wrote it.
Replay it to get the sources:

```text
zig build fuzz -Dfuzz-target=compile -Dfuzz-replay=.zig-cache/f/crash
```

This runs the input once, reproduces the crash, and writes what the target
generated to `.zig-cache/f/crash.<target>/`:

- `compile`: case.mm0 and case.auf;
- `kernel`: case.mm0 and case.mmb;
- `lsp`: the client's messages, one per line, in session.jsonl;
- `search`: case.mm0, the proof with markers as case.auf, and with the
  found proofs in place as filled.auf;
- `shapes`, `theory`: case.mm0 and case.auf.

Without `-Dfuzz-target`, every target reads the same file and writes its
own directory.

Turn a crash into a plain regression test: minimize the replayed sources by
hand, then add them where that kind of input already lives
(`tests/proof_cases/` with a row in `src/tests/proof_cases.zig`, a row in
`src/tests/mmb_mutants.zig`, or a test in the suite of the code that broke).
Never commit a saved fuzz input as a corpus entry: it goes stale as soon as
a target or the harness changes how it reads its bytes.

## Nightly in CI

`.github/workflows/fuzz.yml` fuzzes every target each night (and on
demand, with a chosen number of inputs per target) at Debug, with `mm0-c`
on PATH. Each target's corpus is kept in the Actions cache, so coverage
builds up from night to night; the job summary shows each target's runs
and coverage. When a target crashes, its job replays the crash and fails
with an artifact holding the saved input, the replayed sources and the
logs. Triage from there as above: reproduce with `-Dfuzz-replay`, minimize,
and add a plain regression test.

## Adding a target

A target is a function `fn (context, harness.Input) !void` plus a test
that hands it to `harness.run`:

```zig
test "fuzz my target" {
    try harness.run("my_target", context, myTarget);
}
```

Draw every choice from `input.smith`, allocate from `input.gpa`, and pass
each generated text to `input.dump` so a replay can write it out. Import
the file from `tests/fuzz.zig`, add a row to the table above, and add the
target to the matrix in `.github/workflows/fuzz.yml`.
