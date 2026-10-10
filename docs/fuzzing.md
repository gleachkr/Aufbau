# Fuzzing

The fuzz targets live in `tests/fuzz/` and run on Zig's built-in fuzzer.
Each target turns the fuzzer's choices into an input for one part of the
toolchain and checks what comes back:

| Target | Input | Must hold |
|---|---|---|
| `compile` | a proof case with edits to its `.mm0`, its `.auf`, or both: tokens, lines, statements and blocks, brackets wrapped around runs | whatever compiles passes the trusted verifier, which admits exactly the statements `by sorry!` warned about; a failed compile has a diagnostic for its error; the editor's analysis reports an error exactly when the compile fails |
| `kernel` | a proof case's `.mm0` with the binary this compiler makes for it, or the upstream tutorial pair (built by mm0-rs); the binary gets raw edits (bytes, words, cuts, copies) or structured ones (a header or table field, or one proof or unify command: its opcode, its operand, dropped or repeated), and the spec may get token edits | the verifier rejects bad input with an error; a changed pair it accepts must pass mm0-c too, when `mm0-c` is on PATH |
| `lsp` | a language-server session over lsp-kit's own message loop: initialize with a random position encoding, open a proof case (maybe edited), then up to 32 events (insertions, deletions, whole-document replacements, typing a token a character at a time, hover, completion, definition, implementation, references, symbols, code actions, applying a returned code action's edit, closing, reopening, malformed messages) | every server message is JSON; a well-formed request never fails; every returned range lies inside its document, on a code-point boundary of the negotiated encoding |

Every target must also not panic, leak, write after free, run longer than
10 seconds on one input, or hold more than 1 GiB at once. The fuzzer checks
the first three. `tests/fuzz/harness.zig` adds a watchdog thread and a
capped allocator for the last two, and both panic so the fuzzer saves the
input like any other crash.

Seeds are every case under `tests/proof_cases/` that joins, with `import`s
and `include`s already joined into single texts.

## Running

```text
zig build fuzz                       # each target once, as a smoke check
zig build fuzz --fuzz=100K           # fuzz for 100K inputs per target
zig build fuzz --fuzz                # fuzz until stopped, with a web UI
zig build fuzz --fuzz -Dfuzz-target=compile
```

`zig build test-unit` runs the same smoke check.

Fuzz at Debug (the default) or ReleaseFast. Debug keeps the safety checks
and runs at roughly 35 inputs a second. ReleaseFast is about twice as fast
but cannot catch out-of-bounds or overflow. A ReleaseSafe fuzz build never
finishes compiling on Zig 0.17. The fuzz build uses LLVM even at Debug,
because the self-hosted backend has no fuzzing instrumentation.

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

This runs the input once, reproduces the crash, and writes the generated
files (for `compile`, a `.mm0` and an `.auf` named `case`; for `lsp`, the
client's messages as `session.jsonl`) to
`.zig-cache/f/crash.compile/`. Without `-Dfuzz-target`, every target reads
the same file and writes its own directory.

Turn a crash into a plain regression test: minimize the replayed sources by
hand, then add them where that kind of input already lives
(`tests/proof_cases/` with a row in `src/tests/proof_cases.zig`, a row in
`src/tests/mmb_mutants.zig`, or a test in the suite of the code that broke).
Never commit a saved fuzz input as a corpus entry: it goes stale as soon as
a target or the harness changes how it reads its bytes.

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
the file from `tests/fuzz.zig` and add a row to the table above.
