# Install and run

You do not need to install Aufbau to work through the opening chapters. The
interactive cells run the compiler and language server in your browser.
Install the native tools when you want to work with files on disk, script a
build, or verify an MMB file independently.

## With Nix

With Nix and flakes enabled, you can let Nix obtain or build the tools. Open
a shell with both commands on your `PATH`:

```sh
nix shell github:gleachkr/Aufbau
```

or install them into your profile:

```sh
nix profile install github:gleachkr/Aufbau
```

Either way you get the `abc` and `mm0-zig` commands directly — where the
rest of this chapter writes `zig-out/bin/abc`, just type `abc`. The
repository's flake also provides a development shell (`nix develop`) with
the required Zig version and other build tools. Use it if you prefer to
build from source, as described below.

## Requirements

Building Aufbau requires:

- Git
- Zig 0.15.2

Clone the repository, including its submodules, and make a release build:

```sh
git clone --recurse-submodules https://github.com/gleachkr/Aufbau.git
cd Aufbau
zig build -Doptimize=ReleaseFast
```

The build installs two programs under `zig-out/bin/`: `abc` compiles an MM0
theory and an Aufbau proof script to MMB; `mm0-zig` verifies an MMB file
against its MM0 source. Check that both programs run:

```sh
zig-out/bin/abc --version
zig-out/bin/mm0-zig --version
```

## Compile a proof

An Aufbau project has two source files. The `.mm0` file declares the theory
and the statements to prove. The `.auf` file gives their proofs.

Create `hello.mm0`:

```
delimiter $ ( ) $;
provable sort wff;
term imp (a b: wff): wff; infixr imp: $->$ prec 25;
axiom h1 (a b: wff): $ a -> (b -> a) $;
theorem weaken (p q: wff): $ p -> (q -> p) $;
```

This declares a provable sort of propositions, an implication constructor
written infix as `->`, the weakening axiom `h1`, and a theorem to prove —
weakening restated for the propositions `p` and `q`.

Create `hello.auf`:

```
weaken
------
l1: $ p -> (q -> p) $ by h1
```

The block named `weaken` supplies the proof of the corresponding theorem in
the MM0 file. Its only line states the goal and cites the axiom; the
compiler infers the instantiation.

Compile the pair:

```sh
zig-out/bin/abc compile hello.mm0 hello.auf hello.mmb
```

A successful compile writes `hello.mmb` and prints nothing. The MMB file is
the compact binary proof consumed by the verifier.

## Verify the result

Run the verifier separately:

```sh
zig-out/bin/mm0-zig hello.mmb < hello.mm0
```

It should print:

```
Verification successful!
```

`mm0-zig` takes the MMB path as its argument and reads the matching MM0 source
from standard input.

## Theories in several files

An `.mm0` file can import another one:

```
import "prop.mm0";
theorem weaken (p q: wff): $ p -> (q -> p) $;
```

The path is relative to the importing file. The compiler replaces the
`import` statement with the text of the imported file, so everything
`prop.mm0` declares is available from that point on. Imports nest, and a
file reached by two routes is included once, where it is first reached. A
file that imports itself, directly or through others, is an error.

Proof files follow the theory files by name: when `prop.mm0` has theorems
to prove, put their proofs in `prop.auf` next to it, and the compiler
reads it along with the proofs of the file that imports it. A file that
declares only sorts, terms, notation, and axioms needs no `.auf` at all.

```sh
zig-out/bin/abc compile main.mm0 main.auf main.mmb
```

An `include` line can be used to splice a secondary file of proof-local items 
(lemmas, local definitions, notation) into a given `.auf` file:

```
include "lemmas/weaken.auf";

weaken_twice
------------
l1: $ b -> a $ by weaken [#1]
```

The path is relative to the including file. The included items are visible from 
the `include` on, as if written there. Includes are not deduplicated, so 
include a file once per proof development.

`import` is a convention shared with mm0-rs, not part of MM0 itself, so a
verifier requires that imports be flattened into a single file. `abc join` 
follows imports to generate a flattened single-file mm0:

```sh
zig-out/bin/abc join main.mm0 | zig-out/bin/mm0-zig main.mmb
```

`abc join main.mm0 joined.mm0` writes it to a file instead.

## Command-line help

The compiler also exposes the language server used by editor integrations:

```sh
zig-out/bin/abc lsp
```

For the complete current options, including diagnostic debugging and
treating warnings as errors, use:

```sh
zig-out/bin/abc --help
zig-out/bin/mm0-zig --help
```

The command-line compiler requires finished proofs. Search placeholders
like `auto?` are an editor feature: in a cell or an LSP-connected editor
they run the search and offer a concrete proof to accept, but `abc compile`
rejects a proof script that still contains one.
