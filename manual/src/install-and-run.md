# Install and run

You do not need to install Aufbau to work through the opening chapters. The
interactive cells run the compiler and language server in your browser.
Install the native tools when you want to work with files on disk, script a
build, or verify an MMB file independently.

## With Nix

If you use Nix with flakes enabled, you don't need to build anything. Drop
into a shell with both tools on your `PATH`:

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
the right Zig version and the rest of the toolchain, if you'd rather build
from source as described next.

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
