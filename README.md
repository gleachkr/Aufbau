# Aufbau

Aufbau is an experimental Metamath Zero (MM0/MMB) verifier and proof compiler
written in Zig. The compiler translates MM0 source and Aufbau proof scripts to
MMB; the verifier checks the resulting MM0/MMB pair.

Try the [web demo](https://gleachkr.github.io/Aufbau/).

## Build

Aufbau requires Zig 0.15.2.

```sh
git clone --recurse-submodules https://github.com/gleachkr/Aufbau.git
cd aufbau
zig build -Doptimize=ReleaseFast
```

The native binaries are written to `zig-out/bin/`:

- `abc` — proof compiler and language server
- `mm0-zig` — MMB verifier

## Usage

Compile a proof:

```sh
abc compile INPUT.mm0 INPUT.auf OUTPUT.mmb
```

Verify it:

```sh
mm0-zig OUTPUT.mmb < INPUT.mm0
```

## JavaScript packages

WebAssembly and browser packages are published on npm:

- [`@aufbau/compiler`](https://www.npmjs.com/package/@aufbau/compiler)
- [`@aufbau/verifier`](https://www.npmjs.com/package/@aufbau/verifier)
- [`@aufbau/lsp`](https://www.npmjs.com/package/@aufbau/lsp)
- [`@aufbau/editor`](https://www.npmjs.com/package/@aufbau/editor)

Each package README contains a minimal usage example.

## Documentation

- [`ARCHITECTURE.md`](ARCHITECTURE.md) — structure and trust boundary
- [`docs/proof.md`](docs/proof.md) — Aufbau proof-script format
- [`docs/rewrite_system.md`](docs/rewrite_system.md) — rewrite metadata
- [`docs/transparent_defs.md`](docs/transparent_defs.md) — transparent defs
- [`docs/view_recover.md`](docs/view_recover.md) — view and recovery metadata
- [`docs/fresh_binders.md`](docs/fresh_binders.md) — fresh binders
- [`docs/holes.md`](docs/holes.md) — proof-side holes

The canonical MM0 and MMB specifications are maintained by the
[Metamath Zero project](https://github.com/digama0/mm0).

## Test

```sh
zig build test -Doptimize=ReleaseFast
```

Full integration coverage also requires Node, npm, `mm0-rs`, `mm0-c`, and
initialized repository submodules.

## Status

Aufbau is pre-1.0 software. The verifier is usable, and the compiler supports
its documented proof format, but APIs and proof syntax may still change.

Licensed under the [Apache License 2.0](LICENSE).
