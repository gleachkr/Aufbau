# Aufbau 0.0.1

Aufbau 0.0.1 is the first experimental release of the Aufbau Metamath Zero
verifier and proof compiler.

## Included

- `abc`, a native compiler from MM0 source and Aufbau proof scripts to MMB.
- `mm0-zig`, a native verifier for MM0/MMB proof pairs.
- WebAssembly packages for the compiler, verifier, and language server:
  `@aufbau/compiler`, `@aufbau/verifier`, and `@aufbau/lsp`.
- `@aufbau/editor`, browser custom elements for editable theories, proofs, and
  statement indexes, with local compilation and optional language-server
  support.
- The hosted [web demo](https://gleachkr.github.io/Aufbau/).

The npm WebAssembly loaders support browsers and Node. The language server's
worker transport and `@aufbau/editor` require a browser environment.

Source builds require Zig 0.15.2. See the
[README](https://github.com/gleachkr/Aufbau#readme) for build and usage
instructions.

## Status and known limitations

This is pre-1.0 software. APIs and proof syntax may change in later releases.

Aufbau is licensed under the Apache License 2.0.
