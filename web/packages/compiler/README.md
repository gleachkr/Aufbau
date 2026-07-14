# `@aufbau/compiler`

Compile an MM0 source file and an Aufbau proof script to an MMB proof in
browsers or Node.

## Install

```sh
npm install @aufbau/compiler
```

## Usage

```js
import { loadCompiler } from "@aufbau/compiler";

const compiler = await loadCompiler();
const result = compiler.compile(mm0Text, proofText);

if (!result.ok) {
  console.error(result.diagnostics);
} else {
  console.log(result.mmbBytes);
}
```

`mm0Text` and `proofText` are strings. On success, `mmbBytes` is a
`Uint8Array`. The result also includes compiler metadata and `durationMs`.

The default loader reads the package's WebAssembly file in browsers and Node.
Pass `wasmUrl`, `wasmBytes`, `module`, or `instance` to `loadCompiler()` to
control loading.

The Aufbau proof-script format is documented in
[`docs/proof.md`](https://github.com/gleachkr/Aufbau/blob/main/docs/proof.md).
