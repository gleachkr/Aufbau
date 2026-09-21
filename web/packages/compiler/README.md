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

Theories spread over several files compile from an in-memory file table:

```js
const result = compiler.compileFiles({
  files: [
    { path: "/lib/base.mm0", text: baseText },
    { path: "/main.mm0", text: 'import "lib/base.mm0";\n' + mainText },
    { path: "/main.auf", text: proofText },
  ],
  root: "/main.mm0",
});
```

`import`/`include` statements resolve against the table relative to the
importing file, and `<name>.auf` pairs with `<name>.mm0` (pass `proof` to
name the root's proof file explicitly). Each diagnostic then carries the
`file` it lies in, with `spanStart`/`spanEnd` local to that file.

The default loader reads the package's WebAssembly file in browsers and Node.
Pass `wasmUrl`, `wasmBytes`, `module`, or `instance` to `loadCompiler()` to
control loading.

The Aufbau proof-script format is documented in
[`docs/proof.md`](https://github.com/gleachkr/Aufbau/blob/main/docs/proof.md).
