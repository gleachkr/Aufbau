# `@aufbau/verifier`

Verify an MM0 source file and its MMB proof in browsers or Node.

## Install

```sh
npm install @aufbau/verifier
```

## Usage

```js
import { loadVerifier } from "@aufbau/verifier";

const verifier = await loadVerifier();
const result = verifier.verifyPair(mm0Text, mmbBytes);

if (!result.ok) {
  console.error(result.diagnostics);
}
```

`mm0Text` is a string. `mmbBytes` may be a `Uint8Array`, `ArrayBuffer`, or
another typed-array view. The result includes verifier metadata and
`durationMs`.

The default loader reads the package's WebAssembly file in browsers and Node.
Pass `wasmUrl`, `wasmBytes`, `module`, or `instance` to `loadVerifier()` to
control loading.
