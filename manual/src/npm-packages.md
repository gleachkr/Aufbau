# The npm packages

Aufbau ships four npm packages. Each wraps the same Zig code that the CLI uses, 
compiled to WebAssembly for use in JS environments.

| Package | Contents | Runs in |
|---|---|---|
| `@aufbau/verifier` | the trusted MM0/MMB verifier | browsers and Node |
| `@aufbau/compiler` | the compiler: `.mm0` + `.auf` → `.mmb` | browsers and Node |
| `@aufbau/lsp` | the language server (hover, completion, proof search) | browsers and Node |
| `@aufbau/editor` | the `<aufbau-*>` web components | browsers only |

All four are ES modules with no install-time dependencies, usable from a
bundler, from plain Node, or straight from a CDN import map (see [Embedding
the editor](embedding.md) for the CDN setup).

## `@aufbau/verifier`

```js
import { loadVerifier } from "@aufbau/verifier";

const verifier = await loadVerifier();
const result = verifier.verifyPair(mm0Text, mmbBytes);
if (!result.ok) console.error(result.diagnostics);
```

`mm0Text` is a string; `mmbBytes` is a `Uint8Array` (or any typed-array view).
The result carries `ok`, `diagnostics`, verifier metadata, and `durationMs`.

## `@aufbau/compiler`

```js
import { loadCompiler } from "@aufbau/compiler";

const compiler = await loadCompiler();
const result = compiler.compile(mm0Text, proofText);
if (result.ok) {
  // result.mmbBytes is a Uint8Array, ready for the verifier
}
```

Compiling and verifying compose easily. A browser page can compile a proof 
script and then check the output with the independent verifier.

Both loaders locate their `.wasm` file automatically in browsers and Node.
To control loading (offline bundles, custom hosting), pass `wasmUrl`,
`wasmBytes`, `module`, or `instance` to `loadVerifier()` / `loadCompiler()`.

## `@aufbau/lsp`

The language server speaks JSON-RPC. `loadLspServer()` runs it synchronously
in the calling thread:

```js
import { loadLspServer } from "@aufbau/lsp";

const server = await loadLspServer();
const responses = server.process({
  jsonrpc: "2.0",
  id: 1,
  method: "initialize",
  params: { capabilities: {} },
});
```

Long proof searches block the calling thread, so browser pages should prefer
`loadLspServerWorker()`, which runs the server in a Web Worker and delivers
messages through `server.subscribe(callback)`. The worker transport is
browser-only; Node applications should use `loadLspServer()` directly.

One deployment wrinkle: browsers refuse to build a Worker from a cross-origin
script. When the package is served from a CDN, `loadLspServerWorker()`
transparently boots the worker through a same-origin `blob:` URL. Pages with a
Content-Security-Policy must allow this:

```
worker-src blob:; script-src 'self' https://esm.sh; connect-src 'self' https://esm.sh
```

Passing your own `options.worker` or `options.workerUrl` bypasses the blob
path.

## `@aufbau/editor`

Importing the package registers the custom elements used throughout this
manual:

```js
import "@aufbau/editor";
```

```html
<aufbau-theory id="example" src="/example.mm0"></aufbau-theory>
<aufbau-proof theory="example" src="/example.auf"></aufbau-proof>
```

It declares peer dependencies on `@aufbau/compiler` and CodeMirror 6
(`@codemirror/view`, `state`, `commands`, `lint`), with `@aufbau/lsp` and
`@codemirror/autocomplete` optional. Without those last two packages, the cells 
still compile and report diagnostics, they just lose hover, completion, and 
proof search. Element and attribute reference: [Embedding the editor](embedding.md).
