# `@aufbau/lsp`

This package runs the Aufbau language server as WebAssembly.

## Direct server

`loadLspServer()` loads `lsp.wasm` and runs the server synchronously in the
calling JavaScript thread. The default loader supports browsers and Node:

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

Long-running proof searches block the calling thread. In a browser, use the
worker transport when the page must remain responsive.

## Worker transport

`loadLspServerWorker()` is browser-only. It creates a module Web Worker and
expects the browser `Worker` event interface. It does not support Node's
`node:worker_threads` API.

```js
import { loadLspServerWorker } from "@aufbau/lsp";

const server = await loadLspServerWorker();
server.subscribe((message) => {
  console.log(message);
});
```

Node applications should use `loadLspServer()` unless they provide their own
adapter around `node:worker_threads`.
