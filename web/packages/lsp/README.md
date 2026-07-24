# `@aufbau/lsp`

This package runs the Aufbau language server as WebAssembly.

## Install

```sh
npm install @aufbau/lsp
```

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

## Loading from a CDN

The package works as a plain `<script type="importmap">` entry — no bundler and
no build step:

```html
<script type="importmap">
  {
    "imports": {
      "@aufbau/lsp": "https://esm.sh/@aufbau/lsp"
    }
  }
</script>
<script type="module">
  import { loadLspServerWorker } from "@aufbau/lsp";

  const server = await loadLspServerWorker();
</script>
```

Browsers refuse to construct a Worker from a cross-origin script, and CORS does
not lift that. So when the package is served from another origin,
`loadLspServerWorker()` boots the worker from a same-origin `blob:` URL whose
only statement imports the real worker module. This is transparent to callers,
but a page that sets a Content-Security-Policy has to allow it:

```
worker-src blob:; script-src 'self' https://esm.sh; connect-src 'self' https://esm.sh
```

(`connect-src` covers the worker's `fetch` of `lsp.wasm`.) Passing your own
`options.worker` or `options.workerUrl` bypasses the blob path entirely.
