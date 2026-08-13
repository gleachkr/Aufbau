// Web Worker host for the wasm LSP server.
//
// The server processes each LSP message synchronously, and a proof search
// (triggered by a code-action request on `auto?`/`exact?`/`apply?`) can run for
// seconds. Running that on the page's main thread freezes the tab; hosting it in
// a worker keeps the UI responsive and lets the wasm churn on its own thread.
//
// This is a module worker (`new Worker(url, { type: "module" })`). Module
// workers do NOT inherit the document's import map, so every import here must be
// a relative specifier — `./index.js` pulls in the same wasm loader the
// main-thread path uses, and its `./lsp.wasm` sibling resolves the same way.
//
// Protocol (main thread <-> worker):
//   main -> worker: { type: "send", message } | { type: "reset" }
//                 | { type: "locale", locale }
//   worker -> main: { type: "ready" } | { type: "message", message }
//                 | { type: "error", error }

import { loadLspServer } from "./index.js";

let server = null;
// Messages that arrive before the wasm finishes instantiating. LSP is
// order-sensitive (initialize must precede everything), so we queue rather than
// drop, then replay in arrival order once the server is live.
const queue = [];

function handle(data) {
  if (!data) return;
  switch (data.type) {
    case "send":
      // `send` runs the server synchronously and fans its outputs out through
      // the subscriber wired up in init(); nothing to await here.
      server.send(data.message);
      break;
    case "reset":
      server.reset();
      break;
    case "locale":
      server.setLocale(data.locale);
      break;
  }
}

self.addEventListener("message", (event) => {
  if (!server) {
    queue.push(event.data);
    return;
  }
  handle(event.data);
});

async function init() {
  try {
    const loaded = await loadLspServer();
    loaded.subscribe((message) => {
      self.postMessage({ type: "message", message });
    });
    server = loaded;
    self.postMessage({ type: "ready" });
    for (const data of queue) handle(data);
    queue.length = 0;
  } catch (error) {
    self.postMessage({
      type: "error",
      error: error && error.message ? error.message : String(error),
    });
  }
}

void init();
