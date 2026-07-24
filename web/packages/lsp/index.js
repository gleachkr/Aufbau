const encoder = new TextEncoder();
const decoder = new TextDecoder();

export const defaultWasmUrl = new URL("./lsp.wasm", import.meta.url);
export const defaultWorkerUrl = new URL("./worker.js", import.meta.url);

export class LspServer {
  constructor(instance) {
    this.instance = instance;
    this.exports = instance.exports;
    this.subscribers = new Set();
  }

  subscribe(handler) {
    this.subscribers.add(handler);
  }

  unsubscribe(handler) {
    this.subscribers.delete(handler);
  }

  send(message) {
    const messages = this.process(message);
    for (const output of messages) {
      this.emit(output);
    }
    return messages;
  }

  process(message) {
    const inputText = typeof message === "string"
      ? message
      : JSON.stringify(message);
    const input = writeBytes(this.exports, encoder.encode(inputText));

    try {
      const ok = this.exports.process_lsp_message(input.ptr, input.len);
      const output = readLspResult(this.exports);
      if (!ok && output.length === 0) {
        throw new Error("LSP message failed");
      }
      return output.split("\n").filter((line) => line.length !== 0);
    } finally {
      freeBytes(this.exports, input);
    }
  }

  reset() {
    this.exports.reset_lsp_server();
  }

  emit(message) {
    for (const handler of this.subscribers) {
      handler(message);
    }
  }
}

export async function loadLspServer(options = {}) {
  const instance = await instantiateWasm(options, defaultWasmUrl);
  return new LspServer(instance);
}

// A drop-in `Transport` (send/subscribe/unsubscribe) for `@codemirror/lsp-client`
// that runs the wasm server in a Web Worker. Identical wire behavior to
// `LspServer`, but `send` posts to the worker and server output arrives
// asynchronously as messages — so a long proof search never blocks the caller's
// thread. Note this does not make an in-flight search *interruptible*: the worker
// processes messages one at a time and runs each synchronously, so a
// `$/cancelRequest` only takes effect once the current search returns (bounded by
// the search's own budget). The win is that the page stays responsive meanwhile.
export class WorkerLspServer {
  constructor(worker) {
    this.worker = worker;
    this.subscribers = new Set();
    this.readyError = null;
    let resolveReady;
    let rejectReady;
    this.ready = new Promise((resolve, reject) => {
      resolveReady = resolve;
      rejectReady = reject;
    });

    worker.addEventListener("message", (event) => {
      const data = event.data;
      if (!data) return;
      if (data.type === "message") {
        this.emit(data.message);
      } else if (data.type === "ready") {
        resolveReady(this);
      } else if (data.type === "error") {
        this.readyError = new Error(data.error);
        rejectReady(this.readyError);
      }
    });
    worker.addEventListener("error", (event) => {
      this.readyError = new Error(event.message || "LSP worker failed");
      rejectReady(this.readyError);
    });
  }

  send(message) {
    const text = typeof message === "string" ? message : JSON.stringify(message);
    this.worker.postMessage({ type: "send", message: text });
  }

  subscribe(handler) {
    this.subscribers.add(handler);
  }

  unsubscribe(handler) {
    this.subscribers.delete(handler);
  }

  reset() {
    this.worker.postMessage({ type: "reset" });
  }

  emit(message) {
    for (const handler of this.subscribers) {
      handler(message);
    }
  }

  terminate() {
    this.worker.terminate();
  }
}

// Spawn the worker-hosted LSP server and resolve once its wasm is instantiated
// (so a load failure surfaces as a rejection rather than a silently dead
// transport). This API is browser-only: it expects a Web Worker with the
// browser's event interface, not `node:worker_threads`. Pass `options.worker`
// to supply a preconstructed Web Worker, or `options.workerUrl` to override
// where it is loaded from.
export async function loadLspServerWorker(options = {}) {
  const spawned = options.worker
    ? null
    : spawnWorker(options.workerUrl ?? defaultWorkerUrl);
  const server = new WorkerLspServer(options.worker ?? spawned.worker);
  try {
    await server.ready;
  } finally {
    // The blob only has to survive until the worker script has been fetched.
    // Revoking after `ready` (rather than right after construction) keeps us
    // clear of the spec's "fetch the worker script in parallel" wording.
    if (spawned?.objectUrl) URL.revokeObjectURL(spawned.objectUrl);
  }
  return server;
}

// Browsers refuse to construct a Worker from a cross-origin script, and CORS
// does not lift that — so loading this package straight from a CDN (esm.sh,
// unpkg) would leave the worker transport unusable. The way around it is the
// module-worker analogue of the classic cross-origin `importScripts` trick:
// build the worker from a *same-origin* blob whose only job is to `import` the
// real URL. The blob inherits the page's origin, so construction is allowed,
// while the import inside is an ordinary cross-origin module fetch that the CDN
// serves with permissive CORS. `import.meta.url` inside the worker stays the
// real URL, so its `./lsp.wasm` sibling still resolves back to the CDN.
//
// Pages that do this need `worker-src blob:` in their CSP (plus the CDN host in
// `script-src`/`connect-src`).
function spawnWorker(url) {
  const remote = crossOriginHttpUrl(url);
  if (remote === null) {
    return { worker: new Worker(url, { type: "module" }), objectUrl: null };
  }
  const bootstrap = `import ${JSON.stringify(remote)};`;
  const objectUrl = URL.createObjectURL(
    new Blob([bootstrap], { type: "text/javascript" }),
  );
  return { worker: new Worker(objectUrl, { type: "module" }), objectUrl };
}

// The absolute form of `url` when it is an http(s) URL on another origin, else
// null. Restricted to http(s) so that same-origin URLs, and opaque schemes a
// caller may have built the worker script from themselves (`blob:`, `data:`),
// keep going down the direct path.
function crossOriginHttpUrl(url) {
  const here = globalThis.location;
  if (!here) return null;
  try {
    const resolved = new URL(url, here.href);
    if (resolved.origin === here.origin) return null;
    if (resolved.protocol !== "http:" && resolved.protocol !== "https:") {
      return null;
    }
    return resolved.href;
  } catch {
    return null;
  }
}

async function instantiateWasm(options, fallbackUrl) {
  if (options.instance) return options.instance;

  const imports = options.imports ?? {};
  if (options.module) {
    const instance = await WebAssembly.instantiate(options.module, imports);
    return instance;
  }
  if (options.wasmBytes) {
    const result = await WebAssembly.instantiate(options.wasmBytes, imports);
    return result.instance;
  }

  const url = options.wasmUrl ?? fallbackUrl;
  const bytes = await loadWasmBytes(url);
  const result = await WebAssembly.instantiate(bytes, imports);
  return result.instance;
}

async function loadWasmBytes(url) {
  if (isFileUrl(url)) {
    const { readFile } = await import("node:fs/promises");
    return readFile(url);
  }

  const response = await fetch(url);
  if (!response.ok) {
    throw new Error(`Failed to load ${url}`);
  }
  return response.arrayBuffer();
}

function isFileUrl(url) {
  if (url instanceof URL) return url.protocol === "file:";
  if (typeof url !== "string") return false;

  try {
    return new URL(url).protocol === "file:";
  } catch {
    return false;
  }
}

function writeBytes(exports, bytes) {
  const len = bytes.length;
  const ptr = exports.alloc(len);
  if (len !== 0 && ptr === 0) {
    throw new Error("WebAssembly allocation failed");
  }
  if (len !== 0) {
    new Uint8Array(exports.memory.buffer, ptr, len).set(bytes);
  }
  return { ptr, len };
}

function freeBytes(exports, { ptr, len }) {
  exports.free(ptr, len);
}

function readLspResult(exports) {
  const ptr = exports.result_lsp_ptr();
  const len = exports.result_lsp_len();
  if (!ptr || !len) return "";
  const bytes = new Uint8Array(exports.memory.buffer, ptr, len);
  return decoder.decode(bytes);
}
