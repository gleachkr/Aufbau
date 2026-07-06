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
// transport). Pass `options.worker` to supply a preconstructed worker, or
// `options.workerUrl` to override where it is loaded from.
export async function loadLspServerWorker(options = {}) {
  const worker = options.worker
    ?? new Worker(options.workerUrl ?? defaultWorkerUrl, { type: "module" });
  const server = new WorkerLspServer(worker);
  await server.ready;
  return server;
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
  const response = await fetch(url);
  if (!response.ok) {
    throw new Error(`Failed to load ${url}`);
  }
  const bytes = await response.arrayBuffer();
  const result = await WebAssembly.instantiate(bytes, imports);
  return result.instance;
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
