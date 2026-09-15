// Host plumbing shared by @aufbau/compiler, @aufbau/verifier, and @aufbau/lsp:
// instantiating the wasm module and moving bytes across its linear memory.
//
// This is the one source; `build.zig` copies it into each of the three
// packages as a private `host.js` (imported as `./host.js`, never exported),
// so every package stays independently installable with no import that
// escapes the published tarball. Edit it here, not in `zig-out`.

const encoder = new TextEncoder();
const decoder = new TextDecoder();

export function encodeText(text) {
  return encoder.encode(text);
}

// Resolve `options` to a wasm instance: a preinstantiated `instance`, a
// compiled `module`, raw `wasmBytes`, or a `wasmUrl` (defaulting to the
// package-relative `fallbackUrl`) fetched over http(s) or read from disk.
export async function instantiateWasm(options, fallbackUrl) {
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

// Copy each byte array of `inputs` into the instance's memory, call `fn` with
// one `{ ptr, len }` handle per input, and free every buffer that was
// acquired. The frees run whether `fn` returns, `fn` throws (a trap, a result
// that fails to parse), or a later allocation fails after an earlier one
// succeeded — so a failed call never leaks the inputs it had already copied.
export function withInputs(exports, inputs, fn) {
  const acquired = [];
  try {
    for (const bytes of inputs) acquired.push(writeBytes(exports, bytes));
    return fn(...acquired);
  } finally {
    for (const input of acquired.reverse()) freeBytes(exports, input);
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

// Readers take `exports.memory.buffer` afresh on every call: a call into the
// instance may grow its memory, which detaches any earlier buffer view.
export function readBytes(exports, ptr, len) {
  if (!ptr || !len) return new Uint8Array();
  const view = new Uint8Array(exports.memory.buffer, ptr, len);
  return view.slice();
}

export function readText(exports, ptr, len) {
  if (!ptr || !len) return "";
  return decoder.decode(new Uint8Array(exports.memory.buffer, ptr, len));
}

// The JSON result the compiler and verifier leave behind after a call, or
// null when the call left none.
export function readJsonResult(exports) {
  const text = readText(
    exports,
    exports.result_json_ptr(),
    exports.result_json_len(),
  );
  return text.length === 0 ? null : JSON.parse(text);
}

// Select the diagnostic language ("en", "de") for all subsequent calls.
// Unknown locales are ignored (the instance stays on its current locale), as
// is an instance built without locale support.
export function setLocale(exports, locale) {
  if (typeof exports.set_locale !== "function") return;
  withInputs(exports, [encoder.encode(String(locale))], (input) => {
    exports.set_locale(input.ptr, input.len);
  });
}

export function now() {
  return globalThis.performance?.now?.() ?? Date.now();
}
