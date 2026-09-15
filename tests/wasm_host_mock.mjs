// The packages' wasm hosting, exercised against mock instances.
//
// A real instance cannot be made to fail an allocation, trap, or hand back
// malformed JSON on cue, so the host glue's failure paths (the buffers it
// frees when a call goes wrong, the memory view it re-reads after growth) are
// pinned here with a scripted `exports` object instead. Runs against the built
// packages: `node tests/wasm_host_mock.mjs zig-out/npm/@aufbau`.
import assert from "node:assert/strict";
import { pathToFileURL } from "node:url";
import { join, resolve } from "node:path";

const packageRoot = resolve(process.argv[2] ?? "zig-out/npm/@aufbau");
const load = (name) => import(pathToFileURL(join(packageRoot, name, "index.js")));
const { loadCompiler } = await load("compiler");
const { loadVerifier } = await load("verifier");
const { loadLspServer } = await load("lsp");

const encoder = new TextEncoder();

// A scripted instance. Every allocation is tracked so a test can assert that
// nothing stays live after a call, however that call ended. `call` runs in
// place of the package's entry export and may throw (a trap), grow the
// memory, or leave a result; results are written into memory only by
// `call`, so a reader that cached the old buffer would miss them.
function mockInstance(entryName, { failAllocAt = 0, call } = {}) {
  let memory = { buffer: new ArrayBuffer(1 << 12) };
  const live = new Map();
  let next = 16;
  let allocs = 0;
  let result = { json: "", mmb: new Uint8Array(), lsp: "" };
  const regions = {};

  const store = (bytes) => {
    if (bytes.length === 0) return { ptr: 0, len: 0 };
    if (next + bytes.length > memory.buffer.byteLength) {
      const grown = new ArrayBuffer(memory.buffer.byteLength * 2);
      new Uint8Array(grown).set(new Uint8Array(memory.buffer));
      memory.buffer = grown;
    }
    const ptr = next;
    new Uint8Array(memory.buffer, ptr, bytes.length).set(bytes);
    next += bytes.length;
    return { ptr, len: bytes.length };
  };

  const exports = {
    memory,
    alloc(len) {
      allocs += 1;
      if (allocs === failAllocAt) return 0;
      const ptr = next;
      next += Math.max(len, 1);
      live.set(ptr, len);
      return ptr;
    },
    free(ptr, len) {
      assert.ok(live.has(ptr), `free of a pointer never allocated: ${ptr}`);
      assert.equal(live.get(ptr), len, `free with the wrong length at ${ptr}`);
      live.delete(ptr);
    },
    result_json_ptr: () => regions.json?.ptr ?? 0,
    result_json_len: () => regions.json?.len ?? 0,
    result_mmb_ptr: () => regions.mmb?.ptr ?? 0,
    result_mmb_len: () => regions.mmb?.len ?? 0,
    result_lsp_ptr: () => regions.lsp?.ptr ?? 0,
    result_lsp_len: () => regions.lsp?.len ?? 0,
    set_locale(ptr, len) {
      regions.locale = { ptr, len };
    },
    [entryName](...args) {
      // Inputs must be readable at call time, from the live memory.
      const inputs = [];
      for (let i = 0; i + 1 < args.length; i += 2) {
        inputs.push(
          new Uint8Array(memory.buffer, args[i], args[i + 1]).slice(),
        );
      }
      const outcome = call ? call(inputs) : {};
      result = { ...result, ...outcome };
      regions.json = store(encoder.encode(result.json));
      regions.mmb = store(result.mmb);
      regions.lsp = store(encoder.encode(result.lsp));
      return outcome.ok ?? 1;
    },
  };

  return {
    instance: { exports },
    liveCount: () => live.size,
    memoryBytes: () => memory.buffer.byteLength,
    inputsSeen: (bytes) => new TextDecoder().decode(bytes),
  };
}

const trap = () => {
  throw new WebAssembly.RuntimeError("unreachable executed");
};

// --- compiler --------------------------------------------------------------

{
  // Second allocation fails: the first input must be freed again.
  const mock = mockInstance("compile_sources", { failAllocAt: 2 });
  const compiler = await loadCompiler({ instance: mock.instance });
  assert.throws(() => compiler.compile("mm0", "proof"), {
    message: "WebAssembly allocation failed",
  });
  assert.equal(mock.liveCount(), 0, "first input leaked after alloc failure");
}

{
  // First allocation fails: nothing acquired, nothing freed twice.
  const mock = mockInstance("compile_sources", { failAllocAt: 1 });
  const compiler = await loadCompiler({ instance: mock.instance });
  assert.throws(() => compiler.compile("mm0", "proof"));
  assert.equal(mock.liveCount(), 0);
}

{
  // A trap inside the call propagates and both inputs are freed.
  const mock = mockInstance("compile_sources", { call: trap });
  const compiler = await loadCompiler({ instance: mock.instance });
  assert.throws(() => compiler.compile("mm0", "proof"), WebAssembly.RuntimeError);
  assert.equal(mock.liveCount(), 0, "inputs leaked after a trap");
}

{
  // Malformed result JSON: the parse error propagates, inputs are freed.
  const mock = mockInstance("compile_sources", {
    call: () => ({ json: "{not json" }),
  });
  const compiler = await loadCompiler({ instance: mock.instance });
  assert.throws(() => compiler.compile("mm0", "proof"), SyntaxError);
  assert.equal(mock.liveCount(), 0, "inputs leaked after a bad result");
}

{
  // Memory grows during the call; the result and the MMB come from the new
  // buffer, and the inputs the instance saw are the ones we sent.
  const big = "x".repeat(5000);
  let seen = null;
  const mock = mockInstance("compile_sources", {
    call: (inputs) => {
      seen = inputs.map((bytes) => mock.inputsSeen(bytes));
      return { json: `{"ok":true,"big":"${big}"}`, mmb: new Uint8Array([1, 2, 3]) };
    },
  });
  const before = mock.memoryBytes();
  const compiler = await loadCompiler({ instance: mock.instance });
  const result = compiler.compile("theory", "proof");
  assert.ok(mock.memoryBytes() > before, "the mock did not grow its memory");
  assert.deepEqual(seen, ["theory", "proof"]);
  assert.equal(result.ok, true);
  assert.equal(result.meta.big, big);
  assert.deepEqual([...result.mmbBytes], [1, 2, 3]);
  assert.equal(typeof result.durationMs, "number");
  assert.equal(mock.liveCount(), 0);
}

{
  // The instance stays usable after a failed call.
  let calls = 0;
  const mock = mockInstance("compile_sources", {
    call: () => {
      calls += 1;
      if (calls === 1) trap();
      return { json: '{"ok":false,"diagnostics":[]}' };
    },
  });
  const compiler = await loadCompiler({ instance: mock.instance });
  assert.throws(() => compiler.compile("a", "b"));
  const result = compiler.compile("a", "b");
  assert.equal(result.ok, false);
  assert.deepEqual([...result.mmbBytes], []);
  assert.equal(mock.liveCount(), 0);
}

{
  // A call that leaves no result yields a null meta rather than throwing.
  const mock = mockInstance("compile_sources");
  const compiler = await loadCompiler({ instance: mock.instance });
  const result = compiler.compile("", "");
  assert.equal(result.meta, null);
  assert.equal(mock.liveCount(), 0);
}

{
  // `locale` is delivered through the same guarded path.
  const mock = mockInstance("compile_sources");
  await loadCompiler({ instance: mock.instance, locale: "de" });
  assert.equal(mock.liveCount(), 0, "locale input leaked");
}

// --- verifier --------------------------------------------------------------

{
  const mock = mockInstance("verify_pair", { failAllocAt: 2 });
  const verifier = await loadVerifier({ instance: mock.instance });
  assert.throws(() => verifier.verifyPair("mm0", new Uint8Array([9])), {
    message: "WebAssembly allocation failed",
  });
  assert.equal(mock.liveCount(), 0, "first input leaked after alloc failure");
}

{
  const mock = mockInstance("verify_pair", { call: trap });
  const verifier = await loadVerifier({ instance: mock.instance });
  assert.throws(
    () => verifier.verifyPair("mm0", new Uint8Array([9])),
    WebAssembly.RuntimeError,
  );
  assert.equal(mock.liveCount(), 0, "inputs leaked after a trap");
}

{
  // A typed-array view with an offset is sent as exactly its bytes, and the
  // result is read after the call.
  let seen = null;
  const mock = mockInstance("verify_pair", {
    call: (inputs) => {
      seen = inputs.map((bytes) => [...bytes]);
      return { json: '{"ok":true,"theorems":2}' };
    },
  });
  const verifier = await loadVerifier({ instance: mock.instance });
  const backing = new Uint8Array([0, 0, 7, 8, 9]);
  const view = new DataView(backing.buffer, 2, 3);
  const result = verifier.verifyPair("T", view);
  assert.deepEqual(seen, [[84], [7, 8, 9]]);
  assert.equal(result.ok, true);
  assert.equal(result.theorems, 2);
  assert.equal(mock.liveCount(), 0);
  assert.throws(() => verifier.verifyPair("T", "not bytes"), TypeError);
  assert.equal(mock.liveCount(), 0);
}

// --- lsp -------------------------------------------------------------------

{
  const mock = mockInstance("process_lsp_message", { call: trap });
  const lsp = await loadLspServer({ instance: mock.instance });
  assert.throws(() => lsp.process({ jsonrpc: "2.0" }), WebAssembly.RuntimeError);
  assert.equal(mock.liveCount(), 0, "input leaked after a trap");
}

{
  const mock = mockInstance("process_lsp_message", { failAllocAt: 1 });
  const lsp = await loadLspServer({ instance: mock.instance });
  assert.throws(() => lsp.process("{}"), {
    message: "WebAssembly allocation failed",
  });
  assert.equal(mock.liveCount(), 0);
}

{
  // Output lines are split, a failed call with no output throws, and the
  // server stays usable afterwards.
  let calls = 0;
  const mock = mockInstance("process_lsp_message", {
    call: () => {
      calls += 1;
      return calls === 1 ? { ok: 0, lsp: "" } : { ok: 1, lsp: '{"id":1}\n{"id":2}\n' };
    },
  });
  const lsp = await loadLspServer({ instance: mock.instance, locale: "de" });
  assert.throws(() => lsp.process("{}"), { message: "LSP message failed" });
  assert.equal(mock.liveCount(), 0);
  const received = [];
  lsp.subscribe((message) => received.push(message));
  assert.deepEqual(lsp.send("{}"), ['{"id":1}', '{"id":2}']);
  assert.deepEqual(received, ['{"id":1}', '{"id":2}']);
  assert.equal(mock.liveCount(), 0);
}

console.log("Package wasm hosting frees its inputs on every exit path.");
