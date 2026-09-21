// `./host.js` is copied in by `build.zig` from `web/packages/shared/host.js`;
// the package is only runnable from a built tree (`zig build web-packages`).
import {
  encodeText,
  instantiateWasm,
  now,
  readBytes,
  readJsonResult,
  setLocale,
  withInputs,
} from "./host.js";

export const defaultWasmUrl = new URL("./compiler.wasm", import.meta.url);

export class Compiler {
  constructor(instance) {
    this.instance = instance;
    this.exports = instance.exports;
  }

  compile(mm0Text, proofText) {
    const inputs = [encodeText(mm0Text), encodeText(proofText)];
    return withInputs(this.exports, inputs, (mm0Input, proofInput) => {
      const started = now();
      this.exports.compile_sources(
        mm0Input.ptr,
        mm0Input.len,
        proofInput.ptr,
        proofInput.len,
      );
      const durationMs = now() - started;
      const meta = readJsonResult(this.exports);
      const mmbBytes = meta?.ok
        ? readBytes(
            this.exports,
            this.exports.result_mmb_ptr(),
            this.exports.result_mmb_len(),
          )
        : new Uint8Array();
      return Object.assign({ meta, durationMs, mmbBytes }, meta ?? {});
    });
  }

  // Compile a root `.mm0` out of an in-memory file table. `files` is an
  // array of `{ path, text }` (paths normalised and absolute, POSIX style:
  // `/dir/file.mm0`), `root` the root theory's path, and `proof` the root's
  // proof file's path (defaults to the root's `.auf` sibling in the table,
  // when there is one). `import`/`include` statements resolve against the
  // table relative to the importing file, the way the CLI resolves them
  // against the disk. Every diagnostic carries `file` (a table path) and
  // `spanStart`/`spanEnd` offsets local to that file.
  compileFiles({ files, root, proof = null }) {
    const request = JSON.stringify({ root, proof, files });
    return withInputs(this.exports, [encodeText(request)], (input) => {
      const started = now();
      this.exports.compile_files(input.ptr, input.len);
      const durationMs = now() - started;
      const meta = readJsonResult(this.exports);
      const mmbBytes = meta?.ok
        ? readBytes(
            this.exports,
            this.exports.result_mmb_ptr(),
            this.exports.result_mmb_len(),
          )
        : new Uint8Array();
      return Object.assign({ meta, durationMs, mmbBytes }, meta ?? {});
    });
  }
}

export async function loadCompiler(options = {}) {
  const instance = await instantiateWasm(options, defaultWasmUrl);
  if (options.locale) setLocale(instance.exports, options.locale);
  return new Compiler(instance);
}
