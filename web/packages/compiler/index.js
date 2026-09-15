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
}

export async function loadCompiler(options = {}) {
  const instance = await instantiateWasm(options, defaultWasmUrl);
  if (options.locale) setLocale(instance.exports, options.locale);
  return new Compiler(instance);
}
