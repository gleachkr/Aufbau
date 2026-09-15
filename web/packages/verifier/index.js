// `./host.js` is copied in by `build.zig` from `web/packages/shared/host.js`;
// the package is only runnable from a built tree (`zig build web-packages`).
import {
  encodeText,
  instantiateWasm,
  now,
  readJsonResult,
  withInputs,
} from "./host.js";

export const defaultWasmUrl = new URL("./verifier.wasm", import.meta.url);

export class Verifier {
  constructor(instance) {
    this.instance = instance;
    this.exports = instance.exports;
  }

  verifyPair(mm0Text, mmbBytes) {
    const inputs = [encodeText(mm0Text), byteArray(mmbBytes)];
    return withInputs(this.exports, inputs, (mm0Input, mmbInput) => {
      const started = now();
      this.exports.verify_pair(
        mm0Input.ptr,
        mm0Input.len,
        mmbInput.ptr,
        mmbInput.len,
      );
      const durationMs = now() - started;
      const meta = readJsonResult(this.exports);
      return Object.assign({ meta, durationMs }, meta ?? {});
    });
  }
}

export async function loadVerifier(options = {}) {
  const instance = await instantiateWasm(options, defaultWasmUrl);
  return new Verifier(instance);
}

function byteArray(bytes) {
  if (bytes instanceof Uint8Array) return bytes;
  if (bytes instanceof ArrayBuffer) return new Uint8Array(bytes);
  if (ArrayBuffer.isView(bytes)) {
    return new Uint8Array(bytes.buffer, bytes.byteOffset, bytes.byteLength);
  }
  throw new TypeError("mmbBytes must be a Uint8Array or ArrayBuffer");
}
