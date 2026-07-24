// Same-origin shim for @aufbau/lsp.
//
// TEMPORARY: @aufbau/lsp does this itself as of the next release (see its
// `spawnWorker`). esm.sh still serves 0.0.3, which does not, so the shim has to
// stay until then — at which point this file goes away and the `@aufbau/lsp`
// import-map entry in theme/head.hbs points straight at esm.sh.
//
// The language server runs in a Web Worker, and browsers forbid constructing a
// worker from a cross-origin script — so `@aufbau/lsp` 0.0.3 cannot be loaded
// straight from esm.sh the way the compiler and editor can. The workaround is
// the module-worker analogue of the classic cross-origin `importScripts` trick:
// build the Worker from a *same-origin* blob whose only job is to `import` the
// real (cross-origin) worker module. The blob URL inherits this page's origin,
// so `new Worker` is allowed; the import inside is a cross-origin module fetch,
// which esm.sh serves with permissive CORS, and the worker's own `./lsp.wasm`
// sibling resolves back to esm.sh the same way.
//
// The importmap points `@aufbau/lsp` at this file; everything else stays on
// esm.sh. We re-export the upstream module unchanged and override only
// `loadLspServerWorker`, injecting the blob-built worker the editor's auto-boot
// path would otherwise construct cross-origin.
export * from "https://esm.sh/@aufbau/lsp?external=@aufbau/compiler";
import {
  loadLspServerWorker as upstreamLoad,
  defaultWorkerUrl,
} from "https://esm.sh/@aufbau/lsp?external=@aufbau/compiler";

export function loadLspServerWorker(options = {}) {
  if (!options.worker && !options.workerUrl) {
    const bootstrap = `import ${JSON.stringify(String(defaultWorkerUrl))};`;
    const url = URL.createObjectURL(
      new Blob([bootstrap], { type: "text/javascript" }),
    );
    options = { ...options, worker: new Worker(url, { type: "module" }) };
  }
  return upstreamLoad(options);
}
