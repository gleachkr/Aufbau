// Browsers refuse `new Worker(url, { type: "module" })` when `url` is
// cross-origin, and CORS does not lift that restriction — which is exactly the
// situation of a page that loads `@aufbau/lsp` from a CDN. `@aufbau/lsp`
// works around it by bootstrapping the worker from a same-origin blob that
// imports the real URL; this test pins that behavior down, because nothing in
// the same-origin demo or the Node tests exercises it.
//
// Two loopback servers on different ports are two different origins as far as
// the browser is concerned, so the setup is: serve the packed npm packages
// (with CORS) from one, serve the page from the other, and have the page boot
// the worker transport across the gap and run an `initialize` round trip.

import assert from "node:assert/strict";
import { mkdtemp, rm, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join, resolve } from "node:path";
import {
  close,
  createResultServer,
  findBrowser,
  listen,
  runBrowser,
} from "./browser_harness.mjs";

const packageRoot = resolve(
  process.argv[2] ?? "zig-out/npm/@aufbau",
);
const tempRoot = await mkdtemp(
  join(tmpdir(), "aufbau-lsp-cross-origin-"),
);
let pageServer;
let cdnServer;

try {
  const cdn = createResultServer(packageRoot, {
    headers: { "Access-Control-Allow-Origin": "*" },
  });
  cdnServer = cdn.server;
  const cdnAddress = await listen(cdnServer);
  const lspUrl = `http://127.0.0.1:${cdnAddress.port}/lsp/index.js`;

  await writeFile(join(tempRoot, "index.html"), pageSource(lspUrl));
  const page = createResultServer(tempRoot);
  pageServer = page.server;
  const pageAddress = await listen(pageServer);

  const result = await runBrowser(
    findBrowser(),
    `http://127.0.0.1:${pageAddress.port}/index.html`,
    tempRoot,
    page.result,
  );

  assert.equal(
    result.status,
    "passed",
    `cross-origin LSP worker test failed:\n${result.detail}\n${result.stderr}`,
  );
  console.log(
    `@aufbau/lsp boots its worker across origins in Chromium (${result.detail}).`,
  );
} finally {
  if (pageServer) await close(pageServer);
  if (cdnServer) await close(cdnServer);
  await rm(tempRoot, {
    force: true,
    maxRetries: 10,
    recursive: true,
    retryDelay: 100,
  });
}

function pageSource(lspUrl) {
  return String.raw`<!doctype html>
<html lang="en">
  <head>
    <meta charset="utf-8">
    <title>@aufbau/lsp cross-origin worker</title>
  </head>
  <body>
    <pre id="result">running</pre>
    <script type="module">
      const lspUrl = ${JSON.stringify(lspUrl)};

      try {
        const lsp = await import(lspUrl);

        // The premise of the whole exercise: constructing the worker straight
        // from the cross-origin URL is refused. Recorded rather than asserted —
        // if a browser ever starts allowing it the blob path is merely
        // redundant, not wrong.
        let direct = "allowed";
        try {
          new Worker(lsp.defaultWorkerUrl, { type: "module" }).terminate();
        } catch (error) {
          direct = "refused with " + (error?.name ?? String(error));
        }

        const server = await lsp.loadLspServerWorker();
        const response = await roundTrip(server, {
          jsonrpc: "2.0",
          id: 1,
          method: "initialize",
          params: { processId: null, rootUri: null, capabilities: {} },
        });
        if (!response.result?.capabilities) {
          throw new Error(
            "initialize returned no capabilities: " + JSON.stringify(response),
          );
        }
        server.terminate();
        await report("passed", "direct construction " + direct);
      } catch (error) {
        await report("failed", error?.stack ?? String(error));
      }

      function roundTrip(server, request) {
        return new Promise((resolve, reject) => {
          const timer = setTimeout(
            () => reject(new Error("no response to " + request.method)),
            30000,
          );
          server.subscribe((message) => {
            const parsed = typeof message === "string"
              ? JSON.parse(message)
              : message;
            if (parsed?.id !== request.id) return;
            clearTimeout(timer);
            resolve(parsed);
          });
          server.send(request);
        });
      }

      async function report(status, detail) {
        document.querySelector("#result").textContent = status + ": " + detail;
        const response = await fetch("/__result", {
          method: "POST",
          headers: { "Content-Type": "application/json" },
          body: JSON.stringify({ status, detail }),
        });
        if (!response.ok) throw new Error("unable to report result");
      }
    </script>
  </body>
</html>
`;
}
