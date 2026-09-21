import assert from "node:assert/strict";
import { mkdir, mkdtemp, rm, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join, resolve } from "node:path";
import { pathToFileURL } from "node:url";
import {
  close,
  createResultServer,
  findBrowser,
  listen,
  run,
  runBrowser,
} from "./browser_harness.mjs";

const packageRoot = resolve(
  process.argv[2] ?? "zig-out/npm/@aufbau",
);
const tempRoot = await mkdtemp(
  join(tmpdir(), "aufbau-editor-browser-"),
);
let server;

try {
  await writeFile(
    join(tempRoot, "package.json"),
    JSON.stringify({ private: true, type: "module" }),
  );

  const tarballs = [];
  for (const packageName of ["compiler", "lsp", "editor"]) {
    const output = run("npm", [
      "pack",
      join(packageRoot, packageName),
      "--json",
      "--pack-destination",
      tempRoot,
    ]);
    const packed = JSON.parse(output);
    assert.equal(packed.length, 1);
    tarballs.push(join(tempRoot, packed[0].filename));
  }

  run(
    "npm",
    [
      "install",
      "--ignore-scripts",
      "--no-audit",
      "--no-fund",
      "--package-lock=false",
      ...tarballs,
      "@codemirror/view@6.38.1",
      "@codemirror/state@6.5.2",
      "@codemirror/commands@6.8.1",
      "@codemirror/lint@6.8.5",
      "@codemirror/autocomplete@6.18.6",
      "esbuild@0.25.6",
    ],
    { cwd: tempRoot },
  );

  const entryPath = join(tempRoot, "smoke-entry.mjs");
  await writeFile(entryPath, smokeEntrySource());

  const esbuildPath = join(
    tempRoot,
    "node_modules",
    "esbuild",
    "lib",
    "main.js",
  );
  const esbuild = await import(pathToFileURL(esbuildPath));
  await esbuild.build({
    entryPoints: [entryPath],
    bundle: true,
    // The wasm packages stay external (served from node_modules through
    // the import map, so the language server's worker and wasm resolve
    // next to its index.js); autocomplete bundles in with the editor.
    external: ["@aufbau/compiler", "@aufbau/lsp"],
    format: "esm",
    logLevel: "warning",
    outfile: join(tempRoot, "smoke.js"),
    platform: "browser",
  });

  await writeFile(join(tempRoot, "index.html"), smokePageSource());
  // A library the inline theory imports, fetched relative to the page.
  await mkdir(join(tempRoot, "lib"), { recursive: true });
  await writeFile(
    join(tempRoot, "lib", "smoke-base.mm0"),
    "provable sort wff;\nterm top: wff;\n",
  );
  const smokeServer = createResultServer(tempRoot, {
    resultPath: "/__smoke_result",
  });
  server = smokeServer.server;
  const address = await listen(server);
  const url = `http://127.0.0.1:${address.port}/index.html`;
  const browser = findBrowser();
  const result = await runBrowser(
    browser,
    url,
    tempRoot,
    smokeServer.result,
  );

  assert.equal(
    result.status,
    "passed",
    `browser smoke test failed:\n${result.detail}\n${result.stderr}`,
  );
  console.log(
    "Packed @aufbau/editor loads and verifies a two-cell document in Chromium.",
  );
} finally {
  if (server) await close(server);
  await rm(tempRoot, {
    force: true,
    maxRetries: 10,
    recursive: true,
    retryDelay: 100,
  });
}

function smokePageSource() {
  return String.raw`<!doctype html>
<html lang="en">
  <head>
    <meta charset="utf-8">
    <title>Aufbau editor browser smoke test</title>
    <script type="importmap">
      {
        "imports": {
          "@aufbau/compiler":
            "/node_modules/@aufbau/compiler/index.js",
          "@aufbau/lsp":
            "/node_modules/@aufbau/lsp/index.js"
        }
      }
    </script>
  </head>
  <body data-smoke="running">
    <aufbau-theory id="smoke-theory">
      <script type="text/mm0">
        import "lib/smoke-base.mm0";
        axiom top_i: $ top $;
      </script>
    </aufbau-theory>

    <aufbau-proof id="first" theory="smoke-theory" debounce="0" lsp="off">
      <script type="text/auf">
        lemma smoke: $ top $
        ----
        l1: $ top $ by top_i []
      </script>
    </aufbau-proof>

    <aufbau-proof id="second" theory="smoke-theory" debounce="0">
      <script type="text/mm0">
        theorem main: $ top $;
      </script>
      <script type="text/auf">
        main
        ----
        l1: $ top $ by smoke []
      </script>
    </aufbau-proof>

    <aufbau-index theory="smoke-theory"></aufbau-index>
    <pre id="result">running</pre>
    <script type="module" src="/smoke.js"></script>
  </body>
</html>
`;
}

function smokeEntrySource() {
  return String.raw`
const browserErrors = [];
window.addEventListener("error", (event) => {
  browserErrors.push(event.error?.stack ?? event.message);
});
window.addEventListener("unhandledrejection", (event) => {
  browserErrors.push(event.reason?.stack ?? String(event.reason));
});

try {
  const editor = await import("@aufbau/editor");
  await Promise.all([
    customElements.whenDefined("aufbau-theory"),
    customElements.whenDefined("aufbau-proof"),
    customElements.whenDefined("aufbau-index"),
  ]);

  const theory = document.querySelector("aufbau-theory");
  const proof = document.querySelector("#first");
  const second = document.querySelector("#second");
  const index = document.querySelector("aufbau-index");
  check(theory instanceof editor.AufbauTheory, "theory did not upgrade");
  check(proof instanceof editor.AufbauProof, "proof did not upgrade");
  check(index instanceof editor.AufbauIndex, "index did not upgrade");
  check((await theory.text()).includes("top_i"), "theory did not load");

  // Both cells verify: the theory's import was fetched and joined, and
  // the second cell's theorem sees the first cell's lemma through the
  // chain of cell files.
  for (const [cell, label] of [[proof, "first"], [second, "second"]]) {
    await waitFor(() => {
      const state = cell.statusState();
      if (state?.kind === "err") {
        throw new Error(label + " cell check failed: " + state.text);
      }
      return state?.kind === "ok";
    }, label + " cell did not reach verified state");
  }

  // The language server sees the same chain: hovering the lemma's name in
  // the second cell resolves it across the cell boundary.
  const body = second.shadowRoot.querySelector(".cm-content").textContent;
  const at = body.indexOf("smoke");
  check(at >= 0, "second cell body lost the lemma reference");
  const hover = await second.lspHover(at + 1);
  check(
    hover?.value?.includes("smoke"),
    "hover over a lemma from an earlier cell returned " + JSON.stringify(hover),
  );

  check(proof.shadowRoot, "proof has no shadow root");
  check(
    proof.shadowRoot.querySelector(".cm-editor"),
    "CodeMirror did not render",
  );
  check(
    proof.shadowRoot.querySelector('.status[data-kind="ok"]'),
    "verified status did not render",
  );

  await waitFor(
    () => index.shadowRoot?.querySelectorAll(".index-row").length >= 2,
    "statement index did not render",
  );
  const indexText = index.shadowRoot.textContent;
  check(indexText.includes("top_i"), "index omitted the axiom");
  check(indexText.includes("smoke"), "index omitted the lemma");
  check(indexText.includes("main"), "index omitted the theorem");
  check(browserErrors.length === 0, browserErrors.join("\n"));

  document.body.dataset.smoke = "passed";
  document.querySelector("#result").textContent = "passed";
  await reportSmokeResult("passed", "");
} catch (error) {
  const detail = error?.stack ?? String(error);
  document.body.dataset.smoke = "failed";
  document.querySelector("#result").textContent = detail;
  await reportSmokeResult("failed", detail);
}

async function reportSmokeResult(status, detail) {
  const response = await fetch("/__smoke_result", {
    method: "POST",
    headers: { "Content-Type": "application/json" },
    body: JSON.stringify({ status, detail }),
  });
  if (!response.ok) {
    throw new Error("unable to report browser smoke result");
  }
}

function check(condition, message) {
  if (!condition) throw new Error(message);
}

async function waitFor(predicate, message) {
  const deadline = performance.now() + 15000;
  while (performance.now() < deadline) {
    if (predicate()) return;
    await new Promise((resolveWait) => setTimeout(resolveWait, 25));
  }
  throw new Error(message);
}
`;
}
