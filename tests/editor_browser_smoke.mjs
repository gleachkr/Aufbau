import assert from "node:assert/strict";
import { spawn, spawnSync } from "node:child_process";
import {
  mkdtemp,
  readFile,
  rm,
  stat,
  writeFile,
} from "node:fs/promises";
import { createServer } from "node:http";
import { tmpdir } from "node:os";
import { basename, extname, join, resolve } from "node:path";
import { pathToFileURL } from "node:url";

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
  for (const packageName of ["compiler", "editor"]) {
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
    external: [
      "@aufbau/compiler",
      "@aufbau/lsp",
      "@codemirror/autocomplete",
    ],
    format: "esm",
    logLevel: "warning",
    outfile: join(tempRoot, "smoke.js"),
    platform: "browser",
  });

  await writeFile(join(tempRoot, "index.html"), smokePageSource());
  const smokeServer = createSmokeServer(tempRoot);
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
    "Packed @aufbau/editor loads and verifies a proof in Chromium.",
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

function run(command, args, options = {}) {
  const result = spawnSync(command, args, {
    encoding: "utf8",
    ...options,
  });

  if (result.error) throw result.error;
  if (result.status !== 0) {
    const detail = [result.stdout, result.stderr]
      .filter(Boolean)
      .join("\n");
    throw new Error(
      `${basename(command)} exited with status ${result.status}\n${detail}`,
    );
  }
  return result.stdout;
}

function findBrowser() {
  const configured = process.env.CHROME;
  if (configured) return configured;

  for (const candidate of [
    "chromium",
    "chromium-browser",
    "google-chrome",
    "google-chrome-stable",
  ]) {
    const found = spawnSync("which", [candidate], {
      encoding: "utf8",
    });
    if (found.status === 0) return found.stdout.trim();
  }
  throw new Error(
    "Chromium was not found; set CHROME to a Chromium executable",
  );
}

function createSmokeServer(root) {
  let resolveResult;
  const result = new Promise((resolveSmoke) => {
    resolveResult = resolveSmoke;
  });
  const server = createServer(async (request, response) => {
    try {
      const url = new URL(request.url ?? "/", "http://localhost");
      if (url.pathname === "/__smoke_result") {
        const body = await readRequestBody(request);
        const report = JSON.parse(body);
        if (
          request.method !== "POST" ||
          !["passed", "failed"].includes(report.status) ||
          typeof report.detail !== "string"
        ) {
          response.writeHead(400).end("Invalid smoke result");
          return;
        }
        response.writeHead(204).end();
        resolveResult(report);
        return;
      }

      const path = resolve(root, `.${decodeURIComponent(url.pathname)}`);
      if (path !== root && !path.startsWith(`${root}/`)) {
        response.writeHead(403).end("Forbidden");
        return;
      }
      const info = await stat(path);
      if (!info.isFile()) throw new Error("not a file");
      const body = await readFile(path);
      response.writeHead(200, {
        "Content-Type": mimeType(path),
        "Cache-Control": "no-store",
      });
      response.end(body);
    } catch {
      response.writeHead(404).end("Not found");
    }
  });
  return { result, server };
}

async function readRequestBody(request) {
  const chunks = [];
  for await (const chunk of request) chunks.push(chunk);
  return Buffer.concat(chunks).toString("utf8");
}

function mimeType(path) {
  switch (extname(path)) {
    case ".html":
      return "text/html; charset=utf-8";
    case ".js":
    case ".mjs":
      return "text/javascript; charset=utf-8";
    case ".wasm":
      return "application/wasm";
    default:
      return "application/octet-stream";
  }
}

function listen(httpServer) {
  return new Promise((resolveListen, reject) => {
    httpServer.once("error", reject);
    httpServer.listen(0, "127.0.0.1", () => {
      httpServer.off("error", reject);
      resolveListen(httpServer.address());
    });
  });
}

function close(httpServer) {
  return new Promise((resolveClose, reject) => {
    httpServer.close((error) => {
      if (error) reject(error);
      else resolveClose();
    });
  });
}

async function runBrowser(browser, url, root, resultPromise) {
  try {
    return await launchBrowser(browser, url, root, resultPromise, 1);
  } catch (error) {
    if (!error?.timedOut) throw error;
    console.warn(
      `${basename(browser)} timed out without reporting; retrying once`,
    );
    return await launchBrowser(browser, url, root, resultPromise, 2);
  }
}

async function launchBrowser(browser, url, root, resultPromise, attempt) {
  const child = spawn(
    browser,
    [
      "--headless=new",
      "--no-sandbox",
      "--disable-background-networking",
      "--disable-dev-shm-usage",
      "--disable-gpu",
      "--no-default-browser-check",
      "--no-first-run",
      `--user-data-dir=${join(root, `chrome-profile-${attempt}`)}`,
      url,
    ],
    { detached: process.platform !== "win32" },
  );
  let stderr = "";
  child.stderr.setEncoding("utf8");
  child.stderr.on("data", (chunk) => {
    stderr += chunk;
  });

  const closed = new Promise((resolveClose, rejectClose) => {
    child.once("error", rejectClose);
    child.once("close", resolveClose);
  });
  let timeout;

  try {
    const result = await Promise.race([
      resultPromise,
      closed.then((status) => {
        throw new Error(
          `${basename(browser)} exited with status ${status}\n${stderr}`,
        );
      }),
      new Promise((_, rejectTimeout) => {
        timeout = setTimeout(() => {
          const error = new Error(
            `${basename(browser)} timed out\n${stderr}`,
          );
          error.timedOut = true;
          rejectTimeout(error);
        }, 90000);
      }),
    ]);
    return { ...result, stderr };
  } finally {
    clearTimeout(timeout);
    await stopBrowser(child, closed);
  }
}

async function stopBrowser(child, closed) {
  if (
    child.pid === undefined ||
    child.exitCode !== null ||
    child.signalCode !== null
  ) return;
  signalBrowser(child, "SIGTERM");
  const stopped = await Promise.race([
    closed.then(
      () => true,
      () => true,
    ),
    delay(5000).then(() => false),
  ]);
  if (stopped) return;
  signalBrowser(child, "SIGKILL");
  await closed.catch(() => {});
}

function signalBrowser(child, signal) {
  try {
    if (process.platform === "win32") child.kill(signal);
    else process.kill(-child.pid, signal);
  } catch (error) {
    if (error.code !== "ESRCH") throw error;
  }
}

function delay(milliseconds) {
  return new Promise((resolveDelay) => {
    setTimeout(resolveDelay, milliseconds);
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
            "/node_modules/@aufbau/compiler/index.js"
        }
      }
    </script>
  </head>
  <body data-smoke="running">
    <aufbau-theory id="smoke-theory">
      <script type="text/mm0">
        provable sort wff;
        term top: wff;
        axiom top_i: $ top $;
      </script>
    </aufbau-theory>

    <aufbau-proof theory="smoke-theory" debounce="0" lsp="off">
      <script type="text/auf">
        lemma smoke: $ top $
        ----
        l1: $ top $ by top_i []
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
  const proof = document.querySelector("aufbau-proof");
  const index = document.querySelector("aufbau-index");
  check(theory instanceof editor.AufbauTheory, "theory did not upgrade");
  check(proof instanceof editor.AufbauProof, "proof did not upgrade");
  check(index instanceof editor.AufbauIndex, "index did not upgrade");
  check((await theory.text()).includes("top_i"), "theory did not load");

  await waitFor(() => {
    const state = proof.statusState();
    if (state?.kind === "err") {
      throw new Error("proof check failed: " + state.text);
    }
    return state?.kind === "ok";
  }, "proof did not reach verified state");

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
