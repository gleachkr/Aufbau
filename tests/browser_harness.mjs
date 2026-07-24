// Shared plumbing for the headless-browser tests: a static file server with a
// result-reporting endpoint, and a Chromium launcher that waits for the page to
// POST its verdict.
//
// Both browser tests follow the same shape — serve a directory, open a page in
// headless Chromium, let the page report `{status, detail}` back over HTTP, and
// tear the browser down — so the harness lives here rather than being copied.

import { spawn, spawnSync } from "node:child_process";
import { readFile, stat } from "node:fs/promises";
import { createServer } from "node:http";
import { basename, extname, resolve } from "node:path";

export function run(command, args, options = {}) {
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

export function findBrowser() {
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

// Serve `root` statically. A POST to `resultPath` resolves the returned
// `result` promise with the page's verdict; `headers` are added to every static
// response (used to hand out CORS on a second origin).
export function createResultServer(root, options = {}) {
  const resultPath = options.resultPath ?? "/__result";
  const extraHeaders = options.headers ?? {};
  const serverRoot = resolve(root);
  let resolveResult;
  const result = new Promise((resolveReport) => {
    resolveResult = resolveReport;
  });
  const server = createServer(async (request, response) => {
    try {
      const url = new URL(request.url ?? "/", "http://localhost");
      if (url.pathname === resultPath) {
        const body = await readRequestBody(request);
        const report = JSON.parse(body);
        if (
          request.method !== "POST" ||
          !["passed", "failed"].includes(report.status) ||
          typeof report.detail !== "string"
        ) {
          response.writeHead(400).end("Invalid result");
          return;
        }
        response.writeHead(204).end();
        resolveResult(report);
        return;
      }

      const path = resolve(serverRoot, `.${decodeURIComponent(url.pathname)}`);
      if (path !== serverRoot && !path.startsWith(`${serverRoot}/`)) {
        response.writeHead(403).end("Forbidden");
        return;
      }
      const info = await stat(path);
      if (!info.isFile()) throw new Error("not a file");
      const body = await readFile(path);
      response.writeHead(200, {
        "Content-Type": mimeType(path),
        "Cache-Control": "no-store",
        ...extraHeaders,
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

export function mimeType(path) {
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

export function listen(httpServer) {
  return new Promise((resolveListen, reject) => {
    httpServer.once("error", reject);
    httpServer.listen(0, "127.0.0.1", () => {
      httpServer.off("error", reject);
      resolveListen(httpServer.address());
    });
  });
}

export function close(httpServer) {
  return new Promise((resolveClose, reject) => {
    httpServer.close((error) => {
      if (error) reject(error);
      else resolveClose();
    });
  });
}

// Headless Chromium occasionally comes up without ever reaching the page on a
// loaded machine, so a timeout earns one clean retry before it is a failure.
export async function runBrowser(browser, url, root, resultPromise) {
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
      `--user-data-dir=${resolve(root, `chrome-profile-${attempt}`)}`,
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
