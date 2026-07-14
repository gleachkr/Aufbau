import assert from "node:assert/strict";
import { mkdtemp, rm, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import { basename, join, resolve } from "node:path";
import { spawnSync } from "node:child_process";

const packageRoot = resolve(process.argv[2] ?? "zig-out/npm/@aufbau");
const fixtureRoot = resolve("tests/proof_cases");
const tempRoot = await mkdtemp(join(tmpdir(), "aufbau-node-wasm-"));

try {
  await writeFile(
    join(tempRoot, "package.json"),
    JSON.stringify({ private: true, type: "module" }),
  );

  const tarballs = [];
  for (const packageName of ["compiler", "verifier", "lsp"]) {
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
    ],
    { cwd: tempRoot },
  );

  const runner = join(tempRoot, "smoke.mjs");
  await writeFile(runner, smokeTestSource());
  run(process.execPath, [runner, fixtureRoot], {
    cwd: tempRoot,
    stdio: "inherit",
  });
} finally {
  await rm(tempRoot, { force: true, recursive: true });
}

function run(command, args, options = {}) {
  const result = spawnSync(command, args, {
    encoding: "utf8",
    ...options,
  });

  if (result.error) throw result.error;
  if (result.status !== 0) {
    const detail = [result.stdout, result.stderr].filter(Boolean).join("\n");
    throw new Error(
      `${basename(command)} exited with status ${result.status}\n${detail}`,
    );
  }
  return result.stdout;
}

function smokeTestSource() {
  return String.raw`
import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import { join } from "node:path";
import { loadCompiler } from "@aufbau/compiler";
import { loadLspServer } from "@aufbau/lsp";
import { loadVerifier } from "@aufbau/verifier";

const fixtureRoot = process.argv[2];
const mm0Text = await readFile(join(fixtureRoot, "pass_label.mm0"), "utf8");
const proofText = await readFile(join(fixtureRoot, "pass_label.auf"), "utf8");

const compiler = await loadCompiler();
const compiled = compiler.compile(mm0Text, proofText);
assert.equal(compiled.ok, true, JSON.stringify(compiled.meta));
assert.ok(compiled.mmbBytes.length > 0, "compiler returned an empty MMB");

const verifier = await loadVerifier();
const verified = verifier.verifyPair(mm0Text, compiled.mmbBytes);
assert.equal(verified.ok, true, JSON.stringify(verified.meta));

const lsp = await loadLspServer();
const output = lsp.process({
  jsonrpc: "2.0",
  id: 1,
  method: "initialize",
  params: {
    capabilities: {},
    processId: null,
    rootUri: null,
  },
});
const response = output.map(JSON.parse).find((message) => message.id === 1);
assert.ok(response?.result?.capabilities, "LSP initialization failed");

console.log("Packed npm WASM packages load and run under Node.");
`;
}
