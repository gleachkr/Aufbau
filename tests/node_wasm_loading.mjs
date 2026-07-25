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

// The search tactics are offered wherever a rule name is, and they survive the
// server's applicable-rule filter — no rule filter can vouch for a placeholder.
lsp.process({ jsonrpc: "2.0", method: "initialized", params: {} });
const ruleLine = "l1: $ p $ by auto?";
for (const [uri, languageId, text] of [
  [
    "file:///smoke.mm0",
    "mm0",
    "provable sort wff;\naxiom use (p: wff): $ p $;\ntheorem main (p: wff): $ p $ > $ p $;\n",
  ],
  ["file:///smoke.auf", "aufbau", "main\n----\n" + ruleLine + "\n"],
]) {
  lsp.process({
    jsonrpc: "2.0",
    method: "textDocument/didOpen",
    params: { textDocument: { uri, languageId, version: 1, text } },
  });
}
const completionOutput = lsp.process({
  jsonrpc: "2.0",
  id: 2,
  method: "textDocument/completion",
  params: {
    textDocument: { uri: "file:///smoke.auf" },
    position: { line: 2, character: ruleLine.length },
  },
});
const completion = completionOutput
  .map(JSON.parse)
  .find((message) => message.id === 2);
const items = Array.isArray(completion?.result)
  ? completion.result
  : (completion?.result?.items ?? []);
for (const tactic of ["auto?", "exact?", "apply?", "conversion?"]) {
  assert.ok(
    items.some((item) => item.label === tactic),
    "LSP completion omitted " + tactic,
  );
}
// Completing over a placeholder replaces its trailing question mark too.
const exact = items.find((item) => item.label === "exact?");
assert.deepEqual(
  [exact.textEdit.range.start.character, exact.textEdit.range.end.character],
  [ruleLine.indexOf("auto?"), ruleLine.length],
);

// A half-typed rule name does not parse, and must still not cost the reader
// the rest of the block: the indexer recovers per line.
const brokenLines = [
  "l1: $ p $ by use []",
  "l2: $ p $ by a?",
  "l3: $ p $ by use []",
];
for (const [uri, languageId, text] of [
  [
    "file:///broken.mm0",
    "mm0",
    "provable sort wff;\naxiom use (p: wff): $ p $;\ntheorem main (p: wff): $ p $ > $ p $;\n",
  ],
  [
    "file:///broken.auf",
    "aufbau",
    "main\n----\n" + brokenLines.join("\n") + "\n",
  ],
]) {
  lsp.process({
    jsonrpc: "2.0",
    method: "textDocument/didOpen",
    params: { textDocument: { uri, languageId, version: 1, text } },
  });
}
function brokenCompletion(id, line, character) {
  const output = lsp.process({
    jsonrpc: "2.0",
    id,
    method: "textDocument/completion",
    params: {
      textDocument: { uri: "file:///broken.auf" },
      position: { line, character },
    },
  });
  const message = output.map(JSON.parse).find((entry) => entry.id === id);
  const result = Array.isArray(message?.result)
    ? message.result
    : (message?.result?.items ?? []);
  return result.map((item) => item.label);
}
const brokenLabels = brokenCompletion(3, 3, brokenLines[1].length);
assert.ok(
  brokenLabels.includes("auto?"),
  "completion on a half-typed line omitted auto?",
);
// The typed token holds a question mark, so it can only become a placeholder
// and the theory's rules drop out of the list.
assert.ok(
  !brokenLabels.includes("use"),
  "a placeholder token still offered rule completions",
);
// The broken line's own label survives for the lines that follow it.
const refLabels = brokenCompletion(4, 4, "l3: $ p $ by use [".length);
for (const label of ["l1", "l2"]) {
  assert.ok(
    refLabels.includes(label),
    "reference completion after a half-typed line omitted " + label,
  );
}

console.log("Packed npm WASM packages load and run under Node.");
`;
}
