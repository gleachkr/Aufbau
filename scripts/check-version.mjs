import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";

const packagePaths = [
  "web/packages/compiler/package.json",
  "web/packages/verifier/package.json",
  "web/packages/lsp/package.json",
  "web/packages/editor/package.json",
];

const version = (await readFile("VERSION", "utf8")).trim();
assert.match(
  version,
  /^(0|[1-9]\d*)\.(0|[1-9]\d*)\.(0|[1-9]\d*)$/,
  `VERSION must contain a stable semantic version, got ${version}`,
);

const zon = await readFile("build.zig.zon", "utf8");
const zonMatch = zon.match(/^\s*\.version\s*=\s*"([^"]+)"/m);
assert.ok(zonMatch, "build.zig.zon has no package version");
assert.equal(
  zonMatch[1],
  version,
  `build.zig.zon has ${zonMatch[1]}, expected ${version}`,
);

for (const path of packagePaths) {
  const manifest = JSON.parse(await readFile(path, "utf8"));
  assert.equal(
    manifest.version,
    version,
    `${path} has ${manifest.version}, expected ${version}`,
  );
}

const expected = process.argv[2];
if (expected !== undefined) {
  assert.equal(
    version,
    expected,
    `release expects ${expected}, found ${version}`,
  );
}

console.log(`Release versions agree on ${version}.`);
