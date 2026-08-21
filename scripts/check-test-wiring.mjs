#!/usr/bin/env node
// Guard against dark test suites: every test file must be transitively
// imported from one of build.zig's test roots.
//
// Zig only collects tests reachable from a test root's comptime imports,
// and the roots are wired by hand in build.zig — so a test file that loses
// (or never gains) its import edge silently stops running. That exact
// failure produced a suite that was dark from birth for months
// (the def_ops tests, repaired in task #206). This script makes the wiring
// a CI invariant instead of a memory.
//
// Mechanics: test roots are the `root_source_file` entries in build.zig
// whose path mentions "test". From each root we walk relative
// `@import("….zig")` edges (named module imports like "mm0" cross a module
// boundary, where Zig does not collect tests, so they are not followed).
// Every file under src/ or tests/ that looks like a test file — basename
// `tests.zig`, `*_tests.zig`, or living in a `tests/` directory — must be
// reachable.
import fs from "node:fs";
import path from "node:path";

const repoRoot = path.resolve(path.dirname(new URL(import.meta.url).pathname), "..");
const read = (rel) => fs.readFileSync(path.join(repoRoot, rel), "utf8");

// 1. Test roots from build.zig.
const roots = [];
for (const m of read("build.zig").matchAll(/root_source_file\s*=\s*b\.path\("([^"]+)"\)/g)) {
  if (/test/.test(m[1])) roots.push(m[1]);
}
if (roots.length === 0) {
  console.error("check-test-wiring: found no test roots in build.zig — the extraction regex is broken");
  process.exit(1);
}

// 2. Reachability via relative imports.
const reachable = new Set();
const queue = [...roots];
while (queue.length > 0) {
  const file = queue.pop();
  if (reachable.has(file)) continue;
  if (!fs.existsSync(path.join(repoRoot, file))) continue;
  reachable.add(file);
  for (const m of read(file).matchAll(/@import\("([^"]+\.zig)"\)/g)) {
    queue.push(path.normalize(path.join(path.dirname(file), m[1])));
  }
}

// 3. Candidate test files.
const candidates = [];
const walk = (dir) => {
  for (const entry of fs.readdirSync(path.join(repoRoot, dir), { withFileTypes: true })) {
    if (entry.name.startsWith(".")) continue;
    const rel = path.join(dir, entry.name);
    if (entry.isDirectory()) walk(rel);
    else if (entry.name.endsWith(".zig")) {
      const isTestFile =
        entry.name === "tests.zig" ||
        entry.name.endsWith("_tests.zig") ||
        rel.split(path.sep).includes("tests");
      if (isTestFile) candidates.push(rel);
    }
  }
};
walk("src");
walk("tests");

const dark = candidates.filter((c) => !reachable.has(c));
if (dark.length > 0) {
  for (const c of dark) {
    console.error(`${c}: not reachable from any test root (${roots.join(", ")})`);
  }
  console.error(`\n${dark.length} dark test file(s): wire them into a test root's import graph or delete them.`);
  process.exit(1);
}
console.log(`check-test-wiring: ${candidates.length} test files reachable from ${roots.length} roots`);
