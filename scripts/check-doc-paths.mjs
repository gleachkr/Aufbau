#!/usr/bin/env node
// Guard against doc drift: every backtick-quoted file path in the
// architecture maps must point at a file that actually exists.
//
// ARCHITECTURE.md declares itself authoritative, so a stale path there is
// worse than no docs — it sends a reader to a file that moved or died.
// This check makes the maps self-enforcing, the same way
// manual/scripts/check-cells.mjs keeps the manual's editor cells honest.
//
// Rules:
// - Scanned docs: ARCHITECTURE.md, CLAUDE.md, *.md directly under docs/,
//   and any ARCHITECTURE.md nested under src/.
// - A checked token is a backtick-quoted string ending in a source-ish
//   extension, or a backtick-quoted directory path ending in `/`.
//   Tokens containing globs/placeholders (`*`, `{`, `$`, `<`) are skipped.
// - Multi-segment paths must resolve against one of a few roots (repo
//   root, src/, src/frontend/, src/trusted/, src/bin/, src/bin/compiler/,
//   or the doc's own directory — ARCHITECTURE.md's frontend file lists are
//   written relative to src/frontend/).
// - Bare filenames (no slash) also pass if the basename exists anywhere
//   under src/ — prose like "`checked_ir.zig` enforces …" shouldn't be
//   forced to spell the full path on every mention.
import fs from "node:fs";
import path from "node:path";

const repoRoot = path.resolve(path.dirname(new URL(import.meta.url).pathname), "..");

const docs = [];
for (const p of ["ARCHITECTURE.md", "CLAUDE.md"]) {
  if (fs.existsSync(path.join(repoRoot, p))) docs.push(p);
}
if (fs.existsSync(path.join(repoRoot, "docs"))) {
  for (const entry of fs.readdirSync(path.join(repoRoot, "docs"))) {
    if (entry.endsWith(".md")) docs.push(path.join("docs", entry));
  }
}
const findNested = (dir) => {
  for (const entry of fs.readdirSync(path.join(repoRoot, dir), { withFileTypes: true })) {
    const rel = path.join(dir, entry.name);
    if (entry.isDirectory() && !entry.name.startsWith(".")) findNested(rel);
    else if (entry.name === "ARCHITECTURE.md") docs.push(rel);
  }
};
findNested("src");

// Basename index of src/ for bare-filename mentions and rename hints.
const basenames = new Map();
const indexTree = (dir) => {
  for (const entry of fs.readdirSync(path.join(repoRoot, dir), { withFileTypes: true })) {
    const rel = path.join(dir, entry.name);
    if (entry.isDirectory() && !entry.name.startsWith(".")) indexTree(rel);
    else if (entry.isFile()) {
      if (!basenames.has(entry.name)) basenames.set(entry.name, []);
      basenames.get(entry.name).push(rel);
    }
  }
};
indexTree("src");

const roots = [
  "",
  "src",
  "src/frontend",
  "src/frontend/compiler",
  "src/trusted",
  "src/bin",
  "src/bin/compiler",
  "specs",
  "manual",
];
const checkedExt = /\.(zig|md|mjs|mm0|auf|mmb)$/;

let failures = 0;
for (const doc of docs) {
  const text = fs.readFileSync(path.join(repoRoot, doc), "utf8");
  const docDir = path.dirname(doc);
  const lines = text.split("\n");
  lines.forEach((line, idx) => {
    for (const match of line.matchAll(/`([^`\n]+)`/g)) {
      const token = match[1];
      if (/[*{$<>\s]/.test(token)) continue;
      // Bare extension mentions ("a `.auf` file") are prose, not paths.
      if (token.startsWith(".")) continue;
      const isDir = token.endsWith("/") && token.includes("/");
      if (!isDir && !checkedExt.test(token)) continue;
      const rel = isDir ? token.slice(0, -1) : token;

      const candidates = [...roots, docDir].map((r) => path.join(r, rel));
      const resolved = candidates.some((c) => fs.existsSync(path.join(repoRoot, c)));
      if (resolved) continue;
      if (!token.includes("/") && basenames.has(token)) continue;

      failures += 1;
      const hint = basenames.get(path.basename(rel));
      const suffix = hint ? ` (did you mean ${hint.join(" or ")}?)` : "";
      console.error(`${doc}:${idx + 1}: \`${token}\` does not exist${suffix}`);
    }
  });
}

if (failures > 0) {
  console.error(`\n${failures} stale doc path(s). Update the doc to match the tree.`);
  process.exit(1);
}
console.log(`check-doc-paths: ${docs.length} docs OK`);
