#!/usr/bin/env node
// Compile every live cell in the manual with the native compiler.
//
// Renders each chapter through preprocessor/aufbau-cells.mjs, reassembles the
// documents exactly the way the editor's coordinator does (standalone cells
// are their own document; cells sharing a `doc`/`theory` attribute stitch in
// page order), and runs `abc compile` on each. The report lists one line per
// document so runs can be diffed: a page edit or prelude change that flips a
// cell from ok to error shows up as a one-line diff.
//
// Some cells fail by design (error demonstrations, cells left with search
// placeholders); the point of the report is the *diff*, not universal green.
//
// CI diffs this report (stdout only — the failure count goes to stderr)
// against the checked-in `manual/cells.expected`. When a change moves a cell
// on purpose, regenerate the baseline and review the diff:
//
//   node manual/scripts/check-cells.mjs --abc zig-out/bin/abc > manual/cells.expected
//
// Usage: node scripts/check-cells.mjs [--abc PATH] [--keep DIR]
//   --abc PATH   compiler binary (default ../zig-out/bin/abc)
//   --keep DIR   write the assembled mm0/auf pairs to DIR for inspection

import { readFileSync, readdirSync, writeFileSync, mkdirSync, mkdtempSync } from "node:fs";
import { execFileSync, execSync } from "node:child_process";
import { join, dirname } from "node:path";
import { fileURLToPath } from "node:url";
import { tmpdir } from "node:os";

const manualDir = dirname(dirname(fileURLToPath(import.meta.url)));
const args = process.argv.slice(2);
function argValue(flag) {
  const at = args.indexOf(flag);
  return at === -1 ? null : args[at + 1];
}
const abc = argValue("--abc") ?? join(manualDir, "..", "zig-out", "bin", "abc");
const keepDir = argValue("--keep");
const workDir = keepDir ?? mkdtempSync(join(process.env.TMPDIR ?? tmpdir(), "manual-cells-"));
if (keepDir) mkdirSync(keepDir, { recursive: true });

const srcDir = join(manualDir, "src");
let failures = 0;

for (const file of readdirSync(srcDir).sort()) {
  if (!file.endsWith(".md") || file === "SUMMARY.md") continue;
  const content = readFileSync(join(srcDir, file), "utf8");
  const book = { items: [{ Chapter: { content, sub_items: [] } }] };
  const rendered = execSync(`node ${JSON.stringify(join(manualDir, "preprocessor", "aufbau-cells.mjs"))}`, {
    input: JSON.stringify([{ root: manualDir }, book]),
    cwd: manualDir,
    maxBuffer: 64 * 1024 * 1024,
  });
  const html = JSON.parse(rendered).items[0].Chapter.content;

  // Documents in page order. Shared docs keep insertion order of their cells.
  // Only cells the preprocessor generated count — it wraps each in
  // <div class="aufbau-cell">. Literal <aufbau-*> tags in prose (e.g. inside
  // ```html fences on the embedding page) are documentation, not cells.
  const documents = new Map(); // key -> {mm0: [], auf: []}
  let standalone = 0;
  const wrapperRe = /^<div class="aufbau-cell">\n([\s\S]*?)\n<\/div>$/gm;
  const cellRe = /<(aufbau-proof|aufbau-theory)((?:\s+[-\w]+(?:="[^"]*")?)*)>([\s\S]*?)<\/\1>/g;
  let w;
  while ((w = wrapperRe.exec(html)) !== null) {
    cellRe.lastIndex = 0;
    let m;
    while ((m = cellRe.exec(w[1])) !== null) {
      const [, tag, attrText, inner] = m;
      if (tag === "aufbau-theory") continue; // hidden prelude holder; unused by compile
      const attr = (name) => {
        const hit = attrText.match(new RegExp(`\\s${name}="([^"]*)"`));
        return hit ? hit[1] : null;
      };
      // A src= cell's body lives behind a URL only the deployed site serves;
      // there is nothing to compile here, so exclude it rather than record a
      // vacuous ok for an empty pair.
      if (attr("src") != null) continue;
      // Grouping mirrors the editor coordinator's documentKeyFor
      // (web/packages/editor/index.js) — keep the two ladders in sync.
      const key =
        attr("theory") != null
          ? `theory:${attr("theory")}`
          : attr("theory-src") != null
            ? `theory-src:${attr("theory-src")}`
            : attr("doc") != null
              ? `doc:${attr("doc")}`
              : `cell${++standalone}`;
      const doc = documents.get(key) ?? { mm0: [], auf: [] };
      documents.set(key, doc);
      const scriptRe = /<script type="text\/(mm0|auf)">\n([\s\S]*?)\n<\/script>/g;
      let s;
      while ((s = scriptRe.exec(inner)) !== null) {
        (s[1] === "mm0" ? doc.mm0 : doc.auf).push(s[2]);
      }
    }
  }

  for (const [key, doc] of documents) {
    const stem = `${file.replace(/\.md$/, "")}--${key.replace(/[^\w]+/g, "_")}`;
    const mm0Path = join(workDir, `${stem}.mm0`);
    const aufPath = join(workDir, `${stem}.auf`);
    writeFileSync(mm0Path, doc.mm0.join("\n") + "\n");
    writeFileSync(aufPath, doc.auf.join("\n\n") + "\n");
    let status = "ok";
    try {
      execFileSync(abc, ["compile", mm0Path, aufPath, join(workDir, `${stem}.mmb`)], {
        stdio: ["ignore", "pipe", "pipe"],
      });
    } catch (err) {
      const firstLine = (err.stderr?.toString() ?? "").split("\n").find((l) => l.includes("error")) ?? "compile failed";
      status = `error: ${firstLine.trim()}`;
      failures += 1;
    }
    console.log(`${file} ${key}: ${status}`);
  }
}

console.error(`\n${failures} document(s) with errors (see report above)`);
