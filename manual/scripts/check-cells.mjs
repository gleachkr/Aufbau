#!/usr/bin/env node
// Compile every live cell in the manual with the native compiler.
//
// Renders each chapter through preprocessor/aufbau-cells.mjs, lays each
// document out the way the editor's coordinator does (standalone cells are
// their own document; cells sharing a `doc`/`theory` attribute are combined,
// as a chain of per-cell `cN.mm0`/`cN.auf` files each importing the previous
// cell's, behind a `prelude.mm0`), and runs `abc compile` on the last cell's
// file of each. A document left holding search placeholders goes through
// `abc search --fill` first and the filled proof is compiled instead, so the
// report says whether each search demo still finds its proof. Every MMB that
// compiles is then checked by the verifier against the joined `.mm0`, so a
// compile the kernel rejects shows up as an error, not an ok. The report
// lists one line per document so runs can be diffed: a page edit or prelude
// change that flips a cell from ok to error shows up as a one-line diff.
//
// Some cells fail by design (error demonstrations, a search meant to miss);
// the point of the report is the *diff*, not universal green.
//
// CI diffs this report (stdout only — the failure count goes to stderr)
// against the checked-in `manual/cells.expected`. When a change moves a cell
// on purpose, regenerate the baseline and review the diff:
//
//   node manual/scripts/check-cells.mjs --abc zig-out/bin/abc > manual/cells.expected
//
// Usage: node scripts/check-cells.mjs [--abc PATH] [--verifier PATH] [--keep DIR]
//   --abc PATH        compiler binary (default ../zig-out/bin/abc)
//   --verifier PATH   verifier binary (default mm0-zig next to the compiler)
//   --keep DIR        write the assembled documents (one directory each) to DIR

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
const verifier = argValue("--verifier") ?? join(dirname(abc), "mm0-zig");
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
  const documents = new Map(); // key -> [{mm0, auf}] cells in page order
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
      const doc = documents.get(key) ?? [];
      documents.set(key, doc);
      const cell = { mm0: null, auf: null };
      const scriptRe = /<script type="text\/(mm0|auf)">\n([\s\S]*?)\n<\/script>/g;
      let s;
      while ((s = scriptRe.exec(inner)) !== null) {
        cell[s[1]] = s[2];
      }
      doc.push(cell);
    }
  }

  for (const [key, cells] of documents) {
    const stem = `${file.replace(/\.md$/, "")}--${key.replace(/[^\w]+/g, "_")}`;
    const dir = join(workDir, stem);
    mkdirSync(dir, { recursive: true });
    // The manual's documents carry no shared <aufbau-theory> prelude (cells
    // inline theirs), so the prelude file is empty; the chain still starts
    // from it, as in the browser.
    writeFileSync(join(dir, "prelude.mm0"), "");
    let previous = "prelude.mm0";
    let mm0Path = null;
    let aufPath = null;
    cells.forEach((cell, index) => {
      const name = `c${index + 1}`;
      mm0Path = join(dir, `${name}.mm0`);
      writeFileSync(
        mm0Path,
        `import ${JSON.stringify(previous)};\n${cell.mm0 == null ? "" : cell.mm0 + "\n"}`,
      );
      aufPath = null;
      if (cell.auf != null) {
        aufPath = join(dir, `${name}.auf`);
        writeFileSync(aufPath, cell.auf + "\n");
      }
      previous = `${name}.mm0`;
    });
    // `abc compile` wants a proof file; a theory cell at the end of the
    // chain gets an empty one (the editor leaves it to sibling pairing).
    if (aufPath == null) {
      aufPath = mm0Path.replace(/\.mm0$/, ".auf");
      writeFileSync(aufPath, "");
    }
    let status = compile(mm0Path, aufPath, dir);
    if (status.includes("search placeholder")) status = searchThenCompile(mm0Path, aufPath, dir);
    if (!status.startsWith("ok") && !status.startsWith("sorry")) failures += 1;
    console.log(`${file} ${key}: ${status}`);
  }
}

console.error(`\n${failures} document(s) with errors (see report above)`);

// Compile one document (proof from `input` when given, as `abc compile` reads
// `-` from stdin), verify the MMB, and return its report status.
function compile(mm0Path, aufPath, dir, input) {
  const mmbPath = join(dir, "out.mmb");
  try {
    execFileSync(abc, ["compile", mm0Path, input == null ? aufPath : "-", mmbPath], {
      input,
      stdio: [input == null ? "ignore" : "pipe", "pipe", "pipe"],
    });
  } catch (err) {
    // Compiled, but a line is admitted with `sorry!` (abc's exit 3).
    if (err.status === 3) return "sorry";
    return `error: ${firstError(err.stderr)}`;
  }
  try {
    const joined = execFileSync(abc, ["join", mm0Path], { stdio: ["ignore", "pipe", "pipe"] });
    execFileSync(verifier, [mmbPath], { input: joined, stdio: ["pipe", "pipe", "pipe"] });
  } catch (err) {
    return `error: verify: ${firstLine(err.stderr)}`;
  }
  return "ok";
}

// A document left holding search placeholders: run the search, then compile
// the filled proof, so the baseline pins whether each demo still finds.
function searchThenCompile(mm0Path, aufPath, dir) {
  let filled;
  try {
    filled = execFileSync(abc, ["search", "--fill", mm0Path, aufPath], {
      stdio: ["ignore", "pipe", "pipe"],
      encoding: "utf8",
    });
  } catch (err) {
    // Exit 4: a marker has no proof; the report's last line is the tally.
    if (err.status === 4) return `search: ${lastLine(err.stderr)}`;
    return `error: ${firstError(err.stderr)}`;
  }
  const status = compile(mm0Path, aufPath, dir, filled);
  return status === "ok" ? "ok after search" : `${status} (after search)`;
}

function firstError(stderr) {
  return ((stderr?.toString() ?? "").split("\n").find((l) => l.includes("error")) ?? "compile failed").trim();
}

function firstLine(stderr) {
  return (stderr?.toString() ?? "").trim().split("\n")[0] || "verification failed";
}

function lastLine(stderr) {
  return (stderr?.toString() ?? "").trim().split("\n").at(-1);
}
