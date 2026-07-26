#!/usr/bin/env node
// mdbook preprocessor: turn fenced ```aufbau-theory / ```aufbau-proof blocks
// into live <aufbau-theory>/<aufbau-proof> web components.
//
// Authoring model
// ---------------
//   ```aufbau-theory id=chain
//   provable sort wff;
//   term top: wff;
//   axiom top_i: $ top $;
//   ```
//
//   ```aufbau-proof theory=chain
//   lemma helper: $ top $
//   ----
//   l1: $ top $ by top_i []
//   ```
//
// A proof block may carry its own theory (standalone cell) or an mm0
// declaration (theorem/def cell) ahead of the proof, fenced off with an
// `@@mm0` / `@@auf` marker pair:
//
//   ```aufbau-proof
//   @@mm0
//   provable sort wff; term top: wff; axiom top_i: $ top $;
//   @@auf
//   lemma smoke: $ top $
//   ----
//   l1: $ top $ by top_i []
//   ```
//
// Info-string tokens after the language become element attributes:
// `key=value` (bare or "quoted") and bare flags (`readonly`). So
// `aufbau-proof theory=chain readonly theme=auto` →
// `<aufbau-proof theory="chain" readonly theme="auto">`.
//
// Shared preludes
// ---------------
// `prelude=nd-base,nd-rules` inlines `preludes/nd-base.mm0` and
// `preludes/nd-rules.mm0` as the cell's mm0, ahead of any `@@mm0` section,
// and is consumed rather than emitted as an attribute. Each such cell stays
// a *standalone* document — cells only share a document when they share a
// `theory`/`theory-src`/`doc` — which is what a page full of independent
// search demos needs, since a cell with an unresolved placeholder suppresses
// code actions in later cells of the same document.
//
// The same files can be displayed with ```aufbau-listing prelude=nd-rules```,
// so what a page shows the reader is literally what its cells load.

import { readFileSync } from "node:fs";
import { join } from "node:path";

if (process.argv[2] === "supports") {
  // `mdbook` asks whether we support a given renderer; we only touch html.
  process.exit(process.argv[3] === "html" ? 0 : 1);
}

const [context, book] = JSON.parse(readFileSync(0, "utf8"));
const preludeDir = join(context?.root ?? process.cwd(), "preludes");
const preludeCache = new Map();
walk(book.items);
process.stdout.write(JSON.stringify(book));

// Read `preludes/NAME.mm0`. A missing file fails the build loudly: a cell
// silently missing its theory would show up as a wall of confusing
// diagnostics instead.
function prelude(name) {
  if (!preludeCache.has(name)) {
    const path = join(preludeDir, `${name}.mm0`);
    try {
      preludeCache.set(name, readFileSync(path, "utf8").split("\n"));
    } catch {
      throw new Error(`aufbau-cells: cannot read prelude ${path}`);
    }
  }
  return preludeCache.get(name);
}

function preludeLines(value) {
  return value
    .split(",")
    .map((name) => name.trim())
    .filter(Boolean)
    .flatMap((name) => prelude(name));
}

function walk(items) {
  for (const item of items) {
    const chapter = item?.Chapter;
    if (!chapter) continue;
    if (typeof chapter.content === "string") {
      chapter.content = transform(chapter.content);
    }
    if (Array.isArray(chapter.sub_items)) walk(chapter.sub_items);
  }
}

function transform(markdown) {
  const lines = markdown.split("\n");
  const out = [];
  let index = 0;

  while (index < lines.length) {
    const line = lines[index];
    const open = line.match(/^(\s*)(`{3,}|~{3,})\s*(aufbau-\S+)(.*)$/);
    if (!open) {
      out.push(line);
      index += 1;
      continue;
    }

    const [, indent, fence, lang, rest] = open;
    const closer = new RegExp(`^\\s*${fence[0]}{${fence.length},}\\s*$`);
    const body = [];
    index += 1;
    while (index < lines.length && !closer.test(lines[index])) {
      body.push(lines[index]);
      index += 1;
    }
    index += 1; // consume the closing fence (or run off the end)

    out.push(renderCell(indent, lang, rest, body));
  }

  return out.join("\n");
}

function renderCell(indent, lang, infoRest, body) {
  const attrs = parseAttributes(infoRest);
  if (lang === "aufbau-theory") return renderTheory(attrs, body);
  if (lang === "aufbau-proof") return renderProof(attrs, body);
  if (lang === "aufbau-listing") return renderListing(indent, attrs, body);
  // Unknown aufbau-* language: leave the source visible rather than drop it.
  return `${indent}<pre><code>${escapeText(body.join("\n"))}</code></pre>`;
}

function renderTheory(attrs, body) {
  const open = openTag("aufbau-theory", attrs);
  return oneBlock([
    open,
    script("text/mm0", body),
    "</aufbau-theory>",
  ]);
}

// A read-only listing of prelude files, as an ordinary highlighted code
// block. Lets a page show the rules its cells are loading without keeping a
// second copy of them in the prose.
function renderListing(indent, attrs, body) {
  const spec = takeAttribute(attrs, "prelude");
  const lines = spec === null ? body : preludeLines(spec);
  const text = escapeText(trimBlank(lines).join("\n"));
  return `${indent}<pre><code class="language-mm0">${text}</code></pre>`;
}

function renderProof(attrs, body) {
  const spec = takeAttribute(attrs, "prelude");
  const { mm0, auf } = splitProofBody(body);
  const preamble = spec === null ? mm0 : [...preludeLines(spec), ...mm0];
  const parts = [openTag("aufbau-proof", attrs)];
  if (preamble.length) parts.push(script("text/mm0", preamble));
  if (auf.length) parts.push(script("text/auf", auf));
  parts.push("</aufbau-proof>");
  return oneBlock(parts);
}

// `@@mm0` … `@@auf` splits an optional mm0 preamble from the proof; with no
// marker the whole body is auf (a cell that leans on a shared theory).
function splitProofBody(body) {
  const start = body.findIndex((l) => l.trim() === "@@mm0");
  if (start === -1) return { mm0: [], auf: body };
  const divide = body.findIndex((l) => l.trim() === "@@auf");
  if (divide === -1) return { mm0: body.slice(start + 1), auf: [] };
  return {
    mm0: body.slice(start + 1, divide),
    auf: body.slice(divide + 1),
  };
}

function script(type, body) {
  // Script content is passed through verbatim — the browser reads it as raw
  // text, and mm0/auf never contain the literal "</script". No HTML escaping,
  // or the editor would show &gt; instead of >.
  return `<script type="${type}">\n${trimBlank(body).join("\n")}\n</script>`;
}

// Emit one CommonMark "HTML block": a <div> wrapper with no interior blank
// line, so pulldown-cmark passes the whole thing through verbatim instead of
// splitting it at a blank line and re-parsing the halves as markdown.
function oneBlock(parts) {
  const inner = parts
    .join("\n")
    .split("\n")
    .filter((l) => l.trim() !== "")
    .join("\n");
  return `<div class="aufbau-cell">\n${inner}\n</div>`;
}

function trimBlank(body) {
  let start = 0;
  let end = body.length;
  while (start < end && body[start].trim() === "") start += 1;
  while (end > start && body[end - 1].trim() === "") end -= 1;
  return body.slice(start, end);
}

// Pull a build-time directive out of the info string so it does not reach
// the element as an attribute.
function takeAttribute(attrs, name) {
  const at = attrs.findIndex((attr) => attr.name === name);
  if (at === -1) return null;
  const [attr] = attrs.splice(at, 1);
  return attr.value ?? "";
}

function parseAttributes(info) {
  const attrs = [];
  const pattern = /(\S+?)=("[^"]*"|'[^']*'|\S+)|(\S+)/g;
  let match;
  while ((match = pattern.exec(info)) !== null) {
    if (match[3] !== undefined) {
      attrs.push({ name: match[3], value: null });
    } else {
      const raw = match[2];
      const value =
        raw.startsWith('"') || raw.startsWith("'") ? raw.slice(1, -1) : raw;
      attrs.push({ name: match[1], value });
    }
  }
  return attrs;
}

function openTag(name, attrs) {
  const rendered = attrs.map(({ name: key, value }) =>
    value === null ? ` ${key}` : ` ${key}="${escapeAttr(value)}"`,
  );
  return `<${name}${rendered.join("")}>`;
}

function escapeAttr(value) {
  return value.replace(/&/g, "&amp;").replace(/"/g, "&quot;");
}

function escapeText(value) {
  return value
    .replace(/&/g, "&amp;")
    .replace(/</g, "&lt;")
    .replace(/>/g, "&gt;");
}
