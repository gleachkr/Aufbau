// @aufbau/editor — an embeddable interactive proof editor.
//
// Custom elements:
//   <aufbau-theory id="…">  — holds a fixed MM0 theory prelude (inline or `src`).
//   <aufbau-proof>          — an editor for one proof cell, checked in-browser.
//
// See docs/design_notes/embeddable_editor.md for the design. This is the v2
// (assembled) model: every cell that shares a theory forms one *document*. On
// each edit the document coordinator stitches all cells — in DOM order — into a
// single `(mm0, auf)` pair, runs ONE debounced compile, and routes the compiler's
// per-cell diagnostics back to each editor. The compiler's analyze/recovery path
// means a broken or unfinished cell does not cascade red onto the cells that
// depend on it. There is no separate kernel-verify seal: a cell is "verified"
// only when the whole document compiles clean (meta.ok); otherwise a clean cell
// reads as "no errors (pending)".
//
//   - A lemma cell contributes an `.auf` block only (proves something not in the
//     mm0). A theorem cell also contributes an mm0 `theorem …;` declaration that
//     is stitched *into the document* (not the theory) — the same seam a future
//     editable mm0/def cell would use.

import {
  EditorView,
  keymap,
  highlightActiveLine,
  drawSelection,
} from "@codemirror/view";
import { EditorState } from "@codemirror/state";
import {
  defaultKeymap,
  history,
  historyKeymap,
  indentWithTab,
} from "@codemirror/commands";
import { lintGutter, setDiagnostics } from "@codemirror/lint";
import { loadCompiler } from "@aufbau/compiler";

// ---------------------------------------------------------------------------
// Engine. The compiler is stateless, so one instance serves every document on
// the page. Loaded lazily and shared through a single promise.
// ---------------------------------------------------------------------------

let compilerPromise = null;
function loadCompilerOnce() {
  if (!compilerPromise) compilerPromise = loadCompiler();
  return compilerPromise;
}

// Registries: <aufbau-theory> elements by id, and documents by theory key.
const theoryRegistry = new Map();
const documentRegistry = new Map();
let singletonSeq = 0;

// ---------------------------------------------------------------------------
// Text sourcing + small parsing helpers.
// ---------------------------------------------------------------------------

async function fetchText(url) {
  const res = await fetch(new URL(url, document.baseURI));
  if (!res.ok) throw new Error(`fetch ${url}: ${res.status}`);
  return dedent(await res.text());
}

async function readSource(el, { inlineType, srcAttr }) {
  const src = el.getAttribute(srcAttr);
  if (src) return fetchText(src);
  const script = el.querySelector(`script[type="${inlineType}"]`);
  if (script) return dedent(script.textContent ?? "");
  return null;
}

// Inline <script> blocks are indented to match the surrounding HTML. Strip the
// common leading indentation and any leading/trailing blank lines.
function dedent(text) {
  const lines = text.replace(/\t/g, "  ").split("\n");
  while (lines.length && lines[0].trim() === "") lines.shift();
  while (lines.length && lines[lines.length - 1].trim() === "") lines.pop();
  let indent = Infinity;
  for (const line of lines) {
    if (line.trim() === "") continue;
    indent = Math.min(indent, line.length - line.trimStart().length);
  }
  if (!Number.isFinite(indent)) indent = 0;
  return lines.map((l) => l.slice(indent)).join("\n");
}

// Split a proof into a fixed header block and an editable body at the `----`
// underline. Returns null (full-file mode) when the text isn't a single block.
function splitBlock(text) {
  const lines = text.split("\n");
  const underlines = [];
  for (let i = 0; i < lines.length; i += 1) {
    if (/^\s*-{3,}\s*$/.test(lines[i])) underlines.push(i);
  }
  if (underlines.length !== 1) return null; // 0 = no header; >1 = multi-block
  const ui = underlines[0];
  return {
    header: lines.slice(0, ui).join("\n"),
    underline: lines[ui],
    body: lines.slice(ui + 1).join("\n"),
  };
}

// Pull the name and hypothesis/conclusion formulas out of a block header.
// Formulas are the `$…$` segments in order; the last is the conclusion, the
// rest are hypotheses. A `lemma` block states its own assertion; a plain
// theorem block is just a name (its statement lives in the mm0, see `mm0Goal`).
function parseGoal(header) {
  const formulas = [...header.matchAll(/\$([^$]*)\$/g)].map((m) => m[1].trim());
  const nameMatch = header.match(/(?:lemma|theorem)?\s*([A-Za-z_][\w']*)/);
  const name = nameMatch ? nameMatch[1] : null;
  if (formulas.length === 0) return { name, hyps: [], concl: null };
  return { name, hyps: formulas.slice(0, -1), concl: formulas.at(-1) };
}

// A plain theorem block's `.auf` header is only a name; its statement is the
// matching MM0 `theorem <name> (…): … ;` declaration. Parse the assertion tail
// out of that declaration (looked up in the cell's own mm0 fragment, then the
// shared theory) for the goal display.
function mm0Goal(mm0Text, name) {
  if (!mm0Text || !name) return null;
  const decl = new RegExp(
    `\\btheorem\\s+${name.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")}\\b[^;]*`,
  ).exec(mm0Text);
  if (!decl) return null;
  const formulas = [...decl[0].matchAll(/\$([^$]*)\$/g)].map((m) => m[1].trim());
  if (formulas.length === 0) return null;
  return { name, hyps: formulas.slice(0, -1), concl: formulas.at(-1) };
}

// Byte offset (UTF-8, as reported by the compiler) → JS string index (UTF-16),
// needed because the proof texts are unicode-heavy (⊢, ∀, →, ∈, …).
const utf8 = new TextEncoder();
function byteLen(str) {
  return utf8.encode(str).length;
}
function byteToCharIndex(str, byteOffset) {
  let bytes = 0;
  for (let i = 0; i < str.length; ) {
    if (bytes >= byteOffset) return i;
    const ch = String.fromCodePoint(str.codePointAt(i));
    bytes += utf8.encode(ch).length;
    i += ch.length;
  }
  return str.length;
}

function severityOf(diag) {
  if (diag.severity === "warning") return "warning";
  if (diag.severity === "error") return "error";
  return "info";
}

// ---------------------------------------------------------------------------
// Pure stitching + routing (kept side-effect free so they can be unit-tested).
// ---------------------------------------------------------------------------

// Concatenate `fragments` (each `{ id, text }`, skipping empty text) with the
// given separator, returning the joined string plus a byte range per fragment.
// `base` (if non-empty) is placed first without a tracked range.
function stitch(base, fragments, sep) {
  let text = base ?? "";
  const ranges = [];
  for (const frag of fragments) {
    if (!frag.text) continue;
    if (text.length) text += sep;
    const start = byteLen(text);
    text += frag.text;
    ranges.push({ id: frag.id, start, end: byteLen(text) });
  }
  return { text, ranges };
}

// Assign each compiler diagnostic to the cell whose stitched byte range owns it.
// Returns a Map<cellId, { proof: [...], banner: [...] }> plus `theory` diags
// (mm0 diagnostics that fall in the shared base theory, i.e. author errors).
// `proof` diagnostics carry a `localByte` offset into that cell's editable body.
function routeDiagnostics(diagnostics, { aufRanges, mm0Ranges, bodyStartOf }) {
  const perCell = new Map();
  const theory = [];
  const cellEntry = (id) => {
    let e = perCell.get(id);
    if (!e) {
      e = { proof: [], banner: [] };
      perCell.set(id, e);
    }
    return e;
  };
  const owning = (ranges, offset) =>
    ranges.find((r) => offset >= r.start && offset < r.end);

  for (const d of diagnostics) {
    if (d.spanStart == null) continue;
    if (d.source === "proof") {
      const r = owning(aufRanges, d.spanStart);
      if (!r) continue;
      const bodyStart = bodyStartOf(r.id);
      const localByte = d.spanStart - bodyStart;
      const localEnd = (d.spanEnd ?? d.spanStart) - bodyStart;
      if (localEnd <= 0) {
        cellEntry(r.id).banner.push(d); // inside the fixed header
      } else {
        cellEntry(r.id).proof.push({ diag: d, localByte, localEnd });
      }
    } else {
      const r = owning(mm0Ranges, d.spanStart);
      if (r) cellEntry(r.id).banner.push(d);
      else theory.push(d); // fell in the base theory
    }
  }
  return { perCell, theory };
}

// ---------------------------------------------------------------------------
// <aufbau-theory>
// ---------------------------------------------------------------------------

class AufbauTheory extends HTMLElement {
  connectedCallback() {
    if (this.id) theoryRegistry.set(this.id, this);
    this.style.display = "none";
    this._text = readSource(this, { inlineType: "text/mm0", srcAttr: "src" });
  }
  disconnectedCallback() {
    if (this.id && theoryRegistry.get(this.id) === this) {
      theoryRegistry.delete(this.id);
    }
  }
  text() {
    return this._text ?? Promise.resolve(null);
  }
}

// ---------------------------------------------------------------------------
// AufbauDocument — coordinates all cells that share a theory.
// ---------------------------------------------------------------------------

function documentKeyFor(cell) {
  const ref = cell.getAttribute("theory");
  if (ref) return `theory:${ref}`;
  const src = cell.getAttribute("theory-src");
  if (src) return `theory-src:${src}`;
  return null; // standalone → singleton document
}

function getOrCreateDocument(cell) {
  const key = documentKeyFor(cell);
  if (key == null) return new AufbauDocument(cell, `singleton:${singletonSeq++}`);
  let doc = documentRegistry.get(key);
  if (!doc) {
    doc = new AufbauDocument(cell, key);
    documentRegistry.set(key, doc);
  }
  return doc;
}

class AufbauDocument {
  constructor(representative, key) {
    this.key = key;
    this.cells = new Set();
    this._theoryRef = representative.getAttribute("theory");
    this._theorySrc = representative.getAttribute("theory-src");
    this._theoryText = null;
    this._timer = null;
  }

  register(cell) {
    this.cells.add(cell);
  }

  unregister(cell) {
    this.cells.delete(cell);
    if (this.cells.size === 0 && documentRegistry.get(this.key) === this) {
      documentRegistry.delete(this.key);
    }
  }

  // The shared base theory (axioms/terms/notation). Cell-contributed mm0
  // declarations are NOT part of this — they are stitched at check time.
  theoryText() {
    if (!this._theoryText) {
      if (this._theoryRef) {
        const el = theoryRegistry.get(this._theoryRef);
        this._theoryText = el
          ? Promise.resolve(el.text())
          : Promise.reject(new Error(`unknown theory "${this._theoryRef}"`));
      } else if (this._theorySrc) {
        this._theoryText = fetchText(this._theorySrc);
      } else {
        this._theoryText = Promise.resolve("");
      }
    }
    return this._theoryText;
  }

  // Cells in DOM order.
  orderedCells() {
    return [...this.cells].sort((a, b) => {
      const rel = a.compareDocumentPosition(b);
      if (rel & Node.DOCUMENT_POSITION_FOLLOWING) return -1;
      if (rel & Node.DOCUMENT_POSITION_PRECEDING) return 1;
      return 0;
    });
  }

  scheduleCheck(cell, delay) {
    const attr = cell?.getAttribute("debounce");
    const ms = delay ?? Number.parseInt(attr ?? "300", 10);
    clearTimeout(this._timer);
    if (attr === "manual" && delay == null) return;
    this._timer = setTimeout(
      () => this.check(),
      Number.isFinite(ms) ? ms : 300,
    );
  }

  async check() {
    const cells = this.orderedCells().filter((c) => c.isReady());
    if (cells.length === 0) return;
    for (const c of cells) c.setStatus("busy", "checking…");

    let compiler;
    let theory;
    try {
      [compiler, theory] = await Promise.all([
        loadCompilerOnce(),
        this.theoryText(),
      ]);
    } catch (err) {
      for (const c of cells) c.setStatus("err", `load error: ${err.message}`);
      return;
    }

    const mm0 = stitch(
      theory ?? "",
      cells.map((c) => ({ id: c, text: c.mm0Fragment() })),
      "\n",
    );
    const auf = stitch(
      "",
      cells.map((c) => ({ id: c, text: c.aufText() })),
      "\n\n",
    );

    let result;
    try {
      result = compiler.compile(mm0.text, auf.text);
    } catch (err) {
      for (const c of cells) c.setStatus("err", `compiler error: ${err.message}`);
      return;
    }

    const meta = result.meta ?? {};
    const diagnostics = meta.diagnostics ?? [];
    const bodyStartByte = new Map();
    for (const r of auf.ranges) bodyStartByte.set(r.id, r.start + r.id.prefixBytes());
    const routed = routeDiagnostics(diagnostics, {
      aufRanges: auf.ranges,
      mm0Ranges: mm0.ranges,
      bodyStartOf: (id) => bodyStartByte.get(id),
    });

    const durationMs = Math.round(result.durationMs ?? 0);
    for (const c of cells) {
      const entry = routed.perCell.get(c) ?? { proof: [], banner: [] };
      c.applyRouting(entry, {
        ok: Boolean(meta.ok),
        durationMs,
        theoryDiags: routed.theory,
      });
    }
  }
}

// ---------------------------------------------------------------------------
// <aufbau-proof>
// ---------------------------------------------------------------------------

class AufbauProof extends HTMLElement {
  connectedCallback() {
    if (this._booted) return;
    this._booted = true;
    this.attachShadow({ mode: "open" });
    // Preserve the raw proof source for the static fallback before we build UI.
    this._rawProof = this.querySelector('script[type="text/auf"]')?.textContent;
    this._ready = false;
    this.boot().catch((err) => this.renderFallback(err));
  }

  disconnectedCallback() {
    this._doc?.unregister(this);
  }

  async boot() {
    this._doc = getOrCreateDocument(this);
    this._doc.register(this);

    const proofText = await readSource(this, {
      inlineType: "text/auf",
      srcAttr: "src",
    });
    if (proofText == null) throw new Error("no proof source (inline or src)");
    if (this._rawProof == null) this._rawProof = proofText;

    // A cell's inline text/mm0 is its declaration contribution to the document.
    const inlineMm0 = this.querySelector('script[type="text/mm0"]');
    this._mm0Fragment = inlineMm0 ? dedent(inlineMm0.textContent ?? "") : "";

    const block = splitBlock(proofText);
    this._prefix = block ? `${block.header}\n${block.underline}\n` : "";
    this._prefixBytesValue = byteLen(this._prefix);
    this._body = block ? block.body : proofText;

    // Goal display: a lemma block states its own assertion; a theorem block gets
    // its statement from the mm0 — the cell's own fragment first, then the theory.
    let goal = block ? parseGoal(block.header) : null;
    if (goal && !goal.concl) {
      goal =
        mm0Goal(this._mm0Fragment, goal.name) ??
        mm0Goal(await this._doc.theoryText(), goal.name) ??
        goal;
    }
    this.renderChrome(goal);
    await this.mountEditor(this._body);

    this._ready = true;
    this._doc.scheduleCheck(this, 0);
  }

  // --- fragment accessors used by the document coordinator ---
  isReady() {
    return this._ready === true;
  }
  mm0Fragment() {
    return this._mm0Fragment ?? "";
  }
  prefixBytes() {
    return this._prefixBytesValue ?? 0;
  }
  aufText() {
    const body = this._view ? this._view.state.doc.toString() : this._body;
    return this._prefix + body;
  }

  renderChrome(goal) {
    const root = this.shadowRoot;
    root.innerHTML = "";
    const style = document.createElement("style");
    style.textContent = STYLE;
    root.append(style);

    const host = document.createElement("div");
    host.className = "aufbau";
    host.dataset.theme = this.getAttribute("theme") ?? "auto";

    if (goal && (goal.concl || goal.hyps.length)) {
      const g = document.createElement("div");
      g.className = "goal";
      if (goal.name) {
        const n = document.createElement("span");
        n.className = "goal-name";
        n.textContent = `${goal.name}:`;
        g.append(n);
      }
      for (const h of goal.hyps) g.append(formulaChip(h, "hyp"));
      if (goal.hyps.length && goal.concl) {
        const turnstile = document.createElement("span");
        turnstile.className = "turnstile";
        turnstile.textContent = "⊢";
        g.append(turnstile);
      }
      if (goal.concl) g.append(formulaChip(goal.concl, "concl"));
      host.append(g);
    }

    this._banner = document.createElement("div");
    this._banner.className = "banner";
    this._banner.hidden = true;
    host.append(this._banner);

    this._editorHost = document.createElement("div");
    this._editorHost.className = "editor";
    // Height/max-height apply to the inner CodeMirror editor (via inherited CSS
    // custom properties) so the scroller can bound and scroll its content.
    const h = this.getAttribute("height");
    if (h) this._editorHost.style.setProperty("--editor-height", h);
    const mh = this.getAttribute("max-height");
    if (mh) this._editorHost.style.setProperty("--editor-max-height", mh);
    host.append(this._editorHost);

    if (this.getAttribute("status") !== "off") {
      this._status = document.createElement("div");
      this._status.className = "status";
      this.setStatus("idle", "ready");
      host.append(this._status);
    }
    root.append(host);
  }

  async mountEditor(body) {
    const readonly = this.hasAttribute("readonly");
    const onEdit = EditorView.updateListener.of((u) => {
      if (u.docChanged) this._doc.scheduleCheck(this);
    });
    this._view = new EditorView({
      parent: this._editorHost,
      state: EditorState.create({
        doc: body,
        extensions: [
          history(),
          drawSelection(),
          highlightActiveLine(),
          lintGutter(),
          keymap.of([...defaultKeymap, ...historyKeymap, indentWithTab]),
          EditorView.lineWrapping,
          EditorState.readOnly.of(readonly),
          EditorView.editable.of(!readonly),
          onEdit,
        ],
      }),
    });
  }

  // Apply the document's routing result to this cell: in-body squiggles, a
  // banner for header/mm0/theory errors, and a status line.
  applyRouting(entry, { ok, durationMs, theoryDiags }) {
    const body = this._view ? this._view.state.doc.toString() : this._body;
    const cm = [];
    for (const { diag, localByte, localEnd } of entry.proof) {
      const from = byteToCharIndex(body, Math.max(0, localByte));
      const to = Math.max(from, byteToCharIndex(body, Math.max(0, localEnd)));
      cm.push({
        from,
        to,
        severity: severityOf(diag),
        message: diag.message + (diag.lineLabel ? ` (at ${diag.lineLabel})` : ""),
      });
    }
    if (this._view) {
      this._view.dispatch(setDiagnostics(this._view.state, cm));
    }

    const errors = entry.proof.filter((p) => p.diag.severity === "error");
    const bannerDiag =
      entry.banner.find((d) => d.severity === "error") ??
      theoryDiags.find((d) => d.source === "mm0" && d.severity === "error");
    this.setBanner(bannerDiag);

    if (errors.length || bannerDiag) {
      const n = errors.length + entry.banner.length;
      this.setStatus(
        "err",
        bannerDiag && bannerDiag.source === "mm0" && !entry.banner.length
          ? `theory error: ${bannerDiag.message}`
          : `${n || "compile"} error${n === 1 ? "" : "s"}`,
      );
    } else if (ok) {
      this.setStatus("ok", `✓ verified · ${durationMs} ms`);
    } else {
      // Clean cell, but the document has errors elsewhere: no hard seal.
      this.setStatus("note", "no errors (pending)");
    }
  }

  setBanner(diag) {
    if (!this._banner) return;
    if (!diag) {
      this._banner.hidden = true;
      this._banner.textContent = "";
      return;
    }
    this._banner.hidden = false;
    this._banner.textContent = diag.message;
  }

  setStatus(kind, text) {
    if (!this._status) return;
    this._status.dataset.kind = kind;
    this._status.textContent = text;
  }

  // Robust degradation: show the source read-only if anything fails to load.
  renderFallback(err) {
    console.error("[aufbau-proof] falling back to static source:", err);
    const root = this.shadowRoot ?? this.attachShadow({ mode: "open" });
    root.innerHTML = "";
    const style = document.createElement("style");
    style.textContent = STYLE;
    const pre = document.createElement("pre");
    pre.className = "fallback";
    pre.textContent = (this._rawProof ?? "").trim();
    root.append(style, pre);
  }
}

function formulaChip(text, kind) {
  const el = document.createElement("code");
  el.className = `formula ${kind}`;
  el.textContent = text;
  return el;
}

// ---------------------------------------------------------------------------
// Styles (scoped to the shadow root).
// ---------------------------------------------------------------------------

const STYLE = `
:host { display: block; margin: 1rem 0; }
.aufbau {
  --bg: #ffffff; --fg: #1c1c22; --muted: #6b7280; --line: #e5e7eb;
  --hyp: #eef2ff; --concl: #ecfdf5; --ok: #059669; --err: #dc2626;
  --warnbg: #fef2f2;
  border: 1px solid var(--line); border-radius: 8px; overflow: hidden;
  font-family: ui-monospace, "SF Mono", Menlo, Consolas, monospace;
  color: var(--fg); background: var(--bg);
}
.aufbau[data-theme="dark"] {
  --bg: #16181d; --fg: #e6e6ea; --muted: #9aa0aa; --line: #2b2f38;
  --hyp: #24304d; --concl: #12332a; --ok: #34d399; --err: #f87171;
  --warnbg: #3a1d1d;
}
@media (prefers-color-scheme: dark) {
  .aufbau[data-theme="auto"] {
    --bg: #16181d; --fg: #e6e6ea; --muted: #9aa0aa; --line: #2b2f38;
    --hyp: #24304d; --concl: #12332a; --ok: #34d399; --err: #f87171;
    --warnbg: #3a1d1d;
  }
}
.goal {
  display: flex; flex-wrap: wrap; align-items: center; gap: .4rem;
  padding: .5rem .7rem; border-bottom: 1px solid var(--line);
  background: color-mix(in srgb, var(--fg) 3%, var(--bg));
}
.goal-name { color: var(--muted); font-weight: 600; margin-right: .3rem; }
.turnstile { color: var(--muted); }
.banner {
  padding: .4rem .7rem; font-size: .85em; color: var(--err);
  background: var(--warnbg); border-bottom: 1px solid var(--line);
}
.editor .cm-editor {
  height: var(--editor-height, auto);
  max-height: var(--editor-max-height, none);
}
.editor .cm-scroller { overflow: auto; font-family: inherit; }
/* Keep the lint gutter invisible until it holds an error marker. The
   !important beats CodeMirror's own gutter theme, injected into the shadow
   root after this stylesheet at equal specificity. */
.editor .cm-gutters {
  background: var(--bg) !important;
  border-right: none !important;
}
.status {
  padding: .35rem .7rem; font-size: .82em; border-top: 1px solid var(--line);
  color: var(--muted);
}
.status[data-kind="ok"] { color: var(--ok); }
.status[data-kind="err"] { color: var(--err); }
.status[data-kind="busy"] { color: var(--muted); font-style: italic; }
.status[data-kind="note"] { color: var(--muted); }
.fallback {
  margin: 0; padding: .7rem; overflow: auto; white-space: pre;
  font-family: ui-monospace, monospace; font-size: .9em;
  border: 1px solid #e5e7eb; border-radius: 8px;
}
`;

if (!customElements.get("aufbau-theory")) {
  customElements.define("aufbau-theory", AufbauTheory);
}
if (!customElements.get("aufbau-proof")) {
  customElements.define("aufbau-proof", AufbauProof);
}

export { AufbauProof, AufbauTheory, stitch, routeDiagnostics };
