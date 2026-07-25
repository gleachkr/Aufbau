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
//     is stitched *into the document* (not the theory). A definition cell uses
//     the same seam for a bodyless `def …;` declaration whose `.auf` content is
//     the public body filler — the definiens (and any hidden dummy binders it
//     needs) is what the reader edits, and the cells that prove things *about*
//     the definition check it. A local-def cell's `.auf` content is a
//     proof-local definition (it declares its own signature, nothing in the
//     mm0) usable by every later cell. A theory cell has mm0 content and no
//     `.auf` at all: its editable body IS its mm0 fragment, so terms and
//     axioms can be authored in place; with the `doc` grouping attribute a
//     page needs no <aufbau-theory> element at all.

import {
  EditorView,
  keymap,
  highlightActiveLine,
  drawSelection,
  hoverTooltip,
  Decoration,
  WidgetType,
} from "@codemirror/view";
import {
  EditorState,
  Compartment,
  StateField,
  StateEffect,
} from "@codemirror/state";
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

// ---------------------------------------------------------------------------
// LSP interaction (hover + applicable-rule completion). Optional and lazy: the
// wasm language server (a shared web worker) plus @codemirror/autocomplete are
// dynamically imported the first time a cell is focused or moused over, so
// readers who never touch a proof pay nothing, and a page that doesn't map
// `@aufbau/lsp` just gets no tooltips. Compile feedback stays with the compiler
// path — the server's publishDiagnostics notifications are ignored.
// ---------------------------------------------------------------------------

class LspRpc {
  constructor(server) {
    this.server = server;
    this.nextId = 1;
    this.pending = new Map();
    server.subscribe((raw) => {
      let msg;
      try {
        msg = JSON.parse(raw);
      } catch {
        return;
      }
      const waiter = msg.id != null && this.pending.get(msg.id);
      if (!waiter) return; // a notification (e.g. publishDiagnostics)
      this.pending.delete(msg.id);
      if (msg.error) waiter.reject(new Error(msg.error.message ?? "LSP error"));
      else waiter.resolve(msg.result ?? null);
    });
  }

  request(method, params) {
    return this.requestCancellable(method, params).promise;
  }

  // Cancellation is best-effort: the worker runs one message at a time, so a
  // `$/cancelRequest` only takes effect once the current search returns.
  requestCancellable(method, params) {
    const id = this.nextId++;
    const promise = new Promise((resolve, reject) => {
      this.pending.set(id, { resolve, reject });
      this.server.send({ jsonrpc: "2.0", id, method, params });
    });
    return { promise, cancel: () => this.notify("$/cancelRequest", { id }) };
  }

  notify(method, params) {
    this.server.send({ jsonrpc: "2.0", method, params });
  }
}

let lspPromise = null;
function loadLspOnce() {
  if (!lspPromise) {
    lspPromise = (async () => {
      const { loadLspServerWorker } = await import("@aufbau/lsp");
      const rpc = new LspRpc(await loadLspServerWorker());
      // No snippet support advertised → the server only sends plain-text edits.
      await rpc.request("initialize", {
        processId: null,
        rootUri: "file:///aufbau-editor",
        capabilities: {},
      });
      rpc.notify("initialized", {});
      return rpc;
    })();
  }
  return lspPromise;
}

let lspDocSeq = 0;

// Completion fragments: a word (rule/term names, `auto?`), or a run of
// notation-symbol characters (`->`, `∀`, `∧`, `==>`, …) — everything except
// whitespace, word characters, and structural punctuation. The two never mix,
// so a fragment stays valid while it grows within one class and triggers a
// fresh server query when it doesn't.
const WORD_FRAGMENT = /[\w'!?]+/;
const SYMBOL_FRAGMENT = /[^\w\s$()[\]{},;:.]+/u;
const FRAGMENT_VALID = /^(?:[\w'!?]*|[^\w\s$()[\]{},;:.]*)$/u;

// Map LSP CompletionItemKind numbers onto CodeMirror completion type names
// (which drive the icons in the popup).
const CM_COMPLETION_TYPES = {
  2: "method", // axiom/theorem/lemma
  3: "function", // term/def
  6: "variable", // binder
  7: "class", // sort
  12: "constant", // hypothesis
  14: "keyword",
  18: "text", // proof-line reference
  24: "keyword", // notation operator
};

// Code actions: when the caret pauses on a search placeholder (`auto?` /
// `exact?` / `apply?`), the server offers proof suggestions. The offer renders
// as a line-end bulb whose menu applies the chosen edit. Whether an offer
// exists is entirely the server's call — the client never scans proof text.
const setCellActions = StateEffect.define();

const cellActionField = StateField.define({
  create() {
    return null;
  },
  update(value, tr) {
    // Any edit invalidates the stored offsets and the actions themselves.
    if (tr.docChanged) value = null;
    for (const effect of tr.effects) {
      if (effect.is(setCellActions)) value = effect.value;
    }
    return value;
  },
  provide: (field) =>
    EditorView.decorations.from(field, (value) => {
      if (!value) return Decoration.none;
      return Decoration.set([
        Decoration.widget({
          widget: new ActionBulb(value.cell, value.actions),
          side: 1,
        }).range(value.pos),
      ]);
    }),
});

// Minimalist outline lightbulb (the FontAwesome lightbulb-o silhouette the
// main demo gets from a Nerd Font glyph, redrawn as inline SVG so it renders
// identically without any font dependency).
const BULB_SVG =
  '<svg viewBox="0 0 16 16" width="1em" height="1em" aria-hidden="true" ' +
  'fill="none" stroke="currentColor" stroke-width="1.2" ' +
  'stroke-linecap="round" stroke-linejoin="round">' +
  '<path d="M8 1.75a4.25 4.25 0 0 1 2.45 7.72c-.5.36-.83.9-.93 1.5l-.02.28h-3l-.02-.28c-.1-.6-.43-1.14-.93-1.5A4.25 4.25 0 0 1 8 1.75Z"/>' +
  '<path d="M6.6 13.4h2.8"/><path d="M7.1 14.9h1.8"/></svg>';

class ActionBulb extends WidgetType {
  constructor(cell, actions) {
    super();
    this.cell = cell;
    this.actions = actions;
  }

  eq(other) {
    return other.actions === this.actions;
  }

  toDOM() {
    const bulb = document.createElement("span");
    bulb.className = "action-bulb";
    bulb.innerHTML = BULB_SVG;
    const label =
      this.actions.length === 1
        ? this.actions[0].title
        : `${this.actions.length} suggestions`;
    bulb.title = label;
    bulb.setAttribute("role", "button");
    bulb.setAttribute("aria-label", label);
    bulb.setAttribute("tabindex", "0");
    const open = (event) => {
      event.preventDefault();
      event.stopPropagation();
      this.cell.openActionMenu(bulb, this.actions);
    };
    bulb.addEventListener("mousedown", open);
    bulb.addEventListener("keydown", (event) => {
      if (event.key === "Enter" || event.key === " ") open(event);
    });
    return bulb;
  }

  ignoreEvent() {
    return true;
  }
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

function escapeRe(text) {
  return text.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
}

// A plain theorem block's `.auf` header is only a name; its statement is the
// matching MM0 `theorem <name> (…): … ;` declaration. Parse the assertion tail
// out of that declaration (looked up in the cell's own mm0 fragment, then the
// shared theory) for the goal display.
function mm0Goal(mm0Text, name) {
  if (!mm0Text || !name) return null;
  const decl = new RegExp(
    `\\btheorem\\s+${escapeRe(name)}\\b[^;]*`,
  ).exec(mm0Text);
  if (!decl) return null;
  const formulas = [...decl[0].matchAll(/\$([^$]*)\$/g)].map((m) => m[1].trim());
  if (formulas.length === 0) return null;
  return { name, hyps: formulas.slice(0, -1), concl: formulas.at(-1) };
}

// A definition cell's proof text is a public def body filler: a `def` item
// with no `----` underline (so splitBlock returned null). Returns the def's
// name, or null when the text doesn't start with a def item.
function defFillerName(text) {
  const m = /^\s*def\s+([A-Za-z_][\w']*)/.exec(text);
  return m ? m[1] : null;
}

// The declaration a definition cell is filling: a bodyless `def <name> …;` in
// the mm0 (no `=` before the `;`). Returns the signature tail after the name
// (binders and return sort, e.g. `: wff`), or null when there is no match.
function mm0DefSignature(mm0Text, name) {
  if (!mm0Text || !name) return null;
  const decl = new RegExp(`\\bdef\\s+${escapeRe(name)}\\b([^;=]*);`).exec(
    mm0Text,
  );
  return decl ? decl[1].trim() : null;
}

// A proof-local definition declares its own signature in the `.auf` item: a
// top-level `: sort` in the header tail before the `=`. Returns that tail, or
// null for a public body filler (whose declaration lives in the mm0 instead).
function localDefSignature(text) {
  const m = /^\s*def\s+[A-Za-z_][\w']*([^=]*)=/.exec(text);
  if (!m) return null;
  let depth = 0;
  for (const ch of m[1]) {
    if (ch === "(" || ch === "{") depth += 1;
    else if (ch === ")" || ch === "}") depth -= 1;
    else if (ch === ":" && depth === 0) return m[1].trim();
  }
  return null;
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

// Number of newlines before `charIndex` — the line delta that maps a cell's
// body-local LSP positions into the stitched document it starts within.
function lineDeltaAt(text, charIndex) {
  let delta = 0;
  for (let i = 0; i < charIndex; i += 1) {
    if (text.charCodeAt(i) === 10) delta += 1;
  }
  return delta;
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
// `mm0BodyOwned(id)` marks cells whose editable body IS their mm0 fragment
// (theory cells): their mm0 diagnostics localize like proof ones instead of
// becoming banners.
function routeDiagnostics(
  diagnostics,
  { aufRanges, mm0Ranges, bodyStartOf, mm0BodyOwned },
) {
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
      if (!r) {
        theory.push(d); // fell in the base theory
      } else if (mm0BodyOwned?.(r.id)) {
        cellEntry(r.id).proof.push({
          diag: d,
          localByte: d.spanStart - r.start,
          localEnd: (d.spanEnd ?? d.spanStart) - r.start,
        });
      } else {
        cellEntry(r.id).banner.push(d);
      }
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
  // `doc` groups cells with no shared <aufbau-theory> at all (empty base
  // theory) — the natural pairing for theory cells, which bring their own mm0.
  const doc = cell.getAttribute("doc");
  if (doc) return `doc:${doc}`;
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
    this.indexes = new Set();
    this._theoryRef = representative.getAttribute("theory");
    this._theorySrc = representative.getAttribute("theory-src");
    this._theoryText = null;
    this._timer = null;
    this._lsp = null;
    this._statements = null; // latest statement snapshot (name-hover lookups)
    this._lastDocState = null; // latest check result (replayed to late indexes)
  }

  register(cell) {
    this.cells.add(cell);
  }

  unregister(cell) {
    this.cells.delete(cell);
    this._maybeRetire();
  }

  registerIndex(el) {
    this.indexes.add(el);
    // A late-arriving index catches up on the last completed check.
    if (this._lastDocState) el.applyDocument(this._lastDocState);
  }

  unregisterIndex(el) {
    this.indexes.delete(el);
    this._maybeRetire();
  }

  _maybeRetire() {
    if (
      this.cells.size === 0 &&
      this.indexes.size === 0 &&
      documentRegistry.get(this.key) === this
    ) {
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
      mm0BodyOwned: (id) => id.isTheoryCell(),
    });

    // Pretty-printed statement snapshots, keyed the way cells look them up
    // (defs live in the term namespace, everything else in the rule one).
    const statements = new Map();
    for (const s of meta.statements ?? []) {
      statements.set(`${s.kind === "def" ? "def" : "rule"}:${s.name}`, s);
    }

    const durationMs = Math.round(result.durationMs ?? 0);
    for (const c of cells) {
      const entry = routed.perCell.get(c) ?? { proof: [], banner: [] };
      c.applyRouting(entry, {
        ok: Boolean(meta.ok),
        durationMs,
        theoryDiags: routed.theory,
      });
      c.applyStatements(statements);
    }

    this._statements = statements;
    this._lastDocState = { statements, cells, ok: Boolean(meta.ok) };
    for (const idx of this.indexes) idx.applyDocument(this._lastDocState);
  }

  // Prepare an LSP view of this document for one cell: sync the stitched
  // `(mm0, auf)` pair to the language server as a sibling document pair, and
  // return the request context — the auf uri plus the line delta that maps the
  // cell's body-local positions into the stitched document. Restitched on every
  // request (it's cheap) so hover/completion always see the live text.
  async lspContext(cell) {
    const [rpc, theory] = await Promise.all([loadLspOnce(), this.theoryText()]);
    const cells = this.orderedCells().filter((c) => c.isReady());
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

    if (!this._lsp) {
      const root = `file:///aufbau-editor/doc${lspDocSeq++}`;
      this._lsp = {
        mm0Uri: `${root}/current.mm0`,
        aufUri: `${root}/current.auf`,
        mm0Version: 0,
        aufVersion: 0,
        lastMm0: null,
        lastAuf: null,
      };
    }
    const s = this._lsp;
    // The mm0 must be synced first: analyzing a proof reads its sibling .mm0.
    if (s.lastMm0 !== mm0.text) {
      s.lastMm0 = mm0.text;
      syncLspDoc(rpc, s.mm0Uri, "mm0", ++s.mm0Version, mm0.text);
    }
    if (s.lastAuf !== auf.text) {
      s.lastAuf = auf.text;
      syncLspDoc(rpc, s.aufUri, "aufbau", ++s.aufVersion, auf.text);
    }

    // A theory cell's body lives in the stitched mm0; every other cell's body
    // lives in the stitched auf after its fixed prefix.
    if (cell.isTheoryCell()) {
      const range = mm0.ranges.find((r) => r.id === cell);
      if (!range) return null;
      const bodyCharStart = byteToCharIndex(mm0.text, range.start);
      return { rpc, uri: s.mm0Uri, lineDelta: lineDeltaAt(mm0.text, bodyCharStart) };
    }
    const range = auf.ranges.find((r) => r.id === cell);
    if (!range) return null;
    const bodyCharStart =
      byteToCharIndex(auf.text, range.start) + cell.prefixText().length;
    return { rpc, uri: s.aufUri, lineDelta: lineDeltaAt(auf.text, bodyCharStart) };
  }
}

function syncLspDoc(rpc, uri, languageId, version, text) {
  if (version === 1) {
    rpc.notify("textDocument/didOpen", {
      textDocument: { uri, languageId, version, text },
    });
  } else {
    rpc.notify("textDocument/didChange", {
      textDocument: { uri, version },
      contentChanges: [{ text }],
    });
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
    // Preserve the raw source for the static fallback before we build UI (a
    // theory cell has no text/auf; its mm0 fragment is the content).
    this._rawProof =
      this.querySelector('script[type="text/auf"]')?.textContent ??
      this.querySelector('script[type="text/mm0"]')?.textContent;
    this._ready = false;
    this.boot().catch((err) => this.renderFallback(err));
  }

  disconnectedCallback() {
    this.closeActionMenu();
    this._doc?.unregister(this);
  }

  async boot() {
    this._doc = getOrCreateDocument(this);
    this._doc.register(this);

    // A cell's inline text/mm0 is its declaration contribution to the document.
    const inlineMm0 = this.querySelector('script[type="text/mm0"]');
    this._mm0Fragment = inlineMm0 ? dedent(inlineMm0.textContent ?? "") : "";

    const proofText = await readSource(this, {
      inlineType: "text/auf",
      srcAttr: "src",
    });
    // An mm0 fragment with no proof source makes this a theory cell: the
    // fragment itself is what the editor holds and edits.
    this._mm0Editable = proofText == null && this._mm0Fragment !== "";
    if (proofText == null && !this._mm0Editable) {
      throw new Error("no proof source (inline or src)");
    }
    if (this._rawProof == null) this._rawProof = proofText ?? this._mm0Fragment;

    let goal = null;
    if (this._mm0Editable) {
      this._prefix = "";
      this._prefixBytesValue = 0;
      this._body = this._mm0Fragment;
    } else {
      const block = splitBlock(proofText);
      this._prefix = block ? `${block.header}\n${block.underline}\n` : "";
      this._prefixBytesValue = byteLen(this._prefix);
      this._body = block ? block.body : proofText;

      // Goal display: a lemma block states its own assertion; a theorem block
      // gets its statement from the mm0 — the cell's own fragment first, then
      // the theory. A definition cell (a def item, so no `----` split) shows
      // the signature it inhabits: the bodyless mm0 declaration for a public
      // filler, the item's own header for a proof-local def. These are
      // source-derived first renders; after each compile, `applyStatements`
      // swaps in the compiler's pretty-printed forms under `_stmtKey`.
      goal = block ? parseGoal(block.header) : null;
      if (goal && !goal.concl) {
        goal =
          mm0Goal(this._mm0Fragment, goal.name) ??
          mm0Goal(await this._doc.theoryText(), goal.name) ??
          goal;
      }
      if (block && goal?.name) this._stmtKey = `rule:${goal.name}`;
      if (!block) {
        const defName = defFillerName(proofText);
        if (defName) this._stmtKey = `def:${defName}`;
        const signature =
          mm0DefSignature(this._mm0Fragment, defName) ??
          mm0DefSignature(await this._doc.theoryText(), defName) ??
          localDefSignature(proofText);
        if (defName && signature != null) goal = { name: defName, signature };
      }
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
  isTheoryCell() {
    return this._mm0Editable === true;
  }
  mm0Fragment() {
    if (this._mm0Editable) {
      return this._view ? this._view.state.doc.toString() : this._body;
    }
    return this._mm0Fragment ?? "";
  }
  prefixBytes() {
    return this._prefixBytesValue ?? 0;
  }
  prefixText() {
    return this._prefix ?? "";
  }
  aufText() {
    if (this._mm0Editable) return "";
    const body = this._view ? this._view.state.doc.toString() : this._body;
    return this._prefix + body;
  }
  // The statements-snapshot key this cell owns (`rule:name` / `def:name`),
  // or null for theory and full-file cells.
  statementKey() {
    return this._stmtKey ?? null;
  }
  statusState() {
    return this._statusState ?? null;
  }

  // Briefly highlight this cell — the index panel's click-to-scroll target.
  flash() {
    const host = this._container;
    if (!host) return;
    host.classList.remove("flash");
    void host.offsetWidth; // restart the animation on repeat clicks
    host.classList.add("flash");
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
    this._container = host; // positioning context for the code-action menu

    this._goalEl = buildGoalRow(goal);
    if (this._goalEl) host.append(this._goalEl);

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

  // Replace (or introduce) the goal row in place — used when a compile brings
  // pretty-printed statement data that supersedes the source-derived render.
  renderGoalRow(goal) {
    const next = buildGoalRow(goal);
    if (!next) return;
    if (this._goalEl) {
      this._goalEl.replaceWith(next);
    } else {
      this._container.prepend(next);
    }
    this._goalEl = next;
  }

  // Upgrade the goal display from the compiler's statement snapshots: the
  // pretty-printed statement for theorem/lemma cells, the signature plus the
  // live definiens for definition cells. Entries whose render failed
  // (`concl`/`signature` null) leave the source-derived display in place.
  applyStatements(statements) {
    if (!this._stmtKey) return;
    const stmt = statements.get(this._stmtKey);
    if (!stmt) {
      // A definition invalidated by recovery vanishes from the snapshot:
      // drop the stale definiens chip but keep the signature on display.
      if (this._stmtKey.startsWith("def:") && this._lastGoalKey) {
        const last = JSON.parse(this._lastGoalKey);
        if (last.body) {
          last.body = null;
          this._lastGoalKey = JSON.stringify(last);
          this.renderGoalRow(last);
        }
      }
      return;
    }
    const goal = goalFromStatement(stmt);
    if (!goal) return;
    // Skip the DOM churn when nothing changed since the last upgrade.
    const key = JSON.stringify(goal);
    if (key === this._lastGoalKey) return;
    this._lastGoalKey = key;
    this.renderGoalRow(goal);
  }

  async mountEditor(body) {
    const readonly = this.hasAttribute("readonly");
    const onEdit = EditorView.updateListener.of((u) => {
      if (u.docChanged) this._doc.scheduleCheck(this);
    });
    // LSP hover/completion live in a compartment that starts empty and is
    // filled in the first time the reader shows intent (focus or mouse-over),
    // so the language-server wasm is never loaded for a page that's only read.
    this._interactions = new Compartment();
    const wantLsp = this.getAttribute("lsp") !== "off";
    // Must not return the promise: a truthy return tells CodeMirror the event
    // was handled and would swallow every focus/pointerover.
    const enable = () => {
      void this.enableInteractions();
    };
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
          this._interactions.of([]),
          wantLsp
            ? EditorView.domEventHandlers({ focus: enable, pointerover: enable })
            : [],
        ],
      }),
    });
  }

  // Load the language server + autocomplete module (both optional) and switch
  // the interactions compartment on. Failures degrade to a plain editor.
  async enableInteractions() {
    if (this._lspBooted) return;
    this._lspBooted = true;
    const readonly = this.hasAttribute("readonly");
    let autocompleteMod = null;
    let lspOk = false;
    try {
      [, autocompleteMod] = await Promise.all([
        loadLspOnce(),
        readonly ? null : import("@codemirror/autocomplete"),
      ]);
      lspOk = true;
    } catch (err) {
      console.warn("[aufbau-proof] LSP interactions unavailable:", err);
    }
    // Hover installs regardless: statement popovers come from the compile
    // path's statement snapshots, not the language server.
    const exts = [
      hoverTooltip((view, pos) => this._hoverTooltipAt(pos), {
        hideOnChange: true,
      }),
    ];
    if (autocompleteMod) {
      exts.push(
        autocompleteMod.autocompletion({
          override: [(context) => this._completionSource(context)],
        }),
      );
    }
    // Code actions are proof-search suggestions; a theory cell's mm0 body
    // has no search placeholders, so don't poll for them there.
    if (lspOk && !readonly && !this._mm0Editable) {
      exts.push(
        cellActionField,
        EditorView.updateListener.of((u) => {
          if (u.selectionSet || u.docChanged) this._scheduleActionQuery();
        }),
      );
    }
    this._view.dispatch({ effects: this._interactions.reconfigure(exts) });
    this._lspReady = lspOk;
  }

  // Hover contents at a body-local position, via the stitched document.
  // Public (and used by the hover tooltip) so pages/tests can drive it.
  async lspHover(pos) {
    const ctx = await this._doc.lspContext(this);
    if (!ctx) return null;
    const line = this._view.state.doc.lineAt(pos);
    const result = await ctx.rpc.request("textDocument/hover", {
      textDocument: { uri: ctx.uri },
      position: {
        line: ctx.lineDelta + line.number - 1,
        character: pos - line.from,
      },
    });
    if (!result || !result.contents) return null;
    const value =
      typeof result.contents === "string"
        ? result.contents
        : (result.contents.value ?? "");
    const range = result.range
      ? this._rangeFromStitched(result.range, ctx.lineDelta)
      : null;
    return { value, from: range?.from ?? pos, to: range?.to ?? pos };
  }

  // The compiler statement for the name token at a body-local position, if
  // the document's latest snapshot knows one — `{ stmt, from, to }` with the
  // token's body range, or null. Public for tests/pages.
  statementAt(pos) {
    const statements = this._doc?._statements;
    if (!statements || !this._view) return null;
    const line = this._view.state.doc.lineAt(pos);
    const text = line.text;
    let from = pos - line.from;
    let to = from;
    const wordChar = (ch) => /[\w']/.test(ch);
    while (from > 0 && wordChar(text[from - 1])) from -= 1;
    while (to < text.length && wordChar(text[to])) to += 1;
    const word = text.slice(from, to);
    if (!/^[A-Za-z_][\w']*$/.test(word)) return null;
    const stmt =
      statements.get(`rule:${word}`) ?? statements.get(`def:${word}`);
    if (!stmt) return null;
    return { stmt, from: line.from + from, to: line.from + to };
  }

  _hoverTooltipAt(pos) {
    // A name with a known statement pops its pretty-printed form immediately
    // (no LSP round-trip; works even when the language server failed to
    // load). The server's prose is appended when it arrives.
    const named = this.statementAt(pos);
    if (named && goalFromStatement(named.stmt)) {
      return {
        pos: named.from,
        end: named.to,
        create: () => {
          const dom = statementHoverDom(named.stmt);
          this.lspHover(pos)
            .then((hover) => {
              if (hover?.value) appendHoverProse(dom, hover.value);
            })
            .catch(() => {});
          return { dom };
        },
      };
    }
    return this.lspHover(pos)
      .then((hover) => {
        if (!hover || !hover.value.trim()) return null;
        return {
          pos: hover.from,
          end: hover.to,
          create: () => ({ dom: hoverDom(hover.value) }),
        };
      })
      .catch(() => null);
  }

  // Completion options at a body-local position. Public for the same reason.
  async lspCompletionsAt(pos) {
    const ctx = await this._doc.lspContext(this);
    if (!ctx) return null;
    const line = this._view.state.doc.lineAt(pos);
    const result = await ctx.rpc.request("textDocument/completion", {
      textDocument: { uri: ctx.uri },
      position: {
        line: ctx.lineDelta + line.number - 1,
        character: pos - line.from,
      },
      context: { triggerKind: 1 },
    });
    const items = Array.isArray(result) ? result : (result?.items ?? []);
    if (!items.length) return null;
    // A server that says `isIncomplete` computed this list for the token as it
    // stands; the next keystroke has to be a fresh request, not a re-filter of
    // this one. Ours always does — the applicable-rule search reads the token.
    const incomplete = !Array.isArray(result) && result?.isIncomplete === true;

    // The server anchors every item to the token being completed; map that
    // replacement range back into the body once.
    let from = pos;
    let to = pos;
    const anchored = items.find((i) => i.textEdit?.range);
    if (anchored) {
      const mapped = this._rangeFromStitched(
        anchored.textEdit.range,
        ctx.lineDelta,
      );
      if (mapped) ({ from, to } = mapped);
    }
    // The wire order is construction order; the server's ranking lives in
    // sortText (plain string comparison, per LSP).
    const ranked = [...items].sort((a, b) => {
      const ka = a.sortText ?? a.label;
      const kb = b.sortText ?? b.label;
      return ka < kb ? -1 : ka > kb ? 1 : 0;
    });
    const options = ranked.map((item, idx) => ({
      // CodeMirror matches typed text against `label`; routing the server's
      // filterText through it makes notation items reachable by symbol or by
      // term name (`∀ all`), while displayLabel keeps the popup showing the
      // token itself.
      label: item.filterText ?? item.label,
      displayLabel: item.label,
      detail: item.detail ?? undefined,
      type: CM_COMPLETION_TYPES[item.kind] ?? "text",
      info: item.documentation?.value
        ? () => hoverDom(item.documentation.value)
        : undefined,
      apply: item.textEdit?.newText ?? item.insertText ?? item.label,
      boost: -idx / 100, // keep the server's relevance order among equal matches
    }));
    return { from, to, options, incomplete };
  }

  _completionSource(context) {
    if (!context.explicit) {
      // Auto-trigger inside a word or a run of notation symbols (`->`,
      // `∀`, `∧`, …); Ctrl-Space works anywhere.
      const before =
        context.matchBefore(WORD_FRAGMENT) ??
        context.matchBefore(SYMBOL_FRAGMENT);
      if (!before) return null;
    }
    return this.lspCompletionsAt(context.pos)
      .then((r) => {
        if (!r) return null;
        const { incomplete, ...result } = r;
        // `validFor` is the opposite of `isIncomplete`: it licenses CodeMirror
        // to keep this list and narrow it locally while the token still
        // matches. Withhold it when the server asked to be re-queried.
        return incomplete ? result : { ...result, validFor: FRAGMENT_VALID };
      })
      .catch(() => null);
  }

  // Code actions at a body-local position — proof-search suggestions when the
  // position is a search placeholder. Returns [{ title, changes }] with
  // body-local CodeMirror change specs, or null. Public for tests/pages.
  // The proof search can run for seconds; it happens on the worker thread, and
  // the cell status shows "searching…" while a slow request is in flight.
  async lspCodeActionsAt(pos) {
    const ctx = await this._doc.lspContext(this);
    if (!ctx) return null;
    const line = this._view.state.doc.lineAt(pos);
    const position = {
      line: ctx.lineDelta + line.number - 1,
      character: pos - line.from,
    };
    this._pendingAction?.cancel();
    const req = ctx.rpc.requestCancellable("textDocument/codeAction", {
      textDocument: { uri: ctx.uri },
      range: { start: position, end: position },
      context: { diagnostics: [] },
    });
    this._pendingAction = req;
    const saved = this._statusState;
    const slow = setTimeout(() => this.setStatus("busy", "searching…"), 250);
    let result = null;
    try {
      result = await req.promise;
    } catch {
      result = null;
    } finally {
      clearTimeout(slow);
      if (this._pendingAction === req) this._pendingAction = null;
      // Restore the pre-search status unless a compile overwrote it meanwhile.
      if (saved && this._statusState?.text === "searching…") {
        this.setStatus(saved.kind, saved.text);
      }
    }

    const actions = [];
    for (const action of Array.isArray(result) ? result : []) {
      const edits = action?.edit?.changes
        ? Object.values(action.edit.changes).flat()
        : [];
      const changes = [];
      for (const edit of edits) {
        const mapped = this._rangeFromStitched(edit.range, ctx.lineDelta);
        if (!mapped) {
          changes.length = 0;
          break;
        }
        changes.push({ from: mapped.from, to: mapped.to, insert: edit.newText });
      }
      if (changes.length) actions.push({ title: action.title, changes });
    }
    return actions;
  }

  _scheduleActionQuery() {
    clearTimeout(this._actionTimer);
    this._actionTimer = setTimeout(() => {
      void this._runActionQuery();
    }, 350);
  }

  async _runActionQuery() {
    const gen = (this._actionGen = (this._actionGen ?? 0) + 1);
    const head = this._view.state.selection.main.head;
    const actions = await this.lspCodeActionsAt(head).catch(() => null);
    // Drop stale answers: a newer query started, or the caret moved on.
    if (gen !== this._actionGen) return;
    if (this._view.state.selection.main.head !== head) return;
    const line = this._view.state.doc.lineAt(head);
    if (actions?.length) {
      this._view.dispatch({
        effects: setCellActions.of({ cell: this, actions, pos: line.to }),
      });
    } else if (this._view.state.field(cellActionField, false)) {
      this._view.dispatch({ effects: setCellActions.of(null) });
    }
  }

  openActionMenu(anchor, actions) {
    this.closeActionMenu();
    const menu = document.createElement("div");
    menu.className = "action-menu";
    menu.setAttribute("role", "menu");
    for (const action of actions) {
      const item = document.createElement("button");
      item.type = "button";
      item.className = "action-item";
      item.setAttribute("role", "menuitem");
      item.textContent = action.title;
      item.addEventListener("click", () => {
        this.closeActionMenu();
        this._view.dispatch({
          changes: action.changes,
          effects: setCellActions.of(null),
        });
        this._view.focus();
      });
      menu.append(item);
    }
    // Attached beside .aufbau (not inside it): the container clips overflow
    // for its rounded corners, and a menu near the bottom edge must escape it.
    // Copy the resolved theme vars over, since it no longer inherits them.
    const containerStyle = getComputedStyle(this._container);
    for (const v of ["--bg", "--fg", "--muted", "--line"]) {
      menu.style.setProperty(v, containerStyle.getPropertyValue(v));
    }
    this.shadowRoot.append(menu);
    const cRect = this.getBoundingClientRect();
    const aRect = anchor.getBoundingClientRect();
    menu.style.top = `${aRect.bottom - cRect.top + 4}px`;
    const left = Math.min(
      aRect.left - cRect.left,
      cRect.width - menu.offsetWidth - 8,
    );
    menu.style.left = `${Math.max(8, left)}px`;
    this._menu = menu;
    const dismiss = (event) => {
      const path = event.composedPath ? event.composedPath() : [event.target];
      if (!path.includes(menu) && !path.includes(anchor)) {
        this.closeActionMenu();
      }
    };
    const onKey = (event) => {
      if (event.key === "Escape") {
        this.closeActionMenu();
        this._view.focus();
      }
    };
    // Defer so the opening click doesn't immediately dismiss the menu.
    setTimeout(() => document.addEventListener("mousedown", dismiss), 0);
    document.addEventListener("keydown", onKey);
    this._menuCleanup = () => {
      document.removeEventListener("mousedown", dismiss);
      document.removeEventListener("keydown", onKey);
    };
    menu.querySelector("button")?.focus();
  }

  closeActionMenu() {
    this._menu?.remove();
    this._menu = null;
    this._menuCleanup?.();
    this._menuCleanup = null;
  }

  // Map a stitched-document LSP range back to body-local positions. Returns
  // null when the range falls outside this cell's editable body.
  _rangeFromStitched(range, lineDelta) {
    const doc = this._view.state.doc;
    const mapPos = (p) => {
      const ln = p.line - lineDelta;
      if (ln < 0 || ln >= doc.lines) return null;
      const line = doc.line(ln + 1);
      return Math.min(line.from + p.character, line.to);
    };
    const from = mapPos(range.start);
    const to = mapPos(range.end);
    if (from == null || to == null || to < from) return null;
    return { from, to };
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
      // Clean cell, but the whole document didn't compile: no hard seal. An
      // unfilled search placeholder is the common warning here.
      const warnings = entry.proof.filter(
        (p) => p.diag.severity === "warning",
      ).length;
      this.setStatus(
        "note",
        warnings
          ? `${warnings} warning${warnings === 1 ? "" : "s"}`
          : "no errors (pending)",
      );
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
    this._statusState = { kind, text };
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

// ---------------------------------------------------------------------------
// <aufbau-index> — a live table of contents for one document: every statement
// in the compiler's snapshot, pretty-printed, with the owning cell's
// verification state. Owned rows scroll to (and flash) their cell on click.
// ---------------------------------------------------------------------------

class AufbauIndex extends HTMLElement {
  connectedCallback() {
    if (this._booted) return;
    this._booted = true;
    this.attachShadow({ mode: "open" });
    const style = document.createElement("style");
    style.textContent = STYLE;
    this._container = document.createElement("div");
    this._container.className = "aufbau index";
    this._container.dataset.theme = this.getAttribute("theme") ?? "auto";
    const mh = this.getAttribute("max-height");
    if (mh) {
      this._container.style.maxHeight = mh;
      this._container.style.overflowY = "auto";
    }
    this.shadowRoot.append(style, this._container);
    this._lastStmt = new Map();
    this._lastRenderKey = null;

    if (documentKeyFor(this) == null) {
      this._container.append(
        hintDiv("aufbau-index needs a theory, theory-src, or doc attribute"),
      );
      return;
    }
    this._container.append(hintDiv("waiting for the first check…"));
    this._doc = getOrCreateDocument(this);
    this._doc.registerIndex(this);
  }

  disconnectedCallback() {
    this._doc?.unregisterIndex(this);
  }

  // Called by the document coordinator after every check (and once on
  // registration, replaying the last check).
  applyDocument({ statements, cells }) {
    // Ownership: a single-statement cell claims its own key; beyond that, the
    // cell whose mm0 fragment declares the name claims it (theory cells).
    // What's left is the base theory (or a full-file cell's contents).
    const owners = new Map();
    for (const cell of cells) {
      const key = cell.statementKey();
      if (key) owners.set(key, cell);
    }
    for (const [key, stmt] of statements) {
      if (owners.has(key)) continue;
      const declRe = new RegExp(
        `\\b(?:axiom|theorem|def)\\s+${escapeRe(stmt.name)}\\b`,
      );
      const owner = cells.find((c) => declRe.test(c.mm0Fragment()));
      if (owner) owners.set(key, owner);
    }

    // Row order mirrors the stitched document: base-theory statements first,
    // then each cell's statements in page order. A cell whose statement
    // vanished from the snapshot (broken definition or theorem — recovery
    // invalidated it) keeps its last-known render, marked stale.
    const byCell = new Map();
    const entries = [];
    for (const [key, stmt] of statements) {
      this._lastStmt.set(key, stmt);
      const cell = owners.get(key);
      if (!cell) {
        entries.push({ key, stmt, cell: null, stale: false });
        continue;
      }
      let list = byCell.get(cell);
      if (!list) byCell.set(cell, (list = []));
      list.push({ key, stmt, cell, stale: false });
    }
    for (const cell of cells) {
      const list = byCell.get(cell) ?? [];
      const key = cell.statementKey();
      if (key && !statements.has(key)) {
        list.push({
          key,
          stmt: this._lastStmt.get(key) ?? null,
          cell,
          stale: true,
        });
      }
      entries.push(...list);
    }
    this._render(entries);
  }

  _render(entries) {
    const renderKey = JSON.stringify(
      entries.map((e) => [
        e.key,
        e.stale,
        e.cell ? (e.cell.statusState()?.kind ?? null) : null,
        e.stmt ? goalFromStatement(e.stmt) : null,
        e.stmt ? statementKindLabel(e.stmt) : null,
      ]),
    );
    if (renderKey === this._lastRenderKey) return;
    this._lastRenderKey = renderKey;
    this._container.replaceChildren();
    if (!entries.length) {
      this._container.append(hintDiv("no statements yet"));
      return;
    }
    for (const e of entries) this._container.append(this._buildRow(e));
  }

  _buildRow({ key, stmt, cell, stale }) {
    const row = document.createElement(cell ? "button" : "div");
    row.className = `index-row${stale ? " stale" : ""}`;
    const dot = document.createElement("span");
    dot.className = "index-dot";
    if (cell) {
      row.type = "button";
      row.title = "go to the cell";
      dot.dataset.kind = cell.statusState()?.kind ?? "";
      row.addEventListener("click", () => {
        cell.scrollIntoView({ behavior: "smooth", block: "center" });
        cell.flash();
      });
    } else {
      dot.classList.add("given"); // part of the theory, nothing to verify
    }
    const badge = document.createElement("span");
    badge.className = "index-kind";
    badge.textContent = stmt
      ? statementKindLabel(stmt)
      : key.startsWith("def:")
        ? "def"
        : "theorem";
    row.append(dot, badge);
    const goal = stmt && goalFromStatement(stmt);
    if (goal) {
      row.append(buildGoalRow(goal, { noDefineLabel: true }));
    } else {
      // Unrenderable (or never-seen) statement: name only.
      const n = document.createElement("span");
      n.className = "goal-name";
      n.textContent = key.slice(key.indexOf(":") + 1);
      row.append(n);
    }
    return row;
  }
}

function hintDiv(text) {
  const el = document.createElement("div");
  el.className = "index-empty";
  el.textContent = text;
  return el;
}

function formulaChip(text, kind) {
  const el = document.createElement("code");
  el.className = `formula ${kind}`;
  el.textContent = text;
  return el;
}

// A statement row: `define` + signature (+ live definiens) for definitions,
// name + hyps ⊢ concl for assertions. Shared by the cell goal header, the
// document index, and the name-hover popover. Returns null when there is
// nothing to show. `noDefineLabel` drops the leading `define` when the
// surrounding context already names the kind (index badge, popover caption).
function buildGoalRow(goal, { noDefineLabel = false } = {}) {
  if (!goal) return null;
  const g = document.createElement("div");
  g.className = "goal";
  if (goal.signature != null) {
    // Definition: the declaration to inhabit, not a goal to prove.
    if (!noDefineLabel) {
      const n = document.createElement("span");
      n.className = "goal-name";
      n.textContent = "define";
      g.append(n);
    }
    const sep = goal.signature.startsWith(":") ? "" : " ";
    g.append(formulaChip(`${goal.name}${sep}${goal.signature}`, "concl"));
    if (goal.body) {
      const eq = document.createElement("span");
      eq.className = "turnstile";
      eq.textContent = "=";
      g.append(eq, formulaChip(goal.body, "hyp"));
    }
    return g;
  }
  if (!goal.concl && !goal.hyps?.length) return null;
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
  return g;
}

// Convert a compiler statement snapshot into the shape `buildGoalRow`
// renders. Returns null when the statement isn't renderable (the
// pretty-printer bails on anonymous binders, say) so callers keep whatever
// display they already have.
function goalFromStatement(stmt) {
  if (stmt.kind === "def") {
    if (stmt.signature == null) return null;
    return {
      name: stmt.name,
      signature: stmt.signature,
      body: stmt.body ?? null,
    };
  }
  if (stmt.concl == null) return null;
  return { name: stmt.name, hyps: stmt.hyps ?? [], concl: stmt.concl };
}

function statementKindLabel(stmt) {
  if (stmt.kind === "def") return "def";
  if (stmt.kind === "axiom") return "axiom";
  return stmt.local ? "lemma" : "theorem";
}

// The name-hover popover: kind caption + the pretty-printed statement chips.
function statementHoverDom(stmt) {
  const dom = document.createElement("div");
  dom.className = "lsp-hover stmt-hover";
  const caption = document.createElement("div");
  caption.className = "stmt-kind";
  caption.textContent = statementKindLabel(stmt);
  dom.append(
    caption,
    buildGoalRow(goalFromStatement(stmt), { noDefineLabel: true }),
  );
  return dom;
}

// Append the prose parts (everything outside code fences) of a hover markdown
// below the statement chips — the server's kind/hypothesis-count summary and
// annotation metadata, without repeating the statement in source form.
function appendHoverProse(dom, markdown) {
  const parts = markdown.split(/```[^\n]*\n?/);
  for (let i = 0; i < parts.length; i += 2) {
    const text = parts[i].trim();
    if (!text) continue;
    const el = document.createElement("div");
    el.textContent = text;
    dom.append(el);
  }
}

// Minimal markdown for hover contents: fenced code blocks become <pre>, the
// prose between them plain text (the server's hover markdown is just those two).
function hoverDom(markdown) {
  const dom = document.createElement("div");
  dom.className = "lsp-hover";
  const parts = markdown.split(/```[^\n]*\n?/);
  parts.forEach((part, i) => {
    const text = i % 2 === 1 ? part.replace(/\n$/, "") : part.trim();
    if (!text) return;
    const el = document.createElement(i % 2 === 1 ? "pre" : "div");
    el.textContent = text;
    dom.append(el);
  });
  return dom;
}

// ---------------------------------------------------------------------------
// Styles (scoped to the shadow root).
// ---------------------------------------------------------------------------

const STYLE = `
:host { display: block; margin: 1rem 0; position: relative; }
.aufbau {
  --bg: #ffffff; --fg: #1c1c22; --muted: #6b7280; --line: #e5e7eb;
  --ok: #059669; --err: #dc2626;
  --warnbg: #fef2f2; --bulb: #d97706;
  position: relative;
  border: 1px solid var(--line); border-radius: 8px; overflow: hidden;
  font-family: ui-monospace, "SF Mono", Menlo, Consolas, monospace;
  color: var(--fg); background: var(--bg);
}
.aufbau[data-theme="dark"] {
  --bg: #16181d; --fg: #e6e6ea; --muted: #9aa0aa; --line: #2b2f38;
  --ok: #34d399; --err: #f87171;
  --warnbg: #3a1d1d; --bulb: #fbbf24;
}
@media (prefers-color-scheme: dark) {
  .aufbau[data-theme="auto"] {
    --bg: #16181d; --fg: #e6e6ea; --muted: #9aa0aa; --line: #2b2f38;
    --ok: #34d399; --err: #f87171;
    --warnbg: #3a1d1d; --bulb: #fbbf24;
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
.lsp-hover { max-width: 32rem; padding: .3rem .5rem; font-size: .85em; }
.stmt-kind {
  color: var(--muted); font-size: .72em;
  text-transform: uppercase; letter-spacing: .05em;
}
.stmt-hover .goal {
  border-bottom: none; background: none; color: var(--fg);
  padding: .15rem 0 .1rem;
}
.lsp-hover pre {
  margin: .2rem 0; padding: .25rem .4rem; overflow-x: auto;
  background: color-mix(in srgb, var(--fg) 5%, var(--bg)); border-radius: 4px;
}
.lsp-hover div { color: var(--muted); }
.editor .cm-tooltip {
  background: var(--bg); color: var(--fg);
  border: 1px solid var(--line); border-radius: 6px;
}
.editor .cm-tooltip.cm-tooltip-autocomplete > ul { font-family: inherit; }
.action-bulb {
  cursor: pointer; margin-left: .75ch; color: var(--bulb);
  opacity: .85; user-select: none;
}
.action-bulb svg { vertical-align: -0.15em; }
.action-bulb:hover, .action-bulb:focus-visible { opacity: 1; outline: none; }
.action-menu {
  position: absolute; z-index: 10; display: flex; flex-direction: column;
  min-width: 14rem; max-width: calc(100% - 1rem); padding: .2rem;
  background: var(--bg, #fff); color: var(--fg, #1c1c22);
  border: 1px solid var(--line, #e5e7eb); border-radius: 6px;
  box-shadow: 0 6px 20px rgba(0, 0, 0, .15);
  font-family: ui-monospace, "SF Mono", Menlo, Consolas, monospace;
  font-size: .85em;
}
.action-item {
  all: unset; box-sizing: border-box; cursor: pointer;
  padding: .35rem .55rem; border-radius: 4px;
  white-space: nowrap; overflow: hidden; text-overflow: ellipsis;
}
.action-item:hover, .action-item:focus-visible {
  background: color-mix(in srgb, var(--fg, #1c1c22) 8%, var(--bg, #fff));
}
.aufbau.flash { animation: aufbau-flash 1.4s ease-out; }
@keyframes aufbau-flash {
  from { box-shadow: 0 0 0 3px color-mix(in srgb, var(--ok) 70%, transparent); }
  to { box-shadow: 0 0 0 3px transparent; }
}
.aufbau.index { font-size: .9em; }
.index-row {
  display: flex; align-items: baseline; flex-wrap: wrap; gap: .45rem;
  box-sizing: border-box; width: 100%; margin: 0; padding: .4rem .7rem;
  font: inherit; text-align: left; color: inherit;
  background: none; border: none;
}
.index-row + .index-row { border-top: 1px solid var(--line); }
button.index-row { cursor: pointer; }
button.index-row:hover, button.index-row:focus-visible {
  background: color-mix(in srgb, var(--fg) 5%, var(--bg)); outline: none;
}
.index-row.stale { opacity: .6; }
/* The shared goal-row wrapper dissolves into the row's own flex layout. */
.index-row .goal { display: contents; }
.index-dot {
  flex: none; align-self: center; width: .55em; height: .55em;
  border-radius: 50%; background: var(--muted);
}
.index-dot[data-kind="ok"] { background: var(--ok); }
.index-dot[data-kind="err"] { background: var(--err); }
.index-dot.given {
  background: none; border: 1px solid var(--muted); box-sizing: border-box;
}
.index-kind {
  flex: none; font-size: .75em; color: var(--muted);
  border: 1px solid var(--line); border-radius: 999px; padding: 0 .55em;
}
.index-empty { padding: .45rem .7rem; color: var(--muted); font-size: .85em; }
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
if (!customElements.get("aufbau-index")) {
  customElements.define("aufbau-index", AufbauIndex);
}

export {
  AufbauProof,
  AufbauTheory,
  AufbauIndex,
  stitch,
  routeDiagnostics,
  defFillerName,
  mm0DefSignature,
  localDefSignature,
  goalFromStatement,
  statementKindLabel,
};
