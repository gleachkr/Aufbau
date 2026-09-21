// @aufbau/editor — an embeddable interactive proof editor.
//
// Custom elements:
//   <aufbau-theory id="…">  — holds a fixed MM0 theory prelude (inline or `src`).
//   <aufbau-proof>          — an editor for one proof cell, checked in-browser.
//
// See docs/design_notes/embeddable_editor.md for the design. Every cell that
// shares a theory forms one *document*. Each cell owns a small file pair
// under the document's virtual directory — `cN.mm0` (its declaration
// fragment behind an `import` of the previous cell's file, or of the
// prelude for the first cell) and `cN.auf` (its proof) — so the compiler's
// own import/include machinery chains the cells in DOM order and the
// coordinator never splices text. On each edit it runs ONE debounced compile
// of the last cell's file (which pulls in the whole chain) and hands every
// cell the diagnostics the compiler reports on that cell's two files. The
// compiler's analyze/recovery path means a broken or unfinished cell does
// not cascade red onto the cells that depend on it. There is no separate
// kernel-verify seal: a cell is "verified" only when the whole document
// compiles clean (meta.ok); otherwise a clean cell reads as "no errors
// (pending)".
//
//   - A lemma cell contributes an `.auf` file only (proves something not in
//     the mm0). A theorem cell also contributes an mm0 `theorem …;`
//     declaration in its own `.mm0` file (not the theory). A definition cell
//     uses the same seam for a bodyless `def …;` declaration whose `.auf`
//     content is the public body filler — the definiens (and any hidden dummy
//     binders it needs) is what the reader edits, and the cells that prove
//     things *about* the definition check it. A local-def cell's `.auf`
//     content is a proof-local definition (it declares its own signature,
//     nothing in the mm0) usable by every later cell. A theory cell has mm0
//     content and no `.auf` at all: its editable body IS its mm0 file, so
//     terms and axioms can be authored in place; with the `doc` grouping
//     attribute a page needs no <aufbau-theory> element at all.
//   - An `import "x.mm0";` in the prelude or a cell, or an `include
//     "x.auf";` in a proof, names a file the host fetches: relative to the
//     page for inline sources and to the file's own URL for `src`-loaded
//     ones. Fetched files keep their relative path under the document's
//     virtual directory, so the compiler resolves the statement the same way.

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
    this.listeners = new Set();
    server.subscribe((raw) => {
      let msg;
      try {
        msg = JSON.parse(raw);
      } catch {
        return;
      }
      if (msg.id == null && msg.method) {
        for (const listener of this.listeners) listener(msg);
        return;
      }
      const waiter = msg.id != null && this.pending.get(msg.id);
      if (!waiter) return;
      this.pending.delete(msg.id);
      if (msg.error) waiter.reject(new Error(msg.error.message ?? "LSP error"));
      else waiter.resolve(msg.result ?? null);
    });
  }

  // Server-initiated notifications. One server instance is shared by every
  // document on the page, so a listener must filter on the uri it cares about.
  onNotification(listener) {
    this.listeners.add(listener);
    return () => this.listeners.delete(listener);
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

let documentSeq = 0;

// `Diagnostic.code` the server puts on placeholder search-status entries. They
// are the one thing publishDiagnostics carries that the compiler path cannot
// produce, since running the search is an editor-session act.
const SEARCH_STATUS_CODE = "search-status";

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

// Number of newlines in `text` before `charIndex`.
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
// Pure file assembly + routing (kept side-effect free so they can be
// unit-tested).
// ---------------------------------------------------------------------------

// The virtual file pair of one cell: `mm0` is the cell's declaration fragment
// behind an `import` of `previous` (the file that carries everything before
// the cell), `auf` the proof text or null for a theory cell. `bodyByte` is
// where the editable body starts in each file.
function cellFiles(cell, previous) {
  const importLine = `import ${JSON.stringify(previous)};\n`;
  const mm0 = importLine + cell.mm0Fragment();
  const files = { mm0, mm0BodyByte: byteLen(importLine), auf: null, aufBodyByte: 0 };
  if (!cell.isTheoryCell()) {
    files.auf = cell.aufText();
    files.aufBodyByte = cell.prefixBytes();
  }
  return files;
}

// Assign each compiler diagnostic to the cell whose file owns it. Returns a
// Map<cellId, { proof: [...], banner: [...] }> plus `theory` diags (those on
// the prelude or a fetched library, i.e. author errors). `proof` diagnostics
// carry a `localByte` offset into that cell's editable body. `owner(file)`
// gives `{ id, side, bodyByte }` for a file path — the cell, which of its
// files (`mm0`/`auf`) this is, and where the editable body begins in it — or
// null for a file no cell owns. A theory cell's mm0 diagnostics localize like
// proof ones instead of becoming banners, since its body IS its mm0 file.
function routeDiagnostics(diagnostics, { owner, mm0BodyOwned }) {
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

  for (const d of diagnostics) {
    const hit = d.file == null ? null : owner(d.file);
    if (!hit) {
      theory.push(d);
      continue;
    }
    const { id, side, bodyByte } = hit;
    if (d.spanStart == null) {
      cellEntry(id).banner.push(d);
      continue;
    }
    if (side === "auf" || mm0BodyOwned?.(id)) {
      const localByte = d.spanStart - bodyByte;
      const localEnd = (d.spanEnd ?? d.spanStart) - bodyByte;
      if (localEnd <= 0) {
        cellEntry(id).banner.push(d); // inside the fixed header / import line
      } else {
        cellEntry(id).proof.push({ diag: d, localByte, localEnd });
      }
    } else {
      cellEntry(id).banner.push(d);
    }
  }
  return { perCell, theory };
}

// Statement-level `import "…";` specs of an mm0 text, and line-start
// `include "…";` specs of an auf text — the same rule the compiler's scanner
// applies (`--` comments and `$…$` math are skipped), so the host knows which
// files to fetch before the compiler asks for them. Over-reporting is
// harmless (a fetch that fails is simply not supplied); the compiler stays
// the authority on what a statement means.
function importSpecs(text, syntax) {
  const specs = [];
  const keyword = syntax === "mm0" ? "import" : "include";
  const stmt = new RegExp(`^\\s*${keyword}\\s+"([^"]*)"\\s*;`);
  const scan = (segment) => {
    const m = stmt.exec(segment);
    if (m) specs.push(m[1]);
  };
  // Strip comments and math, keeping newlines so the `include` line rule
  // still sees line starts.
  let stripped = "";
  for (let i = 0; i < text.length; ) {
    if (text.startsWith("--", i)) {
      while (i < text.length && text[i] !== "\n") i += 1;
    } else if (text[i] === "$") {
      i += 1;
      while (i < text.length && text[i] !== "$") {
        if (text[i] === "\n") stripped += "\n";
        i += 1;
      }
      i += 1;
    } else {
      stripped += text[i];
      i += 1;
    }
  }
  if (syntax === "mm0") {
    for (const segment of stripped.split(";")) scan(`${segment};`);
  } else {
    for (const line of stripped.split("\n")) scan(line);
  }
  return specs;
}

// Resolve `spec` against the directory of `fromPath` (POSIX, lexical), the
// way the compiler resolves an import: `/a/b/c.mm0` + `../d.mm0` → `/a/d.mm0`.
function resolvePath(fromPath, spec) {
  const base = spec.startsWith("/") ? [] : fromPath.split("/").slice(0, -1);
  const parts = [];
  for (const part of [...base, ...spec.split("/")]) {
    if (part === "" || part === ".") continue;
    if (part === "..") {
      parts.pop();
      continue;
    }
    parts.push(part);
  }
  return `/${parts.join("/")}`;
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
  // Where the theory came from — what its own `import`s resolve against.
  sourceUrl() {
    const src = this.getAttribute("src");
    return src ? new URL(src, document.baseURI).href : document.baseURI;
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
    this._statements = null; // latest statement snapshot (name-hover lookups)
    this._lastDocState = null; // latest check result (replayed to late indexes)
    // The virtual directory holding this document's files. The compiler
    // sees them as a file table keyed by these paths; the language server
    // as `file://` documents under them. Relative `import`/`include` specs
    // resolve within it on both sides.
    this._dir = `/aufbau-editor/doc${documentSeq++}`;
    this._preludePath = `${this._dir}/prelude.mm0`;
    this._cellSeq = 0;
    this._libraries = new LibraryStore((path) => this.ownsPath(path));
    this._lsp = null;
  }

  register(cell) {
    this.cells.add(cell);
    // A cell keeps its file stem for life; the chain between cells is
    // rebuilt from DOM order on every assembly.
    if (!cell._docPath) cell._docPath = `${this._dir}/c${++this._cellSeq}`;
  }

  unregister(cell) {
    this.cells.delete(cell);
    this._closeLspFiles(cell);
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
      // The language server outlives this document; drop our subscription so
      // a retired coordinator isn't kept alive by the listener set.
      this._lspUnsubscribe?.();
      this._lspUnsubscribe = null;
    }
  }

  // Is `path` one of the files this document assembles itself (the prelude
  // or a cell's pair), as opposed to a library the host must fetch?
  ownsPath(path) {
    if (path === this._preludePath) return true;
    for (const cell of this.cells) {
      if (path === `${cell._docPath}.mm0` || path === `${cell._docPath}.auf`) {
        return true;
      }
    }
    return false;
  }

  // The shared base theory (axioms/terms/notation). Cell-contributed mm0
  // declarations are NOT part of this — each lives in its cell's own file.
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

  // What the prelude's own `import`s resolve against: the theory file's
  // URL when it was fetched, the page otherwise.
  theoryBaseUrl() {
    if (this._theoryRef) {
      return theoryRegistry.get(this._theoryRef)?.sourceUrl() ?? document.baseURI;
    }
    if (this._theorySrc) return new URL(this._theorySrc, document.baseURI).href;
    return document.baseURI;
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

  // Fetch (once) every library the prelude and the cells reference, so the
  // assembled table can satisfy the compiler's imports and includes.
  async ensureLibraries(cells, theory) {
    const jobs = [
      this._libraries.ensure(
        this._preludePath,
        theory ?? "",
        "mm0",
        this.theoryBaseUrl(),
      ),
    ];
    for (const cell of cells) {
      jobs.push(
        this._libraries.ensure(
          `${cell._docPath}.mm0`,
          cell.mm0Fragment(),
          "mm0",
          document.baseURI,
        ),
      );
      if (!cell.isTheoryCell()) {
        jobs.push(
          this._libraries.ensure(
            `${cell._docPath}.auf`,
            cell.aufText(),
            "auf",
            cell.sourceUrl(),
          ),
        );
      }
    }
    await Promise.all(jobs);
  }

  // The document as a file table, in dependency order: the fetched
  // libraries, the prelude, then each cell's pair with its `.mm0` importing
  // the previous cell's (the prelude for the first). `root`/`proof` name the
  // last cell's files — compiling that root pulls in the whole chain.
  // `owners` maps each cell file to `{ id, side, bodyByte }`.
  assemble(cells, theory) {
    const files = [
      ...this._libraries.files(),
      { path: this._preludePath, text: theory ?? "" },
    ];
    const owners = new Map();
    let previous = this._preludePath;
    let root = this._preludePath;
    let proof = null;
    for (const cell of cells) {
      const spec = previous.slice(previous.lastIndexOf("/") + 1);
      const cellFile = cellFiles(cell, spec);
      const mm0Path = `${cell._docPath}.mm0`;
      files.push({ path: mm0Path, text: cellFile.mm0 });
      owners.set(mm0Path, { id: cell, side: "mm0", bodyByte: cellFile.mm0BodyByte });
      root = mm0Path;
      proof = null;
      if (cellFile.auf != null) {
        const aufPath = `${cell._docPath}.auf`;
        files.push({ path: aufPath, text: cellFile.auf });
        owners.set(aufPath, { id: cell, side: "auf", bodyByte: cellFile.aufBodyByte });
        proof = aufPath;
      }
      previous = mm0Path;
    }
    return { files, root, proof, owners };
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
      await this.ensureLibraries(cells, theory);
    } catch (err) {
      for (const c of cells) c.setStatus("err", `load error: ${err.message}`);
      return;
    }

    const table = this.assemble(cells, theory);
    let result;
    try {
      result = compiler.compileFiles(table);
    } catch (err) {
      for (const c of cells) c.setStatus("err", `compiler error: ${err.message}`);
      return;
    }

    const meta = result.meta ?? {};
    const diagnostics = meta.diagnostics ?? [];
    if (!meta.ok && diagnostics.length === 0) {
      // Nothing to pin on a cell (a malformed request, say): say so plainly
      // rather than leaving every cell "pending".
      for (const c of cells) {
        c.setStatus("err", `compile failed: ${meta.message ?? meta.error ?? "unknown"}`);
      }
      return;
    }
    const routed = routeDiagnostics(diagnostics, {
      owner: (path) => table.owners.get(path) ?? null,
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

  // Prepare an LSP view of this document for one cell: sync the assembled
  // files to the language server as documents (only the ones whose text
  // changed), and return the request context — the cell's file uri plus the
  // line delta that maps its body-local positions into that file (the import
  // line of a theory cell's mm0, the header of a proof). Reassembled on every
  // request (it's cheap) so hover/completion always see the live text.
  async lspContext(cell) {
    const [rpc, theory] = await Promise.all([loadLspOnce(), this.theoryText()]);
    const cells = this.orderedCells().filter((c) => c.isReady());
    await this.ensureLibraries(cells, theory);
    const table = this.assemble(cells, theory);

    if (!this._lsp) {
      this._lsp = { docs: new Map() }; // path → { version, text }
      // The server republishes a proof file's diagnostics whenever a
      // placeholder search concludes, and that publish is the only place the
      // failure reason for a missed search exists — a failed search returns no
      // code actions at all. Compile feedback still comes from the compiler
      // path; only the search-status entries are taken from here.
      this._lspUnsubscribe = rpc.onNotification((msg) => {
        if (msg.method !== "textDocument/publishDiagnostics") return;
        const owner = this._cellForUri(msg.params?.uri);
        if (!owner) return;
        this.applySearchDiagnostics(owner, msg.params.diagnostics ?? []);
      });
    }
    // Dependency order: a file's imports are open before the file itself is
    // analysed, so no root is ever seen with a missing library.
    const current = new Set();
    for (const file of table.files) {
      current.add(file.path);
      const doc = this._lsp.docs.get(file.path);
      if (doc && doc.text === file.text) continue;
      const version = (doc?.version ?? 0) + 1;
      this._lsp.docs.set(file.path, { version, text: file.text });
      syncLspDoc(rpc, uriForPath(file.path), languageIdFor(file.path), version, file.text);
    }
    for (const path of [...this._lsp.docs.keys()]) {
      if (current.has(path)) continue;
      this._lsp.docs.delete(path);
      rpc.notify("textDocument/didClose", {
        textDocument: { uri: uriForPath(path) },
      });
    }

    const own = cell.isTheoryCell() ? `${cell._docPath}.mm0` : `${cell._docPath}.auf`;
    const owner = table.owners.get(own);
    if (!owner) return null;
    const text = this._lsp.docs.get(own)?.text ?? "";
    return {
      rpc,
      uri: uriForPath(own),
      lineDelta: lineDeltaAt(text, byteToCharIndex(text, owner.bodyByte)),
    };
  }

  // Forget a departed cell's files on the language server.
  _closeLspFiles(cell) {
    if (!this._lsp) return;
    for (const path of [`${cell._docPath}.mm0`, `${cell._docPath}.auf`]) {
      if (!this._lsp.docs.delete(path)) continue;
      loadLspOnce()
        .then((rpc) =>
          rpc.notify("textDocument/didClose", {
            textDocument: { uri: uriForPath(path) },
          }),
        )
        .catch(() => {});
    }
  }

  // The proof cell whose `.auf` file the uri names, if any.
  _cellForUri(uri) {
    if (typeof uri !== "string") return null;
    for (const cell of this.cells) {
      if (uri === uriForPath(`${cell._docPath}.auf`)) return cell;
    }
    return null;
  }

  // Hand a cell the search-status diagnostics published for its proof file.
  // Ranges arrive in that file's coordinates; the header lines ahead of the
  // editable body are the only offset.
  applySearchDiagnostics(cell, diagnostics) {
    // Errors only. A search-status error is a search that ran and failed (or a
    // rejected `(iters: …)` parameter) — the reason exists nowhere else. The
    // info and warning entries restate what the compiler path already says
    // about a placeholder, so taking them would only duplicate the squiggle.
    const search = diagnostics.filter(
      (d) => d.code === SEARCH_STATUS_CODE && d.severity === 1,
    );
    const prefix = cell.prefixText();
    cell.applySearchDiagnostics(search, lineDeltaAt(prefix, prefix.length));
  }
}

// Libraries a document's sources name with `import`/`include`: fetched once
// per virtual path, along with whatever they name in turn, and a fetched
// `.mm0`'s `<stem>.auf` sibling (the pairing the compiler applies to files
// on disk). A file that cannot be fetched is left to the compiler to report
// on the statement that names it. `isOwn(path)` marks paths the document
// supplies itself, which are never fetched.
class LibraryStore {
  constructor(isOwn) {
    this._isOwn = isOwn;
    this._files = new Map(); // path → { path, text }
    this._pending = new Map(); // path → Promise
    this._missing = new Set();
  }

  files() {
    return [...this._files.values()];
  }

  // Fetch every file `text` (at `path`, obtained from `baseUrl`) references.
  async ensure(path, text, syntax, baseUrl) {
    const jobs = [];
    for (const spec of importSpecs(text, syntax)) {
      let url;
      try {
        url = new URL(spec, baseUrl).href;
      } catch {
        continue;
      }
      jobs.push(this._load(resolvePath(path, spec), url));
    }
    await Promise.all(jobs);
  }

  _load(path, url) {
    if (this._isOwn(path) || this._files.has(path) || this._missing.has(path)) {
      return Promise.resolve();
    }
    const pending = this._pending.get(path);
    if (pending) return pending;
    const job = (async () => {
      let text;
      try {
        const res = await fetch(url);
        if (!res.ok) throw new Error(`fetch ${url}: ${res.status}`);
        text = await res.text();
      } catch {
        this._missing.add(path);
        return;
      }
      this._files.set(path, { path, text });
      const syntax = path.endsWith(".auf") ? "auf" : "mm0";
      const jobs = [this.ensure(path, text, syntax, url)];
      if (syntax === "mm0") {
        jobs.push(
          this._load(path.replace(/\.mm0$/, ".auf"), url.replace(/\.mm0(?=[?#]|$)/, ".auf")),
        );
      }
      await Promise.all(jobs);
    })().finally(() => this._pending.delete(path));
    this._pending.set(path, job);
    return job;
  }
}

function uriForPath(path) {
  return `file://${path}`;
}

function languageIdFor(path) {
  return path.endsWith(".auf") ? "aufbau" : "mm0";
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
  // Where the proof text came from — what its `include`s resolve against.
  sourceUrl() {
    const src = this.getAttribute("src");
    return src ? new URL(src, document.baseURI).href : document.baseURI;
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

  // Hover contents at a body-local position, via the cell's file.
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
      ? this._rangeFromFile(result.range, ctx.lineDelta)
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
      const mapped = this._rangeFromFile(
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
        const mapped = this._rangeFromFile(edit.range, ctx.lineDelta);
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

  // Map an LSP range in this cell's file back to body-local positions.
  // Returns null when the range falls outside the editable body.
  _rangeFromFile(range, lineDelta) {
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

  // Search-status diagnostics for this cell's body, in body-local positions.
  // They arrive out of band (whenever a placeholder search concludes), so keep
  // them and re-render; an edit invalidates them, since the recorded outcome is
  // keyed by document state and the server will not republish until the next
  // search runs.
  applySearchDiagnostics(list, lineDelta) {
    if (!this._view) return;
    const mapped = [];
    for (const d of list) {
      const range = this._rangeFromFile(d.range, lineDelta);
      if (!range) continue;
      mapped.push({
        from: range.from,
        to: Math.max(range.from, range.to),
        severity: "error",
        message: d.message,
      });
    }
    this._searchDiags = mapped;
    this._searchDiagsDoc = this._view.state.doc.toString();
    this.renderDiagnostics();
    // The compile path only knows the placeholder is unfilled, and rates that a
    // warning. A search that ran and failed is a stronger verdict; say so, until
    // the next compile recomputes the status from scratch.
    if (mapped.length) this.setStatus("err", "search failed");
  }

  // The lint set CodeMirror shows: the compile path's diagnostics for this
  // cell, plus any search-status entry. Where both land on the same span the
  // search entry wins — it says *why* the search did not fill the placeholder,
  // which is strictly more than the compiler's "still a placeholder".
  renderDiagnostics() {
    if (!this._view) return;
    const body = this._view.state.doc.toString();
    const search = this._searchDiagsDoc === body ? (this._searchDiags ?? []) : [];
    const covered = new Set(search.map((d) => `${d.from}:${d.to}`));
    const cm = (this._compileDiags ?? []).filter(
      (d) => !covered.has(`${d.from}:${d.to}`),
    );
    this._view.dispatch(
      setDiagnostics(this._view.state, [...cm, ...search].sort((a, b) => a.from - b.from)),
    );
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
    this._compileDiags = cm;
    this.renderDiagnostics();

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
    } else if (ok && entry.proof.some((p) => p.diag.error === "SorryLine")) {
      // The document compiled, but this cell admits a line with `sorry!`:
      // no seal, the proof is incomplete by its own admission.
      this.setStatus("note", "admitted with sorry! · not verified");
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

    // Row order mirrors the document: base-theory statements first,
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
    // Not `⊢`: sequent-style theories put a turnstile inside the formulas
    // themselves, and a second one between the chips read as part of the
    // logic. The boxes make each formula one unit; this is just a small
    // "yields" marker between the premises and the conclusion.
    const sep = document.createElement("span");
    sep.className = "turnstile";
    sep.textContent = "▸";
    g.append(sep);
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

// Append the rest of a hover markdown below the statement chips. The server's
// declaration hover has a fixed shape: a one-line summary, the declaration in
// a code fence with its `@directive` lines ahead of the signature, then the
// doc comment (the plain `--|` prose) as markdown paragraphs. The signature
// itself is skipped — the chips above already show the statement — and the
// rest is laid out as doc, directives, summary: the doc is what a reader
// wants first; the summary only repeats the caption. Directive lines drop
// the `--|` comment marker: it is source syntax, and most monospace fonts
// ligature it into an arrow-like glyph; each one is its own line so a long
// `@view` wraps with a hanging indent instead of running off the popover.
function appendHoverProse(dom, markdown) {
  const parts = markdown.split(/```[^\n]*\n?/);
  const annotations = [];
  const paragraphs = [];
  let summary = "";
  parts.forEach((part, i) => {
    if (i % 2 === 1) {
      for (const line of part.split("\n")) {
        const m = /^--\|\s*(.*)$/.exec(line);
        if (m && m[1]) annotations.push(m[1]);
      }
    } else if (i === 0) {
      summary = part.trim();
    } else {
      for (const para of part.split(/\n[ \t]*\n/)) {
        if (para.trim()) paragraphs.push(para.trim());
      }
    }
  });
  if (paragraphs.length) {
    const doc = document.createElement("div");
    doc.className = "stmt-doc";
    for (const para of paragraphs) {
      const p = document.createElement("p");
      appendInlineMarkdown(p, para);
      doc.append(p);
    }
    dom.append(doc);
  }
  if (annotations.length) {
    const list = document.createElement("div");
    list.className = "stmt-annotations";
    for (const text of annotations) {
      const el = document.createElement("div");
      el.className = "stmt-annotation";
      // The directive (`@view`, `@rewrite`, …) is what the reader scans for;
      // set it apart from its arguments.
      const m = /^(@\S+)(.*)$/s.exec(text);
      if (m) {
        const directive = document.createElement("span");
        directive.className = "stmt-annotation-directive";
        directive.textContent = m[1];
        el.append(directive, m[2]);
      } else {
        el.textContent = text;
      }
      list.append(el);
    }
    dom.append(list);
  }
  if (summary) {
    const el = document.createElement("div");
    appendInlineMarkdown(el, summary);
    dom.append(el);
  }
}

// The only inline markdown the server's prose uses: `code` spans. Everything
// else is plain text (doc comments are shown as written, not rendered).
function appendInlineMarkdown(el, text) {
  text.split("`").forEach((piece, i) => {
    if (i % 2 === 1) {
      const code = document.createElement("code");
      code.textContent = piece;
      el.append(code);
    } else if (piece) {
      el.append(piece);
    }
  });
}

// Minimal markdown for hover contents: fenced code blocks become <pre>, the
// prose between them paragraphs with `code` spans (the server's hover
// markdown is just those two).
function hoverDom(markdown) {
  const dom = document.createElement("div");
  dom.className = "lsp-hover";
  const parts = markdown.split(/```[^\n]*\n?/);
  parts.forEach((part, i) => {
    if (i % 2 === 1) {
      const text = part.replace(/\n$/, "");
      if (!text) return;
      const el = document.createElement("pre");
      el.textContent = text;
      dom.append(el);
      return;
    }
    for (const para of part.split(/\n[ \t]*\n/)) {
      if (!para.trim()) continue;
      const el = document.createElement("div");
      appendInlineMarkdown(el, para.trim());
      dom.append(el);
    }
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
/* Premises and conclusion as boxes on a neutral ground, so each formula
   reads as one unit and the split survives a theory whose own formulas
   contain a turnstile. Deliberately no tint on the conclusion: the
   separator marks it, and the gray is calmer. */
.goal .formula {
  padding: .1em .45em; border-radius: 4px;
  border: 1px solid var(--line);
  background: color-mix(in srgb, var(--fg) 4%, var(--bg));
}
.banner {
  padding: .4rem .7rem; font-size: .85em; color: var(--err);
  background: var(--warnbg); border-bottom: 1px solid var(--line);
}
.editor .cm-editor {
  height: var(--editor-height, auto);
  max-height: var(--editor-max-height, none);
}
.editor .cm-scroller { overflow: auto; font-family: inherit; }
/* Proof lines are long and the view wraps them. A hanging indent keeps a
   wrapped continuation visibly subordinate to the line it belongs to, so a
   two-row line does not read as two lines. The negative text-indent cancels
   the padding on the first row, leaving it where CodeMirror's own theme
   (padding: 0 2px 0 6px) puts it. The padding needs !important for the same
   reason the gutter rule below does: CodeMirror's theme is an adopted
   stylesheet, which cascades after this <style> at equal specificity, and
   without it the base padding wins while the negative indent still applies,
   pulling the first row 4ch out of the editor and clipping it. */
.editor .cm-line {
  padding-left: calc(6px + var(--wrap-indent, 4ch)) !important;
  text-indent: calc(-1 * var(--wrap-indent, 4ch));
}
/* Keep the lint gutter invisible until it holds an error marker. The
   !important beats CodeMirror's own gutter theme, injected into the shadow
   root after this stylesheet at equal specificity. */
.editor .cm-gutters {
  background: var(--bg) !important;
  border-right: none !important;
}
.lsp-hover { max-width: 36rem; padding: .3rem .5rem; font-size: .85em; }
.stmt-kind {
  color: var(--muted); font-size: .72em;
  text-transform: uppercase; letter-spacing: .05em;
}
.stmt-hover .goal {
  border-bottom: none; background: none; color: var(--fg);
  padding: .15rem 0 .1rem;
}
/* The declaration's annotations, one per line. Each line wraps with a
   hanging indent so a long @view signature stays one visual item. The
   color rule outranks the muted .lsp-hover div rule below: annotations
   are content, not commentary. */
/* The doc comment reads as prose, so it gets the page's text face rather
   than the editor's monospace; code spans drop back to monospace. */
.lsp-hover .stmt-doc {
  color: var(--fg); margin: .15rem 0 .45rem;
  font-family: system-ui, -apple-system, "Segoe UI", Roboto, sans-serif;
  font-size: 1.05em; line-height: 1.4;
}
.stmt-doc p { margin: 0; }
.stmt-doc p + p { margin-top: .4em; }
.stmt-doc code {
  font-family: ui-monospace, "SF Mono", Menlo, Consolas, monospace;
  font-size: .9em;
  padding: 0 .2em; border-radius: 3px;
  background: color-mix(in srgb, var(--fg) 6%, var(--bg));
}
.stmt-annotations { margin: .1rem 0 .25rem; }
.lsp-hover .stmt-annotation {
  color: var(--fg); white-space: pre-wrap; overflow-wrap: anywhere;
  padding-left: 2ch; text-indent: -2ch;
}
.stmt-annotation-directive { font-weight: 600; }
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
/* The compiler separates a diagnostic's context lines (theorem, line, rule,
   inference path) with newlines; without this they collapse into one run-on. */
.editor .cm-diagnostic { white-space: pre-line; }
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
  cellFiles,
  importSpecs,
  resolvePath,
  routeDiagnostics,
  defFillerName,
  mm0DefSignature,
  localDefSignature,
  goalFromStatement,
  statementKindLabel,
};
