import { EditorView, keymap, highlightActiveLine, drawSelection }
  from "@codemirror/view";
import { EditorState } from "@codemirror/state";
import { defaultKeymap, history, historyKeymap } from "@codemirror/commands";
import { linter, setDiagnostics } from "@codemirror/lint";
import {
  LSPClient,
  jumpToDefinition,
  languageServerExtensions,
} from "@codemirror/lsp-client";
import { loadCompiler } from "@aufbau/compiler";
import { loadVerifier } from "@aufbau/verifier";
import { loadLspServerWorker } from "@aufbau/lsp";
import { codeActions } from "./code-actions.js";

const encoder = new TextEncoder();
const themeKey = "aufbau-theme";
const mm0Uri = "file:///demo/current.mm0";
const proofUri = "file:///demo/current.auf";

const fixtureRoot = "./fixtures";
const manifestUrl = `${fixtureRoot}/manifest.json`;

// Populated from the build-generated manifest; `build.zig`'s
// WEB_DEMO_FIXTURES is the single roster of demo examples.
const examples = {};

const editorTheme = EditorView.theme({
  "&": {
    height: "100%",
    background: "transparent",
    color: "var(--text)",
  },
  ".cm-scroller": {
    fontFamily:
      '"Fira Code", "FiraCode Nerd Font", "Fira Mono", '
      + '"IBM Plex Mono", ui-monospace, monospace',
    fontFeatureSettings: '"calt" 1, "liga" 1',
    lineHeight: "1.65",
    fontSize: "14px",
    overflow: "auto",
    minHeight: "0",
  },
  ".cm-content": {
    padding: "1rem 0 6rem",
    caretColor: "var(--accent)",
  },
  ".cm-line": {
    padding: "0 1.25rem",
  },
  ".cm-gutters": {
    background: "transparent",
    border: "none",
    color: "var(--muted)",
    paddingLeft: "0.5rem",
  },
  ".cm-activeLineGutter": {
    background: "transparent",
  },
  ".cm-activeLine": {
    background: "var(--panel-muted)",
  },
  "&.cm-focused .cm-selectionBackground, .cm-selectionBackground": {
    background: "var(--selection) !important",
  },
  ".cm-cursor, .cm-dropCursor": {
    borderLeftColor: "var(--accent)",
  },
  "&.cm-focused": {
    outline: "none",
  },
  ".cm-lintRange-error": {
    backgroundImage: "none",
    textDecoration: "underline wavy var(--err)",
    textUnderlineOffset: "3px",
  },
  ".cm-lintRange-warning": {
    backgroundImage: "none",
    textDecoration: "underline wavy var(--warn)",
    textUnderlineOffset: "3px",
  },
  ".cm-tooltip": {
    background: "var(--bubble)",
    border: "1px solid rgb(255 255 255 / 0.12)",
    borderRadius: "0.8rem",
    boxShadow: "0 14px 38px rgb(0 0 0 / 0.22)",
  },
  ".cm-tooltip-lint": {
    padding: "0",
  },
  ".cm-diagnostic": {
    padding: "0.52rem 0.72rem",
    borderLeft: "none",
    color: "#fff6f6",
    whiteSpace: "pre-wrap",
    fontFamily:
      '"Fira Code", "FiraCode Nerd Font", "Fira Mono", '
      + '"IBM Plex Mono", ui-monospace, monospace',
    fontSize: "13px",
  },
  ".cm-diagnostic-error": {
    borderLeft: "none",
  },
  ".cm-diagnostic-warning": {
    borderLeft: "none",
    color: "#fff8e3",
  },
});

const ui = {
  mm0Editor: document.querySelector("#mm0-editor"),
  proofEditor: document.querySelector("#proof-editor"),
  panes: [...document.querySelectorAll(".pane")],
  tabs: [...document.querySelectorAll("[data-pane-tab]")],
  exampleButtons: [],
  exampleList: document.querySelector("#example-list"),
  mm0Meta: document.querySelector("#mm0-meta"),
  proofMeta: document.querySelector("#proof-meta"),
  compileStatus: document.querySelector("#compile-status"),
  compileTime: document.querySelector("#compile-time"),
  mmbSize: document.querySelector("#mmb-size"),
  verifyStatus: document.querySelector("#verify-status"),
  verifyTime: document.querySelector("#verify-time"),
  examplesBtn: document.querySelector("#examples-button"),
  exampleModal: document.querySelector("#example-modal"),
  theme: document.querySelector("#theme-toggle"),
};

let compilerRuntime = null;
let verifierRuntime = null;
let pendingTimer = null;
let runToken = 0;
let mm0View = null;
let proofView = null;
let lspClient = null;
let lspServer = null;
let currentExample = null;
let currentRouteKey = null;

initTheme();
initTabs();
initExamples();
main().catch((error) => {
  renderFatal(error);
});

function makeExtensions(ariaLabel, withLint, lspExtension, extra) {
  const exts = [
    highlightActiveLine(),
    drawSelection(),
    history(),
    keymap.of([
      {
        key: "Ctrl-]",
        run: jumpToDefinition,
        preventDefault: true,
      },
      ...defaultKeymap,
      ...historyKeymap,
    ]),
    EditorView.updateListener.of((update) => {
      if (update.docChanged) scheduleRun();
    }),
    EditorView.contentAttributes.of({
      "aria-label": ariaLabel,
      spellcheck: "false",
    }),
    editorTheme,
    EditorState.tabSize.of(2),
  ];
  if (lspExtension) {
    exts.push(lspExtension);
  }
  if (extra) {
    exts.push(extra);
  }
  if (withLint) {
    exts.push(linter(() => [], { delay: 86400000 }));
  }
  return exts;
}

function routeFromHash() {
  const raw = location.hash.replace(/^#/, "");
  const slash = raw.indexOf("/");
  const rawExample = slash < 0 ? raw : raw.slice(0, slash);
  const rawTheorem = slash < 0 ? "" : raw.slice(slash + 1);
  const name = safeDecode(rawExample);
  const theorem = rawTheorem ? safeDecode(rawTheorem) : null;
  return {
    example: examples[name] ? name : Object.keys(examples)[0],
    theorem,
  };
}

function safeDecode(value) {
  try {
    return decodeURIComponent(value);
  } catch {
    return value;
  }
}

function routeHash(name, theorem) {
  const parts = [encodeURIComponent(name)];
  if (theorem) parts.push(encodeURIComponent(theorem));
  return `#${parts.join("/")}`;
}

function pushRoute(name, theorem) {
  const next = routeHash(name, theorem);
  if (location.hash !== next) {
    window.history.pushState(null, "", next);
  }
}

async function main() {
  await loadExampleManifest();
  renderExampleButtons();

  const initialRoute = routeFromHash();
  const initial = initialRoute.example;
  const [compiler, verifier, server, mm0Text, proofText] = await Promise.all([
    loadCompiler(),
    loadVerifier(),
    loadLspServerWorker(),
    fetchText(examples[initial].mm0),
    fetchText(examples[initial].proof),
  ]);

  compilerRuntime = compiler;
  verifierRuntime = verifier;
  lspServer = server;
  lspClient = new LSPClient({
    rootUri: "file:///demo",
    extensions: languageServerExtensions(),
  }).connect(lspServer);

  mm0View = new EditorView({
    parent: ui.mm0Editor,
    state: EditorState.create({
      doc: mm0Text,
      extensions: makeExtensions(
        "MM0 source",
        true,
        lspClient.plugin(mm0Uri, "mm0"),
        codeActions({ client: lspClient, uri: mm0Uri }),
      ),
    }),
  });

  proofView = new EditorView({
    parent: ui.proofEditor,
    state: EditorState.create({
      doc: proofText,
      extensions: makeExtensions(
        "Aufbau script",
        true,
        lspClient.plugin(proofUri, "aufbau"),
        codeActions({ client: lspClient, uri: proofUri }),
      ),
    }),
  });

  updateSourceMeta();

  currentExample = initial;
  currentRouteKey = routeHash(initial, initialRoute.theorem);
  markActiveExample(initial);
  revealTheoremFromRoute(initialRoute.theorem);
  window.addEventListener("hashchange", handleRouteChange);
  window.addEventListener("popstate", handleRouteChange);

  warmUpAnalysis(mm0Text, proofText);
  await runAnalysis();
}

async function loadExampleManifest() {
  const entries = JSON.parse(await fetchText(manifestUrl));
  for (const entry of entries) {
    examples[entry.name] = {
      label: entry.label,
      mm0: `${fixtureRoot}/${entry.name}.mm0`,
      proof: `${fixtureRoot}/${entry.name}.auf`,
    };
  }
}

function renderExampleButtons() {
  ui.exampleButtons = Object.entries(examples).map(([name, example]) => {
    const button = document.createElement("button");
    button.type = "button";
    button.className = "example-button";
    button.dataset.example = name;
    button.setAttribute("aria-pressed", "false");
    button.textContent = example.label;
    button.addEventListener("click", () => loadExample(name));
    return button;
  });
  ui.exampleList.replaceChildren(...ui.exampleButtons);
}

function markActiveExample(name) {
  const example = examples[name];
  if (!example) return;
  for (const btn of ui.exampleButtons) {
    const active = btn.dataset.example === name;
    btn.classList.toggle("is-active", active);
    btn.setAttribute("aria-pressed", String(active));
  }
  ui.examplesBtn.textContent = example.label;
}

async function handleRouteChange() {
  const route = routeFromHash();
  const routeKey = routeHash(route.example, route.theorem);
  if (routeKey === currentRouteKey) return;
  currentRouteKey = routeKey;

  if (route.example === currentExample) {
    revealTheoremFromRoute(route.theorem);
    return;
  }
  await loadExample(route.example, {
    theorem: route.theorem,
    updateHash: false,
  });
}

async function loadExample(name, options = {}) {
  const example = examples[name];
  if (!example || !compilerRuntime || !verifierRuntime || !mm0View || !proofView) {
    return;
  }

  if (options.updateHash !== false) {
    pushRoute(name, options.theorem ?? null);
  }

  const [mm0Text, proofText] = await Promise.all([
    fetchText(example.mm0),
    fetchText(example.proof),
  ]);

  setEditorContent(mm0View, mm0Text);
  setEditorContent(proofView, proofText);
  lspClient?.sync();
  updateSourceMeta();
  clearDiagnostics();

  currentExample = name;
  currentRouteKey = routeHash(name, options.theorem ?? null);
  markActiveExample(name);
  revealTheoremFromRoute(options.theorem ?? null);
  ui.exampleModal.close();

  await runAnalysis();
}

function setEditorContent(view, text) {
  view.dispatch({
    changes: { from: 0, to: view.state.doc.length, insert: text },
  });
}

function revealTheoremFromRoute(name) {
  if (!name) return;
  if (revealProofBlock(name)) return;
  if (revealMm0Assertion(name)) return;
  console.warn(`No theorem named ${name} in ${currentExample}`);
}

function revealProofBlock(name) {
  if (!proofView) return false;
  const range = findProofBlock(proofView, name);
  if (!range) return false;
  focusRange("proof", proofView, range);
  return true;
}

function revealMm0Assertion(name) {
  if (!mm0View) return false;
  const range = findMm0Assertion(mm0View, name);
  if (!range) return false;
  focusRange("mm0", mm0View, range);
  return true;
}

function findProofBlock(view, name) {
  const doc = view.state.doc;
  for (let i = 1; i <= doc.lines; i += 1) {
    const line = doc.line(i);
    const trimmed = line.text.trim();
    if (trimmed === name && isProofUnderline(doc, i + 1)) {
      return rangeForName(line, name);
    }

    const lemma = line.text.match(/^\s*lemma\s+([A-Za-z_][A-Za-z0-9_']*)\b/);
    if (lemma?.[1] === name) {
      return rangeForName(line, name);
    }
  }
  return null;
}

function isProofUnderline(doc, lineNumber) {
  if (lineNumber > doc.lines) return false;
  return /^-+\s*$/.test(doc.line(lineNumber).text);
}

function findMm0Assertion(view, name) {
  const doc = view.state.doc;
  const pattern = /^\s*(?:(?:pub|local)\s+)?(?:axiom|theorem|lemma)\s+/;
  for (let i = 1; i <= doc.lines; i += 1) {
    const line = doc.line(i);
    if (!pattern.test(line.text)) continue;
    const assertion = line.text.slice(line.text.search(pattern));
    const match = assertion.match(
      /^\s*(?:(?:pub|local)\s+)?(?:axiom|theorem|lemma)\s+([^\s({:]+)/,
    );
    if (match?.[1] === name) {
      return rangeForName(line, name);
    }
  }
  return null;
}

function rangeForName(line, name) {
  const column = line.text.indexOf(name);
  const from = line.from + Math.max(column, 0);
  return { from, to: from + name.length };
}

function focusRange(pane, view, range) {
  setActivePane(pane);
  view.focus();
  view.dispatch({
    selection: {
      anchor: range.from,
      head: range.to,
    },
    effects: EditorView.scrollIntoView(range.from, {
      y: "start",
      yMargin: 16,
    }),
  });
}

function initTheme() {
  const theme = getStoredTheme() ?? getPreferredTheme();
  applyTheme(theme);
  ui.theme.addEventListener("click", toggleTheme);
}

function initTabs() {
  for (const tab of ui.tabs) {
    tab.addEventListener("click", () => {
      setActivePane(tab.dataset.paneTab);
    });
  }
}

function initExamples() {
  ui.examplesBtn.addEventListener("click", () => ui.exampleModal.showModal());
  ui.exampleModal.addEventListener("click", (e) => {
    if (e.target === ui.exampleModal) ui.exampleModal.close();
  });
  document.querySelector("#modal-close").addEventListener("click", () => {
    ui.exampleModal.close();
  });
}

function getStoredTheme() {
  try {
    const value = localStorage.getItem(themeKey);
    return value === "light" || value === "dark" ? value : null;
  } catch {
    return null;
  }
}

function getPreferredTheme() {
  return window.matchMedia("(prefers-color-scheme: light)").matches
    ? "light"
    : "dark";
}

function applyTheme(theme) {
  document.documentElement.dataset.theme = theme;
  ui.theme.textContent = theme === "dark" ? "light" : "dark";
  ui.theme.setAttribute(
    "aria-label",
    theme === "dark" ? "Switch to light mode" : "Switch to dark mode",
  );
  try {
    localStorage.setItem(themeKey, theme);
  } catch {
    // Ignore localStorage failures.
  }
}

function toggleTheme() {
  const current = document.documentElement.dataset.theme === "light"
    ? "light"
    : "dark";
  applyTheme(current === "dark" ? "light" : "dark");
}

function setActivePane(name) {
  for (const pane of ui.panes) {
    pane.classList.toggle("is-active", pane.dataset.pane === name);
  }
  for (const tab of ui.tabs) {
    const active = tab.dataset.paneTab === name;
    tab.classList.toggle("is-active", active);
    tab.setAttribute("aria-selected", String(active));
  }
}

function updateSourceMeta() {
  if (!mm0View || !proofView) return;
  ui.mm0Meta.textContent = formatBytes(
    encoder.encode(mm0View.state.doc.toString()).length,
  );
  ui.proofMeta.textContent = formatBytes(
    encoder.encode(proofView.state.doc.toString()).length,
  );
}

function scheduleRun() {
  updateSourceMeta();
  clearTimeout(pendingTimer);
  pendingTimer = setTimeout(() => {
    void runAnalysis();
  }, 250);
}

function warmUpAnalysis(mm0Text, proofText) {
  try {
    const compileResult = callCompiler(mm0Text, proofText);
    if (compileResult.meta?.ok) {
      callVerifier(mm0Text, compileResult.mmbBytes);
    }
  } catch (error) {
    console.warn("Warm-up run failed", error);
  }
}

async function runAnalysis() {
  if (!compilerRuntime || !verifierRuntime || !mm0View || !proofView) {
    return;
  }

  const token = ++runToken;
  lspClient?.sync();
  setStatus(ui.compileStatus, "running…", "warn");
  setStatus(ui.verifyStatus, "waiting…", "muted");
  ui.compileTime.textContent = "";
  ui.verifyTime.textContent = "";
  ui.mmbSize.textContent = "";

  const mm0Text = mm0View.state.doc.toString();
  const proofText = proofView.state.doc.toString();
  const compileResult = callCompiler(mm0Text, proofText);
  if (token !== runToken) {
    return;
  }

  const compileMeta = compileResult.meta;
  const compileOkay = Boolean(compileMeta?.ok);
  setStatus(
    ui.compileStatus,
    compileOkay ? "ok" : compileMeta?.message || "compile failed",
    compileOkay ? "ok" : "err",
  );
  ui.compileTime.textContent = formatApproxMs(compileResult.durationMs);
  ui.mmbSize.textContent = compileOkay
    ? formatBytes(compileResult.mmbBytes.length)
    : "";

  if (!compileOkay) {
    setStatus(ui.verifyStatus, "compile failed", "err");
    return;
  }

  const verifyResult = callVerifier(mm0Text, compileResult.mmbBytes);
  if (token !== runToken) {
    return;
  }

  const verifyMeta = verifyResult.meta;
  const verifyOkay = Boolean(verifyMeta?.ok);
  setStatus(
    ui.verifyStatus,
    verifyOkay ? "ok" : verifyMeta?.message || "verify failed",
    verifyOkay ? "ok" : "err",
  );
  ui.verifyTime.textContent = formatApproxMs(verifyResult.durationMs);
}

function clearDiagnostics() {
  if (mm0View) {
    mm0View.dispatch(setDiagnostics(mm0View.state, []));
  }
  if (proofView) {
    proofView.dispatch(setDiagnostics(proofView.state, []));
  }
}

function callCompiler(mm0Text, proofText) {
  if (!compilerRuntime) throw new Error("compiler is not loaded");
  return compilerRuntime.compile(mm0Text, proofText);
}

function callVerifier(mm0Text, mmbBytes) {
  if (!verifierRuntime) throw new Error("verifier is not loaded");
  return verifierRuntime.verifyPair(mm0Text, mmbBytes);
}

async function fetchText(url) {
  const response = await fetch(url);
  if (!response.ok) {
    throw new Error(`Failed to load ${url}`);
  }
  return response.text();
}

function setStatus(node, text, kind) {
  node.textContent = text;
  node.className = `status ${kind}`;
}

function formatApproxMs(value) {
  if (!Number.isFinite(value)) {
    return "";
  }
  if (value < 1) {
    return `\u2248 ${value.toFixed(1)} ms`;
  }
  if (value < 10) {
    return `\u2248 ${value.toFixed(1)} ms`;
  }
  return `\u2248 ${Math.round(value)} ms`;
}

function formatBytes(value) {
  if (value < 1024) {
    return `${value} B`;
  }
  if (value < 1024 * 1024) {
    return `${(value / 1024).toFixed(1)} KiB`;
  }
  return `${(value / (1024 * 1024)).toFixed(2)} MiB`;
}

function renderFatal(error) {
  setStatus(ui.compileStatus, error.message, "err");
  setStatus(ui.verifyStatus, "startup failed", "err");
  ui.compileTime.textContent = "";
  ui.verifyTime.textContent = "";
  ui.mmbSize.textContent = "";
  clearDiagnostics();
}
