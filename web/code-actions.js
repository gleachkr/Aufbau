// Client-driven LSP code actions for the demo editors.
//
// This is the standard pull-based flow: on a debounced cursor pause we ask the
// server `textDocument/codeAction` for the range at the caret, and if it hands
// back any actions we mark that line with a clickable lightbulb whose menu
// applies the server-provided edit. Placement and availability are entirely the
// server's call — we never scan proof text for `exact?`/`auto?`/`apply?`, so new
// action kinds surface with no client change.
//
// Note: the demo's LSP server is in-process wasm and runs synchronously, so a
// query that triggers a real proof search blocks the main thread until it
// finishes (bounded by the search's global budget, then cached). Off-placeholder
// queries short-circuit cheaply, so the cost only lands when the caret pauses on
// a fresh placeholder.

import { EditorView, Decoration, WidgetType } from "@codemirror/view";
import { StateField, StateEffect } from "@codemirror/state";

// Debounce between a cursor/selection settling and the code-action request. Long
// enough to collapse arrow-key navigation into a single query, short enough to
// feel responsive on a deliberate pause.
const QUERY_DELAY_MS = 300;

// Nerd Font lightbulb (nf-fa-lightbulb_o); the editor font stack includes a Nerd
// Font, so this renders as a glyph rather than tofu.
const BULB_GLYPH = "";

// The active code-action offer for one editor, or null. `pos` is the line-end
// offset the bulb decorates; it is only ever set for the document state it was
// computed against (the field clears on any doc change).
const setCodeActions = StateEffect.define();

class BulbWidget extends WidgetType {
  constructor(actions, uri) {
    super();
    this.actions = actions;
    this.uri = uri;
  }

  eq(other) {
    return other.actions === this.actions && other.uri === this.uri;
  }

  toDOM(view) {
    const bulb = document.createElement("span");
    bulb.className = "cm-code-action-bulb";
    bulb.textContent = BULB_GLYPH;
    bulb.setAttribute("role", "button");
    bulb.setAttribute("tabindex", "0");
    const label = this.actions.length === 1
      ? this.actions[0].title
      : `${this.actions.length} code actions`;
    bulb.setAttribute("aria-label", label);
    bulb.title = label;
    const open = (event) => {
      event.preventDefault();
      event.stopPropagation();
      openCodeActionMenu(view, bulb, this.actions, this.uri);
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

const codeActionField = StateField.define({
  create() {
    return null;
  },
  update(value, tr) {
    // Any edit invalidates both the stored offset and the actions (their edits
    // are keyed to a document version), so drop the offer and let the next query
    // repopulate it.
    if (tr.docChanged) value = null;
    for (const effect of tr.effects) {
      if (effect.is(setCodeActions)) value = effect.value;
    }
    return value;
  },
  provide: (field) =>
    EditorView.decorations.from(field, (value) => {
      if (!value) return Decoration.none;
      return Decoration.set([
        Decoration.widget({
          widget: new BulbWidget(value.actions, value.uri),
          side: 1,
        }).range(value.pos),
      ]);
    }),
});

const bulbTheme = EditorView.theme({
  ".cm-code-action-bulb": {
    cursor: "pointer",
    marginLeft: "0.75ch",
    padding: "0 0.15rem",
    color: "var(--warn)",
    opacity: "0.85",
    userSelect: "none",
  },
  ".cm-code-action-bulb:hover, .cm-code-action-bulb:focus-visible": {
    opacity: "1",
    outline: "none",
  },
});

// Per-view debounce timer + request generation, so a stale in-flight response
// never overwrites a newer one. Keyed weakly so it dies with the editor.
const queryState = new WeakMap();

function stateFor(view) {
  let state = queryState.get(view);
  if (!state) {
    state = { timer: 0, generation: 0, pendingParams: null };
    queryState.set(view, state);
  }
  return state;
}

function scheduleQuery(view, client, uri) {
  const state = stateFor(view);
  clearTimeout(state.timer);
  state.timer = setTimeout(() => {
    void runQuery(view, client, uri, state);
  }, QUERY_DELAY_MS);
}

async function runQuery(view, client, uri, state) {
  const generation = ++state.generation;
  const head = view.state.selection.main.head;
  const line = view.state.doc.lineAt(head);
  const position = { line: line.number - 1, character: head - line.from };
  const params = {
    textDocument: { uri },
    range: { start: position, end: position },
    context: { diagnostics: [] },
  };

  // A newer query supersedes any request still in flight; ask the server to stop
  // (it may already be done — the generation guard below is what guarantees
  // correctness either way).
  if (state.pendingParams) {
    try {
      client.cancelRequest(state.pendingParams);
    } catch {
      // Best effort — cancellation is an optimization, not a correctness need.
    }
  }

  client.sync();
  state.pendingParams = params;
  let result = null;
  try {
    result = await client.request("textDocument/codeAction", params);
  } catch {
    result = null;
  } finally {
    if (state.pendingParams === params) state.pendingParams = null;
  }

  if (generation !== state.generation) return;
  // The caret moved (a fresh query is already scheduled) or the document shrank
  // out from under the computed offset — either way, drop this stale answer.
  if (view.state.selection.main.head !== head) return;
  if (line.to > view.state.doc.length) return;

  const actions = Array.isArray(result)
    ? result.filter((action) => action && action.edit)
    : [];
  const current = view.state.field(codeActionField, false);
  if (actions.length) {
    view.dispatch({
      effects: setCodeActions.of({ actions, uri, pos: line.to }),
    });
  } else if (current) {
    view.dispatch({ effects: setCodeActions.of(null) });
  }
}

let openMenu = null;
let openMenuCleanup = null;

function closeCodeActionMenu() {
  if (openMenu) {
    openMenu.remove();
    openMenu = null;
  }
  if (openMenuCleanup) {
    openMenuCleanup();
    openMenuCleanup = null;
  }
}

function openCodeActionMenu(view, anchor, actions, uri) {
  closeCodeActionMenu();

  const menu = document.createElement("div");
  menu.className = "cm-code-action-menu";
  menu.setAttribute("role", "menu");
  for (const action of actions) {
    const item = document.createElement("button");
    item.type = "button";
    item.className = "cm-code-action-item";
    item.setAttribute("role", "menuitem");
    item.textContent = action.title;
    item.addEventListener("click", () => {
      applyCodeAction(view, action, uri);
      closeCodeActionMenu();
      view.focus();
    });
    menu.appendChild(item);
  }
  document.body.appendChild(menu);

  const anchorRect = anchor.getBoundingClientRect();
  menu.style.top = `${anchorRect.bottom + window.scrollY + 4}px`;
  menu.style.left = `${anchorRect.left + window.scrollX}px`;
  const menuRect = menu.getBoundingClientRect();
  if (menuRect.right > window.innerWidth - 8) {
    const left = window.innerWidth - menuRect.width - 8;
    menu.style.left = `${Math.max(8, left) + window.scrollX}px`;
  }

  openMenu = menu;

  const onPointerDown = (event) => {
    if (!menu.contains(event.target) && event.target !== anchor) {
      closeCodeActionMenu();
    }
  };
  const onKeyDown = (event) => {
    if (event.key === "Escape") {
      closeCodeActionMenu();
      view.focus();
    }
  };
  const onScroll = () => closeCodeActionMenu();
  // Defer the outside-click listener so the opening click doesn't immediately
  // dismiss the menu.
  setTimeout(() => document.addEventListener("mousedown", onPointerDown), 0);
  document.addEventListener("keydown", onKeyDown);
  window.addEventListener("scroll", onScroll, true);
  openMenuCleanup = () => {
    document.removeEventListener("mousedown", onPointerDown);
    document.removeEventListener("keydown", onKeyDown);
    window.removeEventListener("scroll", onScroll, true);
  };

  const first = menu.querySelector("button");
  if (first) first.focus();
}

function applyCodeAction(view, action, uri) {
  const edit = action.edit;
  if (!edit) return;

  let textEdits = null;
  if (edit.changes) {
    textEdits = edit.changes[uri] ?? Object.values(edit.changes)[0] ?? null;
  } else if (Array.isArray(edit.documentChanges)) {
    const change =
      edit.documentChanges.find(
        (c) => c.textDocument && c.textDocument.uri === uri,
      ) ?? edit.documentChanges[0];
    textEdits = change ? change.edits : null;
  }
  if (!textEdits || !textEdits.length) return;

  const doc = view.state.doc;
  // Apply back-to-front so earlier edits don't shift the offsets of later ones.
  const changes = textEdits
    .map((textEdit) => ({
      from: lspPositionToOffset(doc, textEdit.range.start),
      to: lspPositionToOffset(doc, textEdit.range.end),
      insert: textEdit.newText,
    }))
    .sort((a, b) => b.from - a.from || b.to - a.to);

  view.dispatch({ effects: setCodeActions.of(null), changes });
}

// LSP positions use UTF-16 code units for `character`, which is exactly
// CodeMirror's offset unit, so no re-encoding is needed — just clamp defensively.
function lspPositionToOffset(doc, position) {
  const lineNumber = Math.min(Math.max(position.line + 1, 1), doc.lines);
  const line = doc.line(lineNumber);
  return Math.min(line.from + position.character, line.to);
}

// Build the code-action extension for one editor, bound to its LSP client and
// document URI. Returns an array of CodeMirror extensions.
export function codeActions({ client, uri }) {
  return [
    codeActionField,
    bulbTheme,
    EditorView.updateListener.of((update) => {
      if (update.selectionSet || update.docChanged) {
        scheduleQuery(update.view, client, uri);
      }
    }),
  ];
}
