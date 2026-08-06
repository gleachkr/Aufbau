# Embedding the editor

Every proof cell in this manual is an instance of `@aufbau/editor`, a set of
web components that run the real Aufbau compiler in WebAssembly, in the
reader's browser. You can put the same live, checked proofs on any static
website, using an import map and one module import.

## A complete page

Save this as an `.html` file and serve it from any static host (or open it
through a local web server — module scripts don't load from `file:` URLs):

```html
<!doctype html>
<html>
<head>
<meta charset="utf-8">
<script type="importmap">
  {
    "imports": {
      "@codemirror/state": "https://esm.sh/@codemirror/state",
      "@codemirror/view": "https://esm.sh/@codemirror/view?external=@codemirror/state",
      "@codemirror/commands": "https://esm.sh/@codemirror/commands?external=@codemirror/state,@codemirror/view",
      "@codemirror/lint": "https://esm.sh/@codemirror/lint?external=@codemirror/state,@codemirror/view",
      "@codemirror/autocomplete": "https://esm.sh/@codemirror/autocomplete?external=@codemirror/state,@codemirror/view",
      "@aufbau/compiler": "https://esm.sh/@aufbau/compiler",
      "@aufbau/lsp": "https://esm.sh/@aufbau/lsp",
      "@aufbau/editor": "https://esm.sh/@aufbau/editor?external=@aufbau/compiler,@aufbau/lsp,@codemirror/state,@codemirror/view,@codemirror/commands,@codemirror/lint,@codemirror/autocomplete"
    }
  }
</script>
<script type="module">
  import "@aufbau/editor";
</script>
</head>
<body>

<aufbau-proof>
  <script type="text/mm0">
    delimiter $ ( ) $;
    provable sort wff;
    term imp (a b: wff): wff; infixr imp: $->$ prec 25;
    axiom h1 (a b: wff): $ a -> (b -> a) $;
  </script>
  <script type="text/auf">
    lemma weaken (p q: wff): $ p -> (q -> p) $
    ----
    l1: $ p -> (q -> p) $ by h1
  </script>
</aufbau-proof>

</body>
</html>
```

The cell compiles its theory and proof in WebAssembly and shows a live status
line.

- Everything loads from [esm.sh](https://esm.sh), which serves npm packages
  as ES modules with permissive CORS.
- The `?external=` parameters ensure that CodeMirror and the Aufbau WebAssembly
  packages each have one shared instance. Without them, dependencies may load
  separate copies, which breaks the editor.

## Sharing a theory between cells

To share a theory between cells, give the theory its own element and point the
proof cells at it.

```html
<aufbau-theory id="hilbert">
  <script type="text/mm0">
    delimiter $ ( ) $;
    provable sort wff;
    term imp (a b: wff): wff; infixr imp: $->$ prec 25;
    axiom h1 (a b: wff): $ a -> (b -> a) $;
    axiom mp (a b: wff): $ a $ > $ a -> b $ > $ b $;
  </script>
</aufbau-theory>

<aufbau-proof theory="hilbert">
  <script type="text/auf">
    lemma weaken_under (p q: wff): $ p $ > $ q -> p $
    ----
    l1: $ p -> (q -> p) $ by h1
    l2: $ q -> p $ by mp [#1, l1]
  </script>
</aufbau-proof>
```

`<aufbau-theory>` only holds the shared prelude. Later cells can use anything
proved by earlier cells in the same document. A cell reads "verified" only when
the entire document checks cleanly.

Sources can also live in separate files instead of inline scripts:
`<aufbau-theory id="hilbert" src="/hilbert.mm0">` and
`<aufbau-proof theory="hilbert" src="/proofs.auf">`.

If you want the theory itself to be *visible and editable*, skip
`<aufbau-theory>` and group the cells with a `doc` attribute instead. A
proof cell whose body is only MM0 acts as an editable theory cell:

```html
<aufbau-proof doc="hilbert">
  <script type="text/mm0">
    ...the theory, editable in place...
  </script>
</aufbau-proof>

<aufbau-proof doc="hilbert">
  <script type="text/auf">
    ...a lemma checked against it...
  </script>
</aufbau-proof>
```

A document can also contain theorem cells (an MM0 `theorem` declaration plus
its proof), definition cells (a bodyless `def` whose editable content is the
definiens), and proof-local definitions. There is also `<aufbau-index
theory="…">`, which provides a live index of every statement in the document.

## Cell attributes

| Attribute | Effect |
|---|---|
| `theory="ID"` | join the document anchored by `<aufbau-theory id="ID">` |
| `theory-src="URL"` | like `theory`, but fetch the prelude from a URL |
| `doc="NAME"` | group cells into a document with no fixed prelude |
| `src="URL"` | load the cell's body from a URL instead of an inline script |
| `readonly` | display a checked proof without allowing edits |
| `theme="light\|dark\|auto"` | color scheme (`auto` follows the page) |
| `lsp="off"` | disable hover/completion/search for this cell |
| `status="off"` | hide the status line |
| `height`, `max-height` | fix or cap the editor's height (CSS lengths) |
| `debounce` | milliseconds of idle time before a re-compile (default 400) |

## The language server is optional

Compiling and verifying need only `@aufbau/compiler`. The `@aufbau/lsp`
entry adds hover, completion, and proof search, and it runs in a Web
Worker. Two things to know:

- Browsers only build workers from same-origin scripts, so when the
  package is served from a CDN it bootstraps the worker through a `blob:`
  URL. If your site sets a Content-Security-Policy, allow `worker-src
  blob:` alongside the CDN host.
- If the language server fails to load, the cell degrades to a plain editor
  that still compiles, still shows diagnostics, and still verifies. To skip it
  deliberately, drop the `@aufbau/lsp` and `@codemirror/autocomplete` lines
  from the import map.
