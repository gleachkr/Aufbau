# `@aufbau/editor`

Embeddable browser editor components for MM0 theories and Aufbau proofs.
Compilation and diagnostics run locally in WebAssembly.

## Install

```sh
npm install @aufbau/editor @aufbau/compiler \
  @codemirror/view @codemirror/state @codemirror/commands \
  @codemirror/lint
```

For language-server hover, completion, and proof search, also install the
optional packages:

```sh
npm install @aufbau/lsp @codemirror/autocomplete
```

## Usage

Importing the package registers its custom elements:

```js
import "@aufbau/editor";
```

```html
<aufbau-theory id="example" src="/example.mm0"></aufbau-theory>

<aufbau-proof theory="example" src="/example.auf"></aufbau-proof>
```

Sources may also be inline:

```html
<aufbau-theory id="example">
  <script type="text/mm0">
    -- MM0 source
  </script>
</aufbau-theory>

<aufbau-proof theory="example">
  <script type="text/auf">
    -- Aufbau proof script
  </script>
</aufbau-proof>
```

Multiple proof elements with the same `theory` value form one document in DOM
order. Use `readonly`, `theme="light|dark|auto"`, or `lsp="off"` to adjust an
individual proof element. The package also registers `<aufbau-index>` for a
live statement index.

This package requires a browser DOM. It does not run under plain Node.

## Loading from a CDN

The components need no bundler and no build step — an import map is enough. The
`?external=` parameters keep CodeMirror and the Aufbau wasm packages as single
shared instances rather than one copy per dependent:

```html
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
```

The language server runs in a Web Worker that the browser will only build from
a same-origin script, so `@aufbau/lsp` bootstraps it through a `blob:` URL when
it is served from a CDN. A page with a Content-Security-Policy therefore needs
`worker-src blob:` alongside the CDN host — see the `@aufbau/lsp` README. Drop
the `@aufbau/lsp` and `@codemirror/autocomplete` entries to run without a
language server; the editor still compiles and reports diagnostics.

Host pages with their own global keyboard shortcuts should be aware that
keystrokes typed in a cell bubble out of its shadow root retargeted to the
`<aufbau-*>` host element. If those shortcuts swallow ordinary characters, stop
keyboard events whose `composedPath()` contains an `AUFBAU-` element before the
page's own handlers see them.
