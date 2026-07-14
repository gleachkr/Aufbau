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
