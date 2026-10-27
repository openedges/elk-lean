# elk-lean (npm)

Eclipse Layout Kernel 0.12.0 ported to pure Lean 4 — drop-in replacement for
[elkjs](https://github.com/kieler/elkjs) backed by a native Node.js addon (WASM fallback pending).
The package layout and loaders are ported from [elk-rs](https://github.com/openedges/elk-rs)
`plugins/org.eclipse.elk.js`; the API and typings come from elkjs.

Status: not published (`"private": true`). Requires Node.js 18 or later.

## Usage

```js
const ELK = require('elk-lean');
const elk = new ELK();

const graph = {
  id: 'root',
  layoutOptions: { 'elk.algorithm': 'layered' },
  children: [
    { id: 'n1', width: 30, height: 30 },
    { id: 'n2', width: 30, height: 30 },
  ],
  edges: [{ id: 'e1', sources: ['n1'], targets: ['n2'] }],
};

elk.layout(graph).then(console.log);
```

ESM: `import ELK from 'elk-lean';`. Worker mode (Node.js `worker_threads` or a Web Worker):
`new ELK({ workerUrl: require.resolve('elk-lean/js/elk-worker.js') })`.

## Backends

`js/index.js` (Node.js) loads, in order:

1. the platform package `elk-lean-<triple>` (`optionalDependencies`, templates in `npm/<triple>/`),
2. `dist/elk-lean.<triple>.node` (built by `sh scripts/build_napi.sh`),
3. `dist/elk-lean.node`,
4. the WASM backend `js/load-wasm.js` — currently a stub that throws `WASM backend not built`.

`js/index.browser.js` and the Web Worker branch of `js/elk-worker.js` use `js/load-wasm.browser.mjs`
(also a stub until `plugins/org.eclipse.elk.wasm` exists). A backend is an object with
`layout_json(graphJson, optionsJson)`, `known_layout_algorithms()`, `known_layout_options()`,
`known_layout_categories()` returning JSON strings and throwing `Error(message)`.

Triples: `darwin-arm64`, `darwin-x64`, `linux-x64-gnu`, `linux-x64-musl`, `linux-arm64-gnu`,
`win32-x64-msvc` (only `darwin-arm64` is built and tested so far).

## API

Same as elkjs: `new ELK({ defaultLayoutOptions, algorithms, workerUrl, workerFactory })`,
`elk.layout(graph, { layoutOptions })`, `elk.knownLayoutAlgorithms()`, `elk.knownLayoutOptions()`,
`elk.knownLayoutCategories()`, `elk.terminateWorker()`. `algorithms` is accepted for compatibility;
every ported algorithm (including VertiFlex and DisCo, which elkjs 0.12.0 does not register) stays
available.

## Tests

```sh
sh scripts/build_napi.sh                       # from the repository root
node --test plugins/org.eclipse.elk.js/test/   # node:test, no npm dependencies
```

Parity against the native CLI (byte-for-byte, `elk layout X --sort-keys`):

```sh
node plugins/org.eclipse.elk.js/test/parity/run.mjs --models external/elk-models/realworld --timing 5
node plugins/org.eclipse.elk.js/test/parity/run.mjs --models external/elk-models --ext elkt
# optional structural comparison with elkjs (numeric tolerance 1e-6):
#   ... --elkjs <dir of an installed elkjs@0.12.0 package>
```

## License

[EPL-2.0 OR GPL-3.0-or-later](./LICENSE.md); see [NOTICE](./NOTICE) for ELK, elkjs and elk-rs
attribution and the statically linked Lean runtime components.
