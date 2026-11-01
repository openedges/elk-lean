# org.eclipse.elk.live — ELK Live on elk-lean

A static, server-less replacement for [elk-live](https://github.com/kieler/elk-live)
(`external/elk-live`, "ElkGraph Web"): an ELK Text (`.elkt`) editor with a synchronized diagram.
elk-live needs a Java server (Xtext language server for parsing, validation and completion, ELK Java
for the layout); here everything runs in the browser:

```
edit (Monaco) --250 ms--> elk.convertElkt (Lean .elkt parser) --> elk.layout --> sprotty model update
                          \____________ elk-lean WASM in a Web Worker ___________/
```

`convertElkt` and `layout` are the elk-lean npm package (`plugins/org.eclipse.elk.js`, `file:`
dependency) in Web Worker mode (`workerUrl`): the same WebAssembly build as the npm package and
therefore the same layout as the native CLI (`test/pipeline.test.mjs` checks all bundled examples
against `elk layout X.elkt --defaults`). Design: `PLAN.md` section 8.1 (Phase 10).

## Run

Prerequisites, from the repository root: the WASM build of the npm package
(`sh scripts/build_wasm.sh` → `plugins/org.eclipse.elk.js/dist/wasm/`) and the
`external/elk-models` submodule (examples; in a worktree without submodules the main checkout's
copy is used, or set `ELK_MODELS_DIR`). Node.js 20.19+ or 22.12+ (Vite 8).

```sh
cd plugins/org.eclipse.elk.live
npm ci
npm run dev        # http://localhost:5173 (copies the assets, then Vite's dev server)
npm run build      # static site in dist/ (copies the assets, tsc --noEmit, vite build)
npm run preview    # serves dist/
npm test           # Node smoke tests (see Tests)
npm run gen:choices   # refresh src/generated/option-choices.json from `elk options --choices`
```

`dist/` uses relative URLs (`base: './'`) and can be served from any path by any static file server
(`.wasm` should be served as `application/wasm`; otherwise the engine falls back to a slower
non-streaming compile). It cannot be opened from `file://` (Web Workers and `fetch` need http(s)).

Build output (macOS, 2026-11-01): 26 MB in `dist/` — the WASM engine 20.4 MiB (about 2 MB with
brotli), the app bundle 3.9 MB (1.0 MB gzip; mostly Monaco), Monaco's editor worker 0.3 MB, CSS
0.16 MB, codicon font 0.15 MB, 45 examples 0.2 MB. The first layout appears about 0.5-1 s after the
page load on an M-series Mac (WASM compile in the worker).

## Structure

| path | content |
|---|---|
| `index.html`, `src/main.ts`, `src/style.css` | page, wiring (editor, worker, diagram, toolbar, URL parameters), layout |
| `src/core/pipeline.ts` | DOM-free pipeline: `convertElkt` → `layout` → sprotty model; parse/layout diagnostics with line/column |
| `src/core/elk-to-sprotty.ts` | laid-out ELK JSON → sprotty model (elk-live's visual model) |
| `src/core/options.ts` | completion metadata (`knownLayoutOptions()`, `knownLayoutAlgorithms()`, enum literals), `.elkt` context scan |
| `src/core/elkex.ts`, `src/core/markdown.ts` | example files (`// elkex:` sections) and their descriptions |
| `src/editor/` | Monaco setup (ESM, selected contributions), `.elkt` Monarch grammar, completion and hover providers |
| `src/diagram/` | sprotty container, model classes, views, diagram CSS, SVG export |
| `src/generated/option-choices.json` | enum literals of the ENUM/ENUMSET options (`npm run gen:choices`) |
| `scripts/copy-assets.mjs` | build-time copies into `public/` (gitignored): `examples/**.elkt` + `examples/index.json`, `elk-lean/js/elk-worker.js`, `elk-lean/js/load-wasm.browser.mjs`, `elk-lean/dist/wasm/elk_lean_core.{mjs,wasm}` |
| `test/pipeline.test.mjs`, `test/browser.test.mjs` | Node smoke test, optional headless browser test |

The worker and the WASM are served unbundled at the paths of the npm package, so the package's own
`js/elk-worker.js` loads them exactly as in any other web app; the page bundles only `elk-api.js`
(the `ELK` class).

## Features compared with elk-live

Implemented:

- `.elkt` editor (Monaco 0.57) with syntax highlighting (elk-live's Monarch grammar, extended with
  strings, numbers and option keys), bracket matching, folding, comments, find.
- Parser errors as editor markers and in the status line, with the Lean parser's line and column
  (`ELK Text parse error: L:C: …`); layout errors (Java exception text) in the status line. The
  Xtext messages of elk-live are not reproduced (PLAN 8.1).
- Option completion (replaces the Xtext content assist): option keys filtered by the element the
  cursor is in (option targets: root/parents, nodes, edges, ports, labels), options known to the
  algorithm in scope listed first, insertion as `elk.<id>: `; values for ENUM/ENUMSET options, for
  booleans and for `algorithm:` (algorithm ids); keyword snippets (`node`, `edge`, `port`, `label`,
  `layout`). Hovers on option keys show name, type, targets, literals and description.
- Diagram (sprotty 1.4) with elk-live's visual model and colours: nodes and ports as rectangles,
  labels as text at their laid-out position (hanging baseline), edges as polylines through the
  section start, bend and end points with an arrow head, junction points as small circles; pan,
  zoom, selection and hover feedback, animated updates. Differences that keep more of the layout:
  every section of a hyperedge is drawn (elk-live joined all sections into one polyline), edges are
  placed in their coordinate container, `elk.json.shapeCoords`/`edgeCoords` are honoured, and edges
  are drawn exactly through their routing points (no sprotty anchor computation).
- Debounced edit → convert → layout (Web Worker) → model update; results of outdated edits are
  dropped; status line with node/edge counts and parse/layout timings; loading overlay while the
  WASM initialises.
- Examples: menu grouped by category from the 45 `external/elk-models/examples` files (copied at
  build time with their relative names), showing the `elkex:graph` section in the editor and the
  `elkex:doc` description above it (elk-live's examples page).
- ELK JSON input mode (elk-live's json page): switching from ELK Text converts the current graph
  with `convertElkt`; JSON syntax errors are located (line/column).
- Link sharing compatible with elk-live (`?compressedContent=` LZString, `?initialContent=`; plus
  `?e=<example path>` and `&format=json`), "Link" anchor and "Copy link".
- SVG export (viewBox around the drawing, diagram CSS embedded, dark mode kept), download of the
  laid-out ELK JSON, fit to view, dark mode (remembered per browser).

Left out, and why:

- ELK version selection (elk-live lays out with ELK 0.3–0.11 and snapshots, server-side and with
  several elkjs versions): elk-lean is one engine (ELK 0.12.0); a version menu would have nothing
  to switch to.
- Xtext language server features (validation beyond the parser, formatting, rename, go to
  definition, semantic highlighting): out of scope by design (PLAN 8.1); the Lean parser reports the
  first syntax/linking error only.
- Model browser (elk-live's models page over all of `elk-models`): would copy ~1,450 more files (~60 MB
  with the big realworld models) into the static site; the examples cover the editor use case.
- Graph format conversion page (elkt ↔ json ↔ elkg/XMI via the Java server): only ELK Text → ELK
  JSON exists in elk-lean (`convertElkt`); there is no `.elkg` (XMI) support and no JSON → ELK Text
  writer. The JSON download and the format switch cover the elkt → json direction.
- elk-live's landing page with links to the other demonstrators.

## Supported browsers

The WASM build is `-sMEMORY64=2`: 64-bit C **lowered to wasm32**, so the module does not use the
memory64 proposal and needs no memory64 support in the browser. It uses bulk memory, sign
extension, non-trapping float-to-int and mutable globals (validated with binaryen against that
feature set), BigInt ↔ i64 integration, up to 4 GB of linear memory, and the package's classic Web
Worker loads the engine with a dynamic `import()`. Monaco 0.57 itself targets current evergreen
browsers.

- Tested: Chrome 156 (headless, `test/browser.test.mjs`, macOS arm64).
- Expected to work (feature support, not tested here): current Chrome/Edge (≥ 85), Firefox ≥ 114
  (dynamic `import()` in workers), Safari ≥ 15 (desktop; iOS Safari limits the memory of a page, so
  large graphs may fail there).
- The Web Worker's stack cannot be raised from JavaScript; very deep graphs (thousands of nesting
  levels, long mrtree/radial chains) fail with `RangeError` as described in
  `plugins/org.eclipse.elk.js/README.md` "Limits".

## Tests

`npm test` runs `node --test test/*.test.mjs`:

- `test/pipeline.test.mjs` (needs `npm run assets`; CLI comparisons need `.lake/build/bin/elk`,
  `ELK_LEAN_BIN`): loads the app's core modules with Node's type stripping and the browser WASM
  build from `public/elk-lean/` (the files the worker loads), runs the pipeline on all 45 examples
  and compares the laid-out graphs with `elk layout X.elkt --defaults` (45/45 identical), checks the
  sprotty model ids, parse/layout/JSON diagnostics, the completion metadata and that the enum
  snapshot equals `elk options --choices`; after `npm run build` also the `dist/` contents.
- `test/browser.test.mjs` (optional, skipped without `playwright-core` and a Chrome): serves
  `dist/`, loads the page in headless Chrome, waits for the first layout, types ELK Text and expects
  the new node ids in the SVG, types a syntax error and expects the marker and the error status,
  completes `dire` → `elk.direction: DOWN`, loads an example from the menu, exports the SVG and
  expects no page errors. playwright-core is not a dependency; run it with
  `PLAYWRIGHT_CORE=<dir of an installed playwright-core> npm test` (it uses the installed Chrome,
  `CHROME_PATH`, no browser download).

## CI

`.gitlab-ci.yml` at the repository root has a **draft** `.pages` job (hidden: a job name starting
with `.` never runs). It is not enabled because the runner/image decisions for CI and releases are
on hold; renaming it to `pages` publishes `dist/` to GitLab Pages after `build:wasm`.

## License and provenance

EPL-2.0 OR GPL-3.0-or-later, like the rest of elk-lean, except the files ported from elk-live
(EPL-2.0 only, original headers kept, changes noted in each header):

| file | elk-live source |
|---|---|
| `src/editor/elkt-language.ts` | `client/src/elkgraph/elkt-language.ts` (TypeFox, 2017) |
| `src/diagram/sprotty-config.ts` | `client/src/sprotty-config.ts` (TypeFox, 2017) |
| `src/diagram/sprotty-model.ts` | `client/src/sprotty-model.ts` (TypeFox, 2017) |
| `src/diagram/views.ts` | `client/src/views.tsx` (TypeFox, 2017) |
| `src/diagram/diagram.css` | `client/app/diagram.css` (colours unchanged) |
| `src/core/elkex.ts` | `client/src/examples/elkex.ts` (Kiel University, 2020) |

`src/core/elk-to-sprotty.ts` is new code following elk-live's `json/elkgraph-to-sprotty.ts` and the
server's `ElkGraphDiagramGenerator`. Bundled third-party packages and the copied examples are listed
in the repository's `NOTICE` ("Browser Demo"). elk-live itself (EPL-2.0) is © TypeFox GmbH, Kiel
University and others.
