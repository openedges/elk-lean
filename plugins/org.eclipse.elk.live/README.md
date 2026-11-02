# org.eclipse.elk.live — ELK Live on elk-lean

A static, server-less replacement for [elk-live](https://github.com/kieler/elk-live)
(`external/elk-live`, "ElkGraph Web", the "ELK Demonstrators" site): a landing page, an ELK Text
(`.elkt`) editor and an ELK JSON editor with a synchronized diagram, and the annotated examples.
elk-live needs a Java server (Xtext language server for parsing, validation and completion, ELK Java
for the layout) or elkjs; here everything runs in the browser on one engine:

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
npm run dev        # http://localhost:5173/ (copies the assets, then Vite's dev server)
npm run build      # static site in dist/ (copies the assets, tsc --noEmit, vite build)
npm run preview    # serves dist/
npm test           # Node smoke tests (see Tests)
npm run gen:choices   # refresh src/generated/option-choices.json from `elk options --choices`
```

Pages (relative to the dev server or the deployed `dist/`):

| page | elk-live counterpart | content |
|---|---|---|
| `index.html` | `app/index.html` | "ELK Demonstrators" landing page: links to the editors and the examples |
| `elkgraph.html` | `elkgraph.html` | "ELKT Editor": ELK Text with completion, markers, diagram |
| `json.html` | `json.html` | "ELK JSON Editor": ELK JSON (JSON5 syntax), markers, diagram |
| `examples.html` | `examples.html` | "Examples": table of contents, example text and diagram, description |

URL parameters (elk-live compatible): `elkgraph.html` and `json.html` take
`?compressedContent=<LZString>` (what "Link to this model" produces) and `?initialContent=<text>`;
`examples.html` takes `?e=<example path>` (e.g. `?e=general/direction`; without it a random example
is shown). Links shared from the earlier single-page version (`index.html?compressedContent=…`,
`…&format=json`, `?initialContent=…`, `?e=…`) are forwarded by the landing page to the page that
now shows them, with the query string kept.

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
| `index.html`, `elkgraph.html`, `json.html`, `examples.html` | the four pages (static markup; the editor pages get their navbar and footer from `src/app/chrome.ts`) |
| `src/pages/index.ts` | landing page: old-link redirect, engine badge, dark mode |
| `src/pages/elkgraph.ts` | ELKT editor: `.elkt` language and completion, "Open as JSON" |
| `src/pages/json.ts` | JSON editor: `elkj` language, elk-live's JSON5 sample |
| `src/pages/examples.ts` | examples: table of contents, `?e=` and history, example text, title and description |
| `src/app/editor-page.ts` | the common part of the two editor pages (navbar, footer, model link, start-up) |
| `src/app/editor-diagram.ts` | editor + diagram pair: Monaco, sprotty, debounced pipeline, markers, status line, loading overlay, diagram tools (Fit, SVG, JSON) |
| `src/app/engine.ts` | `ELK` in Web Worker mode and the completion metadata |
| `src/app/chrome.ts` | navbar (brand, title, engine badge, dark-mode toggle) and footer (model link, status, engine line) |
| `src/app/dark-mode.ts` | dark mode (`elk-dark-mode` class, remembered under `elk-lean-live-dark-mode`) |
| `src/style.css`, `src/app/vendor.css` | styles of all pages; Monaco codicons and sprotty CSS (editor pages only) |
| `src/core/pipeline.ts` | DOM-free pipeline: `convertElkt` or JSON5 → `layout` → sprotty model; parse/layout diagnostics with line/column |
| `src/core/urls.ts` | DOM-free URL handling: model links (`?compressedContent=`), initial content, old-link redirect |
| `src/core/elk-to-sprotty.ts` | laid-out ELK JSON → sprotty model (elk-live's visual model) |
| `src/core/options.ts` | completion metadata (`knownLayoutOptions()`, `knownLayoutAlgorithms()`, enum literals), `.elkt` context scan |
| `src/core/elkex.ts`, `src/core/markdown.ts` | example files (`// elkex:` sections), category tree and table of contents; descriptions rendered with showdown (GitHub flavour, `simpleLineBreaks: false`) exactly as elk-live does |
| `src/editor/` | Monaco setup (ESM, selected contributions), `.elkt` and `elkj` Monarch grammars, completion and hover providers |
| `src/diagram/` | sprotty container, model classes, views, diagram CSS, SVG export |
| `src/generated/option-choices.json` | enum literals of the ENUM/ENUMSET options (`npm run gen:choices`) |
| `scripts/copy-assets.mjs` | build-time copies into `public/` (gitignored): `examples/**.elkt` + `examples/index.json`, `elk-lean/js/elk-worker.js`, `elk-lean/js/load-wasm.browser.mjs`, `elk-lean/dist/wasm/elk_lean_core.{mjs,wasm}` |
| `test/pipeline.test.mjs`, `test/browser.test.mjs` | Node smoke test, optional headless browser test |

`src/core/*` has no DOM dependency (the Node test imports it). Vite builds the four pages
(`build.rollupOptions.input`); Monaco, sprotty and the app code shared by the three editor pages
end up in one common chunk, the landing page loads only its small script and the stylesheet.

The worker and the WASM are served unbundled at the paths of the npm package, so the package's own
`js/elk-worker.js` loads them exactly as in any other web app; the pages bundle only `elk-api.js`
(the `ELK` class).
## Features compared with elk-live

Implemented:

- Page structure of elk-live: the "ELK Demonstrators" landing page (`index.html`; cards for the
  interactive editor with its two formats and for the examples), the ELKT editor
  (`elkgraph.html`), the JSON editor (`json.html`) and the examples (`examples.html`), each with
  elk-live's navbar (brand linking to the landing page, centered title, dark-mode toggle) and
  footer ("Link to this model" on the editors). Where elk-live has its ELK version menu, the navbar
  shows an engine badge `elk-lean 0.12.0 · ELK 0.12.0` (tooltip: one engine, nothing to choose).
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
- ELK JSON editor (elk-live's json page): the text is parsed with JSON5 like elk-live (comments,
  unquoted keys, single quotes, trailing commas), highlighted with elk-live's `elkj` Monarch grammar
  (extended with strings, numbers and keys), JSON5 syntax errors become markers with line and
  column, elk-live's JSON5 sample is the default content. Unlike elk-live,
  `org.eclipse.elk.json.edgeCoords` is not forced to `PARENT` before the layout (the renderer here
  honours `shapeCoords`/`edgeCoords`), so the JSON download is the engine's result for the input.
  The ELKT editor's "Open as JSON" converts the current text with `convertElkt` (elk-live default
  sizes) and opens it in the JSON editor (Back returns to the ELK Text).
- Examples page (elk-live's examples page): a sidebar table of contents of the 45
  `external/elk-models/examples` files (copied at build time with their relative names), built like
  elk-live's `createNavigationDepthFirstAlphabetically` (a heading per category, `Parent > Child`
  for nested ones, indented by depth, examples sorted by label); the `elkex:graph` section in an
  editor next to its diagram, below them the category, the label and the `elkex:doc` description.
  `?e=<path>` selects an example, otherwise a random one is shown; choosing from the table of
  contents pushes a history entry with `?e=`, Back/Forward reload the example; like elk-live, the
  initial load leaves the URL as opened (a random example is not written into it). Editing the text re-layouts
  live with markers; "Open in editor" takes the (edited) text to the ELKT editor.
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
- Link sharing compatible with elk-live (`?compressedContent=` LZString, `?initialContent=`),
  "Link to this model" and "Copy link"; `examples.html?e=<example path>`.
- Diagram tools on every editor page (an elk-lean extra, shown while the pointer is over the diagram so
  that the pages start out looking like elk-live's): fit to view (manual only: like elk-live, the diagram starts at
  the top-left corner at zoom 1 and keeps its viewport across updates), SVG export (viewBox around the drawing, diagram
  CSS embedded, dark mode kept), download of the laid-out ELK JSON; dark mode on every page
  (remembered per browser).

Changed on purpose:

- The example drop-down and the elkt/json format switch of the earlier single-page version are
  gone: the examples have their own page (as in elk-live) and the formats have their own editors;
  "Open as JSON" and "Open in editor" carry a graph between the pages. Old links are forwarded.

Left out, and why:

- ELK version selection (elk-live lays out with ELK 0.3–0.11 and snapshots, server-side and with
  several elkjs versions): elk-lean is one engine (ELK 0.12.0); a version menu would have nothing
  to switch to. The navbar shows the engine badge instead.
- Xtext language server features (validation beyond the parser, formatting, rename, go to
  definition, semantic highlighting): out of scope by design (PLAN 8.1); the Lean parser reports the
  first syntax/linking error only. The JSON editor has no content assist (elk-live's came from its
  JSON language server).
- Model browser (elk-live's models page over all of `elk-models`): would copy ~1,450 more files (~60 MB
  with the big realworld models) into the static site; the examples cover the editor use case. The
  landing page shows the card disabled with this reason.
- Graph format conversion page (elkt ↔ json ↔ elkg/XMI via the Java server): only ELK Text → ELK
  JSON exists in elk-lean (`convertElkt`); there is no `.elkg` (XMI) support and no JSON → ELK Text
  writer. "Open as JSON" and the JSON download cover the elkt → json direction. The landing page
  shows the card disabled with this reason.
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
  sprotty model ids, parse/layout/JSON diagnostics, the JSON5 path (elk-live's sample laid out as
  given, JSON5 error locations), old-link redirects and model links, the examples' category tree
  and table of contents order, the completion metadata and that the enum snapshot equals
  `elk options --choices`; after `npm run build` also that `dist/` holds the four pages with their
  scripts.
- `test/browser.test.mjs` (optional, skipped without `playwright-core` and a Chrome): serves
  `dist/` and drives headless Chrome through the pages. Landing page: links, engine badge, dark
  mode, an old `?compressedContent=` link forwarded to the ELKT editor. ELKT editor: first layout,
  typed ELK Text renders the new node ids, a syntax error gets the marker and the error status,
  `dire` completes to `elk.direction: DOWN` (re-laid out top-down), "Open as JSON" opens the
  converted graph in the JSON editor and Back returns. JSON editor: the JSON5 sample renders, a
  JSON5 syntax error is marked at its line and column. Examples: the table of contents has every
  example, `?e=general/direction` shows it, SVG export, a click on another entry renders it and
  updates the URL, edits re-layout, Back restores the previous example, a random example without
  `?e=`. No page errors. playwright-core is not a dependency; run it with
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
| `src/editor/elkj-language.ts` | `client/src/json/elk-json-language.ts` (Kiel University, 2020) |
| `src/diagram/sprotty-config.ts` | `client/src/sprotty-config.ts` (TypeFox, 2017) |
| `src/diagram/sprotty-model.ts` | `client/src/sprotty-model.ts` (TypeFox, 2017) |
| `src/diagram/views.ts` | `client/src/views.tsx` (TypeFox, 2017) |
| `src/diagram/diagram.css` | `client/app/diagram.css` (colours unchanged) |
| `src/core/elkex.ts` | `client/src/examples/elkex.ts` and the navigation of `client/src/examples/examples.ts` (Kiel University, 2020) |

`src/core/elk-to-sprotty.ts` is new code following elk-live's `json/elkgraph-to-sprotty.ts` and the
server's `ElkGraphDiagramGenerator`. The page structure and texts of `index.html`, `elkgraph.html`,
`json.html` and `examples.html` follow elk-live's `client/app/index.html` and page templates
(`elkgraph_template.html`, `json_template.html`, `examples_template.html`); the JSON editor's
default content is elk-live's sample from `client/src/json/editor.ts`. Bundled third-party packages
(including json5 2.2.3, MIT) and the copied examples are listed in the repository's `NOTICE`
("Browser Demo"). elk-live itself (EPL-2.0) is © TypeFox GmbH, Kiel University and others.
