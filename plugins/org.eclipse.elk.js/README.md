# elk-lean (npm)

Eclipse Layout Kernel 0.12.0 ported to pure Lean 4 — drop-in replacement for
[elkjs](https://github.com/kieler/elkjs) backed by a native Node.js addon, with a WebAssembly build
as fallback (Node.js) and as the browser backend.
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

A backend is an object with `layout_json(graphJson, optionsJson)`, `known_layout_algorithms()`,
`known_layout_options()`, `known_layout_categories()` and `convert_elkt(elktText, flags)` returning
JSON strings and throwing `Error(message)` (`convert_elkt` is needed by `convertElkt` only; `flags`
are the `ELK_LEAN_CONVERT_*` bits of `elk_lean.h`, also `ELK.CONVERT_DEFAULTS` = 1,
`ELK.CONVERT_PRETTY` = 2, `ELK.CONVERT_SORT_KEYS` = 4).

`js/index.js` (Node.js) and the `worker_threads` branch of `js/elk-worker.js` load, in order:

1. the platform package `elk-lean-<triple>` (`optionalDependencies`, templates in `npm/<triple>/`),
2. `dist/elk-lean.<triple>.node` (built by `sh scripts/build_napi.sh`),
3. `dist/elk-lean.node`,
4. the WASM backend `js/load-wasm.js`: `dist/wasm-node/elk_lean.cjs` + `elk_lean.wasm`, the
   emscripten CommonJS build, compiled and initialised synchronously on first use. Without a WASM
   build the loader throws `WASM backend not built`.

`js/index.browser.js` (direct mode, lazy asynchronous initialisation) and the Web Worker branch of
`js/elk-worker.js` use `js/load-wasm.browser.mjs`: `dist/wasm/elk_lean.mjs` +
`elk_lean_core.{mjs,wasm}` (ES module; the `.wasm` is resolved next to `elk_lean_core.mjs` through
`import.meta.url`). `sh scripts/build_wasm.sh` builds both WASM variants
(`plugins/org.eclipse.elk.wasm`) and copies them to `dist/wasm-node/` and `dist/wasm/`.

| entry point | direct mode | `workerUrl` |
|---|---|---|
| Node.js `js/index.js` | native addon, else WASM (main thread) | `worker_threads` Worker with a larger stack (`workerStackSizeMb`), backend loaded in the worker in the same order |
| browser `js/index.browser.js` | WASM (main thread) | Web Worker running `js/elk-worker.js` (WASM) |

Triples: `darwin-arm64`, `darwin-x64`, `linux-x64-gnu`, `linux-x64-musl`, `linux-arm64-gnu`,
`win32-x64-msvc` (only `darwin-arm64` is built and tested so far).

## API

Same as elkjs: `new ELK({ defaultLayoutOptions, algorithms, workerUrl, workerFactory })`,
`elk.layout(graph, { layoutOptions })`, `elk.knownLayoutAlgorithms()`, `elk.knownLayoutOptions()`,
`elk.knownLayoutCategories()`, `elk.terminateWorker()`. `algorithms` is accepted for compatibility;
every ported algorithm (including VertiFlex and DisCo, which elkjs 0.12.0 does not register) stays
available.

elk-lean additions and differences:

- `elk.convertElkt(text, { defaults = false } = {}) → Promise<ElkNode>`: parses ELK Text (`.elkt`)
  with the Lean parser (`Elk.Text.parseElkt`) and resolves to the ElkGraph JSON object, the same graph
  as the CLI `elk convert` (the backends' `convert_elkt` string is byte-identical to it, checked for
  the 898 `.elkt` files of `external/elk-models`). `defaults: true` is `elk convert --defaults`: shapes
  without a size get the elk-live sizes (nodes 30 x 30, ports 5 x 5, labels 9 x length by 16). A syntax
  or linking error rejects with the CLI's message `ELK Text parse error: <line>:<col>: <message>` (an
  `Error` in direct mode, `{ message }` in worker mode like layout errors). Available on every backend
  (addon, WASM, Worker; worker command `{ cmd: 'convertElkt', elkt, flags }`). The demo
  `plugins/org.eclipse.elk.live` uses it to edit `.elkt` in the browser without a server.

- `threads` (constructor option, or per call `elk.layout(graph, { threads })`; native addon only):
  the cap of the parallel sibling layout (`docs/parallel-layout.md`). Independent sibling sub-graphs
  of separately laid out compound nodes run on Lean worker threads inside one call; the result is
  byte-identical for every value. `1` = sequential; omitted = the addon default, `ELK_LEAN_THREADS`
  or `min(hardware threads, 8)` (the addon starts the Lean task manager when it loads,
  `elk_lean_init_threads(0)`). A value that is not a positive integer throws `TypeError` (rejects in
  `layout`). The WASM backend is single-threaded and ignores it (sequential); in worker mode it is
  passed to the worker's backend (`{ cmd: 'layout', graphJson, optionsJson, threads }`). Lean worker
  threads have the Lean runtime's thread stack (1 GB reserved; `LEAN_STACK_SIZE_KB` does not apply
  to the addon), not the calling
  thread's: a sub-graph that is too deep for the calling thread's stack can lay out there (see
  "Limits").
- `workerStackSizeMb` (Node.js only, default 64, `ELK.DEFAULT_WORKER_STACK_SIZE_MB`): stack size of
  the `worker_threads` Worker created for `workerUrl` (`resourceLimits.stackSizeMb`). Ignored with
  `workerFactory` (pass `resourceLimits` to your own `Worker`) and in browsers. A non-positive or
  non-numeric value throws `TypeError`.
- In worker mode the graph and the result travel as JSON strings (`{ cmd: 'layout', graphJson,
  optionsJson }`; `js/elk-worker.js` still accepts elkjs-style `graph`/`layoutOptions` objects).
  `structuredClone`/`postMessage` of the graph object recurses per nesting level and fails at about
  1,000 compound levels on the default V8 stack, `JSON.stringify` at about 3,000 and `JSON.parse` not
  at all. `elk-api.js` therefore needs `js/elk-worker.js`, not the elkjs worker.
- A worker that fails outside a request (`error` event, `worker_threads` `exit`, including
  `terminateWorker()`) rejects the pending requests (elkjs leaves them pending).

## Limits

The Lean-generated code is recursive in places (JSON parser per nesting level, JSON importer per
compound level, `EadesRadial.positionNodes` per tree level, unspecialised `Array.foldl` in
`MrTree.EdgeRouter.sortByFloat` per node of a level), and every backend runs it on the stack of the
calling thread. Measured with Node.js 24.22 / Chrome 156 on macOS arm64 (default ~1 MB V8 stack
limit, `--stack-size=984`):

| input (recursing function) | CLI | addon, main | addon, worker 4 MB | addon, worker 64 MB | WASM, main | WASM, worker 64 MB (default) | Chrome, main | Chrome, Web Worker |
|---|---|---|---|---|---|---|---|---|
| nested JSON arrays, depth 4,000 (`Json.Parser.parseValue`) | ok | ok | ok | ok | ok | ok | ok | `RangeError` |
| same, depth 8,000 | ok | ok | ok | ok | `RangeError` | ok | `RangeError` | `RangeError` |
| same, depth 64,000 (1,000,000) | ok (ok) | **crash** | **crash** (at 32,000) | ok | `RangeError` | ok (needs 512 MB) | `RangeError` | `RangeError` |
| compound nesting, 1,000 levels (`JsonImporter.transformNode`/`transformEdges`) | ok | ok | ok | | ok | ok | ok | `RangeError` |
| same, 2,000 levels | ok | ok | ok | | `RangeError` | ok | `RangeError` | `RangeError` |
| mrtree chain, 1,000 nodes (`MrTree.EdgeRouter.sortByFloat`: `Array.foldl` in `Id`) | ok | ok | ok | | ok | ok | ok | `RangeError` |
| same, 2,000 / 8,000 nodes | ok | ok | ok | | `RangeError` | ok | `RangeError` | `RangeError` |
| same, 32,000 nodes | ok | **crash** | **crash** | | `RangeError` | ok | | |
| same, 128,000 nodes | ok | **crash** | **crash** | ok | `RangeError` | `RangeError` (256 MB: ok) | | |
| radial chain, 2,000 nodes (`EadesRadial.positionNodes`) | ok | ok | ok | | borderline | ok | ok | `RangeError` |
| same, 4,000 nodes | ok | ok | ok | | `RangeError` | ok | `RangeError` | `RangeError` |
| layered chain 8,000 nodes; flat DAG 10,000 nodes / 20,000 edges | ok | ok | ok | | ok | ok | ok | ok |

- **WASM**: wasm frames live on the JS engine's native stack, so overflow is a catchable
  `RangeError: Maximum call stack size exceeded`. The instance stays usable; the objects of the
  aborted call are not freed (a few MB per failure). The emscripten shadow stack in linear memory
  (`-sSTACK_SIZE=16MiB`) is not the limit: a 64 KiB build still parses a million nested arrays and
  overflows only on mrtree chains above ~1,000 nodes (~32-64 bytes per level), so 16 MiB lasts for
  ~250,000+ levels, beyond what a 256 MB worker stack reaches.
- **Native addon**: runs on the calling thread's stack (Node.js main thread 8 MB, `worker_threads`
  default 4 MB). Overflow is a `SIGSEGV`/`SIGILL` that kills the whole process (V8's signal handlers
  are kept, the Lean stack-overflow handler is not installed). The CLI runs `main` on Lean's 1 GB
  thread (`LEAN_STACK_SIZE_KB`), hence its much higher limit. With the parallel sibling layout
  (`threads` > 1, the default) the sibling sub-graphs laid out by Lean worker threads get that 1 GB
  stack too; the calling thread lays out the first chunk and everything else on its own stack.
- **Worker mode** raises the limit of both backends: the worker's thread stack and V8's limit are
  both `workerStackSizeMb` (reserved address space, committed only when used). The graph must still
  pass `JSON.stringify` on the calling thread (~3,000 compound levels by default).
- **Node.js main thread**: `node --stack-size=<KB>` raises V8's limit, but the thread stack itself
  is 8 MB (`ulimit -s`): up to ~7,800 is safe (the 8,000-node mrtree chain passes with
  `--stack-size=7000`), larger values crash the process instead of throwing.
- **Browsers**: the stack cannot be set from JavaScript. Chrome's limit is ~1 MB on the main thread
  and smaller in a Web Worker (the worker failed at JSON depth 4,000 and chain 1,000 where the main
  thread passed), so a Web Worker only keeps the page responsive; very deep graphs need Node.js
  worker mode or the native CLI.
- **Memory**: the WASM build is wasm32 (`-sMEMORY64=2`) with a 4 GB maximum
  (`-sMAXIMUM_MEMORY=4GB`; it starts at 42 MiB and grows on demand). The orthogonal router of a
  layered node with N ports, each to its own target node, keeps O(N²) segment dependencies (native
  peak 50 MB at 1,000, 0.74 GB at 4,000, 1.2 GB at 5,000, 2.4 GB at 8,000): N = 8,000 lays out
  (4,085 MiB of wasm memory), 8,500 does not; with emscripten's former 2 GB default the limit was
  ~4,000 (4,250 failed). Results are the same in Node.js direct and worker mode and in Chrome's main
  thread and Web Worker.
- **Out of memory**: the Lean runtime prints `INTERNAL PANIC: out of memory` (stderr) and calls
  C `exit(1)`. The WASM backend then throws `Error('elk-lean: the WASM instance terminated (Program
  terminated with exit(1)), most likely out of memory (N MiB in use); create a new instance')`,
  restores `process.exitCode` (emscripten sets it to 1) and marks the instance failed
  (`backend.failed`): the aborted call's objects are never freed and the runtime state is unknown, so
  every later call on that instance throws the same error. Recovery: `js/load-wasm.js` and
  `js/load-wasm.browser.mjs` create a new instance on their next call, so a new `ELK()` (direct
  mode) gets a fresh backend, the browser direct mode and `js/elk-worker.js` (`worker_threads`, Web
  Worker, in-process fake worker) replace the instance before the next request; the failing request
  itself is rejected. The native addon and the CLI are limited only by the machine's memory.

## Tests

```sh
sh scripts/build_napi.sh                       # from the repository root
sh scripts/build_wasm.sh                       # optional: WASM backend (tests skip it when missing)
node --test plugins/org.eclipse.elk.js/test/   # node:test, no npm dependencies
```

`test/testConvertElkt.test.mjs` converts every `.elkt` of `external/elk-models` (`ELK_MODELS_DIR`;
in a worktree without submodules the main checkout's copy) with the addon and the WASM backend, plain
and with flags 5, and compares the strings byte-for-byte with `elk convert` (and
`--defaults --sort-keys`) of `.lake/build/bin/elk` (`ELK_LEAN_BIN`), plus syntax errors and
`convertElkt` in direct, fake-worker and `worker_threads` modes.
`test/testThreads.test.mjs` (with `ELK_LEAN_PAR_MIN_WORK=0`, every sibling sub-graph on a task)
checks that the addon gives the same bytes for thread caps 1, 2, 3, 8 and the default on hierarchical
and multi-component graphs, the same graphs through `new ELK({ threads })` and `layout(g, { threads })`,
the first throwing child in sibling order, the `TypeError`s, and concurrent `worker_threads` that each
use the parallel layout.
`test/testEntryPoints.test.mjs` runs the WASM fallback in direct, fake-worker and `worker_threads`
modes in a copy of the package without native addon; `test/testDeepRecursion.test.mjs` checks the
stack limits above (8,000-node mrtree chain: `RangeError` in WASM direct mode and with
`workerStackSizeMb: 1`, success in the default worker, equal to the native addon);
`test/testWasmMemory.test.mjs` checks the recovery from a failed WASM instance with a stub module
and, with `ELK_LEAN_TEST_LARGE_MEMORY=1` (~4 GB, ~30 s), the 5,000-port node in direct and worker
mode against the native addon and a 10,000-port node that runs out of memory.

Parity against the native CLI (byte-for-byte, `elk layout X --sort-keys`):

```sh
node plugins/org.eclipse.elk.js/test/parity/run.mjs --models external/elk-models/realworld --timing 5
node plugins/org.eclipse.elk.js/test/parity/run.mjs --models external/elk-models --ext elkt
node plugins/org.eclipse.elk.wasm/test/parity.cjs --models external/elk-models/realworld   # WASM
# optional structural comparison with elkjs (numeric tolerance 1e-6):
#   ... --elkjs <dir of an installed elkjs@0.12.0 package>
```

## License

[EPL-2.0 OR GPL-3.0-or-later](./LICENSE.md); see [NOTICE](./NOTICE) for ELK, elkjs and elk-rs
attribution and the statically linked Lean runtime components.
