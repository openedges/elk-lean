/**
 * elk-lean WASM backend loader for browsers and Web Workers (ESM).
 *
 * Contract: the default export `loadWasm(moduleArg)` returns a Promise of a backend, an object
 * with the four functions layout_json(graphJson, optionsJson), known_layout_algorithms(),
 * known_layout_options(), known_layout_categories() (JSON strings; Error on failure).
 * Concurrent first calls share one initialisation; once the backend has failed (`backend.failed`)
 * the next call creates a new instance. `moduleArg` is forwarded to the emscripten factory (e.g.
 * `locateFile` when dist/wasm/ is served elsewhere).
 *
 * The backend is the browser ES module build of plugins/org.eclipse.elk.wasm
 * (scripts/build_wasm.sh copies it to dist/wasm/: elk_lean.mjs + elk_lean_core.{mjs,wasm}); the
 * emscripten factory `elk_lean_core.mjs` is used directly, since `elk_lean.mjs` keeps one instance.
 *
 * SPDX-License-Identifier: EPL-2.0 OR GPL-3.0-or-later
 */
let ready;
let current;
export default function loadWasm(moduleArg) {
  // a failed instance (`backend.failed`: C exit inside a call, e.g. Lean's out-of-memory panic)
  // is replaced by a new one; the old instance and its linear memory are released with it
  if (current && current.failed) {
    ready = undefined;
    current = undefined;
  }
  if (!ready) {
    ready = import('../dist/wasm/elk_lean_core.mjs')
      .then((factory) => factory.default(moduleArg || {}))
      .then((module) => (current = module.createBackend()));
  }
  return ready;
}
