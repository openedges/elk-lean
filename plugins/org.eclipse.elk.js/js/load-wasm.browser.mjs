/**
 * elk-lean WASM backend loader for browsers and Web Workers (ESM).
 *
 * Contract: the default export `loadWasm(moduleArg)` returns a Promise of a backend, an object
 * with the four functions layout_json(graphJson, optionsJson), known_layout_algorithms(),
 * known_layout_options(), known_layout_categories() (JSON strings; Error on failure).
 * Concurrent first calls share one initialisation. `moduleArg` is forwarded to the emscripten
 * factory (e.g. `locateFile` when dist/wasm/ is served elsewhere).
 *
 * The backend is the browser ES module build of plugins/org.eclipse.elk.wasm
 * (scripts/build_wasm.sh copies it to dist/wasm/: elk_lean.mjs + elk_lean_core.{mjs,wasm}).
 *
 * SPDX-License-Identifier: EPL-2.0 OR GPL-3.0-or-later
 */
let ready;
export default function loadWasm(moduleArg) {
  if (!ready) {
    ready = import('../dist/wasm/elk_lean.mjs').then((wasm) => wasm.default(moduleArg).then(() => wasm));
  }
  return ready;
}
