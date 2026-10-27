/**
 * elk-lean WASM backend loader for browsers and Web Workers (ESM).
 *
 * Contract: the default export `loadWasm()` returns a Promise of a backend, an object with the
 * four functions layout_json(graphJson, optionsJson), known_layout_algorithms(),
 * known_layout_options(), known_layout_categories() (JSON strings; Error on failure).
 * Concurrent first calls must share one initialisation.
 *
 * TODO(Phase 8, WASM): plugins/org.eclipse.elk.wasm is not built yet. Replace this stub with
 * the emscripten ES module loader (browser build under ../dist/wasm/) once it exists.
 *
 * SPDX-License-Identifier: EPL-2.0 OR GPL-3.0-or-later
 */
let ready;
export default function loadWasm() {
  if (!ready) {
    ready = Promise.reject(new Error('elk-lean: WASM backend not built '
      + '(plugins/org.eclipse.elk.wasm is pending)'));
    // keep the rejection observable by every caller without an unhandled-rejection warning
    ready.catch(() => {});
  }
  return ready;
}
