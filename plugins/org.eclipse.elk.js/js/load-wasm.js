'use strict';

/**
 * elk-lean WASM backend loader for Node.js (fallback when no native addon is available).
 *
 * Contract (kept from elk-rs js/load-wasm.js): `loadWasm()` synchronously returns a backend,
 * an object with the four functions
 *   layout_json(graphJson, optionsJson) -> string
 *   known_layout_algorithms() / known_layout_options() / known_layout_categories() -> string
 * that throw an Error(message) on failure, and caches it.
 *
 * The backend is the emscripten CommonJS build of plugins/org.eclipse.elk.wasm
 * (scripts/build_wasm.sh copies it to dist/wasm-node/: elk_lean.cjs + elk_lean.wasm); it compiles
 * and instantiates the module synchronously on the first call.
 *
 * SPDX-License-Identifier: EPL-2.0 OR GPL-3.0-or-later
 */
var backend;
module.exports = function loadWasm() {
  if (backend) return backend;
  var factory;
  try {
    factory = require('../dist/wasm-node/elk_lean.cjs');
  } catch (e) {
    if (e && e.code === 'MODULE_NOT_FOUND' && String(e.message).indexOf('elk_lean.cjs') !== -1) {
      throw new Error('elk-lean: WASM backend not built (dist/wasm-node/elk_lean.cjs missing; '
        + 'run scripts/build_wasm.sh) and no native addon is available');
    }
    throw e;
  }
  backend = factory.createBackend();
  return backend;
};
