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
 * TODO(Phase 8, WASM): plugins/org.eclipse.elk.wasm is not built yet. Replace this stub with
 * the emscripten module loader (Node CJS build under ../dist/wasm-node/) once it exists.
 *
 * SPDX-License-Identifier: EPL-2.0 OR GPL-3.0-or-later
 */
var backend;
module.exports = function loadWasm() {
  if (backend) return backend;
  throw new Error('elk-lean: WASM backend not built (plugins/org.eclipse.elk.wasm is pending); '
    + 'install the native platform package or build the addon with scripts/build_napi.sh');
};
