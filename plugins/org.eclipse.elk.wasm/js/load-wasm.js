'use strict';

/*
 * Node.js loader of this plugin's WASM build, used by test/parity.cjs, test/web_smoke.mjs and
 * test/browser_smoke.cjs: returns an object with the synchronous functions
 * layout_json(graphJson, optionsJson), known_layout_algorithms(), known_layout_options() and
 * known_layout_categories(), which return JSON strings and throw Error(message) on failure. The
 * emscripten CommonJS build compiles and instantiates the module synchronously on the first call;
 * later calls return the same backend.
 *
 * Expects the build output of scripts/build_wasm.sh at ../dist/wasm-node/ (elk_lean.cjs +
 * elk_lean.wasm). The npm package has its own copy (plugins/org.eclipse.elk.js/js/load-wasm.js,
 * same interface as elk-rs, reading the package's dist/wasm-node/).
 *
 * SPDX-License-Identifier: EPL-2.0 OR GPL-3.0-or-later
 */
var backend;
module.exports = function loadWasm() {
  if (backend) return backend;
  backend = require('../dist/wasm-node/elk_lean.cjs').createBackend();
  return backend;
};
