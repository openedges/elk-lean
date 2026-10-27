'use strict';

/*
 * Node.js WASM backend loader of the elk-lean npm package (proposed js/load-wasm.js of
 * plugins/org.eclipse.elk.js, same interface as elk-rs): returns an object with the synchronous
 * functions layout_json(graphJson, optionsJson), known_layout_algorithms(),
 * known_layout_options() and known_layout_categories(), which return JSON strings and throw
 * Error(message) on failure. The emscripten CommonJS build compiles and instantiates the module
 * synchronously on the first call; later calls return the same backend.
 *
 * Expects the build output of scripts/build_wasm.sh at ../dist/wasm-node/ (elk_lean.cjs +
 * elk_lean.wasm), i.e. dist/wasm-node/ of the package.
 *
 * SPDX-License-Identifier: EPL-2.0 OR GPL-3.0-or-later
 */
var backend;
module.exports = function loadWasm() {
  if (backend) return backend;
  backend = require('../dist/wasm-node/elk_lean.cjs').createBackend();
  return backend;
};
