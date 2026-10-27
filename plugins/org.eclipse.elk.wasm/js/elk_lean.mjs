/*
 * elk-lean WASM, browser / Web Worker ES module (dist/wasm/elk_lean.mjs).
 *
 * Same shape as the wasm-bindgen `--target web` glue of elk-rs: the default export initialises
 * the module (async, once), the named exports are the four synchronous backend functions and
 * throw `Error(message)` on failure.
 *
 *   import init, { layout_json } from './elk_lean.mjs';
 *   await init();
 *   const out = JSON.parse(layout_json(JSON.stringify(graph), '{}'));
 *
 * `init(moduleArg)` forwards `moduleArg` to the emscripten factory (e.g. `locateFile` or
 * `wasmBinary` when the .wasm is not served next to elk_lean_core.mjs).
 *
 * SPDX-License-Identifier: EPL-2.0 OR GPL-3.0-or-later
 */
import createElkLeanModule from './elk_lean_core.mjs';

let backend = null;
let ready = null;

export default function init(moduleArg) {
  if (!ready) {
    ready = createElkLeanModule(moduleArg || {}).then((module) => {
      backend = module.createBackend();
      return backend;
    });
  }
  return ready;
}

function current() {
  if (!backend) {
    throw new Error('elk-lean: the WASM module is not initialised (await the default export first)');
  }
  return backend;
}

export function layout_json(graphJson, optionsJson) {
  return current().layout_json(graphJson, optionsJson);
}

export function known_layout_algorithms() {
  return current().known_layout_algorithms();
}

export function known_layout_options() {
  return current().known_layout_options();
}

export function known_layout_categories() {
  return current().known_layout_categories();
}
