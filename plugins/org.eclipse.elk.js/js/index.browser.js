'use strict';

/**
 * elk-lean browser entry point (port of elk-rs plugins/org.eclipse.elk.js/js/index.browser.js).
 *
 * Uses the WASM module directly (direct mode) or via a Web Worker.
 *
 * SPDX-License-Identifier: EPL-2.0 OR GPL-3.0-or-later
 */
var ELK = require('./elk-api.js');

class ELKBrowser extends ELK {
  constructor(options = {}) {
    var optionsClone = Object.assign({}, options);

    // If no worker requested, try direct WASM
    if (typeof optionsClone.workerUrl === 'undefined'
        && typeof optionsClone.workerFactory === 'undefined') {
      // Keep the constructor synchronous; every public operation already returns
      // a Promise and waits for the same lazy WASM initialization.
      var ready;
      var call = function(method, args) {
        if (!ready) {
          ready = import('./load-wasm.browser.mjs').then(function(loader) {
            return loader.default();
          });
        }
        return ready.then(function(wasm) {
          try {
            return wasm[method].apply(wasm, args);
          } finally {
            // a failed instance (out of memory) is replaced on the next call (load-wasm.browser.mjs)
            if (wasm.failed) ready = undefined;
          }
        });
      };
      optionsClone.backend = {
        layout_json: function(graph, layoutOptions) { return call('layout_json', [graph, layoutOptions]); },
        known_layout_algorithms: function() { return call('known_layout_algorithms', []); },
        known_layout_options: function() { return call('known_layout_options', []); },
        known_layout_categories: function() { return call('known_layout_categories', []); },
      };
    }

    super(optionsClone);
  }
}

Object.defineProperty(module.exports, "__esModule", { value: true });
module.exports = ELKBrowser;
ELKBrowser.default = ELKBrowser;
