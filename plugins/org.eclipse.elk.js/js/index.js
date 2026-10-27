'use strict';

/**
 * elk-lean Node.js entry point (port of elk-rs plugins/org.eclipse.elk.js/js/index.js).
 *
 * Backend selection: platform package `elk-lean-<triple>` → local
 * `../dist/elk-lean.<triple>.node` → local `../dist/elk-lean.node` → WASM (`./load-wasm.js`).
 * Unlike elkjs, works without a Worker by default (direct mode).
 * Worker mode is available via workerUrl/workerFactory.
 *
 * SPDX-License-Identifier: EPL-2.0 OR GPL-3.0-or-later
 */
var ELK = require('./elk-api.js');
var native = require('./load-native.js');

function loadBackend() {
  var errors = [];

  // 1.-3. native addon (platform package, local platform .node, local generic .node)
  var addon = native.loadNativeAddon(errors);
  if (addon) return addon;

  // 4. Fall back to WASM (Node.js compatible build)
  try {
    return require('./load-wasm.js')();
  } catch (e) {
    errors.push('./load-wasm.js: ' + (e && e.message ? e.message : e));
  }

  throw new Error(
    'elk-lean: Could not load native addon or WASM module.\n'
    + 'Ensure the package was installed correctly.\n  '
    + errors.join('\n  ')
  );
}

class ELKNode extends ELK {
  constructor(options = {}) {
    var optionsClone = Object.assign({}, options);

    // If user explicitly requested a worker
    if (options.workerUrl) {
      var workerThreadsExist = false;
      try {
        require('worker_threads');
        workerThreadsExist = true;
      } catch (e) { }

      if (workerThreadsExist) {
        var NodeWorker = require('worker_threads').Worker;
        optionsClone.workerFactory = function(url) {
          var worker = new NodeWorker(url);
          // Adapt worker_threads API to Web Worker API for PromisedWorker
          // worker_threads uses .on('message', data) instead of .onmessage({data})
          worker.on('message', function(data) {
            if (typeof worker.onmessage === 'function') {
              worker.onmessage({ data: data });
            }
          });
          worker.on('error', function(err) {
            if (typeof worker.onerror === 'function') {
              worker.onerror(err);
            }
          });
          return worker;
        };
      } else {
        console.warn("Worker requested but 'worker_threads' is not available.\n"
          + "Pass your own 'workerFactory' to ELK's constructor.\n"
          + "... Falling back to non-worker version.");
      }
    }

    // If no workerFactory yet, try direct mode (native/WASM)
    if (!optionsClone.workerFactory && !optionsClone.workerUrl) {
      optionsClone.backend = loadBackend();
    } else if (!optionsClone.workerFactory) {
      // workerUrl provided but worker_threads unavailable: in-process fake worker
      var FakeWorker = require('./elk-worker.js').Worker;
      optionsClone.workerFactory = function(_url) { return new FakeWorker(); };
    }

    super(optionsClone);
  }
}

Object.defineProperty(module.exports, "__esModule", { value: true });
module.exports = ELKNode;
ELKNode.default = ELKNode;
