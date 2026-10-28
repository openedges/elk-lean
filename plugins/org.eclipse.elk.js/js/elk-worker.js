'use strict';

/**
 * elk-lean worker script (port of elk-rs plugins/org.eclipse.elk.js/js/elk-worker.js) —
 * runs in a Web Worker or in Node.js worker_threads.
 *
 * Loads a backend (native addon in Node.js, WASM otherwise) and handles the elkjs-compatible
 * message protocol. Also exports a `Worker` class for in-process use (like elkjs's fake worker).
 *
 * SPDX-License-Identifier: EPL-2.0 OR GPL-3.0-or-later
 */

// Detect environment
var isWebWorker = typeof self !== 'undefined' && typeof self.postMessage === 'function' && typeof window === 'undefined';
var isNode = typeof process !== 'undefined' && process.versions != null && process.versions.node != null;

/** Node.js backend: native addon, then the WASM fallback; throws when neither loads. */
function loadNodeBackend() {
  var errors = [];
  var backend = require('./load-native.js').loadNativeAddon(errors);
  if (backend) return backend;
  try {
    return require('./load-wasm.js')();
  } catch (e) {
    errors.push('./load-wasm.js: ' + (e && e.message ? e.message : e));
  }
  throw new Error('elk-lean: Could not load native addon or WASM module.\n  ' + errors.join('\n  '));
}

// --- In-process (fake) Worker for Node.js direct use ---

function FakeWorker() {
  this._backend = null;
  this._initPromise = null;
}

FakeWorker.prototype._ensureBackend = function() {
  if (this._backend) return Promise.resolve(this._backend);
  if (this._initPromise) return this._initPromise;

  var self = this;
  this._initPromise = new Promise(function(resolve, reject) {
    try {
      self._backend = loadNodeBackend();
      resolve(self._backend);
    } catch (err) {
      reject(err);
    }
  });
  return this._initPromise;
};

FakeWorker.prototype.postMessage = function(msg) {
  var self = this;
  setTimeout(function() {
    self._ensureBackend().then(function(backend) {
      self._handleMessage(backend, msg);
    }).catch(function(err) {
      if (self.onmessage) {
        self.onmessage({ data: { id: msg.id, error: convertError(err) } });
      }
    });
  }, 0);
};

FakeWorker.prototype._handleMessage = function(backend, msg) {
  var result;
  try {
    result = handleCommand(backend, msg);
    if (this.onmessage) {
      this.onmessage({ data: { id: msg.id, data: result } });
    }
  } catch (err) {
    // a failed WASM instance is replaced before the next message (see `failed` below)
    if (failed(backend)) {
      this._backend = null;
      this._initPromise = null;
    }
    if (this.onmessage) {
      this.onmessage({ data: { id: msg.id, error: convertError(err) } });
    }
  }
};

FakeWorker.prototype.terminate = function() {
  // Nothing to clean up for in-process worker
};

// --- Command handling (shared between Web Worker and FakeWorker) ---

function handleCommand(backend, msg) {
  switch (msg.cmd) {
    case 'register':
      // All algorithms are built-in; nothing to register
      return null;

    case 'layout': {
      // elk-api.js sends JSON strings (graphJson/optionsJson) and gets the result string back;
      // an elkjs-style request with graph/layoutOptions objects is answered with an object.
      if (typeof msg.graphJson === 'string') {
        return backend.layout_json(msg.graphJson,
          typeof msg.optionsJson === 'string' ? msg.optionsJson : '{}');
      }
      var graphJson = JSON.stringify(msg.graph);
      var optionsJson = JSON.stringify(msg.layoutOptions || {});
      var resultJson = backend.layout_json(graphJson, optionsJson);
      return JSON.parse(resultJson);
    }

    case 'algorithms':
      return JSON.parse(backend.known_layout_algorithms());

    case 'options':
      return JSON.parse(backend.known_layout_options());

    case 'categories':
      return JSON.parse(backend.known_layout_categories());

    default:
      throw new Error('Unknown command: ' + msg.cmd);
  }
}

/**
 * True when `backend` is a WASM instance that has ended with a C exit (`backend.failed`, set by
 * the WASM build, e.g. after Lean's out-of-memory panic): its memory is lost and every later call
 * fails, so the worker loads a new instance for the next request.
 */
function failed(backend) {
  return !!(backend && backend.failed);
}

function convertError(err) {
  if (err instanceof Error) {
    return { message: err.message };
  }
  if (typeof err === 'string') {
    return { message: err };
  }
  return { message: String(err) };
}

// --- Worker mode ---

// Detect Node.js worker_threads (parentPort is available when running as a worker thread)
var _parentPort = null;
if (isNode) {
  try {
    var _wt = require('worker_threads');
    if (!_wt.isMainThread && _wt.parentPort) {
      _parentPort = _wt.parentPort;
    }
  } catch (e) { /* not a worker thread */ }
}

if (_parentPort) {
  // Node.js worker_threads — native addon (or WASM) loaded in this thread
  var nodeBackend = null;
  var nodeBackendError = null;
  try {
    nodeBackend = loadNodeBackend();
  } catch (e) {
    nodeBackendError = e;
  }

  _parentPort.on('message', function(msg) {
    if (!nodeBackend) {
      _parentPort.postMessage({ id: msg.id, error: { message: 'elk-lean: Could not load backend in worker. '
        + (nodeBackendError && nodeBackendError.message ? nodeBackendError.message : '') } });
      return;
    }
    try {
      var result = handleCommand(nodeBackend, msg);
      _parentPort.postMessage({ id: msg.id, data: result });
    } catch (err) {
      _parentPort.postMessage({ id: msg.id, error: convertError(err) });
      if (failed(nodeBackend)) {
        // js/load-wasm.js evaluates the WASM module again for a failed instance
        try {
          nodeBackend = loadNodeBackend();
        } catch (e) {
          nodeBackend = null;
          nodeBackendError = e;
        }
      }
    }
  });
} else if (isWebWorker && !isNode) {
  // Pure browser Web Worker — WASM via dynamic import
  var loadBrowserBackend = function() {
    return import('./load-wasm.browser.mjs').then(function(loader) {
      return loader.default();
    });
  };
  var wasmReady = loadBrowserBackend();

  self.onmessage = function(e) {
    var msg = e.data;
    wasmReady.then(function(backend) {
      try {
        var result = handleCommand(backend, msg);
        self.postMessage({ id: msg.id, data: result });
      } catch (err) {
        self.postMessage({ id: msg.id, error: convertError(err) });
        // js/load-wasm.browser.mjs creates a new instance for a failed one
        if (failed(backend)) wasmReady = loadBrowserBackend();
      }
    }).catch(function(err) {
      self.postMessage({ id: msg.id, error: convertError(err) });
    });
  };
}

// --- Exports ---

if (typeof module !== 'undefined' && module.exports) {
  module.exports.Worker = FakeWorker;
}
