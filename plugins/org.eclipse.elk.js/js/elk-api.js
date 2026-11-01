'use strict';

/**
 * ELK layout API — elkjs-compatible interface backed by elk-lean (native addon / WASM).
 * Port of elk-rs plugins/org.eclipse.elk.js/js/elk-api.js (itself modelled on elkjs
 * src/js/elk-api.js).
 *
 * Supports two modes:
 *  - Worker mode: workerUrl or workerFactory provided → delegates to a Web Worker / worker_threads
 *    running js/elk-worker.js (the layout request carries the graph as a JSON string)
 *  - Direct mode: neither provided → calls the backend synchronously and wraps in a Promise
 *
 * A backend is an object with functions returning JSON strings and throwing an Error
 * on failure: layout_json(graphJson, optionsJson), known_layout_algorithms(),
 * known_layout_options(), known_layout_categories(), and (elk-lean addition, needed by
 * convertElkt only) convert_elkt(elktText, flags).
 *
 * elk-lean addition: `threads` (constructor option, or per call in `layout(graph, { threads })`)
 * is passed to the backend as the third argument of layout_json: the cap of the parallel sibling
 * layout of the native addon (1 = sequential; omitted = the addon default, ELK_LEAN_THREADS or
 * min(hardware threads, 8)). The WASM backend ignores it (single-threaded). Results do not depend
 * on it.
 *
 * SPDX-License-Identifier: EPL-2.0 OR GPL-3.0-or-later
 */
/** elk-lean: validates the `threads` option (undefined/null = backend default). */
function checkThreads(threads) {
  if (threads === undefined || threads === null) return undefined;
  if (typeof threads !== 'number' || !Number.isInteger(threads) || threads < 1 || threads > 4096) {
    throw new TypeError("'threads' must be a positive integer, got " + threads);
  }
  return threads;
}

class ELK {

  constructor({
    defaultLayoutOptions = {},
    // Compatibility hint; the Lean engine registers every ported Java algorithm.
    algorithms = [
      'layered',
      'stress',
      'mrtree',
      'radial',
      'force',
      'disco',
      'sporeOverlap',
      'sporeCompaction',
      'rectpacking'
    ],
    workerFactory,
    workerUrl,
    // elk-lean direct mode: backend object with layout_json, known_layout_algorithms, etc.
    backend,
    // elk-lean: thread cap of the parallel sibling layout (native addon; undefined = its default)
    threads
  } = {}) {
    this.defaultLayoutOptions = defaultLayoutOptions;
    this.initialized = false;
    this.threads = checkThreads(threads);

    // Direct mode: backend provided, no worker
    if (backend && typeof workerUrl === 'undefined' && typeof workerFactory === 'undefined') {
      this.backend = backend;
      this.initialized = true;
      return;
    }

    // Worker mode (elkjs-compatible)
    if (typeof workerUrl === 'undefined' && typeof workerFactory === 'undefined') {
      throw new Error("Cannot construct an ELK without both 'workerUrl' and 'workerFactory'.");
    }
    let factory = workerFactory;
    if (typeof workerUrl !== 'undefined' && typeof workerFactory === 'undefined') {
      factory = function(url) { return new Worker(url); };
    }

    let worker = factory(workerUrl);
    if (typeof worker.postMessage !== 'function') {
      throw new TypeError("Created worker does not provide"
        + " the required 'postMessage' function.");
    }

    this.worker = new PromisedWorker(worker);

    // Register algorithms
    this.worker.postMessage({
      cmd: 'register',
      algorithms: algorithms
    })
      .then((r) => this.initialized = true)
      .catch((err) => {
        // terminateWorker() before the answer rejects the request; that is not an error
        if (!this.worker.terminated) console.error(err);
      });
  }

  layout(graph, {
    layoutOptions = this.defaultLayoutOptions,
    logging = false,
    measureExecutionTime = false,
    threads = this.threads,
  } = {}) {
    if (!graph) {
      return Promise.reject(new Error("Missing mandatory parameter 'graph'."));
    }
    try {
      threads = checkThreads(threads);
    } catch (err) {
      return Promise.reject(err);
    }

    // Direct mode
    if (this.backend) {
      try {
        const graphJson = JSON.stringify(graph);
        const optionsJson = JSON.stringify(layoutOptions || {});
        const resultJson = threads === undefined
          ? this.backend.layout_json(graphJson, optionsJson)
          : this.backend.layout_json(graphJson, optionsJson, threads);
        return Promise.resolve(resultJson).then(JSON.parse);
      } catch (err) {
        return Promise.reject(err);
      }
    }

    // Worker mode: graph and result travel as JSON strings. Structured cloning (postMessage of
    // the object) recurses per nesting level and fails at ~1000 compound levels on the default
    // V8 stack; JSON.stringify gets about three times as deep and JSON.parse is iterative.
    let graphJson;
    let optionsJson;
    try {
      graphJson = JSON.stringify(graph);
      optionsJson = JSON.stringify(layoutOptions || {});
    } catch (err) {
      return Promise.reject(err);
    }
    return this.worker.postMessage({
      cmd: 'layout',
      graphJson: graphJson,
      optionsJson: optionsJson,
      threads: threads,
      options: {
        logging: logging,
        measureExecutionTime: measureExecutionTime,
      }
    }).then((result) => typeof result === 'string' ? JSON.parse(result) : result);
  }

  /**
   * elk-lean addition: parses ELK Text (`.elkt`) and resolves to the ElkGraph JSON object, the
   * same graph as `elk convert` (Lean `Elk.Text.parseElkt` + JSON exporter). `defaults: true`
   * gives shapes without a size the elk-live default sizes (`elk convert --defaults`: nodes 30,
   * ports 5, labels 9 x length by 16). A syntax or linking error rejects with
   * `Error('ELK Text parse error: <line>:<col>: <message>')`.
   */
  convertElkt(elkt, { defaults = false } = {}) {
    if (typeof elkt !== 'string') {
      return Promise.reject(new TypeError("'elkt' must be a string"));
    }
    const flags = defaults ? ELK.CONVERT_DEFAULTS : 0;
    if (this.backend) {
      try {
        if (typeof this.backend.convert_elkt !== 'function') {
          throw new Error('elk-lean: the loaded backend has no convert_elkt (rebuild the addon / WASM)');
        }
        return Promise.resolve(this.backend.convert_elkt(elkt, flags)).then(JSON.parse);
      } catch (err) {
        return Promise.reject(err);
      }
    }
    return this.worker.postMessage({ cmd: 'convertElkt', elkt: elkt, flags: flags })
      .then((result) => typeof result === 'string' ? JSON.parse(result) : result);
  }

  knownLayoutAlgorithms() {
    if (this.backend) {
      try {
        return Promise.resolve(this.backend.known_layout_algorithms()).then(JSON.parse);
      } catch (err) {
        return Promise.reject(err);
      }
    }
    return this.worker.postMessage({ cmd: 'algorithms' });
  }

  knownLayoutOptions() {
    if (this.backend) {
      try {
        return Promise.resolve(this.backend.known_layout_options()).then(JSON.parse);
      } catch (err) {
        return Promise.reject(err);
      }
    }
    return this.worker.postMessage({ cmd: 'options' });
  }

  knownLayoutCategories() {
    if (this.backend) {
      try {
        return Promise.resolve(this.backend.known_layout_categories()).then(JSON.parse);
      } catch (err) {
        return Promise.reject(err);
      }
    }
    return this.worker.postMessage({ cmd: 'categories' });
  }

  terminateWorker() {
    if (this.worker) {
      this.worker.terminate();
    }
  }

}

/** `elk_lean.h` ELK_LEAN_CONVERT_* flag bits of the backends' convert_elkt(elktText, flags). */
ELK.CONVERT_DEFAULTS = 1;
ELK.CONVERT_PRETTY = 2;
ELK.CONVERT_SORT_KEYS = 4;

class PromisedWorker {

  constructor(worker) {
    if (worker === undefined) {
      throw new Error("Missing mandatory parameter 'worker'.");
    }
    this.resolvers = {};
    this.worker = worker;
    this.worker.onmessage = (answer) => {
      setTimeout(() => {
        this.receive(this, answer);
      }, 0);
    };
    // A worker that fails outside a command (script/backend load error, Web Worker `error`
    // event, worker_threads `error`/`exit`) rejects the pending requests instead of leaving them
    // unsettled.
    this.worker.onerror = (err) => {
      setTimeout(() => {
        this.rejectAll(err);
      }, 0);
    };
  }

  rejectAll(err) {
    const error = err instanceof Error ? err
      : new Error(err && err.message ? err.message : 'elk-lean: layout worker failed');
    const pending = this.resolvers;
    this.resolvers = {};
    for (const id of Object.keys(pending)) {
      pending[id](error);
    }
  }

  postMessage(msg) {
    let id = this.id || 0;
    this.id = id + 1;
    msg.id = id;
    let self = this;
    return new Promise(function(resolve, reject) {
      self.resolvers[id] = function(err, res) {
        if (err) {
          reject(err);
        } else {
          resolve(res);
        }
      };
      self.worker.postMessage(msg);
    });
  }

  receive(self, answer) {
    let json = answer.data;
    let resolver = self.resolvers[json.id];
    if (resolver) {
      delete self.resolvers[json.id];
      if (json.error) {
        resolver(json.error);
      } else {
        resolver(null, json.data);
      }
    }
  }

  terminate() {
    if (this.worker) {
      this.terminated = true;
      this.worker.terminate();
    }
  }

}

// Support both CJS and ESM
if (typeof module !== 'undefined' && module.exports) {
  module.exports = ELK;
  module.exports.default = ELK;
}
if (typeof exports !== 'undefined') {
  exports.default = ELK;
}
