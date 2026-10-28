/*
 * elk-lean WASM backend (org.eclipse.elk.wasm), emscripten `--post-js`.
 *
 * Runs inside the scope of the emscripten module (Node and browser builds alike) and wraps the
 * plain C API of plugins/org.eclipse.elk.ffi/include/elk_lean.h as the elk-rs WASM backend
 * interface (plugins/org.eclipse.elk.wasm/src/lib.rs of elk-rs):
 *
 *   var backend = Module.createBackend();   // initialises the Lean runtime once
 *   backend.layout_json(graphJson, optionsJson)  -> string   (throws Error(message))
 *   backend.known_layout_algorithms()            -> string   (JSON array)
 *   backend.known_layout_options()               -> string
 *   backend.known_layout_categories()            -> string
 *   backend.version                              -> "0.12.0"
 *
 * Calls are synchronous and must not overlap (single-threaded build; the layout engine keeps
 * process-wide registries). Layout errors reported by elk-lean are thrown as Error(message). A
 * JavaScript engine error raised inside the module (RangeError "Maximum call stack size exceeded"
 * for very deep recursion, a WebAssembly.RuntimeError) is rethrown unchanged after the wasm stack
 * pointer is restored; the instance stays usable, but objects of the aborted call are not freed.
 * A C exit() inside a call (Lean "INTERNAL PANIC", e.g. out of memory) ends the instance:
 * `backend.failed` holds the message, and that call and every later one throw Error(failed).
 *
 * SPDX-License-Identifier: EPL-2.0 OR GPL-3.0-or-later
 */
// Diagnostics (not part of the backend interface): current size of the wasm linear memory.
Module['wasmMemoryBytes'] = function () {
  return HEAPU8.length;
};

Module['createBackend'] = function () {
  if (Module['elkBackend']) return Module['elkBackend'];
  if (_elk_lean_init() !== 0) {
    throw new Error('elk-lean: initialisation of the Lean runtime failed');
  }
  var encoder = new TextEncoder();
  var decoder = new TextDecoder('utf-8');
  var flag = _malloc(4);

  function cString(s) {
    var bytes = encoder.encode(String(s));
    var ptr = _malloc(bytes.length + 1);
    if (ptr === 0) throw new Error('elk-lean: out of memory');
    HEAPU8.set(bytes, ptr);
    HEAPU8[ptr + bytes.length] = 0;
    return ptr;
  }

  function jsString(ptr) {
    var end = HEAPU8.indexOf(0, ptr);
    return decoder.decode(HEAPU8.subarray(ptr, end));
  }

  var hasProcess = typeof process === 'object' && process !== null && 'exitCode' in process;

  // Runs a call into the module; restores the wasm stack pointer when an engine error unwinds
  // through the wasm frames (their epilogues, which reset it, are skipped).
  // A C `exit()` inside the call (the Lean runtime's `lean_internal_panic`, e.g. "INTERNAL PANIC:
  // out of memory" when the 4 GB linear memory is exhausted) arrives as emscripten's ExitStatus,
  // which is not an Error and, in Node.js, has set `process.exitCode`: the exit code is restored,
  // the backend is marked failed (`backend.failed`, the call's objects are never freed and the
  // runtime state is unknown) and an Error is thrown; every later call throws it again.
  function guarded(call) {
    if (backend.failed) throw new Error(backend.failed);
    var sp = stackSave();
    var exitCode = hasProcess ? process.exitCode : undefined;
    try {
      return call();
    } catch (e) {
      stackRestore(sp);
      if (e instanceof ExitStatus) {
        if (hasProcess) process.exitCode = exitCode;
        backend.failed = 'elk-lean: the WASM instance terminated (' + e.message + '), most likely out of '
          + 'memory (' + Math.round(HEAPU8.length / 1048576) + ' MiB in use); create a new instance';
        throw new Error(backend.failed);
      }
      throw e;
    }
  }

  // Consumes a result of the elk_lean_* functions (malloc'd C string + is_error flag).
  function take(ptr) {
    if (ptr === 0) throw new Error('elk-lean: out of memory');
    var isError = HEAP32[flag >>> 2] !== 0;
    var s = jsString(ptr);
    _elk_lean_free(ptr);
    if (isError) throw new Error(s);
    return s;
  }

  var backend = {
    layout_json: function (graphJson, optionsJson) {
      if (backend.failed) throw new Error(backend.failed);
      var g = cString(graphJson);
      var o = cString(optionsJson == null ? '' : optionsJson);
      try {
        return take(guarded(function () { return _elk_lean_layout_json(g, o, flag); }));
      } finally {
        _free(o);
        _free(g);
      }
    },
    known_layout_algorithms: function () {
      return take(guarded(function () { return _elk_lean_known_layout_algorithms(flag); }));
    },
    known_layout_options: function () {
      return take(guarded(function () { return _elk_lean_known_layout_options(flag); }));
    },
    known_layout_categories: function () {
      return take(guarded(function () { return _elk_lean_known_layout_categories(flag); }));
    },
    version: jsString(_elk_lean_version()),
    // null, or the message of the ExitStatus that ended this instance (see `guarded`)
    failed: null,
  };
  Module['elkBackend'] = backend;
  return backend;
};
