// elk-lean: memory limit of the WASM backend and recovery of a failed instance.
//
// A C exit() inside the WASM module (the Lean runtime's "INTERNAL PANIC: out of memory" when the
// 4 GB wasm32 memory is exhausted) ends that instance: the backend sets `failed` and throws, and
// js/load-wasm.js / js/elk-worker.js replace it with a new instance (plugins/org.eclipse.elk.js/
// README.md, "Limits"). The recovery logic is tested with a stub module in place of the emscripten
// build; the real thing (a 5,000-port node laid out like the native addon, a 10,000-port node that
// runs out of memory) needs ~4 GB and ~30 s and runs only with ELK_LEAN_TEST_LARGE_MEMORY=1.
// SPDX-License-Identifier: EPL-2.0 OR GPL-3.0-or-later
import { describe, it } from 'node:test';
import assert from 'node:assert/strict';
import { createRequire } from 'node:module';
import { fileURLToPath } from 'node:url';
import path from 'node:path';
import { cpSync, existsSync, mkdirSync, mkdtempSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { spawnSync } from 'node:child_process';

const require = createRequire(import.meta.url);
const __dirname = path.dirname(fileURLToPath(import.meta.url));
const { loadNativeAddon } = require('../js/load-native.js');

// Copies js/ (and dist/wasm-node/ with `withWasm`) into a fresh directory, so no native addon
// can be picked up, adds `files` ({ relativePath: contents }) and runs `script` there (`node -e`).
function runIsolated(prefix, files, script, timeout, withWasm = false) {
  const dir = mkdtempSync(path.join(tmpdir(), prefix));
  try {
    cpSync(path.join(__dirname, '../js'), path.join(dir, 'js'), { recursive: true });
    if (withWasm) cpSync(path.join(__dirname, '../dist/wasm-node'), path.join(dir, 'dist/wasm-node'), { recursive: true });
    for (const [rel, text] of Object.entries(files)) {
      mkdirSync(path.dirname(path.join(dir, rel)), { recursive: true });
      writeFileSync(path.join(dir, rel), text);
    }
    return spawnSync(process.execPath, ['-e', script], { cwd: dir, encoding: 'utf8', timeout });
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
}

// Stand-in for dist/wasm-node/elk_lean.cjs: every evaluation of the module is a new "instance";
// a graph with id "exit" fails the instance like the WASM build does after a C exit().
const STUB = `
globalThis.__stubInstances = (globalThis.__stubInstances || 0) + 1;
const instance = globalThis.__stubInstances;
exports.createBackend = function () {
  const backend = {
    failed: null,
    layout_json(graphJson) {
      if (backend.failed) throw new Error(backend.failed);
      const graph = JSON.parse(graphJson);
      if (graph.id === 'exit') {
        backend.failed = 'elk-lean: the WASM instance terminated (stub ' + instance + ')';
        throw new Error(backend.failed);
      }
      return JSON.stringify({ id: graph.id, instance });
    },
    known_layout_algorithms: () => '[]',
    known_layout_options: () => '[]',
    known_layout_categories: () => '[]',
  };
  return backend;
};`;

// one node with n ports, each connected to its own target node (orthogonal routing: O(n^2)
// segment dependencies)
function ports(n) {
  const g = { id: 'root', layoutOptions: { 'elk.algorithm': 'layered' }, children: [], edges: [] };
  const hub = { id: 'hub', width: 40, height: 40, ports: [] };
  g.children.push(hub);
  for (let i = 0; i < n; i++) {
    hub.ports.push({ id: 'p' + i, width: 4, height: 4 });
    g.children.push({ id: 't' + i, width: 20, height: 20 });
    g.edges.push({ id: 'e' + i, sources: ['p' + i], targets: ['t' + i] });
  }
  return g;
}

describe('WASM memory', () => {

  it('replaces a failed WASM instance in direct and worker mode', () => {
    const script = `
      const assert = require('node:assert/strict');
      const path = require('node:path');
      const ELK = require('./js/index.js');
      (async () => {
        // direct mode: the failed backend stays failed, a new ELK gets a new instance
        const direct = new ELK();
        assert.deepEqual(await direct.layout({ id: 'a' }), { id: 'a', instance: 1 });
        await assert.rejects(direct.layout({ id: 'exit' }), /terminated \\(stub 1\\)/);
        await assert.rejects(direct.layout({ id: 'b' }), /terminated \\(stub 1\\)/);
        assert.deepEqual(await new ELK().layout({ id: 'c' }), { id: 'c', instance: 2 });
        // worker mode: the worker answers the failing request and loads a new instance
        const worker = new ELK({ workerUrl: path.resolve('./js/elk-worker.js') });
        try {
          assert.deepEqual(await worker.layout({ id: 'a' }), { id: 'a', instance: 1 });
          // worker mode rejects with the elkjs error object { message }
          await assert.rejects(worker.layout({ id: 'exit' }), (e) => /terminated \\(stub 1\\)/.test(e.message));
          assert.deepEqual(await worker.layout({ id: 'b' }), { id: 'b', instance: 2 });
        } finally { worker.terminateWorker(); }
      })().catch((error) => { console.error(error); process.exitCode = 1; });
    `;
    const result = runIsolated('elk-lean-wasm-stub-', { 'dist/wasm-node/elk_lean.cjs': STUB }, script, 60000);
    assert.equal(result.error, undefined, result.stderr);
    assert.equal(result.status, 0, result.stderr);
  });

  const skip = !existsSync(path.join(__dirname, '../dist/wasm-node/elk_lean.cjs')) ? 'WASM backend not built (scripts/build_wasm.sh)'
    : process.env.ELK_LEAN_TEST_LARGE_MEMORY !== '1' ? 'needs ~4 GB: set ELK_LEAN_TEST_LARGE_MEMORY=1' : false;
  it('lays out a 5,000-port node and recovers from out of memory', { skip, timeout: 600000 }, () => {
    const native = loadNativeAddon();
    const reference = native ? native.layout_json(JSON.stringify(ports(5000)), '{}') : null;
    const files = { 'reference.json': JSON.stringify(reference) };
    // separate processes: an instance keeps its linear memory (up to 4 GB) until it is released
    const common = `
      const assert = require('node:assert/strict');
      const fs = require('node:fs');
      const path = require('node:path');
      const ELK = require('./js/index.js');
      const ports = ${ports.toString()};
      const reference = JSON.parse(fs.readFileSync('reference.json', 'utf8'));
      const workerUrl = path.resolve('./js/elk-worker.js');
      const small = { id: 'r', children: [{ id: 'a', width: 10, height: 10 }] };
      const terminated = /the WASM instance terminated .*out of memory/;
    `;
    const scripts = [
      // direct mode (needed more than emscripten's former 2 GB default maximum)
      `(async () => {
        const out = await new ELK().layout(ports(5000));
        assert.equal(out.children.length, 5001);
        if (reference !== null) assert.deepEqual(out, JSON.parse(reference));
      })()`,
      // worker mode, then a graph beyond 4 GB: the request fails, the worker recycles its instance
      `(async () => {
        const elk = new ELK({ workerUrl });
        try {
          const out = await elk.layout(ports(5000));
          if (reference !== null) assert.deepEqual(out, JSON.parse(reference));
          await assert.rejects(elk.layout(ports(10000)), (e) => terminated.test(e.message));
          assert.equal((await elk.layout(small)).children.length, 1);
        } finally { elk.terminateWorker(); }
        assert.equal(process.exitCode, undefined);
      })()`,
      // direct mode: the failed instance throws, a new ELK works, the process exit code is untouched
      `(async () => {
        const elk = new ELK();
        await assert.rejects(elk.layout(ports(10000)), terminated);
        await assert.rejects(elk.layout(small), terminated);
        assert.equal((await new ELK().layout(small)).children.length, 1);
        assert.equal(process.exitCode, undefined);
      })()`,
    ];
    for (const s of scripts) {
      const script = common + s + '.catch((error) => { console.error(error); process.exitCode = 1; });';
      const result = runIsolated('elk-lean-wasm-memory-', files, script, 300000, true);
      assert.equal(result.error, undefined, result.stderr);
      assert.equal(result.status, 0, result.stderr);
    }
  });

});
