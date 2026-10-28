// elk-lean: deep recursion in the Lean-generated code vs. the stack of the calling thread, and the
// Worker mode with a larger stack (`workerStackSizeMb`, js/index.js).
//
// The deep input is an mrtree chain: `Elk.Alg.MrTree.P4Route.EdgeRouter.sortByFloat` folds the
// nodes with an unspecialised `Array.foldl` (Id monad), about five wasm frames per node. The WASM
// backend overflows the default V8 stack (~1 MB) at ~1,500-2,000 nodes, a 64 MB worker stack takes
// more than 32,000 nodes (plugins/org.eclipse.elk.js/README.md, "Limits").
// SPDX-License-Identifier: EPL-2.0 OR GPL-3.0-or-later
import { describe, it } from 'node:test';
import assert from 'node:assert/strict';
import { createRequire } from 'node:module';
import { fileURLToPath } from 'node:url';
import path from 'node:path';
import { cpSync, existsSync, mkdtempSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { spawnSync } from 'node:child_process';

const require = createRequire(import.meta.url);
const __dirname = path.dirname(fileURLToPath(import.meta.url));
const ELK = require('../js/index.js');
const { loadNativeAddon } = require('../js/load-native.js');
const workerUrl = path.join(__dirname, '../js/elk-worker.js');

// 8,000 nodes: 4x above the plain-WASM limit, 4x below the limit of the default worker stack
const DEEP = 8000;
function mrtreeChain(n) {
  const children = [];
  const edges = [];
  for (let i = 0; i < n; i++) {
    children.push({ id: 'n' + i, width: 20, height: 20 });
    if (i > 0) edges.push({ id: 'e' + i, sources: ['n' + (i - 1)], targets: ['n' + i] });
  }
  return { id: 'root', layoutOptions: { 'elk.algorithm': 'mrtree' }, children, edges };
}
const small = { id: 'root', children: [{ id: 'a', width: 10, height: 10 }, { id: 'b', width: 10, height: 10 }],
  edges: [{ id: 'e', sources: ['a'], targets: ['b'] }] };

describe('Deep recursion', () => {

  describe('workerStackSizeMb', () => {
    it('defaults to 64 MB', () => {
      assert.equal(ELK.DEFAULT_WORKER_STACK_SIZE_MB, 64);
    });

    it('rejects values that are not positive numbers', () => {
      for (const v of [0, -1, '64', NaN, Infinity]) {
        assert.throws(() => new ELK({ workerUrl, workerStackSizeMb: v }), TypeError, String(v));
      }
    });

    it('rejects pending requests when the worker exits', async () => {
      const dir = mkdtempSync(path.join(tmpdir(), 'elk-lean-exit-'));
      const script = path.join(dir, 'exit-worker.js');
      writeFileSync(script, `const { parentPort } = require('node:worker_threads');
        parentPort.on('message', (m) => m.cmd === 'layout' ? process.exit(3) : parentPort.postMessage({ id: m.id, data: null }));`);
      const elk = new ELK({ workerUrl: script });
      try {
        await assert.rejects(elk.layout(small), /layout worker exited \(code 3\)/);
      } finally {
        elk.terminateWorker();
        rmSync(dir, { recursive: true, force: true });
      }
    });
  });

  describe('native addon', { skip: loadNativeAddon() ? false : 'native addon not built' }, () => {
    it('lays out the deep chain in direct and worker mode alike', async () => {
      const direct = await new ELK().layout(mrtreeChain(DEEP));
      const elk = new ELK({ workerUrl });
      try {
        assert.deepEqual(await elk.layout(mrtreeChain(DEEP)), direct);
      } finally {
        elk.terminateWorker();
      }
    });
  });

  describe('WASM backend (no native addon)', () => {
    const wasmNode = path.join(__dirname, '../dist/wasm-node/elk_lean.cjs');
    const built = existsSync(wasmNode);
    it('overflows the default stack in direct mode and passes in worker mode', { skip: built ? false : 'WASM backend not built (scripts/build_wasm.sh)' }, () => {
      // only the JS and the WASM build are copied, so no native addon can be picked up
      const isolated = mkdtempSync(path.join(tmpdir(), 'elk-lean-wasm-deep-'));
      try {
        cpSync(path.join(__dirname, '../js'), path.join(isolated, 'js'), { recursive: true });
        cpSync(path.join(__dirname, '../dist/wasm-node'), path.join(isolated, 'dist/wasm-node'), { recursive: true });
        const native = loadNativeAddon();
        const reference = native ? native.layout_json(JSON.stringify(mrtreeChain(DEEP)), '{}') : null;
        writeFileSync(path.join(isolated, 'reference.json'), JSON.stringify(reference));
        const script = `
          const assert = require('node:assert/strict');
          const fs = require('node:fs');
          const path = require('node:path');
          const ELK = require('./js/index.js');
          const graph = ${mrtreeChain.toString()}(${DEEP});
          const small = ${JSON.stringify(small)};
          const reference = JSON.parse(fs.readFileSync('reference.json', 'utf8'));
          const overflow = /Maximum call stack size exceeded/;
          const workerUrl = path.resolve('./js/elk-worker.js');
          (async () => {
            // direct mode: RangeError on the ~1 MB main-thread stack; the instance stays usable
            const direct = new ELK();
            await assert.rejects(direct.layout(graph), (err) => err instanceof RangeError && overflow.test(err.message));
            assert.equal((await direct.layout(small)).children.length, 2);
            // worker mode, default stack (64 MB): same result as the native addon
            const worker = new ELK({ workerUrl });
            try {
              const out = await worker.layout(graph);
              assert.equal(out.children.length, graph.children.length);
              if (reference !== null) assert.deepEqual(out, JSON.parse(reference));
            } finally { worker.terminateWorker(); }
            // worker mode with a 1 MB stack overflows like the main thread
            const tiny = new ELK({ workerUrl, workerStackSizeMb: 1 });
            try {
              await assert.rejects(tiny.layout(graph), (err) => overflow.test(err.message));
              assert.equal((await tiny.layout(small)).children.length, 2);
            } finally { tiny.terminateWorker(); }
          })().catch((error) => { console.error(error); process.exitCode = 1; });
        `;
        const result = spawnSync(process.execPath, ['-e', script], { cwd: isolated, encoding: 'utf8', timeout: 120000 });
        assert.equal(result.error, undefined, result.stderr);
        assert.equal(result.status, 0, result.stderr);
      } finally {
        rmSync(isolated, { recursive: true, force: true });
      }
    });
  });

});
