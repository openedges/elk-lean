/*******************************************************************************
 * Ported from elkjs via elk-rs — Copyright (c) 2021 Kiel University and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0, https://www.eclipse.org/legal/epl-2.0.
 * This Source Code may also be made available under the following Secondary
 * Licenses when the conditions for such availability set forth in the Eclipse
 * Public License v. 2.0 are satisfied: GPL-3.0, https://www.gnu.org/licenses/gpl-3.0-standalone.html.
 * SPDX-License-Identifier: EPL-2.0 OR GPL-3.0-or-later
 *******************************************************************************/
import { describe, it } from 'node:test';
import assert from 'node:assert/strict';
import { createRequire } from 'node:module';
import { fileURLToPath } from 'node:url';
import path from 'node:path';
import { cpSync, existsSync, mkdtempSync, readFileSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { spawnSync } from 'node:child_process';

const require = createRequire(import.meta.url);
const __dirname = path.dirname(fileURLToPath(import.meta.url));

const graph = {
  id: "root",
  properties: { 'algorithm': 'layered' },
  children: [
    { id: "n1", width: 30, height: 30 },
    { id: "n2", width: 30, height: 30 },
    { id: "n3", width: 30, height: 30 }
  ],
  edges: [
    { id: "e1", sources: [ "n1" ], targets: [ "n2" ] },
    { id: "e2", sources: [ "n1" ], targets: [ "n3" ] }
  ]
};

function checkLayout(output) {
  assert.equal(output.children.length, 3);
  assert.ok(output.children.every(node => Number.isFinite(node.x) && Number.isFinite(node.y)));
}

describe('Entry point', () => {

  describe('main entry point (direct mode)', () => {
    const ELK = require('../js/index.js');
    const elk = new ELK();

    it('should succeed.', async () => {
      checkLayout(await elk.layout(graph));
    });
  });

  describe('elk-api with fake worker', () => {
    const ELK = require('../js/elk-api.js');
    const elk = new ELK({
      workerFactory: function (_) {
        const { Worker } = require('../js/elk-worker.js');
        return new Worker();
      }
    });

    it('should succeed.', async () => {
      checkLayout(await elk.layout(graph));
    });
  });

  describe('in worker_threads', () => {
    const ELK = require('../js/index.js');

    it('should succeed.', async () => {
      const elk = new ELK({
        workerUrl: path.join(__dirname, '../js/elk-worker.js')
      });
      try {
        checkLayout(await elk.layout(graph));
      } finally {
        elk.terminateWorker();
      }
    });

    it('should report engine errors as rejections.', async () => {
      const elk = new ELK({
        workerUrl: path.join(__dirname, '../js/elk-worker.js')
      });
      try {
        await assert.rejects(elk.layout({ id: 'root', layoutOptions: { algorithm: 'foo.bar.baz' },
          children: [{ id: 'n1' }] }),
          err => /UnsupportedConfigurationException/.test(err.message));
      } finally {
        elk.terminateWorker();
      }
    });
  });

  describe('platform package mapping', () => {
    // Test that platformTriple() returns the correct triple
    // by reading the source and checking the mapping table
    const loaderSrc = readFileSync(path.join(__dirname, '../js/load-native.js'), 'utf8');
    const indexSrc = readFileSync(path.join(__dirname, '../js/index.js'), 'utf8');

    it('should define triples for all supported platforms', () => {
      const triples = [
        'darwin-arm64',
        'darwin-x64',
        'linux-x64-gnu',
        'linux-x64-musl',
        'linux-arm64-gnu',
        'win32-x64-msvc',
      ];
      for (const triple of triples) {
        assert.ok(loaderSrc.includes("'" + triple + "'"), triple);
        const pkg = JSON.parse(readFileSync(path.join(__dirname, '../npm', triple, 'package.json'), 'utf8'));
        assert.equal(pkg.name, '@openedges/elk-lean-' + triple);
        assert.equal(pkg.main, 'elk-lean.' + triple + '.node');
      }
      // the main package lists the platforms release.yml builds; linux-x64-musl and win32-x64-msvc
      // stay templates until a Lean toolchain / a Windows addon build exists for them
      const main = JSON.parse(readFileSync(path.join(__dirname, '../package.json'), 'utf8'));
      assert.deepEqual(Object.keys(main.optionalDependencies).sort(),
        ['darwin-arm64', 'darwin-x64', 'linux-arm64-gnu', 'linux-x64-gnu'].map(t => '@openedges/elk-lean-' + t));
      for (const name of Object.keys(main.optionalDependencies)) {
        assert.ok(triples.includes(name.replace('@openedges/elk-lean-', '')), name);
        assert.equal(main.optionalDependencies[name], main.version);
      }
    });

    it('should try platform package before local .node and WASM', () => {
      // elk-lean-<triple> package -> platform .node -> generic .node -> WASM
      const pkgIdx = loaderSrc.indexOf("'@openedges/elk-lean-'");
      const platformLocalIdx = loaderSrc.indexOf("'../dist/elk-lean.'");
      const genericLocalIdx = loaderSrc.indexOf("'../dist/elk-lean.node'");
      assert.ok(pkgIdx >= 0 && pkgIdx < platformLocalIdx);
      assert.ok(platformLocalIdx < genericLocalIdx);
      assert.ok(indexSrc.indexOf('native.loadNativeAddon(') < indexSrc.indexOf("require('./load-wasm.js')"));
    });

    it('should resolve the running platform', () => {
      const { platformTriple } = require('../js/load-native.js');
      if (process.platform === 'darwin' && process.arch === 'arm64') {
        assert.equal(platformTriple(), 'darwin-arm64');
      } else {
        assert.equal(typeof platformTriple(), 'string');
      }
    });
  });

  describe('WASM fallback when no NAPI binary', () => {
    // Only the JS (and the WASM build, when present) is copied outside the repo, so no optional
    // native package or local .node file can satisfy the loader accidentally.
    const wasmNode = path.join(__dirname, '../dist/wasm-node/elk_lean.cjs');
    const built = existsSync(wasmNode);
    it(built ? 'lays out through WASM in direct, fake-worker and worker_threads modes'
             : 'reports the missing WASM backend in direct, fake-worker, and worker_threads modes', () => {
      const isolated = mkdtempSync(path.join(tmpdir(), 'elk-lean-wasm-fallback-'));
      try {
        cpSync(path.join(__dirname, '../js'), path.join(isolated, 'js'), { recursive: true });
        if (built) {
          cpSync(path.join(__dirname, '../dist/wasm-node'), path.join(isolated, 'dist/wasm-node'), { recursive: true });
        }
        // reference output: the native addon of this checkout when it is built, else structural checks
        let reference = null;
        try {
          const native = require('./../js/load-native.js')();
          reference = JSON.parse(native.layout_json(JSON.stringify(graph), '{}'));
        } catch (e) { reference = null; }
        const script = `
          const assert = require('node:assert/strict');
          const ELK = require('./js/index.js');
          const API = require('./js/elk-api.js');
          const FakeWorker = require('./js/elk-worker.js').Worker;
          const path = require('node:path');
          const graph = ${JSON.stringify(graph)};
          const reference = ${JSON.stringify(reference)};
          const built = ${built};
          const notBuilt = /WASM backend not built/;
          // convertElkt through the WASM backend (elk-lean addition)
          const elkt = 'node n1\\nnode n2\\nedge n1 -> n2\\n';
          const checkConvert = (g) => {
            assert.deepEqual(g.children.map(c => [c.id, c.width, c.height]), [['n1', 30, 30], ['n2', 30, 30]]);
            assert.deepEqual(g.edges.map(e => [e.sources, e.targets]), [[['n1'], ['n2']]]);
          };
          const checkResult = (out) => {
            assert.ok(Array.isArray(out.children) && out.children.length === graph.children.length);
            for (const c of out.children) { assert.equal(typeof c.x, 'number'); assert.equal(typeof c.y, 'number'); }
            if (reference) assert.deepEqual(out, reference);
          };
          (async () => {
            if (!built) {
              assert.throws(() => new ELK(), notBuilt);
            } else {
              const direct = new ELK();
              checkResult(await direct.layout(JSON.parse(JSON.stringify(graph))));
              assert.ok((await direct.knownLayoutAlgorithms()).some(a => a.id === 'org.eclipse.elk.layered'));
              checkConvert(await direct.convertElkt(elkt, { defaults: true }));
              await assert.rejects(direct.convertElkt('node a\\nedge a -> \\n'), err => /^ELK Text parse error: 3:1: /.test(err.message));
            }
            for (const elk of [new API({ workerFactory: () => new FakeWorker() }),
              new ELK({ workerUrl: path.resolve('./js/elk-worker.js') })]) {
              try {
                if (!built) {
                  await assert.rejects(elk.layout(graph), err => notBuilt.test(err.message));
                } else {
                  checkResult(await elk.layout(JSON.parse(JSON.stringify(graph))));
                  checkConvert(await elk.convertElkt(elkt, { defaults: true }));
                }
              } finally { elk.terminateWorker(); }
            }
          })().catch(error => { console.error(error); process.exitCode = 1; });
        `;
        const result = spawnSync(process.execPath, ['-e', script], {
          cwd: isolated, encoding: 'utf8', timeout: 60000,
        });
        assert.equal(result.error, undefined, result.stderr);
        assert.equal(result.status, 0, result.stderr);
      } finally {
        rmSync(isolated, { recursive: true, force: true });
      }
    });
  });

});
