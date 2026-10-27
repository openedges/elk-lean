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
import { cpSync, mkdtempSync, readFileSync, rmSync } from 'node:fs';
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
        assert.equal(pkg.name, 'elk-lean-' + triple);
        assert.equal(pkg.main, 'elk-lean.' + triple + '.node');
      }
      const main = JSON.parse(readFileSync(path.join(__dirname, '../package.json'), 'utf8'));
      assert.deepEqual(Object.keys(main.optionalDependencies).sort(),
        triples.map(t => 'elk-lean-' + t).sort());
    });

    it('should try platform package before local .node and WASM', () => {
      // elk-lean-<triple> package -> platform .node -> generic .node -> WASM
      const pkgIdx = loaderSrc.indexOf("'elk-lean-'");
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
    // TODO(Phase 8, WASM): once plugins/org.eclipse.elk.wasm exists, copy dist/wasm* as in
    // elk-rs testEntryPoints and require successful layouts in all three modes.
    it('reports the missing WASM backend in direct, fake-worker, and worker_threads modes', () => {
      // Copy only the JS outside the repo so no optional native package or local .node file
      // can satisfy the loader accidentally.
      const isolated = mkdtempSync(path.join(tmpdir(), 'elk-lean-wasm-fallback-'));
      try {
        cpSync(path.join(__dirname, '../js'), path.join(isolated, 'js'), { recursive: true });
        const script = `
          const assert = require('node:assert/strict');
          const ELK = require('./js/index.js');
          const API = require('./js/elk-api.js');
          const FakeWorker = require('./js/elk-worker.js').Worker;
          const path = require('node:path');
          const graph = ${JSON.stringify(graph)};
          const notBuilt = /WASM backend not built/;
          (async () => {
            assert.throws(() => new ELK(), notBuilt);
            for (const elk of [new API({ workerFactory: () => new FakeWorker() }),
              new ELK({ workerUrl: path.resolve('./js/elk-worker.js') })]) {
              try {
                await assert.rejects(elk.layout(graph), err => notBuilt.test(err.message));
              } finally { elk.terminateWorker(); }
            }
          })().catch(error => { console.error(error); process.exitCode = 1; });
        `;
        const result = spawnSync(process.execPath, ['-e', script], {
          cwd: isolated, encoding: 'utf8', timeout: 20000,
        });
        assert.equal(result.error, undefined, result.stderr);
        assert.equal(result.status, 0, result.stderr);
      } finally {
        rmSync(isolated, { recursive: true, force: true });
      }
    });
  });

});
