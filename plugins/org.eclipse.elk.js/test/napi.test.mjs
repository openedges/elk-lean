// elk-lean NAPI addon (plugins/org.eclipse.elk.napi/src/elk_napi.c): exports, error mapping
// and worker_threads use (per-thread Lean registration, process-wide serialisation).
// SPDX-License-Identifier: EPL-2.0 OR GPL-3.0-or-later
import { describe, it } from 'node:test';
import assert from 'node:assert/strict';
import { createRequire } from 'node:module';
import { Worker } from 'node:worker_threads';
import { readFileSync } from 'node:fs';

const require = createRequire(import.meta.url);
const { loadNativeAddon } = require('../js/load-native.js');
const addon = loadNativeAddon();

function chain(n) {
  const children = [];
  const edges = [];
  for (let i = 0; i < n; i++) {
    children.push({ id: 'n' + i, width: 20 + (i % 7), height: 10 + (i % 5) });
    if (i > 0) edges.push({ id: 'e' + i, sources: ['n' + (i - 1)], targets: ['n' + i] });
    if (i > 2 && i % 3 === 0) edges.push({ id: 'x' + i, sources: ['n' + (i - 3)], targets: ['n' + i] });
  }
  return { id: 'root', children, edges };
}

const graphs = [
  JSON.stringify(chain(40)),
  JSON.stringify({ ...chain(25), layoutOptions: { 'elk.algorithm': 'mrtree' } }),
  JSON.stringify({ ...chain(25), layoutOptions: { 'elk.algorithm': 'stress' } }),
  readFileSync(new URL('./fixtures/node_flexibility/recompute_inherited.json', import.meta.url), 'utf8'),
];

describe('NAPI addon', { skip: addon ? false : 'native addon not built (sh scripts/build_napi.sh)' }, () => {
  it('exports the elk-rs functions', () => {
    for (const name of ['layout_json', 'known_layout_algorithms', 'known_layout_options', 'known_layout_categories']) {
      assert.equal(typeof addon[name], 'function', name);
    }
    assert.equal(addon.version, '0.12.0');
  });

  it('returns compact JSON with sorted keys', () => {
    const out = addon.layout_json(graphs[0], '{}');
    assert.equal(typeof out, 'string');
    const parsed = JSON.parse(out);
    assert.equal(JSON.stringify(parsed), out);
    assert.deepEqual(Object.keys(parsed), Object.keys(parsed).slice().sort());
  });

  it('applies the options argument as global defaults', () => {
    const g = JSON.stringify({ id: 'root', children: [{ id: 'a', width: 10, height: 10 }, { id: 'b', width: 10, height: 10 }],
      edges: [{ id: 'e', sources: ['a'], targets: ['b'] }] });
    const a = JSON.parse(addon.layout_json(g, JSON.stringify({ 'elk.layered.spacing.nodeNodeBetweenLayers': 50 })));
    assert.equal(a.children[1].x - a.children[0].x, 60);
    // options may be omitted or empty
    assert.equal(addon.layout_json(g, ''), addon.layout_json(g));
  });

  it('returns metadata arrays', () => {
    const algorithms = JSON.parse(addon.known_layout_algorithms());
    const options = JSON.parse(addon.known_layout_options());
    const categories = JSON.parse(addon.known_layout_categories());
    assert.ok(algorithms.length >= 10);
    assert.ok(algorithms.some(a => a.id === 'org.eclipse.elk.layered'));
    assert.ok(options.length > 100);
    assert.ok(categories.length > 0);
  });

  it('throws engine errors as Error(message)', () => {
    assert.throws(() => addon.layout_json('{"id":"r","layoutOptions":{"elk.algorithm":"nope"},"children":[{"id":"a"}]}', '{}'),
      err => err instanceof Error && /^org\.eclipse\.elk\.core\.UnsupportedConfigurationException: /.test(err.message));
    assert.throws(() => addon.layout_json('{not json', '{}'), Error);
    assert.throws(() => addon.layout_json('{"id":"r"}', '{bad'), Error);
  });

  it('rejects non-string arguments with a TypeError', () => {
    assert.throws(() => addon.layout_json(), TypeError);
    assert.throws(() => addon.layout_json({ id: 'r' }, '{}'), TypeError);
    assert.throws(() => addon.layout_json('{"id":"r"}', {}), TypeError);
  });

  it('gives identical results from concurrent worker_threads', async () => {
    const expected = graphs.map(g => addon.layout_json(g, '{}'));
    const addonPath = require.resolve('../js/load-native.js');
    const code = `
      const { parentPort, workerData } = require('node:worker_threads');
      const addon = require(workerData.loader).loadNativeAddon();
      const out = [];
      for (let r = 0; r < workerData.rounds; r++) {
        for (const g of workerData.graphs) out.push(addon.layout_json(g, '{}'));
      }
      out.push(addon.known_layout_algorithms());
      parentPort.postMessage(out);
    `;
    const run = () => new Promise((resolve, reject) => {
      const w = new Worker(code, { eval: true, workerData: { loader: addonPath, graphs, rounds: 3 } });
      w.once('message', resolve);
      w.once('error', reject);
    });
    // two waves: the second one reuses the runtime after the first threads finalised
    for (let wave = 0; wave < 2; wave++) {
      const results = await Promise.all([run(), run(), run(), run()]);
      for (const out of results) {
        const algorithms = out.pop();
        assert.equal(algorithms, addon.known_layout_algorithms());
        out.forEach((s, i) => assert.equal(s, expected[i % graphs.length]));
      }
    }
    // the main thread still works afterwards
    assert.equal(addon.layout_json(graphs[0], '{}'), expected[0]);
  });

  it('keeps an engine error inside a worker thread', async () => {
    const addonPath = require.resolve('../js/load-native.js');
    const code = `
      const { parentPort, workerData } = require('node:worker_threads');
      const addon = require(workerData).loadNativeAddon();
      try { addon.layout_json('{"id":"r","layoutOptions":{"algorithm":"nope"},"children":[{"id":"a"}]}', '{}');
        parentPort.postMessage('no error'); }
      catch (e) { parentPort.postMessage(e.message); }
    `;
    const message = await new Promise((resolve, reject) => {
      const w = new Worker(code, { eval: true, workerData: addonPath });
      w.once('message', resolve);
      w.once('error', reject);
    });
    assert.match(message, /UnsupportedConfigurationException/);
  });
});
