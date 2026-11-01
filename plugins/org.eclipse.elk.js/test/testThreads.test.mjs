// elk-lean: the `threads` option of the native addon (parallel sibling layout, docs/parallel-layout.md).
// Results must be byte-identical for every thread cap, from the main thread and from concurrent
// worker_threads (the Lean task manager's workers and Node's worker threads coexist).
// SPDX-License-Identifier: EPL-2.0 OR GPL-3.0-or-later

// lay out every sibling sub-graph with tasks, however small (read when the addon initialises)
process.env.ELK_LEAN_PAR_MIN_WORK = '0';

import { describe, it } from 'node:test';
import assert from 'node:assert/strict';
import { createRequire } from 'node:module';
import { Worker } from 'node:worker_threads';

const require = createRequire(import.meta.url);
const ELK = require('../js/index.js');
const { loadNativeAddon } = require('../js/load-native.js');
const addon = loadNativeAddon();

/** A root with `k` compound children (layered, mrtree, force alternately), each a chain of `n` nodes
 * with an edge to its own port, and edges between the children's ports. */
function hierarchy(k, n) {
  const algorithms = ['layered', 'mrtree', 'force', 'layered', 'rectpacking', 'layered'];
  const children = [];
  const edges = [];
  for (let c = 0; c < k; c++) {
    const kids = [];
    const inner = [];
    for (let i = 0; i < n; i++) {
      kids.push({ id: `c${c}_n${i}`, width: 20 + ((i * 7 + c) % 13), height: 10 + (i % 5) });
      if (i > 0) inner.push({ id: `c${c}_e${i}`, sources: [`c${c}_n${(i * 5) % i}`], targets: [`c${c}_n${i}`] });
    }
    const alg = algorithms[c % algorithms.length];
    const ports = alg === 'layered' ? [{ id: `c${c}_p`, width: 5, height: 5 }] : [];
    if (ports.length) inner.push({ id: `c${c}_ep`, sources: [`c${c}_n${n - 1}`], targets: [`c${c}_p`] });
    children.push({ id: `c${c}`, layoutOptions: { 'elk.algorithm': alg }, ports, children: kids, edges: inner });
  }
  const portIds = children.flatMap(c => c.ports.map(p => p.id));
  for (let i = 1; i < portIds.length; i++) edges.push({ id: `rp${i}`, sources: [portIds[i - 1]], targets: [portIds[i]] });
  return { id: 'root', children, edges };
}

/** A flat graph with `k` chains (connected components; laid out sequentially by design). */
function components(k) {
  const children = [];
  const edges = [];
  for (let c = 0; c < k; c++) {
    for (let i = 0; i < 5; i++) {
      children.push({ id: `k${c}_${i}`, width: 20, height: 20 });
      if (i > 0) edges.push({ id: `ke${c}_${i}`, sources: [`k${c}_${i - 1}`], targets: [`k${c}_${i}`] });
    }
  }
  return { id: 'root', children, edges };
}

/** A child that throws Java's layer constraint exception naming its node `c<i>_a`. */
function throwing(ids) {
  const children = [];
  for (let c = 0; c < 6; c++) {
    if (ids.includes(c)) {
      children.push({ id: `c${c}`, children: [
        { id: `c${c}_a`, width: 10, height: 10, layoutOptions: { 'elk.layered.layering.layerConstraint': 'FIRST_SEPARATE' } },
        { id: `c${c}_b`, width: 10, height: 10, layoutOptions: { 'elk.layered.layering.layerConstraint': 'FIRST_SEPARATE' } }],
        edges: [{ id: `c${c}_e`, sources: [`c${c}_b`], targets: [`c${c}_a`] }] });
    } else {
      children.push({ id: `c${c}`, children: [{ id: `c${c}_a`, width: 10, height: 10 }, { id: `c${c}_b`, width: 10, height: 10 }],
        edges: [{ id: `c${c}_e`, sources: [`c${c}_a`], targets: [`c${c}_b`] }] });
    }
  }
  return { id: 'root', children };
}

const graphs = [hierarchy(6, 30), hierarchy(3, 80), components(12)].map(g => JSON.stringify(g));

describe('threads option', { skip: addon ? false : 'native addon not built (sh scripts/build_napi.sh)' }, () => {
  it('gives the same bytes for every thread cap (addon)', () => {
    for (const g of graphs) {
      const sequential = addon.layout_json(g, '{}', 1);
      assert.equal(addon.layout_json(g, '{}'), sequential);
      for (const t of [2, 3, 8]) assert.equal(addon.layout_json(g, '{}', t), sequential, `threads ${t}`);
    }
  });

  it('gives the same graph for threads: 1 and the default (ELK API)', async () => {
    const graph = hierarchy(5, 40);
    const sequential = await new ELK({ threads: 1 }).layout(graph);
    assert.deepEqual(await new ELK().layout(graph), sequential);
    assert.deepEqual(await new ELK({ threads: 4 }).layout(graph), sequential);
    assert.deepEqual(await new ELK().layout(graph, { threads: 2 }), sequential);
    const flat = components(9);
    assert.deepEqual(await new ELK().layout(flat), await new ELK({ threads: 1 }).layout(flat));
  });

  it('reports the first throwing child in sibling order', () => {
    for (const ids of [[0], [3], [5], [1, 4], [2, 5], [0, 1, 2, 3, 4, 5]]) {
      const g = JSON.stringify(throwing(ids));
      let sequential;
      assert.throws(() => addon.layout_json(g, '{}', 1), e => { sequential = e.message; return true; });
      assert.match(sequential, new RegExp(`'root\\.c${ids[0]}\\.c${ids[0]}_a'`));
      assert.throws(() => addon.layout_json(g, '{}', 4), e => e.message === sequential, `children ${ids}`);
    }
  });

  it('rejects invalid thread counts', async () => {
    for (const v of [0, -1, 1.5, '2', NaN]) {
      assert.throws(() => addon.layout_json(graphs[2], '{}', v), TypeError, String(v));
      assert.throws(() => new ELK({ threads: v }), TypeError, String(v));
    }
    await assert.rejects(new ELK().layout(hierarchy(2, 3), { threads: 0 }), TypeError);
    // undefined and null mean the default
    assert.equal(addon.layout_json(graphs[2], '{}', undefined), addon.layout_json(graphs[2], '{}', null));
  });

  it('coexists with concurrent worker_threads', async () => {
    const expected = graphs.map(g => addon.layout_json(g, '{}', 1));
    const loader = require.resolve('../js/load-native.js');
    const code = `
      const { parentPort, workerData } = require('node:worker_threads');
      const addon = require(workerData.loader).loadNativeAddon();
      const out = [];
      for (let r = 0; r < 3; r++) {
        for (const g of workerData.graphs) out.push(addon.layout_json(g, '{}', r + 1));
        for (const g of workerData.graphs) out.push(addon.layout_json(g, '{}'));
      }
      parentPort.postMessage(out);
    `;
    const run = () => new Promise((resolve, reject) => {
      const w = new Worker(code, { eval: true, workerData: { loader, graphs } });
      w.once('message', resolve);
      w.once('error', reject);
    });
    for (let wave = 0; wave < 2; wave++) {
      const results = await Promise.all([run(), run(), run(), run()]);
      for (const out of results) out.forEach((s, i) => assert.equal(s, expected[i % graphs.length], `wave ${wave} #${i}`));
    }
    assert.equal(addon.layout_json(graphs[0], '{}'), expected[0]);
  });
});
