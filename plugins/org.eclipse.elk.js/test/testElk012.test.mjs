// Ported from elk-rs plugins/org.eclipse.elk.js/test/testElk012.test.js.
// Fixtures: elk-rs plugins/org.eclipse.elk.alg.layered/tests/resources/node_flexibility/.
// SPDX-License-Identifier: EPL-2.0 OR GPL-3.0-or-later
import { describe, it } from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import ELK from '../js/index.js';

const option = 'org.eclipse.elk.alg.layered.nodePlacement.networkSimplex.nodeFlexibility.recomputeNodePlacement';
function fixture(name) {
  return JSON.parse(readFileSync(new URL(`./fixtures/node_flexibility/${name}.json`, import.meta.url), 'utf8'));
}
function positions(graph) {
  return graph.children.map(({ id, x, y, width, height, ports, labels }) => ({ id, x, y, width, height, ports, labels }));
}

describe('ELK 0.12 node flexibility', () => {
  it('exposes the recomputation option and preserves null-as-disabled behavior', async () => {
    const elk = new ELK();
    assert.ok((await elk.knownLayoutOptions()).map(description => description.id).includes(option));
    assert.deepEqual(positions(await elk.layout(fixture('null_recompute'))),
      positions(await elk.layout(fixture('no_recompute'))));
  });

  it('recomputes inherited flexible sizes and refreshes ports and labels', async () => {
    const elk = new ELK();
    const inherited = await elk.layout(fixture('recompute_inherited'));
    const explicit = await elk.layout(fixture('recompute_brandes_koepf'));
    assert.deepEqual(positions(inherited), positions(explicit));
    assert.notDeepEqual(positions(explicit), positions(await elk.layout(fixture('no_recompute'))));
  });

  it('separates the equal-size split nodes', async () => {
    const result = await new ELK().layout(fixture('unzipping_equal_split'));
    const a = result.children.find(node => node.id === 'a');
    const b = result.children.find(node => node.id === 'b');
    assert.notEqual(a.x, b.x);
  });
});
