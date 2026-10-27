/*******************************************************************************
 * Ported from elkjs via elk-rs — Copyright (c) 2017 Kiel University and others.
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
import ELK from '../js/index.js';

const elk = new ELK();

var simpleGraph = {
  id: "root",
  layoutOptions: { 'elk.direction': 'RIGHT' },
  children: [
    { id: "n1", width: 10, height: 10 },
    { id: "n2", width: 10, height: 10 }
  ],
  edges: [{
    id: "e1",
    sources: [ "n1" ],
    targets: [ "n2" ]
  }]
};

describe('Layout Options', () => {

  describe('#layout(...)', () => {

    it('should respect "options"', async () => {
      const graph = await elk.layout(simpleGraph, {
        layoutOptions: {
          'org.eclipse.elk.layered.spacing.nodeNodeBetweenLayers': 11
        }});
      assert.equal(graph.children[0].y, graph.children[1].y);
      assert.equal(Math.abs(graph.children[0].x - graph.children[1].x), 10 + 11);
    });

    it('should not override concrete layout options', async () => {
      const graph = await elk.layout(simpleGraph, {
        layoutOptions: {
          'org.eclipse.elk.direction': 'DOWN'
        }});
      assert.equal(graph.layoutOptions['elk.direction'], 'RIGHT');
      assert.ok(Math.abs(graph.children[0].x - graph.children[1].x) > 0);
      assert.equal(graph.children[0].y, graph.children[1].y);
    });

    it('should correctly parse ElkPadding', async () => {
      let paddingGraph = {
        id: "root",
        layoutOptions: { 'elk.padding': '[left=2, top=3, right=3, bottom=2]' },
        children: [ { id: "n1", width: 10, height: 10 } ]
      };
      const graph = await elk.layout(paddingGraph);
      assert.equal(graph.children[0].x, 2);
      assert.equal(graph.children[0].y, 3);
      assert.equal(graph.width, 15);
      assert.equal(graph.height, 15);
    });

    it('should correctly parse KVector', async () => {
      let kvectorGraph = {
        id: "root",
        children: [
          {
            id: "n1", width: 10, height: 10,
            layoutOptions: { position: "(23, 43)"}
          }
        ]
      };
      const graph = await elk.layout(kvectorGraph, {
        layoutOptions: {
          algorithm: 'fixed'
        }});
      assert.equal(graph.children[0].x, 23);
      assert.equal(graph.children[0].y, 43);
    });

    it('should correctly parse KVectorChain', async () => {
      let kvectorchainGraph = {
        id: "root",
        children: [
          { id: "n1", width: 10, height: 10 },
          { id: "n2", width: 10, height: 10 }
        ],
        edges: [{
          id: "e1",
          sources: [ "n1" ],
          targets: [ "n2" ],
          layoutOptions: { bendPoints: "( {1,2}, {3,4} )"}
        }]
      };
      const graph = await elk.layout(kvectorchainGraph, {
        layoutOptions: {
          algorithm: 'fixed'
        }});
      assert.equal(graph.edges[0].sections[0].startPoint.x, 1);
      assert.equal(graph.edges[0].sections[0].startPoint.y, 2);
      assert.equal(graph.edges[0].sections[0].endPoint.x, 3);
      assert.equal(graph.edges[0].sections[0].endPoint.y, 4);
    });

    it('should raise an exception for an invalid layouter id', async () => {
      let graph = {
        id: "root",
        children: [{ id: "n1", width: 10, height: 10 }],
        layoutOptions: { algorithm: "foo.bar.baz" }
      };
      await assert.rejects(elk.layout(graph),
        /org\.eclipse\.elk\.core\.UnsupportedConfigurationException/
      );
    });

    it('should default to elk.layered if no layouter has been specified', async () => {
      let graph = {
        id: "root",
        children: [{ id: "n1", width: 10, height: 10 }],
        layoutOptions: { }
      };
      await elk.layout(graph);
    });

  });
});

// Test default layout options

const secondElk = new ELK({
  defaultLayoutOptions: {
    'elk.layered.spacing.nodeNodeBetweenLayers': 33
  }
});

describe('Global Layout Options', () => {

  describe('#layout(...)', () => {

    it('should respect global layout"', async () => {
      const graph = await secondElk.layout(simpleGraph);
      assert.equal(graph.children[0].y, graph.children[1].y);
      assert.equal(Math.abs(graph.children[0].x - graph.children[1].x), 10 + 33);
    });

  });
});
