// Ported from elk-rs plugins/org.eclipse.elk.js/test/testAlgorithmSuperset.test.js.
// SPDX-License-Identifier: EPL-2.0 OR GPL-3.0-or-later
import { describe, it } from 'node:test';
import assert from 'node:assert/strict';
import { fileURLToPath } from 'node:url';
import ELK from '../js/index.js';
import ELKApi from '../js/elk-api.js';
import workerModule from '../js/elk-worker.js';

const FakeWorker = workerModule.Worker;

const constructors = {
  direct: () => new ELK({ algorithms: ['layered'] }),
  fakeWorker: () => new ELKApi({ algorithms: ['layered'], workerFactory: () => new FakeWorker() }),
  workerThreads: () => new ELK({ algorithms: ['layered'],
    workerUrl: fileURLToPath(new URL('../js/elk-worker.js', import.meta.url)) }),
};

describe('Java algorithm superset in every JS mode', () => {
  for (const [mode, create] of Object.entries(constructors)) {
    it(`retains VertiFlex with the compatibility algorithms hint (${mode})`, async () => {
      const elk = create();
      try {
        const ids = (await elk.knownLayoutAlgorithms()).map(algorithm => algorithm.id);
        assert.ok(ids.includes('org.eclipse.elk.vertiflex'));
        assert.ok(ids.includes('org.eclipse.elk.disco'));
        const result = await elk.layout({ id: 'root',
          layoutOptions: { 'elk.algorithm': 'vertiflex' },
          children: [{ id: 'a', width: 30, height: 20 }, { id: 'b', width: 30, height: 20 }],
          edges: [{ id: 'ab', sources: ['a'], targets: ['b'] }],
        });
        assert.ok(result.children.every(node => Number.isFinite(node.x) && Number.isFinite(node.y)));
        assert.notEqual(result.children[0].y, result.children[1].y);
      } finally {
        elk.terminateWorker();
      }
    });
  }
});
