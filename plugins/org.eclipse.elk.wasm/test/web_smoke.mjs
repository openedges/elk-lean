/*
 * Smoke test of the browser ES module build (dist/wasm/elk_lean.mjs) under Node.js: the .wasm is
 * handed over as `wasmBinary` (browsers fetch it next to elk_lean_core.mjs), then the four named
 * exports are called (including convert_elkt) and the layout is compared with the Node build (dist/wasm-node).
 *
 * usage: node plugins/org.eclipse.elk.wasm/test/web_smoke.mjs
 *
 * SPDX-License-Identifier: EPL-2.0 OR GPL-3.0-or-later
 */
import { readFileSync } from 'node:fs';
import { createRequire } from 'node:module';
import init, {
  layout_json, known_layout_algorithms, known_layout_options, known_layout_categories, convert_elkt,
} from '../dist/wasm/elk_lean.mjs';

const require = createRequire(import.meta.url);
const graph = JSON.stringify({
  id: 'root',
  layoutOptions: { 'elk.algorithm': 'layered', 'elk.direction': 'DOWN', 'elk.hierarchyHandling': 'INCLUDE_CHILDREN' },
  children: [
    { id: 'a', width: 30, height: 20, labels: [{ text: 'A', width: 8, height: 10 }] },
    { id: 'b', width: 30, height: 20 },
    { id: 'c', width: 30, height: 20, children: [{ id: 'c1', width: 10, height: 10 }] },
  ],
  edges: [
    { id: 'e1', sources: ['a'], targets: ['b'] },
    { id: 'e2', sources: ['a'], targets: ['c1'] },
  ],
});

let failures = 0;
function check(name, cond, extra) {
  console.log(`${cond ? 'ok  ' : 'FAIL'} ${name}${extra ? ': ' + extra : ''}`);
  if (!cond) failures++;
}

let early = null;
try { layout_json(graph, '{}'); } catch (e) { early = e; }
check('calls before init throw', early instanceof Error, early && early.message);

const wasmBinary = readFileSync(new URL('../dist/wasm/elk_lean_core.wasm', import.meta.url));
await init({ wasmBinary });
await init(); // idempotent

const web = layout_json(graph, '{}');
const node = require('../js/load-wasm.js')().layout_json(graph, '{}');
check('layout_json equals the Node build', web === node, web.slice(0, 80) + '...');
check('known_layout_algorithms', JSON.parse(known_layout_algorithms()).length > 0);
check('known_layout_options', JSON.parse(known_layout_options()).length > 0);
check('known_layout_categories', JSON.parse(known_layout_categories()).length > 0);
const elkt = 'algorithm: layered\nnode a { label "A" }\nnode b { port p }\nedge a -> b.p\n';
for (const flags of [0, 5]) {
  const w = convert_elkt(elkt, flags);
  check(`convert_elkt(flags ${flags}) equals the Node build`, w === require('../js/load-wasm.js')().convert_elkt(elkt, flags), w.slice(0, 80));
}
let cerr = null;
try { convert_elkt('node a\nedge a -> \n'); } catch (e) { cerr = e; }
check('convert_elkt errors carry line:col', cerr instanceof Error && /^ELK Text parse error: 3:1: /.test(cerr.message), cerr && cerr.message);
let err = null;
try { layout_json(graph, '{"elk.algorithm":"doesNotExist"}'); } catch (e) { err = e; }
check('errors throw Error(message)', err instanceof Error && /doesNotExist/.test(err.message), err && err.message);
process.exit(failures === 0 ? 0 : 1);
