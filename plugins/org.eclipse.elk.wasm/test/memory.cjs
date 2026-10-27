'use strict';
/*
 * Memory check of the WASM backend: lays out every `.json` model under MODELS_DIR several times in
 * one module instance and reports the size of the wasm linear memory after each round. WebAssembly
 * memory never shrinks, so any growth after the first round means leaked objects (the reason the
 * build uses 64-bit C, see tools/build.py TARGET_FLAGS).
 *
 * usage: node plugins/org.eclipse.elk.wasm/test/memory.cjs [--models DIR] [--rounds N] [--module elk_lean.cjs]
 * Exit code 0 iff the memory size after the last round equals the size after the first round.
 *
 * SPDX-License-Identifier: EPL-2.0 OR GPL-3.0-or-later
 */
const fs = require('fs');
const path = require('path');

const ROOT = path.resolve(__dirname, '..', '..', '..');
const a = { models: path.join(ROOT, 'external', 'elk-models', 'realworld'), rounds: 3, module: null };
const argv = process.argv.slice(2);
for (let i = 0; i < argv.length; i++) {
  if (argv[i] === '--models') a.models = path.resolve(argv[++i]);
  else if (argv[i] === '--rounds') a.rounds = Math.max(2, Number(argv[++i]));
  else if (argv[i] === '--module') a.module = path.resolve(argv[++i]);
  else { console.error('unknown argument ' + argv[i]); process.exit(2); }
}

function walk(d) {
  const out = [];
  for (const e of fs.readdirSync(d, { withFileTypes: true })) {
    const p = path.join(d, e.name);
    if (e.isDirectory()) out.push(...walk(p));
    else if (e.name.endsWith('.json')) out.push(p);
  }
  return out;
}

const texts = walk(a.models).sort().map((f) => fs.readFileSync(f, 'utf8'));
const M = require(a.module || path.join(__dirname, '..', 'dist', 'wasm-node', 'elk_lean.cjs'));
const backend = M.createBackend();
const mib = (x) => (x / 1048576).toFixed(1);
const sizes = [];
for (let r = 0; r < a.rounds; r++) {
  const t0 = process.hrtime.bigint();
  let errors = 0;
  for (const t of texts) {
    try { backend.layout_json(t, '{}'); } catch (e) { errors++; }
  }
  const s = Number(process.hrtime.bigint() - t0) / 1e9;
  sizes.push(M.wasmMemoryBytes());
  console.log(`round ${r + 1}/${a.rounds}: ${texts.length} models (${errors} errors) in ${s.toFixed(2)} s, ` +
    `wasm memory ${mib(sizes[r])} MiB`);
}
const grew = sizes[sizes.length - 1] > sizes[0];
console.log(grew ? `memory: GREW by ${mib(sizes[sizes.length - 1] - sizes[0])} MiB after round 1` : 'memory: stable after round 1');
process.exit(grew ? 1 : 0);
