#!/usr/bin/env node
// Build-time assets of the demo (run by `npm run dev` / `npm run build`):
//   public/examples/<path>.elkt   the example files of external/elk-models/examples (relative names kept)
//   public/examples/index.json    [{ path, label, category, doc }] for the examples page (elkex sections)
//   public/elk-lean/js/{elk-worker.js,load-wasm.browser.mjs}
//   public/elk-lean/dist/wasm/elk_lean_core.{mjs,wasm}
//                                 the Web Worker of the elk-lean npm package and its WASM backend,
//                                 served unbundled (the app passes `workerUrl` to `new ELK(...)`)
// Sources: ELK_MODELS_DIR or ../../external/elk-models (in a git worktree without submodules the
// main checkout's copy); the elk-lean package (node_modules/elk-lean -> ../org.eclipse.elk.js) with
// its WASM build (sh scripts/build_wasm.sh at the repository root).
// SPDX-License-Identifier: EPL-2.0 OR GPL-3.0-or-later
import { cpSync, existsSync, mkdirSync, readdirSync, readFileSync, rmSync, statSync, writeFileSync, realpathSync } from 'node:fs';
import { execFileSync } from 'node:child_process';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { parseElkex } from '../src/core/elkex.ts';

const app = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const repo = path.resolve(app, '../..');
const pub = path.join(app, 'public');

function fail(msg) {
  console.error(`copy-assets: ${msg}`);
  process.exit(1);
}

function modelsDir() {
  if (process.env.ELK_MODELS_DIR) return process.env.ELK_MODELS_DIR;
  const local = path.join(repo, 'external/elk-models');
  if (existsSync(path.join(local, 'examples'))) return local;
  try {
    const common = execFileSync('git', ['-C', repo, 'rev-parse', '--path-format=absolute', '--git-common-dir'],
      { encoding: 'utf8' }).trim();
    const main = path.join(path.dirname(common), 'external/elk-models');
    if (existsSync(path.join(main, 'examples'))) return main;
  } catch { /* not a git checkout */ }
  return null;
}

// --- examples ---
const models = modelsDir();
if (!models) fail('external/elk-models/examples not found (git submodule update --init external/elk-models, or ELK_MODELS_DIR)');
const exSrc = path.join(models, 'examples');
const exOut = path.join(pub, 'examples');
rmSync(exOut, { recursive: true, force: true });
const index = [];
const walk = (dir) => {
  for (const name of readdirSync(dir).sort()) {
    const p = path.join(dir, name);
    if (statSync(p).isDirectory()) walk(p);
    else if (name.endsWith('.elkt')) {
      const rel = path.relative(exSrc, p).split(path.sep).join('/');
      const target = path.join(exOut, rel);
      mkdirSync(path.dirname(target), { recursive: true });
      cpSync(p, target);
      const ex = parseElkex(rel.replace(/\.elkt$/, ''), readFileSync(p, 'utf8'));
      index.push({ path: ex.path, label: ex.label, category: ex.category, doc: ex.doc });
    }
  }
};
walk(exSrc);
index.sort((a, b) => a.category.join('>').localeCompare(b.category.join('>')) || a.label.localeCompare(b.label));
writeFileSync(path.join(exOut, 'index.json'), JSON.stringify(index, null, 1) + '\n');

// --- elk-lean worker + WASM ---
const pkgLink = path.join(app, 'node_modules/elk-lean');
if (!existsSync(pkgLink)) fail('node_modules/elk-lean missing: run npm install');
const pkg = realpathSync(pkgLink);
const wasmDir = path.join(pkg, 'dist/wasm');
for (const f of ['elk_lean_core.mjs', 'elk_lean_core.wasm']) {
  if (!existsSync(path.join(wasmDir, f))) fail(`${path.join(wasmDir, f)} missing: run sh scripts/build_wasm.sh at the repository root`);
}
const elkOut = path.join(pub, 'elk-lean');
rmSync(elkOut, { recursive: true, force: true });
mkdirSync(path.join(elkOut, 'js'), { recursive: true });
mkdirSync(path.join(elkOut, 'dist/wasm'), { recursive: true });
for (const f of ['elk-worker.js', 'load-wasm.browser.mjs']) cpSync(path.join(pkg, 'js', f), path.join(elkOut, 'js', f));
for (const f of ['elk_lean_core.mjs', 'elk_lean_core.wasm']) cpSync(path.join(wasmDir, f), path.join(elkOut, 'dist/wasm', f));
for (const f of ['LICENSE.md', 'NOTICE']) if (existsSync(path.join(pkg, f))) cpSync(path.join(pkg, f), path.join(elkOut, f));
const wasmBytes = statSync(path.join(elkOut, 'dist/wasm/elk_lean_core.wasm')).size;
console.log(`copy-assets: ${index.length} examples from ${exSrc}; elk-lean worker + WASM (${(wasmBytes / 1048576).toFixed(1)} MiB) from ${pkg}`);
