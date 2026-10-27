'use strict';
/*
 * Browser smoke test of dist/wasm/elk_lean.mjs in headless Chrome: serves this plugin directory
 * over HTTP (the .wasm is fetched next to elk_lean_core.mjs like on a web page), loads a page that
 * initialises the module and lays out a graph, and compares the result with the Node build.
 *
 * usage: node plugins/org.eclipse.elk.wasm/test/browser_smoke.cjs [CHROME_BINARY]
 *   default binary: $CHROME, else the usual macOS / Linux locations. Exit code 0 on success,
 *   77 when no Chrome is found.
 *
 * SPDX-License-Identifier: EPL-2.0 OR GPL-3.0-or-later
 */
const fs = require('fs');
const http = require('http');
const path = require('path');
const { spawn } = require('child_process');

const PLUGIN = path.resolve(__dirname, '..');
const GRAPH = {
  id: 'root',
  layoutOptions: { 'elk.algorithm': 'layered', 'elk.hierarchyHandling': 'INCLUDE_CHILDREN' },
  children: [
    { id: 'a', width: 30, height: 20, labels: [{ text: 'A', width: 8, height: 10 }] },
    { id: 'b', width: 30, height: 20 },
    { id: 'c', width: 40, height: 30, children: [{ id: 'c1', width: 10, height: 10 }] },
  ],
  edges: [
    { id: 'e1', sources: ['a'], targets: ['b'] },
    { id: 'e2', sources: ['a'], targets: ['c1'] },
  ],
};

const PAGE = `<!doctype html><meta charset="utf-8"><title>elk-lean wasm smoke</title>
<pre id="out">pending</pre>
<script type="module">
import init, { layout_json, known_layout_algorithms } from './dist/wasm/elk_lean.mjs';
const out = document.getElementById('out');
try {
  await init();
  const layout = layout_json(${JSON.stringify(JSON.stringify(GRAPH))}, '{}');
  let error = null;
  try { layout_json(${JSON.stringify(JSON.stringify({ ...GRAPH, layoutOptions: { 'elk.algorithm': 'nope' } }))}, '{}'); } catch (e) { error = e instanceof Error ? e.message : String(e); }
  out.textContent = JSON.stringify({ layout, algorithms: JSON.parse(known_layout_algorithms()).length, error });
} catch (e) {
  out.textContent = 'FAILED ' + (e && e.stack || e);
}
</script>`;

function findChrome() {
  const cands = [process.argv[2], process.env.CHROME,
    '/Applications/Google Chrome.app/Contents/MacOS/Google Chrome',
    '/usr/bin/google-chrome', '/usr/bin/chromium', '/usr/bin/chromium-browser'];
  return cands.find((c) => c && fs.existsSync(c));
}

const TYPES = { '.mjs': 'text/javascript', '.js': 'text/javascript', '.wasm': 'application/wasm', '.html': 'text/html' };

async function main() {
  const chrome = findChrome();
  if (!chrome) {
    console.log('browser smoke: no Chrome found, skipped');
    process.exit(77);
  }
  const server = http.createServer((req, res) => {
    const url = decodeURIComponent(req.url.split('?')[0]);
    if (url === '/' || url === '/index.html') {
      res.writeHead(200, { 'content-type': 'text/html' });
      res.end(PAGE);
      return;
    }
    const file = path.join(PLUGIN, path.normalize(url));
    if (!file.startsWith(PLUGIN) || !fs.existsSync(file)) {
      res.writeHead(404);
      res.end();
      return;
    }
    res.writeHead(200, { 'content-type': TYPES[path.extname(file)] || 'application/octet-stream' });
    fs.createReadStream(file).pipe(res);
  });
  await new Promise((r) => server.listen(0, '127.0.0.1', r));
  const url = `http://127.0.0.1:${server.address().port}/`;
  const profile = fs.mkdtempSync(path.join(require('os').tmpdir(), 'elk-wasm-chrome-'));
  const args = ['--headless=new', '--disable-gpu', '--no-first-run', '--no-default-browser-check',
    `--user-data-dir=${profile}`, '--virtual-time-budget=60000', '--dump-dom', url];
  const dom = await new Promise((resolve, reject) => {
    const p = spawn(chrome, args, { stdio: ['ignore', 'pipe', 'pipe'] });
    let outText = '';
    p.stdout.on('data', (d) => { outText += d; });
    p.on('error', reject);
    p.on('close', () => resolve(outText));
  });
  server.close();
  fs.rmSync(profile, { recursive: true, force: true });
  const m = dom.match(/<pre id="out">([\s\S]*?)<\/pre>/);
  const text = m ? m[1].replace(/&quot;/g, '"').replace(/&lt;/g, '<').replace(/&gt;/g, '>').replace(/&amp;/g, '&') : '';
  if (!text.startsWith('{')) {
    console.log('browser smoke: FAILED: ' + (text || dom.slice(0, 500)));
    process.exit(1);
  }
  const res = JSON.parse(text);
  const node = require('../js/load-wasm.js')().layout_json(JSON.stringify(GRAPH), '{}');
  const ok = res.layout === node && res.algorithms > 0 && /nope/.test(res.error || '');
  const version = require('child_process').execFileSync(chrome, ['--version']).toString().trim();
  console.log(`browser smoke (${version}): layout ${res.layout === node ? 'equals' : 'DIFFERS FROM'} the Node build, ` +
    `${res.algorithms} algorithms, error path: ${res.error}`);
  process.exit(ok ? 0 : 1);
}

main();
