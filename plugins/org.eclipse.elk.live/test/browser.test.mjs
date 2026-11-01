// Headless browser smoke test of the built app (dist/): the WASM layout engine loads in the Web
// Worker, the default graph renders, typed ELK Text re-renders with the new node ids, a syntax error
// gets an editor marker and an error status, an example from the menu renders, option-key completion
// offers `elk.direction`, and the SVG export contains the nodes.
// Optional: needs `playwright-core` (not a dependency of the app; PLAYWRIGHT_CORE=<dir of the
// package>, or resolvable from here) and a Chrome/Chromium (CHROME_PATH, else the usual install
// locations). Skipped otherwise.
// SPDX-License-Identifier: EPL-2.0 OR GPL-3.0-or-later
import { describe, it, before, after } from 'node:test';
import assert from 'node:assert/strict';
import { createRequire } from 'node:module';
import { createServer } from 'node:http';
import { existsSync, readFileSync, statSync, writeFileSync } from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const require = createRequire(import.meta.url);
const app = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const dist = path.join(app, 'dist');

function loadPlaywright() {
  for (const p of [process.env.PLAYWRIGHT_CORE, 'playwright-core'].filter(Boolean)) {
    try {
      return require(p);
    } catch { /* try the next */ }
  }
  return null;
}

function findChrome() {
  const candidates = [process.env.CHROME_PATH,
    '/Applications/Google Chrome.app/Contents/MacOS/Google Chrome',
    '/Applications/Chromium.app/Contents/MacOS/Chromium',
    '/usr/bin/google-chrome', '/usr/bin/chromium', '/usr/bin/chromium-browser'];
  return candidates.find((c) => c && existsSync(c)) ?? null;
}

const MIME = {
  '.html': 'text/html', '.js': 'text/javascript', '.mjs': 'text/javascript', '.css': 'text/css',
  '.json': 'application/json', '.wasm': 'application/wasm', '.svg': 'image/svg+xml', '.ttf': 'font/ttf',
  '.elkt': 'text/plain', '.md': 'text/plain',
};

const pw = loadPlaywright();
const chrome = findChrome();
const skip = !existsSync(path.join(dist, 'index.html')) ? 'run `npm run build` first'
  : !pw ? 'playwright-core not available (PLAYWRIGHT_CORE)' : !chrome ? 'no Chrome/Chromium (CHROME_PATH)' : false;

describe('browser (headless Chrome, built app)', { skip }, () => {
  let server;
  let browser;
  let page;
  let base;
  const errors = [];

  before(async () => {
    server = createServer((req, res) => {
      const url = new URL(req.url, 'http://localhost');
      let file = path.join(dist, decodeURIComponent(url.pathname));
      if (!file.startsWith(dist)) { res.writeHead(403).end(); return; }
      if (existsSync(file) && statSync(file).isDirectory()) file = path.join(file, 'index.html');
      if (!existsSync(file)) { res.writeHead(404).end(); return; }
      res.writeHead(200, { 'content-type': MIME[path.extname(file)] ?? 'application/octet-stream' });
      res.end(readFileSync(file));
    });
    await new Promise((r) => server.listen(0, '127.0.0.1', r));
    base = `http://127.0.0.1:${server.address().port}/`;
    browser = await pw.chromium.launch({ executablePath: chrome, headless: true });
    page = await browser.newPage({ viewport: { width: 1400, height: 900 } });
    page.on('console', (m) => { if (m.type() === 'error') errors.push(m.text()); });
    page.on('pageerror', (e) => errors.push(String(e)));
  });

  after(async () => {
    await browser?.close();
    server?.close();
  });

  const svgHas = (ids) => page.waitForFunction((ids) => ids.every((id) => document.getElementById(`sprotty_${id}`)), ids,
    { timeout: 20000 });
  const statusOk = () => page.waitForFunction(() => document.getElementById('status').className === 'ok', null, { timeout: 20000 });

  it('loads the engine and renders the default graph', async () => {
    const t0 = Date.now();
    await page.goto(base);
    await statusOk();
    await svgHas(['n1', 'n2', 'n3']);
    console.log(`# first layout after ${Date.now() - t0} ms: ${await page.textContent('#status')}`);
    const edges = await page.$$eval('#sprotty path.elkedge:not(.arrow)', (ps) => ps.length);
    assert.equal(edges, 2);
  });

  it('re-renders typed ELK Text', async () => {
    await page.click('#monaco-editor .view-lines');
    await page.keyboard.press(process.platform === 'darwin' ? 'Meta+A' : 'Control+A');
    await page.keyboard.press('Delete');
    // line by line; Escape closes the completion list, which would take the Enter otherwise
    for (const line of ['algorithm: layered', 'node alpha', 'node beta', 'node gamma', 'edge alpha -> beta',
      'edge alpha -> gamma']) {
      await page.keyboard.type(line);
      await page.keyboard.press('Escape');
      await page.keyboard.press('Enter');
    }
    await svgHas(['alpha', 'beta', 'gamma']);
    await statusOk();
    // removed elements fade out (sprotty fadeModule) before they leave the DOM
    await page.waitForFunction(() => !document.getElementById('sprotty_n1'), null, { timeout: 20000 });
  });

  it('marks syntax errors with line and column', async () => {
    await page.keyboard.type('edge alpha -> ');
    await page.keyboard.press('Escape');
    await page.waitForFunction(() => document.getElementById('status').className === 'error', null, { timeout: 30000 });
    const status = await page.textContent('#status');
    assert.match(status, /^Parse error at \d+:\d+: /);
    await page.waitForSelector('#monaco-editor .squiggly-error', { timeout: 10000 });
    for (let i = 0; i < 'edge alpha -> '.length; i++) await page.keyboard.press('Backspace');
    await statusOk();
  });

  it('offers option keys and enum values', async () => {
    await page.keyboard.type('dire');
    await page.keyboard.press('Control+Space');
    await page.waitForSelector('.suggest-widget .monaco-list-row', { timeout: 10000 });
    const labels = await page.$$eval('.suggest-widget .monaco-list-row', (rows) => rows.map((r) => r.textContent));
    assert.ok(labels.some((l) => l.includes('elk.direction')), labels.join(' | '));
    await page.keyboard.press('Enter'); // inserts `elk.direction: ` and opens the value list
    await page.waitForFunction(() => [...document.querySelectorAll('.suggest-widget .monaco-list-row')]
      .some((r) => r.textContent.includes('DOWN')), null, { timeout: 10000 });
    await page.keyboard.type('DOWN');
    await page.keyboard.press('Escape');
    await statusOk();
    const text = await page.evaluate(() => window.elkLive.editor.getValue());
    assert.match(text, /elk\.direction: DOWN/);
  });

  it('loads an example from the menu', async () => {
    await page.selectOption('#example-select', 'general/direction');
    await svgHas(['leftToRight', 'topToBottom', 'rightToLeft', 'bottomToTop']);
    await statusOk();
    assert.match(await page.textContent('#example-title'), /Basics/);
    const shot = process.env.ELK_LIVE_SCREENSHOT;
    if (shot) await page.screenshot({ path: shot });
  });

  it('exports SVG with the nodes', async () => {
    const [download] = await Promise.all([page.waitForEvent('download'), page.click('#svg-button')]);
    const file = await download.path();
    const text = readFileSync(file, 'utf8');
    assert.match(text, /^<\?xml/);
    assert.match(text, /viewBox="/);
    assert.ok(text.includes('id="sprotty_leftToRight"'));
    if (process.env.ELK_LIVE_SVG) writeFileSync(process.env.ELK_LIVE_SVG, text);
  });

  it('logs no page errors', () => {
    assert.deepEqual(errors, []);
  });
});
