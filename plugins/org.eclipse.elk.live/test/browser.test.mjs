// Headless browser smoke test of the built site (dist/), page by page:
//   index.html     landing links, engine badge, dark mode, redirect of an old single-page link
//   elkgraph.html  the WASM layout engine loads in the Web Worker, the default graph renders, typed
//                  ELK Text re-renders with the new node ids, a syntax error gets an editor marker
//                  and an error status, option-key completion offers `elk.direction`, "Open as
//                  JSON" opens the converted graph in the JSON editor
//   json.html      the default JSON5 sample renders, a JSON5 syntax error gets a marker
//   examples.html  the table of contents, `?e=general/direction`, a click on another entry renders
//                  it and updates the URL, Back restores the previous one, the SVG export
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
const LZString = require('lz-string');
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
const pages = ['index', 'elkgraph', 'json', 'examples'];
const skip = !pages.every((p) => existsSync(path.join(dist, `${p}.html`))) ? 'run `npm run build` first'
  : !pw ? 'playwright-core not available (PLAYWRIGHT_CORE)' : !chrome ? 'no Chrome/Chromium (CHROME_PATH)' : false;

describe('browser (headless Chrome, built site)', { skip }, () => {
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
    page.on('console', (m) => { if (m.type() === 'error') errors.push(`${page.url()}: ${m.text()}`); });
    page.on('pageerror', (e) => errors.push(`${page.url()}: ${e}`));
  });

  after(async () => {
    await browser?.close();
    server?.close();
  });

  const svgHas = (ids) => page.waitForFunction((ids) => ids.every((id) => document.getElementById(`sprotty_${id}`)), ids,
    { timeout: 20000 });
  const statusOk = () => page.waitForFunction(() => document.getElementById('status')?.className === 'ok', null, { timeout: 20000 });
  const statusError = () => page.waitForFunction(() => document.getElementById('status')?.className === 'error', null, { timeout: 30000 });
  const selectAll = () => page.keyboard.press(process.platform === 'darwin' ? 'Meta+A' : 'Control+A');

  describe('index.html', () => {
    it('links the demonstrators and toggles dark mode', async () => {
      await page.goto(base);
      assert.equal(await page.textContent('h1'), 'ELK Demonstrators');
      const hrefs = await page.$$eval('a', (as) => as.map((a) => a.getAttribute('href')));
      for (const h of ['elkgraph.html', 'json.html', 'examples.html']) assert.ok(hrefs.includes(h), h);
      assert.match(await page.textContent('#engine-badge'), /^elk-lean 0\.12\.0 · ELK 0\.12\.0$/);
      const dark = await page.evaluate(() => document.body.classList.contains('elk-dark-mode'));
      await page.click('#dark-toggle');
      assert.equal(await page.evaluate(() => document.body.classList.contains('elk-dark-mode')), !dark);
      await page.click('#dark-toggle');
      assert.equal(await page.evaluate(() => document.body.classList.contains('elk-dark-mode')), dark);
      await page.click('#link-examples');
      await page.waitForURL(/\/examples\.html/);
    });

    it('forwards an old single-page link to the ELKT editor', async () => {
      const content = LZString.compressToEncodedURIComponent('node redirected\nnode kept\nedge redirected -> kept');
      await page.goto(`${base}?compressedContent=${content}`);
      await page.waitForURL(new RegExp(`/elkgraph\\.html\\?compressedContent=${content.replace(/[$+]/g, '\\$&')}$`));
      await svgHas(['redirected', 'kept']);
      await statusOk();
    });
  });

  describe('elkgraph.html', () => {
    it('loads the engine and renders the default graph', async () => {
      const t0 = Date.now();
      await page.goto(`${base}elkgraph.html`);
      await statusOk();
      await svgHas(['n1', 'n2', 'n3']);
      console.log(`# first layout after ${Date.now() - t0} ms: ${await page.textContent('#status')}`);
      const edges = await page.$$eval('#sprotty path.elkedge:not(.arrow)', (ps) => ps.length);
      assert.equal(edges, 2);
      assert.equal(await page.textContent('.navbar-title'), 'ELKT Editor');
      assert.equal(await page.getAttribute('.navbar-brand', 'href'), 'index.html');
      assert.ok(await page.getAttribute('#engine-badge', 'title'));
    });

    it('re-renders typed ELK Text', async () => {
      await page.click('#monaco-editor .view-lines');
      await selectAll();
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
      // the model link carries the text
      await page.waitForFunction(() => document.getElementById('model-link').getAttribute('href').includes('elkgraph.html?compressedContent='),
        null, { timeout: 5000 });
    });

    it('marks syntax errors with line and column', async () => {
      await page.keyboard.type('edge alpha -> ');
      await page.keyboard.press('Escape');
      await statusError();
      assert.match(await page.textContent('#status'), /^Parse error at \d+:\d+: /);
      await page.waitForSelector('#monaco-editor .squiggly-error', { timeout: 10000 });
      for (let i = 0; i < 'edge alpha -> '.length; i++) await page.keyboard.press('Backspace');
      await statusOk();
    });

    it('offers option keys and enum values', async () => {
      // on a new line 2: root options precede the nodes and edges
      await page.evaluate(() => {
        window.elkLive.editor.setPosition({ lineNumber: 1, column: 19 });
        window.elkLive.editor.focus();
      });
      await page.keyboard.press('End');
      await page.keyboard.press('Enter');
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
      assert.match(text, /^algorithm: layered\nelk\.direction: DOWN\nnode alpha\n/);
      // laid out top-down now
      await page.waitForFunction(() => {
        const y = (id) => document.getElementById(`sprotty_${id}`)?.getBoundingClientRect().y ?? 0;
        return y('beta') > y('alpha') + 20;
      }, null, { timeout: 20000 });
      await statusOk();
    });

    it('opens the graph as ELK JSON in the JSON editor', async () => {
      await page.click('#open-json-button');
      await page.waitForURL(/\/json\.html\?compressedContent=/);
      await svgHas(['alpha', 'beta', 'gamma']);
      await statusOk();
      const json = JSON.parse(await page.evaluate(() => window.elkLive.editor.getValue()));
      assert.deepEqual(json.children.map((c) => [c.id, c.width, c.height]), [['alpha', 30, 30], ['beta', 30, 30], ['gamma', 30, 30]]);
      assert.equal(json.layoutOptions['org.eclipse.elk.direction'] ?? json.layoutOptions['elk.direction'], 'DOWN');
      // Back returns to the ELKT editor with the text
      await page.goBack();
      await page.waitForURL(/\/elkgraph\.html\?compressedContent=/);
      await svgHas(['alpha', 'beta', 'gamma']);
    });
  });

  describe('json.html', () => {
    it('renders the default JSON5 sample', async () => {
      await page.goto(`${base}json.html`);
      await statusOk();
      await svgHas(['n1', 'n2', 'n3']);
      assert.equal(await page.textContent('.navbar-title'), 'ELK JSON Editor');
      assert.match(await page.evaluate(() => window.elkLive.editor.getValue()), /layoutOptions: \{ 'algorithm': 'layered' \}/);
      assert.equal(await page.$$eval('#sprotty path.elkedge:not(.arrow)', (ps) => ps.length), 2);
    });

    it('marks a JSON5 syntax error', async () => {
      await page.evaluate(() => {
        const m = window.elkLive.editor.getModel();
        m.setValue(m.getValue().replace('{ id: "n3", width: 30, height: 30 }', '{ id: "n3", width: 30, height: 30 } }'));
      });
      await statusError();
      assert.match(await page.textContent('#status'), /^Parse error at 7:41: invalid character/);
      await page.waitForSelector('#monaco-editor .squiggly-error', { timeout: 10000 });
      const markers = await page.evaluate(() => window.elkLive.monaco.editor.getModelMarkers({}).map((m) => [m.startLineNumber, m.startColumn]));
      assert.deepEqual(markers, [[7, 41]]);
      await page.evaluate(() => {
        const m = window.elkLive.editor.getModel();
        m.setValue(m.getValue().replace('height: 30 } }', 'height: 30 }'));
      });
      await statusOk();
    });
  });

  describe('examples.html', () => {
    it('builds the table of contents and shows ?e=general/direction', async () => {
      await page.goto(`${base}examples.html?e=general/direction`);
      await svgHas(['leftToRight', 'topToBottom', 'rightToLeft', 'bottomToTop']);
      await statusOk();
      assert.equal(await page.textContent('#title'), 'Basics');
      assert.equal(await page.textContent('#title-small'), 'General > Direction');
      assert.ok((await page.textContent('#example-description')).length > 20);
      const index = JSON.parse(readFileSync(path.join(dist, 'examples/index.json'), 'utf8'));
      assert.equal(await page.$$eval('#toc button.sidebar-link', (bs) => bs.length), index.length);
      const headings = await page.$$eval('#toc .sidebar-heading', (hs) => hs.map((h) => h.textContent));
      assert.ok(headings.includes('General') && headings.includes('General > Direction'), headings.join(' | '));
      assert.equal(await page.getAttribute('#toc button[aria-current="true"]', 'data-path'), 'general/direction');
      const shot = process.env.ELK_LIVE_SCREENSHOT;
      if (shot) await page.screenshot({ path: shot });
    });

    it('exports SVG with the nodes', async () => {
      const [download] = await Promise.all([page.waitForEvent('download'), page.click('#svg-button')]);
      const text = readFileSync(await download.path(), 'utf8');
      assert.match(text, /^<\?xml/);
      assert.match(text, /viewBox="/);
      assert.ok(text.includes('id="sprotty_leftToRight"'));
      if (process.env.ELK_LIVE_SVG) writeFileSync(process.env.ELK_LIVE_SVG, text);
    });

    it('renders another TOC entry, updates the URL, and goes back', async () => {
      await page.click('#toc button[data-path="hierarchy/hierarchicalEdges"]');
      await page.waitForURL(/\/examples\.html\?e=hierarchy%2FhierarchicalEdges$/);
      await svgHas(['source', 'outside', 'inside']);
      await statusOk();
      assert.equal(await page.textContent('#title-small'), 'Hierarchy > Edges');
      // edits re-layout live
      await page.evaluate(() => {
        const m = window.elkLive.editor.getModel();
        m.setValue(`${m.getValue()}\nnode addedByTest`);
      });
      await svgHas(['addedByTest']);
      await page.goBack();
      // the URL this page was opened with is kept as typed (the slash is not re-encoded)
      await page.waitForURL(/\/examples\.html\?e=general(%2F|\/)direction$/);
      await svgHas(['leftToRight', 'topToBottom']);
      assert.equal(await page.textContent('#title-small'), 'General > Direction');
    });

    it('shows a random example without ?e= and leaves the URL alone (elk-live)', async () => {
      await page.goto(`${base}examples.html`);
      await statusOk();
      assert.ok((await page.textContent('#title')).length > 0);
      assert.match(page.url(), /\/examples\.html$/);
      // the choice is recorded as history state (Back/Forward), not in the URL
      const state = await page.evaluate(() => history.state);
      assert.equal(typeof state?.e, 'string');
    });
  });

  it('logs no page errors', () => {
    assert.deepEqual(errors, []);
  });
});
