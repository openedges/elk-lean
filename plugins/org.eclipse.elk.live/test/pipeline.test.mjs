// Smoke test of the app's pipeline without a DOM: the app's core modules (src/core/*.ts, loaded with
// Node's type stripping) driving the browser WASM build that the app serves (public/elk-lean/, the
// files the Web Worker loads), compared with the native CLI. Run `npm run assets` first (done by
// `npm run build` / `npm run dev`).
// SPDX-License-Identifier: EPL-2.0 OR GPL-3.0-or-later
import { describe, it, before } from 'node:test';
import assert from 'node:assert/strict';
import { createRequire } from 'node:module';
import { execFileSync } from 'node:child_process';
import { existsSync, readFileSync, readdirSync } from 'node:fs';
import path from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { runPipeline, parseElktError, parseJsonError } from '../src/core/pipeline.ts';
import { collectIds, elkToSprotty } from '../src/core/elk-to-sprotty.ts';
import { buildMetadata, contextAt, resolveOption } from '../src/core/options.ts';
import { parseElkex } from '../src/core/elkex.ts';
import { renderMarkdown } from '../src/core/markdown.ts';

const require = createRequire(import.meta.url);
const app = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const cli = process.env.ELK_LEAN_BIN || path.resolve(app, '../../.lake/build/bin/elk');
const pub = path.join(app, 'public');
const loader = path.join(pub, 'elk-lean/js/load-wasm.browser.mjs');
const haveAssets = existsSync(loader) && existsSync(path.join(pub, 'examples/index.json'));
const haveCli = existsSync(cli);

describe('pipeline (browser WASM build in Node)', { skip: !haveAssets ? 'run `npm run assets` first' : false }, () => {
  let elk;
  before(async () => {
    const { default: loadWasm } = await import(pathToFileURL(loader).href);
    const wasmBinary = readFileSync(path.join(pub, 'elk-lean/dist/wasm/elk_lean_core.wasm'));
    const backend = await loadWasm({ wasmBinary });
    const ELK = require('elk-lean/js/elk-api.js');
    elk = new ELK({ backend });
  });

  it('converts, lays out and renders every bundled example like the CLI', { skip: !haveCli ? `no CLI at ${cli}` : false }, async () => {
    const index = JSON.parse(readFileSync(path.join(pub, 'examples/index.json'), 'utf8'));
    assert.ok(index.length >= 40, `${index.length} examples`);
    let laidOut = 0;
    for (const entry of index) {
      const file = path.join(pub, 'examples', `${entry.path}.elkt`);
      const ex = parseElkex(entry.path, readFileSync(file, 'utf8'));
      assert.equal(ex.label, entry.label);
      const result = await runPipeline(elk, ex.graph, 'elkt');
      // the CLI on the whole file (the graph section is the file minus comments)
      let expected;
      try {
        expected = JSON.parse(execFileSync(cli, ['layout', file, '--defaults'], { encoding: 'utf8', maxBuffer: 64 << 20, stdio: ['ignore', 'pipe', 'pipe'] }));
      } catch (e) {
        assert.equal(result.ok, false, `${entry.path}: CLI failed (${e.stderr}) but the app laid out`);
        continue;
      }
      assert.equal(result.ok, true, `${entry.path}: ${result.diagnostic?.message}`);
      assert.deepEqual(result.laidOut, expected, entry.path);
      // every node, port and edge id reaches the sprotty model
      const ids = new Set(collectIds(result.model));
      const visit = (n) => {
        for (const c of n.children ?? []) { assert.ok(ids.has(c.id), `${entry.path}: node ${c.id}`); visit(c); }
        for (const p of n.ports ?? []) assert.ok(ids.has(p.id), `${entry.path}: port ${p.id}`);
        for (const e of n.edges ?? []) assert.ok(ids.has(e.id), `${entry.path}: edge ${e.id}`);
      };
      visit(result.laidOut);
      laidOut++;
    }
    console.log(`# ${laidOut}/${index.length} examples laid out identically to \`elk layout X.elkt --defaults\``);
    assert.ok(laidOut >= index.length - 2);
  });

  it('reports parse errors with line and column, layout errors as layout', async () => {
    const r = await runPipeline(elk, 'node a\nedge a -> \n', 'elkt');
    assert.equal(r.ok, false);
    assert.deepEqual([r.diagnostic.kind, r.diagnostic.line, r.diagnostic.column], ['parse', 3, 1]);
    const l = await runPipeline(elk, 'algorithm: foo.bar\nnode a', 'elkt');
    assert.equal(l.ok, false);
    assert.equal(l.diagnostic.kind, 'layout');
    assert.match(l.diagnostic.message, /UnsupportedConfigurationException/);
    const j = await runPipeline(elk, '{"id": "root", "children": [}', 'json');
    assert.equal(j.diagnostic.kind, 'parse');
    assert.deepEqual([j.diagnostic.line, j.diagnostic.column], [1, 29]);
    const ok = await runPipeline(elk, JSON.stringify({ id: 'root', children: [{ id: 'a', width: 10, height: 10 }] }), 'json');
    assert.equal(ok.ok, true);
  });

  it('knownLayoutOptions + the enum snapshot give completion metadata', async () => {
    const choices = JSON.parse(readFileSync(path.join(app, 'src/generated/option-choices.json'), 'utf8'));
    const meta = buildMetadata(await elk.knownLayoutOptions(), await elk.knownLayoutAlgorithms(), choices);
    const ids = new Set(meta.options.map((o) => o.id));
    for (const id of Object.keys(choices)) assert.ok(ids.has(id), `snapshot option ${id} is registered`);
    assert.deepEqual(resolveOption(meta, 'direction').choices, ['UNDEFINED', 'RIGHT', 'LEFT', 'DOWN', 'UP']);
    assert.equal(resolveOption(meta, 'elk.direction').id, 'org.eclipse.elk.direction');
    assert.ok(meta.algorithms.some((a) => a.shortId === 'layered' && a.knownOptions.length > 50));
    if (haveCli) {
      const fresh = {};
      for (const o of JSON.parse(execFileSync(cli, ['options', '--choices'], { encoding: 'utf8', maxBuffer: 64 << 20 }))
        .sort((a, b) => a.id.localeCompare(b.id))) {
        if (o.choices?.length) fresh[o.id] = o.choices;
      }
      assert.deepEqual(choices, fresh, 'src/generated/option-choices.json is stale: npm run gen:choices');
    }
  });
});

describe('core helpers', () => {
  it('parseElktError / parseJsonError', () => {
    assert.deepEqual(parseElktError("ELK Text parse error: 3:7: mismatched input '}'"),
      { kind: 'parse', message: "mismatched input '}'", line: 3, column: 7 });
    assert.deepEqual(parseElktError('weird'), { kind: 'parse', message: 'weird' });
    const d = parseJsonError('Unexpected token } in JSON at position 12', '{\n  "a": 1,\n}');
    assert.deepEqual([d.line, d.column], [3, 1]);
  });

  it('contextAt finds the enclosing element and algorithm', () => {
    assert.equal(contextAt('algorithm: layered\n').element, 'root');
    assert.deepEqual(contextAt('algorithm: layered\nnode a {\n  algorithm: mrtree\n  port p {\n').algorithms, ['mrtree', 'layered']);
    assert.equal(contextAt('node a {\n  port p {\n').element, 'port');
    assert.equal(contextAt('node a {\n  port p { }\n  ').element, 'node');
    assert.equal(contextAt('edge a -> b {\n').element, 'edge');
    assert.equal(contextAt('node a {\n  label "x {" {\n').element, 'label');
    assert.equal(contextAt('node a {\n  layout [ size: 3, ').inLayoutBlock, true);
    assert.equal(contextAt('node a { // {\n').element, 'node');
  });

  it('elkToSprotty keeps positions relative to the parent and edges under their container', () => {
    const g = {
      id: 'root', width: 100, height: 100,
      children: [{
        id: 'p', x: 10, y: 20, width: 50, height: 50,
        labels: [{ text: 'P', x: 1, y: 2, width: 9, height: 16 }],
        ports: [{ id: 'pp', x: 45, y: 5, width: 5, height: 5 }],
        children: [{ id: 'c1', x: 5, y: 5, width: 10, height: 10 }, { id: 'c2', x: 30, y: 5, width: 10, height: 10 }],
      }],
      edges: [{
        id: 'e', sources: ['c1'], targets: ['c2'], container: 'p', junctionPoints: [{ x: 20, y: 10 }],
        sections: [{ id: 's', startPoint: { x: 15, y: 10 }, bendPoints: [{ x: 20, y: 10 }], endPoint: { x: 30, y: 10 } }],
        labels: [{ text: 'L', x: 18, y: 0, width: 9, height: 16 }],
      }],
    };
    const m = elkToSprotty(g);
    const p = m.children[0];
    assert.deepEqual([p.id, p.position], ['p', { x: 10, y: 20 }]);
    assert.deepEqual(p.children.map((c) => `${c.type}:${c.id}`), ['port:pp', 'label:p_label0', 'node:c1', 'node:c2', 'edge:e']);
    const e = p.children[4];
    assert.deepEqual(e.routingPoints, [{ x: 15, y: 10 }, { x: 20, y: 10 }, { x: 30, y: 10 }]);
    assert.deepEqual(e.children.map((c) => c.type), ['junction', 'label']);
    assert.equal(e.arrow, true);
  });

  it('parseElkex and renderMarkdown', () => {
    const ex = parseElkex('general/x', '/*\n// elkex:category\nA > B\n\n// elkex:label\nX\n\n// elkex:doc\nSome `code` and _emph_.\n*/\n// elkex:graph\nnode a\n');
    assert.deepEqual([ex.label, ex.category, ex.graph], ['X', ['A', 'B'], 'node a']);
    assert.equal(renderMarkdown(ex.doc), '<p>Some <code>code</code> and <em>emph</em>.</p>');
    assert.equal(renderMarkdown('<script>x</script> [l](javascript:alert(1))'), '<p>&lt;script&gt;x&lt;/script&gt; l)</p>');
  });
});

describe('static build', { skip: !existsSync(path.join(app, 'dist/index.html')) ? 'run `npm run build` first' : false }, () => {
  it('dist/ holds the page, the bundle, the worker, the WASM and the examples', () => {
    const html = readFileSync(path.join(app, 'dist/index.html'), 'utf8');
    assert.match(html, /<script type="module" crossorigin src="\.\/assets\/index-[\w-]+\.js">/);
    for (const f of ['elk-lean/js/elk-worker.js', 'elk-lean/js/load-wasm.browser.mjs', 'elk-lean/dist/wasm/elk_lean_core.mjs',
      'elk-lean/dist/wasm/elk_lean_core.wasm', 'examples/index.json', 'examples/general/direction.elkt', 'favicon.svg']) {
      assert.ok(existsSync(path.join(app, 'dist', f)), f);
    }
    assert.ok(readdirSync(path.join(app, 'dist/assets')).some((f) => f.startsWith('editor.worker')));
  });
});
