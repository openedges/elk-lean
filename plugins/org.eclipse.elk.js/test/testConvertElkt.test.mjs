// elk-lean `convertElkt` (ELK Text -> ELK JSON, an elk-lean addition to the elkjs API): every
// `.elkt` file of external/elk-models converted by the native addon and by the WASM backend must be
// byte-identical to the CLI `elk convert` (plain, and with `--defaults --sort-keys`); syntax errors
// carry the CLI's message with line and column; the npm API resolves the parsed graph in direct,
// fake-worker and worker_threads modes.
// SPDX-License-Identifier: EPL-2.0 OR GPL-3.0-or-later
import { describe, it, before } from 'node:test';
import assert from 'node:assert/strict';
import { createRequire } from 'node:module';
import { fileURLToPath } from 'node:url';
import path from 'node:path';
import { execFile, execFileSync } from 'node:child_process';
import { existsSync, readdirSync, readFileSync, statSync, writeFileSync, mkdtempSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';

const require = createRequire(import.meta.url);
const __dirname = path.dirname(fileURLToPath(import.meta.url));
const repo = path.resolve(__dirname, '../../..');
const cli = process.env.ELK_LEAN_BIN || path.join(repo, '.lake/build/bin/elk');

/** external/elk-models of this checkout, else of the main checkout (git worktrees). */
function modelsDir() {
  if (process.env.ELK_MODELS_DIR) return process.env.ELK_MODELS_DIR;
  const local = path.join(repo, 'external/elk-models');
  if (existsSync(path.join(local, 'examples'))) return local;
  try {
    const common = execFileSync('git', ['-C', repo, 'rev-parse', '--path-format=absolute', '--git-common-dir'],
      { encoding: 'utf8' }).trim();
    const main = path.join(path.dirname(common), 'external/elk-models');
    if (existsSync(path.join(main, 'examples'))) return main;
  } catch (e) { /* not a git checkout */ }
  return null;
}

function listElkt(dir) {
  const out = [];
  const walk = (d) => {
    for (const name of readdirSync(d).sort()) {
      const p = path.join(d, name);
      if (statSync(p).isDirectory()) walk(p);
      else if (name.endsWith('.elkt')) out.push(p);
    }
  };
  walk(dir);
  return out;
}

/** `elk convert <file> [args]`: { ok, text } with the trailing newline of the CLI removed. */
function runCli(file, args) {
  return new Promise((resolve) => {
    execFile(cli, ['convert', file, ...args], { encoding: 'utf8', maxBuffer: 256 * 1024 * 1024 },
      (err, stdout, stderr) => {
        if (err && typeof err.code !== 'number') resolve({ ok: false, text: String(err) });
        else if (err) resolve({ ok: false, text: stderr.replace(/\n$/, '') });
        else resolve({ ok: true, text: stdout.replace(/\n$/, '') });
      });
  });
}

async function pool(items, n, fn) {
  const results = new Array(items.length);
  let next = 0;
  await Promise.all(Array.from({ length: n }, async () => {
    while (next < items.length) {
      const i = next++;
      results[i] = await fn(items[i], i);
    }
  }));
  return results;
}

function callBackend(backend, text, flags) {
  try {
    return { ok: true, text: backend.convert_elkt(text, flags) };
  } catch (e) {
    return { ok: false, text: e.message };
  }
}

const { loadNativeAddon } = require('../js/load-native.js');
const addon = loadNativeAddon();
const wasmBuilt = existsSync(path.join(__dirname, '../dist/wasm-node/elk_lean.cjs'));
const wasm = wasmBuilt ? require('../js/load-wasm.js')() : null;
const models = modelsDir();
const haveCli = existsSync(cli);

// flag sets: `elk convert X` and `elk convert X --defaults --sort-keys`
const VARIANTS = [{ flags: 0, args: [] }, { flags: 5, args: ['--defaults', '--sort-keys'] }];

const ERROR_CASES = [
  'node a\nedge a -> \n',
  'node a {\n  label "x"\n',
  'node a\nnode b\nedge a -> c\n',
  'graph g\nalgorithm layered\n',
  'node n1 { layout [ position: 1, ] }\n',
  'edge -> b\n',
  '"unterminated\n',
];

describe('convertElkt', { skip: !haveCli ? `CLI not built (${cli})` : false }, () => {
  const files = models ? listElkt(models) : [];
  const expected = new Map(); // `${variant}:${file}` -> CLI result

  before(async () => {
    const jobs = [];
    for (const f of files) for (let v = 0; v < VARIANTS.length; v++) jobs.push([f, v]);
    await pool(jobs, 6, async ([f, v]) => {
      expected.set(`${v}:${f}`, await runCli(f, VARIANTS[v].args));
    });
  });

  for (const [name, backend, reason] of [
    ['native addon', addon, 'native addon not built (sh scripts/build_napi.sh)'],
    ['WASM', wasm, 'WASM backend not built (sh scripts/build_wasm.sh)'],
  ]) {
    it(`${name}: every external/elk-models .elkt is byte-identical to elk convert`,
      { skip: !backend ? reason : !models ? 'external/elk-models not found (ELK_MODELS_DIR)' : false }, () => {
        assert.ok(files.length >= 800, `found ${files.length} .elkt files under ${models}`);
        let same = 0;
        let errors = 0;
        const diffs = [];
        for (const f of files) {
          const text = readFileSync(f, 'utf8');
          for (let v = 0; v < VARIANTS.length; v++) {
            const want = expected.get(`${v}:${f}`);
            const got = callBackend(backend, text, VARIANTS[v].flags);
            if (got.ok === want.ok && got.text === want.text) {
              same++;
              if (!got.ok) errors++;
            } else if (diffs.length < 5) {
              diffs.push(`${path.relative(models, f)} flags ${VARIANTS[v].flags}: ${got.ok}/${want.ok} `
                + `${got.text.slice(0, 120)} vs ${want.text.slice(0, 120)}`);
            }
          }
        }
        console.log(`# ${name}: ${same}/${files.length * VARIANTS.length} identical `
          + `(${files.length} files x ${VARIANTS.length} flag sets, ${errors} identical errors)`);
        assert.deepEqual(diffs, []);
        assert.equal(same, files.length * VARIANTS.length);
      });

    it(`${name}: syntax errors carry the CLI message with line and column`,
      { skip: !backend ? reason : false }, async () => {
        const dir = mkdtempSync(path.join(tmpdir(), 'elk-lean-convert-'));
        try {
          for (const [i, text] of ERROR_CASES.entries()) {
            const file = path.join(dir, `e${i}.elkt`);
            writeFileSync(file, text);
            const want = await runCli(file, []);
            const got = callBackend(backend, text, 0);
            assert.equal(want.ok, false, `CLI accepted ${JSON.stringify(text)}`);
            assert.equal(got.ok, false, `${name} accepted ${JSON.stringify(text)}`);
            assert.equal(got.text, want.text);
            assert.match(got.text, /^ELK Text parse error: \d+:\d+: \S/);
          }
        } finally {
          rmSync(dir, { recursive: true, force: true });
        }
      });
  }

  it('native addon: argument checks', { skip: !addon ? 'native addon not built' : false }, () => {
    assert.throws(() => addon.convert_elkt(42), TypeError);
    assert.throws(() => addon.convert_elkt('node a', 'x'), TypeError);
    assert.equal(addon.convert_elkt('node a'), addon.convert_elkt('node a', 0));
  });

  describe('npm API', () => {
    const sample = 'algorithm: layered\nnode a { label "A" }\nnode b { port p }\nedge a -> b.p\n';
    let plain;
    let defaults;
    before(async () => {
      const dir = mkdtempSync(path.join(tmpdir(), 'elk-lean-convert-'));
      try {
        writeFileSync(path.join(dir, 's.elkt'), sample);
        plain = JSON.parse((await runCli(path.join(dir, 's.elkt'), [])).text);
        defaults = JSON.parse((await runCli(path.join(dir, 's.elkt'), ['--defaults'])).text);
      } finally {
        rmSync(dir, { recursive: true, force: true });
      }
    });

    const ELK = require('../js/index.js');
    const API = require('../js/elk-api.js');
    const FakeWorker = require('../js/elk-worker.js').Worker;
    const modes = [
      ['direct', () => new ELK()],
      ['fake worker', () => new API({ workerFactory: () => new FakeWorker() })],
      ['worker_threads', () => new ELK({ workerUrl: path.join(__dirname, '../js/elk-worker.js') })],
    ];
    for (const [mode, make] of modes) {
      it(`${mode}: resolves the graph, rejects syntax errors`, { skip: !addon && !wasm ? 'no backend built' : false },
        async () => {
          const elk = make();
          try {
            assert.deepEqual(await elk.convertElkt(sample), plain);
            assert.deepEqual(await elk.convertElkt(sample, { defaults: true }), defaults);
            await assert.rejects(elk.convertElkt('node a\nedge a -> \n'),
              // worker modes reject with { message } like elkjs' layout errors
              (err) => /^ELK Text parse error: 3:1: /.test(err.message));
            await assert.rejects(elk.convertElkt(42), TypeError);
            // the converted graph lays out like the CLI's (`elk layout X.elkt --defaults`)
            const laid = await elk.layout(await elk.convertElkt(sample, { defaults: true }));
            assert.equal(laid.children.length, 2);
            assert.ok(laid.children.every((c) => Number.isFinite(c.x) && c.width === 30));
          } finally {
            elk.terminateWorker();
          }
        });
    }
  });
});
