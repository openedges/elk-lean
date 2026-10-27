#!/usr/bin/env node
/**
 * elk-lean JS parity: lays out every model under a directory through the native addon
 * (layout_json(graph, "{}")) and compares the result string byte for byte with the output of the
 * native CLI (`elk layout MODEL --sort-keys`; one trailing newline of the CLI output is ignored).
 * Both engines failing with the same message counts as a match.
 *
 *   node test/parity/run.mjs --models <dir> [--ext json|elkt] [--elkt-cache <dir>]
 *     [--cli <elk binary>] [--backend <addon .node>] [--output <dir>] [--jobs N]
 *     [--limit N] [--filter SUBSTR] [--timing K] [--repeat R]
 *     [--elkjs [<elkjs package dir>]] [--tolerance T]
 *
 * --ext elkt      lays out the .elkt models instead, converted first with `elk convert X.elkt -o`
 *                 into --elkt-cache (default <output>/elkt_json); both engines read the converted JSON
 * --timing K      afterwards times the K largest models: addon (in-process, median of R runs after a
 *                 warm-up) vs CLI (process wall time including start-up, median of R runs)
 * --elkjs [dir]   optional structural comparison (numeric tolerance) against elkjs, loaded from dir
 *                 or resolved as the `elkjs` package; skipped when it cannot be loaded
 *
 * Writes <output>/summary.json and <output>/details.tsv (default output: test/parity/results).
 * Exit code 0 when every model matches the CLI, 1 otherwise, 2 on setup errors.
 *
 * SPDX-License-Identifier: EPL-2.0 OR GPL-3.0-or-later
 */
import { readFile, writeFile, mkdir, stat } from 'node:fs/promises';
import { readdirSync, existsSync } from 'node:fs';
import { join, relative, resolve, dirname } from 'node:path';
import { fileURLToPath } from 'node:url';
import { createRequire } from 'node:module';
import { execFile } from 'node:child_process';
import { availableParallelism } from 'node:os';
import { stripInternal, deepCompare } from './compare.mjs';

const require = createRequire(import.meta.url);
const PKG_ROOT = fileURLToPath(new URL('../..', import.meta.url));
const REPO_ROOT = resolve(PKG_ROOT, '../..');
const args = process.argv.slice(2);
function getArg(name, fallback) {
  const idx = args.indexOf(name);
  return idx === -1 ? fallback : args[idx + 1];
}
function hasArg(name) { return args.includes(name); }

const MODELS_DIR = resolve(getArg('--models', join(REPO_ROOT, 'external/elk-models/realworld')));
const EXT = getArg('--ext', 'json');
const REPORT_DIR = resolve(getArg('--output', join(PKG_ROOT, 'test/parity/results')));
const ELKT_CACHE = resolve(getArg('--elkt-cache', join(REPORT_DIR, 'elkt_json')));
const CLI = resolve(getArg('--cli', join(REPO_ROOT, '.lake/build/bin/elk')));
const BACKEND_PATH = getArg('--backend', null);
const JOBS = Math.max(1, Number(getArg('--jobs', String(Math.max(1, availableParallelism() - 2)))));
const LIMIT = Number(getArg('--limit', '0'));
const FILTER = getArg('--filter', '');
const TIMING = Number(getArg('--timing', '0'));
const REPEAT = Math.max(1, Number(getArg('--repeat', '5')));
const TOLERANCE = Number(getArg('--tolerance', '1e-6'));
const ELKJS = hasArg('--elkjs');
const ELKJS_DIR = (() => {
  const v = getArg('--elkjs', null);
  return v && !v.startsWith('--') ? resolve(v) : null;
})();

function findFiles(dir, ext) {
  return readdirSync(dir, { withFileTypes: true }).flatMap(entry => {
    const path = join(dir, entry.name);
    if (entry.name.startsWith('.')) return [];
    return entry.isDirectory() ? findFiles(path, ext) : entry.name.endsWith('.' + ext) ? [path] : [];
  });
}

function run(cmd, argv) {
  return new Promise(resolvePromise => {
    const t0 = process.hrtime.bigint();
    execFile(cmd, argv, { maxBuffer: 1 << 30, encoding: 'utf8' }, (error, stdout, stderr) => {
      const ms = Number(process.hrtime.bigint() - t0) / 1e6;
      resolvePromise({ ok: !error, stdout, stderr, ms, code: error ? error.code : 0 });
    });
  });
}

async function pool(items, jobs, fn) {
  let next = 0;
  const workers = Array.from({ length: Math.min(jobs, items.length) }, async () => {
    while (next < items.length) {
      const i = next++;
      await fn(items[i], i);
    }
  });
  await Promise.all(workers);
}

function firstLine(s) { return String(s).trim().split('\n')[0]; }

function loadBackend() {
  if (BACKEND_PATH) return require(resolve(BACKEND_PATH));
  const errors = [];
  const backend = require(join(PKG_ROOT, 'js/load-native.js')).loadNativeAddon(errors);
  if (!backend) throw new Error('native addon not found (sh scripts/build_napi.sh):\n  ' + errors.join('\n  '));
  return backend;
}

function loadElkjs() {
  try {
    const ELKjs = ELKJS_DIR ? require(ELKJS_DIR) : require('elkjs');
    const pkg = ELKJS_DIR ? require(join(ELKJS_DIR, 'package.json')) : require('elkjs/package.json');
    return { engine: new ELKjs(), version: pkg.version };
  } catch (error) {
    console.log(`elkjs comparison skipped: ${firstLine(error.message)}`);
    return null;
  }
}

function median(values) {
  const s = [...values].sort((a, b) => a - b);
  return s.length % 2 ? s[(s.length - 1) / 2] : (s[s.length / 2 - 1] + s[s.length / 2]) / 2;
}

async function main() {
  if (!existsSync(CLI)) throw new Error(`CLI not found: ${CLI} (lake build)`);
  if (EXT !== 'json' && EXT !== 'elkt') throw new Error('--ext must be json or elkt');
  const backend = loadBackend();
  let sources = findFiles(MODELS_DIR, EXT).map(p => relative(MODELS_DIR, p).split('\\').join('/')).sort();
  if (FILTER) sources = sources.filter(m => m.includes(FILTER));
  if (LIMIT > 0) sources = sources.slice(0, LIMIT);
  if (!sources.length) throw new Error(`No .${EXT} models found in ${MODELS_DIR}`);
  console.log(`elk-lean JS parity: ${sources.length} .${EXT} models under ${MODELS_DIR}`);
  console.log(`addon: ${BACKEND_PATH ? resolve(BACKEND_PATH) : 'automatic (js/load-native.js)'}, CLI: ${CLI}, jobs: ${JOBS}`);

  // .elkt: convert with the CLI first (both engines then read the same JSON)
  const models = [];
  const convertErrors = [];
  if (EXT === 'elkt') {
    await pool(sources, JOBS, async model => {
      const dst = join(ELKT_CACHE, model.replace(/\.elkt$/, '.json'));
      const src = join(MODELS_DIR, model);
      try {
        const [s, d] = await Promise.all([stat(src), stat(dst).catch(() => null)]);
        if (d && d.mtimeMs >= s.mtimeMs) { models.push({ model, path: dst }); return; }
      } catch (e) { /* convert below */ }
      await mkdir(dirname(dst), { recursive: true });
      const r = await run(CLI, ['convert', src, '-o', dst]);
      if (r.ok) models.push({ model, path: dst });
      else convertErrors.push({ model, error: firstLine(r.stderr || r.stdout) });
    });
    models.sort((a, b) => a.model < b.model ? -1 : a.model > b.model ? 1 : 0);
    console.log(`converted ${models.length} models (${convertErrors.length} conversion errors)`);
  } else {
    for (const model of sources) models.push({ model, path: join(MODELS_DIR, model) });
  }

  const stats = { identical: 0, different: 0, bothErrorSame: 0, bothErrorDifferent: 0, addonErrorOnly: 0, cliErrorOnly: 0 };
  const rows = [];
  let addonMs = 0, cliMs = 0, done = 0;
  await pool(models, JOBS, async ({ model, path }) => {
    const text = await readFile(path, 'utf8');
    const cliPromise = run(CLI, ['layout', path, '--sort-keys']);
    let addonOut = null, addonErr = null;
    const t0 = process.hrtime.bigint();
    try { addonOut = backend.layout_json(text, '{}'); } catch (e) { addonErr = e && e.message ? e.message : String(e); }
    const aMs = Number(process.hrtime.bigint() - t0) / 1e6;
    const cli = await cliPromise;
    const cliOut = cli.ok ? cli.stdout.replace(/\n$/, '') : null;
    const cliErr = cli.ok ? null : firstLine(cli.stderr || cli.stdout || `exit ${cli.code}`);
    let status;
    let detail = '';
    if (addonErr === null && cliErr === null) {
      if (addonOut === cliOut) status = 'identical';
      else {
        status = 'different';
        let i = 0;
        while (i < addonOut.length && addonOut[i] === cliOut[i]) i++;
        detail = `first difference at byte ${i}: addon ${JSON.stringify(addonOut.slice(i, i + 40))} cli ${JSON.stringify(cliOut.slice(i, i + 40))}`;
      }
    } else if (addonErr !== null && cliErr !== null) {
      // the CLI prefixes its message (e.g. "error: "); compare the engine message only
      status = cliErr.includes(firstLine(addonErr)) ? 'bothErrorSame' : 'bothErrorDifferent';
      detail = `addon: ${firstLine(addonErr)} | cli: ${cliErr}`;
    } else if (addonErr !== null) {
      status = 'addonErrorOnly';
      detail = firstLine(addonErr);
    } else {
      status = 'cliErrorOnly';
      detail = cliErr;
    }
    stats[status]++;
    addonMs += aMs;
    cliMs += cli.ms;
    rows.push({ model, path, status, addonMs: aMs, cliMs: cli.ms, bytes: text.length, detail, addonOut: ELKJS || addonOut === null ? addonOut : "" });
    done++;
    if (status !== 'identical' && status !== 'bothErrorSame') console.log(`[${done}/${models.length}] ${status} ${model}: ${detail}`);
    else if (done % 200 === 0) console.log(`[${done}/${models.length}]`);
  });
  rows.sort((a, b) => a.model < b.model ? -1 : a.model > b.model ? 1 : 0);

  const summary = {
    modelsDir: MODELS_DIR, ext: EXT, total: sources.length, compared: models.length,
    conversionErrors: convertErrors.length, ...stats,
    matches: stats.identical + stats.bothErrorSame,
    addonTotalMs: Math.round(addonMs), cliTotalWallMs: Math.round(cliMs),
  };

  // optional elkjs comparison (structural, numeric tolerance)
  if (ELKJS) {
    const elkjs = loadElkjs();
    if (elkjs) {
      const js = { match: 0, drift: 0, elkjsErrorOnly: 0, leanErrorOnly: 0, bothError: 0, version: elkjs.version };
      for (const row of rows) {
        const graph = JSON.parse(await readFile(row.path, 'utf8'));
        let jsOut = null, jsErr = null;
        try { jsOut = await elkjs.engine.layout(graph); } catch (e) { jsErr = e && e.message ? e.message : String(e); }
        const leanOk = row.addonOut !== null;
        if (jsErr !== null && !leanOk) js.bothError++;
        else if (jsErr !== null) js.elkjsErrorOnly++;
        else if (!leanOk) js.leanErrorOnly++;
        else {
          const diffs = deepCompare(stripInternal(jsOut), stripInternal(JSON.parse(row.addonOut)), '', TOLERANCE);
          if (diffs.length) { js.drift++; row.elkjs = `drift (${diffs.length} diffs, first ${diffs[0].path})`; }
          else js.match++;
        }
      }
      summary.elkjs = js;
    }
  }

  // timing on the largest models
  if (TIMING > 0) {
    const candidates = rows.filter(r => r.status === 'identical').sort((a, b) => b.bytes - a.bytes).slice(0, TIMING);
    summary.timing = [];
    for (const row of candidates) {
      const text = await readFile(row.path, 'utf8');
      backend.layout_json(text, '{}');
      const addonRuns = [];
      for (let i = 0; i < REPEAT; i++) {
        const t0 = process.hrtime.bigint();
        backend.layout_json(text, '{}');
        addonRuns.push(Number(process.hrtime.bigint() - t0) / 1e6);
      }
      const cliRuns = [];
      for (let i = 0; i < REPEAT; i++) cliRuns.push((await run(CLI, ['layout', row.path, '--sort-keys'])).ms);
      const entry = { model: row.model, bytes: row.bytes, addonMedianMs: +median(addonRuns).toFixed(2),
        cliMedianWallMs: +median(cliRuns).toFixed(2) };
      summary.timing.push(entry);
      console.log(`timing ${entry.model} (${entry.bytes} B): addon ${entry.addonMedianMs} ms, CLI ${entry.cliMedianWallMs} ms (wall, incl. start-up)`);
    }
    const t0 = process.hrtime.bigint();
    await run(CLI, ['--version']);
    summary.cliStartupMs = +(Number(process.hrtime.bigint() - t0) / 1e6).toFixed(2);
  }

  await mkdir(REPORT_DIR, { recursive: true });
  await writeFile(join(REPORT_DIR, 'summary.json'), JSON.stringify(summary, null, 2) + '\n');
  await writeFile(join(REPORT_DIR, 'details.tsv'),
    'model\tstatus\taddon_ms\tcli_wall_ms\tdetail\n'
    + rows.map(r => [r.model, r.status, r.addonMs.toFixed(2), r.cliMs.toFixed(2),
      (r.detail + (r.elkjs ? ` | elkjs ${r.elkjs}` : '')).replace(/[\t\n]/g, ' ')].join('\t')).join('\n') + '\n'
    + convertErrors.map(c => `${c.model}\tconversionError\t\t\t${c.error.replace(/[\t\n]/g, ' ')}`).join('\n'));
  console.log(JSON.stringify(summary, null, 2));
  process.exitCode = summary.matches === summary.compared ? 0 : 1;
}

main().catch(error => {
  console.error(error);
  process.exitCode = 2;
});
