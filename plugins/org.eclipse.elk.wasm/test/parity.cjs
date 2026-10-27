'use strict';
/*
 * WASM vs native parity of elk-lean (PLAN.md 6.5, Phase 8).
 *
 * Lays out every `.json` model under MODELS_DIR through the WASM backend (js/load-wasm.js, the
 * emscripten Node build in dist/wasm-node/) and compares the result string byte for byte with the
 * output of the native CLI `elk layout MODEL --sort-keys` (both serialise like elk-rs: compact,
 * keys sorted). Errors are compared by message. Timing: in-process layout time per model of the
 * WASM backend vs the native `elk bench --mode models` (same models, same iteration counts).
 *
 * usage: node plugins/org.eclipse.elk.wasm/test/parity.cjs [--models DIR] [--elk PATH]
 *          [--limit N] [--iterations N] [--warmup N] [--no-timing] [--report FILE.tsv]
 *          [--module elk_lean.cjs]
 * defaults: --models external/elk-models/realworld, --elk .lake/build/bin/elk, --iterations 3,
 *           --warmup 1. Exit code 0 iff every model is identical (or fails identically).
 *
 * SPDX-License-Identifier: EPL-2.0 OR GPL-3.0-or-later
 */
const fs = require('fs');
const os = require('os');
const path = require('path');
const { spawnSync } = require('child_process');

const ROOT = path.resolve(__dirname, '..', '..', '..');

function parseArgs(argv) {
  const a = {
    models: path.join(ROOT, 'external', 'elk-models', 'realworld'),
    elk: path.join(ROOT, '.lake', 'build', 'bin', 'elk'),
    limit: 0, iterations: 3, warmup: 1, timing: true, report: null, module: null,
  };
  for (let i = 0; i < argv.length; i++) {
    const k = argv[i];
    const v = () => argv[++i];
    if (k === '--models') a.models = path.resolve(v());
    else if (k === '--elk') a.elk = path.resolve(v());
    else if (k === '--limit') a.limit = Number(v());
    else if (k === '--iterations') a.iterations = Math.max(1, Number(v()));
    else if (k === '--warmup') a.warmup = Number(v());
    else if (k === '--no-timing') a.timing = false;
    else if (k === '--report') a.report = path.resolve(v());
    else if (k === '--module') a.module = path.resolve(v());
    else { console.error('unknown argument ' + k); process.exit(2); }
  }
  return a;
}

function walk(dir) {
  const out = [];
  for (const e of fs.readdirSync(dir, { withFileTypes: true })) {
    const p = path.join(dir, e.name);
    if (e.isDirectory()) out.push(...walk(p));
    else if (e.name.endsWith('.json')) out.push(p);
  }
  return out;
}

// `elk bench` scenario name of a model (PerfBenchmark.loadModelsFromDir).
function benchName(dir, file) {
  return path.relative(dir, file).replace(/\.json$/, '').replace(/[\\/]/g, '_');
}

function firstDiff(a, b) {
  const n = Math.min(a.length, b.length);
  for (let i = 0; i < n; i++) if (a[i] !== b[i]) return i;
  return n;
}

function main() {
  const a = parseArgs(process.argv.slice(2));
  let files = walk(a.models).sort();
  if (a.limit > 0) files = files.slice(0, a.limit);

  const t0 = process.hrtime.bigint();
  // default: the npm loader (dist/wasm-node); --module: another emscripten Node build (experiments)
  const backend = a.module ? require(a.module).createBackend() : require('../js/load-wasm.js')();
  const initMs = Number(process.hrtime.bigint() - t0) / 1e6;
  console.log(`elk-lean WASM ${backend.version}: init ${initMs.toFixed(1)} ms, ${files.length} models from ${path.relative(ROOT, a.models) || a.models}`);

  const rows = [];
  const counts = { identical: 0, different: 0, bothError: 0, errorMismatch: 0 };
  let nativeWallMs = 0;
  let wasmFirstMs = 0;
  for (const file of files) {
    const rel = path.relative(a.models, file);
    const text = fs.readFileSync(file, 'utf8');
    const s0 = process.hrtime.bigint();
    const nat = spawnSync(a.elk, ['layout', file, '--sort-keys'], { maxBuffer: 1 << 30 });
    nativeWallMs += Number(process.hrtime.bigint() - s0) / 1e6;
    let natOut = null;
    let natErr = null;
    if (nat.status === 0) {
      natOut = nat.stdout;
      if (natOut.length && natOut[natOut.length - 1] === 0x0a) natOut = natOut.subarray(0, natOut.length - 1);
    } else {
      natErr = nat.stderr.toString('utf8').trim() || ('exit ' + nat.status);
    }
    let wasmOut = null;
    let wasmErr = null;
    const w0 = process.hrtime.bigint();
    try {
      wasmOut = Buffer.from(backend.layout_json(text, '{}'), 'utf8');
    } catch (e) {
      wasmErr = e && e.message !== undefined ? e.message : String(e);
    }
    wasmFirstMs += Number(process.hrtime.bigint() - w0) / 1e6;
    let status;
    let detail = '';
    if (natOut && wasmOut) {
      if (natOut.equals(wasmOut)) status = 'identical';
      else {
        status = 'different';
        const i = firstDiff(natOut, wasmOut);
        detail = `first difference at byte ${i}: native ${JSON.stringify(natOut.subarray(Math.max(0, i - 40), i + 40).toString())} wasm ${JSON.stringify(wasmOut.subarray(Math.max(0, i - 40), i + 40).toString())}`;
      }
    } else if (natErr !== null && wasmErr !== null) {
      // the CLI prints `error: <message>`
      const same = natErr === wasmErr || natErr.endsWith(wasmErr);
      status = same ? 'bothError' : 'errorMismatch';
      detail = same ? wasmErr.slice(0, 200) : `native: ${natErr.slice(0, 200)} | wasm: ${wasmErr.slice(0, 200)}`;
    } else {
      status = 'errorMismatch';
      detail = natErr !== null ? `native error: ${natErr.slice(0, 300)}` : `wasm error: ${wasmErr.slice(0, 300)}`;
    }
    counts[status]++;
    rows.push({ rel, name: benchName(a.models, file), status, detail, text });
    if (status !== 'identical') console.log(`  ${status}: ${rel}${detail ? ' — ' + detail : ''}`);
  }
  console.log(`parity: ${files.length} models, identical ${counts.identical}, different ${counts.different}, ` +
    `error (same message on both sides) ${counts.bothError}, error mismatch ${counts.errorMismatch}`);
  console.log(`first pass: native CLI wall ${(nativeWallMs / 1000).toFixed(2)} s (process start + init + I/O per model), ` +
    `WASM in-process ${(wasmFirstMs / 1000).toFixed(2)} s`);

  if (a.timing) {
    // Native in-process times from `elk bench --mode models` (layoutJson only, monotonic clock),
    // interleaved with the WASM measurements in batches so that load changes on a shared machine
    // affect both sides alike.
    const tmp = fs.mkdtempSync(path.join(os.tmpdir(), 'elk-wasm-parity-'));
    const timed = rows.filter((r) => r.status === 'identical');
    const BATCH = 20;
    for (let start = 0; start < timed.length; start += BATCH) {
      const batch = timed.slice(start, start + BATCH);
      const manifest = path.join(tmp, 'batch.tsv');
      const csv = path.join(tmp, 'native.csv');
      fs.writeFileSync(manifest, 'model_rel_path\tinput_json\tlayout\tstatus\terror\n' +
        batch.map((r, i) => `m${i}\t${path.join(a.models, r.rel)}\t\tok\t`).join('\n') + '\n');
      const b = spawnSync(a.elk, ['bench', '--mode', 'models', '--manifest', manifest, '--limit', '0',
        '--iterations', String(a.iterations), '--warmup', String(a.warmup), '--output', csv], { maxBuffer: 1 << 30 });
      if (b.status !== 0) {
        console.error('elk bench failed: ' + b.stderr.toString());
        process.exit(2);
      }
      const native = new Map();
      for (const line of fs.readFileSync(csv, 'utf8').split('\n').slice(1)) {
        const c = line.split(',');
        if (c.length >= 8) native.set(c[2], Number(c[6]));
      }
      batch.forEach((r, i) => {
        for (let k = 0; k < a.warmup; k++) backend.layout_json(r.text, '{}');
        const w0 = process.hrtime.bigint();
        for (let k = 0; k < a.iterations; k++) backend.layout_json(r.text, '{}');
        r.wasmMs = Number(process.hrtime.bigint() - w0) / 1e6 / a.iterations;
        r.nativeMs = native.get('m' + i);
      });
    }
    fs.rmSync(tmp, { recursive: true, force: true });
    let sumW = 0;
    let sumN = 0;
    const ratios = [];
    for (const r of timed) {
      if (r.nativeMs === undefined) continue;
      sumW += r.wasmMs;
      sumN += r.nativeMs;
      if (r.nativeMs > 0) ratios.push(r.wasmMs / r.nativeMs);
    }
    ratios.sort((x, y) => x - y);
    const q = (p) => ratios.length ? ratios[Math.min(ratios.length - 1, Math.floor(p * ratios.length))] : NaN;
    console.log(`timing (${ratios.length} models, warmup ${a.warmup}, iterations ${a.iterations}): ` +
      `native ${(sumN / 1000).toFixed(2)} s, WASM ${(sumW / 1000).toFixed(2)} s, total ratio WASM/native ${(sumW / sumN).toFixed(2)}x; ` +
      `per-model ratio median ${q(0.5).toFixed(2)}x, p10 ${q(0.1).toFixed(2)}x, p90 ${q(0.9).toFixed(2)}x, max ${q(1).toFixed(2)}x`);
  }
  if (a.report) {
    const lines = ['model\tstatus\tnative_ms\twasm_ms\tdetail'];
    for (const r of rows) {
      lines.push([r.rel, r.status, r.nativeMs === undefined ? '' : r.nativeMs.toFixed(3),
        r.wasmMs === undefined ? '' : r.wasmMs.toFixed(3), r.detail.replace(/[\t\n]/g, ' ')].join('\t'));
    }
    fs.writeFileSync(a.report, lines.join('\n') + '\n');
    console.log('report: ' + a.report);
  }
  process.exit(counts.different === 0 && counts.errorMismatch === 0 ? 0 : 1);
}

main();
