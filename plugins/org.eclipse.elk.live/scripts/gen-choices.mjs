#!/usr/bin/env node
// Regenerates src/generated/option-choices.json ({ optionId: [literal, ...] } of the ENUM and ENUMSET
// layout options) from `elk options --choices` of the native CLI (ELK_LEAN_BIN, default
// ../../.lake/build/bin/elk; build it with `lake build` at the repository root). The elkjs-compatible
// `knownLayoutOptions()` does not report enum literals, so the editor's value completion reads them
// from this snapshot; test/pipeline.test.mjs checks that it matches the CLI.
// SPDX-License-Identifier: EPL-2.0 OR GPL-3.0-or-later
import { execFileSync } from 'node:child_process';
import { mkdirSync, writeFileSync } from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const app = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const cli = process.env.ELK_LEAN_BIN || path.resolve(app, '../../.lake/build/bin/elk');

/** `{ id: choices }` of `elk options --choices`, keys sorted. */
export function readChoices(bin = cli) {
  const options = JSON.parse(execFileSync(bin, ['options', '--choices'], { encoding: 'utf8', maxBuffer: 64 << 20 }));
  const out = {};
  for (const o of options.slice().sort((a, b) => a.id.localeCompare(b.id))) {
    if (Array.isArray(o.choices) && o.choices.length > 0) out[o.id] = o.choices;
  }
  return out;
}

if (import.meta.url === `file://${process.argv[1]}`) {
  const choices = readChoices();
  const target = path.join(app, 'src/generated/option-choices.json');
  mkdirSync(path.dirname(target), { recursive: true });
  writeFileSync(target, JSON.stringify(choices, null, 1) + '\n');
  console.log(`gen-choices: ${Object.keys(choices).length} enum options -> ${path.relative(app, target)}`);
}
