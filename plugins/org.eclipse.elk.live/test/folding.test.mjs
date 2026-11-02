// The `.elkt` folding ranges against those of elk-live's Xtext 2.36.0 language server
// (`textDocument/foldingRange`, captured from a local build of external/elk-live into
// fixtures/elkt-folding-xtext.json): the 45 examples of elk-models and crafted inputs (comments,
// layouts, sections, bend points, property entries across lines, braces shared by lines, …).
// Inputs the ELK Text parser rejects are run for robustness only (Xtext's error recovery is not
// reproduced); a difference there is reported as a diagnostic.
// SPDX-License-Identifier: EPL-2.0 OR GPL-3.0-or-later
import { describe, it } from 'node:test';
import assert from 'node:assert/strict';
import { existsSync, readFileSync } from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { elktFoldingRanges, elktFoldingRegions } from '../src/editor/elkt-folding.ts';

const here = path.dirname(fileURLToPath(import.meta.url));
const fixture = JSON.parse(readFileSync(path.join(here, 'fixtures/elkt-folding-xtext.json'), 'utf8'));
const examples = path.resolve(here, '../../../external/elk-models/examples');

describe('ELK Text folding ranges (Xtext language server fixture)', () => {
  let exact = 0;
  for (const c of fixture.cases) {
    const file = c.example === undefined ? null : path.join(examples, c.example);
    const text = file === null ? c.text : existsSync(file) ? readFileSync(file, 'utf8') : null;
    it(c.name, { skip: text === null ? 'elk-models submodule not checked out' : false }, (t) => {
      const got = elktFoldingRanges(text);
      if (c.invalid !== undefined) {
        if (JSON.stringify(got) !== JSON.stringify(c.ranges)) {
          t.diagnostic(`differs from Xtext's error recovery (${c.invalid}): ${JSON.stringify(got)} vs ${JSON.stringify(c.ranges)}`);
        }
        return;
      }
      assert.deepEqual(got, c.ranges);
      exact++;
    });
  }
  it('matches the server on every valid input', () => {
    const valid = fixture.cases.filter((c) => c.invalid === undefined && (c.example === undefined || existsSync(path.join(examples, c.example)))).length;
    assert.equal(exact, valid);
    assert.ok(valid >= 80, `${valid} valid cases`);
  });
  it('folds the same lines with CRLF line ends', () => {
    const lf = 'node a {\n    node b {\n        node c\n    }\n    /* two\n       lines */\n}\n';
    assert.deepEqual(elktFoldingRanges(lf.replaceAll('\n', '\r\n')), elktFoldingRanges(lf));
    assert.deepEqual(elktFoldingRanges(lf), [{ startLine: 0, endLine: 6 }, { startLine: 1, endLine: 3 }, { startLine: 4, endLine: 5, kind: 'comment' }]);
  });
  it('reports regions by offset, parent first, comments by kind', () => {
    const text = '// head\nnode a { // open\n    node b\n} /* tail\n*/\n';
    assert.deepEqual(elktFoldingRegions(text), [
      { start: 8, end: text.indexOf('} /*') + 1 },
      { start: text.indexOf('node b'), end: text.indexOf('node b') + 6 },
      { start: text.indexOf('/* tail'), end: text.indexOf('*/') + 2, kind: 'comment' },
    ]);
  });
  it('keeps the controls of intact objects while a document is being typed', () => {
    for (const text of ['node a {\n    node b {\n', 'node a {\n    label "x\n    node b\n}\n', 'node a {\n    elk.direction:\n', 'edge a ->\n', 'node a {\n    layout [\n', '/* open\n comment', 'node a {\n    port p {\n        node x\n    }\n}\n']) {
      assert.ok(Array.isArray(elktFoldingRanges(text)), JSON.stringify(text));
    }
  });
});
