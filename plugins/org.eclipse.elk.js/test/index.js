'use strict';

// Entry point for `node --test plugins/org.eclipse.elk.js/test/`: Node.js resolves a directory
// argument to this file, which loads every `*.test.mjs` of this directory (sorted) into one
// test run. `node --test test/*.test.mjs` runs them as separate processes instead.
// SPDX-License-Identifier: EPL-2.0 OR GPL-3.0-or-later
const { readdirSync } = require('node:fs');
const path = require('node:path');
const { pathToFileURL } = require('node:url');

(async () => {
  const files = readdirSync(__dirname).filter(name => name.endsWith('.test.mjs')).sort();
  for (const name of files) {
    await import(pathToFileURL(path.join(__dirname, name)).href);
  }
})().catch(error => {
  console.error(error);
  process.exitCode = 1;
});
