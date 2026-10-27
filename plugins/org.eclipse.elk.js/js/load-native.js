'use strict';

/**
 * elk-lean native addon loader (Node.js), shared by index.js and elk-worker.js.
 *
 * Search order (as in elk-rs plugins/org.eclipse.elk.js/js/index.js):
 *  1. the platform package `elk-lean-<triple>` (installed via optionalDependencies)
 *  2. a local `../dist/elk-lean.<triple>.node` (scripts/build_napi.sh)
 *  3. a local `../dist/elk-lean.node` (generic development build)
 * Returns the addon, or null when none could be loaded; `errors` collects the reasons.
 *
 * SPDX-License-Identifier: EPL-2.0 OR GPL-3.0-or-later
 */

function isMusl() {
  if (process.platform !== 'linux') return false;
  try {
    var report = typeof process.report === 'object' && process.report.getReport();
    return !(report && report.header && report.header.glibcVersionRuntime);
  } catch (e) {
    return false;
  }
}

/** Platform triple of the running Node.js, using the napi-rs package names, or null. */
function platformTriple() {
  var platform = process.platform;
  var arch = process.arch;
  var tripleMap = {
    'darwin-arm64': 'darwin-arm64',
    'darwin-x64': 'darwin-x64',
    'linux-x64': isMusl() ? 'linux-x64-musl' : 'linux-x64-gnu',
    'linux-arm64': 'linux-arm64-gnu',
    'win32-x64': 'win32-x64-msvc',
  };
  var key = platform + '-' + arch;
  return tripleMap[key] || null;
}

function isBackend(candidate) {
  return candidate && typeof candidate.layout_json === 'function'
    && typeof candidate.known_layout_algorithms === 'function'
    && typeof candidate.known_layout_options === 'function'
    && typeof candidate.known_layout_categories === 'function';
}

/** Loads the native addon; `errors` (optional array) receives the failed attempts. */
function loadNativeAddon(errors) {
  var triple = platformTriple();
  var candidates = [];
  if (triple) {
    // 1. platform-specific NAPI package (optionalDependencies)
    candidates.push('elk-lean-' + triple);
    // 2. platform-specific local .node file
    candidates.push('../dist/elk-lean.' + triple + '.node');
  }
  // 3. generic local .node file
  candidates.push('../dist/elk-lean.node');
  for (var i = 0; i < candidates.length; i++) {
    try {
      var addon = require(candidates[i]);
      if (isBackend(addon)) return addon;
      if (errors) errors.push(candidates[i] + ': not an elk-lean backend');
    } catch (e) {
      if (errors) errors.push(candidates[i] + ': ' + (e && e.message ? e.message.split('\n')[0] : e));
    }
  }
  return null;
}

module.exports = { platformTriple: platformTriple, loadNativeAddon: loadNativeAddon, isBackend: isBackend };
