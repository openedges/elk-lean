// Structural layout comparison with numeric tolerance, used for the optional elkjs check of
// run.mjs. Ported from elk-rs plugins/org.eclipse.elk.js/test/parity/compare.mjs
// (stripInternal, deepCompare). SPDX-License-Identifier: EPL-2.0 OR GPL-3.0-or-later

/** Keys that are input metadata, not layout output — skip in comparison */
const SKIP_KEYS = new Set(['$H', 'properties', 'layoutOptions']);

/** Deep-clone and strip non-layout properties for comparison */
export function stripInternal(obj) {
  if (obj === null || obj === undefined) return obj;
  if (typeof obj !== 'object') return obj;
  if (Array.isArray(obj)) return obj.map(stripInternal);
  const result = {};
  for (const key of Object.keys(obj).sort()) {
    if (key.startsWith('$')) continue;
    if (SKIP_KEYS.has(key)) continue;
    result[key] = stripInternal(obj[key]);
  }
  return result;
}

/** Sort arrays by .id if all elements have one */
function stableSort(arr) {
  if (arr.length === 0) return arr;
  if (arr.every(item => item && typeof item === 'object' && 'id' in item)) {
    return [...arr].sort((a, b) => String(a.id).localeCompare(String(b.id)));
  }
  if (arr.every(item => typeof item === 'string')) {
    return [...arr].sort();
  }
  return arr;
}

/** Deep-compare two values with numeric tolerance. Returns list of diffs. */
export function deepCompare(a, b, path = '', tolerance = 1e-6) {
  const diffs = [];
  if (a === b) return diffs;

  if (typeof a === 'number' && typeof b === 'number') {
    if (Number.isNaN(a) && Number.isNaN(b)) return diffs;
    if (!Number.isFinite(a) || !Number.isFinite(b) || Math.abs(a - b) > tolerance) {
      diffs.push({ path, expected: a, actual: b, type: 'value' });
    }
    return diffs;
  }

  if (typeof a !== typeof b) {
    diffs.push({ path, expected: a, actual: b, type: 'type' });
    return diffs;
  }

  if (a === null || b === null) {
    if (a !== b) diffs.push({ path, expected: a, actual: b, type: 'null' });
    return diffs;
  }

  if (Array.isArray(a) || Array.isArray(b)) {
    if (!Array.isArray(a) || !Array.isArray(b)) {
      diffs.push({ path, expected: `array(${Array.isArray(a)})`, actual: `array(${Array.isArray(b)})`, type: 'type' });
      return diffs;
    }
    const sa = stableSort(a);
    const sb = stableSort(b);
    if (sa.length !== sb.length) {
      diffs.push({ path, expected: `length=${sa.length}`, actual: `length=${sb.length}`, type: 'array_length' });
    }
    const len = Math.min(sa.length, sb.length);
    for (let i = 0; i < len; i++) {
      diffs.push(...deepCompare(sa[i], sb[i], `${path}[${i}]`, tolerance));
    }
    return diffs;
  }

  if (typeof a === 'object') {
    const allKeys = [...new Set([...Object.keys(a), ...Object.keys(b)])].sort();
    for (const key of allKeys) {
      if (!(key in a)) {
        diffs.push({ path: `${path}.${key}`, expected: '<missing>', actual: b[key], type: 'missing_in_expected' });
      } else if (!(key in b)) {
        diffs.push({ path: `${path}.${key}`, expected: a[key], actual: '<missing>', type: 'missing_in_actual' });
      } else {
        diffs.push(...deepCompare(a[key], b[key], `${path}.${key}`, tolerance));
      }
    }
    return diffs;
  }

  if (a !== b) {
    diffs.push({ path, expected: a, actual: b, type: 'value' });
  }
  return diffs;
}
