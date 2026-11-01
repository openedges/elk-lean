/*******************************************************************************
 * Copyright (c) 2020 Kiel University and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * http://www.eclipse.org/legal/epl-2.0.
 *
 * SPDX-License-Identifier: EPL-2.0
 *******************************************************************************/
/*
 * Ported from elk-live client/src/examples/elkex.ts (class ElkExample) for elk-lean: the
 * `// elkex:<key>` sections (category, label, doc, graph) of the example files under
 * external/elk-models/examples. Changed: a plain function returning an object, files without the
 * sections fall back to their path (label) and the whole text (graph) instead of throwing.
 * DOM-free (used by scripts/copy-assets.mjs at build time and by the app).
 */

export interface ElkExample {
  /** path below `examples/` without `.elkt`, e.g. `general/direction` */
  path: string;
  label: string;
  /** category path, e.g. `['General', 'Direction']` */
  category: string[];
  /** description (markdown) */
  doc: string;
  /** the ELK Text shown in the editor */
  graph: string;
}

const KEYS = new Set(['graph', 'doc', 'category', 'label']);

function removeComments(s: string): string {
  return s.replace(/^( |\t)*\/\//gm, '').replace(/\/\*/g, '').replace(/\*\//g, '');
}

/** Parses an elkex example file (`path` without the `.elkt` extension). */
export function parseElkex(path: string, serialized: string): ElkExample {
  const out: Partial<ElkExample> = { path };
  for (const raw of serialized.split(/\/\/\s*elkex:/)) {
    const s = raw.trim();
    const ws = s.search(/\s/);
    const key = ws < 0 ? s : s.substring(0, ws);
    if (!KEYS.has(key)) continue;
    const nl = s.search(/[\r\n]/);
    let value = nl < 0 ? '' : s.substring(nl + 1);
    if (key !== 'graph') value = removeComments(value);
    value = value.trim();
    if (key === 'category') out.category = value.split('>').map((c) => c.trim());
    else (out as Record<string, unknown>)[key] = value;
  }
  const parts = path.split('/');
  return {
    path,
    label: out.label ?? parts[parts.length - 1],
    category: out.category ?? parts.slice(0, -1),
    doc: out.doc ?? '',
    graph: out.graph ?? serialized,
  };
}
