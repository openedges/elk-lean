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
 * Ported from elk-live client/src/examples/elkex.ts (class ElkExample, createExampleCategoryTree)
 * and the navigation builder of client/src/examples/examples.ts
 * (createNavigationDepthFirstAlphabetically) for elk-lean: the `// elkex:<key>` sections
 * (category, label, doc, graph) of the example files under external/elk-models/examples and the
 * category tree of the examples page. Changed: a plain function returning an object, files without
 * the sections fall back to their path (label) and the whole text (graph) instead of throwing; the
 * tree works on the index entries (no graph text); the navigation is returned as a flat list of
 * headings and examples (the page renders it), sorted copies instead of in-place sorts, and nested
 * headings are prefixed `Parent > Child` (elk-live's prefix started with a space and doubled
 * the spaces below the second level).
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

/** An example of the index (`examples/index.json`): the elkex sections without the graph. */
export type ElkExampleEntry = Omit<ElkExample, 'graph'>;

/** elk-live `ExampleCategory`: examples of one category and its sub-categories. */
export interface ExampleCategory<T extends ElkExampleEntry = ElkExampleEntry> {
  name: string;
  elements: T[];
  subCategories: ExampleCategory<T>[];
}

/** elk-live `createExampleCategoryTree`: groups the examples by `category[depth]`, recursively. */
export function createExampleCategoryTree<T extends ElkExampleEntry>(examples: T[], depth = 0, name = 'root'): ExampleCategory<T> {
  const grouped = new Map<string, T[]>();
  const elements: T[] = [];
  for (const e of examples) {
    const key = e.category[depth];
    if (key === undefined || key === '') {
      elements.push(e);
    } else {
      let list = grouped.get(key);
      if (!list) grouped.set(key, (list = []));
      list.push(e);
    }
  }
  const subCategories = [...grouped].map(([k, list]) => createExampleCategoryTree(list, depth + 1, k));
  return { name, elements, subCategories };
}

/** One row of the examples page's table of contents. */
export type NavigationItem<T extends ElkExampleEntry = ElkExampleEntry> =
  | { kind: 'heading'; text: string; indent: number }
  | { kind: 'example'; example: T; indent: number };

/**
 * elk-live `createNavigationDepthFirstAlphabetically`: a heading per category (except the root),
 * then its examples by label, then its sub-categories by name, depth-first. Examples are indented
 * like the heading of their category.
 */
export function navigationItems<T extends ElkExampleEntry>(category: ExampleCategory<T>, indent = 0, namePrefix = ''): NavigationItem<T>[] {
  const out: NavigationItem<T>[] = [];
  const isRoot = category.name === 'root';
  if (!isRoot) out.push({ kind: 'heading', text: namePrefix + category.name, indent });
  for (const e of [...category.elements].sort((a, b) => a.label.localeCompare(b.label))) {
    out.push({ kind: 'example', example: e, indent });
  }
  const prefix = isRoot ? namePrefix : `${namePrefix}${category.name} > `;
  for (const c of [...category.subCategories].sort((a, b) => a.name.localeCompare(b.name))) {
    out.push(...navigationItems(c, indent + 1, prefix));
  }
  return out;
}
