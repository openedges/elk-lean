/*
 * examples.html, "Examples" (elk-live client/src/examples/examples.ts): a table of contents of the
 * bundled examples (build-time copies of external/elk-models/examples, `examples/index.json`) as a
 * category tree, the selected example's ELK Text in an editor next to its diagram (edits re-layout
 * live), and its label, category and description below. `?e=<path>` selects an example, otherwise
 * a random one is shown; the TOC pushes history entries, Back/Forward reload the example.
 *
 * SPDX-License-Identifier: EPL-2.0 OR GPL-3.0-or-later
 */
import { monaco } from '../editor/monaco.ts';
import { ELKT, registerElkt } from '../editor/elkt-language.ts';
import { registerCompletion } from '../editor/completion.ts';
import { createExampleCategoryTree, navigationItems, parseElkex, type ElkExampleEntry } from '../core/elkex.ts';
import { renderMarkdown } from '../core/markdown.ts';
import { modelLink } from '../core/urls.ts';
import { mountFooter, mountNavbar } from '../app/chrome.ts';
import { setupDarkMode } from '../app/dark-mode.ts';
import { baseUrl, errorMessage, startEngine } from '../app/engine.ts';
import { createEditorDiagram, setStatus } from '../app/editor-diagram.ts';

/** elk-live `HistoryMode` (IGNORE, PUSH_STATE, REPLACE_STATE) */
type HistoryMode = 'ignore' | 'push' | 'replace';

mountNavbar('Examples');
mountFooter({ modelLink: false });
setupDarkMode();

const engine = startEngine();
registerElkt(monaco);
registerCompletion(monaco, engine.metadata);

let current: string | null = null;
const ctrl = createEditorDiagram({
  engine,
  format: 'elkt',
  language: ELKT,
  initialText: '',
  editorOptions: { scrollBeyondLastLine: false }, // elk-live examples.ts
  fileName: () => current?.split('/').pop() || 'graph',
  tools: [{
    id: 'open-elkt-button',
    label: 'Open in editor',
    title: 'Open this (edited) example in the ELKT editor',
    onClick: () => { location.href = modelLink(location.href, 'elkgraph.html', ctrl.model.getValue()); },
  }],
});

const toc = document.getElementById('toc')!;
const title = document.getElementById('title')!;
const titleSmall = document.getElementById('title-small')!;
const description = document.getElementById('example-description')!;

// ------------------------------------------------------------------ table of contents
async function loadIndex(): Promise<ElkExampleEntry[]> {
  const res = await fetch(new URL('examples/index.json', baseUrl));
  if (!res.ok) throw new Error(`examples/index.json: HTTP ${res.status}`);
  return (await res.json()) as ElkExampleEntry[];
}

const tocButtons = new Map<string, HTMLButtonElement>();

// elk-live indents headings and buttons with Bootstrap 4 `pl-${indent}` classes, which Bootstrap 5
// (the version it ships) does not define: on the live page nothing is indented, headings sit at the
// sidebar's edge and every button has the plain `.btn` padding. The same here, so the panels match.

/** elk-live `createNavigationDepthFirstAlphabetically` (headings and buttons per example). */
function buildToc(examples: ElkExampleEntry[]): void {
  for (const item of navigationItems(createExampleCategoryTree(examples))) {
    if (item.kind === 'heading') {
      const h = document.createElement('h6');
      h.className = 'sidebar-heading';
      h.textContent = item.text;
      toc.append(h);
    } else {
      const li = document.createElement('li');
      const b = document.createElement('button');
      b.type = 'button';
      b.className = 'sidebar-link';
      b.textContent = item.example.label;
      b.dataset.path = item.example.path;
      b.addEventListener('click', () => void loadExample(item.example.path, 'push'));
      tocButtons.set(item.example.path, b);
      li.append(b);
      toc.append(li);
    }
  }
}

// ------------------------------------------------------------------ examples
async function loadExample(path: string, historyMode: HistoryMode = 'ignore'): Promise<boolean> {
  let text: string;
  try {
    const res = await fetch(new URL(`examples/${path}.elkt`, baseUrl));
    // the dev server answers unknown paths with index.html
    if (!res.ok || (res.headers.get('content-type') ?? '').includes('text/html')) throw new Error(`HTTP ${res.status}`);
    text = await res.text();
  } catch (e) {
    setStatus(`Unknown example ${path} (${errorMessage(e)})`, 'error');
    title.textContent = 'Unknown example';
    titleSmall.textContent = path;
    description.textContent = '';
    return false;
  }
  const ex = parseElkex(path, text);
  current = ex.path;
  title.textContent = ex.label;
  titleSmall.textContent = ex.category.join(' > ');
  description.innerHTML = renderMarkdown(ex.doc);
  document.title = `${ex.label} - ELK Examples`;
  for (const [p, b] of tocButtons) {
    if (p === ex.path) b.setAttribute('aria-current', 'true');
    else b.removeAttribute('aria-current');
  }
  tocButtons.get(ex.path)?.scrollIntoView({ block: 'nearest' });
  ctrl.setText(ex.graph);
  // elk-live: a click pushes `?e=<path>`; the initial example (random or from `?e=`) only records
  // its state, the URL stays as opened
  if (historyMode === 'push') history.pushState({ e: ex.path }, '', `${location.pathname}?e=${encodeURIComponent(ex.path)}`);
  else if (historyMode === 'replace') history.replaceState({ e: ex.path }, '');
  return true;
}

window.addEventListener('popstate', (event) => {
  const e = (event.state as { e?: unknown } | null)?.e;
  if (typeof e === 'string') void loadExample(e);
});

// ------------------------------------------------------------------ start
setStatus('Loading the layout engine (WebAssembly, ~20 MB) in a Web Worker…');
const firstExample = loadIndex().then((examples) => {
  buildToc(examples);
  // either the example passed with `?e=` or a random one (elk-live)
  const requested = new URLSearchParams(location.search).get('e');
  const path = requested || examples[Math.floor(Math.random() * examples.length)].path;
  return loadExample(path, 'replace');
});
Promise.all([engine.ready, firstExample]).then(([ms, ok]) => {
  ctrl.setLoading('Laying out…');
  if (ok) {
    setStatus(`Layout engine ready (${(ms / 1000).toFixed(1)} s)`);
    void ctrl.update();
  } else {
    ctrl.setLoading(null);
  }
}).catch((e: unknown) => {
  const msg = errorMessage(e);
  ctrl.setLoading(`Could not start: ${msg}`);
  setStatus(`Could not start: ${msg}`, 'error');
});

// debugging / tests
(window as unknown as { elkLive: unknown }).elkLive = { elk: engine.elk, editor: ctrl.editor, monaco, update: ctrl.update, loadExample };
