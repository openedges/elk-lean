/*
 * ELK Live on elk-lean: `.elkt` (or ELK JSON) editor with a synchronized diagram, without a server.
 * Edit -> debounce -> elk.convertElkt (Lean parser in the WASM Web Worker) -> elk.layout (same
 * worker) -> sprotty model update. Replaces elk-live's elkgraph.html / examples.html / json.html
 * (external/elk-live/client/src/elkgraph/editor.ts, examples/examples.ts, json/editor.ts).
 *
 * SPDX-License-Identifier: EPL-2.0 OR GPL-3.0-or-later
 */
import './style.css';
import './diagram/diagram.css';
import LZString from 'lz-string';
import { FitToScreenAction } from 'sprotty-protocol';
import { LocalModelSource, TYPES, type IActionDispatcher } from 'sprotty';
// the ELK class only: the WASM backend runs in the Web Worker (public/elk-lean/, scripts/copy-assets.mjs)
import ELK from 'elk-lean/js/elk-api.js';
import type { ElkNode } from 'elk-lean';
import { monaco, registerJson } from './editor/monaco.ts';
import { ELKT, registerElkt } from './editor/elkt-language.ts';
import { registerCompletion } from './editor/completion.ts';
import { createContainer } from './diagram/sprotty-config.ts';
import { download, exportSvg } from './diagram/svg-export.ts';
import { runPipeline, type InputFormat, type PipelineResult } from './core/pipeline.ts';
import { buildMetadata, type Metadata } from './core/options.ts';
import { parseElkex, type ElkExample } from './core/elkex.ts';
import { renderMarkdown } from './core/markdown.ts';
import choices from './generated/option-choices.json';

const $ = <T extends HTMLElement>(id: string): T => document.getElementById(id) as T;

const DEFAULT_ELKT = `algorithm: layered

node n1
node n2
node n3
edge n1 -> n2
edge n1 -> n3`;

const DEBOUNCE_MS = 250;
const baseUrl = new URL(import.meta.env.BASE_URL, document.baseURI);

// ---------------------------------------------------------------- dark mode
const DARK_KEY = 'elk-lean-live-dark-mode';
function storedDark(): boolean | null {
  try {
    const v = localStorage.getItem(DARK_KEY);
    return v === null ? null : v === 'true';
  } catch {
    return null;
  }
}
let dark = storedDark() ?? window.matchMedia('(prefers-color-scheme: dark)').matches;
function applyDark(): void {
  document.body.classList.toggle('elk-dark-mode', dark);
  $('dark-toggle').setAttribute('aria-pressed', String(dark));
  monaco.editor.setTheme(dark ? 'vs-dark' : 'vs');
}

// ---------------------------------------------------------------- URL parameters (elk-live compatible)
const params = new URLSearchParams(location.search);
let format: InputFormat = params.get('format') === 'json' ? 'json' : 'elkt';
let initialText = DEFAULT_ELKT;
if (params.has('compressedContent')) {
  initialText = LZString.decompressFromEncodedURIComponent(params.get('compressedContent') ?? '') ?? DEFAULT_ELKT;
} else if (params.has('initialContent')) {
  initialText = params.get('initialContent') ?? DEFAULT_ELKT;
}
const initialExample = params.get('e');

// ---------------------------------------------------------------- editor
registerElkt(monaco);
registerJson(monaco);
let metadata: Metadata | null = null;
registerCompletion(monaco, () => metadata);
const model = monaco.editor.createModel(initialText, format === 'json' ? 'json' : ELKT,
  monaco.Uri.parse(`inmemory:/model.${format === 'json' ? 'json' : 'elkt'}`));
const editor = monaco.editor.create($('monaco-editor'), {
  model,
  minimap: { enabled: false },
  automaticLayout: true,
  fontSize: 13,
  scrollBeyondLastLine: false,
  quickSuggestions: { other: true, comments: false, strings: false },
  suggestOnTriggerCharacters: true,
});
applyDark();
$('format-select').querySelector<HTMLOptionElement>(`option[value="${format}"]`)!.selected = true;

// ---------------------------------------------------------------- diagram
const container = createContainer('sprotty');
const modelSource = container.get<LocalModelSource>(TYPES.ModelSource);
const dispatcher = container.get<IActionDispatcher>(TYPES.IActionDispatcher);
let hasModel = false;
let lastResult: PipelineResult | null = null;

function fit(animate = true): void {
  void dispatcher.dispatch(FitToScreenAction.create([], { padding: 20, maxZoom: 1.5, animate }));
}

// ---------------------------------------------------------------- engine (WASM in a Web Worker)
const status = $('status');
function setStatus(text: string, kind: 'ok' | 'error' | 'info' = 'info'): void {
  status.textContent = text;
  status.className = kind === 'info' ? '' : kind;
}

const elk = new ELK({ workerUrl: new URL('elk-lean/js/elk-worker.js', baseUrl).href });
const ready = (async () => {
  const t0 = performance.now();
  const [options, algorithms] = await Promise.all([elk.knownLayoutOptions(), elk.knownLayoutAlgorithms()]);
  metadata = buildMetadata(options as unknown as Record<string, unknown>[],
    algorithms as unknown as Record<string, unknown>[], choices as Record<string, string[]>);
  return performance.now() - t0;
})();

// ---------------------------------------------------------------- pipeline
let pending = false;
let running = false;
let fitNext = true;
let timer: number | undefined;

function markers(result: PipelineResult): void {
  const d = result.diagnostic;
  const list: Monaco.editor.IMarkerData[] = [];
  if (d) {
    const line = d.line ?? 1;
    const column = d.column ?? 1;
    const word = model.getWordAtPosition({ lineNumber: Math.min(line, model.getLineCount()), column });
    list.push({
      severity: monaco.MarkerSeverity.Error,
      message: d.kind === 'layout' ? `Layout failed: ${d.message}` : d.message,
      startLineNumber: line,
      startColumn: column,
      endLineNumber: d.line ? line : model.getLineCount(),
      endColumn: d.line ? (word ? word.endColumn : column + 1) : model.getLineMaxColumn(model.getLineCount()),
    });
  }
  monaco.editor.setModelMarkers(model, 'elk-lean', list);
}

async function update(): Promise<void> {
  if (running) {
    pending = true;
    return;
  }
  running = true;
  try {
    do {
      pending = false;
      const text = model.getValue();
      const result = await runPipeline(elk, text, format);
      if (pending) continue; // a newer edit arrived meanwhile: skip this result
      lastResult = result;
      markers(result);
      const timing = `parse ${result.parseMs.toFixed(1)} ms, layout ${result.layoutMs.toFixed(1)} ms`;
      if (result.ok && result.model) {
        const first = !hasModel;
        if (first) {
          await modelSource.setModel(result.model);
          hasModel = true;
        } else {
          await modelSource.updateModel(result.model);
        }
        if (fitNext) {
          // the first model needs the canvas bounds of its initial render before it can be fitted
          window.setTimeout(() => fit(false), first ? 100 : 0);
          fitNext = false;
        }
        setStatus(`Laid out ${count(result.laidOut!)} (${timing})`, 'ok');
      } else if (result.diagnostic) {
        const d = result.diagnostic;
        const where = d.line ? ` at ${d.line}:${d.column}` : '';
        setStatus(`${d.kind === 'parse' ? 'Parse error' : 'Layout error'}${where}: ${d.message}`, 'error');
      }
      $('loading').hidden = true;
    } while (pending);
  } catch (e) {
    setStatus(`Error: ${e instanceof Error ? e.message : String(e)}`, 'error');
    $('loading').hidden = true;
  } finally {
    running = false;
  }
}

function count(g: ElkNode): string {
  let nodes = 0;
  let edges = 0;
  const visit = (n: ElkNode) => {
    for (const c of n.children ?? []) {
      nodes++;
      visit(c);
    }
    edges += (n.edges ?? []).length;
  };
  visit(g);
  return `${nodes} node${nodes === 1 ? '' : 's'}, ${edges} edge${edges === 1 ? '' : 's'}`;
}

function schedule(): void {
  window.clearTimeout(timer);
  timer = window.setTimeout(() => void update(), DEBOUNCE_MS);
  updateLink();
}

model.onDidChangeContent(() => {
  if (!loadingExample) $('example-select').querySelector<HTMLOptionElement>('option[value=""]')!.selected = true;
  schedule();
});

// ---------------------------------------------------------------- examples (build-time copies of external/elk-models/examples)
let loadingExample = false;
type ExampleEntry = Omit<ElkExample, 'graph'>;
async function loadExamples(): Promise<ExampleEntry[]> {
  const res = await fetch(new URL('examples/index.json', baseUrl));
  if (!res.ok) throw new Error(`examples/index.json: HTTP ${res.status}`);
  return (await res.json()) as ExampleEntry[];
}

const exampleSelect = $<HTMLSelectElement>('example-select');
let examples: ExampleEntry[] = [];
void loadExamples().then((list) => {
  examples = list;
  const groups = new Map<string, HTMLOptGroupElement>();
  for (const ex of list) {
    const cat = ex.category.join(' > ') || 'Examples';
    let group = groups.get(cat);
    if (!group) {
      group = document.createElement('optgroup');
      group.label = cat;
      groups.set(cat, group);
      exampleSelect.appendChild(group);
    }
    const opt = document.createElement('option');
    opt.value = ex.path;
    opt.textContent = ex.label;
    group.appendChild(opt);
  }
  if (initialExample) void selectExample(initialExample);
}).catch((e) => setStatus(`Could not load the examples: ${e instanceof Error ? e.message : e}`, 'error'));

async function selectExample(path: string): Promise<void> {
  const doc = $('example-doc');
  if (!path) {
    doc.hidden = true;
    return;
  }
  const res = await fetch(new URL(`examples/${path}.elkt`, baseUrl));
  if (!res.ok) {
    setStatus(`Could not load example ${path}: HTTP ${res.status}`, 'error');
    return;
  }
  const ex = parseElkex(path, await res.text());
  if (format !== 'elkt') setFormat('elkt', false);
  loadingExample = true;
  try {
    model.setValue(ex.graph);
  } finally {
    loadingExample = false;
  }
  editor.setPosition({ lineNumber: 1, column: 1 });
  exampleSelect.value = path;
  $('example-title').textContent = ex.label;
  $('example-category').textContent = ex.category.join(' > ');
  $('example-description').innerHTML = renderMarkdown(ex.doc);
  doc.hidden = false;
  fitNext = true;
  updateLink();
}

exampleSelect.addEventListener('change', () => void selectExample(exampleSelect.value));

// ---------------------------------------------------------------- format switch (elkt <-> json)
function setFormat(next: InputFormat, convert: boolean): void {
  if (next === format) return;
  const prev = format;
  format = next;
  monaco.editor.setModelLanguage(model, next === 'json' ? 'json' : ELKT);
  $<HTMLSelectElement>('format-select').value = next;
  if (convert && prev === 'elkt' && next === 'json') {
    // carry the current graph over: the converted ELK JSON (with the elk-live default sizes)
    void elk.convertElkt(model.getValue(), { defaults: true })
      .then((g) => model.setValue(JSON.stringify(g, null, 2)))
      .catch(() => schedule());
  } else {
    schedule();
  }
}
$<HTMLSelectElement>('format-select').addEventListener('change', (e) => {
  setFormat((e.target as HTMLSelectElement).value as InputFormat, true);
  $('example-doc').hidden = true;
  exampleSelect.value = '';
});

// ---------------------------------------------------------------- toolbar
function linkHref(): string {
  const url = new URL(location.href);
  url.search = '';
  if (exampleSelect.value) {
    url.searchParams.set('e', exampleSelect.value);
  } else {
    url.searchParams.set('compressedContent', LZString.compressToEncodedURIComponent(model.getValue()));
    if (format === 'json') url.searchParams.set('format', 'json');
  }
  return url.href;
}
let linkTimer: number | undefined;
function updateLink(): void {
  window.clearTimeout(linkTimer);
  linkTimer = window.setTimeout(() => $<HTMLAnchorElement>('model-link').setAttribute('href', linkHref()), 400);
}
$('copy-link-button').addEventListener('click', () => {
  const href = linkHref();
  $<HTMLAnchorElement>('model-link').href = href;
  navigator.clipboard.writeText(href).then(() => setStatus('Link copied to the clipboard', 'ok'),
    () => setStatus('Copying failed; use the "Link" anchor instead', 'error'));
});
$('fit-button').addEventListener('click', () => fit());
$('svg-button').addEventListener('click', () => {
  const text = exportSvg($('sprotty'), dark);
  if (text) download(`${exampleSelect.value.split('/').pop() || 'graph'}.svg`, text, 'image/svg+xml');
});
$('json-button').addEventListener('click', () => {
  if (lastResult?.laidOut) {
    download(`${exampleSelect.value.split('/').pop() || 'graph'}.json`, JSON.stringify(lastResult.laidOut, null, 2), 'application/json');
  }
});
$('dark-toggle').addEventListener('click', () => {
  dark = !dark;
  try {
    localStorage.setItem(DARK_KEY, String(dark));
  } catch { /* storage unavailable */ }
  applyDark();
});

// ---------------------------------------------------------------- start
setStatus('Loading the layout engine (WebAssembly, ~20 MB) in a Web Worker…');
ready.then((ms) => {
  $('loading-text').textContent = 'Laying out…';
  setStatus(`Layout engine ready (${(ms / 1000).toFixed(1)} s)`);
  if (!initialExample) void update();
}).catch((e: unknown) => {
  const msg = e && typeof e === 'object' && 'message' in e ? String((e as { message: unknown }).message) : String(e);
  $('loading-text').textContent = `The layout engine could not be loaded: ${msg}`;
  setStatus(`The layout engine could not be loaded: ${msg}`, 'error');
});
updateLink();

// debugging / tests
(window as unknown as { elkLive: unknown }).elkLive = { elk, editor, monaco, update, selectExample, get examples() { return examples; } };

import type * as Monaco from 'monaco-editor/editor/editor.api';
