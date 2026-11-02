/*
 * The editor + diagram pair of the editor and examples pages: a Monaco editor, the sprotty
 * diagram, and the pipeline between them (edit -> debounce -> `runPipeline` (convertElkt or JSON5,
 * then layout, in the Web Worker) -> sprotty model update), with error markers, the status line,
 * the loading overlay and the diagram tools (Fit, SVG, JSON download, page-specific actions).
 * Replaces the editor/diagram wiring of elk-live's elkgraph/editor.ts, json/editor.ts and
 * examples/examples.ts (Xtext language server and websocket diagram server there).
 *
 * SPDX-License-Identifier: EPL-2.0 OR GPL-3.0-or-later
 */
import './vendor.css';
import '../style.css';
import '../diagram/diagram.css';
import { FitToScreenAction } from 'sprotty-protocol';
import { LocalModelSource, TYPES, type IActionDispatcher } from 'sprotty';
import type * as Monaco from 'monaco-editor/editor/editor.api';
import { monaco } from '../editor/monaco.ts';
import { createContainer } from '../diagram/sprotty-config.ts';
import { download, exportSvg } from '../diagram/svg-export.ts';
import { countElements, runPipeline, type InputFormat, type PipelineResult } from '../core/pipeline.ts';
import { errorMessage, type Engine } from './engine.ts';
import { isDark, onDarkModeChange } from './dark-mode.ts';

const DEBOUNCE_MS = 250;

export type StatusKind = 'ok' | 'error' | 'info';

/** Sets the footer's status line (`#status`). */
export function setStatus(text: string, kind: StatusKind = 'info'): void {
  const status = document.getElementById('status');
  if (!status) return;
  status.textContent = text;
  status.className = kind === 'info' ? '' : kind;
}

export interface ToolButton {
  id: string;
  label: string;
  title: string;
  onClick: () => void;
}

export interface EditorDiagramOptions {
  engine: Engine;
  format: InputFormat;
  /** Monaco language id (`elkt`, `elkj`) */
  language: string;
  initialText: string;
  /** element ids: the editor and the sprotty base div (inside a `.diagram-pane`) */
  editorId?: string;
  diagramId?: string;
  /** base name of the SVG / JSON downloads */
  fileName: () => string;
  /** page-specific buttons, shown after Fit / SVG / JSON */
  tools?: ToolButton[];
  /** called after every text change (debounced layout is scheduled already) */
  onChange?: () => void;
  editorOptions?: Monaco.editor.IStandaloneEditorConstructionOptions;
}

export interface EditorDiagram {
  editor: Monaco.editor.IStandaloneCodeEditor;
  model: Monaco.editor.ITextModel;
  /** lays out the current text now (a newer edit drops the result of an older one) */
  update(): Promise<void>;
  /** replaces the text and moves the cursor to the start (the viewport is kept, as in elk-live) */
  setText(text: string): void;
  lastResult(): PipelineResult | null;
  fit(animate?: boolean): void;
  /** hides the loading overlay with a message (engine start-up failure) or without */
  setLoading(text: string | null): void;
}

function el<K extends keyof HTMLElementTagNameMap>(tag: K, props: Partial<HTMLElementTagNameMap[K]> = {},
  ...children: (Node | string)[]): HTMLElementTagNameMap[K] {
  const e = Object.assign(document.createElement(tag), props);
  e.append(...children);
  return e;
}

export function createEditorDiagram(opts: EditorDiagramOptions): EditorDiagram {
  const editorId = opts.editorId ?? 'monaco-editor';
  const diagramId = opts.diagramId ?? 'sprotty';
  // sprotty replaces its base div on the first render: look it up by id when needed
  const diagramDiv = () => document.getElementById(diagramId)!;
  const pane = diagramDiv().closest('.diagram-pane') ?? diagramDiv().parentElement!;

  // ---------------------------------------------------------------- diagram tools and loading overlay
  const tools = el('div', { className: 'diagram-tools' });
  const buttons: ToolButton[] = [
    { id: 'fit-button', label: 'Fit', title: 'Fit the diagram to the view', onClick: () => fit() },
    { id: 'svg-button', label: 'SVG', title: 'Download the diagram as SVG', onClick: () => downloadSvg() },
    { id: 'json-button', label: 'JSON', title: 'Download the laid-out graph as ELK JSON', onClick: () => downloadJson() },
    ...(opts.tools ?? []),
  ];
  for (const b of buttons) {
    const button = el('button', { type: 'button', id: b.id, title: b.title }, b.label);
    button.addEventListener('click', b.onClick);
    tools.append(button);
  }
  const loadingText = el('div', { id: 'loading-text' }, 'Loading the layout engine (WebAssembly)…');
  const spinner = el('div', { className: 'spinner' });
  spinner.setAttribute('aria-hidden', 'true');
  const loading = el('div', { id: 'loading', className: 'loading-overlay' }, spinner, loadingText);
  pane.append(tools, loading);

  // ---------------------------------------------------------------- editor
  const ext = opts.format === 'json' ? 'json' : 'elkt';
  const model = monaco.editor.createModel(opts.initialText, opts.language,
    monaco.Uri.parse(`inmemory:/${diagramId}/model.${ext}`));
  const editor = monaco.editor.create(document.getElementById(editorId)!, {
    model,
    minimap: { enabled: false },
    automaticLayout: true,
    fontSize: 13,
    scrollBeyondLastLine: false,
    quickSuggestions: { other: true, comments: false, strings: false },
    suggestOnTriggerCharacters: true,
    ...opts.editorOptions,
  });
  onDarkModeChange((dark) => monaco.editor.setTheme(dark ? 'vs-dark' : 'vs'));

  // ---------------------------------------------------------------- diagram
  const container = createContainer(diagramId);
  const modelSource = container.get<LocalModelSource>(TYPES.ModelSource);
  const dispatcher = container.get<IActionDispatcher>(TYPES.IActionDispatcher);
  let hasModel = false;
  let lastResult: PipelineResult | null = null;

  function fit(animate = true): void {
    void dispatcher.dispatch(FitToScreenAction.create([], { padding: 20, maxZoom: 1.5, animate }));
  }

  function downloadSvg(): void {
    const text = exportSvg(diagramDiv(), isDark());
    if (text) download(`${opts.fileName()}.svg`, text, 'image/svg+xml');
  }

  function downloadJson(): void {
    if (lastResult?.laidOut) {
      download(`${opts.fileName()}.json`, JSON.stringify(lastResult.laidOut, null, 2), 'application/json');
    }
  }

  // ---------------------------------------------------------------- pipeline
  let pending = false;
  let running = false;
  let timer: number | undefined;

  function markers(result: PipelineResult): void {
    const d = result.diagnostic;
    const list: Monaco.editor.IMarkerData[] = [];
    if (d) {
      const lines = model.getLineCount();
      const line = Math.min(Math.max(d.line ?? 1, 1), lines);
      const column = Math.max(d.column ?? 1, 1);
      const word = model.getWordAtPosition({ lineNumber: line, column });
      list.push({
        severity: monaco.MarkerSeverity.Error,
        message: d.kind === 'layout' ? `Layout failed: ${d.message}` : d.message,
        startLineNumber: line,
        startColumn: column,
        endLineNumber: d.line ? line : lines,
        endColumn: d.line ? (word ? word.endColumn : column + 1) : model.getLineMaxColumn(lines),
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
        const result = await runPipeline(opts.engine.elk, model.getValue(), opts.format);
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
          // no automatic fit: like elk-live, the diagram starts at the top-left corner at zoom 1 and
          // the viewport is kept across updates; "Fit" is a manual action
          setStatus(`Laid out ${countElements(result.laidOut!)} (${timing})`, 'ok');
        } else if (result.diagnostic) {
          const d = result.diagnostic;
          const where = d.line ? ` at ${d.line}:${d.column}` : '';
          setStatus(`${d.kind === 'parse' ? 'Parse error' : 'Layout error'}${where}: ${d.message}`, 'error');
        }
        loading.hidden = true;
      } while (pending);
    } catch (e) {
      setStatus(`Error: ${errorMessage(e)}`, 'error');
      loading.hidden = true;
    } finally {
      running = false;
    }
  }

  let ready = false;
  void opts.engine.ready.then(() => { ready = true; }, () => { /* reported by the page */ });

  function schedule(): void {
    window.clearTimeout(timer);
    // before the engine is ready the page runs the first layout itself
    if (ready) timer = window.setTimeout(() => void update(), DEBOUNCE_MS);
    opts.onChange?.();
  }
  model.onDidChangeContent(() => schedule());

  function setText(text: string): void {
    model.setValue(text);
    editor.setPosition({ lineNumber: 1, column: 1 });
    editor.revealLine(1);
  }

  function setLoading(text: string | null): void {
    if (text === null) {
      loading.hidden = true;
    } else {
      loadingText.textContent = text;
      loading.hidden = false;
    }
  }

  return { editor, model, update, setText, lastResult: () => lastResult, fit, setLoading };
}
