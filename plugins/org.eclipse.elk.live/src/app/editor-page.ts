/*
 * The common part of the two editor pages (elkgraph.html, json.html; elk-live's
 * elkgraph/editor.ts and json/editor.ts): navbar, footer with the model link, the engine, the
 * editor + diagram pair, start-up status and the `window.elkLive` handle for tests.
 *
 * SPDX-License-Identifier: EPL-2.0 OR GPL-3.0-or-later
 */
import { monaco } from '../editor/monaco.ts';
import type { InputFormat } from '../core/pipeline.ts';
import { initialContent, modelLink } from '../core/urls.ts';
import { mountFooter, mountNavbar } from './chrome.ts';
import { setupDarkMode } from './dark-mode.ts';
import { errorMessage, startEngine, type Engine } from './engine.ts';
import { createEditorDiagram, setStatus, type EditorDiagram, type ToolButton } from './editor-diagram.ts';

export interface EditorPageOptions {
  title: string;
  /** this page's file (`elkgraph.html`, `json.html`), the target of the model link */
  page: string;
  format: InputFormat;
  language: string;
  defaultText: string;
  /** registers the Monaco language (and providers) before the editor is created */
  register: (engine: Engine) => void;
  tools?: (ctx: { engine: Engine; ctrl: () => EditorDiagram; linkHref: () => string }) => ToolButton[];
}

export function startEditorPage(opts: EditorPageOptions): { engine: Engine; ctrl: EditorDiagram } {
  mountNavbar(opts.title);
  mountFooter({ modelLink: true });
  setupDarkMode();

  const engine = startEngine();
  opts.register(engine);

  // ------------------------------------------------------------ model link (elk-live setupModelLink)
  let ctrl: EditorDiagram;
  const linkHref = () => modelLink(location.href, opts.page, ctrl.model.getValue());
  const linkAnchor = document.getElementById('model-link') as HTMLAnchorElement;
  let linkTimer: number | undefined;
  const updateLink = () => {
    window.clearTimeout(linkTimer);
    linkTimer = window.setTimeout(() => linkAnchor.setAttribute('href', linkHref()), 400);
  };

  ctrl = createEditorDiagram({
    engine,
    format: opts.format,
    language: opts.language,
    initialText: initialContent(location.search, opts.defaultText),
    fileName: () => 'graph',
    tools: opts.tools?.({ engine, ctrl: () => ctrl, linkHref }),
    onChange: updateLink,
  });
  updateLink();

  document.getElementById('copy-link-button')!.addEventListener('click', () => {
    const href = linkHref();
    linkAnchor.href = href;
    navigator.clipboard.writeText(href).then(() => setStatus('Link copied to the clipboard', 'ok'),
      () => setStatus('Copying failed; use "Link to this model" instead', 'error'));
  });

  setStatus('Loading the layout engine (WebAssembly, ~20 MB) in a Web Worker…');
  engine.ready.then((ms) => {
    ctrl.setLoading('Laying out…');
    setStatus(`Layout engine ready (${(ms / 1000).toFixed(1)} s)`);
    void ctrl.update();
  }).catch((e: unknown) => {
    const msg = errorMessage(e);
    ctrl.setLoading(`The layout engine could not be loaded: ${msg}`);
    setStatus(`The layout engine could not be loaded: ${msg}`, 'error');
  });

  // debugging / tests
  (window as unknown as { elkLive: unknown }).elkLive = { elk: engine.elk, editor: ctrl.editor, monaco, update: ctrl.update };
  return { engine, ctrl };
}
