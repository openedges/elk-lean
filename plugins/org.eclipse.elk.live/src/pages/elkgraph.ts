/*
 * elkgraph.html, "ELKT Editor" (elk-live client/src/elkgraph/editor.ts): ELK Text with highlighting,
 * parser error markers, option completion and hovers; edit -> convertElkt -> layout -> diagram.
 * "Open as JSON" converts the text (elk-live default sizes) and opens it in the JSON editor.
 *
 * SPDX-License-Identifier: EPL-2.0 OR GPL-3.0-or-later
 */
import { monaco } from '../editor/monaco.ts';
import { ELKT, registerElkt } from '../editor/elkt-language.ts';
import { registerCompletion } from '../editor/completion.ts';
import { registerElktFolding } from '../editor/elkt-folding.ts';
import { parseElktError } from '../core/pipeline.ts';
import { modelLink } from '../core/urls.ts';
import { startEditorPage } from '../app/editor-page.ts';
import { setStatus } from '../app/editor-diagram.ts';
import { errorMessage } from '../app/engine.ts';

const DEFAULT_ELKT = `algorithm: layered

node n1
node n2
node n3
edge n1 -> n2
edge n1 -> n3`;

startEditorPage({
  title: 'ELKT Editor',
  page: 'elkgraph.html',
  format: 'elkt',
  language: ELKT,
  defaultText: DEFAULT_ELKT,
  register: (engine) => {
    registerElkt(monaco);
    registerCompletion(monaco, engine.metadata);
    registerElktFolding(monaco);
  },
  tools: ({ engine, ctrl, linkHref }) => [{
    id: 'open-json-button',
    label: 'Open as JSON',
    title: 'Convert this graph to ELK JSON (with the default sizes) and open it in the JSON editor',
    onClick: () => {
      void engine.elk.convertElkt(ctrl().model.getValue(), { defaults: true }).then((graph) => {
        // keep this text in the history entry, so that Back returns to it
        history.replaceState(null, '', linkHref());
        location.href = modelLink(location.href, 'json.html', JSON.stringify(graph, null, 2));
      }, (e: unknown) => {
        const d = parseElktError(errorMessage(e));
        setStatus(`Cannot open as JSON: ${d.line ? `parse error at ${d.line}:${d.column}: ` : ''}${d.message}`, 'error');
      });
    },
  }],
});
