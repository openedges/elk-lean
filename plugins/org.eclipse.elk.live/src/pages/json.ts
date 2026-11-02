/*
 * json.html, "ELK JSON Editor" (elk-live client/src/json/editor.ts): ELK JSON parsed with JSON5,
 * syntax errors as markers with line/column, layout of the parsed object as given (elk-live
 * forces `org.eclipse.elk.json.edgeCoords: PARENT` for its renderer; the elk-lean renderer honours
 * the coordinate options, so the input is not changed).
 *
 * SPDX-License-Identifier: EPL-2.0 OR GPL-3.0-or-later
 */
import { monaco } from '../editor/monaco.ts';
import { ELKJ, registerElkj } from '../editor/elkj-language.ts';
import { startEditorPage } from '../app/editor-page.ts';

/** elk-live's default content of the JSON editor (json/editor.ts). */
const DEFAULT_JSON = `{
  id: "root",
  layoutOptions: { 'algorithm': 'layered' },
  children: [
    { id: "n1", width: 30, height: 30 },
    { id: "n2", width: 30, height: 30 },
    { id: "n3", width: 30, height: 30 }
  ],
  edges: [
    { id: "e1", sources: [ "n1" ], targets: [ "n2" ] },
    { id: "e2", sources: [ "n1" ], targets: [ "n3" ] }
  ]
}`;

startEditorPage({
  title: 'ELK JSON Editor',
  page: 'json.html',
  format: 'json',
  language: ELKJ,
  defaultText: DEFAULT_JSON,
  register: () => registerElkj(monaco),
});
