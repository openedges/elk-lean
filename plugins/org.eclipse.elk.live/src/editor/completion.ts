/*
 * Completion and hover providers for `.elkt` (replacing the Xtext language server of elk-live):
 * option keys filtered by the element they apply to (targets of `knownLayoutOptions()`), options
 * of the algorithm in scope first; values of ENUM / ENUMSET / BOOLEAN options and of `algorithm:`;
 * element keywords; hovers with an option's name, type, targets, literals and description.
 *
 * SPDX-License-Identifier: EPL-2.0 OR GPL-3.0-or-later
 */
import type * as Monaco from 'monaco-editor/editor/editor.api';
import { contextAt, resolveAlgorithm, resolveOption, TARGETS, type Metadata, type OptionInfo } from '../core/options.ts';
import { ELKT } from './elkt-language.ts';

const KEYWORD_SNIPPETS: [string, string, string][] = [
  ['node', 'node ${1:id}', 'node'],
  ['node {…}', 'node ${1:id} {\n\t$0\n}', 'node with a block (children, ports, labels, options)'],
  ['edge', 'edge ${1:source} -> ${2:target}', 'edge'],
  ['port', 'port ${1:id}', 'port'],
  ['label', 'label "${1:text}"', 'label'],
  ['layout', 'layout [ size: ${1:30}, ${2:30} ]', 'layout block (position / size)'],
];

function optionDoc(o: OptionInfo): string {
  const lines = [`**${o.name || o.shortId}** \`${o.id}\``, '', `type \`${o.type}\` · targets ${o.targets.join(', ') || '—'}`
    + (o.group ? ` · group \`${o.group}\`` : '')];
  if (o.choices.length) lines.push('', `values: ${o.choices.map((c) => `\`${c}\``).join(', ')}`);
  if (o.description) lines.push('', o.description);
  return lines.join('\n');
}

export function registerCompletion(monaco: typeof Monaco, getMeta: () => Metadata | null): Monaco.IDisposable[] {
  const { CompletionItemKind, CompletionItemInsertTextRule } = monaco.languages;

  const completion = monaco.languages.registerCompletionItemProvider(ELKT, {
    triggerCharacters: ['.', ':', ' '],
    provideCompletionItems(model, position) {
      const meta = getMeta();
      const line = model.getLineContent(position.lineNumber).substring(0, position.column - 1);
      const before = model.getValueInRange({ startLineNumber: 1, startColumn: 1, endLineNumber: position.lineNumber, endColumn: position.column });
      const ctx = contextAt(before);
      if (ctx.inLayoutBlock) return { suggestions: [] };

      // value position: `<key>: <prefix>`
      const val = /^\s*([A-Za-z_$][\w$.]*)\s*:\s*("?)([^"\s]*)$/.exec(line);
      if (val) {
        if (!meta) return { suggestions: [] };
        const prefixStart = position.column - val[3].length - val[2].length;
        const range = new monaco.Range(position.lineNumber, prefixStart, position.lineNumber, position.column);
        const option = resolveOption(meta, val[1]);
        if (!option) return { suggestions: [] };
        let values: { label: string; detail?: string; doc?: string }[] = [];
        if (option.id === 'org.eclipse.elk.algorithm') {
          values = meta.algorithms.map((a) => ({ label: a.shortId, detail: a.name, doc: a.description }));
        } else if (option.type === 'BOOLEAN') {
          values = [{ label: 'true' }, { label: 'false' }];
        } else if (option.choices.length) {
          values = option.choices.map((c) => ({ label: c }));
        }
        const quote = option.type === 'ENUMSET';
        return {
          suggestions: values.map((v, i) => ({
            label: v.label,
            kind: CompletionItemKind.EnumMember,
            detail: v.detail ?? option.shortId,
            documentation: v.doc ? { value: v.doc } : undefined,
            insertText: quote ? `"${v.label}"` : v.label,
            sortText: String(i).padStart(4, '0'),
            range,
          })),
        };
      }

      // key position: start of a statement
      const key = /^\s*([A-Za-z_$][\w$.]*)?$/.exec(line);
      if (!key) return { suggestions: [] };
      const prefix = key[1] ?? '';
      const range = new monaco.Range(position.lineNumber, position.column - prefix.length, position.lineNumber, position.column);
      const suggestions: Monaco.languages.CompletionItem[] = KEYWORD_SNIPPETS
        .filter(([label]) => ctx.element !== 'label' || label === 'label')
        .map(([label, snippet, doc]) => ({
          label,
          kind: CompletionItemKind.Keyword,
          insertText: snippet,
          insertTextRules: CompletionItemInsertTextRule.InsertAsSnippet,
          documentation: doc,
          sortText: '0' + label,
          range,
        }));
      if (meta) {
        const targets = TARGETS[ctx.element];
        const algorithm = ctx.algorithms.map((a) => resolveAlgorithm(meta, a)).find((a) => a !== undefined)
          ?? meta.algorithms.find((a) => a.id === 'org.eclipse.elk.layered');
        const known = new Set(algorithm?.knownOptions ?? []);
        for (const o of meta.options) {
          if (!o.targets.some((t) => targets.includes(t))) continue;
          const preferred = known.has(o.id) || o.id === 'org.eclipse.elk.algorithm';
          suggestions.push({
            label: { label: o.shortId, description: o.group || undefined, detail: '  ' + o.type.toLowerCase() } as Monaco.languages.CompletionItemLabel,
            kind: CompletionItemKind.Property,
            filterText: o.shortId,
            insertText: `${o.shortId}: `,
            documentation: { value: optionDoc(o) },
            sortText: (preferred ? '1' : '2') + o.shortId,
            range,
            command: o.choices.length || o.type === 'BOOLEAN' || o.id === 'org.eclipse.elk.algorithm'
              ? { id: 'editor.action.triggerSuggest', title: 'values' } : undefined,
          });
        }
      }
      return { suggestions };
    },
  });

  const hover = monaco.languages.registerHoverProvider(ELKT, {
    provideHover(model, position) {
      const meta = getMeta();
      if (!meta) return null;
      const line = model.getLineContent(position.lineNumber);
      const re = /([A-Za-z_$][\w$]*(?:\.[A-Za-z_$][\w$]*)*)\s*:/g;
      for (let m = re.exec(line); m; m = re.exec(line)) {
        const start = m.index + 1;
        const end = start + m[1].length;
        if (position.column >= start && position.column <= end) {
          const o = resolveOption(meta, m[1]);
          if (!o) return null;
          return {
            range: new monaco.Range(position.lineNumber, start, position.lineNumber, end),
            contents: [{ value: optionDoc(o) }],
          };
        }
      }
      return null;
    },
  });
  return [completion, hover];
}
