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
 * Ported from elk-live client/src/json/elk-json-language.ts (language registration, language
 * configuration and Monarch tokenizer of ELK JSON, `elkj`) to the ESM API of current Monaco.
 * Changed for elk-lean: strings in double and single quotes are tokenized (the original never
 * entered its `string` state), property keys (quoted or not, followed by `:`) get their own token,
 * numbers and `true`/`false`/`null` are tokenized, auto-closing quotes; the empty `typeKeywords` and
 * `operators` lists are dropped.
 */
import type * as Monaco from 'monaco-editor/editor/editor.api';

export const ELKJ = 'elkj';

export function registerElkj(monaco: typeof Monaco): void {
  monaco.languages.register({ id: ELKJ, extensions: ['.elkj'] });

  monaco.languages.setLanguageConfiguration(ELKJ, {
    comments: { lineComment: '//', blockComment: ['/*', '*/'] },
    brackets: [['{', '}'], ['[', ']']],
    autoClosingPairs: [
      { open: '{', close: '}' },
      { open: '[', close: ']' },
      { open: '"', close: '"', notIn: ['string'] },
      { open: "'", close: "'", notIn: ['string'] },
    ],
    surroundingPairs: [
      { open: '{', close: '}' },
      { open: '[', close: ']' },
      { open: '"', close: '"' },
      { open: "'", close: "'" },
    ],
  });

  monaco.languages.setMonarchTokensProvider(ELKJ, {
    keywords: [
      'id', 'children', 'edges', 'ports', 'labels',
      'source', 'sources', 'target', 'targets',
      'text',
      'x', 'y', 'width', 'height',
      'layoutOptions', 'properties',
    ],
    constants: ['true', 'false', 'null'],
    symbols: /[=><!~?:&|+\-*/^%]+/,
    escapes: /\\(?:[btnfru\\"']|x[0-9A-Fa-f]{1,4}|u[0-9A-Fa-f]{4}|U[0-9A-Fa-f]{8})/,
    tokenizer: {
      root: [
        // quoted property keys: "a.b": / 'a.b':
        [/"(?:[^"\\]|\\.)*"(?=\s*:)/, 'type.identifier'],
        [/'(?:[^'\\]|\\.)*'(?=\s*:)/, 'type.identifier'],
        // identifiers and keywords (unquoted JSON5 keys)
        [/[a-zA-Z_$][\w$]*/, {
          cases: {
            '@constants': 'keyword',
            '@keywords': 'keyword',
            '@default': 'identifier',
          },
        }],
        { include: '@whitespace' },
        [/[{}()[\]]/, '@brackets'],
        [/[-+]?(?:\d+\.?\d*|\.\d+)(?:[eE][-+]?\d+)?/, 'number'],
        [/"/, 'string', '@string'],
        [/'/, 'string', '@sstring'],
        [/@symbols/, 'delimiter'],
        [/[,.]/, 'delimiter'],
      ],
      whitespace: [
        [/[ \t\r\n]+/, 'white'],
        [/\/\*/, 'comment', '@comment'],
        [/\/\/.*$/, 'comment'],
      ],
      comment: [
        [/[^/*]+/, 'comment'],
        [/\/\*/, 'comment.invalid'],
        [/\*\//, 'comment', '@pop'],
        [/[/*]/, 'comment'],
      ],
      string: [
        [/[^\\"]+/, 'string'],
        [/@escapes/, 'string.escape'],
        [/\\./, 'string.escape.invalid'],
        [/"/, 'string', '@pop'],
      ],
      sstring: [
        [/[^\\']+/, 'string'],
        [/@escapes/, 'string.escape'],
        [/\\./, 'string.escape.invalid'],
        [/'/, 'string', '@pop'],
      ],
    },
  } as Monaco.languages.IMonarchLanguage);
}
