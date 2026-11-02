/*******************************************************************************
 * Copyright (c) 2017 TypeFox GmbH (http://www.typefox.io) and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * http://www.eclipse.org/legal/epl-2.0.
 *
 * SPDX-License-Identifier: EPL-2.0
 *******************************************************************************/
/*
 * Ported from elk-live client/src/elkgraph/elkt-language.ts (language registration, language
 * configuration and Monarch tokenizer of `.elkt`) to the ESM API of current Monaco, tokenising
 * exactly as elk-live does: keywords, identifiers, brackets and comments; strings, numbers and
 * option keys stay plain text (the original's `string` state is never entered, and it has no
 * number rule). Only the Monarch regexes were rewritten for the strict TypeScript build.
 */
import type * as Monaco from 'monaco-editor/editor/editor.api';

export const ELKT = 'elkt';

export function registerElkt(monaco: typeof Monaco): void {
  monaco.languages.register({ id: ELKT, extensions: ['.elkt'] });

  monaco.languages.setLanguageConfiguration(ELKT, {
    comments: { lineComment: '//', blockComment: ['/*', '*/'] },
    brackets: [['{', '}'], ['[', ']']],
    autoClosingPairs: [
      { open: '{', close: '}' },
      { open: '[', close: ']' },
    ],
  });

  monaco.languages.setMonarchTokensProvider(ELKT, {
    keywords: [
      'graph', 'node', 'label', 'port', 'edge', 'layout', 'position', 'size', 'incoming', 'outgoing',
      'start', 'end', 'bends', 'section', 'true', 'false',
    ],
    typeKeywords: [],
    operators: [],
    symbols: /[=><!~?:&|+\-*/^%]+/,
    escapes: /\\(?:[btnfru\\"']|x[0-9A-Fa-f]{1,4}|u[0-9A-Fa-f]{4}|U[0-9A-Fa-f]{8})/,
    tokenizer: {
      root: [
        // identifiers and keywords
        [/[a-z_$][\w$]*/, { cases: { '@typeKeywords': 'keyword', '@keywords': 'keyword', '@default': 'identifier' } }],
        { include: '@whitespace' },
        // delimiters and operators
        [/[{}()[\]]/, '@brackets'],
        [/[<>](?!@symbols)/, '@brackets'],
        [/@symbols/, { cases: { '@operators': 'operator', '@default': '' } }],
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
      // never entered (as in elk-live): kept for fidelity with the original grammar
      string: [
        [/[^\\"]+/, 'string'],
        [/@escapes/, 'string.escape'],
        [/\\./, 'string.escape.invalid'],
        [/"/, 'string', '@pop'],
      ],
    },
  } as Monaco.languages.IMonarchLanguage);
}
