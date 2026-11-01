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
 * configuration and Monarch tokenizer of `.elkt`) to the ESM API of current Monaco. Changed for
 * elk-lean: strings and numbers are tokenized (the original never entered its `string` state),
 * option keys (`a.b.c:`) get their own token, `null` is a keyword, auto-closing quotes.
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
      { open: '"', close: '"', notIn: ['string'] },
    ],
    surroundingPairs: [
      { open: '{', close: '}' },
      { open: '[', close: ']' },
      { open: '"', close: '"' },
    ],
    wordPattern: /[A-Za-z_$][\w$.]*|-?\d+(?:\.\d+)?(?:[eE][+-]?\d+)?/,
    indentationRules: {
      increaseIndentPattern: /\{[^}"']*$/,
      decreaseIndentPattern: /^\s*\}/,
    },
  });

  monaco.languages.setMonarchTokensProvider(ELKT, {
    keywords: [
      'graph', 'node', 'label', 'port', 'edge', 'layout', 'position', 'size', 'incoming', 'outgoing',
      'start', 'end', 'bends', 'section', 'true', 'false', 'null',
    ],
    symbols: /[=><!~?:&|+\-*/^%]+/,
    escapes: /\\(?:[btnfru\\"']|x[0-9A-Fa-f]{1,4}|u[0-9A-Fa-f]{4}|U[0-9A-Fa-f]{8})/,
    tokenizer: {
      root: [
        // option keys: identifiers (with dots) directly followed by ':'
        [/[a-zA-Z_$][\w$]*(?:\.[a-zA-Z_$][\w$]*)*(?=\s*:)/, 'type.identifier'],
        [/[a-zA-Z_$][\w$]*/, { cases: { '@keywords': 'keyword', '@default': 'identifier' } }],
        { include: '@whitespace' },
        [/[{}()[\]]/, '@brackets'],
        [/-?\d+(?:\.\d+)?(?:[eE][+-]?\d+)?/, 'number'],
        [/"/, 'string', '@string'],
        [/'/, 'string', '@sstring'],
        [/->/, 'operator'],
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
