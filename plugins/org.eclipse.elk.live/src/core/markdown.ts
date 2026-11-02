/*
 * Markdown of the example descriptions, rendered exactly as elk-live renders them
 * (client/src/examples/examples.ts): showdown with the GitHub flavour and
 * `simpleLineBreaks: false` (a paragraph needs a blank line). The descriptions come from
 * external/elk-models (trusted content), so no sanitising, as in elk-live. DOM-free.
 *
 * SPDX-License-Identifier: EPL-2.0 OR GPL-3.0-or-later
 */
import showdown from 'showdown';

showdown.setFlavor('github');
const converter = new showdown.Converter({ simpleLineBreaks: false });

/** The HTML of an `elkex:doc` section (showdown, GitHub flavour). */
export function renderMarkdown(md: string): string {
  return converter.makeHtml(md);
}
