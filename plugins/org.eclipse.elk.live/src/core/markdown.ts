/*
 * Tiny markdown subset for the example descriptions (elk-live renders them with showdown):
 * paragraphs, `code`, **strong**, _emphasis_ / *emphasis*, [links](url), "- " lists. The input is
 * HTML-escaped first; only http(s) and relative link targets are kept.
 *
 * SPDX-License-Identifier: EPL-2.0 OR GPL-3.0-or-later
 */

const escapeHtml = (s: string): string =>
  s.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;').replace(/"/g, '&quot;');

function inline(s: string): string {
  return s
    .replace(/`([^`]+)`/g, '<code>$1</code>')
    .replace(/\*\*([^*]+)\*\*/g, '<strong>$1</strong>')
    .replace(/(^|[\s(])_([^_]+)_(?=[\s).,;:!?]|$)/g, '$1<em>$2</em>')
    .replace(/(^|[\s(])\*([^*]+)\*(?=[\s).,;:!?]|$)/g, '$1<em>$2</em>')
    .replace(/\[([^\]]+)\]\(([^)\s]+)\)/g, (_m, text: string, url: string) =>
      /^(https?:\/\/|\.{0,2}\/|#)/.test(url) && !/^javascript:/i.test(url)
        ? `<a href="${url}" target="_blank" rel="noopener">${text}</a>` : text);
}

export function renderMarkdown(md: string): string {
  const blocks = escapeHtml(md.replace(/\r\n/g, '\n')).split(/\n\s*\n/);
  return blocks.map((b) => {
    const lines = b.split('\n').map((l) => l.trim()).filter((l) => l.length > 0);
    if (lines.length === 0) return '';
    if (lines.every((l) => /^[-*] /.test(l))) {
      return '<ul>' + lines.map((l) => `<li>${inline(l.substring(2))}</li>`).join('') + '</ul>';
    }
    return `<p>${inline(lines.join(' '))}</p>`;
  }).join('\n');
}
