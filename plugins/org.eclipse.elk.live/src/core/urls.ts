/*
 * URL handling of the pages, without DOM: model links (`?compressedContent=` LZString, elk-live
 * compatible) and the redirect of links shared from the earlier single-page version of the demo
 * (`index.html?compressedContent=…[&format=json]`, `index.html?initialContent=…`,
 * `index.html?e=<example>`), which now belong to the editor and examples pages.
 *
 * SPDX-License-Identifier: EPL-2.0 OR GPL-3.0-or-later
 */
import LZString from 'lz-string';

/**
 * The page an old single-page link belongs to, with its query string kept (`search` is
 * `location.search`), or `null` when the landing page itself was requested.
 */
export function legacyRedirect(search: string): string | null {
  const params = new URLSearchParams(search);
  const query = search.startsWith('?') ? search : `?${search}`;
  if (params.has('e')) return `examples.html${query}`;
  if (params.has('compressedContent') || params.has('initialContent')) {
    return `${params.get('format') === 'json' ? 'json.html' : 'elkgraph.html'}${query}`;
  }
  return null;
}

/** The editor text of `?compressedContent=` (LZString) or `?initialContent=`, else `fallback`. */
export function initialContent(search: string, fallback: string): string {
  const params = new URLSearchParams(search);
  if (params.has('compressedContent')) {
    return LZString.decompressFromEncodedURIComponent(params.get('compressedContent') ?? '') || fallback;
  }
  if (params.has('initialContent')) return params.get('initialContent') ?? fallback;
  return fallback;
}

/** `<page>?compressedContent=<LZString of text>`, resolved against `base` (elk-live's model link). */
export function modelLink(base: string, page: string, text: string): string {
  const url = new URL(page, base);
  url.search = '';
  url.hash = '';
  url.searchParams.set('compressedContent', LZString.compressToEncodedURIComponent(text));
  return url.href;
}
