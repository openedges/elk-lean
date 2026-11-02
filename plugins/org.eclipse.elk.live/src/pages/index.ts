/*
 * index.html, "ELK Demonstrators" landing page (elk-live client/app/index.html): links to the
 * editors and the examples, dark-mode toggle, engine badge. Links shared from the earlier
 * single-page demo (`index.html?compressedContent=…`, `?initialContent=…`, `?e=…`) are forwarded to
 * the page that now shows them, with the query string kept.
 *
 * SPDX-License-Identifier: EPL-2.0 OR GPL-3.0-or-later
 */
import '../style.css';
import { legacyRedirect } from '../core/urls.ts';
import { darkToggle, engineBadge } from '../app/chrome.ts';
import { setupDarkMode } from '../app/dark-mode.ts';

const target = legacyRedirect(location.search);
if (target) {
  location.replace(new URL(target, location.href).href);
} else {
  document.getElementById('landing-tools')!.append(engineBadge(), darkToggle());
  setupDarkMode();
}
