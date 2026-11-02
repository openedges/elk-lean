/*
 * Navbar and footer of the editor and examples pages (elk-live's elkgraph/json/examples
 * templates): brand link to the landing page, centered page title, engine badge (in place of
 * elk-live's ELK version menu: elk-lean is a single engine) and the dark-mode toggle; a footer with
 * the model link, the status line and the engine/license line.
 *
 * SPDX-License-Identifier: EPL-2.0 OR GPL-3.0-or-later
 */
import elkLeanPackage from 'elk-lean/package.json';

/** Version of the bundled elk-lean engine and of the ELK release it ports. */
export const ENGINE_VERSION: string = elkLeanPackage.version;
export const ELK_VERSION = '0.12.0';

export const ENGINE_BADGE = `elk-lean ${ENGINE_VERSION} · ELK ${ELK_VERSION}`;
const BADGE_TOOLTIP = `The layout runs in this browser: elk-lean ${ENGINE_VERSION}, the Eclipse Layout Kernel `
  + `${ELK_VERSION} ported to pure Lean 4, compiled to WebAssembly and run in a Web Worker. `
  + 'elk-live offers a menu of ELK versions here; elk-lean is a single engine, so there is nothing to choose.';

function el<K extends keyof HTMLElementTagNameMap>(tag: K, props: Partial<HTMLElementTagNameMap[K]> = {},
  ...children: (Node | string)[]): HTMLElementTagNameMap[K] {
  const e = Object.assign(document.createElement(tag), props);
  e.append(...children);
  return e;
}

/** The engine badge (also used on the landing page). */
export function engineBadge(): HTMLElement {
  return el('span', { className: 'engine-badge', id: 'engine-badge', title: BADGE_TOOLTIP }, ENGINE_BADGE);
}

/** The dark-mode toggle button (`#dark-toggle`, wired by `setupDarkMode`). */
export function darkToggle(): HTMLElement {
  const b = el('button', { type: 'button', id: 'dark-toggle', className: 'dark-toggle', title: 'Toggle dark mode' }, 'Dark');
  b.setAttribute('aria-pressed', 'false');
  return b;
}

/** Inserts the navbar at the top of `<body>`. */
export function mountNavbar(title: string): void {
  const logo = el('img', { className: 'logo-small', src: new URL('favicon.svg', document.baseURI).href, alt: '' });
  const nav = el('nav', { className: 'navbar' },
    el('a', { className: 'navbar-brand', href: 'index.html' }, logo, 'ELK Demonstrators'),
    el('div', { className: 'navbar-title' }, el('h1', {}, title)),
    el('div', { className: 'navbar-right' }, engineBadge(), darkToggle()));
  document.body.prepend(nav);
}

/**
 * Appends the footer: `Link to this model` + `Copy link` (when `modelLink`), the status line
 * (`#status`) and the engine/license line.
 */
export function mountFooter(opts: { modelLink: boolean }): void {
  const footer = el('footer', { className: 'statusbar' });
  if (opts.modelLink) {
    footer.append(
      el('a', { id: 'model-link', href: '#', title: 'Link to this model (the text is compressed into the URL)' }, 'Link to this model'),
      el('button', { type: 'button', id: 'copy-link-button', title: 'Copy the link to this model' }, 'Copy link'));
  }
  const status = el('span', { id: 'status' }, 'Starting…');
  status.setAttribute('role', 'status');
  const engine = el('span', { className: 'muted' });
  engine.innerHTML = `layout in the browser by <a href="https://www.eclipse.org/elk/">ELK</a> ${ELK_VERSION} in Lean 4 `
    + `(elk-lean ${ENGINE_VERSION}, WebAssembly) &middot; EPL-2.0 OR GPL-3.0-or-later`;
  footer.append(status, el('span', { className: 'spacer' }), engine);
  document.body.append(footer);
}
