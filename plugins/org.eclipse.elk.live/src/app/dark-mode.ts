/*
 * Dark mode of all pages (elk-live's simple-dark-mode-toggle, without the dependency): the
 * `elk-dark-mode` class on `<body>`, remembered per browser under `elk-lean-live-dark-mode`,
 * defaulting to the system preference. Listeners (the Monaco theme) are called on every change.
 *
 * SPDX-License-Identifier: EPL-2.0 OR GPL-3.0-or-later
 */

const DARK_KEY = 'elk-lean-live-dark-mode';

function storedDark(): boolean | null {
  try {
    const v = localStorage.getItem(DARK_KEY);
    return v === null ? null : v === 'true';
  } catch {
    return null;
  }
}

let dark = storedDark() ?? window.matchMedia('(prefers-color-scheme: dark)').matches;
const listeners: ((dark: boolean) => void)[] = [];

function apply(): void {
  document.body.classList.toggle('elk-dark-mode', dark);
  document.getElementById('dark-toggle')?.setAttribute('aria-pressed', String(dark));
  for (const l of listeners) l(dark);
}

export function isDark(): boolean {
  return dark;
}

/** Calls `listener` now and on every change. */
export function onDarkModeChange(listener: (dark: boolean) => void): void {
  listeners.push(listener);
  listener(dark);
}

/** Applies the stored mode and wires the `#dark-toggle` button. */
export function setupDarkMode(): void {
  document.getElementById('dark-toggle')?.addEventListener('click', () => {
    dark = !dark;
    try {
      localStorage.setItem(DARK_KEY, String(dark));
    } catch { /* storage unavailable */ }
    apply();
  });
  apply();
}
