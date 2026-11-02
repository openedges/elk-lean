// SPDX-License-Identifier: EPL-2.0 OR GPL-3.0-or-later
import { fileURLToPath } from 'node:url';
import { defineConfig } from 'vite';

// the pages (elk-live's demonstrators): landing page, ELKT editor, JSON editor, examples
const pages = ['index', 'elkgraph', 'json', 'examples'];

export default defineConfig({
  // relative asset URLs: dist/ works under any path (GitLab Pages project sub-path, file servers)
  base: './',
  optimizeDeps: {
    // elk-lean is a linked (file:) CommonJS package: pre-bundle its API module for the dev server
    include: ['@openedges/elk-lean/js/elk-api.js', 'sprotty', 'sprotty-protocol', 'inversify', 'lz-string', 'json5'],
  },
  build: {
    target: 'es2022',
    chunkSizeWarningLimit: 4096,
    rollupOptions: {
      input: Object.fromEntries(pages.map((p) => [p, fileURLToPath(new URL(`./${p}.html`, import.meta.url))])),
    },
  },
  worker: {
    format: 'es',
  },
});
