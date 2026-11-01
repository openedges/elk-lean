// SPDX-License-Identifier: EPL-2.0 OR GPL-3.0-or-later
import { defineConfig } from 'vite';

export default defineConfig({
  // relative asset URLs: dist/ works under any path (GitLab Pages project sub-path, file servers)
  base: './',
  optimizeDeps: {
    // elk-lean is a linked (file:) CommonJS package: pre-bundle its API module for the dev server
    include: ['elk-lean/js/elk-api.js', 'sprotty', 'sprotty-protocol', 'inversify', 'lz-string'],
  },
  build: {
    target: 'es2022',
    chunkSizeWarningLimit: 4096,
  },
  worker: {
    format: 'es',
  },
});
