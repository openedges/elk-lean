// SPDX-License-Identifier: EPL-2.0 OR GPL-3.0-or-later
/// <reference types="vite/client" />

// The ELK class of the elk-lean npm package without its backend loaders (worker mode only).
declare module '@openedges/elk-lean/js/elk-api.js' {
  import ELK from '@openedges/elk-lean';
  export default ELK;
}
