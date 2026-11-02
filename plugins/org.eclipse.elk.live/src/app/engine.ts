/*
 * The layout engine of the editor pages: the elk-lean `ELK` class in Web Worker mode (the WASM
 * backend runs in the worker, served unbundled from public/elk-lean/ by scripts/copy-assets.mjs)
 * and the completion metadata (`knownLayoutOptions()`, `knownLayoutAlgorithms()`, enum literals).
 *
 * SPDX-License-Identifier: EPL-2.0 OR GPL-3.0-or-later
 */
// the ELK class only: the WASM backend runs in the Web Worker
import ELK from '@openedges/elk-lean/js/elk-api.js';
import { buildMetadata, type Metadata } from '../core/options.ts';
import choices from '../generated/option-choices.json';

export interface Engine {
  elk: InstanceType<typeof ELK>;
  /** resolves with the start-up time (ms) once the worker answered the metadata queries */
  ready: Promise<number>;
  /** completion metadata, `null` until `ready` */
  metadata(): Metadata | null;
}

/** Base URL of the site (`base: './'`): the directory of the page. */
export const baseUrl = new URL(import.meta.env.BASE_URL, document.baseURI);

export function startEngine(): Engine {
  const elk = new ELK({ workerUrl: new URL('elk-lean/js/elk-worker.js', baseUrl).href });
  let metadata: Metadata | null = null;
  const ready = (async () => {
    const t0 = performance.now();
    const [options, algorithms] = await Promise.all([elk.knownLayoutOptions(), elk.knownLayoutAlgorithms()]);
    metadata = buildMetadata(options as unknown as Record<string, unknown>[],
      algorithms as unknown as Record<string, unknown>[], choices as Record<string, string[]>);
    return performance.now() - t0;
  })();
  return { elk, ready, metadata: () => metadata };
}

/** The message of a thrown value (worker errors are plain objects with `message`). */
export function errorMessage(e: unknown): string {
  return e && typeof e === 'object' && 'message' in e ? String((e as { message: unknown }).message) : String(e);
}
