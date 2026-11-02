/*
 * The edit -> diagram pipeline of the app, without DOM: ELK Text (or ELK JSON) -> ElkGraph JSON
 * (`elk.convertElkt`, Lean parser; JSON5 for ELK JSON like elk-live's json page) -> layout
 * (`elk.layout`) -> sprotty model. Errors are classified so that the editor can place a marker
 * (parse errors carry line and column).
 *
 * SPDX-License-Identifier: EPL-2.0 OR GPL-3.0-or-later
 */
import JSON5 from 'json5';
import type { ElkNode } from '@openedges/elk-lean';
import { elkToSprotty, type SGraph } from './elk-to-sprotty.ts';

/** The part of the elk-lean API the pipeline needs (`new ELK(...)`). */
export interface ElkLike {
  convertElkt(text: string, args?: { defaults?: boolean }): Promise<ElkNode>;
  layout(graph: ElkNode): Promise<ElkNode>;
}

export type InputFormat = 'elkt' | 'json';

export interface Diagnostic {
  /** `parse`: syntax/linking error of the input; `layout`: error of the layout engine */
  kind: 'parse' | 'layout';
  message: string;
  /** 1-based line and column when the message carries them */
  line?: number;
  column?: number;
}

export interface PipelineResult {
  ok: boolean;
  graph?: ElkNode;
  laidOut?: ElkNode;
  model?: SGraph;
  diagnostic?: Diagnostic;
  /** milliseconds of the conversion (parse) and layout steps */
  parseMs: number;
  layoutMs: number;
}

const ELKT_ERROR = /^ELK Text parse error: (\d+):(\d+): ([\s\S]*)$/;

/** Splits `ELK Text parse error: <line>:<col>: <message>` (the CLI / `convertElkt` message). */
export function parseElktError(message: string): Diagnostic {
  const m = ELKT_ERROR.exec(message);
  if (m) return { kind: 'parse', message: m[3], line: Number(m[1]), column: Number(m[2]) };
  return { kind: 'parse', message };
}

/** Offset of the first syntax error of a JSON text (a minimal validator), or -1 when it is valid. */
export function jsonErrorOffset(text: string): number {
  let i = 0;
  const n = text.length;
  const ws = () => { while (i < n && ' \t\r\n'.includes(text[i])) i++; };
  const fail = (): never => { throw i; };
  const lit = (w: string) => { if (text.startsWith(w, i)) i += w.length; else fail(); };
  const str = () => {
    i++;
    while (i < n && text[i] !== '"') {
      if (text[i] === '\\') i++;
      else if (text.charCodeAt(i) < 0x20) fail();
      i++;
    }
    if (i >= n) fail();
    i++;
  };
  const num = () => {
    const m = /^-?(?:0|[1-9]\d*)(?:\.\d+)?(?:[eE][+-]?\d+)?/.exec(text.substring(i));
    if (!m) fail();
    i += m![0].length;
  };
  const value = (): void => {
    ws();
    const c = text[i];
    if (c === '{') {
      i++; ws();
      if (text[i] === '}') { i++; return; }
      for (;;) {
        ws(); if (text[i] !== '"') fail(); str(); ws();
        if (text[i] !== ':') fail(); i++; value(); ws();
        if (text[i] === ',') { i++; continue; }
        if (text[i] === '}') { i++; return; }
        fail();
      }
    } else if (c === '[') {
      i++; ws();
      if (text[i] === ']') { i++; return; }
      for (;;) {
        value(); ws();
        if (text[i] === ',') { i++; continue; }
        if (text[i] === ']') { i++; return; }
        fail();
      }
    } else if (c === '"') str();
    else if (c === 't') lit('true');
    else if (c === 'f') lit('false');
    else if (c === 'n') lit('null');
    else num();
  };
  try {
    value(); ws();
    return i < n ? i : -1;
  } catch (pos) {
    return typeof pos === 'number' ? pos : 0;
  }
}

/** Line/column of a `JSON.parse` error (V8: "(line L column C)", "at position N", else located). */
export function parseJsonError(message: string, text: string): Diagnostic {
  const lc = /line (\d+) column (\d+)/.exec(message);
  if (lc) return { kind: 'parse', message, line: Number(lc[1]), column: Number(lc[2]) };
  const pos = /position (\d+)/.exec(message);
  const offset = pos ? Number(pos[1]) : jsonErrorOffset(text);
  if (offset >= 0) {
    const lines = text.slice(0, offset).split('\n');
    return { kind: 'parse', message, line: lines.length, column: lines[lines.length - 1].length + 1 };
  }
  return { kind: 'parse', message };
}

const JSON5_LOCATION = / at \d+:\d+$/;

/**
 * Parses ELK JSON like elk-live's json editor: JSON5 (comments, unquoted keys, single quotes,
 * trailing commas), so plain JSON works too. JSON5 syntax errors carry `lineNumber` and
 * `columnNumber`; other errors are located with `parseJsonError`.
 */
export function parseJsonInput(text: string): { graph: ElkNode; diagnostic?: undefined } | { graph?: undefined; diagnostic: Diagnostic } {
  try {
    return { graph: JSON5.parse(text) as ElkNode };
  } catch (e) {
    const err = e as { message?: unknown; lineNumber?: unknown; columnNumber?: unknown };
    const message = messageOf(e);
    if (typeof err.lineNumber === 'number' && typeof err.columnNumber === 'number') {
      // "JSON5: invalid character '}' at 1:29" -> "invalid character '}'" (the location is kept separately)
      const short = message.replace(/^JSON5: /, '').replace(JSON5_LOCATION, '');
      return { diagnostic: { kind: 'parse', message: short, line: err.lineNumber, column: err.columnNumber } };
    }
    return { diagnostic: parseJsonError(message, text) };
  }
}

/** `N nodes, M edges` of a laid-out graph (all levels; the root is not counted). */
export function countElements(g: ElkNode): string {
  let nodes = 0;
  let edges = 0;
  const visit = (n: ElkNode) => {
    for (const c of n.children ?? []) {
      nodes++;
      visit(c);
    }
    edges += (n.edges ?? []).length;
  };
  visit(g);
  return `${nodes} node${nodes === 1 ? '' : 's'}, ${edges} edge${edges === 1 ? '' : 's'}`;
}

function messageOf(err: unknown): string {
  if (err && typeof err === 'object' && 'message' in err) return String((err as { message: unknown }).message);
  return String(err);
}

const now = (): number => (typeof performance !== 'undefined' ? performance.now() : Date.now());

/**
 * Runs the pipeline once. ELK Text gets the elk-live default sizes (`defaults: true`: nodes 30,
 * ports 5, labels 9 x length by 16), like the elk-live language server. ELK JSON is laid out as
 * parsed: unlike elk-live, `org.eclipse.elk.json.edgeCoords` is not forced to `PARENT`
 * (`elkToSprotty` honours `shapeCoords`/`edgeCoords`), so the laid-out JSON is the engine's result
 * for the user's input.
 */
export async function runPipeline(elk: ElkLike, text: string, format: InputFormat = 'elkt'): Promise<PipelineResult> {
  const t0 = now();
  let graph: ElkNode;
  try {
    if (format === 'elkt') {
      graph = await elk.convertElkt(text, { defaults: true });
    } else {
      const parsed = parseJsonInput(text);
      if (parsed.diagnostic) return { ok: false, diagnostic: parsed.diagnostic, parseMs: now() - t0, layoutMs: 0 };
      graph = parsed.graph;
    }
  } catch (e) {
    return { ok: false, diagnostic: parseElktError(messageOf(e)), parseMs: now() - t0, layoutMs: 0 };
  }
  const t1 = now();
  let laidOut: ElkNode;
  try {
    laidOut = await elk.layout(graph);
  } catch (e) {
    return { ok: false, graph, diagnostic: { kind: 'layout', message: messageOf(e) }, parseMs: t1 - t0, layoutMs: now() - t1 };
  }
  const t2 = now();
  return { ok: true, graph, laidOut, model: elkToSprotty(laidOut), parseMs: t1 - t0, layoutMs: t2 - t1 };
}
