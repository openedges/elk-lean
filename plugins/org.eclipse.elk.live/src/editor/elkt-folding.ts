/*
 * Folding ranges of `.elkt` as elk-live's editor receives them from its Xtext 2.36.0 language
 * server (`textDocument/foldingRange`; Monaco uses only these, no indentation fallback):
 *  - every model object below the root whose text spans more than one line: node, port, label,
 *    edge, edge section (also the unnamed single section of an edge `layout`), bend point and
 *    property entry (`org.eclipse.xtext.ide.editor.folding.DefaultFoldingRangeProvider`:
 *    `isHandled` = has a container; the region is `ILocationInFileProvider.getFullTextRegion`,
 *    i.e. the object's first to last significant token — leading and trailing comments and
 *    whitespace excluded; `FoldingRangeService` keeps a region when its start and end lines differ);
 *  - every `/* … *\/` comment (kind `comment`); line comments are not folded.
 * The parser below follows ElkGraph.xtext (`external/elk/plugins/org.eclipse.elk.graph.text`) and
 * is tolerant of syntax errors so that typing keeps the controls of the intact objects; Xtext's
 * ANTLR error recovery is not reproduced, so the ranges of a broken document may differ from the
 * original. Regions are collected in model order (parent before children) and a second region at
 * an offset already taken is dropped, as the provider's offset-ordered `TreeSet` does.
 *
 * SPDX-License-Identifier: EPL-2.0 OR GPL-3.0-or-later
 */
import type * as Monaco from 'monaco-editor/editor/editor.api';
import { ELKT } from './elkt-language.ts';

/** A folding region in text offsets, `[start, end)`; `kind` is set for block comments. */
export interface ElktFoldingRegion {
  start: number;
  end: number;
  kind?: 'comment';
}

/** A folding range in 0-based lines, as the language server protocol reports it. */
export interface ElktFoldingRange {
  startLine: number;
  endLine: number;
  kind?: 'comment';
}

interface Token {
  kind: 'id' | 'string' | 'number' | 'punct';
  text: string;
  start: number;
  end: number;
}

/** Keywords of the grammar; an identifier spelled like one needs the `^` escape. */
const KEYWORDS = new Set([
  'graph', 'node', 'label', 'port', 'edge', 'layout', 'position', 'size', 'incoming', 'outgoing',
  'start', 'end', 'bends', 'section', 'true', 'false', 'null',
]);

function isIdStart(c: string | undefined): boolean {
  return c !== undefined && /[A-Za-z_]/.test(c);
}

function isIdPart(c: string | undefined): boolean {
  return c !== undefined && /[A-Za-z0-9_]/.test(c);
}

function isDigit(c: string | undefined): boolean {
  return c !== undefined && c >= '0' && c <= '9';
}

/**
 * The terminals of the grammar (`org.eclipse.xtext.common.Terminals` plus SIGNED_INT and FLOAT):
 * hidden tokens (whitespace, `//` and `/* *\/` comments) are skipped, block comments collected.
 */
function tokenize(text: string, comments: ElktFoldingRegion[]): Token[] {
  const tokens: Token[] = [];
  const n = text.length;
  let i = 0;
  while (i < n) {
    const c = text[i];
    if (c === ' ' || c === '\t' || c === '\r' || c === '\n') {
      i++;
      continue;
    }
    if (c === '/' && text[i + 1] === '/') {
      let j = i + 2;
      while (j < n && text[j] !== '\n' && text[j] !== '\r') j++;
      i = j;
      continue;
    }
    if (c === '/' && text[i + 1] === '*') {
      const close = text.indexOf('*/', i + 2);
      const end = close < 0 ? n : close + 2;
      comments.push({ start: i, end, kind: 'comment' });
      i = end;
      continue;
    }
    if (c === '"' || c === "'") {
      let j = i + 1;
      while (j < n && text[j] !== c) {
        if (text[j] === '\\') j++;
        j++;
      }
      const end = Math.min(j + 1, n);
      tokens.push({ kind: 'string', text: text.slice(i, end), start: i, end });
      i = end;
      continue;
    }
    if (c === '-' && text[i + 1] === '>') {
      tokens.push({ kind: 'punct', text: '->', start: i, end: i + 2 });
      i += 2;
      continue;
    }
    if (isDigit(c) || ((c === '-' || c === '+') && isDigit(text[i + 1]))) {
      let j = i + 1;
      while (j < n && isDigit(text[j])) j++;
      if (text[j] === '.' && isDigit(text[j + 1])) {
        j += 2;
        while (j < n && isDigit(text[j])) j++;
      }
      if (text[j] === 'e' || text[j] === 'E') {
        let k = j + 1;
        if (text[k] === '+' || text[k] === '-') k++;
        if (isDigit(text[k])) {
          while (k < n && isDigit(text[k])) k++;
          j = k;
        }
      }
      tokens.push({ kind: 'number', text: text.slice(i, j), start: i, end: j });
      i = j;
      continue;
    }
    if (isIdStart(c) || (c === '^' && isIdStart(text[i + 1]))) {
      let j = i + 1;
      while (j < n && isIdPart(text[j])) j++;
      tokens.push({ kind: 'id', text: text.slice(i, j), start: i, end: j });
      i = j;
      continue;
    }
    tokens.push({ kind: 'punct', text: c, start: i, end: i + 1 });
    i++;
  }
  return tokens;
}

/** Recursive descent over the grammar's rules, recording the region of every object. */
class Parser {
  private pos = 0;
  /** End offset of the last consumed token. */
  private last = 0;
  readonly regions: ElktFoldingRegion[] = [];
  private readonly tokens: Token[];

  constructor(tokens: Token[]) {
    this.tokens = tokens;
  }

  private peek(k = 0): Token | undefined {
    return this.tokens[this.pos + k];
  }

  private isKw(word: string, k = 0): boolean {
    const t = this.peek(k);
    return t !== undefined && t.kind === 'id' && t.text === word;
  }

  private isPunct(p: string, k = 0): boolean {
    const t = this.peek(k);
    return t !== undefined && t.kind === 'punct' && t.text === p;
  }

  /** An ID that is not a keyword. */
  private isName(k = 0): boolean {
    const t = this.peek(k);
    return t !== undefined && t.kind === 'id' && !KEYWORDS.has(t.text);
  }

  private isNumber(k = 0): boolean {
    return this.peek(k)?.kind === 'number';
  }

  private next(): Token {
    const t = this.tokens[this.pos++];
    this.last = t.end;
    return t;
  }

  private accept(p: string): boolean {
    if (!this.isPunct(p)) return false;
    this.next();
    return true;
  }

  private acceptKw(w: string): boolean {
    if (!this.isKw(w)) return false;
    this.next();
    return true;
  }

  /** Opens an object's region in model order; `close` sets its end. */
  private open(start: number): number {
    return this.regions.push({ start, end: start }) - 1;
  }

  private close(index: number): void {
    this.regions[index].end = this.last;
  }

  /** `PropertyKey ':'` ahead (ID ('.' ID)* — a `hidden()` rule, comments inside are not checked). */
  private atProperty(): boolean {
    if (!this.isName()) return false;
    let k = 1;
    while (this.isPunct('.', k) && this.isName(k + 1)) k += 2;
    return this.isPunct(':', k);
  }

  private atElement(): boolean {
    return this.isKw('node') || this.isKw('label') || this.isKw('port') || this.isKw('edge');
  }

  /** RootNode: `('graph' ID)? ShapeLayout? Property* (ElkLabel | ElkPort | ElkNode | ElkEdge)*`. */
  root(): void {
    if (this.acceptKw('graph') && this.isName()) this.next();
    this.shapeLayout();
    this.members({ ports: true, children: true }, null);
  }

  /**
   * The body of a node, port or label (and of the root): `Property*` and the elements the rule
   * allows, up to `closer` or the end of the text. Unexpected tokens are skipped; an element the
   * rule does not allow ends the body (recovery for a missing `}`).
   */
  private members(allow: { ports: boolean; children: boolean }, closer: '}' | null): void {
    for (;;) {
      const t = this.peek();
      if (t === undefined) return;
      if (closer !== null && this.isPunct(closer)) return;
      if (this.isKw('layout')) {
        this.shapeLayout();
      } else if (this.atProperty()) {
        this.property();
      } else if (this.isKw('label')) {
        this.label();
      } else if (this.isKw('port')) {
        if (!allow.ports) return;
        this.port();
      } else if (this.isKw('node')) {
        if (!allow.children) return;
        this.node();
      } else if (this.isKw('edge')) {
        if (!allow.children) return;
        this.edge();
      } else {
        this.next();
      }
    }
  }

  /** ElkNode: `'node' ID ('{' ShapeLayout? Property* (ElkLabel | ElkPort | ElkNode | ElkEdge)* '}')?`. */
  private node(): void {
    const r = this.open(this.next().start);
    if (this.isName()) this.next();
    if (this.accept('{')) {
      this.shapeLayout();
      this.members({ ports: true, children: true }, '}');
      this.accept('}');
    }
    this.close(r);
  }

  /** ElkPort: `'port' ID ('{' ShapeLayout? Property* ElkLabel* '}')?`. */
  private port(): void {
    const r = this.open(this.next().start);
    if (this.isName()) this.next();
    if (this.accept('{')) {
      this.shapeLayout();
      this.members({ ports: false, children: false }, '}');
      this.accept('}');
    }
    this.close(r);
  }

  /** ElkLabel: `'label' (ID ':')? STRING ('{' ShapeLayout? Property* ElkLabel* '}')?`. */
  private label(): void {
    const r = this.open(this.next().start);
    if (this.isName() && this.isPunct(':', 1)) {
      this.next();
      this.next();
    }
    if (this.peek()?.kind === 'string') this.next();
    if (this.accept('{')) {
      this.shapeLayout();
      this.members({ ports: false, children: false }, '}');
      this.accept('}');
    }
    this.close(r);
  }

  /**
   * ElkEdge: `'edge' (ID ':')? QualifiedId (',' QualifiedId)* '->' QualifiedId (',' QualifiedId)*
   * ('{' EdgeLayout? Property* ElkLabel* '}')?`.
   */
  private edge(): void {
    const r = this.open(this.next().start);
    if (this.isName() && this.isPunct(':', 1)) {
      this.next();
      this.next();
    }
    this.qualifiedIds();
    if (this.accept('->')) this.qualifiedIds();
    if (this.accept('{')) {
      if (this.isKw('layout')) this.edgeLayout();
      this.members({ ports: false, children: false }, '}');
      this.accept('}');
    }
    this.close(r);
  }

  /** `QualifiedId (',' QualifiedId)*`. */
  private qualifiedIds(): void {
    if (!this.isName()) return;
    for (;;) {
      this.qualifiedId();
      if (!(this.isPunct(',') && this.isName(1))) return;
      this.next();
    }
  }

  /** QualifiedId: `ID ('.' ID)*`. */
  private qualifiedId(): void {
    this.next();
    while (this.isPunct('.') && this.isName(1)) {
      this.next();
      this.next();
    }
  }

  /**
   * ShapeLayout (a fragment, part of the enclosing object): `'layout' '[' (('position' ':' Number
   * ',' Number)? & ('size' ':' Number ',' Number)?) ']'`.
   */
  private shapeLayout(): void {
    if (!this.acceptKw('layout')) return;
    if (!this.accept('[')) return;
    while (this.peek() !== undefined && !this.isPunct(']')) {
      if (this.atElement() || this.isPunct('}')) return;
      this.next();
    }
    this.accept(']');
  }

  /** EdgeLayout (a fragment): `'layout' '[' (ElkSingleEdgeSection | ElkEdgeSection+) ']'`. */
  private edgeLayout(): void {
    this.next();
    if (!this.accept('[')) return;
    if (this.isKw('section')) {
      while (this.isKw('section')) this.section();
    } else {
      this.sectionContent(true);
    }
    this.accept(']');
  }

  /** ElkEdgeSection: `'section' ID ('->' ID (',' ID)*)? '[' <section content> ']'`. */
  private section(): void {
    const r = this.open(this.next().start);
    if (this.isName()) this.next();
    if (this.accept('->') && this.isName()) {
      this.next();
      while (this.isPunct(',') && this.isName(1)) {
        this.next();
        this.next();
      }
    }
    if (this.accept('[')) {
      this.sectionContent(false);
      this.accept(']');
    }
    this.close(r);
  }

  /**
   * The content of a section: `(('incoming' ':' QualifiedId)? & ('outgoing' ':' QualifiedId)? &
   * ('start' ':' Number ',' Number)? & ('end' ':' Number ',' Number)?) ('bends' ':' ElkBendPoint
   * ('|' ElkBendPoint)*)? Property*`. ElkSingleEdgeSection (`single`) is an object of its own
   * (`{ElkEdgeSection}`) whose region covers exactly these tokens; it is empty, and so not folded,
   * when the edge's `layout [ ]` has no content.
   */
  private sectionContent(single: boolean): void {
    const first = this.peek();
    const r = single && first !== undefined ? this.open(first.start) : -1;
    for (;;) {
      const t = this.peek();
      if (t === undefined || this.isPunct(']') || this.isPunct('}')) break;
      if (this.isKw('incoming') || this.isKw('outgoing')) {
        this.next();
        this.accept(':');
        if (this.isName()) this.qualifiedId();
      } else if (this.isKw('start') || this.isKw('end')) {
        this.next();
        this.accept(':');
        this.numberPair();
      } else if (this.isKw('bends')) {
        this.next();
        this.accept(':');
        this.bendPoint();
        while (this.accept('|')) this.bendPoint();
      } else if (this.atProperty()) {
        this.property();
      } else if (this.atElement() || this.isKw('section') || this.isKw('layout')) {
        break;
      } else {
        this.next();
      }
    }
    if (r >= 0) {
      if (this.peek() === first) this.regions.splice(r, 1);
      else this.close(r);
    }
  }

  /** ElkBendPoint: `Number ',' Number`. */
  private bendPoint(): void {
    if (!this.isNumber()) return;
    const r = this.open(this.next().start);
    if (this.accept(',') && this.isNumber()) this.next();
    this.close(r);
  }

  private numberPair(): void {
    if (this.isNumber()) this.next();
    if (this.accept(',') && this.isNumber()) this.next();
  }

  /**
   * Property: `PropertyKey ':' (STRING | QualifiedId | Number | 'true' | 'false' | 'null')` — a map
   * entry object, folded when key and value are on different lines.
   */
  private property(): void {
    const r = this.open(this.next().start);
    while (this.isPunct('.') && this.isName(1)) {
      this.next();
      this.next();
    }
    this.accept(':');
    const v = this.peek();
    if (v !== undefined) {
      if (v.kind === 'string' || v.kind === 'number') this.next();
      else if (v.kind === 'id' && !KEYWORDS.has(v.text)) this.qualifiedId();
      else if (v.kind === 'id' && (v.text === 'true' || v.text === 'false' || v.text === 'null')) this.next();
    }
    this.close(r);
  }
}

/** The folding regions of an ELK Text document, in text offsets and ordered by start. */
export function elktFoldingRegions(text: string): ElktFoldingRegion[] {
  const comments: ElktFoldingRegion[] = [];
  const parser = new Parser(tokenize(text, comments));
  parser.root();
  const byStart = new Map<number, ElktFoldingRegion>();
  for (const region of [...parser.regions, ...comments]) {
    if (!byStart.has(region.start)) byStart.set(region.start, region);
  }
  return [...byStart.values()].sort((a, b) => a.start - b.start);
}

/**
 * The folding ranges in 0-based lines (lines end at `\n`, `\r\n` or `\r`), as the language server
 * reports them: regions whose start and end lines differ.
 */
export function elktFoldingRanges(text: string): ElktFoldingRange[] {
  const lineStarts = [0];
  for (let i = 0; i < text.length; i++) {
    if (text[i] === '\n') lineStarts.push(i + 1);
    else if (text[i] === '\r') {
      if (text[i + 1] === '\n') i++;
      lineStarts.push(i + 1);
    }
  }
  const lineOf = (offset: number): number => {
    let lo = 0;
    let hi = lineStarts.length - 1;
    while (lo < hi) {
      const mid = (lo + hi + 1) >> 1;
      if (lineStarts[mid] <= offset) lo = mid;
      else hi = mid - 1;
    }
    return lo;
  };
  const result: ElktFoldingRange[] = [];
  for (const region of elktFoldingRegions(text)) {
    const startLine = lineOf(region.start);
    const endLine = lineOf(region.end);
    if (startLine < endLine) {
      result.push(region.kind === 'comment' ? { startLine, endLine, kind: 'comment' } : { startLine, endLine });
    }
  }
  return result;
}

/** Registers the folding range provider of `.elkt` models. */
export function registerElktFolding(monaco: typeof Monaco): Monaco.IDisposable {
  return monaco.languages.registerFoldingRangeProvider(ELKT, {
    provideFoldingRanges(model) {
      const ranges: Monaco.languages.FoldingRange[] = [];
      for (const region of elktFoldingRegions(model.getValue())) {
        const start = model.getPositionAt(region.start).lineNumber;
        const end = model.getPositionAt(region.end).lineNumber;
        if (start < end) {
          ranges.push(region.kind === 'comment'
            ? { start, end, kind: monaco.languages.FoldingRangeKind.Comment }
            : { start, end });
        }
      }
      return ranges;
    },
  });
}
