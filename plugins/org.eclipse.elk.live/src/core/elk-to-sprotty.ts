/*
 * ELK JSON (laid out) -> sprotty model, the visual model of elk-live
 * (external/elk-live/client/src/json/elkgraph-to-sprotty.ts and the server's
 * ElkGraphDiagramGenerator.processContent): nodes, ports and labels keep their positions relative
 * to the parent, edges become children of the node their coordinates refer to, every edge section
 * is one polyline (start point, bend points, end point), junction points are small circles.
 * Written for elk-lean; differs from elk-live where elk-live loses layout information: each section
 * of a hyperedge is its own polyline (elk-live joins all sections into one), an edge is placed under
 * its `container` (elk-live: under the node whose `edges` list holds it), and the JSON coordinate
 * modes `elk.json.shapeCoords` / `elk.json.edgeCoords` are honoured.
 *
 * DOM-free (used by the app and by the Node smoke test).
 *
 * SPDX-License-Identifier: EPL-2.0 OR GPL-3.0-or-later
 */
import type { ElkEdgeSection, ElkExtendedEdge, ElkLabel, ElkNode, ElkPoint, ElkPort } from 'elk-lean';

/** Sprotty schema element (the subset of sprotty-protocol `SModelElement` this app emits). */
export interface SElement {
  type: string;
  id: string;
  children?: SElement[];
  position?: { x: number; y: number };
  size?: { width: number; height: number };
  text?: string;
  sourceId?: string;
  targetId?: string;
  routingPoints?: { x: number; y: number }[];
  /** edge section: draw an arrow head at the end (the section ends at a target shape) */
  arrow?: boolean;
  /** node / port / label kind for styling (`hierarchical` for nodes with children) */
  cssClasses?: string[];
}

export interface SGraph extends SElement {
  type: 'graph';
  children: SElement[];
}

interface Offset {
  x: number;
  y: number;
}

type CoordMode = 'INHERIT' | 'CONTAINER' | 'PARENT' | 'ROOT';

function optionValue(node: ElkNode, key: string): string | undefined {
  const opts = (node.layoutOptions ?? {}) as Record<string, unknown>;
  const props = ((node as unknown as { properties?: Record<string, unknown> }).properties ?? {});
  for (const k of [`org.eclipse.elk.json.${key}`, `elk.json.${key}`, `json.${key}`, key]) {
    const v = opts[k] ?? props[k];
    if (v !== undefined && v !== null) return String(v).toUpperCase();
  }
  return undefined;
}

/**
 * Converts a laid-out ELK graph into a sprotty model. Element ids are the ELK ids (unique in the
 * output of `elk convert` and of elk-lean's JSON exporter); labels get `<owner>_label<i>`, junction
 * points `<edge>_j<i>`, sections after the first `<edge>_s<i>`. Duplicates get a numeric suffix.
 */
export function elkToSprotty(graph: ElkNode): SGraph {
  const used = new Set<string>();
  const unique = (id: string): string => {
    let out = id;
    for (let i = 1; used.has(out); i++) out = `${id}~${i}`;
    used.add(out);
    return out;
  };
  const rootId = unique(graph.id || 'root');
  const root: SGraph = { type: 'graph', id: rootId, children: [] };

  // JSON coordinate modes (ELK JsonImporter): shapes relative to the parent (default) or the root;
  // edges relative to their container (default), their parent (the node listing them) or the root.
  const shapeMode = (optionValue(graph, 'shapeCoords') ?? 'INHERIT') as CoordMode;
  const edgeMode = (optionValue(graph, 'edgeCoords') ?? 'INHERIT') as CoordMode;
  const shapesAbsolute = shapeMode === 'ROOT';

  // absolute offset of each node's coordinate system, and its sprotty element
  const nodeOrigin = new Map<string, Offset>();
  const nodeElement = new Map<string, SElement>();
  nodeOrigin.set(graph.id, { x: 0, y: 0 });
  nodeElement.set(graph.id, root);
  const pendingEdges: { edge: ElkExtendedEdge; listedIn: ElkNode }[] = [];

  const labelsOf = (owner: string, labels: ElkLabel[] | undefined, origin: Offset, parent: SElement) => {
    (labels ?? []).forEach((l, i) => {
      if (l.text === undefined) return;
      const lab: SElement = {
        type: 'label',
        id: unique(l.id || `${owner}_label${i}`),
        text: l.text,
        position: { x: (l.x ?? 0) - origin.x, y: (l.y ?? 0) - origin.y },
        size: { width: l.width ?? 0, height: l.height ?? 0 },
      };
      (parent.children ??= []).push(lab);
    });
  };

  // shapes: positions relative to the sprotty parent (= ELK parent node)
  const visitNode = (node: ElkNode, parentEl: SElement, parentAbs: Offset) => {
    for (const child of node.children ?? []) {
      const x = child.x ?? 0;
      const y = child.y ?? 0;
      const abs = shapesAbsolute ? { x, y } : { x: parentAbs.x + x, y: parentAbs.y + y };
      const el: SElement = {
        type: 'node',
        id: unique(child.id),
        position: { x: abs.x - parentAbs.x, y: abs.y - parentAbs.y },
        size: { width: child.width ?? 0, height: child.height ?? 0 },
        children: [],
      };
      if ((child.children ?? []).length > 0) el.cssClasses = ['hierarchical'];
      parentEl.children!.push(el);
      nodeOrigin.set(child.id, abs);
      nodeElement.set(child.id, el);
      // like elk-live: ports, labels, child nodes, then the contained edges
      for (const port of (child.ports ?? []) as ElkPort[]) {
        const px = port.x ?? 0;
        const py = port.y ?? 0;
        const pAbs = shapesAbsolute ? { x: px, y: py } : { x: abs.x + px, y: abs.y + py };
        const pEl: SElement = {
          type: 'port',
          id: unique(port.id),
          position: { x: pAbs.x - abs.x, y: pAbs.y - abs.y },
          size: { width: port.width ?? 0, height: port.height ?? 0 },
          children: [],
        };
        el.children!.push(pEl);
        // with absolute shape coordinates the labels are absolute too
        labelsOf(port.id, port.labels, shapesAbsolute ? pAbs : { x: 0, y: 0 }, pEl);
      }
      labelsOf(child.id, child.labels, shapesAbsolute ? abs : { x: 0, y: 0 }, el);
      visitNode(child, el, abs);
    }
    for (const e of (node.edges ?? []) as ElkExtendedEdge[]) pendingEdges.push({ edge: e, listedIn: node });
  };
  labelsOf(graph.id, graph.labels, { x: 0, y: 0 }, root);
  visitNode(graph, root, { x: 0, y: 0 });

  // edges: under the node their coordinates refer to
  for (const { edge, listedIn } of pendingEdges) {
    const containerId = (edge as unknown as { container?: string }).container;
    let refId: string;
    switch (edgeMode) {
      case 'ROOT': refId = graph.id; break;
      case 'PARENT': refId = listedIn.id; break;
      default: refId = containerId && nodeOrigin.has(containerId) ? containerId : listedIn.id;
    }
    // elk-live places the edge in the sprotty element of the node its coordinates refer to
    const parentEl = nodeElement.get(refId) ?? root;
    const sources = edge.sources ?? [];
    const targets = edge.targets ?? [];
    const sections: ElkEdgeSection[] = edge.sections ?? [];
    const pts = (s: ElkEdgeSection): ElkPoint[] => [s.startPoint, ...(s.bendPoints ?? []), s.endPoint];
    const makeEdge = (id: string, sourceId: string, targetId: string, route: ElkPoint[], arrow: boolean): SElement => ({
      type: 'edge',
      id: unique(id),
      sourceId,
      targetId,
      routingPoints: route.map((p) => ({ x: p.x, y: p.y })),
      arrow,
      children: [],
    });
    const edgeEls: SElement[] = [];
    if (sections.length === 0) {
      edgeEls.push(makeEdge(edge.id, sources[0] ?? '', targets[0] ?? '', [], false));
    } else {
      sections.forEach((s, i) => {
        const outgoing = (s as unknown as { outgoingSections?: string[] }).outgoingSections ?? [];
        edgeEls.push(makeEdge(i === 0 ? edge.id : `${edge.id}_s${i}`,
          s.incomingShape ?? sources[0] ?? '', s.outgoingShape ?? targets[0] ?? '', pts(s), outgoing.length === 0));
      });
    }
    const first = edgeEls[0];
    (edge.junctionPoints ?? []).forEach((jp, i) => {
      first.children!.push({ type: 'junction', id: unique(`${edge.id}_j${i}`), position: { x: jp.x, y: jp.y } });
    });
    labelsOf(edge.id, edge.labels, { x: 0, y: 0 }, first);
    parentEl.children!.push(...edgeEls);
  }
  return root;
}

/** All element ids of a sprotty model (for tests). */
export function collectIds(el: SElement, out: string[] = []): string[] {
  out.push(el.id);
  for (const c of el.children ?? []) collectIds(c, out);
  return out;
}
