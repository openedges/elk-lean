/*******************************************************************************
 * Copyright (c) 2017 TypeFox GmbH (http://www.typefox.io) and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * http://www.eclipse.org/legal/epl-2.0.
 *
 * SPDX-License-Identifier: EPL-2.0
 *******************************************************************************/
/*
 * Ported from elk-live client/src/views.tsx to sprotty 1.x without JSX (sprotty's `svg` factory)
 * and without decorators (inversify `decorate`). The visual model is elk-live's: nodes and ports
 * are rectangles at their laid-out bounds, labels are `<text>` with a hanging baseline at the label
 * position, edges are polylines with an 8 x 6 arrow head, junction points are circles of radius 2.
 * Changed for elk-lean: edges draw exactly their routing points (ELK section start, bend and end
 * points) instead of sprotty's anchor-computed route, an edge section that continues in another
 * section has no arrow head, and the graph view skips sprotty's edge router.
 */
import { decorate, injectable } from 'inversify';
import type { VNode } from 'snabbdom';
import {
  svg, type IView, type RenderingContext, type SGraphImpl, type SLabelImpl,
} from 'sprotty';
import { angleOfPoint, toDegrees } from 'sprotty-protocol';
import type { ElkEdge, ElkJunction, ElkNode, ElkPort } from './sprotty-model.ts';

export class ElkGraphView implements IView {
  render(model: Readonly<SGraphImpl>, context: RenderingContext): VNode {
    const transform = `scale(${model.zoom}) translate(${-model.scroll.x},${-model.scroll.y})`;
    return svg('svg', { 'class-sprotty-graph': true },
      svg('g', { transform }, ...context.renderChildren(model)));
  }
}

export class ElkNodeView implements IView {
  render(node: Readonly<ElkNode>, context: RenderingContext): VNode {
    return svg('g', null,
      svg('rect', {
        'class-elknode': true, 'class-mouseover': node.hoverFeedback, 'class-selected': node.selected,
        x: 0, y: 0, width: Math.max(node.bounds.width, 0), height: Math.max(node.bounds.height, 0),
      }),
      ...context.renderChildren(node));
  }
}

export class ElkPortView implements IView {
  render(port: Readonly<ElkPort>, context: RenderingContext): VNode {
    return svg('g', null,
      svg('rect', {
        'class-elkport': true, 'class-mouseover': port.hoverFeedback, 'class-selected': port.selected,
        x: 0, y: 0, width: Math.max(port.bounds.width, 0), height: Math.max(port.bounds.height, 0),
      }),
      ...context.renderChildren(port));
  }
}

export class ElkEdgeView implements IView {
  render(edge: Readonly<ElkEdge>, context: RenderingContext): VNode {
    const pts = edge.routingPoints;
    const children: VNode[] = [];
    if (pts.length >= 2) {
      let d = `M ${pts[0].x},${pts[0].y}`;
      for (let i = 1; i < pts.length; i++) d += ` L ${pts[i].x},${pts[i].y}`;
      children.push(svg('path', { 'class-elkedge': true, d }));
      if (edge.arrow !== false) {
        const p1 = pts[pts.length - 2];
        const p2 = pts[pts.length - 1];
        const angle = toDegrees(angleOfPoint({ x: p1.x - p2.x, y: p1.y - p2.y }));
        children.push(svg('path', {
          'class-elkedge': true, 'class-arrow': true, d: 'M 0,0 L 8,-3 L 8,3 Z',
          transform: `rotate(${angle} ${p2.x} ${p2.y}) translate(${p2.x} ${p2.y})`,
        }));
      }
    }
    // hover / selection classes on the group as sprotty's PolylineEdgeView (elk-live) puts them: the
    // path's own `.elkedge` stroke wins, so edges show no feedback there either
    return svg('g', { 'class-sprotty-edge': true, 'class-mouseover': edge.hoverFeedback, 'class-selected': edge.selected },
      ...children, ...context.renderChildren(edge));
  }
}

export class ElkLabelView implements IView {
  render(label: Readonly<SLabelImpl>): VNode {
    return svg('text', { 'class-elklabel': true }, label.text);
  }
}

export class JunctionView implements IView {
  render(_node: Readonly<ElkJunction>): VNode {
    return svg('g', null, svg('circle', { 'class-elkjunction': true, r: 2 }));
  }
}

for (const view of [ElkGraphView, ElkNodeView, ElkPortView, ElkEdgeView, ElkLabelView, JunctionView]) {
  decorate(injectable(), view);
}
