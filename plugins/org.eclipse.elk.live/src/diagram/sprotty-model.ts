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
 * Ported from elk-live client/src/sprotty-model.ts to sprotty 1.x (`…Impl` model classes).
 * Changed for elk-lean: `ElkEdge.arrow` (only sections that end at a target shape get an arrow head).
 */
import {
  RectangularNode, RectangularPort, SEdgeImpl, SLabelImpl, SNodeImpl, edgeLayoutFeature, editFeature,
  hoverFeedbackFeature, moveFeature, selectFeature,
} from 'sprotty';

export class ElkNode extends RectangularNode {
  override hasFeature(feature: symbol): boolean {
    return feature === moveFeature ? false : super.hasFeature(feature);
  }
}

export class ElkPort extends RectangularPort {
  override hasFeature(feature: symbol): boolean {
    return feature === moveFeature ? false : super.hasFeature(feature);
  }
}

export class ElkEdge extends SEdgeImpl {
  arrow = true;

  override hasFeature(feature: symbol): boolean {
    return feature === editFeature ? false : super.hasFeature(feature);
  }
}

/**
 * Labels keep the position ELK computed, also under an edge: without `edgeLayoutFeature`, sprotty's
 * `LocationPostprocessor` translates them by their position like node and port labels, instead of
 * `EdgeLayoutPostprocessor` placing them along a router-computed route (the edges here are drawn from
 * their ELK routing points and have no sprotty route, which left edge labels at the edge's origin).
 */
export class ElkLabel extends SLabelImpl {
  override hasFeature(feature: symbol): boolean {
    return feature === edgeLayoutFeature ? false : super.hasFeature(feature);
  }
}

export class ElkJunction extends SNodeImpl {
  override hasFeature(feature: symbol): boolean {
    if (feature === moveFeature || feature === selectFeature || feature === hoverFeedbackFeature) return false;
    return super.hasFeature(feature);
  }
}
