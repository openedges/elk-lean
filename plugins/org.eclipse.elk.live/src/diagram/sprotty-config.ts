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
 * Ported from elk-live client/src/sprotty-config.ts to sprotty 1.x. Changed for elk-lean: the model
 * source is a `LocalModelSource` (the layout runs in the browser, not in a diagram server), the
 * edit modules are not loaded (the diagram is read-only), and the base div is a parameter.
 */
import 'reflect-metadata';
import { Container, ContainerModule } from 'inversify';
import {
  ConsoleLogger, LocalModelSource, LogLevel, SGraphImpl, SLabelImpl, TYPES, boundsModule, configureModelElement,
  configureViewerOptions, defaultModule, exportModule, fadeModule, hoverModule, modelSourceModule, moveModule,
  routingModule, selectModule, undoRedoModule, updateModule, viewportModule,
} from 'sprotty';
import { ElkEdge, ElkJunction, ElkNode, ElkPort } from './sprotty-model.ts';
import { ElkEdgeView, ElkGraphView, ElkLabelView, ElkNodeView, ElkPortView, JunctionView } from './views.ts';

export function createContainer(baseDiv: string): Container {
  const elkGraphModule = new ContainerModule((bind, unbind, isBound, rebind) => {
    rebind(TYPES.ILogger).to(ConsoleLogger).inSingletonScope();
    rebind(TYPES.LogLevel).toConstantValue(LogLevel.warn);
    bind(TYPES.ModelSource).to(LocalModelSource).inSingletonScope();
    const context = { bind, unbind, isBound, rebind };
    configureModelElement(context, 'graph', SGraphImpl, ElkGraphView);
    configureModelElement(context, 'node', ElkNode, ElkNodeView);
    configureModelElement(context, 'port', ElkPort, ElkPortView);
    configureModelElement(context, 'edge', ElkEdge, ElkEdgeView);
    configureModelElement(context, 'label', SLabelImpl, ElkLabelView);
    configureModelElement(context, 'junction', ElkJunction, JunctionView);
    configureViewerOptions(context, {
      baseDiv,
      needsClientLayout: false,
      needsServerLayout: false,
    });
  });
  const container = new Container();
  container.load(defaultModule, selectModule, boundsModule, moveModule, fadeModule, hoverModule, updateModule,
    undoRedoModule, viewportModule, routingModule, exportModule, modelSourceModule, elkGraphModule);
  return container;
}
