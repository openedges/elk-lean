import Elk.Alg.Common.NodeSpacing.NodeDimensionCalculation
/-!
# `org.eclipse.elk.alg.common.NodeMicroLayout`

"Node micro layout" of an `ElkGraph` (elk-rs `node_micro_layout`): sorts the port lists, computes
node sizes, places node and port labels and computes node margins for all children of a graph.
Java and elk-rs put the class into `org.eclipse.elk.alg.common`; the Lean module lives next to
`NodeDimensionCalculation` in `NodeSpacing`.

`execute` follows ELK Java 0.12.0 (the result reference): `sortPortLists` (Java `TimSort` with the
throwing `ElkGraphAdapters.PortComparator`), the full cell system pipeline of
`NodeLabelAndSizeCalculator.process` for every child (`calculateLabelAndNodeSizesJava`, with Java's
node size validation) and `calculateNodeMargins`. elk-rs dispatches the label and size step for an
`ElkGraphAdapter` to its own simplified path (`calculateLabelAndNodeSizesForElk`: `processNode` plus
a port label pass that never moves ports), which Java does not have.
-/
namespace Elk.Alg.Common.NodeSpacing

open Elk.Graph Elk.Core.Util.Adapters

/-- `NodeMicroLayout`: the adapters of an `ElkGraph` and the graph (parent node) whose children are
laid out. The Lean adapter record does not contain the graph, so both are stored. -/
structure NodeMicroLayout where
  /-- The adapter family (`ElkGraphAdapters.adapt`). -/
  adapter : ElkAdapters
  /-- The graph whose children are processed. -/
  graph : NodeId

namespace NodeMicroLayout

/-- `NodeMicroLayout.forGraph(elkGraph)` (elk-rs `for_graph(graph)`): a micro layout for the
children of `graph` with fresh adapters; run it with `execute`. -/
def forGraph (graph : NodeId) : IO NodeMicroLayout := do
  return { adapter := ← ElkGraphAdapters.adapt graph, graph }

/-- `NodeMicroLayout.forGraph(adapter)` (elk-rs `for_adapter(adapter)`): a micro layout with the
given adapters for the children of `graph`. -/
def forAdapter (adapter : ElkAdapters) (graph : NodeId) : NodeMicroLayout :=
  { adapter, graph }

/-- `NodeMicroLayout.execute()`: `sortPortLists`, then `calculateLabelAndNodeSizes` (Java's full
pipeline, `calculateLabelAndNodeSizesJava`), then `calculateNodeMargins`. Throws Java's
node size validation exceptions (`IllegalStateException: Port side is undefined` from the port sort,
`UnsupportedConfigurationException: Invalid port/node label placement: [..]`,
`IllegalArgumentException: Label and node size calculator can only be used with ports that have port
sides assigned.`). -/
def execute (l : NodeMicroLayout) : ElkM Unit := do
  NodeDimensionCalculation.sortPortLists l.adapter l.graph
  NodeDimensionCalculation.calculateLabelAndNodeSizesJava l.adapter l.graph
  NodeDimensionCalculation.calculateNodeMargins l.adapter l.graph

end NodeMicroLayout

end Elk.Alg.Common.NodeSpacing
