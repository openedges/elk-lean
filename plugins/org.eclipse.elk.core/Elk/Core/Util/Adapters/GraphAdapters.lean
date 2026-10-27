import Elk.Graph
import Elk.Core.Math
import Elk.Core.Options
import Elk.Core.Util.IndividualSpacings
/-!
# `org.eclipse.elk.core.util.adapters.GraphAdapters`

The Java adapter interfaces (`GraphElementAdapter`, `GraphAdapter`, `NodeAdapter`,
`PortAdapter`, `LabelAdapter`, `EdgeAdapter`) become one record of closures over
typed element ids, parameterised by the monad the underlying graph lives in.
`ElkGraphAdapters` instantiates it for `ElkGraph`/`ElkM`; the layered algorithm
instantiates it for its `LGraph`. Consumers (`alg.common.nodespacing`) are written
against the record and the generic helpers below.
-/
namespace Elk.Core.Util.Adapters

open Elk.Graph Elk.Core.Math Elk.Core.Options

/-- `GraphAdapters.GraphElementAdapter<T>`: size/position/property/volatile-id access to
one element kind `E`. Property access works on raw `PropValue`s so the record stays in
`Type`; use `ElementOps.getProperty` for typed access. -/
structure ElementOps (m : Type → Type) (E : Type) where
  /-- `getSize()`. -/
  getSize : E → m KVector
  /-- `setSize(size)`. -/
  setSize : E → KVector → m Unit
  /-- `getPosition()`. -/
  getPosition : E → m KVector
  /-- `setPosition(pos)`. -/
  setPosition : E → KVector → m Unit
  /-- Raw stored property value (no default). -/
  getRaw : E → PropKey → m (Option PropValue)
  /-- `hasProperty(prop)`. -/
  hasProperty : E → PropKey → m Bool
  /-- `getVolatileId()`. -/
  getVolatileId : E → m Int
  /-- `setVolatileId(id)`. -/
  setVolatileId : E → Int → m Unit
  /-- Default used when the property is absent and this adapter overrides the property's own
  default (the `PORT_BORDER_OFFSET` proxy of `ElkGraphAdapters`). -/
  defaultOverride : PropKey → Option PropValue := fun _ => none

namespace ElementOps

variable {m : Type → Type} {E : Type} [Monad m]

/-- `GraphElementAdapter.getProperty(prop)`: the stored value decoded to `α`, else the
adapter's default override, else the property's default (`none` = Java `null`). -/
def getProperty {α : Type} [PropCodec α] (ops : ElementOps m E) (e : E) (p : Property α) : m (Option α) := do
  match ← ops.getRaw e p.key with
  | some raw =>
    match PropCodec.dec raw with
    | some v => return some v
    | none => return p.default
  | none =>
    match ops.defaultOverride p.key with
    | some raw => return (PropCodec.dec raw : Option α) <|> p.default
    | none => return p.default

/-- `getProperty` with an explicit fallback. -/
def getPropertyD {α : Type} [PropCodec α] (ops : ElementOps m E) (e : E) (p : Property α) (d : α) : m α := do
  return (← ops.getProperty e p).getD d

/-- `hasProperty(prop)` for a typed property. -/
def hasProp {α : Type} (ops : ElementOps m E) (e : E) (p : Property α) : m Bool :=
  ops.hasProperty e p.key

end ElementOps

/-- The whole adapter family of `GraphAdapters` for one graph model: `G` is the graph
(parent node) type, `N` nodes, `P` ports, `L` labels, `E` edges. -/
structure GraphAdapters (m : Type → Type) (G N P L E : Type) where
  /-- `GraphAdapter<T>` element access to the graph itself. -/
  graph : ElementOps m G
  /-- `GraphAdapter.getNodes()`. -/
  getNodes : G → m (Array N)
  /-- `NodeAdapter<T>` element access. -/
  node : ElementOps m N
  /-- `NodeAdapter.getGraph()`. -/
  getGraph : N → m (Option G)
  /-- `NodeAdapter.getLabels()`. -/
  nodeLabels : N → m (Array L)
  /-- `NodeAdapter.getPorts()`. -/
  nodePorts : N → m (Array P)
  /-- `NodeAdapter.getIncomingEdges()`. -/
  nodeIncomingEdges : N → m (Array E)
  /-- `NodeAdapter.getOutgoingEdges()`. -/
  nodeOutgoingEdges : N → m (Array E)
  /-- `NodeAdapter.sortPortList()` with the default port comparator. -/
  sortPortList : N → m Unit
  /-- `NodeAdapter.isCompoundNode()`. -/
  isCompoundNode : N → m Bool
  /-- `NodeAdapter.getPadding()`. -/
  getPadding : N → m ElkPadding
  /-- `NodeAdapter.setPadding(padding)`. -/
  setPadding : N → ElkPadding → m Unit
  /-- `NodeAdapter.getMargin()`. -/
  getNodeMargin : N → m ElkMargin
  /-- `NodeAdapter.setMargin(margin)`. -/
  setNodeMargin : N → ElkMargin → m Unit
  /-- `PortAdapter<T>` element access. -/
  port : ElementOps m P
  /-- `PortAdapter.getSide()`. -/
  portSide : P → m PortSide
  /-- `PortAdapter.getLabels()`. -/
  portLabels : P → m (Array L)
  /-- `PortAdapter.getMargin()`. -/
  getPortMargin : P → m ElkMargin
  /-- `PortAdapter.setMargin(margin)`. -/
  setPortMargin : P → ElkMargin → m Unit
  /-- `PortAdapter.getIncomingEdges()`. -/
  portIncomingEdges : P → m (Array E)
  /-- `PortAdapter.getOutgoingEdges()`. -/
  portOutgoingEdges : P → m (Array E)
  /-- `PortAdapter.hasCompoundConnections()`. -/
  hasCompoundConnections : P → m Bool
  /-- `LabelAdapter<T>` element access. -/
  label : ElementOps m L
  /-- `LabelAdapter.getSide()`. -/
  labelSide : L → m LabelSide
  /-- `LabelAdapter.getText()`. -/
  labelText : L → m String
  /-- `EdgeAdapter.getLabels()`. -/
  edgeLabels : E → m (Array L)

/-- The two lookup sources of `IndividualSpacings.getIndividualOrInherited(NodeAdapter, property)`
for one node: its `SPACING_INDIVIDUAL` value (if the property is set and decodes) and its graph
(`NodeAdapter.getGraph()`). Read once with `GraphAdapters.spacingSource` and used for several
lookups with `GraphAdapters.getIndividualOrInheritedFrom`, it saves the repeated adapter reads of
`getIndividualOrInherited` (no Java counterpart; the node's properties and graph must not change
in between). -/
structure SpacingSource (G : Type) where
  /-- The node's individual spacings (`none` if `SPACING_INDIVIDUAL` is not set). -/
  individual : Option IndividualSpacings
  /-- The node's graph. -/
  graph : Option G

namespace GraphAdapters

variable {m : Type → Type} {G N P L E : Type} [Monad m]

/-- Reads the `SpacingSource` of a node: `SPACING_INDIVIDUAL` if the node has the property, and
the node's graph. -/
def spacingSource (a : GraphAdapters m G N P L E) (n : N) : m (SpacingSource G) := do
  let individual ←
    if ← a.node.hasProp n CoreOptions.SPACING_INDIVIDUAL then a.node.getProperty n CoreOptions.SPACING_INDIVIDUAL
    else pure none
  return { individual, graph := ← a.getGraph n }

/-- `getIndividualOrInherited` on a `SpacingSource` read before: the individual spacing if set,
else the graph's value, else the property default. -/
def getIndividualOrInheritedFrom {α : Type} [PropCodec α] (a : GraphAdapters m G N P L E) (src : SpacingSource G)
    (p : Property α) : m (Option α) := do
  let mut result : Option α := none
  if let some individual := src.individual then
    if individual.props.has p then
      result := individual.props.get p
  if result.isNone then
    if let some g := src.graph then
      result ← a.graph.getProperty g p
  if result.isNone then
    result := p.default
  return result

/-- `IndividualSpacings.getIndividualOrInherited(NodeAdapter, property)`: the node's
individual spacing if set, else the parent graph's value, else the property default. -/
def getIndividualOrInherited {α : Type} [PropCodec α] (a : GraphAdapters m G N P L E) (n : N) (p : Property α) : m (Option α) := do
  a.getIndividualOrInheritedFrom (← a.spacingSource n) p

end GraphAdapters

end Elk.Core.Util.Adapters
