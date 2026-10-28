import Elk.Core.Exceptions
import Elk.Alg.Common.NodeSpacing.Internal.NodeContext
/-!
# `org.eclipse.elk.alg.common.nodespacing.internal.algorithm.PortContextCreator`

Creates the port contexts of a node and assigns volatile ids to its ports (elk-rs
`internal::algorithm::PortContextCreator`). Unless port labels are fixed (or inside port labels
are ignored), the labels of each port are added to a new label cell created in the node context's
cell arena and referenced by `PortContext.portLabelCell`.

Order (elk-rs `create_port_contexts`): the volatile id of a port is its index in
`NodeAdapter.getPorts()`; contexts are appended to their side in that order and afterwards the
SOUTH and WEST lists are reversed. This reproduces Java's
`TreeMultimap.create(comparePortSides, comparePortContexts)` (ascending volatile ids on
NORTH/EAST, descending on SOUTH/WEST). `PortContext.portRatioOrPosition` is the port's
`PORT_RATIO_OR_POSITION` (`GraphAdapters.portRatioOrPosition`, Java reads the property; elk-rs
never sets it and places FIXED_RATIO ports at `0.0`).

Deviation from Java (following elk-rs): Java's `PortContext` keeps the port adapter and reads it
lazily; elk-rs (and this port) extracts the port size, side, position, border offset, compound
connections and the sizes/positions of the port labels once, when the context is created.
-/
namespace Elk.Alg.Common.NodeSpacing.Internal.Algorithm

open Elk Elk.Core Elk.Core.Math Elk.Core.Util Elk.Core.Options Elk.Core.Util.Adapters
open Elk.Alg.Common.NodeSpacing.CellSystem Elk.Alg.Common.NodeSpacing.Internal

namespace PortContextCreator

variable {m : Type → Type} [Monad m] {G N P L E : Type}

/-- Whether a port's labels have to be placed next to the port (Java `PortContext` constructor,
elk-rs `PortContextCreator::create_port_context`): always for inside labels of non-compound nodes;
for inside labels of compound nodes only with `NEXT_TO_PORT_IF_POSSIBLE` and no compound
connections; for outside labels only with `NEXT_TO_PORT_IF_POSSIBLE` and no incident edges. The
incident edges are only read in the last case. -/
def computeLabelsNextToPort (a : GraphAdapters m G N P L E) (ctx : NodeContext N P L) (port : P)
    (hasCompoundConnections : Bool) : m Bool := do
  let portLabelsNextToPort := ctx.portLabelsPlacement.contains .nextToPortIfPossible
  if ctx.portLabelsPlacement.contains .inside then
    if ctx.treatAsCompoundNode then
      return portLabelsNextToPort && !hasCompoundConnections
    else
      return true
  else if ctx.portLabelsPlacement.contains .outside then
    if portLabelsNextToPort then
      let incoming ← a.portIncomingEdges port
      let outgoing ← a.portOutgoingEdges port
      let hasIncidentEdges := !incoming.isEmpty || !outgoing.isEmpty
      return !hasIncidentEdges
    else
      return false
  else
    return false

/-- `createPortContext` for a port whose side and volatile id the caller has read already. The
port's options (`ElementOps.getProps`), labels and label sizes are read once (Java/elk-rs read
them again for the label cell; adapter reads have no side effects). A port without labels gets no
label cell: an empty label cell (zero padding) has minimum size `0` and no labels, which every
consumer treats like a missing cell (port margins, inside port label widths, label placement); no
Java counterpart. -/
def createPortContextOnSide (a : GraphAdapters m G N P L E) (ctx : NodeContext N P L) (port : P)
    (portSide : PortSide) (volatileId : Int) (imPortLabels : Bool) : m (NodeContext N P L) := do
  let portSize ← a.port.getSize port
  let portPosition ← a.port.getPosition port
  let props ← a.port.getProps port
  let portBorderOffset := a.port.getPropertyDFrom props CoreOptions.PORT_BORDER_OFFSET 0.0
  let hasPortBorderOffset := props.hasKey CoreOptions.PORT_BORDER_OFFSET.key
  let hasCompoundConnections ← a.hasCompoundConnections port
  -- Collect label sizes and positions
  let labels ← a.portLabels port
  let labelSizes ← labels.mapM a.label.getSize
  let labelPositions ← labels.mapM a.label.getPosition
  let labelsNextToPort ← computeLabelsNextToPort a ctx port hasCompoundConnections
  let pc : PortContext P L := PortContext.new port portSize portSide volatileId portPosition
    portBorderOffset hasPortBorderOffset hasCompoundConnections
  -- Java reads `PORT_RATIO_OR_POSITION` from the port whenever it places a FIXED_RATIO port; the
  -- value does not change during the calculation (elk-rs never sets it: always `0.0`)
  let portRatioOrPosition ← a.portRatioOrPosition port
  let pc := { pc with labelsNextToPort, labels, labelSizes, labelPositions, portRatioOrPosition }
  -- If the port has labels and if port labels are to be placed, we need to remember them
  if imPortLabels && !labels.isEmpty && !PortLabelPlacement.isFixed ctx.portLabelsPlacement then
    let gap := ctx.labelLabelSpacing
    -- the arena is taken out of the context so that it is updated in place
    let (ctx, labelCell) := ctx.modifyCellsGet fun cells => Id.run do
      let (cells, labelCell) := cells.createLabel gap
      let mut cells := cells
      for i in [0:labels.size] do
        if h : i < labels.size then
          cells := cells.addLabel labelCell labels[i] (labelSizes.getD i {})
      return (cells, labelCell)
    return ctx.addPortContext { pc with portLabelCell := some labelCell }
  return ctx.addPortContext pc

/-- `PortContextCreator.createPortContext(nodeContext, port, imPortLabels)` (elk-rs
`create_port_context`): extracts the port's data into a new `PortContext`, creates the port label
cell (gap `labelLabelSpacing`, one label per port label, in label order) if `imPortLabels` holds
and port labels are not fixed, and appends the context to its side. The port's volatile id must
already be set. -/
def createPortContext (a : GraphAdapters m G N P L E) (ctx : NodeContext N P L) (port : P)
    (imPortLabels : Bool) : m (NodeContext N P L) := do
  createPortContextOnSide a ctx port (← a.portSide port) (← a.port.getVolatileId port) imPortLabels

/-- `PortContextCreator.createPortContexts(nodeContext, ignoreInsidePortLabels)` (elk-rs
`create_port_contexts`): assigns volatile ids `0, 1, …` to the node's ports in port order, creates
a context for each of them and finally reverses the SOUTH and WEST context lists (see the module
doc). Port labels get a label cell unless `ignoreInsidePortLabels` is set and port labels are
placed inside. Throws `IllegalArgumentException` for a port without a side (elk-rs panics with the
same message). -/
def createPortContexts [MonadExcept IO.Error m] (a : GraphAdapters m G N P L E) (ctx : NodeContext N P L)
    (ignoreInsidePortLabels : Bool) : m (NodeContext N P L) := do
  let imPortLabels := !ignoreInsidePortLabels || !ctx.portLabelsPlacement.contains .inside
  let mut ctx := ctx
  let mut volatileId : Int := 0
  for port in (← a.nodePorts ctx.node) do
    let portSide ← a.portSide port
    if portSide == .undefined then
      throwIllegalArgument
        "Label and node size calculator can only be used with ports that have port sides assigned."
    a.port.setVolatileId port volatileId
    -- the volatile id just set (`getVolatileId` returns it)
    ctx ← createPortContextOnSide a ctx port portSide volatileId imPortLabels
    volatileId := volatileId + 1
  -- Java's TreeMultimap order: NORTH/EAST ascending, SOUTH/WEST descending by volatile id
  ctx := ctx.modifyPortContextsOf .south (·.reverse)
  ctx := ctx.modifyPortContextsOf .west (·.reverse)
  return ctx

end PortContextCreator

end Elk.Alg.Common.NodeSpacing.Internal.Algorithm
