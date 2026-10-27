import Elk.Core.Util.Adapters.GraphAdapters
import Elk.Alg.Common.NodeSpacing.CellSystem.Cell
/-!
# `org.eclipse.elk.alg.common.nodespacing.internal.PortContext`

Data holder for port-related information during node size calculation (elk-rs
`internal::PortContext`). Like elk-rs, the port's data is extracted once (size, side, volatile
id, border offset, label sizes and positions); unlike elk-rs, the context also keeps the port
handle `port : P` and the label handles, so results can be applied through the adapters
(Java `applyPortPosition()`).

* `portLabelCell` refers to a label cell in the owning `NodeContext.cells` arena (Java
  `LabelCell portLabelCell`).
* `portRatioOrPosition` is kept for the fixed-ratio placement like elk-rs, which never sets it
  (it stays `0.0`).
* Java's `parentNodeContext` back reference is not kept (the node context owns the port
  contexts).
-/
namespace Elk.Alg.Common.NodeSpacing.Internal

open Elk Elk.Core.Math Elk.Core.Util Elk.Core.Options Elk.Core.Util.Adapters
open Elk.Alg.Common.NodeSpacing.CellSystem

/-- `PortContext`: port data extracted from the adapter plus the values the algorithm computes. -/
structure PortContext (P L : Type) where
  /-- `port`: the port we calculate stuff for. -/
  port : P
  /-- Port size (extracted from the adapter). -/
  portSize : KVector
  /-- Port side. -/
  portSide : PortSide
  /-- The port's volatile id (Java `port.getVolatileId()`, used for sorting). -/
  volatileId : Int
  /-- `portPosition`: initial position, modified by the algorithm and applied later. -/
  portPosition : KVector
  /-- `labelsNextToPort`: whether the port's labels need to be placed next to the port. -/
  labelsNextToPort : Bool := false
  /-- `PORT_BORDER_OFFSET` (`0.0` when unset). -/
  portBorderOffset : Float
  /-- Whether `PORT_BORDER_OFFSET` is explicitly set on the port. -/
  hasPortBorderOffset : Bool
  /-- `port.hasCompoundConnections()`. -/
  hasCompoundConnections : Bool
  /-- `portMargin`: margin assumed around the port when placing it (includes the label cell if
  node labels are taken into account). -/
  portMargin : ElkMargin := {}
  /-- `portLabelCell`: the label cell for the port's labels, in `NodeContext.cells`. -/
  portLabelCell : Option CellId := none
  /-- The port's label handles (`port.getLabels()`), parallel to `labelSizes`/`labelPositions`. -/
  labels : Array L := #[]
  /-- Sizes of the port labels (extracted from the adapter). -/
  labelSizes : Array KVector := #[]
  /-- Positions of the port labels (extracted from the adapter, for fixed label bounds). -/
  labelPositions : Array KVector := #[]
  /-- Port ratio or position for fixed-ratio placement (elk-rs never sets it: `0.0`). -/
  portRatioOrPosition : Float := 0.0
  deriving Inhabited

namespace PortContext

variable {P L : Type}

/-- elk-rs `PortContext::new(...)`: a context with the given extracted data, no labels, zero
margin, no label cell. -/
def new (port : P) (portSize : KVector) (portSide : PortSide) (volatileId : Int) (portPosition : KVector)
    (portBorderOffset : Float) (hasPortBorderOffset hasCompoundConnections : Bool) : PortContext P L :=
  { port, portSize, portSide, volatileId, portPosition, portBorderOffset, hasPortBorderOffset,
    hasCompoundConnections }

/-- elk-rs `PortContext::get_labels_bounds()` (Java `ElkUtil.getLabelsBounds(port)`): bounding
box of the port's labels relative to the port (zero rectangle without labels). -/
def getLabelsBounds (pc : PortContext P L) : ElkRectangle := Id.run do
  let mut bounds : ElkRectangle := {}
  let mut first := true
  for (pos, size) in pc.labelPositions.zip pc.labelSizes do
    if first then
      bounds := { x := pos.x, y := pos.y, width := size.x, height := size.y }
      first := false
    else
      let right := fmax (bounds.x + bounds.width) (pos.x + size.x)
      let bottom := fmax (bounds.y + bounds.height) (pos.y + size.y)
      let x := fmin bounds.x pos.x
      let y := fmin bounds.y pos.y
      bounds := { x := x, y := y, width := right - x, height := bottom - y }
  return bounds

/-- `PortContext.applyPortPosition()`: writes `portPosition` to the port. -/
def applyPortPosition {m : Type → Type} [Monad m] {G N E : Type} (a : GraphAdapters m G N P L E)
    (pc : PortContext P L) : m Unit :=
  a.port.setPosition pc.port pc.portPosition

end PortContext

end Elk.Alg.Common.NodeSpacing.Internal
