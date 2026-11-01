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
* `portRatioOrPosition` is the port's `PORT_RATIO_OR_POSITION`, read once by `PortContextCreator`
  (Java reads it from the port when placing FIXED_RATIO ports; elk-rs never sets it: `0.0`).
* Java's `parentNodeContext` back reference is not kept (the node context owns the port
  contexts).
-/
/-! Float literals as global constants (FL): inside branches, loops and specialised code the compiler
shares a literal's `Nat`/`Bool` arguments with unrelated variables (CSE) and then parses it on every
evaluation (`FastFloat.ofScientificImpl`); a top-level constant is a load (PLAN §7.1 items 17, 22). -/
private def fl0p0 : Float := 0.0

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
  /-- Port ratio or position for fixed-ratio placement (`GraphAdapters.portRatioOrPosition`). -/
  portRatioOrPosition : Float := fl0p0
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

/-! ### Field updaters (not inlined)

Used as the update of `Array.modify`/`Array.map` on port context arrays: with the record update
lambda inlined into `modify`/`map`, the compiler tests the context's exclusivity before the slot is
cleared and every update allocated a fresh context (PLAN 7.1 item 16; `modifyIn` would need
`Inhabited P`). Called out of line, the update reuses the unshared context. -/

/-- `portMargin := m`. -/
@[noinline] def withPortMargin (pc : PortContext P L) (m : ElkMargin) : PortContext P L :=
  { pc with portMargin := m }

/-- `portMargin.left := v`. -/
@[noinline] def withMarginLeft (pc : PortContext P L) (v : Float) : PortContext P L :=
  { pc with portMargin := { pc.portMargin with left := v } }

/-- `portMargin.right := v`. -/
@[noinline] def withMarginRight (pc : PortContext P L) (v : Float) : PortContext P L :=
  { pc with portMargin := { pc.portMargin with right := v } }

/-- `portMargin.top := v`. -/
@[noinline] def withMarginTop (pc : PortContext P L) (v : Float) : PortContext P L :=
  { pc with portMargin := { pc.portMargin with top := v } }

/-- `portMargin.bottom := v`. -/
@[noinline] def withMarginBottom (pc : PortContext P L) (v : Float) : PortContext P L :=
  { pc with portMargin := { pc.portMargin with bottom := v } }

/-- `portMargin.left := l`, `portMargin.right := r`. -/
@[noinline] def withMarginLeftRight (pc : PortContext P L) (l r : Float) : PortContext P L :=
  { pc with portMargin := { pc.portMargin with left := l, right := r } }

/-- `portMargin.top := t`, `portMargin.bottom := b`. -/
@[noinline] def withMarginTopBottom (pc : PortContext P L) (t b : Float) : PortContext P L :=
  { pc with portMargin := { pc.portMargin with top := t, bottom := b } }

/-- `portPosition := pos`. -/
@[noinline] def withPortPosition (pc : PortContext P L) (pos : KVector) : PortContext P L :=
  { pc with portPosition := pos }

/-- `portPosition.y += dy`. -/
@[noinline] def offsetPositionY (pc : PortContext P L) (dy : Float) : PortContext P L :=
  { pc with portPosition := { pc.portPosition with y := pc.portPosition.y + dy } }

/-- `PortContext.applyPortPosition()`: writes `portPosition` to the port. -/
def applyPortPosition {m : Type → Type} [Monad m] {G N E : Type} (a : GraphAdapters m G N P L E)
    (pc : PortContext P L) : m Unit :=
  a.port.setPosition pc.port pc.portPosition

end PortContext

end Elk.Alg.Common.NodeSpacing.Internal
