import Elk.Core.Util.Java
import Elk.Alg.Common.NodeSpacing.Internal.NodeContext
import Elk.Core.Util.FloatConst
open Elk.Core.Util.FloatConst
/-!
# `org.eclipse.elk.alg.common.nodespacing.internal.algorithm.PortPlacementCalculator`

Actually places ports (elk-rs `internal::algorithm::PortPlacementCalculator`). Northern and
southern ports are placed by `placeHorizontalPorts` (PHASE 5 of the node size calculation),
eastern and western ports by `placeVerticalPorts` (PHASE 6). The port positions are written to
`PortContext.portPosition` (applied later by `NodeLabelAndSizeUtilities.applyStuff`).

The free placement reads the side's inside port label cell (`NodeContext.insidePortLabelCell`):
its cell rectangle (set by the cell layout), its padding and its minimum content area size (set
by `Horizontal/VerticalPortPlacementSizeCalculator`). Ports of a side are visited in
`portContexts` (`TreeMultimap`) order.

Deviations from Java (following elk-rs):
* `FIXED_RATIO` reads `PortContext.portRatioOrPosition`, the port's `PORT_RATIO_OR_POSITION`
  property read once when the context is created (Java reads it here; elk-rs never sets the field,
  so its FIXED_RATIO ports end up at `0.0`).
* `Math.max(0, additional)` is `f64::max` (`fmax`: a NaN operand is ignored).
* A side without an inside port label cell is skipped (Java would throw a
  `NullPointerException`).
-/

namespace Elk.Alg.Common.NodeSpacing.Internal.Algorithm

open Elk Elk.Core.Math Elk.Core.Util Elk.Core.Options
open Elk.Alg.Common.NodeSpacing.CellSystem Elk.Alg.Common.NodeSpacing.Internal

namespace PortPlacementCalculator

variable {N P L : Type}

/-! ### Utilities -/

/-- `modifiedPortPlacementSize(nodeContext, oldPortAlignment, currentPortPlacementSize)`: for
`DISTRIBUTED` alignment, removes the two port-port spacings that surround the ports. -/
private def modifiedPortPlacementSize (ctx : NodeContext N P L) (oldPortAlignment : PortAlignment)
    (currentPortPlacementSize : Float) : Float :=
  if oldPortAlignment == .distributed then
    currentPortPlacementSize - fl2p0 * ctx.portPortSpacing
  else
    currentPortPlacementSize

/-- `calculateHorizontalPortYCoordinate(portContext)`: northern ports end at y = 0 (or at the
negated border offset), southern ports start at y = 0 (or at the border offset). -/
private def calculateHorizontalPortYCoordinate (pc : PortContext P L) : Float :=
  if pc.hasPortBorderOffset then
    if pc.portSide == .north then -pc.portSize.y - pc.portBorderOffset else pc.portBorderOffset
  else if pc.portSide == .north then -pc.portSize.y
  else 0.0

/-- `calculateVerticalPortXCoordinate(portContext, nodeWidth)`: western ports end at x = 0,
eastern ports start at x = node width (both shifted by the border offset, if any). -/
private def calculateVerticalPortXCoordinate (pc : PortContext P L) (nodeWidth : Float) : Float :=
  if pc.hasPortBorderOffset then
    if pc.portSide == .west then -pc.portSize.x - pc.portBorderOffset else nodeWidth + pc.portBorderOffset
  else if pc.portSide == .west then -pc.portSize.x
  else nodeWidth

/-- The free placement parameters shared by `placeHorizontalFreePorts` and
`placeVerticalFreePorts`: the start coordinate and the space between two ports for the given
available space, required size and alignment. -/
private def freePortPlacementStart (ctx : NodeContext N P L) (portCount : Nat) (portAlignment : PortAlignment)
    (availableSpace calculatedPortPlacementSize startPos : Float) : Float × Float := Id.run do
  let mut portAlignment := portAlignment
  let mut calculatedPortPlacementSize := calculatedPortPlacementSize
  let mut currentPos := startPos
  let mut spaceBetweenPorts := ctx.portPortSpacing
  -- If DISTRIBUTED or JUSTIFIED with a single port, switch to CENTER
  if (portAlignment == .distributed || portAlignment == .justified) && portCount == 1 then
    calculatedPortPlacementSize := modifiedPortPlacementSize ctx portAlignment calculatedPortPlacementSize
    portAlignment := .center
  if availableSpace < calculatedPortPlacementSize && !ctx.sizeOptions.contains .portsOverhang then
    -- Not enough space and ports can't overhang: cram them in
    if portAlignment == .distributed then
      spaceBetweenPorts := spaceBetweenPorts +
        (availableSpace - calculatedPortPlacementSize) / (portCount + 1).toFloat
      currentPos := currentPos + spaceBetweenPorts
    else
      spaceBetweenPorts := spaceBetweenPorts +
        (availableSpace - calculatedPortPlacementSize) / (portCount - 1).toFloat
  else
    -- We are allowed to overhang; DISTRIBUTED and JUSTIFIED fall back to CENTER
    if availableSpace < calculatedPortPlacementSize then
      calculatedPortPlacementSize := modifiedPortPlacementSize ctx portAlignment calculatedPortPlacementSize
      portAlignment := .center
    match portAlignment with
    | .begin => pure ()
    | .center =>
      currentPos := currentPos + (availableSpace - calculatedPortPlacementSize) / fl2p0
    | .«end» =>
      currentPos := currentPos + (availableSpace - calculatedPortPlacementSize)
    | .distributed =>
      let additional := (availableSpace - calculatedPortPlacementSize) / (portCount + 1).toFloat
      spaceBetweenPorts := spaceBetweenPorts + fmax fl0p0 additional
      currentPos := currentPos + spaceBetweenPorts
    | .justified =>
      let additional := (availableSpace - calculatedPortPlacementSize) / (portCount - 1).toFloat
      spaceBetweenPorts := spaceBetweenPorts + fmax fl0p0 additional
  return (currentPos, spaceBetweenPorts)

/-- The port loop of `placeHorizontalFreePorts` from context `i` on, at `x`: the port goes to
`x + left margin` (y by `calculateHorizontalPortYCoordinate`), the next one to
`x + (left margin + width + right margin + gap)`. Updates the contexts in place
(`withPortPosition`; the Java loop's arithmetic order). -/
private partial def placeHorizontalFreeLoop (pcs : Array (PortContext P L)) (i : Nat) (x gap : Float) :
    Array (PortContext P L) :=
  if h : i < pcs.size then
    let pc := pcs[i]
    let left := pc.portMargin.left
    let pos : KVector := { x := x + left, y := calculateHorizontalPortYCoordinate pc }
    let next := x + (left + pc.portSize.x + pc.portMargin.right + gap)
    placeHorizontalFreeLoop (pcs.modify i (·.withPortPosition pos)) (i + 1) next gap
  else pcs

/-- The port loop of `placeVerticalFreePorts` from context `i` on, at `y` (see
`placeHorizontalFreeLoop`). -/
private partial def placeVerticalFreeLoop (pcs : Array (PortContext P L)) (i : Nat) (nodeWidth y gap : Float) :
    Array (PortContext P L) :=
  if h : i < pcs.size then
    let pc := pcs[i]
    let top := pc.portMargin.top
    let pos : KVector := { x := calculateVerticalPortXCoordinate pc nodeWidth, y := y + top }
    let next := y + (top + pc.portSize.y + pc.portMargin.bottom + gap)
    placeVerticalFreeLoop (pcs.modify i (·.withPortPosition pos)) (i + 1) nodeWidth next gap
  else pcs

/-! ### Horizontal port placement -/

/-- `placeHorizontalFixedPosPorts(nodeContext, portSide)`: the x coordinate is fixed, only the y
coordinate is adjusted to the border offset. -/
private def placeHorizontalFixedPosPorts (ctx : NodeContext N P L) (portSide : PortSide) : NodeContext N P L :=
  ctx.modifyPortContextsOf portSide fun pcs => pcs.map fun pc =>
    let pos : KVector := { pc.portPosition with y := calculateHorizontalPortYCoordinate pc }
    pc.withPortPosition pos

/-- `placeHorizontalFixedRatioPorts(nodeContext, portSide)`: x = node width × position ratio. -/
private def placeHorizontalFixedRatioPorts (ctx : NodeContext N P L) (portSide : PortSide) : NodeContext N P L :=
  let nodeWidth := ctx.nodeSize.x
  ctx.modifyPortContextsOf portSide fun pcs => pcs.map fun pc =>
    let pos : KVector := { x := nodeWidth * pc.portRatioOrPosition, y := calculateHorizontalPortYCoordinate pc }
    pc.withPortPosition pos

/-- `placeHorizontalFreePorts(nodeContext, portSide)`: places the ports inside the content area
of the side's inside port label cell according to the side's port alignment. The port margins
already include the space reserved for port labels. -/
private def placeHorizontalFreePorts (ctx : NodeContext N P L) (portSide : PortSide) : NodeContext N P L := Id.run do
  let portContexts := ctx.portContextsOf portSide
  let portCount := portContexts.size
  if portCount == 0 then
    return ctx
  -- Read cell information
  let some cell := ctx.insidePortLabelCell portSide | return ctx
  let cellRect := ctx.cells.cellRectangle cell
  let cellPadding := ctx.cells.padding cell
  let minContentX := (ctx.cells.minimumContentAreaSize cell).x
  let availableSpace := cellRect.width - cellPadding.left - cellPadding.right
  let (start, spaceBetweenPorts) := freePortPlacementStart ctx portCount (ctx.getPortAlignment portSide)
    availableSpace minContentX (cellRect.x + cellPadding.left)
  -- Iterate over all ports and place them (on the contexts taken out of the node context)
  return ctx.modifyPortContextsOf portSide fun pcs => placeHorizontalFreeLoop pcs 0 start spaceBetweenPorts

/-- `placeHorizontalPorts(nodeContext)`: places the northern, then the southern ports according
to the port constraints (`FIXED_POS`, `FIXED_RATIO`, anything else is free). -/
def placeHorizontalPorts (ctx : NodeContext N P L) : NodeContext N P L :=
  match ctx.portConstraints with
  | .fixedPos => placeHorizontalFixedPosPorts (placeHorizontalFixedPosPorts ctx .north) .south
  | .fixedRatio => placeHorizontalFixedRatioPorts (placeHorizontalFixedRatioPorts ctx .north) .south
  | _ => placeHorizontalFreePorts (placeHorizontalFreePorts ctx .north) .south

/-! ### Vertical port placement -/

/-- `placeVerticalFixedPosPorts(nodeContext, portSide)`: the y coordinate is fixed, only the x
coordinate is adjusted to the node width and the border offset. -/
private def placeVerticalFixedPosPorts (ctx : NodeContext N P L) (portSide : PortSide) : NodeContext N P L :=
  let nodeWidth := ctx.nodeSize.x
  ctx.modifyPortContextsOf portSide fun pcs => pcs.map fun pc =>
    let pos : KVector := { pc.portPosition with x := calculateVerticalPortXCoordinate pc nodeWidth }
    pc.withPortPosition pos

/-- `placeVerticalFixedRatioPorts(nodeContext, portSide)`: y = node height × position ratio. -/
private def placeVerticalFixedRatioPorts (ctx : NodeContext N P L) (portSide : PortSide) : NodeContext N P L :=
  let nodeWidth := ctx.nodeSize.x
  let nodeHeight := ctx.nodeSize.y
  ctx.modifyPortContextsOf portSide fun pcs => pcs.map fun pc =>
    let pos : KVector := { x := calculateVerticalPortXCoordinate pc nodeWidth, y := nodeHeight * pc.portRatioOrPosition }
    pc.withPortPosition pos

/-- `placeVerticalFreePorts(nodeContext, portSide)`: places the ports inside the content area of
the side's inside port label cell according to the side's port alignment. -/
private def placeVerticalFreePorts (ctx : NodeContext N P L) (portSide : PortSide) : NodeContext N P L := Id.run do
  let portContexts := ctx.portContextsOf portSide
  let portCount := portContexts.size
  if portCount == 0 then
    return ctx
  -- Read cell information
  let some cell := ctx.insidePortLabelCell portSide | return ctx
  let cellRect := ctx.cells.cellRectangle cell
  let cellPadding := ctx.cells.padding cell
  let minContentY := (ctx.cells.minimumContentAreaSize cell).y
  let availableSpace := cellRect.height - cellPadding.top - cellPadding.bottom
  let nodeWidth := ctx.nodeSize.x
  let (start, spaceBetweenPorts) := freePortPlacementStart ctx portCount (ctx.getPortAlignment portSide)
    availableSpace minContentY (cellRect.y + cellPadding.top)
  -- Iterate over all ports and place them (on the contexts taken out of the node context)
  return ctx.modifyPortContextsOf portSide fun pcs => placeVerticalFreeLoop pcs 0 nodeWidth start spaceBetweenPorts

/-- `placeVerticalPorts(nodeContext)`: places the eastern, then the western ports according to
the port constraints (`FIXED_POS`, `FIXED_RATIO`, anything else is free). -/
def placeVerticalPorts (ctx : NodeContext N P L) : NodeContext N P L :=
  match ctx.portConstraints with
  | .fixedPos => placeVerticalFixedPosPorts (placeVerticalFixedPosPorts ctx .east) .west
  | .fixedRatio => placeVerticalFixedRatioPorts (placeVerticalFixedRatioPorts ctx .east) .west
  | _ => placeVerticalFreePorts (placeVerticalFreePorts ctx .east) .west

end PortPlacementCalculator

end Elk.Alg.Common.NodeSpacing.Internal.Algorithm
