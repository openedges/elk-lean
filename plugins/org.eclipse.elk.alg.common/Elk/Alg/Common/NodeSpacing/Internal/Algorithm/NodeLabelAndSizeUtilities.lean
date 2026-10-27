import Elk.Core.Util.ElkUtil
import Elk.Alg.Common.NodeSpacing.Internal.NodeContext
/-!
# `org.eclipse.elk.alg.common.nodespacing.internal.algorithm.NodeLabelAndSizeUtilities`

Various little methods that didn't quite fit into any of the other classes (elk-rs
`internal::algorithm::NodeLabelAndSizeUtilities`). All functions work on the `NodeContext`
(pure); the ones that write to the graph (`setNodePadding`, `applyStuff`) take the adapters.

Notes on elk-rs:
* elk-rs `set_node_padding` returns the padding instead of applying it, and its
  `NodeLabelAndSizeCalculator::process_with_options` discards that value. `computeNodePadding`
  is the elk-rs function; `setNodePadding` applies it like Java. The calculator port (N3) must
  pick the variant that matches the oracle.
* elk-rs `apply_stuff` is inlined in `process_with_options` (node size, then port positions by
  volatile-id order); `applyStuff` applies through the stored port handles, which is equivalent.
-/
namespace Elk.Alg.Common.NodeSpacing.Internal.Algorithm

open Elk Elk.Core.Math Elk.Core.Util Elk.Core.Options Elk.Core.Util.Adapters
open Elk.Alg.Common.NodeSpacing.CellSystem Elk.Alg.Common.NodeSpacing.Internal

namespace NodeLabelAndSizeUtilities

variable {N P L : Type}

/-! ### Minimum size things -/

/-- `getMinimumNodeOrClientAreaSize(nodeContext)`: `NODE_SIZE_MINIMUM`, with non-positive
components replaced by `ElkUtil.DEFAULT_MIN_WIDTH/HEIGHT` if `DEFAULT_MINIMUM_SIZE` is set. -/
def getMinimumNodeOrClientAreaSize (ctx : NodeContext N P L) : KVector := Id.run do
  let mut minSize := ctx.nodeSizeMinimum
  -- If we are instructed to revert to a default minimum size, check whether we need to
  if ctx.sizeOptions.contains .defaultMinimumSize then
    if minSize.x <= 0.0 then
      minSize := { minSize with x := ElkUtil.DEFAULT_MIN_WIDTH }
    if minSize.y <= 0.0 then
      minSize := { minSize with y := ElkUtil.DEFAULT_MIN_HEIGHT }
  return minSize

/-- `getMinimumClientAreaSize(nodeContext)`: the client area's minimum size if `MINIMUM_SIZE` and
`MINIMUM_SIZE_ACCOUNTS_FOR_PADDING` are set, else `none`. -/
def getMinimumClientAreaSize (ctx : NodeContext N P L) : Option KVector :=
  if ctx.sizeConstraints.contains .minimumSize && ctx.sizeOptions.contains .minimumSizeAccountsForPadding then
    some (getMinimumNodeOrClientAreaSize ctx)
  else none

/-- `getMinimumNodeSize(nodeContext)`: the node's minimum size if `MINIMUM_SIZE` is set and
`MINIMUM_SIZE_ACCOUNTS_FOR_PADDING` is not, else `none`. -/
def getMinimumNodeSize (ctx : NodeContext N P L) : Option KVector :=
  if ctx.sizeConstraints.contains .minimumSize && !ctx.sizeOptions.contains .minimumSizeAccountsForPadding then
    some (getMinimumNodeOrClientAreaSize ctx)
  else none

/-! ### Algorithm phase implementation fragments -/

/-- `setupMinimumClientAreaSize(nodeContext)`: imposes the client area minimum size (if any) on
the inside node label container's center cell. Does not touch contribution flags. -/
def setupMinimumClientAreaSize (ctx : NodeContext N P L) : NodeContext N P L :=
  match getMinimumClientAreaSize ctx, ctx.insideNodeLabelContainer with
  | some minSize, some container => ctx.modifyCells (·.setCenterCellMinimumSize container minSize)
  | _, _ => ctx

/-- Grows the node container padding on the port's side to `-portBorderOffset` (ports extending
into the node). -/
private def growForBorderOffset (p : ElkPadding) (side : PortSide) (portBorderOffset : Float) : ElkPadding :=
  match side with
  | .north => { p with top := fmax p.top (-portBorderOffset) }
  | .south => { p with bottom := fmax p.bottom (-portBorderOffset) }
  | .east => { p with right := fmax p.right (-portBorderOffset) }
  | .west => { p with left := fmax p.left (-portBorderOffset) }
  | .undefined => p

/-- Grows the node container padding for the inside part of fixed port labels, mirroring the
padding of the opposite side if the node is symmetric (the border offset is added there). -/
private def growForInsidePart (p : ElkPadding) (side : PortSide) (maxInsidePart portBorderOffset : Float)
    (symmetry : Bool) : ElkPadding :=
  match side with
  | .north =>
    let insidePartIsBigger := maxInsidePart > p.top
    let p := { p with top := fmax p.top maxInsidePart }
    if symmetry && insidePartIsBigger then
      let p := { p with top := fmax p.top p.bottom }
      { p with bottom := p.top + portBorderOffset }
    else p
  | .south =>
    let insidePartIsBigger := maxInsidePart > p.bottom
    let p := { p with bottom := fmax p.bottom maxInsidePart }
    if symmetry && insidePartIsBigger then
      let p := { p with bottom := fmax p.bottom p.top }
      { p with top := p.bottom + portBorderOffset }
    else p
  | .east =>
    let insidePartIsBigger := maxInsidePart > p.right
    let p := { p with right := fmax p.right maxInsidePart }
    if symmetry && insidePartIsBigger then
      let p := { p with right := fmax p.left p.right }
      { p with left := p.right + portBorderOffset }
    else p
  | .west =>
    let insidePartIsBigger := maxInsidePart > p.left
    let p := { p with left := fmax p.left maxInsidePart }
    if symmetry && insidePartIsBigger then
      let p := { p with left := fmax p.left p.right }
      { p with right := p.left + portBorderOffset }
    else p
  | .undefined => p

/-- `setupNodePaddingForPortsWithOffset(nodeContext)`: grows the node container's padding for
ports with a negative `PORT_BORDER_OFFSET` and, with fixed port labels, for the part of the labels
that lies inside the node (elk-rs: maximum `ElkUtil.computeInsidePart` over the labels, applied
only if positive). Ports are visited in `portContexts.values()` order. -/
def setupNodePaddingForPortsWithOffset (ctx : NodeContext N P L) : NodeContext N P L := Id.run do
  let isFixed := PortLabelPlacement.isFixed ctx.portLabelsPlacement
  let symmetry := !ctx.sizeOptions.contains .asymmetrical
  let mut padding := ctx.cells.padding ctx.nodeContainer
  for pc in ctx.allPortContexts do
    -- If the port extends into the node, ensure the inside port space is enough
    if pc.hasPortBorderOffset && pc.portBorderOffset < 0.0 then
      padding := growForBorderOffset padding pc.portSide pc.portBorderOffset
    if isFixed then
      -- Compute the maximum inside part across all labels
      let mut maxInsidePart := 0.0
      for (labelPos, labelSize) in pc.labelPositions.zip pc.labelSizes do
        let inside := ElkUtil.computeInsidePart labelPos labelSize pc.portSize pc.portBorderOffset pc.portSide
        maxInsidePart := fmax maxInsidePart inside
      if maxInsidePart > 0.0 then
        padding := growForInsidePart padding pc.portSide maxInsidePart pc.portBorderOffset symmetry
  return ctx.modifyCells (·.setPadding ctx.nodeContainer padding)

/-- `offsetSouthernPortsByNodeSize(nodeContext)`: moves the southern ports (placed relative to
y = 0) down by the node height. -/
def offsetSouthernPortsByNodeSize (ctx : NodeContext N P L) : NodeContext N P L :=
  let nodeHeight := ctx.nodeSize.y
  ctx.modifyPortContextsOf .south fun pcs =>
    pcs.map fun pc => { pc with portPosition := { pc.portPosition with y := pc.portPosition.y + nodeHeight } }

/-- elk-rs `set_node_padding(nodeContext)`: the node padding implied by the client area (center
cell rectangle of the inside node label container) if `COMPUTE_PADDING` is set, else `none`. -/
def computeNodePadding (ctx : NodeContext N P L) : Option ElkPadding :=
  if !ctx.sizeOptions.contains .computePadding then none
  else
    let nodeRect := ctx.cells.cellRectangle ctx.nodeContainer
    let clientArea := match ctx.insideNodeLabelContainer with
      | some c => ctx.cells.centerCellRectangle c
      | none => {}
    some {
      left := clientArea.x - nodeRect.x
      top := clientArea.y - nodeRect.y
      right := (nodeRect.x + nodeRect.width) - (clientArea.x + clientArea.width)
      bottom := (nodeRect.y + nodeRect.height) - (clientArea.y + clientArea.height) }

/-- Java `setNodePadding(nodeContext)`: applies `computeNodePadding` to the node (`setPadding`).
See the module doc: elk-rs computes but never applies this padding. -/
def setNodePadding {m : Type → Type} [Monad m] {G E : Type} (a : GraphAdapters m G N P L E)
    (ctx : NodeContext N P L) : m Unit := do
  if let some padding := computeNodePadding ctx then
    a.setPadding ctx.node padding

/-- `applyStuff(nodeContext)`: applies the node size, then every port position (in
`portContexts.values()` order). -/
def applyStuff {m : Type → Type} [Monad m] {G E : Type} (a : GraphAdapters m G N P L E)
    (ctx : NodeContext N P L) : m Unit := do
  ctx.applyNodeSize a
  for pc in ctx.allPortContexts do
    pc.applyPortPosition a

/-! ### Utilities -/

/-- `areSizeConstraintsFixed(nodeContext)`: the constraints are empty or exactly
`{PORT_LABELS}` (`EFFECTIVELY_FIXED_SIZE_CONSTRAINTS`). -/
def areSizeConstraintsFixed (ctx : NodeContext N P L) : Bool :=
  ctx.sizeConstraints.isEmpty || ctx.sizeConstraints == EnumSet.of #[SizeConstraint.portLabels]

/-- `isFirstOutsidePortLabelPlacedDifferently(nodeContext, portSide)`: with at least two ports on
the side, the first port's label goes to the other side if it is not placed next to the port,
`ALWAYS_SAME_SIDE` is not set, and there are exactly two ports or `SPACE_EFFICIENT` is set. -/
def isFirstOutsidePortLabelPlacedDifferently (ctx : NodeContext N P L) (portSide : PortSide) : Bool :=
  let portContexts := ctx.portContextsOf portSide
  if h : 2 ≤ portContexts.size then
    let firstPort := portContexts[0]'(by omega)
    let alwaysSameSide := ctx.portLabelsPlacement.contains .alwaysSameSide
    let spaceEfficient := ctx.portLabelsPlacement.contains .spaceEfficient
    !firstPort.labelsNextToPort && !alwaysSameSide && (portContexts.size == 2 || spaceEfficient)
  else false

end NodeLabelAndSizeUtilities

end Elk.Alg.Common.NodeSpacing.Internal.Algorithm
