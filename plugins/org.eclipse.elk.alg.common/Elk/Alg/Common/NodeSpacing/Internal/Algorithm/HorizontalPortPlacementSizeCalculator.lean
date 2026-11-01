import Elk.Core.Util.Java
import Elk.Alg.Common.NodeSpacing.Internal.NodeContext
import Elk.Core.Util.FloatConst
open Elk.Core.Util.FloatConst
/-!
# `org.eclipse.elk.alg.common.nodespacing.internal.algorithm.HorizontalPortPlacementSizeCalculator`

Calculates the space required to set up the horizontal (northern and southern) port placements
(elk-rs `internal::algorithm::HorizontalPortPlacementSizeCalculator`, PHASE 3 of the node size
calculation). The result is written to the side's inside port label cell: its left/right padding
and the width of its minimum content area. With `SizeConstraint.PORT_LABELS`, the port margins
are set up first so that they include the space needed by the port labels.

Inside port label cells: Java has one `AtomicCell` per side, shared by
`NodeContext.insidePortLabelCells` and the node container (`BEGIN` = NORTH, `END` = SOUTH).
elk-rs holds two copies and updates both; in the Lean arena both refer to the same cell, which
is updated once (`updateInsidePortLabelCells`).

`minSizeRequiredToRespectSpacing` treats ratios as equal like Java's `DoubleMath.fuzzyEquals`
(difference at most `EQUALITY_TOLERANCE`; elk-rs requires a difference strictly below it).

Deviations from Java (following elk-rs):
* `FIXED_RATIO` reads `PortContext.portRatioOrPosition` (the port's `PORT_RATIO_OR_POSITION`, read
  once when the context is created) and sets up the port margins once before the loop (Java calls
  `setupPortMargins` once per port).
* `Math.max` is `f64::max` (`fmax`).
-/

namespace Elk.Alg.Common.NodeSpacing.Internal.Algorithm

open Elk Elk.Core.Math Elk.Core.Util Elk.Core.Options
open Elk.Alg.Common.NodeSpacing.CellSystem Elk.Alg.Common.NodeSpacing.Internal

namespace HorizontalPortPlacementSizeCalculator

variable {N P L : Type}

/-- `EQUALITY_TOLERANCE`: fuzziness allowed to still consider two ratios equal. -/
private def EQUALITY_TOLERANCE : Float := 0.01

/-- Applies `f` to the side's inside port label cell (Java `insidePortLabelCells.get(portSide)`)
and to the atomic cell in the node container's `BEGIN` (NORTH) / `END` (SOUTH) area. elk-rs
updates both of its copies; when both ids denote the same arena cell (the normal case) the
update is applied once. Other sides are ignored. -/
@[inline] private def updateInsidePortLabelCells (ctx : NodeContext N P L) (portSide : PortSide)
    (f : CellArena L → CellId → CellArena L) : NodeContext N P L :=
  let area? : Option ContainerArea := match portSide with
    | .north => some .begin
    | .south => some .«end»
    | _ => none
  match area? with
  | none => ctx
  | some area =>
    let containerCell := (ctx.cells.getCell ctx.nodeContainer area).filter ctx.cells.isAtomic
    let insideCell := ctx.insidePortLabelCell portSide
    -- the arena is taken out of the context first so that it is updated in place
    ctx.modifyCells fun cells =>
      let cells := match containerCell with
        | some c => f cells c
        | none => cells
      match insideCell with
      | some c => if containerCell == some c then cells else f cells c
      | none => cells

/-! ### Fixed position -/

/-- `calculateHorizontalNodeSizeRequiredByFixedPosPorts(nodeContext, portSide)`: the cell's
content width is the rightmost port border; the left padding is removed. -/
private def calculateHorizontalNodeSizeRequiredByFixedPosPorts (ctx : NodeContext N P L) (portSide : PortSide) :
    NodeContext N P L :=
  let rightmostPortBorder := (ctx.portContextsOf portSide).foldl
    (fun m pc => fmax m (pc.portPosition.x + pc.portSize.x)) 0.0
  -- Set the cell size and remove the left padding
  updateInsidePortLabelCells ctx portSide fun cs c =>
    (cs.modifyPadding c fun p => { p with left := 0.0 }).modifyMinimumContentAreaSize c
      fun s => { s with x := rightmostPortBorder }

/-! ### Fixed ratio -/

/-- `minSizeRequiredToRespectSpacing(spacing, firstRatio, secondRatio)`: the minimum width that
satisfies the given spacing between the two ratios multiplied by that width (`0` if the ratios
are (nearly) equal). -/
def minSizeRequiredToRespectSpacing (spacing firstRatio secondRatio : Float) : Float :=
  -- Guava `DoubleMath.fuzzyEquals(a, b, tol)`: `|a - b| <= tol || a == b || (isNaN a && isNaN b)`
  if (firstRatio - secondRatio).abs ≤ EQUALITY_TOLERANCE || firstRatio == secondRatio
      || (firstRatio.isNaN && secondRatio.isNaN) then fl0p0
  else spacing / (secondRatio - firstRatio)

/-! ### Port margins -/

/-- The body of the `computeHorizontalPortMargins` loop for one port context: the new port
margin. -/
private def horizontalPortMargin (cells : CellArena L) (isFixed : Bool) (portLabelSpacingH : Float)
    (pc : PortContext P L) : ElkMargin := Id.run do
  let mut margin := pc.portMargin
  let labelWidth := match pc.portLabelCell with
    | some c => cells.minimumWidth c
    | none => 0.0
  if labelWidth > 0.0 then
    if pc.labelsNextToPort then
      -- The label is placed next to (centered on) the port
      let portWidth := pc.portSize.x
      if labelWidth > portWidth then
        let overhang := (labelWidth - portWidth) / 2.0
        margin := { margin with left := overhang, right := overhang }
    else
      -- The label is placed right of the port
      margin := { margin with right := portLabelSpacingH + labelWidth }
  else if isFixed then
    -- Fixed labels are not in the label cell: use their bounds
    let labelsBounds := pc.getLabelsBounds
    if labelsBounds.x < 0.0 then
      margin := { margin with left := -labelsBounds.x }
    if labelsBounds.x + labelsBounds.width > pc.portSize.x then
      margin := { margin with right := labelsBounds.x + labelsBounds.width - pc.portSize.x }
  return margin

/-- `computeHorizontalPortMargins(nodeContext, portSide, portLabelsOutside)`: sets the
horizontal margins of the side's ports to include the space of their labels (label cell
centered on the port or placed to its right; fixed labels by their bounds). -/
private def computeHorizontalPortMargins (ctx : NodeContext N P L) (portSide : PortSide)
    (_portLabelsOutside : Bool) : NodeContext N P L :=
  let isFixed := PortLabelPlacement.isFixed ctx.portLabelsPlacement
  let portLabelSpacingH := ctx.portLabelSpacingHorizontal
  let cells := ctx.cells
  ctx.modifyPortContextsOf portSide fun pcs => pcs.map fun pc =>
    let m := horizontalPortMargin cells isFixed portLabelSpacingH pc
    pc.withPortMargin m

/-- `unifyPortMargins(portContexts)`: sets every left/right margin to the maximum one. -/
private def unifyPortMargins (pcs : Array (PortContext P L)) : Array (PortContext P L) :=
  let maxLeft := pcs.foldl (fun m pc => fmax m pc.portMargin.left) 0.0
  let maxRight := pcs.foldl (fun m pc => fmax m pc.portMargin.right) 0.0
  pcs.map (·.withMarginLeftRight maxLeft maxRight)

/-- Sets the left margin of the first and the right margin of the last context to `0`. -/
private def clearOuterMargins (pcs : Array (PortContext P L)) : Array (PortContext P L) :=
  if pcs.isEmpty then pcs
  else
    let pcs := pcs.modify 0 (·.withMarginLeft fl0p0)
    pcs.modify (pcs.size - 1) (·.withMarginRight fl0p0)

/-- `setupPortMargins(nodeContext, portSide)`: port margins including the label space, subject to
the outside / space-efficient / uniform port spacing options. -/
private def setupPortMargins (ctx : NodeContext N P L) (portSide : PortSide) : NodeContext N P L :=
  let portLabelsOutside := ctx.portLabelsPlacement.contains .outside
  let alwaysSameSide := ctx.portLabelsPlacement.contains .alwaysSameSide
  let alwaysSameSideAbove := ctx.portLabelsPlacement.contains .alwaysOtherSameSide
  let spaceEfficient := ctx.portLabelsPlacement.contains .spaceEfficient
  let uniformPortSpacing := ctx.sizeOptions.contains .uniformPortSpacing
  let portCount := (ctx.portContextsOf portSide).size
  let spaceEfficientPortLabels := !alwaysSameSide && !alwaysSameSideAbove && (spaceEfficient || portCount == 2)
  -- Set the horizontal port margins
  let ctx := computeHorizontalPortMargins ctx portSide portLabelsOutside
  let ctx := if portLabelsOutside then
      ctx.modifyPortContextsOf portSide fun pcs =>
        -- The first port doesn't need a left margin, the last port doesn't need a right margin
        let pcs := clearOuterMargins pcs
        -- Space-efficient: the first port doesn't need a right margin if its label is not next to it
        match pcs[0]? with
        | some first =>
          if spaceEfficientPortLabels && !first.labelsNextToPort then
            pcs.modify 0 (·.withMarginRight fl0p0)
          else pcs
        | none => pcs
    else ctx
  if uniformPortSpacing then
    ctx.modifyPortContextsOf portSide fun pcs =>
      let pcs := unifyPortMargins pcs
      if portLabelsOutside then clearOuterMargins pcs else pcs
  else ctx

/-- `portWidthPlusPortPortSpacing(nodeContext, portSide)`: the sum of the port widths including
their margins, with a port-port spacing between consecutive ports. -/
private def portWidthPlusPortPortSpacing (ctx : NodeContext N P L) (portSide : PortSide) : Float := Id.run do
  let pcs := ctx.portContextsOf portSide
  let mut result := 0.0
  let mut i := 0
  for pc in pcs do
    result := result + (pc.portMargin.left + pc.portSize.x + pc.portMargin.right)
    if i + 1 < pcs.size then
      result := result + ctx.portPortSpacing
    i := i + 1
  return result

/-! ### Fixed ratio and free placement -/

/-- `calculateHorizontalNodeSizeRequiredByFixedRatioPorts(nodeContext, portSide)`: the minimum
width such that consecutive ports (and the surrounding port margins) keep their spacing at the
ports' position ratios; the left padding is removed. Without ports, the left/right padding is
cleared. -/
private def calculateHorizontalNodeSizeRequiredByFixedRatioPorts (ctx : NodeContext N P L) (portSide : PortSide) :
    NodeContext N P L := Id.run do
  if (ctx.portContextsOf portSide).isEmpty then
    return updateInsidePortLabelCells ctx portSide fun cs c =>
      cs.modifyPadding c fun p => { p with left := fl0p0, right := fl0p0 }
  let portLabelsInside := ctx.portLabelsPlacement.contains .inside
  let mut ctx := ctx
  if ctx.sizeConstraints.contains .portLabels then
    ctx := setupPortMargins ctx portSide
  let mut minWidth := fl0p0
  let surroundingLeft := ctx.surroundingPortMargins.left
  let surroundingRight := ctx.surroundingPortMargins.right
  let portPortSpacing := ctx.portPortSpacing
  -- (ratio, width, right margin) of the previous port
  let mut previous : Option (Float × Float × Float) := none
  for pc in ctx.portContextsOf portSide do
    let ratio := pc.portRatioOrPosition
    match previous with
    | some (prevRatio, prevWidth, prevMarginRight) =>
      let requiredSpace := prevWidth + prevMarginRight + portPortSpacing + pc.portMargin.left
      minWidth := fmax minWidth (minSizeRequiredToRespectSpacing requiredSpace prevRatio ratio)
    | none =>
      -- First port: respect the left surrounding port margin
      if surroundingLeft > fl0p0 then
        minWidth := fmax minWidth (minSizeRequiredToRespectSpacing (surroundingLeft + pc.portMargin.left) fl0p0 ratio)
    previous := some (ratio, pc.portSize.x, pc.portMargin.right)
  -- Right surrounding port margin
  if let some (prevRatio, prevWidth, prevMarginRight) := previous then
    if surroundingRight > fl0p0 then
      let mut requiredSpace := prevWidth + surroundingRight
      if portLabelsInside then
        requiredSpace := requiredSpace + prevMarginRight
      minWidth := fmax minWidth (minSizeRequiredToRespectSpacing requiredSpace prevRatio fl1p0)
  -- Set the cell size and remove the left padding
  return updateInsidePortLabelCells ctx portSide fun cs c =>
    (cs.modifyPadding c fun p => { p with left := fl0p0 }).modifyMinimumContentAreaSize c
      fun s => { s with x := minWidth }

/-- `calculateHorizontalNodeSizeRequiredByFreePorts(nodeContext, portSide)`: the padding is the
surrounding port margin, the content width the sum of the port widths and margins plus the
port-port spacings (and two more spacings for `DISTRIBUTED` alignment). Without ports, the
left/right padding is cleared. -/
private def calculateHorizontalNodeSizeRequiredByFreePorts (ctx : NodeContext N P L) (portSide : PortSide) :
    NodeContext N P L := Id.run do
  if (ctx.portContextsOf portSide).isEmpty then
    return updateInsidePortLabelCells ctx portSide fun cs c =>
      cs.modifyPadding c fun p => { p with left := fl0p0, right := fl0p0 }
  -- Set the padding to match the surrounding port space
  let surrLeft := ctx.surroundingPortMargins.left
  let surrRight := ctx.surroundingPortMargins.right
  let mut ctx := updateInsidePortLabelCells ctx portSide fun cs c =>
    cs.modifyPadding c fun p => { p with left := surrLeft, right := surrRight }
  if ctx.sizeConstraints.contains .portLabels then
    ctx := setupPortMargins ctx portSide
  let mut width := portWidthPlusPortPortSpacing ctx portSide
  if ctx.getPortAlignment portSide == .distributed then
    width := width + fl2p0 * ctx.portPortSpacing
  -- Set the cell size
  return updateInsidePortLabelCells ctx portSide fun cs c =>
    cs.modifyMinimumContentAreaSize c fun s => { s with x := width }

/-- `calculateHorizontalPortPlacementSize(nodeContext)`: the space required by the northern and
southern ports (computed even if ports are not part of the size constraints, since the port
placement uses it). -/
def calculateHorizontalPortPlacementSize (ctx : NodeContext N P L) : NodeContext N P L :=
  match ctx.portConstraints with
  | .fixedPos =>
    calculateHorizontalNodeSizeRequiredByFixedPosPorts
      (calculateHorizontalNodeSizeRequiredByFixedPosPorts ctx .north) .south
  | .fixedRatio =>
    calculateHorizontalNodeSizeRequiredByFixedRatioPorts
      (calculateHorizontalNodeSizeRequiredByFixedRatioPorts ctx .north) .south
  | _ =>
    calculateHorizontalNodeSizeRequiredByFreePorts
      (calculateHorizontalNodeSizeRequiredByFreePorts ctx .north) .south

end HorizontalPortPlacementSizeCalculator

end Elk.Alg.Common.NodeSpacing.Internal.Algorithm
