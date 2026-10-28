import Elk.Alg.Layered.LayeredPhases
import Elk.Alg.Layered.Graph.LGraphUtil
import Elk.Core.Util.Java
import Elk.Alg.Layered.Intermediate.LongEdgeJoiner
/-!
# `org.eclipse.elk.alg.layered.intermediate.LabelDummyRemover`

Port of elk-rs `intermediate/label_dummy_remover.rs` (Java `LabelDummyRemover`): "Processor that
removes the inserted center label dummies and places the labels on their position."

Slot: after phase 5 (same-slot dependency `HierarchicalPortOrthogonalEdgeRouter`). Postcondition:
labels are placed, there are no `LABEL` dummy nodes left and the center labels are attached to their
original edges again.

Iteration order (Rust): the graph's layers, per layer a copy of its node list; each `LABEL` node is
processed (`place_labels_and_restore_edge`), joined (`LongEdgeJoiner::join_at`, bend point at the dummy
for polyline routing) and removed from its layer.

Labels are placed from the dummy position (moved below the edge by `thickness + edgeLabelSpacing`
for `LABEL_SIDE = BELOW`) inside the label space `(width, height - thickness - edgeLabelSpacing)`
(full height for inline labels): stacked and centred horizontally, or side by side in vertical
layouts (inline-centred, top-aligned below the edge, else bottom-aligned; reverse order for `UP`).

Rust additions over Java (ported): in horizontal layouts without spline routing the dummy x position
is first adjusted to the post-compaction bounds (`LEFT`/`RIGHT` compaction with known `SPACINGS`,
`adjust_horizontal_dummy_position_for_post_compaction`); a dummy whose `ORIGIN` is not an `LEdge` or
that represents no labels is only joined and removed (Java would fail).

Dummies are joined with `LongEdgeJoiner.joinAt` (elk-rs `LongEdgeJoiner::join_at`).
-/
/-! Float literals as global constants (FL): inside branches, loops and specialised code the compiler
shares a literal's `Nat`/`Bool` arguments with unrelated variables (CSE) and then parses it on every
evaluation (`FastFloat.ofScientificImpl`); a top-level constant is a load (PLAN §7.1 items 17, 22). -/
private def fl2p0 : Float := 2.0

namespace Elk.Alg.Layered.Intermediate

open Elk.Graph Elk.Core Elk.Core.Alg Elk.Core.Math Elk.Core.Options Elk.Core.Util Elk.Alg.Layered
  Elk.Alg.Layered.Graph Elk.Alg.Layered.Options LayeredM

namespace LabelDummyRemover

/-- Rust `edge_thickness(edge)`: the stored `EDGE_THICKNESS`, else `1.0`. -/
def edgeThickness (edge : LEdgeId) : LayeredM Float := do
  let ed ← getEdge edge
  if ed.props.has CoreOptions.EDGE_THICKNESS then
    return ed.props.getD CoreOptions.EDGE_THICKNESS 1.0
  return 1.0

/-- Rust `label_inline_property(label)`: the stored `EDGE_LABELS_INLINE`, else `false`. -/
def labelInlineProperty (label : LLabelId) : LayeredM Bool := do
  let lb ← getLabel label
  if lb.props.has LayeredOptions.EDGE_LABELS_INLINE then
    return lb.props.getD LayeredOptions.EDGE_LABELS_INLINE false
  return false

/-- Rust `labels.iter().all(label_inline_property)` (`true` for an empty list). -/
def allInline (labels : Array LLabelId) : LayeredM Bool := do
  for l in labels do
    if !(← labelInlineProperty l) then return false
  return true

/-- Rust `adjacent_source_and_target_nodes(node)`: the source of the first incoming edge of the first
`WEST` port and the target of the first outgoing edge of the first `EAST` port. -/
def adjacentSourceAndTargetNodes (node : LNodeId) : LayeredM (Option (LNodeId × LNodeId)) := do
  let westPort := (← withArena (·.nodePortsBySide node .west))[0]?
  let eastPort := (← withArena (·.nodePortsBySide node .east))[0]?
  let some westPort := westPort | return none
  let some incomingEdge := (← getPort westPort).incomingEdges[0]? | return none
  let some eastPort := eastPort | return none
  let some outgoingEdge := (← getPort eastPort).outgoingEdges[0]? | return none
  let some sourcePort := (← getEdge incomingEdge).source | return none
  let some sourceNode := (← getPort sourcePort).owner | return none
  let some targetPort := (← getEdge outgoingEdge).target | return none
  let some targetNode := (← getPort targetPort).owner | return none
  return some (sourceNode, targetNode)

/-- Rust `adjust_horizontal_dummy_position_for_post_compaction`: with `LEFT`/`RIGHT` post-compaction
and known spacings, the label x position becomes the left bound (right of the source node plus the
horizontal spacing) or the right bound (left of the target node minus spacing and dummy width); the
left bound wins when the bounds cross; nothing happens for non-finite bounds. -/
def adjustHorizontalDummyPositionForPostCompaction (node : LNodeId) (currLabelPos : KVector) (nodeWidth : Float)
    (compactionStrategy : GraphCompactionStrategy) (spacings : Option Spacings) : LayeredM KVector := do
  if compactionStrategy != .left && compactionStrategy != .right then return currLabelPos
  let some spacings := spacings | return currLabelPos
  let some (sourceNode, targetNode) ← adjacentSourceAndTargetNodes node | return currLabelPos
  let src ← getNode sourceNode
  let sourceRight := src.position.x + src.size.x
  let targetLeft := (← getNode targetNode).position.x
  let leftSpacing ← LGraphUtil.horizontalSpacing spacings sourceNode node
  let rightSpacing ← LGraphUtil.horizontalSpacing spacings node targetNode
  let leftBound := sourceRight + leftSpacing
  let rightBound := targetLeft - rightSpacing - nodeWidth
  if !leftBound.isFinite || !rightBound.isFinite then return currLabelPos
  if leftBound > rightBound then return { currLabelPos with x := leftBound }
  return { currLabelPos with x := if compactionStrategy == .left then leftBound else rightBound }

/-- Rust `place_labels_for_horizontal_layout`: labels centred in the label space, stacked downwards
with `labelSpacing` between them. Returns the advanced position. -/
def placeLabelsForHorizontalLayout (labels : Array LLabelId) (labelPos : KVector) (labelSpacing : Float)
    (labelSpace : KVector) : LayeredM KVector := do
  let mut pos := labelPos
  for label in labels do
    let lb ← getLabel label
    let x := pos.x + (labelSpace.x - lb.size.x) / fl2p0
    let y := pos.y
    modifyLabel label fun l => { l with position := ⟨x, y⟩ }
    pos := { pos with y := pos.y + (lb.size.y + labelSpacing) }
  return pos

/-- Rust `place_vertical_label`: one label at the current x (advanced by its width and the spacing);
y is centred for inline labels, at the top when left-aligned, else bottom-aligned. -/
def placeVerticalLabel (label : LLabelId) (labelPos : KVector) (labelSpacing : Float) (labelSpace : KVector)
    (inline leftAligned : Bool) : LayeredM KVector := do
  let lb ← getLabel label
  let x := labelPos.x
  let y :=
    if inline then labelPos.y + (labelSpace.y - lb.size.y) / fl2p0
    else if leftAligned then labelPos.y
    else labelPos.y + labelSpace.y - lb.size.y
  modifyLabel label fun l => { l with position := ⟨x, y⟩ }
  return { labelPos with x := labelPos.x + (lb.size.x + labelSpacing) }

/-- Rust `place_labels_for_vertical_layout`: labels side by side, in reverse order for `UP`. -/
def placeLabelsForVerticalLayout (labels : Array LLabelId) (labelPos : KVector) (labelSpacing : Float)
    (labelSpace : KVector) (leftAligned : Bool) (layoutDirection : Direction) : LayeredM KVector := do
  let inline ← allInline labels
  let ordered := if layoutDirection == .up then labels.reverse else labels
  let mut pos := labelPos
  for label in ordered do
    pos ← placeVerticalLabel label pos labelSpacing labelSpace inline leftAligned
  return pos

/-- Rust `place_labels_and_restore_edge`: places the represented labels of a label dummy (`ORIGIN`
must be an `LEdge` and the list non-empty) and appends them to the origin edge's labels. -/
def placeLabelsAndRestoreEdge (node : LNodeId) (edgeLabelSpacing labelLabelSpacing : Float)
    (layoutDirection : Direction) (edgeRouting : EdgeRouting) (compactionStrategy : GraphCompactionStrategy)
    (spacings : Option Spacings) : LayeredM Unit := do
  let nd ← getNode node
  let some (.lEdge originEdge) := nd.internal.origin | return
  let representedLabels := nd.internal.representedLabels
  if representedLabels.isEmpty then return
  let thickness ← edgeThickness originEdge
  let labelsBelowEdge := nd.internal.labelSide == .below
  let mut currLabelPos := nd.position
  if labelsBelowEdge then
    currLabelPos := { currLabelPos with y := currLabelPos.y + (thickness + edgeLabelSpacing) }
  let nodeSize := nd.size
  let inlineLabels ← allInline representedLabels
  if !layoutDirection.isVertical && edgeRouting != .splines then
    currLabelPos ← adjustHorizontalDummyPositionForPostCompaction node currLabelPos nodeSize.x
      compactionStrategy spacings
  let spaceAdjust ← if inlineLabels then pure 0.0 else do
    let t ← edgeThickness originEdge
    pure (-t - edgeLabelSpacing)
  let labelSpace : KVector := ⟨nodeSize.x, nodeSize.y + spaceAdjust⟩
  if layoutDirection.isVertical then
    let _ ← placeLabelsForVerticalLayout representedLabels currLabelPos labelLabelSpacing labelSpace
      labelsBelowEdge layoutDirection
  else
    let _ ← placeLabelsForHorizontalLayout representedLabels currLabelPos labelLabelSpacing labelSpace
  modifyEdge originEdge fun e => { e with labels := e.labels ++ representedLabels }

/-- `process(layeredGraph, monitor)`. -/
def process (layeredGraph : LGraphId) (monitor : ProgressMonitor) : LayeredM Unit := do
  let _ ← monitor.begin "Label dummy removal" 1.0
  let gr ← getGraph layeredGraph
  let edgeLabelSpacing := gr.props.getD LayeredOptions.SPACING_EDGE_LABEL 2.0
  let labelLabelSpacing := gr.props.getD LayeredOptions.SPACING_LABEL_LABEL 1.0
  let layoutDirection := gr.props.getD LayeredOptions.DIRECTION Direction.right
  let edgeRouting := gr.props.getD LayeredOptions.EDGE_ROUTING EdgeRouting.orthogonal
  let compactionStrategy := gr.props.getD LayeredOptions.COMPACTION_POST_COMPACTION_STRATEGY GraphCompactionStrategy.none
  let spacings := gr.internal.spacings
  let layers := gr.layers
  for layer in layers do
    let nodes := (← getLayer layer).nodes
    for node in nodes do
      if (← getNode node).type != .label then continue
      placeLabelsAndRestoreEdge node edgeLabelSpacing labelLabelSpacing layoutDirection edgeRouting
        compactionStrategy spacings
      LongEdgeJoiner.joinAt node (edgeRouting == .polyline)
      setNodeLayer node none
  monitor.done

/-- The `LabelDummyRemover` processor. -/
def processor : LayeredProcessor := { name := "LabelDummyRemover", process := process }

end LabelDummyRemover

builtin_initialize registerLabelDummyRemover : Unit ←
  IntermediateProcessorStrategy.register .labelDummyRemover LabelDummyRemover.processor

end Elk.Alg.Layered.Intermediate
