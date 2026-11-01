import Elk.Alg.Layered.LayeredPhases
import Elk.Alg.Layered.Graph.LGraphUtil
import Elk.Core.Util.FloatConst
open Elk.Core.Util.FloatConst
/-!
# `org.eclipse.elk.alg.layered.intermediate.CommentNodeMarginCalculator`

Port of elk-rs `intermediate/comment_node_margin_calculator.rs`. Enlarges the margins of nodes with
attached comment boxes (`TOP_COMMENTS`/`BOTTOM_COMMENTS`): the top/bottom margin grows by the highest box
of the row plus `SPACING_COMMENT_NODE`, and when a row (box widths plus `SPACING_COMMENT_COMMENT` between
them) is wider than the node, the left/right margins are raised to half the protrusion.

The spacings are read like elk-rs `Spacings::get_individual_or_default_with_graph`: the node's individual
spacing, else the processed graph's value (stored or default), else the property default.
-/

namespace Elk.Alg.Layered.Intermediate

open Elk.Graph Elk.Core Elk.Core.Alg Elk.Core.Options Elk.Core.Util Elk.Core.Math Elk.Alg.Layered
  Elk.Alg.Layered.Graph Elk.Alg.Layered.Options LayeredM

namespace CommentNodeMarginCalculator

/-- elk-rs `Spacings::get_individual_or_default_with_graph(graph, node, property)`; throws
`UnspecifiedSpacingException` when no value exists at all. -/
def individualOrDefaultWithGraph {α : Type} [PropCodec α] (graph : LGraphId) (node : LNodeId) (p : Property α) :
    LayeredM α := do
  let props := (← getNode node).props
  let mut value : Option α := none
  if props.has CoreOptions.SPACING_INDIVIDUAL then
    if let some individual := props.get CoreOptions.SPACING_INDIVIDUAL then
      if individual.props.has p then value := individual.props.get p
  if let some v := value then return v
  if let some v := (← getGraph graph).props.get p then return v
  match p.default with
  | some d => return d
  | none => throw (unspecifiedSpacing)

/-- Width of a row of comment boxes (with spacings) and the extra margin it needs (`0` for no boxes). -/
def rowMetrics (boxes : Array LNodeId) (commentCommentSpacing commentNodeSpacing : Float) :
    LayeredM (Float × Float) := do
  let mut width := 0.0
  let mut extraMargin := 0.0
  if !boxes.isEmpty then
    let mut maxHeight := 0.0
    for b in boxes do
      let size := (← getNode b).size
      maxHeight := fmax maxHeight size.y
      width := width + size.x
    width := width + commentCommentSpacing * (boxes.size - 1).toFloat
    extraMargin := maxHeight + commentNodeSpacing
  return (width, extraMargin)

/-- `processComments(node)`. -/
def processComments (graph : LGraphId) (node : LNodeId) : LayeredM Unit := do
  let nd ← getNode node
  let topBoxes := nd.internal.topComments
  let bottomBoxes := nd.internal.bottomComments
  let nodeWidth := nd.size.x
  if topBoxes.isEmpty && bottomBoxes.isEmpty then return
  let commentCommentSpacing ← individualOrDefaultWithGraph graph node LayeredOptions.SPACING_COMMENT_COMMENT
  let commentNodeSpacing ← individualOrDefaultWithGraph graph node LayeredOptions.SPACING_COMMENT_NODE
  let (topWidth, topExtraMargin) ← rowMetrics topBoxes commentCommentSpacing commentNodeSpacing
  let (bottomWidth, bottomExtraMargin) ← rowMetrics bottomBoxes commentCommentSpacing commentNodeSpacing
  modifyNode node fun n =>
    let m := n.margin
    let m := { m with top := m.top + topExtraMargin, bottom := m.bottom + bottomExtraMargin }
    let maxCommentWidth := fmax topWidth bottomWidth
    let m := if maxCommentWidth > nodeWidth then
        let protrusion := (maxCommentWidth - nodeWidth) / fl2p0
        { m with left := fmax m.left protrusion, right := fmax m.right protrusion }
      else m
    { n with margin := m }

/-- `process(layeredGraph, monitor)` body: all nodes in layer order. -/
def run (graph : LGraphId) : LayeredM Unit := do
  for layer in (← getGraph graph).layers do
    for node in (← getLayer layer).nodes do
      processComments graph node

/-- The `CommentNodeMarginCalculator` processor. -/
def processor : LayeredProcessor :=
  { name := "CommentNodeMarginCalculator"
    process := fun graph monitor => do
      let _ ← monitor.begin "Node margin calculation" 1.0
      run graph
      monitor.done }

end CommentNodeMarginCalculator

builtin_initialize registerCommentNodeMarginCalculator : Unit ←
  IntermediateProcessorStrategy.register .commentNodeMarginCalculator CommentNodeMarginCalculator.processor

end Elk.Alg.Layered.Intermediate
