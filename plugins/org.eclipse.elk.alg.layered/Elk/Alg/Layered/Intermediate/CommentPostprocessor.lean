import Elk.Alg.Layered.LayeredPhases
import Elk.Alg.Layered.Graph.LGraphUtil
/-!
# `org.eclipse.elk.alg.layered.intermediate.CommentPostprocessor`

Port of elk-rs `intermediate/comment_postprocessor.rs`. After node placement, the comment boxes attached
by `CommentPreprocessor` are placed centred above (`TOP_COMMENTS`) or below (`BOTTOM_COMMENTS`) their node,
`SPACING_COMMENT_COMMENT` apart, aligned to the node margin; each box edge is reconnected to the
remembered `COMMENT_CONN_PORT`, which is re-attached to the node (when it has exactly one edge) at evenly
distributed x positions on the node's top/bottom border. The boxes are appended to the node list of the
node's layer **without** setting their `layer` (Java `layer.getNodes().addAll(...)`, elk-rs
`nodes_mut().extend`).

The comment spacing is the node's individual `SPACING_COMMENT_COMMENT`, else the graph's (`10.0` when the
graph does not set it). Rust's compound assignments `x += a + b` are reproduced as `x + (a + b)`.
-/
/-! Float literals as global constants (FL): inside branches, loops and specialised code the compiler
shares a literal's `Nat`/`Bool` arguments with unrelated variables (CSE) and then parses it on every
evaluation (`FastFloat.ofScientificImpl`); a top-level constant is a load (PLAN §7.1 items 17, 22). -/
private def fl0p0 : Float := 0.0
private def fl2p0 : Float := 2.0

namespace Elk.Alg.Layered.Intermediate

open Elk.Graph Elk.Core Elk.Core.Alg Elk.Core.Options Elk.Core.Util Elk.Core.Math Elk.Alg.Layered
  Elk.Alg.Layered.Graph Elk.Alg.Layered.Options LayeredM

namespace CommentPostprocessor

/-- Rust `spacing_comment_comment(node, graphCommentSpacing)`. -/
def spacingCommentComment (node : LNodeId) (graphCommentSpacing : Float) : LayeredM Float := do
  let props := (← getNode node).props
  if props.has CoreOptions.SPACING_INDIVIDUAL then
    if let some individual := props.get CoreOptions.SPACING_INDIVIDUAL then
      if individual.props.has LayeredOptions.SPACING_COMMENT_COMMENT then
        if let some value := individual.props.get LayeredOptions.SPACING_COMMENT_COMMENT then
          return value
  return graphCommentSpacing

/-- `getBoxPort(commentBox)`: reconnects the first edge of the box (first port with an outgoing edge →
new target, else with an incoming edge → new source) to `COMMENT_CONN_PORT` and returns that box port. -/
def getBoxPort (commentBox : LNodeId) : LayeredM (Option LPortId) := do
  let some nodePort := (← getNode commentBox).internal.commentConnPort | return none
  for port in (← getNode commentBox).ports do
    if let some edge := (← getPort port).outgoingEdges[0]? then
      setEdgeTarget edge (some nodePort)
      return some port
    if let some edge := (← getPort port).incomingEdges[0]? then
      setEdgeSource edge (some nodePort)
      return some port
  return none

/-- Total width (sizes plus spacings) and maximal height of a row of comment boxes. -/
def rowExtent (boxes : Array LNodeId) (spacing : Float) : LayeredM (Float × Float) := do
  let mut boxesWidth := spacing * (boxes.size - 1).toFloat
  let mut maxHeight := 0.0
  for b in boxes do
    let size := (← getNode b).size
    boxesWidth := boxesWidth + size.x
    maxHeight := fmax maxHeight size.y
  return (boxesWidth, maxHeight)

/-- Places one row of comment boxes (`top`: above the node) and reattaches their connection ports. -/
def placeRow (node : LNodeId) (boxes : Array LNodeId) (top : Bool) (spacing : Float) : LayeredM Unit := do
  let nd ← getNode node
  let nodeX := nd.position.x
  let nodeY := nd.position.y
  let nodeW := nd.size.x
  let nodeH := nd.size.y
  let (boxesWidth, maxHeight) ← rowExtent boxes spacing
  let mut x := nodeX - (boxesWidth - nodeW) / fl2p0
  let baseLine := if top then nodeY - nd.margin.top + maxHeight else nodeY + nodeH + nd.margin.bottom - maxHeight
  let anchorInc := nodeW / (boxes.size + 1).toFloat
  let mut anchorX := anchorInc
  for boxNode in boxes do
    let boxX := x
    modifyNode boxNode fun b =>
      { b with position := ⟨boxX, if top then baseLine - b.size.y else baseLine⟩ }
    x := x + ((← getNode boxNode).size.x + spacing)
    if let some boxPort ← getBoxPort boxNode then
      let boxSize := (← getNode boxNode).size
      modifyPort boxPort fun p => { p with position := ⟨boxSize.x / fl2p0 - p.anchor.x, if top then boxSize.y else fl0p0⟩ }
    if let some nodePort := (← getNode boxNode).internal.commentConnPort then
      if (← getPort nodePort).degree == 1 then
        let ax := anchorX
        modifyPort nodePort fun p => { p with position := ⟨ax - p.anchor.x, if top then fl0p0 else nodeH⟩ }
        setPortNode nodePort (some node)
    anchorX := anchorX + anchorInc

/-- `processNode(node, topBoxes, bottomBoxes)`. -/
def processNode (node : LNodeId) (topBoxes bottomBoxes : Array LNodeId) (graphCommentSpacing : Float) :
    LayeredM Unit := do
  let spacing ← spacingCommentComment node graphCommentSpacing
  if !topBoxes.isEmpty then placeRow node topBoxes true spacing
  if !bottomBoxes.isEmpty then placeRow node bottomBoxes false spacing

/-- `process(layeredGraph, monitor)` body. -/
def run (graph : LGraphId) : LayeredM Unit := do
  let gr ← getGraph graph
  let graphCommentSpacing := if gr.props.has LayeredOptions.SPACING_COMMENT_COMMENT then
      gr.props.getD LayeredOptions.SPACING_COMMENT_COMMENT 10.0
    else 10.0
  for layer in gr.layers do
    let mut commentBoxes : Array LNodeId := #[]
    for node in (← getLayer layer).nodes do
      let nd ← getNode node
      let topBoxes := nd.internal.topComments
      let bottomBoxes := nd.internal.bottomComments
      if topBoxes.isEmpty && bottomBoxes.isEmpty then continue
      processNode node topBoxes bottomBoxes graphCommentSpacing
      commentBoxes := commentBoxes ++ topBoxes ++ bottomBoxes
    let boxes := commentBoxes
    modifyLayer layer fun l => { l with nodes := l.nodes ++ boxes }

/-- The `CommentPostprocessor` processor. -/
def processor : LayeredProcessor :=
  { name := "CommentPostprocessor"
    process := fun graph monitor => do
      let _ ← monitor.begin "Comment post-processing" 1.0
      run graph
      monitor.done }

end CommentPostprocessor

builtin_initialize registerCommentPostprocessor : Unit ←
  IntermediateProcessorStrategy.register .commentPostprocessor CommentPostprocessor.processor

end Elk.Alg.Layered.Intermediate
