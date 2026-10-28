import Elk.Core.Alg
import Elk.Core.LayoutProvider
import Elk.Core.Options
import Elk.Core.Exceptions
import Elk.Core.Util.Java
import Elk.Alg.Common.NodeSpacing.NodeMicroLayout
import Elk.Alg.VertiFlex.VertiFlexLayoutPhases
import Elk.Alg.VertiFlex.VertiFlexUtil
import Elk.Alg.VertiFlex.EdgeRoutingStrategy
import Elk.Alg.VertiFlex.Options.VertiFlexOptions
import Elk.Alg.VertiFlex.P1YPlacement.NodeYPlacerStrategy
import Elk.Alg.VertiFlex.P2Relative.RelativeXPlacerStrategy
import Elk.Alg.VertiFlex.P3Absolute.AbsoluteXPlacerStrategy
import Elk.Alg.VertiFlex.P4EdgeRouting.EdgerouterStrategy
/-!
# `org.eclipse.elk.alg.vertiflex.VertiFlexLayoutProvider`

Port of `vertiflex_layout_provider.rs` (elk-rs): assembles the four phases (the edge routing
phase is chosen by the `LAYOUT_STRATEGY` option), checks that the graph is a tree and that the
vertical constraints are consistent, runs the phases and sets the graph size.

Rust reports the three failures with `panic!("{}", UnsupportedConfigurationException::new(..))`;
they are thrown as `org.eclipse.elk.core.UnsupportedConfigurationException` here.
-/
/-! Float literals as global constants (FL): inside branches, loops and specialised code the compiler
shares a literal's `Nat`/`Bool` arguments with unrelated variables (CSE) and then parses it on every
evaluation (`FastFloat.ofScientificImpl`); a top-level constant is a load (PLAN §7.1 items 17, 22). -/
private def fl0p0 : Float := 0.0
private def fl1p0 : Float := 1.0

namespace Elk.Alg.VertiFlex

open Elk.Graph Elk.Core Elk.Core.Alg Elk.Core.Util Elk.Core.Options Elk.Alg.Common.NodeSpacing
open Elk.Alg.VertiFlex.Options Elk.Alg.VertiFlex.P1YPlacement Elk.Alg.VertiFlex.P2Relative
open Elk.Alg.VertiFlex.P3Absolute Elk.Alg.VertiFlex.P4EdgeRouting

namespace VertiFlexLayoutProvider

/-- `assemble_algorithm(graph)`: the processor list (the four phases in order). -/
def assembleAlgorithm (graph : NodeId) : VertiFlexM (Array (LayoutProcessor VertiFlexM NodeId)) := do
  let assembler : AlgorithmAssembler VertiFlexM VertiFlexLayoutPhases NodeId VertiFlexProcessors ←
    AlgorithmAssembler.create (fun _ =>
      throw (IO.userError "java.lang.UnsupportedOperationException: vertiflex has no intermediate processors"))
  let routingStrategy : EdgerouterStrategy :=
    match (← ElkM.getNode graph).props.getD VertiFlexOptions.LAYOUT_STRATEGY default with
    | .bend => .bendRouting
    | .straight => .directRouting
  assembler.setPhase .p1NodeYPlacement NodeYPlacerStrategy.simpleYPlacing.phaseFactory
  assembler.setPhase .p2NodeRelativePlacement RelativeXPlacerStrategy.simpleXPlacing.phaseFactory
  assembler.setPhase .p3NodeAbsolutePlacement AbsoluteXPlacerStrategy.absoluteXPlacing.phaseFactory
  assembler.setPhase .p4EdgeRouting routingStrategy.phaseFactory
  assembler.build graph

/-- `check_vertical_constraint_validity(root, current_min_constraint, node_node_spacing)`: every
node with a vertical constraint must lie below the bottom (plus margin / spacing) of its
ancestors. -/
partial def checkVerticalConstraintValidity (root : NodeId) (currentMinConstraint nodeNodeSpacing : Float) :
    ElkM Unit := do
  let node ← ElkM.getNode root
  let rootHeight := match node.props.get VertiFlexOptions.VERTICAL_CONSTRAINT with
    | some value => value
    | none => currentMinConstraint
  let margins := node.props.getD CoreOptions.MARGINS {}
  let newMinConstraint := rootHeight + node.height + fmax margins.bottom nodeNodeSpacing
  let edges ← ElkM.withGraph fun g => ElkGraphUtil.allOutgoingEdges g root
  for edge in edges do
    let some child ← VertiFlexUtil.edgeTargetNode edge | continue
    let childNode ← ElkM.getNode child
    if childNode.props.has VertiFlexOptions.VERTICAL_CONSTRAINT then
      let childConstraint := (childNode.props.get VertiFlexOptions.VERTICAL_CONSTRAINT).getD fl0p0
      let childMargin := childNode.props.getD CoreOptions.MARGINS {}
      if newMinConstraint > childConstraint + childMargin.top then
        let identifier := childNode.identifier.getD "<unknown>"
        throwUnsupportedConfiguration
          s!"Invalid vertical constraints. Node {identifier} has a vertical constraint that is too low for its ancestors."
  for edge in edges do
    let some child ← VertiFlexUtil.edgeTargetNode edge | continue
    checkVerticalConstraintValidity child newMinConstraint nodeNodeSpacing

/-- `set_graph_size(graph)`: the size of the graph is the bounding box of the children (with
margins) plus the right / bottom padding. -/
def setGraphSize (graph : NodeId) : ElkM Unit := do
  let gNode ← ElkM.getNode graph
  let padding := gNode.props.getD CoreOptions.PADDING {}
  let mut maxX := 0.0
  let mut maxY := 0.0
  for child in gNode.children do
    let node ← ElkM.getNode child
    let margins := node.props.getD CoreOptions.MARGINS {}
    maxX := fmax maxX (node.x + node.width + margins.right)
    maxY := fmax maxY (node.y + node.height + margins.bottom)
  ElkM.modifyNode graph fun n => { n with width := maxX + padding.right, height := maxY + padding.bottom }

/-- `layout(layout_graph, progress_monitor)`. -/
def layout (layoutGraph : NodeId) (monitor : ProgressMonitor) : ElkM Unit := do
  let nodeCount ← ElkM.withGraph (·.nodeCount)
  let run : VertiFlexM Unit := do
    let algorithm ← assembleAlgorithm layoutGraph
    let _ ← monitor.begin "Tree layout" algorithm.size.toFloat
    let props := (← ElkM.getNode layoutGraph).props
    let nodeNodeSpacing := props.getD CoreOptions.SPACING_NODE_NODE fl0p0
    let omitMicro := props.getD VertiFlexOptions.OMIT_NODE_MICRO_LAYOUT false
    if !omitMicro then
      (← NodeMicroLayout.forGraph layoutGraph).execute
    let some root ← VertiFlexUtil.findRoot layoutGraph
      | throwUnsupportedConfiguration "The given graph is not a tree!"
    let children := (← ElkM.getNode layoutGraph).children
    for child in children do
      let numberOfParents ← ElkM.withGraph fun g => (ElkGraphUtil.allIncomingEdges g child).size
      if numberOfParents > 1 then
        throwUnsupportedConfiguration "The given graph is not an acyclic tree!"
      ElkM.modifyNode child fun n => { n with x := fl0p0, y := fl0p0 }
    checkVerticalConstraintValidity root fl0p0 nodeNodeSpacing
    let mut index : Int := 0
    for node in children do
      VertiFlexM.modifyProps node fun p => { p with nodeModelOrder := some index }
      index := index + 1
    for processor in algorithm do
      let sub ← monitor.subTask fl1p0
      processor.process layoutGraph sub
    setGraphSize layoutGraph
    monitor.done
  StateRefT'.run' run { nodes := Array.replicate nodeCount {} }

/-- The `org.eclipse.elk.vertiflex` layout provider. -/
def provider : LayoutProvider :=
  { id := VertiFlexOptions.ALGORITHM_ID
    layout := layout }

end VertiFlexLayoutProvider

end Elk.Alg.VertiFlex
