import Elk.Alg.Layered.Graph.LGraphUtil
import Elk.Core.Util.FloatConst
open Elk.Core.Util.FloatConst
/-!
# `org.eclipse.elk.alg.layered.intermediate.wrapping.CuttingUtils`

Port of elk-rs `CuttingUtils` (`intermediate/single_edge_graph_wrapper.rs`): inserts in-layer
dummies and long edge dummies for an edge that was reversed by a wrapping step.

Let `originalEdge = e = (u, v)`. Dummies are created for every layer from `L(u)` to `L(v)`
(inclusive), i.e. two in-layer dummies `il_1 ∈ L(u)`, `il_2 ∈ L(v)` and long edge dummies in
between:

```
                              v
                              ^
il_1 -> d_1 -> ... -> d_m -> il_2
 ^
 u
```

Follows Java (agent COV): a negative insertion index for the first dummy throws Java's
`IllegalArgumentException` of `LNode.setLayer(int, Layer)` (elk-rs saturated it at `0`); it cannot
occur in the pipeline (the offset is `1` in `SingleEdgeGraphWrapper` and the number of nodes just
moved into the source layer in `BreakingPointProcessor`). The elk-rs guards for a missing end node or
layer (no edges; layer indexes `0`/the source index) are unreachable: the reversed edge connects two
layered nodes.

Each dummy edge copies all properties of the current edge (Rust `copy_properties` into the empty
map of the new edge = the public `props` and the typed `internal` values) except `JUNCTION_POINTS`.
-/

namespace Elk.Alg.Layered.Intermediate.Wrapping

open Elk.Graph Elk.Core Elk.Core.Math Elk.Core.Options Elk.Core.Util Elk.Alg.Layered.Graph
  Elk.Alg.Layered.Options LayeredM

namespace CuttingUtils

/-- `setDummyProperties(dummy, inEdge, outEdge)` (copied from `LongEdgeSplitter`): the
`LONG_EDGE_SOURCE`/`LONG_EDGE_TARGET` of a preceding long edge dummy, else the input edge's source
port and the output edge's target port. -/
def setDummyProperties (dummy : LNodeId) (inEdge outEdge : LEdgeId) : LayeredM Unit := do
  let inEdgeSource := (← getEdge inEdge).source
  let outEdgeTarget := (← getEdge outEdge).target
  let inEdgeSourceNode ← match inEdgeSource with
    | some p => pure (← getPort p).owner
    | none => pure none
  if let some srcNode := inEdgeSourceNode then
    let src ← getNode srcNode
    if src.type == .longEdge then
      modifyNode dummy fun d => { d with internal := { d.internal with
        longEdgeSource := src.internal.longEdgeSource, longEdgeTarget := src.internal.longEdgeTarget } }
      return
  modifyNode dummy fun d => { d with internal := { d.internal with
    longEdgeSource := inEdgeSource, longEdgeTarget := outEdgeTarget } }

/-- Creates the two ports of a dummy (`WEST` input, `EAST` output, both at `y = portPos`). -/
private def createDummyPorts (dummyNode : LNodeId) (portPos : Float) : LayeredM (LPortId × LPortId) := do
  let dummyInput ← createPort
  modifyPort dummyInput fun p =>
    let p := p.setSide .west
    { p with position := { p.position with y := portPos } }
  setPortNode dummyInput (some dummyNode)
  let dummyOutput ← createPort
  modifyPort dummyOutput fun p =>
    let p := p.setSide .east
    { p with position := { p.position with y := portPos } }
  setPortNode dummyOutput (some dummyNode)
  return (dummyInput, dummyOutput)

/-- `insertDummies(layeredGraph, originalEdge, offsetFirstInLayerDummy)`: returns the created
edges in chain order. All dummies are appended to their layers except the first one, which is
inserted `offsetFirstInLayerDummy` positions before the end of its layer. -/
def insertDummies (graph : LGraphId) (originalEdge : LEdgeId) (offsetFirstInLayerDummy : Nat) :
    LayeredM (Array LEdgeId) := do
  let gr ← getGraph graph
  let edgeNodeSpacing := (gr.props.get LayeredOptions.SPACING_EDGE_NODE).getD fl0p0
  let additionalSpacing := (gr.props.get LayeredOptions.WRAPPING_ADDITIONAL_EDGE_SPACING).getD fl0p0
  let individualSpacings : IndividualSpacings :=
    { props := PropertyMap.empty.set LayeredOptions.SPACING_EDGE_NODE (edgeNodeSpacing + additionalSpacing) }
  let mut edge := originalEdge
  let targetPort := (← getEdge edge).target
  let sourceNode ← match (← getEdge edge).source with
    | some p => pure (← getPort p).owner
    | none => pure none
  let targetNode ← match targetPort with
    | some p => pure (← getPort p).owner
    | none => pure none
  let (some sourceNode, some targetNode) := (sourceNode, targetNode) | return #[]
  let (some sourceLayer, some targetLayer) := ((← getNode sourceNode).layer, (← getNode targetNode).layer)
    | return #[]
  let layers := gr.layers
  let srcIndex := (layers.findIdx? (· == sourceLayer)).getD 0
  let tgtIndex := (layers.findIdx? (· == targetLayer)).getD srcIndex
  let mut createdEdges : Array LEdgeId := #[]
  for layerIndex in [srcIndex:tgtIndex + 1] do
    let dummyNode ← createNode graph
    modifyNode dummyNode fun d => { d with
      type := .longEdge,
      internal := { d.internal with origin := some (.lEdge edge) },
      props := (d.props.set LayeredOptions.PORT_CONSTRAINTS PortConstraints.fixedPos).set
        LayeredOptions.SPACING_INDIVIDUAL individualSpacings }
    let some nextLayer := layers[layerIndex]? | break
    if layerIndex == srcIndex then
      let size := (← getLayer nextLayer).nodes.size
      -- Java `dummyNode.setLayer(size - offset, layer)`: a negative index throws
      if size < offsetFirstInLayerDummy then
        throwIllegalArgument "index must be >= 0 and <= layer node count"
      setNodeLayerAtIndex dummyNode (size - offsetFirstInLayerDummy) (some nextLayer)
    else
      setNodeLayer dummyNode (some nextLayer)
    let mut thickness := ((← getEdge edge).props.get CoreOptions.EDGE_THICKNESS).getD fl1p0
    if thickness < fl0p0 then
      thickness := fl0p0
      setEdgeProp edge CoreOptions.EDGE_THICKNESS fl0p0
    let height := thickness
    modifyNode dummyNode fun d => { d with size := { d.size with y := height } }
    let portPos := Float.floor (thickness / fl2p0)
    let (dummyInput, dummyOutput) ← createDummyPorts dummyNode portPos
    setEdgeTarget edge (some dummyInput)
    let old ← getEdge edge
    let dummyEdge ← createEdge { props := old.props.remove LayeredOptions.JUNCTION_POINTS, internal := old.internal }
    setEdgeSource dummyEdge (some dummyOutput)
    if let some tp := targetPort then
      setEdgeTarget dummyEdge (some tp)
    setDummyProperties dummyNode edge dummyEdge
    createdEdges := createdEdges.push dummyEdge
    edge := dummyEdge
  return createdEdges

end CuttingUtils

end Elk.Alg.Layered.Intermediate.Wrapping
