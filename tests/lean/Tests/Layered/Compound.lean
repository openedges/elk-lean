import Tests.Framework
import Elk.Alg.Layered
import Elk.Alg.Layered.Compound
/-! Tests of `org.eclipse.elk.alg.layered.compound`: the cross-hierarchy map, the segment
comparator and a preprocessing + postprocessing round trip on a two-level graph. -/
namespace Tests.Layered.Compound

open Tests Elk Elk.Graph Elk.Core.Math Elk.Core.Options Elk.Core.Util Elk.Alg.Layered Elk.Alg.Layered.Graph
open Elk.Alg.Layered.Options Elk.Alg.Layered.Compound

def mkPort (n : LNodeId) (p : LPort := {}) : LayeredM LPortId := do
  let id ← LayeredM.createPort p
  LayeredM.setPortNode id (some n)
  return id

def mapTests : Suite := suite "layered.compound.crossHierarchyMap" do
  let e0 : LEdgeId := ⟨0⟩
  let e1 : LEdgeId := ⟨1⟩
  let c (i : Nat) (t : PortType) : CrossHierarchyEdge := { edge := ⟨10 + i⟩, graph := ⟨i⟩, portType := t }
  let m : CrossHierarchyMap := #[]
  let m := CrossHierarchyMap.put m e1 (c 0 .output)
  let m := CrossHierarchyMap.put m e0 (c 1 .input)
  let m := CrossHierarchyMap.put m e1 (c 2 .input)
  checkEq "keys in first-put order" (CrossHierarchyMap.keys m) #[e1, e0]
  checkEq "values in put order" ((CrossHierarchyMap.get m e1).map (·.edge)) #[⟨10⟩, ⟨12⟩]
  checkEq "unknown key" (CrossHierarchyMap.get m ⟨5⟩).size 0
  -- hand: [OUT, OUT, IN, IN] → last OUTPUT before the first INPUT
  checkEq "shallowest segment [O, O, I, I]"
    (CompoundGraphPreprocessor.getShallowestEdgeSegment #[c 0 .output, c 1 .output, c 2 .input, c 3 .input]) 1
  checkEq "shallowest segment [I]" (CompoundGraphPreprocessor.getShallowestEdgeSegment #[c 0 .input]) 0
  checkEq "shallowest segment [O, O]" (CompoundGraphPreprocessor.getShallowestEdgeSegment #[c 0 .output, c 1 .output]) 1

def comparatorTests : Suite := suite "layered.compound.comparator" do
  let ((g0, g1, g2, sorted, levels), _) ← LayeredM.run (do
    let g0 ← LayeredM.createGraph
    let c ← LayeredM.createNode g0
    let g1 ← LayeredM.createGraph { parentNode := some c }
    LayeredM.modifyNode c fun x => { x with nestedGraph := some g1 }
    let c2 ← LayeredM.createNode g1
    let g2 ← LayeredM.createGraph { parentNode := some c2 }
    let other ← LayeredM.createGraph
    let mk (g : LGraphId) (t : PortType) : CrossHierarchyEdge := { edge := ⟨0⟩, graph := g, portType := t }
    let sorted ← CrossHierarchyEdgeComparator.sortCrossHierarchyEdges
      #[mk g1 .input, mk g0 .input, mk g2 .output, mk g1 .output, mk g2 .input, mk g0 .output] g0
    let levels ← #[g0, g1, g2, other].mapM (CrossHierarchyEdgeComparator.hierarchyLevel · g0)
    return (g0, g1, g2, sorted, levels))
  -- hand: OUTPUT first from deep to shallow (g2, g1, g0), then INPUT from shallow to deep (g0, g1, g2)
  checkEq "segments sorted from start to end" (sorted.map fun e => (e.graph, e.portType == .output))
    #[(g2, true), (g1, true), (g0, true), (g0, false), (g1, false), (g2, false)]
  checkEq "hierarchy levels (unrelated graph: none)" levels #[some 0, some 1, some 2, none]

/-- The two-level sample: top graph `G0` with the compound node `C` (nested graph `G1` holding
`M`) and the node `N`; the cross-hierarchy edge `E: pm (on M) → pn (on N)` with a centre label. -/
structure Sample where
  g0 : LGraphId
  g1 : LGraphId
  c : LNodeId
  n : LNodeId
  m : LNodeId
  pm : LPortId
  pn : LPortId
  e : LEdgeId
  label : LLabelId

def buildSample : LayeredM Sample := do
  let g0 ← LayeredM.createGraph
  let c ← LayeredM.createNode g0 { size := ⟨100.0, 80.0⟩ }
  let n ← LayeredM.createNode g0 { size := ⟨20.0, 20.0⟩ }
  LayeredM.modifyGraph g0 fun g => { g with layerlessNodes := #[c, n] }
  let g1 ← LayeredM.createGraph { parentNode := some c, padding := ⟨6.0, 0.0, 0.0, 5.0⟩ }
  LayeredM.modifyNode c fun x => { x with nestedGraph := some g1 }
  let m ← LayeredM.createNode g1 { size := ⟨20.0, 20.0⟩ }
  LayeredM.modifyGraph g1 fun g => { g with layerlessNodes := #[m] }
  let pm ← mkPort m { side := .east }
  let pn ← mkPort n { side := .west }
  let e ← LayeredM.createEdge
  LayeredM.setEdgeSource e (some pm)
  LayeredM.setEdgeTarget e (some pn)
  let label ← LayeredM.createLabel "E"
  LayeredM.modifyEdge e fun x => { x with labels := #[label] }
  return { g0, g1, c, n, m, pm, pn, e, label }

def roundTripTests : Suite := suite "layered.compound.roundTrip" do
  let ((s, pre), afterPre) ← LayeredM.run (do
    let s ← buildSample
    CompoundGraphPreprocessor.processor.process s.g0 ProgressMonitor.null
    return (s, ← LayeredM.getGraph s.g0))
  let a := afterPre
  let map := pre.internal.crossHierarchyMap
  let segments := CrossHierarchyMap.get map s.e
  checkEq "cross-hierarchy map has the original edge" (CrossHierarchyMap.keys map) #[s.e]
  -- hand: G1 introduces the OUTPUT segment pm → dummy, G0 connects the compound port to pn
  checkEq "two segments (inner first)" (segments.map fun x => (x.graph, x.portType == .output))
    #[(s.g1, true), (s.g0, true)]
  let x1 := segments[0]!.edge
  let x2 := segments[1]!.edge
  checkEq "original edge disconnected" ((a.edge s.e).source, (a.edge s.e).target) (none, none)
  checkEq "pm now only has the inner segment" (a.port s.pm).outgoingEdges #[x1]
  checkEq "pn now only has the outer segment" (a.port s.pn).incomingEdges #[x2]
  let g1Nodes := (a.graph s.g1).layerlessNodes
  checkEq "external port dummy added to G1" g1Nodes.size 2
  let d := g1Nodes[1]!
  checkEq "dummy is an external port dummy" (a.node d).type NodeType.externalPort
  -- hand: no port constraints, net flow +1, direction RIGHT → EAST
  checkEq "dummy on the EAST side" (a.node d).internal.extPortSide PortSide.east
  checkEq "compound node got one port" (a.node s.c).ports.size 1
  let pc := (a.node s.c).ports[0]!
  check "dummy origin is the compound port" ((a.node d).internal.origin == some (.lPort pc))
  checkEq "compound port on the EAST side" (a.port pc).side PortSide.east
  checkEq "compound port knows its dummy" (a.port pc).internal.portDummy (some d)
  check "compound port has inside connections" (a.port pc).internal.insideConnections
  -- hand: SPACING_EDGE_EDGE default 10 / 2
  checkFloat "compound port border offset" ((a.port pc).props.getD CoreOptions.PORT_BORDER_OFFSET 0.0) 5.0
  checkEq "inner segment ends at the dummy port" ((a.edge x1).source, (a.edge x1).target)
    (some s.pm, (a.node d).ports[0]?)
  checkEq "outer segment starts at the compound port" ((a.edge x2).source, (a.edge x2).target) (some pc, some s.pn)
  check "segment origin is the original edge" ((a.edge x1).internal.origin == some (.lEdge s.e))
  -- hand: centre label → shallowest segment = index 1 (the G0 segment)
  checkEq "label moved to the outer segment" (a.edge x2).labels #[s.label]
  checkEq "label remembers its original edge" (a.label s.label).internal.originalLabelEdge (some s.e)
  check "G1 has external ports" ((a.graph s.g1).internal.graphProperties.contains .externalPorts)
  checkEq "G1 port constraints FREE" ((a.graph s.g1).props.getD CoreOptions.PORT_CONSTRAINTS .undefined) .free
  check "G0 has centre and end labels" ((a.graph s.g0).internal.graphProperties.containsAll
    (EnumSet.of #[.centerLabels, .endLabels, .nonFreePorts]))
  checkEq "compound node port constraints FIXED_SIDE"
    ((a.node s.c).props.getD CoreOptions.PORT_CONSTRAINTS .undefined) .fixedSide
  -- "layout": hand-set coordinates
  let (_, post) ← LayeredM.run (do
    LayeredM.modifyNode s.c fun x => { x with position := ⟨10.0, 20.0⟩ }
    LayeredM.modifyNode s.n fun x => { x with position := ⟨200.0, 50.0⟩ }
    LayeredM.modifyPort s.pn fun x => { x with position := ⟨0.0, 5.0⟩, anchor := ⟨0.0, 0.0⟩ }
    LayeredM.modifyPort pc fun x => { x with position := ⟨100.0, 30.0⟩, anchor := ⟨0.0, 0.0⟩ }
    LayeredM.modifyNode s.m fun x => { x with position := ⟨10.0, 10.0⟩ }
    LayeredM.modifyPort s.pm fun x => { x with position := ⟨20.0, 5.0⟩, anchor := ⟨0.0, 0.0⟩ }
    LayeredM.modifyNode d fun x => { x with position := ⟨90.0, 30.0⟩ }
    LayeredM.modifyEdge x1 fun x => { x with bendPoints := #[⟨50.0, 15.0⟩, ⟨50.0, 30.0⟩] }
    LayeredM.setEdgeProp x1 CoreOptions.JUNCTION_POINTS #[⟨50.0, 30.0⟩]
    LayeredM.modifyEdge x2 fun x => { x with bendPoints := #[⟨150.0, 50.0⟩] }
    LayeredM.modifyLabel s.label fun x => { x with position := ⟨120.0, 40.0⟩ }
    CompoundGraphPostprocessor.processor.process s.g0 ProgressMonitor.null) a
  -- hand: reference graph = G1 (M's graph); offset of G0 in G1 = -(padding (5, 6) + C (10, 20))
  -- = (-15, -26); X1 bends as is; X2: source (110, 50) → (95, 24) added (both coordinates
  -- differ from the last point (50, 30)), bend (150, 50) → (135, 24)
  checkEq "original edge reconnected" ((post.edge s.e).source, (post.edge s.e).target) (some s.pm, some s.pn)
  checkEq "pm has the original edge again" (post.port s.pm).outgoingEdges #[s.e]
  checkEq "pn has the original edge again" (post.port s.pn).incomingEdges #[s.e]
  checkEqR "bend points restored in the reference graph"
    (post.edge s.e).bendPoints #[⟨50.0, 15.0⟩, ⟨50.0, 30.0⟩, ⟨95.0, 24.0⟩, ⟨135.0, 24.0⟩]
  checkEqR "junction points restored" ((post.edge s.e).props.getD CoreOptions.JUNCTION_POINTS #[]) #[⟨50.0, 30.0⟩]
  checkEqR "target offset (-15, -26)" (post.edge s.e).internal.targetOffset (some ⟨-15.0, -26.0⟩)
  checkEq "label moved back" (post.edge s.e).labels #[s.label]
  checkEq "outer segment has no label left" (post.edge x2).labels #[]
  checkEqR "label position converted to G1" (post.label s.label).position ⟨105.0, 14.0⟩
  checkEq "inner segment disconnected" ((post.edge x1).source, (post.edge x1).target) (none, none)
  checkEq "outer segment disconnected" ((post.edge x2).source, (post.edge x2).target) (none, none)
  checkEq "compound port has no edges left" (post.port pc).connectedEdges #[]

/-- Two cross-hierarchy edges leaving the same port of `M` are merged into one external port
(`MERGE_HIERARCHY_EDGES` default `true`); an edge entering `M` creates an INPUT segment pair. -/
def mergeTests : Suite := suite "layered.compound.merge" do
  let ((s, n2, e2, eIn), a) ← LayeredM.run (do
    let s ← buildSample
    let n2 ← LayeredM.createNode s.g0
    LayeredM.modifyGraph s.g0 fun g => { g with layerlessNodes := g.layerlessNodes.push n2 }
    let p2 ← mkPort n2 { side := .west }
    let e2 ← LayeredM.createEdge
    LayeredM.setEdgeSource e2 (some s.pm)
    LayeredM.setEdgeTarget e2 (some p2)
    LayeredM.setEdgeProp e2 CoreOptions.EDGE_THICKNESS 3.0
    let pIn ← mkPort s.m { side := .west }
    let pOut ← mkPort n2 { side := .east }
    let eIn ← LayeredM.createEdge
    LayeredM.setEdgeSource eIn (some pOut)
    LayeredM.setEdgeTarget eIn (some pIn)
    CompoundGraphPreprocessor.processor.process s.g0 ProgressMonitor.null
    return (s, n2, e2, eIn))
  let _ := n2
  let map := (a.graph s.g0).internal.crossHierarchyMap
  checkEq "three original edges in the map (inner level first)" (CrossHierarchyMap.keys map) #[s.e, e2, eIn]
  let seg1 := CrossHierarchyMap.get map s.e
  let seg2 := CrossHierarchyMap.get map e2
  checkEq "merged edge shares the inner segment" (seg2[0]?.map (·.edge)) (seg1[0]?.map (·.edge))
  checkEq "merged edge has its own outer segment" (seg2.size, seg2[1]?.map (·.graph)) (2, some s.g0)
  -- hand: thickness of the shared segment = max(1, 3)
  checkFloat "shared segment thickness" ((a.edge seg1[0]!.edge).props.getD CoreOptions.EDGE_THICKNESS 0.0) 3.0
  -- hand: one OUTPUT dummy (merged) and one INPUT dummy (net flow -1 → WEST)
  checkEq "two external port dummies in G1" (a.graph s.g1).layerlessNodes.size 3
  checkEq "compound node has two ports" (a.node s.c).ports.size 2
  let segIn := CrossHierarchyMap.get map eIn
  checkEq "input edge segments (inner INPUT recorded first)"
    (segIn.map fun x => (x.graph, x.portType == .input)) #[(s.g1, true), (s.g0, true)]
  let inDummy := (a.graph s.g1).layerlessNodes[2]!
  checkEq "input dummy on the WEST side" (a.node inDummy).internal.extPortSide PortSide.west

def suites : Array Suite := #[mapTests, comparatorTests, roundTripTests, mergeTests]

end Tests.Layered.Compound
