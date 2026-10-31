import Tests.Framework
import Elk.Alg.Layered
import Elk.Alg.Layered.Intermediate.HierarchicalPortProcessors
/-!
Tests of the hierarchical (external) port processors and the hierarchical node resizer
(`HierarchicalPortConstraintProcessor`, `HierarchicalPortDummySizeProcessor`,
`HierarchicalPortPositionProcessor`, `HierarchicalNodeResizingProcessor`,
`InteractiveExternalPortPositioner`). The elk-rs unit tests in
`hierarchical_port_position_processor.rs` and `interactive_external_port_positioner.rs` are ported
on hand-built graphs; the assertions of the pipeline-driven `compound_external_port_side_test.rs`
(external EAST port keeps its side and lies on or beyond the parent width) are checked on a
hand-built nested graph. All other expected values are derived by hand ("hand: …").
-/
namespace Tests.Layered.IntermediateHierarchicalPorts

open Tests Elk.Graph Elk.Core.Util Elk.Core.Alg Elk.Core.Math Elk.Core.Options Elk.Alg.Layered
  Elk.Alg.Layered.Graph Elk.Alg.Layered.Options Elk.Alg.Layered.Intermediate
open Elk (ElkEnum EnumSet)

/-- Runs a processor with a null monitor. -/
def runProc (p : LayeredProcessor) (g : LGraphId) : LayeredM Unit := p.process g ProgressMonitor.null

/-- Appends a new layer to the graph. -/
def addLayer (g : LGraphId) : LayeredM LayerId := do
  let l ← LayeredM.createLayer g
  LayeredM.modifyGraph g fun x => { x with layers := x.layers.push l }
  return l

/-- A node of graph `g`, put into `layer` when given. -/
def mkNode (g : LGraphId) (layer : Option LayerId := none) (n : LNode := {}) : LayeredM LNodeId := do
  let node ← LayeredM.createNode g n
  if layer.isSome then LayeredM.setNodeLayer node layer
  return node

/-- An external port dummy with `EXT_PORT_SIDE`, `PORT_RATIO_OR_POSITION` and `ORIGIN`. -/
def mkExt (g : LGraphId) (layer : Option LayerId) (side : PortSide) (ratio : Float := 0.0)
    (origin : Option Origin := none) (n : LNode := {}) : LayeredM LNodeId := do
  let d ← mkNode g layer { n with type := .externalPort }
  LayeredM.modifyNode d fun x => { x with internal := { x.internal with
    extPortSide := side, portRatioOrPosition := ratio, origin := origin } }
  return d

/-- A new port of `node`. -/
def mkPort (node : LNodeId) (p : LPort := {}) : LayeredM LPortId := do
  let port ← LayeredM.createPort p
  LayeredM.setPortNode port (some node)
  return port

/-- An edge between two existing ports. -/
def connectPorts (s t : LPortId) : LayeredM LEdgeId := do
  let e ← LayeredM.createEdge
  LayeredM.setEdgeSource e (some s)
  LayeredM.setEdgeTarget e (some t)
  return e

/-- An edge between fresh ports of `s` and `t` (Rust test helper `connect`). -/
def connect (s t : LNodeId) : LayeredM LEdgeId := do
  let sp ← mkPort s
  let tp ← mkPort t
  connectPorts sp tp

/-- Sets the graph's `PORT_CONSTRAINTS`. -/
def setConstraints (g : LGraphId) (pc : PortConstraints) : LayeredM Unit :=
  LayeredM.setGraphProp g CoreOptions.PORT_CONSTRAINTS pc

/-! ## HierarchicalPortConstraintProcessor -/

/-- Two layers: layer 0 `[n, w1 (W, 3), w2 (W, 1), north (N, 2)]`, layer 1 `[e1 (E, 5), m, e2 (E, 5)]`. -/
def eastWestGraph (pc : PortConstraints) : LayeredM (LGraphId × Array LNodeId) := do
  let g ← LayeredM.createGraph
  setConstraints g pc
  let l0 ← addLayer g
  let l1 ← addLayer g
  let n ← mkNode g l0
  let w1 ← mkExt g l0 .west 3.0
  let w2 ← mkExt g l0 .west 1.0
  let north ← mkExt g l0 .north 2.0 (some (.elkPort ⟨4⟩))
  let e1 ← mkExt g l1 .east 5.0
  let m ← mkNode g l1
  let e2 ← mkExt g l1 .east 5.0
  return (g, #[n, w1, w2, north, e1, m, e2])

def eastWestTests : Suite := suite "layered.intermediate.hierarchicalPortConstraints.eastWest" do
  let ((g, ns), a) ← LayeredM.run (do
    let r ← eastWestGraph .fixedOrder
    runProc HierarchicalPortConstraintProcessor.processor r.1
    return r)
  let succ (i : Nat) := (a.node ns[i]!).internal.inLayerSuccessorConstraints
  checkEq "hand: FIXED_ORDER west w2 (1.0) before w1 (3.0)" (succ 2) #[ns[1]!]
  checkEq "hand: last west dummy has no successor" (succ 1) #[]
  checkEq "hand: north dummy is skipped by the east/west chain" (succ 3) #[]
  checkEq "hand: equal positions keep the layer order (e1 → e2)" (succ 4) #[ns[6]!]
  checkEq "hand: normal nodes get no constraint" (succ 0 ++ succ 5) #[]
  checkEq "hand: unconnected north dummy removed from layer 0 (FIXED_ORDER is side-fixed)"
    (a.layer (a.graph g).layers[0]!).nodes #[ns[0]!, ns[1]!, ns[2]!]
  checkEq "hand: replaced dummies recorded" (a.graph g).internal.extPortReplacedDummies #[ns[3]!]
  let ((_, ns2), a2) ← LayeredM.run (do
    let r ← eastWestGraph .fixedRatio
    runProc HierarchicalPortConstraintProcessor.processor r.1
    return r)
  checkEq "hand: FIXED_RATIO also chains by ratio" (a2.node ns2[2]!).internal.inLayerSuccessorConstraints #[ns2[1]!]
  let ((g3, ns3), a3) ← LayeredM.run (do
    let r ← eastWestGraph .fixedSide
    runProc HierarchicalPortConstraintProcessor.processor r.1
    return r)
  check "hand: FIXED_SIDE is not order-fixed (no chain)"
    (ns3.all fun n => (a3.node n).internal.inLayerSuccessorConstraints.isEmpty)
  checkEq "hand: FIXED_SIDE still removes the north dummy" (a3.graph g3).internal.extPortReplacedDummies #[ns3[3]!]
  let ((g4, ns4), a4) ← LayeredM.run (do
    let r ← eastWestGraph .free
    runProc HierarchicalPortConstraintProcessor.processor r.1
    return r)
  check "hand: FREE changes nothing"
    (ns4.all fun n => (a4.node n).internal.inLayerSuccessorConstraints.isEmpty)
  checkEq "hand: FREE keeps the north dummy" (a4.layer (a4.graph g4).layers[0]!).nodes.size 4
  -- three layers: the middle layer is not processed
  let ((_, mid), a5) ← LayeredM.run (do
    let g ← LayeredM.createGraph
    setConstraints g .fixedPos
    let _ ← addLayer g
    let l1 ← addLayer g
    let _ ← addLayer g
    let x ← mkExt g l1 .west 2.0
    let y ← mkExt g l1 .west 1.0
    runProc HierarchicalPortConstraintProcessor.processor g
    return (g, #[x, y]))
  check "hand: middle layer dummies are not chained"
    (mid.all fun n => (a5.node n).internal.inLayerSuccessorConstraints.isEmpty)

/-- Layers `L0 = [a, nN]`, `L1 = [b, c, nS]` with `nS → a`, `a → nN`, `nN → b`, `nN → c`, `b → nS`
(`nN`: north dummy with an `ElkPort` origin, `nS`: south dummy with an `LPort` origin). -/
def northSouthGraph (pc : PortConstraints) : LayeredM (LGraphId × Array LNodeId × Array LEdgeId) := do
  let g ← LayeredM.createGraph
  setConstraints g pc
  let l0 ← addLayer g
  let l1 ← addLayer g
  let a ← mkNode g l0
  let nN ← mkExt g l0 .north 0.0 (some (.elkPort ⟨7⟩))
  LayeredM.modifyNode nN fun x => { x with
    props := x.props.set CoreOptions.PORT_BORDER_OFFSET 3.0
    internal := { x.internal with inLayerConstraint := .top } }
  let pN ← mkPort nN { side := .south }
  let b ← mkNode g l1
  let c ← mkNode g l1
  let nS ← mkExt g l1 .south 0.0 (some (.lPort ⟨99⟩))
  let pS ← mkPort nS { side := .north }
  let eSA ← connectPorts pS (← mkPort a)
  let eAN ← connectPorts (← mkPort a) pN
  let eNB ← connectPorts pN (← mkPort b)
  let eNC ← connectPorts pN (← mkPort c)
  let eBS ← connectPorts (← mkPort b) pS
  return (g, #[a, nN, b, c, nS], #[eSA, eAN, eNB, eNC, eBS])

def northSouthTests : Suite := suite "layered.intermediate.hierarchicalPortConstraints.northSouth" do
  let ((g, ns, es), a) ← LayeredM.run (do
    let r ← northSouthGraph .fixedSide
    runProc HierarchicalPortConstraintProcessor.processor r.1
    return r)
  let nA := ns[0]!; let nN := ns[1]!; let nB := ns[2]!; let nC := ns[3]!; let nS := ns[4]!
  let layers := (a.graph g).layers
  checkEq "hand: a new layer in front and one at the end" layers.size 4
  let lnodes (i : Nat) := (a.layer layers[i]!).nodes
  checkEq "hand: front layer holds one replacement" (lnodes 0).size 1
  checkEq "hand: end layer holds one replacement" (lnodes 3).size 1
  checkEq "hand: layer 0 = [a, r1]" (lnodes 1).size 2
  checkEq "hand: layer 1 = [b, c, r2]" (lnodes 2).size 3
  let r3 := (lnodes 0)[0]!
  let r1 := (lnodes 1)[1]!
  let r2 := (lnodes 2)[2]!
  let r4 := (lnodes 3)[0]!
  checkEq "hand: a and b, c keep their layers" #[(lnodes 1)[0]!, (lnodes 2)[0]!, (lnodes 2)[1]!] #[nA, nB, nC]
  check "hand: creation order r3 < r2 < r1 < r4 (a's incoming, a's outgoing, b's incoming, b's outgoing)"
    (r3.idx < r2.idx && r2.idx < r1.idx && r1.idx < r4.idx)
  let srcNode (e : LEdgeId) := ((a.edge e).source.bind fun p => (a.port p).owner)
  let tgtNode (e : LEdgeId) := ((a.edge e).target.bind fun p => (a.port p).owner)
  let outPort (n : LNodeId) := (a.node n).ports[HierarchicalPortConstraintProcessor.DUMMY_OUTPUT_PORT]?
  let inPort (n : LNodeId) := (a.node n).ports[HierarchicalPortConstraintProcessor.DUMMY_INPUT_PORT]?
  checkEq "hand: nS → a now starts at the front replacement's output port" (a.edge es[0]!).source (outPort r3)
  checkEq "hand: a → nN now ends at the layer-1 replacement's input port" (a.edge es[1]!).target (inPort r2)
  checkEq "hand: nN → b starts at the layer-0 replacement" (srcNode es[2]!) (some r1)
  checkEq "hand: nN → c reuses the same replacement (same origin, same layer)" (a.edge es[3]!).source (outPort r1)
  checkEq "hand: b → nS ends at the end replacement" (tgtNode es[4]!) (some r4)
  checkEq "hand: replaced dummies in layer order" (a.graph g).internal.extPortReplacedDummies #[nN, nS]
  checkEq "hand: original dummies have no layer" #[(a.node nN).layer, (a.node nS).layer] #[none, none]
  let rd := a.node r1
  checkEq "replacement: EXT_PORT_REPLACED_DUMMY" rd.internal.extPortReplacedDummy (some nN)
  check "replacement: type EXTERNAL_PORT" (rd.type == .externalPort)
  check "replacement: PORT_CONSTRAINTS FIXED_POS"
    (rd.props.getD CoreOptions.PORT_CONSTRAINTS .undefined == .fixedPos)
  check "replacement: ALIGNMENT CENTER" (rd.props.getD CoreOptions.ALIGNMENT .automatic == .center)
  checkFloat "replacement: copied PORT_BORDER_OFFSET" (rd.props.getD CoreOptions.PORT_BORDER_OFFSET 0.0) 3.0
  check "replacement: copied internals (EXT_PORT_SIDE, IN_LAYER_CONSTRAINT, ORIGIN)"
    (rd.internal.extPortSide == .north && rd.internal.inLayerConstraint == .top && rd.internal.origin == some (.elkPort ⟨7⟩))
  checkEq "replacement: two ports (input WEST, output EAST)"
    (rd.ports.map fun p => ElkEnum.javaName (a.port p).side) #["WEST", "EAST"]
  check "south replacement copies the south side" ((a.node r4).internal.extPortSide == .south)
  checkEq "hand: original north port lost all edges" ((a.node nN).ports.map fun p => (a.port p).degree) #[0]
  -- FREE: nothing happens
  let ((g2, _, es2), a2) ← LayeredM.run (do
    let r ← northSouthGraph .free
    runProc HierarchicalPortConstraintProcessor.processor r.1
    return r)
  checkEq "hand: FREE keeps the two layers" (a2.graph g2).layers.size 2
  checkEq "hand: FREE keeps the edges" ((a2.edge es2[2]!).source.bind fun p => (a2.port p).owner) (some ⟨1⟩)
  -- a dummy without an ElkPort/LPort origin is skipped (Rust `origin_port_key` = None)
  let ((g3, _, es3), a3) ← LayeredM.run (do
    let r ← northSouthGraph .fixedPos
    LayeredM.modifyNode r.2.1[1]! fun x => { x with internal := { x.internal with origin := none } }
    runProc HierarchicalPortConstraintProcessor.processor r.1
    return r)
  checkEq "hand: nN → b keeps its source without an origin key"
    ((a3.edge es3[2]!).source.bind fun p => (a3.port p).owner) (some ⟨1⟩)
  checkEq "hand: still removed from its layer" (a3.graph g3).internal.extPortReplacedDummies.size 2

/-! ## HierarchicalPortDummySizeProcessor -/

def dummySizeTests : Suite := suite "layered.intermediate.hierarchicalPortDummySize" do
  let ((ns, ports), a) ← LayeredM.run (do
    let g ← LayeredM.createGraph
    LayeredM.setGraphProp g LayeredOptions.SPACING_EDGE_EDGE_BETWEEN_LAYERS 5.0
    let l ← addLayer g
    let n1 ← mkExt g l .north
    let s1 ← mkExt g l .south
    let n2 ← mkExt g l .north
    let s2 ← mkExt g l .south
    let s3 ← mkExt g l .south
    let m ← mkNode g l { size := ⟨7, 7⟩ }
    let w ← mkExt g l .west
    LayeredM.modifyNode w fun x => { x with size := ⟨3, 3⟩ }
    let pe ← mkPort n2 { side := .east }
    let pw ← mkPort n2 { side := .west, position := ⟨1, 1⟩ }
    runProc HierarchicalPortDummySizeProcessor.processor g
    return (#[n1, s1, n2, s2, s3, m, w], #[pe, pw]))
  let width (i : Nat) := (a.node ns[i]!).size.x
  checkEq "hand: north widths top-down 0, 2·5" #[width 0, width 2] #[0.0, 10.0]
  checkEq "hand: south widths bottom-up 20, 10, 0" #[width 1, width 3, width 4] #[20.0, 10.0, 0.0]
  checkEq "hand: normal and west nodes keep their widths" #[width 5, width 6] #[7.0, 3.0]
  checkFloat "hand: east port moved to the new width" (a.port ports[0]!).position.x 10.0
  checkFloat "hand: west port untouched" (a.port ports[1]!).position.x 1.0
  check "hand: north/south dummies get ALIGNMENT CENTER"
    (#[0, 1, 2, 3, 4].all fun i => (a.node ns[i]!).props.getD CoreOptions.ALIGNMENT .automatic == .center)
  check "hand: other nodes keep the default alignment" (!(a.node ns[5]!).props.has CoreOptions.ALIGNMENT)
  -- default spacing (10) → delta 20, per layer
  let (ws, _) ← LayeredM.run (do
    let g ← LayeredM.createGraph
    let l0 ← addLayer g
    let l1 ← addLayer g
    let s1 ← mkExt g l0 .south
    let s2 ← mkExt g l0 .south
    let s3 ← mkExt g l1 .south
    runProc HierarchicalPortDummySizeProcessor.processor g
    return #[(← LayeredM.getNode s1).size.x, (← LayeredM.getNode s2).size.x, (← LayeredM.getNode s3).size.x])
  checkEq "hand: default edge-edge spacing 10 → 20, 0 (per layer: 0)" ws #[20.0, 0.0, 0.0]

/-! ## HierarchicalPortPositionProcessor -/

def positionTests : Suite := suite "layered.intermediate.hierarchicalPortPosition" do
  -- elk-rs `hierarchical_port_position_processor_does_not_deadlock_with_graph_lock`
  let (y0, _) ← LayeredM.run (do
    let g ← LayeredM.createGraph
    let l ← addLayer g
    setConstraints g .fixedPos
    LayeredM.modifyGraph g fun x => { x with size := ⟨100, 100⟩ }
    let node ← mkExt g l .east 0.5
    LayeredM.setNodeProp node CoreOptions.PORT_ANCHOR ({} : KVector)
    -- the Rust test pushes the node into the layer a second time
    LayeredM.modifyLayer l fun x => { x with nodes := x.nodes.push node }
    runProc HierarchicalPortPositionProcessor.processor g
    return (← LayeredM.getNode node).position.y)
  checkFloat "rust: hierarchical_port_position_processor_does_not_deadlock_with_graph_lock (FIXED_POS y = 0.5)" y0 0.5
  let build (pc : PortConstraints) : LayeredM (Array LNodeId) := do
    let g ← LayeredM.createGraph
    setConstraints g pc
    LayeredM.modifyGraph g fun x => { x with size := ⟨100, 100⟩, padding := ⟨10, 0, 10, 0⟩, offset := ⟨0, 3⟩ }
    let l0 ← addLayer g
    let l1 ← addLayer g
    let l2 ← addLayer g
    let w ← mkExt g l0 .west 0.25 none { position := ⟨0, 77⟩ }
    LayeredM.setNodeProp w CoreOptions.PORT_ANCHOR (⟨0, 2⟩ : KVector)
    let n ← mkExt g l0 .north 0.25 none { position := ⟨0, 77⟩ }
    let mid ← mkExt g l1 .east 0.25 none { position := ⟨0, 77⟩ }
    let e ← mkExt g l2 .east 40.0 none { position := ⟨0, 77⟩ }
    runProc HierarchicalPortPositionProcessor.processor g
    return #[w, n, mid, e]
  let (ns, a) ← LayeredM.run (build .fixedRatio)
  let ys := ns.map fun n => (a.node n).position.y
  checkFloat "hand: FIXED_RATIO west y = 0.25·120 - 2 - 10 - 3" ys[0]! 15.0
  checkFloat "hand: north dummy untouched" ys[1]! 77.0
  checkFloat "hand: middle layer untouched" ys[2]! 77.0
  checkFloat "hand: FIXED_RATIO last-layer east y = 40·120 - 10 - 3" ys[3]! 4787.0
  let (ns2, a2) ← LayeredM.run (build .fixedPos)
  checkFloat "hand: FIXED_POS east y = 40 - 0 - 10 - 3" (a2.node ns2[3]!).position.y 27.0
  let (ns3, a3) ← LayeredM.run (build .fixedOrder)
  checkFloat "hand: FIXED_ORDER leaves the dummies alone" (a3.node ns3[0]!).position.y 77.0

/-! ## HierarchicalNodeResizingProcessor -/

/-- A non-nested graph `60×50` (size `50×40` + padding 5) with external port dummies on all sides
in two layers and a layerless node. -/
def resizeGraph (alignment : EnumSet ContentAlignment) (minSize : KVector) : LayeredM (LGraphId × Array LNodeId) := do
  let g ← LayeredM.createGraph
  LayeredM.modifyGraph g fun x => { x with
    size := ⟨50, 40⟩, padding := ⟨5, 5, 5, 5⟩
    internal := { x.internal with graphProperties := EnumSet.of #[.externalPorts] } }
  LayeredM.setGraphProp g CoreOptions.NODE_SIZE_CONSTRAINTS (EnumSet.of #[SizeConstraint.minimumSize])
  LayeredM.setGraphProp g CoreOptions.NODE_SIZE_MINIMUM minSize
  LayeredM.setGraphProp g CoreOptions.CONTENT_ALIGNMENT alignment
  let free ← mkNode g none { position := ⟨1, 1⟩ }
  LayeredM.modifyGraph g fun x => { x with layerlessNodes := #[free] }
  let l0 ← addLayer g
  let l1 ← addLayer g
  let w ← mkExt g l0 .west 0.0 none { position := ⟨0, 10⟩ }
  let n ← mkNode g l0 { position := ⟨10, 10⟩ }
  let e ← mkExt g l1 .east 0.0 none { position := ⟨45, 10⟩ }
  let s ← mkExt g l1 .south 0.0 none { position := ⟨20, 35⟩ }
  let north ← mkExt g l1 .north 0.0 none { position := ⟨30, 0⟩ }
  return (g, #[free, w, n, e, s, north])

def resizingTests : Suite := suite "layered.intermediate.hierarchicalNodeResizing" do
  let ((g, ns), a) ← LayeredM.run (do
    let r ← resizeGraph (EnumSet.of #[.hCenter, .vBottom]) ⟨100, 80⟩
    runProc HierarchicalNodeResizingProcessor.processor r.1
    return r)
  let gr := a.graph g
  checkEq "hand: layers removed" gr.layers.size 0
  checkEq "hand: layerless = old layerless, then layer by layer" gr.layerlessNodes ns
  check "hand: no node keeps a layer" (ns.all fun n => (a.node n).layer.isNone)
  checkEq "hand: size = minimum - padding" gr.size ⟨90, 70⟩
  checkEq "hand: H_CENTER/V_BOTTOM offset = ((100-60)/2, 80-50)" gr.offset ⟨20, 30⟩
  let pos (i : Nat) := (a.node ns[i]!).position
  checkEq "hand: east dummy moved by the width growth" (pos 3) ⟨85, 10⟩
  checkEq "hand: south dummy moved by the height growth" (pos 4) ⟨20, 65⟩
  checkEq "hand: west, north and normal nodes stay" #[pos 1, pos 5, pos 2] #[⟨0, 10⟩, ⟨30, 0⟩, ⟨10, 10⟩]
  let ((g2, _), a2) ← LayeredM.run (do
    let r ← resizeGraph (EnumSet.of #[.hRight, .vCenter]) ⟨100, 80⟩
    runProc HierarchicalNodeResizingProcessor.processor r.1
    return r)
  checkEq "hand: H_RIGHT/V_CENTER offset = (40, 15)" (a2.graph g2).offset ⟨40, 15⟩
  let ((g3, ns3), a3) ← LayeredM.run (do
    let r ← resizeGraph ContentAlignment.topLeft ⟨10, 10⟩
    runProc HierarchicalNodeResizingProcessor.processor r.1
    return r)
  checkEq "hand: smaller minimum keeps the size" (a3.graph g3).size ⟨50, 40⟩
  checkEq "hand: no growth → no offset" (a3.graph g3).offset ⟨0, 0⟩
  checkEq "hand: no growth → east dummy stays" (a3.node ns3[3]!).position ⟨45, 10⟩
  -- default minimum size (20×20) applies to a 10×10 graph; without DEFAULT_MINIMUM_SIZE it does not
  let (sizes, _) ← LayeredM.run (do
    let g ← LayeredM.createGraph { size := ⟨10, 10⟩ }
    LayeredM.setGraphProp g CoreOptions.NODE_SIZE_CONSTRAINTS (EnumSet.of #[SizeConstraint.minimumSize])
    runProc HierarchicalNodeResizingProcessor.processor g
    let g2 ← LayeredM.createGraph { size := ⟨10, 10⟩ }
    LayeredM.setGraphProp g2 CoreOptions.NODE_SIZE_CONSTRAINTS (EnumSet.of #[SizeConstraint.minimumSize])
    LayeredM.setGraphProp g2 CoreOptions.NODE_SIZE_OPTIONS (EnumSet.noneOf : EnumSet SizeOptions)
    runProc HierarchicalNodeResizingProcessor.processor g2
    let g3 ← LayeredM.createGraph { size := ⟨10, 10⟩ }
    runProc HierarchicalNodeResizingProcessor.processor g3
    return #[(← LayeredM.getGraph g).size, (← LayeredM.getGraph g2).size, (← LayeredM.getGraph g3).size])
  checkEq "hand: DEFAULT_MINIMUM_SIZE → 20×20; without it 10×10; without MINIMUM_SIZE 10×10" sizes
    #[⟨20, 20⟩, ⟨10, 10⟩, ⟨10, 10⟩]

/-- A parent graph with compound node `parent` (ports `pE`, `pW`, `pN`, `pS`) whose nested graph
(`100×60`, padding top 10 right 8 bottom 6 left 12, offset (2,3)) holds one external port dummy per
side (origins: the parent's ports) and a normal node connected to the east dummy. -/
def nestedGraph (externalPorts : Bool := true) :
    LayeredM (LGraphId × LGraphId × LNodeId × Array LPortId × Array LNodeId) := do
  let top ← LayeredM.createGraph
  let parent ← mkNode top none { size := ⟨50, 30⟩ }
  LayeredM.modifyGraph top fun x => { x with layerlessNodes := #[parent] }
  let pE ← mkPort parent { size := ⟨8, 8⟩ }
  let pW ← mkPort parent { size := ⟨6, 4⟩ }
  let pN ← mkPort parent { size := ⟨4, 6⟩ }
  let pS ← mkPort parent { size := ⟨4, 6⟩ }
  let child ← LayeredM.createGraph { size := ⟨100, 60⟩, padding := ⟨10, 8, 6, 12⟩, offset := ⟨2, 3⟩, parentNode := some parent }
  if externalPorts then
    LayeredM.modifyGraph child fun x => { x with internal := { x.internal with graphProperties := EnumSet.of #[.externalPorts] } }
  LayeredM.modifyNode parent fun x => { x with nestedGraph := some child }
  let l ← addLayer child
  let n ← mkNode child l { position := ⟨30, 20⟩, size := ⟨20, 20⟩ }
  let e ← mkExt child l .east 0.0 (some (.lPort pE)) { position := ⟨90, 20⟩, size := ⟨5, 8⟩ }
  let w ← mkExt child l .west 0.0 (some (.lPort pW)) { position := ⟨0, 30⟩, size := ⟨5, 4⟩ }
  LayeredM.setNodeProp w CoreOptions.PORT_BORDER_OFFSET 2.0
  let no ← mkExt child l .north 0.0 (some (.lPort pN)) { position := ⟨40, 0⟩, size := ⟨10, 0⟩ }
  let so ← mkExt child l .south 0.0 (some (.lPort pS)) { position := ⟨60, 50⟩, size := ⟨10, 0⟩ }
  let _ ← connect n e
  let _ ← connect w n
  return (top, child, parent, #[pE, pW, pN, pS], #[n, e, w, no, so])

def transferTests : Suite := suite "layered.intermediate.hierarchicalNodeResizing.transfer" do
  let ((top, child, parent, ps, ns), a) ← LayeredM.run (do
    let r ← nestedGraph
    runProc HierarchicalNodeResizingProcessor.processor r.2.1
    return r)
  let port (i : Nat) := a.port ps[i]!
  -- compound_external_port_side_test (assertions on a hand-built nested graph)
  check "rust: compound_external_port_preserves_side_and_position (side stays EAST)" ((port 0).side == .east)
  check "rust: compound_external_port_preserves_side_and_position (x ≥ node width)"
    ((port 0).position.x >= (a.node parent).size.x - 1e-6)
  checkEq "hand: east port = (100+12+8, 24 + (10+3-4))" (port 0).position ⟨120, 33⟩
  checkEq "hand: east port anchor from setSide(EAST)" (port 0).anchor ⟨8, 4⟩
  checkEq "hand: west port = (-6-2, 32 + (10+3-2))" (port 1).position ⟨-8, 43⟩
  checkEq "hand: north port = (45 + (12+2-2), -6)" (port 2).position ⟨57, -6⟩
  checkEq "hand: south port = (65 + (12+2-2), 60+10+6)" (port 3).position ⟨77, 76⟩
  checkEq "hand: sides W, N, S" #[ElkEnum.javaName (port 1).side, ElkEnum.javaName (port 2).side, ElkEnum.javaName (port 3).side]
    #["WEST", "NORTH", "SOUTH"]
  let dpos (i : Nat) := (a.node ns[i]!).position
  checkEq "hand: east dummy x = 100+8+0-2" (dpos 1) ⟨106, 20⟩
  checkEq "hand: west dummy x = -(12+2+2)" (dpos 2) ⟨-16, 30⟩
  checkEq "hand: north dummy y = -(10+0+3)" (dpos 3) ⟨40, -13⟩
  checkEq "hand: south dummy y = 60+6+0-3" (dpos 4) ⟨60, 63⟩
  checkEq "hand: parent node resized to the actual size" (a.node parent).size ⟨120, 76⟩
  check "hand: parent PORT_CONSTRAINTS FIXED_POS"
    ((a.node parent).props.getD CoreOptions.PORT_CONSTRAINTS .undefined == .fixedPos)
  check "hand: parent graph gets NON_FREE_PORTS" ((a.graph top).internal.graphProperties.contains .nonFreePorts)
  check "hand: resizeNode stores NODE_SIZE_CONSTRAINTS = fixed()"
    ((a.node parent).props.has CoreOptions.NODE_SIZE_CONSTRAINTS)
  checkEq "hand: child graph layers removed" (a.graph child).layers.size 0
  -- without EXTERNAL_PORTS: ports are scaled by resizeNode instead (50×30 → 120×76)
  let ((top2, _, parent2, _, _), a2) ← LayeredM.run (do
    let r ← nestedGraph false
    let _ ← mkPort r.2.2.1 { side := .east, position := ⟨50, 10⟩ }
    runProc HierarchicalNodeResizingProcessor.processor r.2.1
    return r)
  let q := (a2.node parent2).ports.back!
  checkEq "hand: east port moved by widthDiff and scaled by the f32 height ratio"
    (a2.port q).position ⟨120, 10.0 * Float.toF32 (76.0 / 30.0)⟩
  check "hand: no FIXED_POS without external ports" (!(a2.node parent2).props.has CoreOptions.PORT_CONSTRAINTS)
  check "hand: no NON_FREE_PORTS without external ports" (!(a2.graph top2).internal.graphProperties.contains .nonFreePorts)

/-- One nested graph (`100×60`, no padding) with eastern dummies `d1` (self loop), `d2` (no edges)
and optionally `d3` (no edges). -/
def selfLoopGraph (third : Bool) : LayeredM (Array LPortId) := do
  let top ← LayeredM.createGraph
  let parent ← mkNode top
  let p1 ← mkPort parent { size := ⟨8, 8⟩ }
  let p2 ← mkPort parent { size := ⟨8, 8⟩ }
  let p3 ← mkPort parent { size := ⟨8, 8⟩ }
  let child ← LayeredM.createGraph { size := ⟨100, 60⟩, parentNode := some parent }
  LayeredM.modifyGraph child fun x => { x with internal := { x.internal with graphProperties := EnumSet.of #[.externalPorts] } }
  let d1 ← mkExt child none .east 0.0 (some (.lPort p1)) { position := ⟨0, 20⟩, size := ⟨0, 8⟩ }
  let d2 ← mkExt child none .east 0.0 (some (.lPort p2)) { position := ⟨0, 30⟩, size := ⟨0, 8⟩ }
  let _ ← connect d1 d1
  let mut nodes := #[d1, d2]
  if third then
    nodes := nodes.push (← mkExt child none .east 0.0 (some (.lPort p3)) { position := ⟨0, 40⟩, size := ⟨0, 8⟩ })
  LayeredM.modifyGraph child fun x => { x with layerlessNodes := nodes }
  runProc HierarchicalNodeResizingProcessor.processor child
  return #[p1, p2, p3]

def selfLoopTests : Suite := suite "layered.intermediate.hierarchicalNodeResizing.selfLoops" do
  let (ps, a) ← LayeredM.run (selfLoopGraph false)
  -- Java: the external port position is used as computed (elk-rs subtracted the dummy's y for
  -- eastern "pure self loop" dummies)
  checkFloat "java: self-loop east dummy: y = 24 - 4" (a.port ps[0]!).position.y 20.0
  checkFloat "java: the only edge-less east dummy: y = 34 - 4" (a.port ps[1]!).position.y 30.0
  let (ps2, a2) ← LayeredM.run (selfLoopGraph true)
  checkFloat "java: self loop with two edge-less dummies: y = 24 - 4" (a2.port ps2[0]!).position.y 20.0
  checkFloat "hand: two edge-less east dummies are not pure: y = 34 - 4" (a2.port ps2[1]!).position.y 30.0
  checkFloat "hand: third edge-less dummy: y = 44 - 4" (a2.port ps2[2]!).position.y 40.0
  checkFloat "hand: east x = graph width" (a2.port ps2[2]!).position.x 100.0

/-! ## InteractiveExternalPortPositioner -/

/-- Rust test helper `node`: a node at (100,200) of size 40×20 in the layerless nodes. -/
def iNode (g : LGraphId) (external : Bool) : LayeredM LNodeId := do
  let n ← mkNode g none { type := if external then .externalPort else .normal, position := ⟨100, 200⟩, size := ⟨40, 20⟩ }
  LayeredM.modifyGraph g fun x => { x with layerlessNodes := x.layerlessNodes.push n }
  return n

/-- Rust test helper `graph`: `GRAPH_PROPERTIES = {EXTERNAL_PORTS}`. -/
def iGraph : LayeredM LGraphId :=
  LayeredM.createGraph { internal := { graphProperties := EnumSet.of #[.externalPorts] } }

def interactiveSide (side : Nat) : LayeredM KVector := do
  let g ← iGraph
  let normal ← iNode g false
  let external ← iNode g true
  match side with
  | 0 =>
    LayeredM.setNodeProp external LayeredOptions.LAYERING_LAYER_CONSTRAINT LayerConstraint.firstSeparate
    let _ ← connect external normal
  | 1 =>
    LayeredM.setNodeProp external LayeredOptions.LAYERING_LAYER_CONSTRAINT LayerConstraint.lastSeparate
    let _ ← connect normal external
  | 2 =>
    LayeredM.modifyNode external fun x => { x with internal := { x.internal with inLayerConstraint := .top } }
    let _ ← connect external normal
  | _ =>
    LayeredM.modifyNode external fun x => { x with internal := { x.internal with inLayerConstraint := .bottom } }
    let _ ← connect normal external
  runProc InteractiveExternalPortPositioner.processor g
  return (← LayeredM.getNode external).position

def interactiveTests : Suite := suite "layered.intermediate.interactiveExternalPortPositioner" do
  let expected : Array KVector := #[⟨90, 210⟩, ⟨150, 210⟩, ⟨110, 190⟩, ⟨150, 230⟩]
  for side in [0:4] do
    let (pos, _) ← LayeredM.run (interactiveSide side)
    checkEq s!"rust: interactive_external_ports_preserve_all_four_side_coordinates (side={side})" pos expected[side]!
  -- external_port_helpers_allow_edges_back_to_the_same_node
  let (r, _) ← LayeredM.run (do
    let g ← iGraph
    let external ← iNode g true
    let _ ← connect external external
    let disconnected ← iNode g true
    return (#[← InteractiveExternalPortPositioner.findYFromTargets external,
        ← InteractiveExternalPortPositioner.findYFromSources external,
        ← InteractiveExternalPortPositioner.findNorthSouthX external],
      #[← InteractiveExternalPortPositioner.findYFromTargets disconnected,
        ← InteractiveExternalPortPositioner.findYFromSources disconnected,
        ← InteractiveExternalPortPositioner.findNorthSouthX disconnected]))
  checkEq "rust: external_port_helpers_allow_edges_back_to_the_same_node (self edge)" r.1 #[some 210.0, some 210.0, some 100.0]
  checkEq "rust: external_port_helpers_allow_edges_back_to_the_same_node (disconnected)" r.2 #[none, none, none]
  -- no EXTERNAL_PORTS → nothing happens; margins widen the box of the normal nodes
  let (pos, _) ← LayeredM.run (do
    let g ← LayeredM.createGraph
    let normal ← iNode g false
    let external ← iNode g true
    LayeredM.setNodeProp external LayeredOptions.LAYERING_LAYER_CONSTRAINT LayerConstraint.firstSeparate
    let _ ← connect external normal
    runProc InteractiveExternalPortPositioner.processor g
    return (← LayeredM.getNode external).position)
  checkEq "hand: without EXTERNAL_PORTS the dummy is not moved" pos ⟨100, 200⟩
  let (pos2, _) ← LayeredM.run (do
    let g ← iGraph
    let normal ← iNode g false
    LayeredM.setNodeProp normal CoreOptions.MARGINS ({ left := 5, right := 7, top := 3, bottom := 4 } : ElkMargin)
    let external ← iNode g true
    LayeredM.modifyNode external fun x => { x with internal := { x.internal with inLayerConstraint := .bottom } }
    let _ ← connect normal external
    runProc InteractiveExternalPortPositioner.processor g
    return (← LayeredM.getNode external).position)
  checkEq "hand: south dummy x = 100+40+7+10, y = 200+20+4+10 (MARGINS)" pos2 ⟨157, 234⟩
  -- Rust applies the layer constraint and the in-layer constraint together
  let (pos3, _) ← LayeredM.run (do
    let g ← iGraph
    let normal ← iNode g false
    let external ← iNode g true
    LayeredM.setNodeProp external LayeredOptions.LAYERING_LAYER_CONSTRAINT LayerConstraint.lastSeparate
    LayeredM.modifyNode external fun x => { x with internal := { x.internal with inLayerConstraint := .top } }
    let _ ← connect normal external
    runProc InteractiveExternalPortPositioner.processor g
    return (← LayeredM.getNode external).position)
  checkEq "hand: LAST_SEPARATE + TOP: x from the north/south rule (140+10), y = 200-10" pos3 ⟨150, 190⟩

/-! ## Registration -/

def registrationTests : Suite := suite "layered.intermediate.hierarchicalPorts.registration" do
  let strategies : Array IntermediateProcessorStrategy :=
    #[.hierarchicalPortConstraintProcessor, .hierarchicalPortDummySizeProcessor, .hierarchicalPortPositionProcessor,
      .hierarchicalNodeResizer, .interactiveExternalPortPositioner]
  let names ← strategies.mapM fun s => do return (← IntermediateProcessorStrategy.create s).name
  checkEq "registered processors (elk-rs type names)" names
    #["HierarchicalPortConstraintProcessor", "HierarchicalPortDummySizeProcessor", "HierarchicalPortPositionProcessor",
      "HierarchicalNodeResizingProcessor", "InteractiveExternalPortPositioner"]

def suites : Array Suite :=
  #[eastWestTests, northSouthTests, dummySizeTests, positionTests, resizingTests, transferTests, selfLoopTests,
    interactiveTests, registrationTests]

end Tests.Layered.IntermediateHierarchicalPorts
