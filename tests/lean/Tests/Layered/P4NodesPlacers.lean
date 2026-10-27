import Tests.Framework
import Elk.Alg.Layered
import Elk.Alg.Layered.P4Nodes.Placers
/-!
# Tests for the `p4nodes` placers other than Brandes-Köpf

`SimpleNodePlacer`, `InteractiveNodePlacer`, `LinearSegmentsNodePlacer` and
`NetworkSimplexPlacer` on hand-built layered graphs. The elk-rs tests
(`basic_node_placement_test.rs`, `network_simplex_bk_test.rs`, `node_placement_strategy_test.rs`)
run the whole layered algorithm on the A→B, A→C, B→D, C→D diamond and assert that the nodes of
every layer are ordered without overlap (`assert_layer_node_positions_increasing`); that
assertion is ported onto the diamond after layering. Expected coordinates marked "hand:" are
derived by hand in the comments (default spacings: node-node 20, edge-node 10, edge-edge 10).
Layer ids are set to the layer indices (as the crossing minimizer does).
-/
namespace Tests.Layered.P4NodesPlacers

open Tests Elk Elk.Graph Elk.Core.Math Elk.Core.Options Elk.Core.Util Elk.Core.Alg
open Elk.Alg.Layered Elk.Alg.Layered.Graph Elk.Alg.Layered.Options Elk.Alg.Layered.P4Nodes
open Elk.Alg.Layered.Intermediate

/-- A graph with `layerCount` layers (ids = indices) and `Spacings.new props` in `internal.spacings`. -/
def mkGraph (layerCount : Nat) (props : PropertyMap := {}) : LayeredM (LGraphId × Array LayerId) := do
  let g ← LayeredM.createGraph { props := props }
  let mut layers : Array LayerId := #[]
  for i in [0:layerCount] do
    let l ← LayeredM.createLayer g
    LayeredM.modifyLayer l fun x => { x with id := (i : Int) }
    layers := layers.push l
  let ls := layers
  LayeredM.modifyGraph g fun x =>
    { x with layers := ls, internal := { x.internal with spacings := some (Spacings.new props) } }
  return (g, layers)

/-- A node of width 20 and the given height (and type, properties, y, margin) appended to `layer`. -/
def addNode (g : LGraphId) (layer : LayerId) (height : Float) (type : NodeType := .normal)
    (props : PropertyMap := {}) (y : Float := 0.0) (margin : LMargin := {}) : LayeredM LNodeId := do
  let n ← LayeredM.createNode g
    { size := ⟨20.0, height⟩, type := type, props := props, position := ⟨0.0, y⟩, margin := margin }
  LayeredM.setNodeLayer n (some layer)
  return n

/-- A port of size 0 at `(0, y)` on `side` of `n`. -/
def addPort (n : LNodeId) (side : PortSide) (y : Float) : LayeredM LPortId := do
  let p ← LayeredM.createPort { side := side, position := ⟨0.0, y⟩ }
  LayeredM.setPortNode p (some n)
  return p

/-- An edge `s → t`. -/
def connect (s t : LPortId) (props : PropertyMap := {}) : LayeredM LEdgeId := do
  let e ← LayeredM.createEdge { props := props }
  LayeredM.setEdgeSource e (some s)
  LayeredM.setEdgeTarget e (some t)
  return e

/-- Two layers: `A` (height 30, east port at 15) → `B` (height 50, west port at `bPortY`). -/
def buildChain (bPortY : Float := 25.0) (props : PropertyMap := {}) : LayeredM (LGraphId × Array LNodeId) := do
  let (g, ls) ← mkGraph 2 props
  let a ← addNode g ls[0]! 30.0
  let b ← addNode g ls[1]! 50.0
  let pa ← addPort a .east 15.0
  let pb ← addPort b .west bPortY
  let _ ← connect pa pb
  return (g, #[a, b])

/-- The elk-rs test diamond after layering: `A | B C | D` (height 30, one port per side at 15);
edges `A→B`, `A→C`, `B→D`, `C→D`; `strong` is put on `A→B` and `B→D`. -/
def buildDiamond (props : PropertyMap := {}) (strong : PropertyMap := {}) :
    LayeredM (LGraphId × Array LNodeId) := do
  let (g, ls) ← mkGraph 3 props
  let a ← addNode g ls[0]! 30.0
  let b ← addNode g ls[1]! 30.0
  let c ← addNode g ls[1]! 30.0
  let d ← addNode g ls[2]! 30.0
  let pa ← addPort a .east 15.0
  let pbw ← addPort b .west 15.0
  let pbe ← addPort b .east 15.0
  let pcw ← addPort c .west 15.0
  let pce ← addPort c .east 15.0
  let pd ← addPort d .west 15.0
  let _ ← connect pa pbw strong
  let _ ← connect pa pcw
  let _ ← connect pbe pd strong
  let _ ← connect pce pd
  return (g, #[a, b, c, d])

/-- Runs `phase` on the graph built by `build`. -/
def runPhase (build : LayeredM (LGraphId × Array LNodeId)) (phase : LayeredPhase) :
    IO ((LGraphId × Array LNodeId) × LGraphArena) :=
  LayeredM.run do
    let r ← build
    phase.process r.1 ProgressMonitor.null
    return r

/-- `assert_layer_node_positions_increasing`: in every layer the next node starts strictly below the
bottom of the previous one. -/
def positionsIncreasing (a : LGraphArena) (g : LGraphId) : Bool :=
  (a.graph g).layers.all fun l =>
    let nodes := (a.layer l).nodes
    (Array.range (nodes.size - 1)).all fun i =>
      let n1 := a.node nodes[i]!
      let n2 := a.node nodes[i + 1]!
      n1.position.y + n1.size.y < n2.position.y

/-- Every node of every layer is at least `spacing` below its predecessor. -/
def respectsSpacing (a : LGraphArena) (g : LGraphId) (spacing : Float) : Bool :=
  (a.graph g).layers.all fun l =>
    let nodes := (a.layer l).nodes
    (Array.range (nodes.size - 1)).all fun i =>
      let n1 := a.node nodes[i]!
      let n2 := a.node nodes[i + 1]!
      n1.position.y + n1.size.y + n1.margin.bottom + spacing <= n2.position.y - n2.margin.top + 1e-9

/-- Absolute y of a port anchor. -/
def portY (a : LGraphArena) (p : LPortId) : Float := ((a.portAbsoluteAnchor p).map (·.y)).getD Float.nan

/-- Absolute y of the first port of `n` on `side`. -/
def sidePortY (a : LGraphArena) (n : LNodeId) (side : PortSide) : Float :=
  match (a.nodePortsBySide n side)[0]? with
  | some p => portY a p
  | none => Float.nan

def y (a : LGraphArena) (n : LNodeId) : Float := (a.node n).position.y

-- ============================================================================================

def simpleTests : Suite := suite "layered.p4nodes.simple" do
  -- hand: layer heights 30 and 50, maximum 50 → A at (50 - 30) / 2 = 10, B at 0
  let ((g, ns), a) ← runPhase (buildChain) SimpleNodePlacer.phase
  checkFloat "chain: A y (hand: 10)" (y a ns[0]!) 10.0
  checkFloat "chain: B y (hand: 0)" (y a ns[1]!) 0.0
  checkFloat "chain: layer 0 height (hand: 30)" (a.layer (a.graph g).layers[0]!).size.y 30.0
  checkFloat "chain: layer 1 height (hand: 50)" (a.layer (a.graph g).layers[1]!).size.y 50.0
  -- hand: middle layer 30 + 20 + 30 = 80 → A = D = (80 - 30) / 2 = 25, B = 0, C = 50
  let ((g, ns), a) ← runPhase (buildDiamond) SimpleNodePlacer.phase
  checkFloat "diamond: A y (hand: 25)" (y a ns[0]!) 25.0
  checkFloat "diamond: B y (hand: 0)" (y a ns[1]!) 0.0
  checkFloat "diamond: C y (hand: 50)" (y a ns[2]!) 50.0
  checkFloat "diamond: D y (hand: 25)" (y a ns[3]!) 25.0
  check "diamond: layer node positions increasing" (positionsIncreasing a g)
  check "diamond: node spacing respected" (respectsSpacing a g 20.0)
  -- hand: margins 5/5 → middle layer 40 + 20 + 40 = 100, B at 5, C at 40 + 20 + 5 = 65, A at (100 - 30) / 2
  let ((g, ns), a) ← LayeredM.run do
    let (g, ls) ← mkGraph 2
    let a ← addNode g ls[0]! 30.0
    let b ← addNode g ls[1]! 30.0 (margin := { top := 5.0, bottom := 5.0 })
    let c ← addNode g ls[1]! 30.0 (margin := { top := 5.0, bottom := 5.0 })
    SimpleNodePlacer.phase.process g ProgressMonitor.null
    return (g, #[a, b, c])
  checkFloat "margins: B y (hand: 5)" (y a ns[1]!) 5.0
  checkFloat "margins: C y (hand: 65)" (y a ns[2]!) 65.0
  checkFloat "margins: A y (hand: 35)" (y a ns[0]!) 35.0
  checkFloat "margins: layer 1 height (hand: 100)" (a.layer (a.graph g).layers[1]!).size.y 100.0

def interactiveTests : Suite := suite "layered.p4nodes.interactive" do
  -- hand: A keeps 100; B (authored 110) is pushed to 100 + 30 + 20 = 150; C keeps 300
  -- dummy D (long edge, no original position): 0 + spacing(longEdge, normal) 10 = 10; E (authored 5)
  -- is pushed to 10 + 0 + 10 = 20; dummy F with original position 77 is put there
  let ((_, ns), a) ← LayeredM.run do
    let (g, ls) ← mkGraph 2
    let na ← addNode g ls[0]! 30.0 (y := 100.0)
    let nb ← addNode g ls[0]! 30.0 (y := 110.0)
    let nc ← addNode g ls[0]! 30.0 (y := 300.0)
    let nd ← addNode g ls[1]! 0.0 (type := .longEdge) (y := 500.0)
    let ne ← addNode g ls[1]! 30.0 (y := 5.0)
    let nf ← addNode g ls[1]! 0.0 (type := .longEdge)
    LayeredM.modifyNode nf fun x => { x with internal := { x.internal with originalDummyNodePosition := some 77.0 } }
    InteractiveNodePlacer.phase.process g ProgressMonitor.null
    return (g, #[na, nb, nc, nd, ne, nf])
  checkFloat "A keeps its position (hand: 100)" (y a ns[0]!) 100.0
  checkFloat "B moved below A (hand: 150)" (y a ns[1]!) 150.0
  checkFloat "C keeps its position (hand: 300)" (y a ns[2]!) 300.0
  checkFloat "dummy without original position (hand: 10)" (y a ns[3]!) 10.0
  checkFloat "E moved below the dummy (hand: 20)" (y a ns[4]!) 20.0
  checkFloat "dummy at its original position (hand: 77)" (y a ns[5]!) 77.0
  -- authored diamond positions in order are kept
  let ((g, _), a) ← LayeredM.run do
    let (g, ns) ← buildDiamond
    LayeredM.modifyNode ns[2]! fun x => { x with position := ⟨0.0, 60.0⟩ }
    InteractiveNodePlacer.phase.process g ProgressMonitor.null
    return (g, ns)
  check "diamond: layer node positions increasing" (positionsIncreasing a g)
  check "diamond: node spacing respected" (respectsSpacing a g 20.0)

def linearSegmentsTests : Suite := suite "layered.p4nodes.linearSegments" do
  -- segment order of the diamond: segments A0 B1 C2 D3; dependency B → C; queue [0, 1, 3], then 2
  -- → ranks A 0, B 1, D 2, C 3 (the node ids)
  let ((_, ns, segIds), a) ← LayeredM.run do
    let (g, ns) ← buildDiamond
    let (segments, _) ← LinearSegmentsNodePlacer.sortLinearSegments g
    let some spacings := (← LayeredM.getGraph g).internal.spacings | return (g, ns, #[])
    LinearSegmentsNodePlacer.createUnbalancedPlacement g segments spacings
    return (g, ns, segments.map (·.nodes))
  checkEq "segment ranks as node ids (A B C D)" (ns.map fun n => (a.node n).id) #[0, 1, 3, 2]
  checkEq "segment count" segIds.size 4
  -- hand: unbalanced placement: first node of each layer at SPACING_EDGE_EDGE 10, C below B at 40 + 20
  checkFloat "unbalanced: A y (hand: 10)" (y a ns[0]!) 10.0
  checkFloat "unbalanced: B y (hand: 10)" (y a ns[1]!) 10.0
  checkFloat "unbalanced: C y (hand: 60)" (y a ns[2]!) 60.0
  checkFloat "unbalanced: D y (hand: 10)" (y a ns[3]!) 10.0
  -- long edge dummies in consecutive layers form one segment
  let (ids, _) ← LayeredM.run do
    let (g, ls) ← mkGraph 4
    let na ← addNode g ls[0]! 30.0
    let x ← addNode g ls[1]! 0.0 (type := .longEdge)
    let z ← addNode g ls[2]! 0.0 (type := .longEdge)
    let nb ← addNode g ls[3]! 30.0
    let pa ← addPort na .east 15.0
    let pxw ← addPort x .west 0.0
    let pxe ← addPort x .east 0.0
    let pzw ← addPort z .west 0.0
    let pze ← addPort z .east 0.0
    let pb ← addPort nb .west 15.0
    let _ ← connect pa pxw
    let _ ← connect pxe pzw
    let _ ← connect pze pb
    let (segments, _) ← LinearSegmentsNodePlacer.sortLinearSegments g
    return (segments.map (·.nodes.size), (← LayeredM.getNode x).id == (← LayeredM.getNode z).id)
  checkEq "long edge chain: segment sizes" ids.1 #[1, 2, 1]
  check "long edge chain: both dummies in one segment" ids.2
  -- hand: aligned chain (both ports at 15): no deflection, both nodes stay at SPACING_EDGE_EDGE 10
  let ((_, ns), a) ← runPhase (buildChain (bPortY := 15.0)) LinearSegmentsNodePlacer.phase
  checkFloat "aligned chain: A y (hand: 10)" (y a ns[0]!) 10.0
  checkFloat "aligned chain: B y (hand: 10)" (y a ns[1]!) 10.0
  -- misaligned chain: the pendulum and the post-processing straighten the edge
  let ((_, ns), a) ← runPhase (buildChain) LinearSegmentsNodePlacer.phase
  checkFloat "chain: edge straight" (sidePortY a ns[0]! .east) (sidePortY a ns[1]! .west) (eps := 1e-9)
  let ((g, _), a) ← runPhase (buildDiamond) LinearSegmentsNodePlacer.phase
  check "diamond: layer node positions increasing" (positionsIncreasing a g)
  check "diamond: node spacing respected" (respectsSpacing a g 20.0)

def networkSimplexTests : Suite := suite "layered.p4nodes.networkSimplex" do
  -- hand: auxiliary edges d→A (delta 25 - 15 = 10) and d→B (delta 0), weight 4: optimum A = d + 10,
  -- B = d, normalized d = 0 → A at 10, B at 0 (A port 10 + 15 = B port 0 + 25)
  let ((g, ns), a) ← runPhase (buildChain) NetworkSimplexPlacer.phase
  checkFloat "chain: A y (hand: 10)" (y a ns[0]!) 10.0
  checkFloat "chain: B y (hand: 0)" (y a ns[1]!) 0.0
  checkEq "prepare: node ids" (ns.map fun n => (a.node n).id) #[0, 1]
  checkEq "prepare: edge id" ((a.nodeOutgoingEdges ns[0]!).map fun e => (a.edge e).id) #[0]
  let _ := g
  -- hand: priority 2 on A→B and B→D (weight 8) beats A→C and C→D (weight 4); C ≥ B + 30 + 20:
  -- optimum A = B = D = 0, C = 50
  let strong := ({} : PropertyMap).set LayeredOptions.PRIORITY_STRAIGHTNESS (2 : Int)
  let ((g, ns), a) ← runPhase (buildDiamond (strong := strong)) NetworkSimplexPlacer.phase
  checkFloat "diamond: A y (hand: 0)" (y a ns[0]!) 0.0
  checkFloat "diamond: B y (hand: 0)" (y a ns[1]!) 0.0
  checkFloat "diamond: C y (hand: 50)" (y a ns[2]!) 50.0
  checkFloat "diamond: D y (hand: 0)" (y a ns[3]!) 0.0
  check "diamond: layer node positions increasing" (positionsIncreasing a g)
  -- unweighted diamond: B = 0 and C = B + 50 (tight), A and D anywhere in between
  let ((g, ns), a) ← runPhase (buildDiamond) NetworkSimplexPlacer.phase
  checkFloat "plain diamond: B y (hand: 0)" (y a ns[1]!) 0.0
  checkFloat "plain diamond: C y (hand: 50)" (y a ns[2]!) 50.0
  check "plain diamond: A between B and C" (y a ns[0]! >= 0.0 && y a ns[0]! <= 50.0)
  check "plain diamond: D between B and C" (y a ns[3]! >= 0.0 && y a ns[3]! <= 50.0)
  check "plain diamond: layer node positions increasing" (positionsIncreasing a g)
  check "plain diamond: node spacing respected" (respectsSpacing a g 20.0)
  -- hand: straight chain A(30, port 15) → B(50, ports 10 / 40) → C(30, port 15) with favored straight
  -- edges: B = A + 5, C = B + 25, normalized A = 0 → 0, 5, 30
  for favor in [false, true] do
    let props := ({} : PropertyMap).set LayeredOptions.NODE_PLACEMENT_FAVOR_STRAIGHT_EDGES favor
    let ((_, ns), a) ← runPhase (do
        let (g, ls) ← mkGraph 3 props
        let na ← addNode g ls[0]! 30.0
        let nb ← addNode g ls[1]! 50.0
        let nc ← addNode g ls[2]! 30.0
        let pa ← addPort na .east 15.0
        let pbw ← addPort nb .west 10.0
        let pbe ← addPort nb .east 40.0
        let pc ← addPort nc .west 15.0
        let _ ← connect pa pbw
        let _ ← connect pbe pc
        return (g, #[na, nb, nc])) NetworkSimplexPlacer.phase
    let tag := if favor then "favor straight" else "default"
    checkFloat s!"{tag}: A y (hand: 0)" (y a ns[0]!) 0.0
    checkFloat s!"{tag}: B y (hand: 5)" (y a ns[1]!) 5.0
    checkFloat s!"{tag}: C y (hand: 30)" (y a ns[2]!) 30.0
    checkFloat s!"{tag}: first edge straight" (sidePortY a ns[0]! .east) (sidePortY a ns[1]! .west)
    checkFloat s!"{tag}: second edge straight" (sidePortY a ns[1]! .east) (sidePortY a ns[2]! .west)
  -- flexible ports (PORT_POSITION): B(60) keeps its size, its ports move so that both edges are straight
  let flexProps := ({} : PropertyMap).set LayeredOptions.NODE_PLACEMENT_NETWORK_SIMPLEX_NODE_FLEXIBILITY
    NodeFlexibility.portPosition
  let ((g, ns), a) ← runPhase (do
      let (g, ls) ← mkGraph 3
      let na ← addNode g ls[0]! 30.0
      let nb ← addNode g ls[1]! 60.0 (props := flexProps)
      let nc ← addNode g ls[2]! 30.0
      let pa ← addPort na .east 15.0
      let pbw ← addPort nb .west 10.0
      let pbe ← addPort nb .east 40.0
      let pc ← addPort nc .west 15.0
      let _ ← connect pa pbw
      let _ ← connect pbe pc
      return (g, #[na, nb, nc])) NetworkSimplexPlacer.phase
  check "flexible node is flexible" (← (NetworkSimplexPlacer.isFlexibleNode (a.graph g).props ns[1]!).run' a)
  checkFloat "flexible ports: B keeps its height" (a.node ns[1]!).size.y 60.0
  checkFloat "flexible ports: first edge straight" (sidePortY a ns[0]! .east) (sidePortY a ns[1]! .west)
  checkFloat "flexible ports: second edge straight" (sidePortY a ns[1]! .east) (sidePortY a ns[2]! .west)
  let westY := (a.port (a.nodePortsBySide ns[1]! .west)[0]!).position.y
  check "flexible ports: west port inside the node" (westY >= 0.0 && westY <= 60.0)
  -- flexible size where space permits: a second network simplex run, the node never shrinks
  let sizeProps := ({} : PropertyMap).set LayeredOptions.NODE_PLACEMENT_NETWORK_SIMPLEX_NODE_FLEXIBILITY
    NodeFlexibility.nodeSizeWhereSpacePermits
  let ((g, ns), a) ← runPhase (do
      let (g, ls) ← mkGraph 3
      let na ← addNode g ls[0]! 30.0
      let nb ← addNode g ls[1]! 60.0 (props := sizeProps)
      let nb2 ← addNode g ls[1]! 30.0
      let nc ← addNode g ls[2]! 30.0
      let pa ← addPort na .east 15.0
      let pbw ← addPort nb .west 10.0
      let pbe ← addPort nb .east 40.0
      let pb2 ← addPort nb2 .west 15.0
      let pc ← addPort nc .west 15.0
      let _ ← connect pa pbw
      let _ ← connect pa pb2
      let _ ← connect pbe pc
      return (g, #[na, nb, nb2, nc])) NetworkSimplexPlacer.phase
  check "space-permitting size: B does not shrink" ((a.node ns[1]!).size.y >= 60.0)
  check "space-permitting size: layer node positions increasing" (positionsIncreasing a g)
  check "space-permitting size: node spacing respected" (respectsSpacing a g 20.0)
  -- `ArenaSync` lists incoming edges in discovery order (source ports in arena order), not in
  -- `LPort.incomingEdges` order: e2 (from the lower source) was connected first
  let ((g, target, e1, e2), a) ← LayeredM.run do
    let (g, ls) ← mkGraph 2
    let s1 ← addNode g ls[0]! 30.0
    let s2 ← addNode g ls[0]! 30.0
    let t ← addNode g ls[1]! 30.0
    let p1 ← addPort s1 .east 15.0
    let p2 ← addPort s2 .east 15.0
    let pt ← addPort t .west 15.0
    let e2 ← connect p2 pt
    let e1 ← connect p1 pt
    return (g, pt, e1, e2)
  check "port incoming edges in connection order" ((a.port target).incomingEdges == #[e2, e1])
  check "arena incoming edges in discovery order"
    ((NetworkSimplexPlacer.arenaIncomingEdges a g).getD target #[] == #[e1, e2])

def configurationTests : Suite := suite "layered.p4nodes.configuration" do
  let phases : Array LayeredPhase := #[SimpleNodePlacer.phase, InteractiveNodePlacer.phase,
    LinearSegmentsNodePlacer.phase, NetworkSimplexPlacer.phase]
  for phase in phases do
    let (cfgs, _) ← LayeredM.run do
      let (g, _) ← buildChain
      let plain ← phase.getLayoutProcessorConfiguration g
      LayeredM.modifyGraph g fun x =>
        { x with internal := { x.internal with graphProperties := EnumSet.of #[GraphProperties.externalPorts] } }
      let ext ← phase.getLayoutProcessorConfiguration g
      return (plain, ext)
    check s!"{phase.name}: no configuration without external ports" cfgs.1.isNone
    check s!"{phase.name}: hierarchical port position processor before P5 with external ports"
      ((cfgs.2.map (·.processorsBefore .p5EdgeRouting)) == some #[IntermediateProcessorStrategy.hierarchicalPortPositionProcessor])
  -- registration of the strategies (`NodePlacementStrategy.create`)
  let registered : Array (NodePlacementStrategy × String) := #[(.simple, "SimpleNodePlacer"),
    (.interactive, "InteractiveNodePlacer"), (.linearSegments, "LinearSegmentsNodePlacer"),
    (.networkSimplex, "NetworkSimplexPlacer")]
  for (strategy, name) in registered do
    let phase ← (LayeredPhases.strategyFactory .p4NodePlacement "NodePlacementStrategy" (ElkEnum.ordinal strategy)
      (ElkEnum.javaName strategy)).create
    checkEq s!"{ElkEnum.javaName strategy} creates {name}" phase.name name
  -- the elk-rs basic placement assertion on the diamond for every ported strategy
  for phase in phases do
    let ((g, _), a) ← runPhase (buildDiamond) phase
    check s!"{phase.name}: diamond layer node positions increasing" (positionsIncreasing a g)
  -- missing spacings: Java/Rust fail
  for phase in phases do
    checkThrows s!"{phase.name}: missing spacings" do
      let _ ← LayeredM.run do
        let (g, _) ← buildChain
        LayeredM.modifyGraph g fun x => { x with internal := { x.internal with spacings := none } }
        phase.process g ProgressMonitor.null

def suites : Array Suite := #[simpleTests, interactiveTests, linearSegmentsTests, networkSimplexTests, configurationTests]

end Tests.Layered.P4NodesPlacers
