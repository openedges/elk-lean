import Tests.Framework
import Elk.Alg.Layered
import Elk.Alg.Layered.P2Layers
/-! Tests of `org.eclipse.elk.alg.layered.p2layers`: the assertions of elk-rs
`tests/p2_layers/basic_layer_assignment_test.rs` (no layerless nodes, no empty layers, edges point
towards later layers) on hand-built graphs, exact layerings derived by hand, the width bounds,
interactive layering from positions, the model order layerers, the processor configurations and
the phase registrations. -/
namespace Tests.Layered.P2Layers

open Tests Elk Elk.Graph Elk.Core Elk.Core.Util Elk.Core.Math Elk.Core.Alg Elk.Core.Options
open Elk.Alg.Common.NetworkSimplex
open Elk.Alg.Layered Elk.Alg.Layered.Graph Elk.Alg.Layered.Options Elk.Alg.Layered.Intermediate
open Elk.Alg.Layered.P2Layers

/-- A hand-built test graph. -/
structure Built where
  graph : LGraphId
  nodes : Array LNodeId
  edges : Array LEdgeId
  deriving Inhabited

/-- `n` layerless 30×30 nodes (optionally with x positions/widths) and one edge (own source and
target port) per pair `(s, t)`. -/
def build (n : Nat) (edges : Array (Nat × Nat)) (xs : Array (Float × Float) := #[])
    (types : Array NodeType := #[]) : LayeredM Built := do
  let g ← LayeredM.createGraph
  let mut ns : Array LNodeId := #[]
  for i in [0:n] do
    let (x, w) := xs.getD i (0.0, 30.0)
    ns := ns.push (← LayeredM.createNode g { size := ⟨w, 30.0⟩, position := ⟨x, 0.0⟩, type := types.getD i .normal })
  LayeredM.modifyGraph g fun x => { x with layerlessNodes := ns }
  let mut es : Array LEdgeId := #[]
  for (s, t) in edges do
    let ps ← LayeredM.createPort { side := .east }
    LayeredM.setPortNode ps (some ns[s]!)
    let pt ← LayeredM.createPort { side := .west }
    LayeredM.setPortNode pt (some ns[t]!)
    let e ← LayeredM.createEdge
    LayeredM.setEdgeSource e (some ps)
    LayeredM.setEdgeTarget e (some pt)
    es := es.push e
  return ⟨g, ns, es⟩

/-- Runs `setup` and then the phase on its graph. -/
def runPhase (phase : LayeredPhase) (setup : LayeredM Built) : IO (Built × LGraphArena) := do
  let monitor ← ProgressMonitor.basic
  LayeredM.run (do
    let b ← setup
    phase.process b.graph monitor
    return b)

/-- Index of the node's layer in the graph's layer list. -/
def layerIndexOf (a : LGraphArena) (b : Built) (n : LNodeId) : Option Nat :=
  (a.node n).layer.bind fun l => (a.graph b.graph).indexOfLayer l

/-- Layer index of every node (in node creation order). -/
def assignment (a : LGraphArena) (b : Built) : Array (Option Nat) := b.nodes.map (layerIndexOf a b ·)

/-- The layers as lists of node creation indices (in layer order). -/
def layering (a : LGraphArena) (b : Built) : Array (Array Nat) :=
  (a.graph b.graph).layers.map fun l => (a.layer l).nodes.map fun n => (b.nodes.findIdx? (· == n)).getD 999

/-- `assert_no_layerless_nodes`. -/
def noLayerless (a : LGraphArena) (b : Built) : Bool := (a.graph b.graph).layerlessNodes.isEmpty

/-- `assert_no_empty_layers`. -/
def noEmptyLayers (a : LGraphArena) (b : Built) : Bool :=
  (a.graph b.graph).layers.all fun l => !(a.layer l).nodes.isEmpty

/-- Every node is in a layer of the graph. -/
def allPlaced (a : LGraphArena) (b : Built) : Bool := (assignment a b).all (·.isSome)

/-- `assert_edges_point_towards_next_layers` (self-loops are skipped). -/
def edgesForward (a : LGraphArena) (b : Built) : Bool :=
  b.edges.all fun e =>
    if a.edgeIsSelfLoop e then true
    else
      let ed := a.edge e
      let s := ed.source.bind (fun p => (a.port p).owner) |>.bind (layerIndexOf a b ·)
      let t := ed.target.bind (fun p => (a.port p).owner) |>.bind (layerIndexOf a b ·)
      match s, t with
      | some s, some t => s < t
      | _, _ => false

/-- Maximal number of nodes in a layer. -/
def maxWidth (a : LGraphArena) (b : Built) : Nat :=
  (a.graph b.graph).layers.foldl (fun m l => max m (a.layer l).nodes.size) 0

/-- The diamond of `basic_layer_assignment_test.rs`: a→b, a→c, b→d, c→d. -/
def diamond : LayeredM Built := build 4 #[(0, 1), (0, 2), (1, 3), (2, 3)]

/-- A chain 0→1→2 with a shortcut source 3→2. -/
def chainWithShortcut : LayeredM Built := build 4 #[(0, 1), (1, 2), (3, 2)]

/-- Two chains, a single edge and an isolated node: 0→1→2, 3→4, 5. -/
def disconnected : LayeredM Built := build 6 #[(0, 1), (1, 2), (3, 4)]

/-- A larger DAG with a node with `LAYERING_LAYER_CONSTRAINT = FIRST` (the constraint itself is
handled by the requested `LayerConstraintPreprocessor`/`Postprocessor`), optionally with a
self-loop on node 2. -/
def mixed (selfLoop : Bool) : LayeredM Built := do
  let loops : Array (Nat × Nat) := if selfLoop then #[(2, 2)] else #[]
  let b ← build 8 (#[(0, 1), (0, 2)] ++ loops ++ #[(1, 3), (2, 3), (3, 4), (5, 4), (6, 7), (0, 4)])
  LayeredM.setNodeProp b.nodes[5]! LayeredOptions.LAYERING_LAYER_CONSTRAINT LayerConstraint.first
  return b

/-- The basic assertions for one phase and graph. -/
def basicChecks (label : String) (phase : LayeredPhase) (setup : LayeredM Built) : TestM Unit := do
  let (b, a) ← runPhase phase setup
  check s!"{label}: no layerless nodes" (noLayerless a b)
  check s!"{label}: no empty layers" (noEmptyLayers a b)
  check s!"{label}: all nodes placed" (allPlaced a b)
  check s!"{label}: edges point towards next layers" (edgesForward a b)

/-- The phases checked against the generic invariants (all but the model order layerers). -/
def genericPhases : Array LayeredPhase :=
  #[NetworkSimplexLayerer.phase, LongestPathLayerer.phase, LongestPathSourceLayerer.phase,
    CoffmanGrahamLayerer.phase, MinWidthLayerer.phase, StretchWidthLayerer.phase]

def basicTests : Suite := suite "layered.p2layers.basic" do
  for phase in genericPhases do
    basicChecks s!"{phase.name} diamond" phase diamond
    basicChecks s!"{phase.name} chain+shortcut" phase chainWithShortcut
    basicChecks s!"{phase.name} disconnected" phase disconnected
    basicChecks s!"{phase.name} mixed (layer constraint)" phase (mixed false)
  -- self-loops are ignored (Coffman-Graham and StretchWidth do not terminate on them, like Java/Rust)
  for phase in #[NetworkSimplexLayerer.phase, LongestPathLayerer.phase, LongestPathSourceLayerer.phase,
      MinWidthLayerer.phase] do
    basicChecks s!"{phase.name} mixed (self-loop)" phase (mixed true)
  -- interactive with the positions of `apply_interactive_positions` (x = index * 100)
  basicChecks "InteractiveLayerer diamond" InteractiveLayerer.phase
    (build 4 #[(0, 1), (0, 2), (1, 3), (2, 3)] (xs := #[(0, 30), (100, 30), (200, 30), (300, 30)]))
  -- empty graphs are left untouched
  let (b, a) ← runPhase NetworkSimplexLayerer.phase (build 0 #[])
  checkEq "empty graph: no layers" (a.graph b.graph).layers.size 0

def longestPathTests : Suite := suite "layered.p2layers.LongestPath" do
  let (b, a) ← runPhase LongestPathLayerer.phase diamond
  -- hand: heights d=1, b=c=2, a=3; new layers are inserted at the front
  checkEq "diamond layering" (layering a b) #[#[0], #[1, 2], #[3]]
  checkEq "node ids = layerless index" (b.nodes.map fun n => (a.node n).id) #[0, 1, 2, 3]
  let (b, a) ← runPhase LongestPathLayerer.phase chainWithShortcut
  -- hand: heights 2=1, 1=2, 0=3, 3=2 → the shortcut source sits next to 1
  checkEq "chain+shortcut layering (sink aligned)" (layering a b) #[#[0], #[1, 3], #[2]]
  let (b, a) ← runPhase LongestPathSourceLayerer.phase diamond
  checkEq "source: diamond layering" (layering a b) #[#[0], #[1, 2], #[3]]
  let (b, a) ← runPhase LongestPathSourceLayerer.phase chainWithShortcut
  -- hand: heights 0=1, 1=2, 3=1 (visited from 2), 2=3 → the shortcut source sits next to 0
  checkEq "source: chain+shortcut layering (source aligned)" (layering a b) #[#[0, 3], #[1], #[2]]
  let (b, a) ← runPhase LongestPathLayerer.phase disconnected
  -- hand: heights 2=1, 1=2, 0=3, 4=1, 3=2, 5=1
  checkEq "disconnected layering" (assignment a b) #[some 0, some 1, some 2, some 1, some 2, some 2]

def networkSimplexTests : Suite := suite "layered.p2layers.NetworkSimplex" do
  let (b, a) ← runPhase NetworkSimplexLayerer.phase diamond
  -- hand: the unique optimum a=0, b=c=1, d=2; within layer 1 the NGraph node order (DFS a, b, d, c)
  checkEq "diamond layering" (layering a b) #[#[0], #[1, 2], #[3]]
  let (b, a) ← runPhase NetworkSimplexLayerer.phase chainWithShortcut
  -- hand: total edge length 3 only with 3 in layer 1 (layer 0 would give 4)
  checkEq "chain+shortcut layering" (layering a b) #[#[0], #[1, 3], #[2]]
  -- connected components: the largest first, ties keep the discovery order
  let ((comps, ngraph), _) ← LayeredM.run (do
      let b ← build 6 #[(1, 2), (2, 3), (4, 5)]
      let comps ← NetworkSimplexLayerer.connectedComponents b.nodes
      let ngraph ← NetworkSimplexLayerer.initializeGraph comps[0]!
      let comps := comps.map (·.map fun n => (b.nodes.findIdx? (· == n)).getD 999)
      return (comps, ngraph))
  checkEq "components (largest first, then discovery order)" comps #[#[1, 2, 3], #[0], #[4, 5]]
  checkEq "NGraph node count" ngraph.nodeList.size 3
  let edgeEnds := ngraph.edges.map fun e => (e.source.idx, e.target.idx, e.weight, e.delta)
  checkEq "NGraph edges (component order, weight 1, delta 1)" (toString edgeEnds)
    (toString #[(0, 1, 1.0, (1 : Int)), (1, 2, 1.0, (1 : Int))])
  -- DFS order of the diamond component: a, b, d, c
  let (order, _) ← LayeredM.run (do
      let b ← diamond
      let comps ← NetworkSimplexLayerer.connectedComponents b.nodes
      return comps.map (·.map fun n => (b.nodes.findIdx? (· == n)).getD 999))
  checkEq "diamond DFS order" order #[#[0, 1, 3, 2]]
  -- PRIORITY_SHORTNESS weights the network simplex edges
  let (w, _) ← LayeredM.run (do
      let b ← build 2 #[(0, 1)]
      LayeredM.setEdgeProp b.edges[0]! LayeredOptions.PRIORITY_SHORTNESS 5
      let g ← NetworkSimplexLayerer.initializeGraph b.nodes
      return g.edges.map (·.weight))
  checkEq "shortness priority as weight" (toString w) (toString #[5.0])
  let (b, a) ← runPhase NetworkSimplexLayerer.phase disconnected
  check "disconnected: at most 3 layers" ((a.graph b.graph).layers.size <= 3)

def coffmanGrahamTests : Suite := suite "layered.p2layers.CoffmanGraham" do
  let (b, a) ← runPhase CoffmanGrahamLayerer.phase diamond
  -- hand: topo a=0, b=1, c=2, d=3; sinks by descending topo: d | c (in-layer edge to d → new) b | a
  checkEq "diamond layering" (layering a b) #[#[0], #[2, 1], #[3]]
  -- star s→t0..t3 with bound 2
  let star : LayeredM Built := do
    let b ← build 5 #[(0, 1), (0, 2), (0, 3), (0, 4)]
    LayeredM.setGraphProp b.graph LayeredOptions.LAYERING_COFFMAN_GRAHAM_LAYER_BOUND 2
    return b
  let (b, a) ← runPhase CoffmanGrahamLayerer.phase star
  check "star bound 2: width bound" (maxWidth a b <= 2)
  -- hand: topo t0..t3 = 1..4; sinks t3, t2 | t1, t0 | s
  checkEq "star bound 2 layering" (layering a b) #[#[0], #[2, 1], #[4, 3]]
  check "star bound 2: edges forward" (edgesForward a b)
  let diamondBound1 : LayeredM Built := do
    let b ← diamond
    LayeredM.setGraphProp b.graph LayeredOptions.LAYERING_COFFMAN_GRAHAM_LAYER_BOUND 1
    return b
  let (b, a) ← runPhase CoffmanGrahamLayerer.phase diamondBound1
  checkEq "diamond bound 1: one node per layer" (layering a b) #[#[0], #[1], #[2], #[3]]
  -- transitive edge a→c of a→b→c is ignored; edge ids are re-assigned in node/outgoing order
  let transitive : LayeredM Built := do
    let b ← build 3 #[(0, 1), (1, 2), (0, 2)]
    for e in b.edges do LayeredM.modifyEdge e fun x => { x with id := 100 }
    return b
  let (b, a) ← runPhase CoffmanGrahamLayerer.phase transitive
  checkEq "transitive reduction layering" (layering a b) #[#[0], #[1], #[2]]
  checkEq "edge ids re-assigned" (b.edges.map fun e => (a.edge e).id) #[0, 2, 1]
  -- the topological priority
  checkEqR "compareNodesInTopo by largest differing number" (CoffmanGrahamLayerer.compareNodesInTopo #[#[0, 3], #[1, 3]] 0 1) .lt
  checkEqR "compareNodesInTopo tie → ids" (CoffmanGrahamLayerer.compareNodesInTopo #[#[2], #[1, 2]] 1 0) .gt
  checkEq "popBestBy takes the first minimum (swap_remove)"
    (CoffmanGrahamLayerer.popBestBy #[3, 1, 2, 1] (· < ·)) (some (1, #[3, 1, 2]))

def minWidthTests : Suite := suite "layered.p2layers.MinWidth" do
  -- `min_width_keeps_input_order_of_out_degree_ties`: sinks t0..t4, source s with an edge to each sink
  let star : LayeredM Built := build 6 #[(5, 0), (5, 1), (5, 2), (5, 3), (5, 4)]
  let (b, a) ← runPhase MinWidthLayerer.phase star
  checkEq "keeps input order of out-degree ties" ((layering a b).map fun l => stableSort l compare)
    #[#[5], #[4], #[0, 1, 2, 3]]
  -- upper bound on width 1 / compensator 1: smaller layers
  let narrow : LayeredM Built := do
    let b ← star
    LayeredM.setGraphProp b.graph LayeredOptions.LAYERING_MIN_WIDTH_UPPER_BOUND_ON_WIDTH 1
    LayeredM.setGraphProp b.graph LayeredOptions.LAYERING_MIN_WIDTH_UPPER_LAYER_ESTIMATION_SCALING_FACTOR 1
    return b
  let (b, a) ← runPhase MinWidthLayerer.phase narrow
  check "ubw 1: width bound (one sink per layer)" (maxWidth a b <= 1)
  check "ubw 1: edges forward" (edgesForward a b)
  -- negative options select the parameter ranges
  let ranges : LayeredM Built := do
    let b ← star
    LayeredM.setGraphProp b.graph LayeredOptions.LAYERING_MIN_WIDTH_UPPER_BOUND_ON_WIDTH (-1)
    LayeredM.setGraphProp b.graph LayeredOptions.LAYERING_MIN_WIDTH_UPPER_LAYER_ESTIMATION_SCALING_FACTOR (-1)
    return b
  let (b, a) ← runPhase MinWidthLayerer.phase ranges
  check "parameter ranges: valid layering" (noEmptyLayers a b && allPlaced a b && edgesForward a b)

def interactiveTests : Suite := suite "layered.p2layers.Interactive" do
  let (b, a) ← runPhase InteractiveLayerer.phase
    (build 4 #[(0, 1), (0, 2), (1, 3), (2, 3)] (xs := #[(0, 30), (100, 30), (200, 30), (300, 30)]))
  checkEq "diamond from positions" (layering a b) #[#[0], #[1], #[2], #[3]]
  checkEq "layer ids = span index" ((a.graph b.graph).layers.map fun l => (a.layer l).id) #[0, 1, 2, 3]
  -- overlapping nodes share a span; the correction moves targets behind their sources
  let (b, a) ← runPhase InteractiveLayerer.phase
    (build 3 #[(0, 1), (1, 2)] (xs := #[(0, 30), (10, 30), (100, 30)]))
  checkEq "topology correction" (layering a b) #[#[0], #[1], #[2]]
  check "topology correction: edges forward" (edgesForward a b)
  -- a wide node merges two spans; zero width counts as width 1
  let (b, a) ← runPhase InteractiveLayerer.phase (build 3 #[] (xs := #[(0, 30), (100, 30), (20, 100)]))
  checkEq "span merging" (layering a b) #[#[0, 2, 1]]
  let (b, a) ← runPhase InteractiveLayerer.phase (build 2 #[] (xs := #[(5, 0), (5.5, 0)]))
  checkEq "zero width nodes overlap within one unit" (layering a b) #[#[0, 1]]
  -- spans are sorted by position, not by node order
  let (b, a) ← runPhase InteractiveLayerer.phase (build 3 #[] (xs := #[(200, 30), (0, 30), (100, 30)]))
  checkEq "spans sorted by x" (layering a b) #[#[1], #[2], #[0]]

/-- Sets the model order of the nodes (`InternalProperties.MODEL_ORDER`). -/
def withModelOrder (setup : LayeredM Built) (orders : Array (Option Int)) : LayeredM Built := do
  let b ← setup
  for h : i in [0:b.nodes.size] do
    let order := orders.getD i none
    LayeredM.modifyNode b.nodes[i] fun x => { x with internal := { x.internal with modelOrder := order } }
  return b

def modelOrderTests : Suite := suite "layered.p2layers.ModelOrder" do
  let tree := withModelOrder (build 4 #[(0, 1), (1, 2), (0, 3)]) #[some 0, some 1, some 2, some 3]
  let (b, a) ← runPhase BreadthFirstModelOrderLayerer.phase tree
  -- hand: 1 is connected to the current layer → new layers; 2 connected → new; 3 not → current
  checkEq "BF layering" (layering a b) #[#[0], #[1], #[2, 3]]
  checkEq "BF layer ids re-indexed" ((a.graph b.graph).layers.map fun l => (a.layer l).id) #[0, 1, 2]
  check "BF no empty layers" (noEmptyLayers a b && noLayerless a b)
  let (b, a) ← runPhase DepthFirstModelOrderLayerer.phase tree
  -- hand: 3 is not connected to the current layer (4) → placed behind its predecessor 0 (layer 2)
  checkEq "DF layering" (layering a b) #[#[0], #[1, 3], #[2]]
  checkEq "DF layer ids re-indexed" ((a.graph b.graph).layers.map fun l => (a.layer l).id) #[0, 1, 2]
  -- model order decides, not the node order
  let reversed := withModelOrder (build 3 #[(2, 1), (1, 0)]) #[some 2, some 1, some 0]
  let (b, a) ← runPhase BreadthFirstModelOrderLayerer.phase reversed
  checkEq "BF follows the model order" (layering a b) #[#[2], #[1], #[0]]
  -- DF: a second source starts a pending chain in layer 0
  let twoChains := withModelOrder (build 4 #[(0, 1), (2, 3)]) #[some 0, some 1, some 2, some 3]
  let (b, a) ← runPhase DepthFirstModelOrderLayerer.phase twoChains
  checkEq "DF pending chain" (layering a b) #[#[0, 2], #[1, 3]]
  let (b, a) ← runPhase BreadthFirstModelOrderLayerer.phase twoChains
  checkEq "BF two chains" (layering a b) #[#[0], #[1, 2], #[3]]
  -- label dummies between connected nodes go into the dummy layer
  let withLabel := withModelOrder (build 3 #[(0, 1), (1, 2)] (types := #[.normal, .label, .normal]))
    #[some 0, none, some 1]
  let (b, a) ← runPhase BreadthFirstModelOrderLayerer.phase withLabel
  checkEq "BF label dummy layer" (layering a b) #[#[0], #[1], #[2]]
  let (b, a) ← runPhase DepthFirstModelOrderLayerer.phase withLabel
  checkEq "DF label dummy layer" (layering a b) #[#[0], #[1], #[2]]
  -- real nodes need a model order
  checkThrows "BF requires model orders" (do
    let _ ← runPhase BreadthFirstModelOrderLayerer.phase (withModelOrder (build 2 #[(0, 1)]) #[some 0, none])
    pure ())
  checkThrows "DF requires model orders" (do
    let _ ← runPhase DepthFirstModelOrderLayerer.phase (withModelOrder (build 2 #[(0, 1)]) #[none, some 0])
    pure ())

/-- The processor configuration requested by the phase of `strategy`. -/
def configurationOf (strategy : LayeringStrategy) : IO LayeredProcessorConfiguration := do
  let (c, _) ← LayeredM.run (do
    let b ← diamond
    strategy.createPhase.getLayoutProcessorConfiguration b.graph)
  return c.getD {}

def configurationTests : Suite := suite "layered.p2layers.configuration" do
  for strategy in ElkEnum.values (α := LayeringStrategy) do
    let c ← configurationOf strategy
    let first : IntermediateProcessorStrategy :=
      if strategy == .interactive then .interactiveExternalPortPositioner else .edgeAndLayerConstraintEdgeReverser
    let name := ElkEnum.javaName strategy
    checkEq s!"{name}: before P1" (c.processorsBefore .p1CycleBreaking) #[first]
    checkEq s!"{name}: before P2" (c.processorsBefore .p2Layering) #[.layerConstraintPreprocessor]
    checkEq s!"{name}: before P3" (c.processorsBefore .p3NodeOrdering) #[.layerConstraintPostprocessor]
    checkEq s!"{name}: nothing after P3" (c.processorsAfter .p3NodeOrdering) #[]

def registrationTests : Suite := suite "layered.p2layers.registration" do
  let expected : Array (LayeringStrategy × String) :=
    #[(.networkSimplex, "NetworkSimplexLayerer"), (.longestPath, "LongestPathLayerer"),
      (.longestPathSource, "LongestPathSourceLayerer"), (.coffmanGraham, "CoffmanGrahamLayerer"),
      (.interactive, "InteractiveLayerer"), (.stretchWidth, "StretchWidthLayerer"),
      (.minWidth, "MinWidthLayerer"), (.bfModelOrder, "BreadthFirstModelOrderLayerer"),
      (.dfModelOrder, "DepthFirstModelOrderLayerer")]
  for (strategy, name) in expected do
    checkEq s!"createPhase {ElkEnum.javaName strategy}" strategy.createPhase.name name
    let factory := LayeredPhases.strategyFactory .p2Layering "LayeringStrategy" (ElkEnum.ordinal strategy) (ElkEnum.javaName strategy)
    let phase ← factory.create
    checkEq s!"registered {ElkEnum.javaName strategy}" phase.name name

def suites : Array Tests.Suite :=
  #[basicTests, longestPathTests, networkSimplexTests, coffmanGrahamTests, minWidthTests, interactiveTests,
    modelOrderTests, configurationTests, registrationTests]

end Tests.Layered.P2Layers
