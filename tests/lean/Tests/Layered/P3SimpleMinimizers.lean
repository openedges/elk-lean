import Tests.Framework
import Tests.Layered.P3Counting
import Elk.Alg.Layered
import Elk.Alg.Layered.P3Order.SimpleMinimizers
/-!
Tests of `InteractiveCrossingMinimizer` and `NoCrossingMinimizer`, ported from elk-rs
`tests/p3_order/interactive_crossing_minimizer_test.rs` (check names contain the Rust test names)
and hand-derived checks ("hand: ..."). The Rust test drives the phase through
`CrossingMinimizationStrategy::Interactive.create_phase()` on hand-built layered graphs; here the
phase comes from `LayeredPhases.strategyFactory`, the graphs are built with the arena helpers.
The pipeline-driven elk-rs assertions have no counterpart: the layout pipeline is not wired for
these phases yet.
-/
namespace Tests.Layered.P3SimpleMinimizers

open Tests Elk.Graph Elk.Core.Math Elk.Core.Options Elk.Core.Util Elk.Core.Alg
open Elk.Alg.Layered Elk.Alg.Layered.Graph Elk.Alg.Layered.Options Elk.Alg.Layered.Intermediate
open Elk.Alg.Layered.P3Order
open Tests.Layered.P3Counting (Cfg newGraph makeLayer addPort connect runL)
open Elk (ElkEnum)
open LayeredM

/-! ## Builders -/

/-- A node of the given geometry and type, appended to layer `l`. -/
def addN (g : LGraphId) (l : LayerId) (x y w h : Float) (t : NodeType := .normal) : LayeredM LNodeId := do
  let n ← createNode g { position := ⟨x, y⟩, size := ⟨w, h⟩, type := t }
  setNodeLayer n (some l)
  return n

/-- A port at absolute position `(x, y)` (anchor `(0, 0)`) on a fresh node outside all layers. -/
def anchorPort (g : LGraphId) (x y : Float) : LayeredM LPortId := do
  let owner ← createNode g { position := ⟨x, y⟩ }
  let p ← createPort
  setPortNode p (some owner)
  return p

/-- A long edge dummy at `(x, 0)` (size `0 x 0`) whose origin edge has the given bend points. -/
def addLongEdge (g : LGraphId) (l : LayerId) (x : Float) (bends : Array KVector) (reversed : Bool := false)
    (src : Option LPortId := none) (tgt : Option LPortId := none) : LayeredM LNodeId := do
  let e ← createEdge { bendPoints := bends, internal := { reversed := reversed } }
  let n ← addN g l x 0 0 0 .longEdge
  modifyNode n fun d => { d with internal := { d.internal with
    origin := some (.lEdge e), longEdgeSource := src, longEdgeTarget := tgt } }
  return n

/-- A north/south dummy at `y` whose single port stems from a port of `origin` on `side`. -/
def addNsDummy (g : LGraphId) (l : LayerId) (y : Float) (origin : LNodeId) (side : PortSide) : LayeredM LNodeId := do
  let n ← addN g l 0 y 0 0 .northSouthPort
  let originPort ← createPort
  modifyPort originPort (·.setSide side)
  setPortNode originPort (some origin)
  let dummyPort ← createPort
  setPortNode dummyPort (some n)
  modifyPort dummyPort fun p => { p with internal := { p.internal with origin := some (.lPort originPort) } }
  return n

/-- The nodes of a layer. -/
def nodesOf (l : LayerId) : LayeredM (Array LNodeId) := do return (← getLayer l).nodes

/-- Runs a phase with the null monitor. -/
def runPhase (phase : LayeredPhase) (g : LGraphId) : LayeredM Unit := phase.process g ProgressMonitor.null

/-- Runs the interactive minimizer. -/
def runInteractive (g : LGraphId) : LayeredM Unit := runPhase InteractiveCrossingMinimizer.phase g

/-- A graph with one layer. -/
def singleLayer : LayeredM (LGraphId × LayerId) := do
  let g ← newGraph {}
  return (g, ← makeLayer g)

/-- `ORIGINAL_DUMMY_NODE_POSITION` of a node. -/
def dummyPos (n : LNodeId) : LayeredM (Option Float) := do return (← getNode n).internal.originalDummyNodePosition

/-- The phase registered for a crossing minimization strategy. -/
def phaseOf (s : CrossingMinimizationStrategy) : IO LayeredPhase :=
  (LayeredPhases.strategyFactory .p3NodeOrdering "CrossingMinimizationStrategy" (ElkEnum.ordinal s)
    (ElkEnum.javaName s)).create

/-! ## `interactive_crossing_minimizer_test.rs` -/

def rustTests : Suite := suite "layered.p3order.interactive_crossing_minimizer" do
  let phase ← phaseOf .interactive
  checkEq "interactive_strategy_creates_interactive_crossing_minimizer_phase" phase.name "InteractiveCrossingMinimizer"
  -- sorts layer and sets dummy position
  let ((normal, dummy, order, pos, normalPos), _) ← LayeredM.run (do
    let (g, l) ← singleLayer
    let normal ← addN g l 0 100 0 20
    let dummy ← addN g l 0 20 0 10 .longEdge
    runInteractive g
    return (normal, dummy, ← nodesOf l, ← dummyPos dummy, ← dummyPos normal))
  check "interactive_crossing_minimizer_sorts_layer_and_sets_dummy_position (order)" (order == #[dummy, normal])
  match pos with
  | some p => checkFloat "interactive_crossing_minimizer_sorts_layer_and_sets_dummy_position (dummy y center 25)" p 25.0 1e-6
  | none => check "interactive_crossing_minimizer_sorts_layer_and_sets_dummy_position (position set)" false
  checkNone "hand: only long edge dummies get ORIGINAL_DUMMY_NODE_POSITION" normalPos
  -- successor constraints on ties
  let ((a, b, order), _) ← LayeredM.run (do
    let (g, l) ← singleLayer
    let a ← addN g l 0 0 0 0
    let b ← addN g l 0 0 0 0
    modifyNode a fun x => { x with internal := { x.internal with inLayerSuccessorConstraints := #[b] } }
    -- start in reverse order
    modifyLayer l fun x => { x with nodes := #[b, a] }
    runInteractive g
    return (a, b, ← nodesOf l))
  check "interactive_crossing_minimizer_respects_in_layer_successor_constraints_on_ties" (order == #[a, b])

/-! ## Reference points, ids, stability -/

def sortingTests : Suite := suite "layered.p3order.interactive_crossing_minimizer.sorting" do
  -- center vs top-left
  let center ← runL (do
    let (g, l) ← singleLayer
    let a ← addN g l 0 0 0 100
    let b ← addN g l 0 30 0 10
    runInteractive g
    return (← nodesOf l) == #[b, a])
  check "hand: CENTER reference: B (35) before A (50)" center
  let topLeft ← runL (do
    let (g, l) ← singleLayer
    setGraphProp g LayeredOptions.INTERACTIVE_REFERENCE_POINT InteractiveReferencePoint.topLeft
    let b ← addN g l 0 30 0 10
    let a ← addN g l 0 0 0 100
    runInteractive g
    return (← nodesOf l) == #[a, b])
  check "hand: TOP_LEFT reference: A (0) before B (30)" topLeft
  -- stability
  let stable ← runL (do
    let (g, l) ← singleLayer
    let ns ← [0, 1, 2, 3].toArray.mapM fun _ => addN g l 0 10 0 0
    runInteractive g
    return (← nodesOf l) == ns)
  check "hand: equal positions keep the input order (stable)" stable
  let mixed ← runL (do
    let (g, l) ← singleLayer
    let c ← addN g l 0 50 0 0
    let a1 ← addN g l 0 10 0 0
    let b ← addN g l 0 30 0 0
    let a2 ← addN g l 0 10 0 0
    runInteractive g
    return (← nodesOf l) == #[a1, a2, b, c])
  check "hand: y 50, 10, 30, 10 sorts to [10 (first), 10 (second), 30, 50]" mixed
  -- layers are independent
  let layers ← runL (do
    let g ← newGraph {}
    let l0 ← makeLayer g
    let l1 ← makeLayer g
    let a ← addN g l0 0 80 0 0
    let b ← addN g l0 0 5 0 0
    let c ← addN g l1 0 1 0 0
    let d ← addN g l1 0 0 0 0
    runInteractive g
    return (← nodesOf l0) == #[b, a] && (← nodesOf l1) == #[d, c])
  check "hand: two layers are sorted independently" layers
  -- ids
  let ids ← runL (do
    let g ← newGraph {}
    let l0 ← makeLayer g
    let l1 ← makeLayer g
    let a ← addN g l0 0 80 0 0
    let b ← addN g l0 0 5 0 0
    let c ← addN g l1 0 1 0 0
    let _ ← addPort {} a .east
    let _ ← addPort {} a .east
    let _ ← addPort {} b .east
    let pc ← addPort {} c .west
    runInteractive g
    return (#[(← getLayer l0).id, (← getLayer l1).id], #[(← getNode a).id, (← getNode b).id, (← getNode c).id],
      (← getPort pc).id))
  checkEqR "hand: layer ids are the layer indices" ids.1 #[0, 1]
  checkEqR "hand: node ids are the pre-sort indices in the layer" ids.2.1 #[0, 1, 0]
  checkEqR "hand: port ids count over the layers in pre-sort order" ids.2.2 3
  -- degenerate graphs
  let empty ← runL (do
    let g ← newGraph {}
    runInteractive g
    let l ← makeLayer g
    runInteractive g
    return (← nodesOf l).isEmpty)
  check "hand: an empty graph and an empty layer are fine" empty
  let sameAsSingle ← runL (do
    let (g, l) ← singleLayer
    let a ← addN g l 0 7 0 0
    runInteractive g
    return (← nodesOf l) == #[a] && (← getNode a).id == 0)
  check "hand: a single node stays and gets id 0" sameAsSingle

/-! ## Long edge dummies -/

/-- Position of a long edge dummy that is alone in its layer. -/
def longEdgeY (build : LGraphId → LayerId → LayeredM LNodeId) : IO (Option Float) :=
  runL (do
    let (g, l) ← singleLayer
    let d ← build g l
    runInteractive g
    dummyPos d)

def expectPos (name : String) (actual : Option Float) (expected : Float) : TestM Unit :=
  match actual with
  | some p => checkFloat name p expected
  | none => check name false

def longEdgeTests : Suite := suite "layered.p3order.interactive_crossing_minimizer.long_edge_dummies" do
  expectPos "hand: line (0,0)-(100,100) at x = 50 gives y = 50"
    (← longEdgeY fun g l => addLongEdge g l 50 #[⟨0, 0⟩, ⟨100, 100⟩]) 50.0
  expectPos "hand: line (0,0)-(100,40) at x = 25 gives y = 10"
    (← longEdgeY fun g l => addLongEdge g l 25 #[⟨0, 0⟩, ⟨100, 40⟩]) 10.0
  -- reversed edges use the reversed chain [(100,100), (50,100), (0,0)]: segment (100,100)-(50,100)
  expectPos "hand: not reversed (0,0),(50,100),(100,100) at x = 25 gives y = 50"
    (← longEdgeY fun g l => addLongEdge g l 25 #[⟨0, 0⟩, ⟨50, 100⟩, ⟨100, 100⟩]) 50.0
  expectPos "hand: reversed chain starts with the last point, segment (100,100)-(50,100) gives y = 100"
    (← longEdgeY fun g l => addLongEdge g l 25 #[⟨0, 0⟩, ⟨50, 100⟩, ⟨100, 100⟩] (reversed := true)) 100.0
  -- source and target anchors
  expectPos "hand: x left of the source anchor (10, 65) gives its y"
    (← longEdgeY fun g l => do
      let s ← anchorPort g 10 65
      addLongEdge g l 5 #[⟨0, 0⟩, ⟨100, 100⟩] (src := some s)) 65.0
  expectPos "hand: x right of the target anchor (30, 77) gives its y"
    (← longEdgeY fun g l => do
      let t ← anchorPort g 30 77
      addLongEdge g l 50 #[⟨0, 0⟩, ⟨100, 100⟩] (tgt := some t)) 77.0
  expectPos "hand: target anchor (200, 80) appended to the single point (0, 0) at x = 50 gives y = 20"
    (← longEdgeY fun g l => do
      let t ← anchorPort g 200 80
      addLongEdge g l 50 #[⟨0, 0⟩] (tgt := some t)) 20.0
  expectPos "hand: source (0,0), bend (50,0), target (100,100) at x = 75 gives y = 50"
    (← longEdgeY fun g l => do
      let s ← anchorPort g 0 0
      let t ← anchorPort g 100 100
      addLongEdge g l 75 #[⟨50, 0⟩] (src := some s) (tgt := some t)) 50.0
  expectPos "hand: anchor offsets count: node (0,60) + port (10,5) + anchor (2,3) gives x 12, y 68"
    (← longEdgeY fun g l => do
      let owner ← createNode g { position := ⟨0, 60⟩ }
      let p ← createPort { position := ⟨10, 5⟩, anchor := ⟨2, 3⟩ }
      setPortNode p (some owner)
      addLongEdge g l 5 #[] (src := some p)) 68.0
  expectPos "hand: zero x distance gives the second point's y (|dx| <= EPSILON)"
    (← longEdgeY fun g l => addLongEdge g l 10 #[⟨10, 5⟩, ⟨10, 9⟩]) 9.0
  -- fallbacks to the reference point (size 0, y 0 -> centre 0)
  expectPos "hand: fewer than two points falls back to the centre (y 0 + 0/2)"
    (← longEdgeY fun g l => addLongEdge g l 10 #[⟨10, 5⟩]) 0.0
  expectPos "hand: no origin edge falls back to the reference point"
    (← longEdgeY fun g l => do
      let n ← addN g l 3 40 0 10 .longEdge
      return n) 45.0
  -- horizontal position: mean over the nodes with x > 0
  let horiz ← runL (do
    let (g, l) ← singleLayer
    let _ ← addN g l 10 300 20 0
    let _ ← addN g l 0 300 0 0
    let d ← addLongEdge g l 40 #[⟨0, 0⟩, ⟨60, 60⟩]
    runInteractive g
    dummyPos d)
  expectPos "hand: horizPos = ((10 + 20/2) + 40) / 2 = 30 (node at x = 0 not counted) gives y = 30" horiz 30.0
  -- the dummy is placed among normal nodes by the interpolated position
  let order ← runL (do
    let (g, l) ← singleLayer
    let d ← addLongEdge g l 50 #[⟨0, 0⟩, ⟨100, 100⟩]
    let n ← addN g l 0 30 0 10
    let m ← addN g l 0 90 0 0
    runInteractive g
    return (← nodesOf l) == #[n, d, m])
  check "hand: dummy (y 50) between node centre 35 and node 90" order

/-! ## North/south dummies and in-layer constraints -/

def northSouthTests : Suite := suite "layered.p3order.interactive_crossing_minimizer.north_south" do
  let order ← runL (do
    let (g, l) ← singleLayer
    let x ← addN g l 0 100 50 40
    let south ← addNsDummy g l 1000 x .south
    let north ← addNsDummy g l 1000 x .north
    runInteractive g
    return (← nodesOf l) == #[north, x, south])
  check "hand: north dummy at 100 < node centre 120 < south dummy at 140" order
  let ordinaryPos ← runL (do
    let (g, l) ← singleLayer
    let x ← addN g l 0 100 50 40
    let south ← addNsDummy g l 1000 x .south
    runInteractive g
    dummyPos south)
  checkNone "hand: north/south dummies do not get ORIGINAL_DUMMY_NODE_POSITION" ordinaryPos
  let east ← runL (do
    let (g, l) ← singleLayer
    let x ← addN g l 0 100 50 40
    let d ← addNsDummy g l 500 x .east
    let low ← addN g l 0 200 0 0
    runInteractive g
    return (← nodesOf l) == #[x, low, d])
  check "hand: origin port on an east side falls back to the dummy's own centre (500)" east
  let tie ← runL (do
    let (g, l) ← singleLayer
    setGraphProp g LayeredOptions.INTERACTIVE_REFERENCE_POINT InteractiveReferencePoint.topLeft
    let x ← addN g l 0 100 50 40
    let north ← addNsDummy g l 0 x .north
    modifyNode north fun d => { d with internal := { d.internal with inLayerSuccessorConstraints := #[x] } }
    runInteractive g
    return (← nodesOf l) == #[north, x])
  check "hand: TOP_LEFT tie (100 = 100) resolved by the north dummy's successor constraint" tie
  let missingOrigin ← runL (do
    let (g, l) ← singleLayer
    let d ← addN g l 0 5 0 10 .northSouthPort
    let a ← addN g l 0 9 0 0
    runInteractive g
    return (← nodesOf l) == #[a, d])
  -- dummy without ports: centre 5 + 10 / 2 = 10 > 9
  check "hand: north/south dummy without port falls back to the centre (10 > 9)" missingOrigin

def constraintTests : Suite := suite "layered.p3order.interactive_crossing_minimizer.constraints" do
  let pairs ← runL (do
    let (g, l) ← singleLayer
    let a ← addN g l 0 0 0 0
    let b ← addN g l 0 0 0 0
    let c ← addN g l 0 0 0 0
    let d ← addN g l 0 0 0 0
    modifyNode a fun x => { x with internal := { x.internal with inLayerSuccessorConstraints := #[b] } }
    modifyNode c fun x => { x with internal := { x.internal with inLayerSuccessorConstraints := #[d] } }
    modifyLayer l fun x => { x with nodes := #[b, a, d, c] }
    runInteractive g
    return (← nodesOf l) == #[a, b, c, d])
  check "hand: pairwise constraints a->b, c->d on a tie: [b, a, d, c] -> [a, b, c, d]" pairs
  let ignoredOnDifferentPositions ← runL (do
    let (g, l) ← singleLayer
    let a ← addN g l 0 20 0 0
    let b ← addN g l 0 10 0 0
    modifyNode a fun x => { x with internal := { x.internal with inLayerSuccessorConstraints := #[b] } }
    runInteractive g
    return (← nodesOf l) == #[b, a])
  check "hand: constraints are only tie breakers (b at 10 stays before a at 20)" ignoredOnDifferentPositions
  let nodeSucc ← runL (do
    let (g, l) ← singleLayer
    let a ← addN g l 0 0 0 0
    let b ← addN g l 0 0 0 0
    modifyNode b fun x => { x with internal := { x.internal with inLayerSuccessorConstraints := #[a] } }
    runInteractive g
    return (← nodesOf l) == #[b, a])
  check "hand: second node's constraint moves it first on a tie" nodeSucc
  check "hand: compareEntries is Less for a constraint of the first, Greater for the second"
    (InteractiveCrossingMinimizer.compareEntries ⟨⟨0⟩, 1.0, #[⟨1⟩]⟩ ⟨⟨1⟩, 1.0, #[]⟩ == .lt
      && InteractiveCrossingMinimizer.compareEntries ⟨⟨0⟩, 1.0, #[]⟩ ⟨⟨1⟩, 1.0, #[⟨0⟩]⟩ == .gt
      && InteractiveCrossingMinimizer.compareEntries ⟨⟨0⟩, 1.0, #[]⟩ ⟨⟨1⟩, 1.0, #[]⟩ == .eq
      && InteractiveCrossingMinimizer.compareEntries ⟨⟨0⟩, 1.0, #[]⟩ ⟨⟨1⟩, 2.0, #[]⟩ == .lt)
  check "hand: NaN positions compare equal (partial_cmp.unwrap_or(Equal))"
    (InteractiveCrossingMinimizer.compareEntries ⟨⟨0⟩, 0.0 / 0.0, #[]⟩ ⟨⟨1⟩, 1.0, #[]⟩ == .eq)

/-! ## Port distribution -/

/-- Two layers: `a` (y 0) and `b` (y 100) in front of `c`, whose two west ports are crossed:
the first port is connected to `a` (upper), the second to `b` (lower); west ports run clockwise
(bottom to top), so the order is crossed and must be reversed. -/
def crossedPorts (constraints : Option PortConstraints) : LayeredM (Array LPortId × Array LPortId) := do
  let cfg : Cfg := { fixSide := true }
  let g ← newGraph cfg
  let l0 ← makeLayer g
  let l1 ← makeLayer g
  let a ← addN g l0 0 0 0 0
  let b ← addN g l0 0 100 0 0
  let c ← addN g l1 0 0 0 0
  let pa ← addPort cfg a .east
  let pb ← addPort cfg b .east
  let pc1 ← addPort cfg c .west
  let pc2 ← addPort cfg c .west
  connect pa pc1
  connect pb pc2
  for n in [a, b, c] do cachePortSides n
  if let some pcs := constraints then
    setNodeProp c LayeredOptions.PORT_CONSTRAINTS pcs
  runInteractive g
  return (#[pc2, pc1], (← getNode c).ports)

def portTests : Suite := suite "layered.p3order.interactive_crossing_minimizer.port_distribution" do
  let (expected, actual) ← runL (crossedPorts none)
  check "hand: crossed western ports of c (clockwise: upper first) are swapped by the node-relative distribution" (actual == expected)
  let (expected, actual) ← runL (crossedPorts (some PortConstraints.fixedOrder))
  check "hand: FIXED_ORDER ports keep their order (original [pc1, pc2])" (actual == expected.reverse)

/-! ## Configurations and registration -/

def lt3 (c : LayeredProcessorConfiguration) : Array IntermediateProcessorStrategy × Array IntermediateProcessorStrategy
    × Array IntermediateProcessorStrategy × Array IntermediateProcessorStrategy :=
  (c.processorsBefore .p3NodeOrdering, c.processorsBefore .p4NodePlacement, c.processorsAfter .p5EdgeRouting,
    c.processorsBefore .p1CycleBreaking ++ c.processorsBefore .p2Layering ++ c.processorsBefore .p5EdgeRouting)

def configTests : Suite := suite "layered.p3order.simple_minimizers.configuration" do
  let ((plain, nonFree, noPlain), _) ← LayeredM.run (do
    let g ← newGraph {}
    let plain ← InteractiveCrossingMinimizer.phase.getLayoutProcessorConfiguration g
    modifyGraph g fun x => { x with
      internal := { x.internal with graphProperties := x.internal.graphProperties.insert .nonFreePorts } }
    let nonFree ← InteractiveCrossingMinimizer.phase.getLayoutProcessorConfiguration g
    let noPlain ← NoCrossingMinimizer.phase.getLayoutProcessorConfiguration g
    return (plain, nonFree, noPlain))
  let plain := plain.getD default
  let nonFree := nonFree.getD default
  let noPlain := noPlain.getD default
  checkEqR "hand: interactive before P3 = [LongEdgeSplitter]" (lt3 plain).1 #[IntermediateProcessorStrategy.longEdgeSplitter]
  checkEqR "hand: interactive before P4 = [InLayerConstraintProcessor]" (lt3 plain).2.1
    #[IntermediateProcessorStrategy.inLayerConstraintProcessor]
  checkEqR "hand: interactive after P5 = [LongEdgeJoiner]" (lt3 plain).2.2.1 #[IntermediateProcessorStrategy.longEdgeJoiner]
  checkEqR "hand: interactive requests nothing else" (lt3 plain).2.2.2 #[]
  checkEqR "hand: interactive with NON_FREE_PORTS adds PortListSorter after LongEdgeSplitter"
    (lt3 nonFree).1 #[IntermediateProcessorStrategy.longEdgeSplitter, IntermediateProcessorStrategy.portListSorter]
  checkEqR "hand: NON_FREE_PORTS leaves P4 and P5 slots alone" ((lt3 nonFree).2.1, (lt3 nonFree).2.2.1)
    ((lt3 plain).2.1, (lt3 plain).2.2.1)
  checkEqR "hand: none before P3 = [LongEdgeSplitter, PortListSorter] without NON_FREE_PORTS"
    (lt3 noPlain).1 #[IntermediateProcessorStrategy.longEdgeSplitter, IntermediateProcessorStrategy.portListSorter]
  checkEqR "hand: none before P4 = [InLayerConstraintProcessor]" (lt3 noPlain).2.1
    #[IntermediateProcessorStrategy.inLayerConstraintProcessor]
  checkEqR "hand: none after P5 = [LongEdgeJoiner]" (lt3 noPlain).2.2.1 #[IntermediateProcessorStrategy.longEdgeJoiner]
  checkEqR "hand: none requests nothing else" (lt3 noPlain).2.2.2 #[]
  checkEqR "hand: the shared static configuration is not modified by the NON_FREE_PORTS case"
    InteractiveCrossingMinimizer.intermediateProcessingConfiguration.list.size 6

def registrationTests : Suite := suite "layered.p3order.simple_minimizers.registration" do
  let interactive ← phaseOf .interactive
  let none' ← phaseOf .none
  checkEq "CrossingMinimizationStrategy.INTERACTIVE creates InteractiveCrossingMinimizer" interactive.name
    "InteractiveCrossingMinimizer"
  checkEq "CrossingMinimizationStrategy.NONE creates NoCrossingMinimizer" none'.name "NoCrossingMinimizer"
  let f := LayeredPhases.strategyFactory .p3NodeOrdering "CrossingMinimizationStrategy"
    (ElkEnum.ordinal CrossingMinimizationStrategy.interactive) "INTERACTIVE"
  check "hand: the factory key is (enum name, ordinal)"
    (f.key == some ("CrossingMinimizationStrategy", ElkEnum.ordinal CrossingMinimizationStrategy.interactive))
  check "hand: the two phases are not hierarchy aware" (!interactive.isHierarchyAware && !none'.isHierarchyAware)

/-! ## `NoCrossingMinimizer` -/

def noCrossingTests : Suite := suite "layered.p3order.no_crossing_minimizer" do
  let r ← runL (do
    let cfg : Cfg := {}
    let g ← newGraph cfg
    let l0 ← makeLayer g
    let l1 ← makeLayer g
    let a ← addN g l0 0 80 0 0
    let b ← addN g l0 0 5 0 0
    let d ← addN g l0 0 1 0 0 .longEdge
    let c ← addN g l1 0 1 0 0
    let p1 ← addPort cfg c .west
    let p2 ← addPort cfg c .west
    modifyNode a fun x => { x with id := 7 }
    modifyPort p1 fun x => { x with id := 11 }
    modifyLayer l0 fun x => { x with id := 5 }
    runPhase NoCrossingMinimizer.phase g
    return ((← nodesOf l0) == #[a, b, d], (← nodesOf l1) == #[c], (← getNode c).ports == #[p1, p2],
      (← getNode a).id, (← getPort p1).id, (← getLayer l0).id, ← dummyPos d))
  check "hand: node order unchanged although positions differ" r.1
  check "hand: second layer unchanged" r.2.1
  check "hand: port order unchanged" r.2.2.1
  checkEqR "hand: node id untouched" r.2.2.2.1 7
  checkEqR "hand: port id untouched" r.2.2.2.2.1 11
  checkEqR "hand: layer id untouched" r.2.2.2.2.2.1 5
  checkNone "hand: no ORIGINAL_DUMMY_NODE_POSITION" r.2.2.2.2.2.2
  checkEq "phase name (Rust struct name)" NoCrossingMinimizer.phase.name "NoCrossingMinimizer"
  let empty ← runL (do
    let g ← newGraph {}
    runPhase NoCrossingMinimizer.phase g
    return true)
  check "hand: empty graph is fine" empty

def suites : Array Tests.Suite :=
  #[rustTests, sortingTests, longEdgeTests, northSouthTests, constraintTests, portTests, configTests,
    registrationTests, noCrossingTests]

end Tests.Layered.P3SimpleMinimizers
