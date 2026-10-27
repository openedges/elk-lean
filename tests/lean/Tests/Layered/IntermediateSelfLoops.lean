import Tests.Framework
import Elk.Alg.Layered
import Elk.Alg.Layered.Intermediate.SelfLoopProcessors
/-!
Tests of the self-loop model (`intermediate.loops`) and of `SelfLoopPreProcessor`,
`SelfLoopPortRestorer` and `SelfLoopPostProcessor`.

Ported from elk-rs `tests/intermediate/loops/self_loop_holder_test.rs`,
`self_loop_preprocessor_test.rs` and the `self_loop_port_restorer_*` tests of
`self_loop_router_test.rs` (hand-built graphs, same assertions; exact port orders added and derived
by hand). The remaining expectations are hand-derived from the Rust sources ("hand: …").
-/
namespace Tests.Layered.IntermediateSelfLoops

open Tests Elk.Graph Elk.Core.Math Elk.Core.Options Elk.Core.Util Elk.Core.Alg Elk.Alg.Layered
  Elk.Alg.Layered.Graph Elk.Alg.Layered.Options Elk.Alg.Layered.Intermediate Elk.Alg.Layered.Intermediate.Loops
  LayeredM
open Elk (ElkEnum EnumSet)

-- Graph building helpers -------------------------------------------------------------------

/-- `LNode::new(graph)` + `layerless_nodes_mut().push`. -/
def addNode (g : LGraphId) (n : LNode := {}) : LayeredM LNodeId := do
  let id ← createNode g n
  modifyGraph g fun x => { x with layerlessNodes := x.layerlessNodes.push id }
  return id

/-- `create_port(node, side, x, y)`: `LPort::new`, `set_side`, position, `set_node`. -/
def mkPort (n : LNodeId) (side : PortSide) (x y : Float := 0.0) : LayeredM LPortId := do
  let p ← createPort { ((({} : LPort).setSide side)) with position := ⟨x, y⟩ }
  setPortNode p (some n)
  return p

/-- `ports(node, north, east, south, west)` of the Rust tests. -/
def mkPorts (n : LNodeId) (north east south west : Nat) : LayeredM Unit := do
  for _ in [0:north] do let _ ← mkPort n .north
  for _ in [0:east] do let _ ← mkPort n .east
  for _ in [0:south] do let _ ← mkPort n .south
  for _ in [0:west] do let _ ← mkPort n .west

/-- `edge(source, target)`. -/
def mkEdge (s t : LPortId) : LayeredM LEdgeId := do
  let e ← createEdge
  setEdgeSource e (some s)
  setEdgeTarget e (some t)
  return e

/-- `add_single_label(edge, width, height)`. -/
def addLabel (e : LEdgeId) (w h : Float) : LayeredM LLabelId := do
  let l ← createLabel "self-loop" { size := ⟨w, h⟩ }
  modifyEdge e fun x => { x with labels := x.labels.push l }
  return l

/-- Moves a layerless node into a new layer (as the Rust restorer tests do). -/
def moveToLayer (g : LGraphId) (n : LNodeId) : LayeredM LayerId := do
  let l ← createLayer g
  modifyGraph g fun x => { x with layers := x.layers.push l, layerlessNodes := x.layerlessNodes.erase n }
  setNodeLayer n (some l)
  return l

def runPre (g : LGraphId) : LayeredM Unit := SelfLoopPreProcessor.processor.process g ProgressMonitor.null
def runRestorer (g : LGraphId) : LayeredM Unit := SelfLoopPortRestorer.processor.process g ProgressMonitor.null
def runPost (g : LGraphId) : LayeredM Unit := SelfLoopPostProcessor.processor.process g ProgressMonitor.null

/-- Sets port constraints (and the `ORIGINAL_PORT_CONSTRAINTS` the importer would set). -/
def setConstraints (n : LNodeId) (pc : PortConstraints) (original : Bool := true) : LayeredM Unit :=
  modifyNode n fun x => { x with
    props := x.props.set LayeredOptions.PORT_CONSTRAINTS pc
    internal := { x.internal with originalPortConstraints := if original then some pc else x.internal.originalPortConstraints } }

/-- The holder of a node (default when missing). -/
def holderOf (a : LGraphArena) (n : LNodeId) : SelfLoopHolder := (a.node n).internal.selfLoopHolder.getD default

/-- `basic_graph_without_self_loops()`: `n1[E] -> n2[W]`. -/
def basicGraphWithoutSelfLoops : LayeredM (LGraphId × LNodeId × LNodeId) := do
  let g ← createGraph
  let n1 ← addNode g
  mkPorts n1 0 1 0 0
  let n2 ← addNode g
  mkPorts n2 0 0 0 1
  let p1 := (← getNode n1).ports[0]!
  let p2 := (← getNode n2).ports[0]!
  let _ ← mkEdge p1 p2
  return (g, n1, n2)

/-- `basic_graph_with_self_loops()`: `n2` gets 2/2/2/1 more ports and loops `(0,1),(2,3),(4,5),(6,7)`. -/
def basicGraphWithSelfLoops : LayeredM (LGraphId × LNodeId) := do
  let (g, _, n2) ← basicGraphWithoutSelfLoops
  mkPorts n2 2 2 2 1
  let ports := (← getNode n2).ports
  let mut i := 1
  while i < ports.size do
    let _ ← mkEdge ports[i - 1]! ports[i]!
    i := i + 2
  return (g, n2)

-- SelfLoopHolder (self_loop_holder_test.rs) -------------------------------------------------

def holderTests : Suite := suite "layered.intermediate.loops.holder" do
  -- test_non_self_loop_graph
  let ((_, n1, n2), a) ← LayeredM.run basicGraphWithoutSelfLoops
  check "test_non_self_loop_graph: n1 needs no processing" (!SelfLoopHolder.needsSelfLoopProcessing a n1)
  check "test_non_self_loop_graph: n2 needs no processing" (!SelfLoopHolder.needsSelfLoopProcessing a n2)
  checkThrows "test_non_self_loop_graph: install throws" (discard <| LayeredM.run (SelfLoopHolder.install n2) a)
  -- test_basic_self_loops
  let ((_, n), a) ← LayeredM.run basicGraphWithSelfLoops
  check "test_basic_self_loops: needs processing" (SelfLoopHolder.needsSelfLoopProcessing a n)
  let (h, a) ← LayeredM.run (SelfLoopHolder.install n) a
  check "test_basic_self_loops: holder stored on node" ((a.node n).internal.selfLoopHolder.isSome)
  checkEq "test_basic_self_loops: holder node" (holderOf a n).lNode n
  let nodePorts := (a.node n).ports
  checkEq "test_basic_self_loops: port map size = node port count" h.slPortMap.size nodePorts.size
  checkEq "test_basic_self_loops: hyper loops = ports / 2" h.slHyperLoops.size (nodePorts.size / 2)
  checkEq "hand: port map in node port order" (h.slPortMap.map (·.1)) nodePorts
  checkEq "hand: only the port with the n1 edge had other edges"
    (h.slPorts.map (·.hadOnlySelfLoops)) #[false, true, true, true, true, true, true, true]
  check "hand: every hyper loop has one edge and two ports"
    (h.slHyperLoops.all fun l => l.slEdges.size == 1 && l.slPorts.size == 2)
  checkEq "hand: all self loop edges in loop order" h.allSelfLoopEdges.size 4
  checkEq "hand: edge hyper loop back reference" (h.slEdges.map (·.slHyperLoop.map (·.idx))) #[some 0, some 1, some 2, some 3]
  -- test_different_self_hyper_loops
  let (((n, first, second)), a) ← LayeredM.run (do
      let (_, _, n2) ← basicGraphWithoutSelfLoops
      mkPorts n2 2 2 2 1
      let ports := (← getNode n2).ports
      let mut first := #[]
      for i in [1:ports.size / 2] do first := first.push (← mkEdge ports[i - 1]! ports[i]!)
      let mut second := #[]
      for i in [ports.size / 2 + 1:ports.size] do second := second.push (← mkEdge ports[i - 1]! ports[i]!)
      return (n2, first, second))
  let (h, a) ← LayeredM.run (SelfLoopHolder.install n) a
  checkEq "test_different_self_hyper_loops: two hyper loops" h.slHyperLoops.size 2
  let loopEdges (i : Nat) := (h.slHyperLoops[i]!).slEdges.map fun e => (h.slEdge e).lEdge
  check "test_different_self_hyper_loops: edges grouped" (loopEdges 0 == first && loopEdges 1 == second)
  let ports := (a.node n).ports
  checkEq "hand: first loop ports (BFS order)" ((h.slHyperLoops[0]!).slPorts.map h.lPortOf) (ports.extract 0 4)
  checkEq "hand: second loop ports (BFS order)" ((h.slHyperLoops[1]!).slPorts.map h.lPortOf) (ports.extract 4 8)

/-- A node with three north ports and loops `p0 -> p1` (labels 10x5, 20x4) and `p1 -> p2` (label 6x9),
plus a separate loop `p3 -> p3` on one port. -/
def labelGraph (direction : Option Direction) (spacing : Option Float) : LayeredM (LGraphId × LNodeId × Array LPortId) := do
  let g ← createGraph
  if let some d := direction then setGraphProp g LayeredOptions.DIRECTION d
  if let some s := spacing then setGraphProp g LayeredOptions.SPACING_LABEL_LABEL s
  let n ← addNode g { size := ⟨60, 40⟩ }
  setConstraints n .free
  let p0 ← mkPort n .north 10 0
  let p1 ← mkPort n .north 30 0
  let p2 ← mkPort n .north 50 0
  let p3 ← mkPort n .south 20 40
  let e0 ← mkEdge p0 p1
  let _ ← addLabel e0 10 5
  let _ ← addLabel e0 20 4
  let e1 ← mkEdge p1 p2
  let _ ← addLabel e1 6 9
  let _ ← mkEdge p3 p3
  return (g, n, #[p0, p1, p2, p3])

def labelTests : Suite := suite "layered.intermediate.loops.labels" do
  let ((_, n, ports), a) ← LayeredM.run (labelGraph none none)
  let (h, _) ← LayeredM.run (SelfLoopHolder.install n) a
  checkEq "hand: two hyper loops (shared port p1, single-port loop p3)" h.slHyperLoops.size 2
  let l0 := h.slHyperLoops[0]!
  checkEq "hand: loop 0 ports" (l0.slPorts.map h.lPortOf) (ports.extract 0 3)
  checkEq "hand: loop 0 labels collected" ((l0.slLabels.map (·.lLabels.size)).getD 0) 3
  -- holder defaults: horizontal, spacing 0 -> (max width, sum height)
  checkEq "hand: initial label block size (horizontal, spacing 0)" ((l0.slLabels.map (·.size)).getD {}) ⟨20, 18⟩
  checkEq "hand: single-port loop has one port and one edge" ((h.slHyperLoops[1]!).slPorts.size, (h.slHyperLoops[1]!).slEdges.size) (1, 1)
  check "hand: loop without labels has none" (h.slHyperLoops[1]!).slLabels.isNone
  let p3 := (h.slPorts.find? (·.lPort == ports[3]!)).getD default
  checkEq "hand: single-port loop port has one incoming and one outgoing sl edge"
    (p3.incomingSLEdges.size, p3.outgoingSLEdges.size, p3.slNetFlow) (1, 1, 0)
  -- preprocessor label configuration
  let sizeAfterPre (d : Option Direction) (s : Option Float) : IO KVector := do
    let ((g, n, _), a) ← LayeredM.run (labelGraph d s)
    let (_, a) ← LayeredM.run (runPre g) a
    return (((holderOf a n).slHyperLoops[0]!).slLabels.map (·.size)).getD {}
  checkEq "hand: horizontal (RIGHT), spacing 3 -> (20, 5+4+9+2*3)" (← sizeAfterPre (some .right) (some 3)) ⟨20, 24⟩
  checkEq "hand: vertical (DOWN), spacing 3 -> (10+20+6+2*3, 9)" (← sizeAfterPre (some .down) (some 3)) ⟨42, 9⟩
  checkEq "hand: unset DIRECTION reads UNDEFINED (not horizontal) -> vertical stacking" (← sizeAfterPre none none) ⟨36, 9⟩
  -- placement
  let lb : SelfHyperLoopLabels := { lLabels := #[⟨0⟩, ⟨1⟩], size := ⟨20, 12⟩, position := ⟨100, 50⟩, labelLabelSpacing := 2 }
  let sizes : LLabelId → KVector := fun l => if l.idx == 0 then ⟨10, 5⟩ else ⟨20, 5⟩
  checkEq "hand: horizontal centred placement" ((lb.placement ⟨1, 1⟩ sizes).map (·.2))
    (#[⟨106, 51⟩, ⟨101, 58⟩] : Array KVector)
  checkEq "hand: horizontal placement on the west side is right aligned" ((SelfHyperLoopLabels.placement { lb with side := .west } {} sizes).map (·.2))
    (#[⟨110, 50⟩, ⟨100, 57⟩] : Array KVector)
  checkEq "hand: vertical placement on the north side is bottom aligned"
    ((SelfHyperLoopLabels.placement { lb with side := .north, layoutDirectionHorizontal := false, size := ⟨32, 7⟩ } {} sizes).map (·.2))
    (#[⟨100, 52⟩, ⟨112, 52⟩] : Array KVector)
  -- self loop types
  checkEq "SelfLoopType one side" (SelfLoopType.fromPortSides (EnumSet.of #[PortSide.north])) (some .oneSide)
  checkEq "SelfLoopType corner" (SelfLoopType.fromPortSides (EnumSet.of #[PortSide.north, .east])) (some .twoSidesCorner)
  checkEq "SelfLoopType opposing" (SelfLoopType.fromPortSides (EnumSet.of #[PortSide.west, .east])) (some .twoSidesOpposing)
  checkEq "SelfLoopType three" (SelfLoopType.fromPortSides (EnumSet.of #[PortSide.west, .east, .south])) (some .threeSides)
  checkEq "SelfLoopType four" (SelfLoopType.fromPortSides (EnumSet.of #[PortSide.north, .west, .east, .south])) (some .fourSides)
  checkEq "SelfLoopType undefined side" (SelfLoopType.fromPortSides (EnumSet.of #[PortSide.north, .undefined])) none
  checkEq "SelfLoopType no side" (SelfLoopType.fromPortSides EnumSet.empty) none

-- SelfLoopPreProcessor (self_loop_preprocessor_test.rs) ------------------------------------

/-- `TestGraph::new(port_constraints)`: ports `[W0, N, N, E, E, S, S, W]`, loops
`(0,1),(1,2),(3,4),(4,5)`; regular `[0]`, only-self-loop `[1..5]`, unconnected `[6,7]`. -/
def preTestGraph (pc : PortConstraints) : LayeredM (LGraphId × LNodeId × Array LPortId) := do
  let (g, _, n) ← basicGraphWithoutSelfLoops
  modifyNode n fun x => { x with size := ⟨50, 50⟩, props := x.props.set LayeredOptions.PORT_CONSTRAINTS pc }
  mkPorts n 2 2 2 1
  let ports := (← getNode n).ports
  let _ ← mkEdge ports[0]! ports[1]!
  let _ ← mkEdge ports[1]! ports[2]!
  let _ ← mkEdge ports[3]! ports[4]!
  let _ ← mkEdge ports[4]! ports[5]!
  return (g, n, ports)

def preprocessorTests : Suite := suite "layered.intermediate.selfLoopPreProcessor" do
  let hiddenCase (pc : PortConstraints) : TestM Unit := do
    let ((g, n, ports), a) ← LayeredM.run (preTestGraph pc)
    let (_, a) ← LayeredM.run (runPre g) a
    let remaining := (a.node n).ports
    let tag := s!"test_ports_hidden({pc})"
    checkEq s!"{tag}: regular + unconnected ports remain" remaining.size 3
    check s!"{tag}: regular and unconnected ports kept" (#[0, 6, 7].all fun i => remaining.contains ports[i]!)
    check s!"{tag}: only-self-loop ports removed" (#[1, 2, 3, 4, 5].all fun i => !remaining.contains ports[i]!)
    let connected := a.nodeConnectedEdges n
    check s!"{tag}: hidden edges" (!connected.isEmpty && connected.all fun e => !a.edgeIsSelfLoop e)
    let h := holderOf a n
    check s!"{tag} hand: holder marks ports hidden" h.arePortsHidden
    checkEq s!"{tag} hand: hidden flags in map order" (h.slPorts.map (·.isHidden)) #[false, true, true, true, true, true]
    check s!"hand: {tag}: hidden ports have no owner" (#[1, 2, 3, 4, 5].all fun i => (a.port ports[i]!).owner.isNone)
    check s!"hand: {tag}: self loop edges detached" (h.allSelfLoopEdges.all fun e => (a.edge e).source.isNone && (a.edge e).target.isNone)
  let untouchedCase (pc : PortConstraints) : TestM Unit := do
    let ((g, n, _), a) ← LayeredM.run (preTestGraph pc)
    let (_, a) ← LayeredM.run (runPre g) a
    let tag := s!"test_ports_untouched({pc})"
    checkEq s!"{tag}: all ports remain" (a.node n).ports.size 8
    let connected := a.nodeConnectedEdges n
    check s!"{tag}: hidden edges" (!connected.isEmpty && connected.all fun e => !a.edgeIsSelfLoop e)
    check s!"{tag} hand: holder not hidden" (!(holderOf a n).arePortsHidden)
  hiddenCase .free           -- test_free_ports
  hiddenCase .fixedSide      -- test_fixed_side
  untouchedCase .fixedOrder  -- test_fixed_order
  untouchedCase .fixedRatio  -- test_fixed_ratio
  untouchedCase .fixedPos    -- test_fixed_pos
  -- hierarchical node with external ports keeps its ports
  let ((g, n, _), a) ← LayeredM.run (do
      let (g, n, ports) ← preTestGraph .free
      let nested ← createGraph
      modifyGraph nested fun x => { x with internal := { x.internal with graphProperties := EnumSet.of #[GraphProperties.externalPorts] } }
      modifyNode n fun x => { x with nestedGraph := some nested }
      return (g, n, ports))
  let (_, a) ← LayeredM.run (runPre g) a
  checkEq "hand: nested graph with external ports keeps all ports" (a.node n).ports.size 8
  checkEq "hand: holder groups (0,1),(1,2) and (3,4),(4,5)" ((holderOf a n).slHyperLoops.map (·.slEdges.size)) #[2, 2]

-- SelfLoopPortRestorer (self_loop_router_test.rs `self_loop_port_restorer_*`) ---------------

/-- Runs pre-processor, moves `n` into a layer and runs the restorer. -/
def preAndRestore (g : LGraphId) (n : LNodeId) : LayeredM Unit := do
  runPre g
  let _ ← moveToLayer g n
  runRestorer g

/-- `build_north_west_corner_mixed_graph()` + pre/restorer: `[hiddenN, hiddenW, visibleN, visibleW]`. -/
def northWestCornerMixed : LayeredM (LNodeId × Array LPortId) := do
  let g ← createGraph
  let n ← addNode g { size := ⟨90, 60⟩, position := ⟨15, 20⟩ }
  setConstraints n .fixedSide
  let hiddenNorth ← mkPort n .north 30 0
  let hiddenWest ← mkPort n .west 0 30
  let visibleNorth ← mkPort n .north 60 0
  let visibleWest ← mkPort n .west 0 45
  let _ ← mkEdge hiddenWest hiddenNorth
  let ext ← addNode g { size := ⟨20, 20⟩, position := ⟨130, 20⟩ }
  setConstraints ext .fixedOrder false
  let extWest ← mkPort ext .west 0 10
  let extEast ← mkPort ext .east 20 10
  let _ ← mkEdge visibleWest extWest
  let _ ← mkEdge extEast visibleNorth
  preAndRestore g n
  return (n, #[hiddenNorth, hiddenWest, visibleNorth, visibleWest])

/-- Five chained north loops of 6, 5, 4, 3 and 2 ports with `EQUALLY` distribution. -/
def equallyGraph : LayeredM (LNodeId × Array (Array LPortId)) := do
  let g ← createGraph
  let n ← addNode g { size := ⟨120, 70⟩, position := ⟨15, 20⟩ }
  setConstraints n .free
  setNodeProp n LayeredOptions.EDGE_ROUTING_SELF_LOOP_DISTRIBUTION .equally
  let mut loops := #[]
  for (count, startX) in #[(6, 4.0), (5, 50.0), (4, 90.0), (3, 130.0), (2, 160.0)] do
    let mut ports := #[]
    for i in [0:count] do ports := ports.push (← mkPort n .north (startX + i.toFloat * 7.0) 0)
    for i in [1:ports.size] do let _ ← mkEdge ports[i - 1]! ports[i]!
    loops := loops.push ports
  preAndRestore g n
  return (n, loops)

/-- A visible port on `side` with an external edge and a `PORT_DUMMY` whose port (on `dummySide`,
origin = the visible port) has an edge, plus a hidden two-port loop on `side`. -/
def middleWithDummyGraph (side dummySide : PortSide) : LayeredM (LNodeId × LPortId × Array LPortId) := do
  let g ← createGraph
  let n ← addNode g { size := ⟨120, 70⟩, position := ⟨15, 20⟩ }
  setConstraints n .fixedSide
  let y := if side == .south then 70.0 else 0.0
  let hidden0 ← mkPort n side 30 y
  let hidden1 ← mkPort n side 50 y
  let _ ← mkEdge hidden0 hidden1
  let visible ← mkPort n side 80 y
  let ext ← addNode g
  let extPort ← mkPort ext (if side == .south then .west else .east) 0 10
  if side == .south then let _ ← mkEdge visible extPort else let _ ← mkEdge extPort visible
  let dummy ← addNode g
  let dummyPort ← mkPort dummy dummySide
  modifyPort dummyPort fun x => { x with internal := { x.internal with origin := some (.lPort visible) } }
  let dummyExt ← addNode g
  let dummyOther ← mkPort dummyExt (if dummySide == .east then .west else .east)
  if dummySide == .east then let _ ← mkEdge dummyPort dummyOther else let _ ← mkEdge dummyOther dummyPort
  modifyPort visible fun x => { x with internal := { x.internal with portDummy := some dummy } }
  preAndRestore g n
  return (n, visible, #[hidden0, hidden1])

/-- `build_corner_and_dummy_combined_graph()` + pre/restorer. Returns the node and
`[cornerW, cornerN, northMid0, northMid1, southMid0, southMid1, visibleN, visibleS]`. -/
def cornerAndDummyCombined : LayeredM (LNodeId × Array LPortId) := do
  let g ← createGraph
  let n ← addNode g { size := ⟨150, 90⟩, position := ⟨15, 20⟩ }
  setConstraints n .fixedSide
  let hwc ← mkPort n .west 0 20
  let hnc ← mkPort n .north 22 0
  let corner ← mkEdge hwc hnc
  let _ ← addLabel corner 12 6
  let hnm0 ← mkPort n .north 66 0
  let hnm1 ← mkPort n .north 86 0
  let northMid ← mkEdge hnm0 hnm1
  let _ ← addLabel northMid 11 6
  let hsm0 ← mkPort n .south 70 90
  let hsm1 ← mkPort n .south 90 90
  let southMid ← mkEdge hsm0 hsm1
  let _ ← addLabel southMid 11 6
  let visibleNorth ← mkPort n .north 124 0
  let extNorth ← addNode g
  let extNorthEast ← mkPort extNorth .east 10 10
  let _ ← mkEdge extNorthEast visibleNorth
  let northDummy ← addNode g
  let northDummyPort ← mkPort northDummy .west
  modifyPort northDummyPort fun x => { x with internal := { x.internal with origin := some (.lPort visibleNorth) } }
  let northDummyExternal ← createNode g
  let northDummySource ← mkPort northDummyExternal .east
  let _ ← mkEdge northDummySource northDummyPort
  modifyPort visibleNorth fun x => { x with internal := { x.internal with portDummy := some northDummy } }
  let visibleSouth ← mkPort n .south 124 90
  let extSouth ← addNode g
  let extSouthWest ← mkPort extSouth .west 0 10
  let _ ← mkEdge visibleSouth extSouthWest
  let southDummy ← addNode g
  let southDummyPort ← mkPort southDummy .east
  modifyPort southDummyPort fun x => { x with internal := { x.internal with origin := some (.lPort visibleSouth) } }
  let southDummyExternal ← createNode g
  let southDummyTarget ← mkPort southDummyExternal .west
  let _ ← mkEdge southDummyPort southDummyTarget
  modifyPort visibleSouth fun x => { x with internal := { x.internal with portDummy := some southDummy } }
  preAndRestore g n
  return (n, #[hwc, hnc, hnm0, hnm1, hsm0, hsm1, visibleNorth, visibleSouth])

def restorerRustTests : Suite := suite "layered.intermediate.selfLoopPortRestorer.rust" do
  -- self_loop_port_restorer_keeps_north_west_corner_clockwise_order
  let ((n, ps), a) ← LayeredM.run northWestCornerMixed
  let ports := (a.node n).ports
  let idx (p : LPortId) := (ports.findIdx? (· == p)).getD 1000
  check "keeps_north_west_corner_clockwise_order: north corner before regular north" (idx ps[0]! < idx ps[2]!)
  check "keeps_north_west_corner_clockwise_order: west corner after regular west" (idx ps[1]! > idx ps[3]!)
  checkEq "hand: north-west corner full order" ports #[ps[0]!, ps[2]!, ps[3]!, ps[1]!]
  checkEq "hand: corner loop type" (((holderOf a n).slHyperLoops[0]!).selfLoopType) (some .twoSidesCorner)
  check "hand: restored ports owned again" (ps.all fun p => (a.port p).owner == some n)
  check "hand: holder and ports un-hidden" (!(holderOf a n).arePortsHidden && (holderOf a n).slPorts.all (!·.isHidden))
  -- self_loop_port_restorer_equally_distribution_assigns_corner_by_net_flow
  let ((n, loops), a) ← LayeredM.run equallyGraph
  let h := holderOf a n
  checkEq "equally_distribution: five loops with unique sizes" (h.slHyperLoops.map (·.slPorts.size)) #[6, 5, 4, 3, 2]
  let small := loops[4]!
  checkEq "equally_distribution: size-2 loop split across WEST/NORTH" ((a.port small[0]!).side, (a.port small[1]!).side) (.west, .north)
  let sides := (a.node n).ports.map fun p => (a.port p).side
  check "equally_distribution: all four sides covered" (#[PortSide.north, .east, .south, .west].all sides.contains)
  let q := loops[0]!; let r := loops[1]!; let s := loops[2]!; let t := loops[3]!
  checkEq "hand: equally distribution target sides" (loops.map fun l => (a.port l[0]!).side) #[.north, .south, .east, .west, .west]
  checkEq "hand: equally distribution restored order"
    (a.node n).ports
    #[small[1]!, q[2]!, q[1]!, q[0]!, q[5]!, q[4]!, q[3]!, s[1]!, s[0]!, s[3]!, s[2]!,
      r[1]!, r[0]!, r[4]!, r[3]!, r[2]!, t[0]!, t[2]!, t[1]!, small[0]!]
  -- self_loop_port_restorer_places_east_connected_south_before_middle_hidden_south
  let ((n, visible, hidden), a) ← LayeredM.run (middleWithDummyGraph .south .east)
  let ports := (a.node n).ports
  let idx (p : LPortId) := (ports.findIdx? (· == p)).getD 1000
  check "places_east_connected_south_before_middle_hidden_south" (hidden.all fun p => idx visible < idx p && idx p < 1000)
  checkEq "hand: south order" ports #[visible, hidden[0]!, hidden[1]!]
  -- self_loop_port_restorer_places_west_connected_north_before_middle_hidden_north
  let ((n, visible, hidden), a) ← LayeredM.run (middleWithDummyGraph .north .west)
  let ports := (a.node n).ports
  let idx (p : LPortId) := (ports.findIdx? (· == p)).getD 1000
  check "places_west_connected_north_before_middle_hidden_north" (hidden.all fun p => idx visible < idx p && idx p < 1000)
  checkEq "hand: north order" ports #[visible, hidden[0]!, hidden[1]!]
  -- self_loop_port_restorer_orders_corner_and_dummy_connected_ports_before_middle_groups
  let ((n, ps), a) ← LayeredM.run cornerAndDummyCombined
  let ports := (a.node n).ports
  let idx (p : LPortId) := (ports.findIdx? (· == p)).getD 1000
  check "orders_corner_and_dummy: north corner before dummy-connected north" (idx ps[1]! < idx ps[6]!)
  check "orders_corner_and_dummy: dummy-connected north before north middle" (idx ps[6]! < idx ps[2]! && idx ps[6]! < idx ps[3]!)
  check "orders_corner_and_dummy: dummy-connected south before south middle" (idx ps[7]! < idx ps[4]! && idx ps[7]! < idx ps[5]!)
  checkEq "hand: combined full order" ports #[ps[1]!, ps[6]!, ps[2]!, ps[3]!, ps[7]!, ps[4]!, ps[5]!, ps[0]!]

/-- Free node with three two-port loops on the east side (all hidden) and the given distribution. -/
def distributionGraph (d : SelfLoopDistributionStrategy) : LayeredM (LNodeId × Array LPortId) := do
  let g ← createGraph
  let n ← addNode g
  setConstraints n .free
  setNodeProp n LayeredOptions.EDGE_ROUTING_SELF_LOOP_DISTRIBUTION d
  let mut ports := #[]
  for _ in [0:3] do
    let a ← mkPort n .east
    let b ← mkPort n .east
    let _ ← mkEdge a b
    ports := ports ++ #[a, b]
  preAndRestore g n
  return (n, ports)

/-- Free node with two north loops `a0 -> a1`, `b0 -> b1` and the given ordering. -/
def orderingGraph (o : SelfLoopOrderingStrategy) : LayeredM (LNodeId × Array LPortId) := do
  let g ← createGraph
  let n ← addNode g
  setConstraints n .free
  setNodeProp n LayeredOptions.EDGE_ROUTING_SELF_LOOP_ORDERING o
  let a0 ← mkPort n .north
  let a1 ← mkPort n .north
  let b0 ← mkPort n .north
  let b1 ← mkPort n .north
  let _ ← mkEdge a0 a1
  let _ ← mkEdge b0 b1
  preAndRestore g n
  return (n, #[a0, a1, b0, b1])

/-- A `FIXED_SIDE` node with one hidden loop over ports on `sides` (chained) and, optionally,
visible north/south ports `v`/`w` connected to an external node. -/
def sidesGraph (sides : Array PortSide) (visible : Bool) : LayeredM (LNodeId × Array LPortId × Array LPortId) := do
  let g ← createGraph
  let n ← addNode g
  setConstraints n .fixedSide
  let mut ports := #[]
  for side in sides do ports := ports.push (← mkPort n side)
  for i in [1:ports.size] do let _ ← mkEdge ports[i - 1]! ports[i]!
  let mut vis := #[]
  if visible then
    let ext ← addNode g
    let v ← mkPort n .north
    let w ← mkPort n .south
    let _ ← mkEdge v (← mkPort ext .west)
    let _ ← mkEdge (← mkPort ext .east) w
    vis := #[v, w]
  preAndRestore g n
  return (n, ports, vis)

def restorerTests : Suite := suite "layered.intermediate.selfLoopPortRestorer" do
  -- distributions
  let ((n, ps), a) ← LayeredM.run (distributionGraph .north)
  check "hand: NORTH distribution puts every hidden port north" (ps.all fun p => (a.port p).side == .north)
  checkEq "hand: NORTH distribution, stacked order (later loops enclose earlier ones)" (a.node n).ports
    #[ps[4]!, ps[2]!, ps[0]!, ps[1]!, ps[3]!, ps[5]!]
  let ((_, ps), a) ← LayeredM.run (distributionGraph .northSouth)
  checkEq "hand: NORTH_SOUTH distribution alternates by hidden port count"
    (ps.map fun p => (a.port p).side) #[.north, .north, .south, .south, .north, .north]
  -- orderings
  let ((n, ps), a) ← LayeredM.run (orderingGraph .stacked)
  checkEq "hand: STACKED order" (a.node n).ports #[ps[2]!, ps[0]!, ps[1]!, ps[3]!]
  let ((n, ps), a) ← LayeredM.run (orderingGraph .reverseStacked)
  checkEq "hand: REVERSE_STACKED order" (a.node n).ports #[ps[0]!, ps[2]!, ps[3]!, ps[1]!]
  let ((n, ps), a) ← LayeredM.run (orderingGraph .sequenced)
  checkEq "hand: SEQUENCED order (each loop appended reversed)" (a.node n).ports #[ps[1]!, ps[0]!, ps[3]!, ps[2]!]
  -- loop types
  let ((n, ps, vis), a) ← LayeredM.run (sidesGraph #[.north, .east, .south] true)
  checkEq "hand: three-sided loop type" ((holderOf a n).slHyperLoops[0]!).selfLoopType (some .threeSides)
  checkEq "hand: three-sided order (N/END, E/MIDDLE, S/START between visible ports)" (a.node n).ports
    #[vis[0]!, ps[0]!, ps[1]!, ps[2]!, vis[1]!]
  let ((n, ps, _), a) ← LayeredM.run (sidesGraph #[.north, .east, .south, .west] false)
  checkEq "hand: four-sided loop type" ((holderOf a n).slHyperLoops[0]!).selfLoopType (some .fourSides)
  checkEq "hand: four-sided order" (a.node n).ports ps
  checkEq "hand: four-sided ports by side" (((holderOf a n).slHyperLoops[0]!).portsOnSide .south).size 1
  let ((n, ps, _), a) ← LayeredM.run (sidesGraph #[.west, .east] false)
  checkEq "hand: opposing loop type" ((holderOf a n).slHyperLoops[0]!).selfLoopType (some .twoSidesOpposing)
  checkEq "hand: opposing order (E/END, W/START)" (a.node n).ports #[ps[1]!, ps[0]!]
  -- ports not hidden: only the types are computed
  let ((n, ps), a) ← LayeredM.run (do
      let g ← createGraph
      let n ← addNode g
      setConstraints n .fixedOrder
      let p0 ← mkPort n .east
      let p1 ← mkPort n .north
      let _ ← mkEdge p0 p1
      preAndRestore g n
      return (n, #[p0, p1]))
  checkEq "hand: FIXED_ORDER keeps the port list" (a.node n).ports ps
  checkEq "hand: FIXED_ORDER still computes the type" ((holderOf a n).slHyperLoops[0]!).selfLoopType (some .twoSidesCorner)
  -- a loop port that also has a regular edge stays visible
  let ((n, ps), a) ← LayeredM.run (do
      let g ← createGraph
      let n ← addNode g
      setConstraints n .free
      let a0 ← mkPort n .north
      let a1 ← mkPort n .north
      let a2 ← mkPort n .north
      let _ ← mkEdge a0 a1
      let _ ← mkEdge a1 a2
      let ext ← addNode g
      let _ ← mkEdge a0 (← mkPort ext .west)
      preAndRestore g n
      return (n, #[a0, a1, a2]))
  checkEq "hand: mixed port stays, hidden ports enter NORTH/MIDDLE reversed" (a.node n).ports #[ps[2]!, ps[1]!, ps[0]!]
  -- split index
  checkEq "split index [-1,0,1,1]" (SelfLoopPortRestorer.computePortListSplitIndex #[-1, 0, 1, 1]) 2
  checkEq "split index [0,0]" (SelfLoopPortRestorer.computePortListSplitIndex #[0, 0]) 1
  checkEq "split index [1,1]" (SelfLoopPortRestorer.computePortListSplitIndex #[1, 1]) 1
  checkEq "split index [-1,-1,1]" (SelfLoopPortRestorer.computePortListSplitIndex #[-1, -1, 1]) 1
  checkEq "split index [-2,1,1]" (SelfLoopPortRestorer.computePortListSplitIndex #[-2, 1, 1]) 1
  checkEq "split index []" (SelfLoopPortRestorer.computePortListSplitIndex #[]) 0

-- SelfLoopPostProcessor ---------------------------------------------------------------------

def postprocessorTests : Suite := suite "layered.intermediate.selfLoopPostProcessor" do
  let ((g, n, ps, es, lbs), a) ← LayeredM.run (do
      let g ← createGraph
      let n ← addNode g { position := ⟨10, 20⟩, size := ⟨40, 30⟩ }
      setConstraints n .free
      let p0 ← mkPort n .north
      let p1 ← mkPort n .north
      let p2 ← mkPort n .east
      let e0 ← mkEdge p0 p1
      let e1 ← mkEdge p2 p2
      let l0 ← addLabel e0 8 4
      preAndRestore g n
      -- what the router would leave: relative bend points and label positions
      modifyEdge e0 fun x => { x with bendPoints := #[⟨1, 2⟩, ⟨3, -4⟩] }
      modifyLabel l0 fun x => { x with position := ⟨3, 4⟩ }
      SelfLoopHolder.update n fun h => h.modifySLHyperLoop ⟨0⟩ fun x =>
        { x with slLabels := x.slLabels.map fun lb => { lb with position := ⟨5, 6⟩ } }
      return (g, n, #[p0, p1, p2], #[e0, e1], #[l0]))
  checkEq "hand: edges hidden before post-processing" ((a.edge es[0]!).source, (a.edge es[1]!).target) (none, none)
  let (_, a) ← LayeredM.run (runPost g) a
  checkEq "hand: edge 0 reconnected" ((a.edge es[0]!).source, (a.edge es[0]!).target) (some ps[0]!, some ps[1]!)
  checkEq "hand: single-port loop reconnected" ((a.edge es[1]!).source, (a.edge es[1]!).target) (some ps[2]!, some ps[2]!)
  checkEq "hand: port edge lists restored" ((a.port ps[0]!).outgoingEdges, (a.port ps[1]!).incomingEdges) (#[es[0]!], #[es[0]!])
  checkEq "hand: bend points offset by node position" (a.edge es[0]!).bendPoints #[⟨11, 22⟩, ⟨13, 16⟩]
  checkEq "hand: label position offset by node position" (a.label lbs[0]!).position ⟨13, 24⟩
  checkEq "hand: label block position offset" ((((holderOf a n).slHyperLoops[0]!).slLabels.map (·.position)).getD {}) ⟨15, 26⟩
  check "hand: edges are self loops again" (es.all (a.edgeIsSelfLoop ·))
  check "hand: holder ports all owned by the node" (ps.all fun p => (a.port p).owner == some n)
  -- registration
  let pre ← IntermediateProcessorStrategy.create .selfLoopPreprocessor
  let restorer ← IntermediateProcessorStrategy.create .selfLoopPortRestorer
  let post ← IntermediateProcessorStrategy.create .selfLoopPostprocessor
  checkEq "registered processor names" #[pre.name, restorer.name, post.name]
    #["SelfLoopPreProcessor", "SelfLoopPortRestorer", "SelfLoopPostProcessor"]

def suites : Array Suite :=
  #[holderTests, labelTests, preprocessorTests, restorerRustTests, restorerTests, postprocessorTests]

end Tests.Layered.IntermediateSelfLoops
