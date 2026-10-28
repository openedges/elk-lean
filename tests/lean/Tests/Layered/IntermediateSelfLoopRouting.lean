import Tests.Framework
import Tests.Layered.IntermediateSelfLoops
import Elk.Alg.Layered
import Elk.Alg.Layered.Intermediate.Loops.Routing
import Elk.Alg.Layered.Intermediate.SelfLoopRouter
/-!
Tests of the self-loop routing package (`intermediate.loops.routing`) and of `SelfLoopRouter`.

Ported from elk-rs `tests/intermediate/loops/self_loop_router_test.rs` (the `self_loop_router_*`
cases), `ptides_self_loop_margin_test.rs` and `polyline_self_loop_router_test.rs` (hand-built
graphs, same assertions; exact bend points, slots and label positions added). The remaining
expectations are hand-derived from the Rust sources ("hand: …"). The graph helpers come from
`Tests.Layered.IntermediateSelfLoops`.
-/
namespace Tests.Layered.IntermediateSelfLoopRouting

open Tests Elk.Graph Elk.Core.Math Elk.Core.Options Elk.Core.Util Elk.Core.Alg Elk.Alg.Layered
  Elk.Alg.Layered.Graph Elk.Alg.Layered.Options Elk.Alg.Layered.Intermediate Elk.Alg.Layered.Intermediate.Loops
  Elk.Alg.Layered.Intermediate.Loops.Routing Tests.Layered.IntermediateSelfLoops LayeredM
open Elk (ElkEnum EnumSet)

-- Helpers ----------------------------------------------------------------------------------

def runRouter (g : LGraphId) : LayeredM Unit := SelfLoopRouter.processor.process g ProgressMonitor.null

/-- Pre-processor, move into a layer, port restorer, router (the Rust test sequence). -/
def preRestoreRoute (g : LGraphId) (n : LNodeId) : LayeredM Unit := do
  preAndRestore g n
  runRouter g

/-- Pre-processor, restorer, router and post-processor. -/
def fullPipeline (g : LGraphId) (n : LNodeId) : LayeredM Unit := do
  preRestoreRoute g n
  runPost g

/-- `add_single_label_with_inline(edge, w, h, inline)`. -/
def addInlineLabel (e : LEdgeId) (w h : Float) (inline : Bool) : LayeredM LLabelId := do
  let l ← addLabel e w h
  setLabelProp l LayeredOptions.EDGE_LABELS_INLINE inline
  return l

def bends (a : LGraphArena) (e : LEdgeId) : Array KVector := (a.edge e).bendPoints

def minY (ps : Array KVector) : Float := ps.foldl (fun m p => fmin m p.y) Float.posInf
def maxY (ps : Array KVector) : Float := ps.foldl (fun m p => fmax m p.y) Float.negInf
def minX (ps : Array KVector) : Float := ps.foldl (fun m p => fmin m p.x) Float.posInf
def maxX (ps : Array KVector) : Float := ps.foldl (fun m p => fmax m p.x) Float.negInf

/-- Whether a point of `ps` lies outside the node's bounds. -/
def hasOutsidePoint (a : LGraphArena) (n : LNodeId) (ps : Array KVector) : Bool :=
  let nd := a.node n
  ps.any fun p => p.x < nd.position.x || p.x > nd.position.x + nd.size.x || p.y < nd.position.y || p.y > nd.position.y + nd.size.y

def loopOf (a : LGraphArena) (n : LNodeId) (i : Nat) : SelfHyperLoop := (holderOf a n).slHyperLoops[i]!

/-- Routing slots of loop `i` on N, E, S, W. -/
def slotsOf (a : LGraphArena) (n : LNodeId) (i : Nat) : Array Int :=
  #[PortSide.north, .east, .south, .west].map (loopOf a n i).getRoutingSlot

def labelBlock (a : LGraphArena) (n : LNodeId) (i : Nat) : SelfHyperLoopLabels := ((loopOf a n i).slLabels).getD {}

def marginOf (a : LGraphArena) (n : LNodeId) : LMargin := (a.node n).margin

-- Rust test graphs ----------------------------------------------------------------------------

/-- The one-port loop of `self_loop_router_keeps_duplicate_bend_points_for_same_port`. -/
def onePortGraph (routing : Option EdgeRouting) : LayeredM (LGraphId × LNodeId × LEdgeId) := do
  let g ← createGraph
  if let some r := routing then setGraphProp g LayeredOptions.EDGE_ROUTING r
  let n ← addNode g { size := ⟨50, 40⟩, position := ⟨10, 20⟩ }
  setConstraints n .free
  let p ← mkPort n .north 20 0
  let e ← mkEdge p p
  return (g, n, e)

/-- `build_self_loop_graph()`. -/
def selfLoopGraph : LayeredM (LGraphId × LNodeId × Array LEdgeId) := do
  let g ← createGraph
  let n ← addNode g { size := ⟨60, 50⟩, position := ⟨15, 20⟩ }
  setConstraints n .free
  let east ← mkPort n .east 60 14
  let west ← mkPort n .west 0 32
  let north ← mkPort n .north 24 0
  let first ← mkEdge east west
  let second ← mkEdge north east
  return (g, n, #[first, second])

/-- `build_parallel_north_self_loop_graph()` (optionally with 14x8 labels and an ordering). -/
def parallelNorthGraph (labels : Bool) (ordering : Option SelfLoopOrderingStrategy := none)
    (xs : Array Float := #[10, 30, 50, 70]) : LayeredM (LGraphId × LNodeId × Array LEdgeId) := do
  let g ← createGraph
  let n ← addNode g { size := ⟨80, 60⟩, position := ⟨10, 30⟩ }
  setConstraints n .free
  if let some o := ordering then setNodeProp n LayeredOptions.EDGE_ROUTING_SELF_LOOP_ORDERING o
  let mut ports := #[]
  for x in xs do ports := ports.push (← mkPort n .north x 0)
  let first ← mkEdge ports[0]! ports[1]!
  let second ← mkEdge ports[2]! ports[3]!
  if labels then
    let _ ← addInlineLabel first 14 8 false
    let _ ← addInlineLabel second 14 8 false
  return (g, n, #[first, second])

/-- `build_north_south_self_loop_graph_with_label(inline)`. -/
def northSouthGraph (inline : Bool) : LayeredM (LGraphId × LNodeId × LEdgeId × LLabelId) := do
  let g ← createGraph
  let n ← addNode g { size := ⟨80, 60⟩, position := ⟨10, 20⟩ }
  setConstraints n .fixedOrder
  let north ← mkPort n .north 40 0
  let south ← mkPort n .south 40 60
  let e ← mkEdge north south
  let l ← addInlineLabel e 20 10 inline
  return (g, n, e, l)

/-- `build_east_west_self_loop_graph()`. -/
def eastWestGraph : LayeredM (LGraphId × LNodeId × LEdgeId) := do
  let g ← createGraph
  let n ← addNode g { size := ⟨80, 60⟩, position := ⟨10, 20⟩ }
  setConstraints n .fixedOrder
  let west ← mkPort n .west 0 30
  let east ← mkPort n .east 80 30
  let e ← mkEdge west east
  return (g, n, e)

/-- `build_opposing_self_loop_with_side_penalty(eastConnected, westConnected)`. -/
def opposingPenaltyGraph (eastConnected westConnected : Bool) : LayeredM (LGraphId × LNodeId × LEdgeId) := do
  let g ← createGraph
  let n ← addNode g { size := ⟨80, 60⟩, position := ⟨10, 20⟩ }
  setConstraints n .fixedOrder
  let north ← mkPort n .north 40 0
  let east ← mkPort n .east 80 30
  let south ← mkPort n .south 40 60
  let west ← mkPort n .west 0 30
  let selfLoop ← mkEdge north south
  let ext ← addNode g { size := ⟨20, 20⟩, position := ⟨140, 20⟩ }
  setConstraints ext .fixedOrder false
  let extWest ← mkPort ext .west 0 10
  let extEast ← mkPort ext .east 20 10
  if eastConnected then let _ ← mkEdge east extWest
  if westConnected then let _ ← mkEdge west extEast
  return (g, n, selfLoop)

/-- A port `create_port` with size (side set before the size, so the anchor stays `(0, 0)`). -/
def mkSizedPort (n : LNodeId) (side : PortSide) (x y w h : Float) (index : Int) : LayeredM LPortId := do
  let p ← createPort { ((({} : LPort).setSide side)) with position := ⟨x, y⟩, size := ⟨w, h⟩ }
  setPortProp p LayeredOptions.PORT_INDEX index
  setPortNode p (some n)
  return p

/-- The N12 graph of `ptides_self_loop_margin_test.rs`: `[p33, p32, p34, p35]` and `e21`. -/
def ptidesGraph : LayeredM (LGraphId × LNodeId × Array LPortId × LEdgeId) := do
  let g ← createGraph
  let n ← addNode g { size := ⟨121, 30⟩, position := ⟨0, 0⟩, margin := { left := 8 } }
  setConstraints n .fixedPos false
  let p33 ← mkSizedPort n .east 113 7 8 8 (-1)
  let p32 ← mkSizedPort n .west (-8) 7 8 8 0
  let p34 ← mkSizedPort n .west (-8) 15 8 8 2
  let p35 ← mkSizedPort n .east 113 15 8 8 3
  let e21 ← mkEdge p33 p34
  let ext ← addNode g { size := ⟨20, 20⟩ }
  let extEast ← createPort { ((({} : LPort).setSide .east)) with position := ⟨20, 10⟩, size := ⟨8, 8⟩ }
  setPortNode extEast (some ext)
  let extWest ← createPort { ((({} : LPort).setSide .west)) with position := ⟨0, 10⟩, size := ⟨8, 8⟩ }
  setPortNode extWest (some ext)
  let _ ← mkEdge p32 extWest
  let _ ← mkEdge extEast p35
  return (g, n, #[p33, p32, p34, p35], e21)

-- self_loop_router_test.rs ------------------------------------------------------------------

def routerRustTests : Suite := suite "layered.intermediate.selfLoopRouter.rust" do
  -- self_loop_router_keeps_duplicate_bend_points_for_same_port
  let ((n, e), a) ← LayeredM.run (do
      let (g, n, e) ← onePortGraph none
      fullPipeline g n
      return (n, e))
  let bs := bends a e
  checkEq "keeps_duplicate_bend_points_for_same_port: two bend points" bs.size 2
  check "keeps_duplicate_bend_points_for_same_port: identical" (bs.size == 2 && (bs[0]!.x - bs[1]!.x).abs < 1e-9 && (bs[0]!.y - bs[1]!.y).abs < 1e-9)
  checkEq "hand: one-port loop bend points (slot N0 at -10, + node position)" bs #[⟨30, 10⟩, ⟨30, 10⟩]
  checkEq "hand: one-port loop routingSlotCount (unoccupied sides count slot 0)" (holderOf a n).routingSlotCount #[0, 1, 1, 1, 1]
  checkEqR "hand: one-port loop margins" (marginOf a n) { top := 10 }
  -- self_loop_router_creates_outside_bend_points_for_hidden_loops
  let ((n, es), a) ← LayeredM.run (do
      let (g, n, es) ← selfLoopGraph
      fullPipeline g n
      return (n, es))
  check "creates_outside_bend_points: edges reconnected" (es.all fun e => (a.edge e).source.isSome && (a.edge e).target.isSome)
  check "creates_outside_bend_points: bend points present" (es.all fun e => !(bends a e).isEmpty)
  check "creates_outside_bend_points: routes leave the node" (es.all fun e => hasOutsidePoint a n (bends a e))
  checkEq "hand: NORTH distribution makes the loop one-sided; first edge" (bends a es[0]!) #[⟨75, 10⟩, ⟨15, 10⟩]
  checkEq "hand: second edge" (bends a es[1]!) #[⟨39, 10⟩, ⟨75, 10⟩]
  -- self_loop_router_assigns_separate_slots_for_parallel_north_loops
  let ((n, es), a) ← LayeredM.run (do
      let (g, n, es) ← parallelNorthGraph false
      fullPipeline g n
      return (n, es))
  let nodeY := (a.node n).position.y
  check "assigns_separate_slots: bend points present" (es.all fun e => !(bends a e).isEmpty)
  check "assigns_separate_slots: routes above the node" (es.all fun e => minY (bends a e) < nodeY)
  checkEq "hand: nested loops: inner loop N slot 0, outer loop N slot 1" (slotsOf a n 0, slotsOf a n 1) (#[0, 0, 0, 0], #[1, 0, 0, 0])
  checkEq "hand: nested loops routingSlotCount" (holderOf a n).routingSlotCount #[0, 2, 1, 1, 1]
  checkEq "hand: inner loop bend points" (bends a es[0]!) #[⟨20, 20⟩, ⟨40, 20⟩]
  checkEq "hand: outer loop bend points" (bends a es[1]!) #[⟨60, 10⟩, ⟨80, 10⟩]
  checkEqR "hand: nested loops margins" (marginOf a n) { top := 20 }
  -- self_loop_router_places_labels_above_parallel_north_loops
  let ((n, es), a) ← LayeredM.run (do
      let (g, n, es) ← parallelNorthGraph true
      fullPipeline g n
      return (n, es))
  let nd := a.node n
  let labelsOf (e : LEdgeId) := (a.edge e).labels
  check "places_labels_above: one label per edge" (es.all fun e => (labelsOf e).size == 1)
  let lbs := es.map fun e => a.label (labelsOf e)[0]!
  check "places_labels_above: finite positions" (lbs.all fun l => !l.position.isNaN && !l.position.isInfinite)
  check "places_labels_above: labels above the node" (lbs.all fun l => l.position.y + l.size.y < nd.position.y)
  check "places_labels_above: centred labels within node width"
    (lbs.all fun l => l.position.x ≥ nd.position.x - 1e-6 && l.position.x + l.size.x ≤ nd.position.x + nd.size.x + 1e-6)
  check "places_labels_above: different label lanes" ((lbs[0]!.position.y - lbs[1]!.position.y).abs > 1e-3)
  checkEq "hand: label positions (lanes -10/-30 with label height 8 + spacing 2)" (lbs.map (·.position)) #[⟨43, 10⟩, ⟨43, -10⟩]
  checkEq "hand: labelled loop bend points" (es.map (bends a)) #[#[⟨20, 20⟩, ⟨40, 20⟩], #[⟨60, 0⟩, ⟨80, 0⟩]]
  checkEq "hand: label sides" ((labelBlock a n 0).side, (labelBlock a n 1).side) (.north, .north)
  check "hand: inline flag removed for one-sided loops" (lbs.all fun l => !l.props.has LayeredOptions.EDGE_LABELS_INLINE)
  -- self_loop_router_sequences_one_sided_north_labels_left_and_right
  let ((n, es), a) ← LayeredM.run (do
      let (g, n, es) ← parallelNorthGraph true (some .sequenced) #[8, 20, 58, 72]
      fullPipeline g n
      return (n, es))
  let nd := a.node n
  let lbs := es.map fun e => a.label (a.edge e).labels[0]!
  let centers := stableSortByFloat (lbs.map fun l => l.position.x + l.size.x / 2.0) id
  let nodeCenterX := nd.position.x + nd.size.x / 2.0
  check "sequences_one_sided_north_labels: above the node" (lbs.all fun l => l.position.y + l.size.y < nd.position.y)
  check "sequences_one_sided_north_labels: one left and one right of the centre"
    (centers[0]! < nodeCenterX - 5.0 && centers[1]! > nodeCenterX + 5.0)
  checkEq "hand: sequenced alignments (RIGHT at the leftmost loop, LEFT at the other)"
    ((labelBlock a n 0).alignment, (labelBlock a n 1).alignment) (.right, .left)
  -- ELK Java computes the label blocks' x (`LabelPlacer.computeCoordinates`) before the slot
  -- assignment: the RIGHT/LEFT aligned blocks do not overlap, so both loops stay in N slot 0
  -- (elk-rs compares unset positions, sees an overlap and moves the second loop to slot 1)
  checkEq "hand: sequenced label positions" (lbs.map (·.position)) #[⟨4, 10⟩, ⟨82, 10⟩]
  checkEq "hand: non-overlapping label blocks share N slot 0" ((slotsOf a n 0)[0]!, (slotsOf a n 1)[0]!) (0, 0)
  -- self_loop_router_expands_node_margin_for_self_loop_labels
  let ((n, es), a) ← LayeredM.run (do
      let (g, n, es) ← parallelNorthGraph true
      preRestoreRoute g n
      return (n, es))
  let labelTopLocal := (a.label (a.edge es[0]!).labels[0]!).position.y
  check "expands_node_margin_for_self_loop_labels" ((marginOf a n).top + 1e-6 ≥ -labelTopLocal)
  checkEq "hand: label-covering top margin (outer label at -40)" (marginOf a n).top 40.0
  checkEq "hand: label positions are node-relative before post-processing" labelTopLocal (-20.0)
  -- self_loop_router_offsets_corner_for_inline_label_clearance
  let ((rn, re, rl), ra) ← LayeredM.run (do
      let (g, n, e, l) ← northSouthGraph false
      fullPipeline g n
      return (n, e, l))
  let ((inl, ie, il, inlineBefore), ia) ← LayeredM.run (do
      let (g, n, e, l) ← northSouthGraph true
      let before := (← getLabel l).props.getD LayeredOptions.EDGE_LABELS_INLINE false
      fullPipeline g n
      return (n, e, l, before))
  check "offsets_corner_for_inline_label: inline flag set before routing" inlineBefore
  checkEq "offsets_corner_for_inline_label: two-sided opposing" (loopOf ia inl 0).selfLoopType (some .twoSidesOpposing)
  let labelSide := (labelBlock ia inl 0).side
  checkEq "hand: inline label goes EAST (west side free)" labelSide .east
  check "offsets_corner_for_inline_label: inline corner farther out" (maxX (bends ia ie) > maxX (bends ra re) + 3.0)
  checkEq "hand: regular opposing route (clockwise over EAST)" (bends ra re) #[⟨50, 10⟩, ⟨100, 10⟩, ⟨100, 90⟩, ⟨50, 90⟩]
  checkEq "hand: inline route (EAST corners + half label width)" (bends ia ie) #[⟨50, 10⟩, ⟨110, 10⟩, ⟨110, 90⟩, ⟨50, 90⟩]
  checkEq "hand: regular label NORTH/LEFT at the leftmost port" ((ra.label rl).position, (labelBlock ra rn 0).alignment) (⟨50, -2⟩, .left)
  -- Java `computeCoordinates` sets only `x` for CENTER: on the EAST lane the block keeps `y = 0`
  checkEq "hand: inline CENTER label on the EAST lane (no label distance, block y 0)" (ia.label il).position ⟨100, 20⟩
  -- self_loop_router_prefers_west_route_when_east_ports_are_more_connected
  let ((n, e), a) ← LayeredM.run (do
      let (g, n, e) ← opposingPenaltyGraph true false
      fullPipeline g n
      return (n, e))
  check "prefers_west_route_when_east_ports_are_more_connected" (minX (bends a e) < (a.node n).position.x - 1e-6)
  checkEq "hand: west route" (bends a e) #[⟨50, 10⟩, ⟨0, 10⟩, ⟨0, 90⟩, ⟨50, 90⟩]
  checkEq "hand: west route occupies S, W, N" (loopOf a n 0).occupiedPortSides (EnumSet.of #[PortSide.south, .west, .north])
  -- self_loop_router_prefers_east_route_when_west_ports_are_more_connected
  let ((n, e), a) ← LayeredM.run (do
      let (g, n, e) ← opposingPenaltyGraph false true
      fullPipeline g n
      return (n, e))
  check "prefers_east_route_when_west_ports_are_more_connected"
    (maxX (bends a e) > (a.node n).position.x + (a.node n).size.x + 1e-6)
  checkEq "hand: east route" (bends a e) #[⟨50, 10⟩, ⟨100, 10⟩, ⟨100, 90⟩, ⟨50, 90⟩]
  -- self_loop_router_prefers_south_route_on_east_west_tie
  let ((n, e), a) ← LayeredM.run (do
      let (g, n, e) ← eastWestGraph
      fullPipeline g n
      return (n, e))
  check "prefers_south_route_on_east_west_tie" (maxY (bends a e) > (a.node n).position.y + (a.node n).size.y - 1e-6)
  checkEq "hand: south route" (bends a e) #[⟨0, 50⟩, ⟨0, 90⟩, ⟨100, 90⟩, ⟨100, 50⟩]
  -- self_loop_router_routes_corner_and_dummy_combined_loops_with_labels
  let ((n, es), a) ← LayeredM.run (do
      let (n, _) ← cornerAndDummyCombined
      let some g ← nodeGraph n | return (n, #[])
      runRouter g
      runPost g
      let some h ← SelfLoopHolder.get? n | return (n, #[])
      return (n, h.allSelfLoopEdges))
  checkEq "routes_corner_and_dummy_combined: three self loops" es.size 3
  check "routes_corner_and_dummy_combined: labels stay attached" (es.all fun e => (a.edge e).labels.size == 1)
  check "routes_corner_and_dummy_combined: bend points present" (es.all fun e => !(bends a e).isEmpty)
  check "routes_corner_and_dummy_combined: routes leave the node" (es.all fun e => hasOutsidePoint a n (bends a e))

-- ptides_self_loop_margin_test.rs ----------------------------------------------------------

def ptidesTests : Suite := suite "layered.intermediate.selfLoopRouter.ptides" do
  let ((n, e, hasHolder), a) ← LayeredM.run (do
      let (g, n, _, e) ← ptidesGraph
      runPre g
      let hasHolder := (← getNode n).internal.selfLoopHolder.isSome
      let _ ← moveToLayer g n
      runRestorer g
      runRouter g
      return (n, e, hasHolder))
  check "opposing_east_west_fixedpos: holder installed" hasHolder
  check "opposing_east_west_fixedpos_extends_west_margin" (((marginOf a n).left - 28.0).abs < 1.0)
  checkEq "east_west_fixedpos_self_loop_detected_as_two_sides_opposing" (loopOf a n 0).selfLoopType (some .twoSidesOpposing)
  checkEq "hand: occupied E, S, W (option 1 wins the penalty tie)" (loopOf a n 0).occupiedPortSides
    (EnumSet.of #[PortSide.east, .south, .west])
  checkEq "hand: WEST shifted to slot 1 by the shared port column" (slotsOf a n 0) #[0, 0, 0, 1]
  checkEq "hand: routingSlotCount" (holderOf a n).routingSlotCount #[0, 1, 1, 1, 2]
  checkEq "hand: route (WEST slot 1 at -(8+10)-10)" (bends a e) #[⟨131, 7⟩, ⟨131, 40⟩, ⟨-28, 40⟩, ⟨-28, 15⟩]
  checkEqR "hand: margins" (marginOf a n) { left := 28, right := 10, bottom := 10 }

-- polyline_self_loop_router_test.rs ---------------------------------------------------------

def polylineTests : Suite := suite "layered.intermediate.loops.polylineSelfLoopRouter" do
  let input : KVectorChain := #[⟨0, 0⟩, ⟨100, 0⟩, ⟨100, 100⟩, ⟨-100, 100⟩, ⟨-100, -100⟩, ⟨0, -100⟩]
  let ok (r : Except String KVectorChain) : KVectorChain := match r with | .ok v => v | .error _ => #[]
  checkEq "test_usual_case" (ok (PolylineSelfLoopRouter.cutCorners input 10))
    #[⟨90, 0⟩, ⟨100, 10⟩, ⟨100, 90⟩, ⟨90, 100⟩, ⟨-90, 100⟩, ⟨-100, 90⟩, ⟨-100, -90⟩, ⟨-90, -100⟩]
  checkEq "test_smaller_distance" (ok (PolylineSelfLoopRouter.cutCorners input 80))
    #[⟨50, 0⟩, ⟨100, 50⟩, ⟨100, 50⟩, ⟨50, 100⟩, ⟨-20, 100⟩, ⟨-100, 20⟩, ⟨-100, -50⟩, ⟨-50, -100⟩]
  let isError (r : Except String KVectorChain) : Bool := match r with | .ok _ => false | .error _ => true
  check "hand: two points are rejected (assert)" (isError (PolylineSelfLoopRouter.cutCorners #[⟨0, 0⟩, ⟨1, 0⟩] 10))
  check "hand: diagonal corners are rejected (assert)" (isError (PolylineSelfLoopRouter.cutCorners #[⟨0, 0⟩, ⟨5, 5⟩, ⟨10, 0⟩] 10))
  checkEq "hand: tolerance 0.01 keeps nearly straight corners" (ok (PolylineSelfLoopRouter.cutCorners #[⟨0, 0⟩, ⟨0.0078125, 20⟩, ⟨30, 20⟩] 10))
    #[⟨0.0078125, 10⟩, ⟨10.0078125, 20⟩]

-- Hand-derived routes (FIXED_ORDER node 40x30 at (100, 200): ports keep sides and order) --------

/-- A `FIXED_ORDER` node 40x30 at `(100, 200)` in a graph with the given `EDGE_ROUTING`. -/
def handNode (routing : Option EdgeRouting) : LayeredM (LGraphId × LNodeId) := do
  let g ← createGraph
  if let some r := routing then setGraphProp g LayeredOptions.EDGE_ROUTING r
  let n ← addNode g { size := ⟨40, 30⟩, position := ⟨100, 200⟩ }
  setConstraints n .fixedOrder
  return (g, n)

/-- Two north ports `(10,0)`, `(30,0)` and the loop between them. -/
def twoPortCase (routing : Option EdgeRouting) : LayeredM (LNodeId × Array LEdgeId) := do
  let (g, n) ← handNode routing
  let a ← mkPort n .north 10 0
  let b ← mkPort n .north 30 0
  let e ← mkEdge a b
  preRestoreRoute g n
  return (n, #[e])

/-- West `(0,20)` → north `(30,0)`. -/
def cornerCase (routing : Option EdgeRouting) : LayeredM (LNodeId × Array LEdgeId) := do
  let (g, n) ← handNode routing
  let w ← mkPort n .west 0 20
  let t ← mkPort n .north 30 0
  let e ← mkEdge w t
  preRestoreRoute g n
  return (n, #[e])

/-- West `(0,20)`, north `(20,0)`, east `(40,10)`; loops west → north and west → east. -/
def threeSidedCase (routing : Option EdgeRouting) : LayeredM (LNodeId × Array LEdgeId) := do
  let (g, n) ← handNode routing
  let w ← mkPort n .west 0 20
  let t ← mkPort n .north 20 0
  let e ← mkPort n .east 40 10
  let e0 ← mkEdge w t
  let e1 ← mkEdge w e
  preRestoreRoute g n
  return (n, #[e0, e1])

/-- North `(20,0)`, east `(40,15)`, south `(20,30)`, west `(0,15)`; loops n → s, s → e, w → n. -/
def fourSidedCase (routing : Option EdgeRouting) : LayeredM (LNodeId × Array LEdgeId) := do
  let (g, n) ← handNode routing
  let pn ← mkPort n .north 20 0
  let pe ← mkPort n .east 40 15
  let ps ← mkPort n .south 20 30
  let pw ← mkPort n .west 0 15
  let e0 ← mkEdge pn ps
  let e1 ← mkEdge ps pe
  let e2 ← mkEdge pw pn
  preRestoreRoute g n
  return (n, #[e0, e1, e2])

def handRouteTests : Suite := suite "layered.intermediate.selfLoopRouter.hand" do
  -- one-port loop (FREE, pre/restorer hide and restore the port)
  let ((_, e), a) ← LayeredM.run (do
      let (g, n, e) ← onePortGraph (some .polyline)
      preRestoreRoute g n
      return (n, e))
  checkEq "hand: POLYLINE one-port loop keeps duplicate points" (bends a e) #[⟨20, -10⟩, ⟨20, -10⟩, ⟨20, -10⟩, ⟨20, -10⟩]
  let ((_, e), a) ← LayeredM.run (do
      let (g, n, e) ← onePortGraph (some .splines)
      preRestoreRoute g n
      return (n, e))
  checkEq "hand: SPLINES one-port loop Bézier control points" (bends a e) #[⟨20, -10⟩, ⟨20, -11⟩, ⟨20, -11⟩, ⟨20, -11⟩, ⟨20, -10⟩]
  -- two ports on the same side
  let ((n, es), a) ← LayeredM.run (twoPortCase none)
  checkEq "hand: ORTHOGONAL two-port loop" (bends a es[0]!) #[⟨10, -10⟩, ⟨30, -10⟩]
  checkEq "hand: two-port loop leftmost/rightmost by port id" ((loopOf a n 0).leftmostPort.map (·.idx), (loopOf a n 0).rightmostPort.map (·.idx)) (some 0, some 1)
  checkEq "hand: two-port loop type and occupied sides" ((loopOf a n 0).selfLoopType, (loopOf a n 0).occupiedPortSides) (some .oneSide, EnumSet.of #[PortSide.north])
  let ((_, es), a) ← LayeredM.run (twoPortCase (some .polyline))
  checkEq "hand: POLYLINE two-port loop" (bends a es[0]!) #[⟨10, -5⟩, ⟨15, -10⟩, ⟨25, -10⟩, ⟨30, -5⟩]
  let ((_, es), a) ← LayeredM.run (twoPortCase (some .splines))
  checkEq "hand: SPLINES two-port loop" (bends a es[0]!) #[⟨10, -10⟩, ⟨15, -11⟩, ⟨20, -11⟩, ⟨25, -11⟩, ⟨30, -10⟩]
  -- corner loop
  let ((n, es), a) ← LayeredM.run (cornerCase none)
  checkEq "hand: corner loop type" (loopOf a n 0).selfLoopType (some .twoSidesCorner)
  checkEq "hand: corner loop occupies W, N" (loopOf a n 0).occupiedPortSides (EnumSet.of #[PortSide.west, .north])
  checkEq "hand: ORTHOGONAL corner loop" (bends a es[0]!) #[⟨-10, 20⟩, ⟨-10, -10⟩, ⟨30, -10⟩]
  checkEqR "hand: corner loop margins" (marginOf a n) { left := 10, top := 10 }
  let ((_, es), a) ← LayeredM.run (cornerCase (some .polyline))
  checkEq "hand: POLYLINE corner loop" (bends a es[0]!) #[⟨-5, 20⟩, ⟨-10, 15⟩, ⟨-10, 0⟩, ⟨0, -10⟩, ⟨25, -10⟩, ⟨30, -5⟩]
  let ((_, es), a) ← LayeredM.run (cornerCase (some .splines))
  let sp := bends a es[0]!
  checkEq "hand: SPLINES corner loop: 4 Bézier segments minus both ends" sp.size 11
  checkEq "hand: SPLINES corner loop: clamped ends keep the 2nd and next-to-last polygon points"
    (sp[0]!, sp[sp.size - 1]!) (⟨-10, 20⟩, ⟨30, -10⟩)
  -- three-sided loop
  let ((n, es), a) ← LayeredM.run (threeSidedCase none)
  checkEq "hand: three-sided loop type" (loopOf a n 0).selfLoopType (some .threeSides)
  checkEq "hand: three-sided loop occupies W, N, E" (loopOf a n 0).occupiedPortSides (EnumSet.of #[PortSide.west, .north, .east])
  checkEq "hand: ORTHOGONAL three-sided loop, west → north" (bends a es[0]!) #[⟨-10, 20⟩, ⟨-10, -10⟩, ⟨20, -10⟩]
  checkEq "hand: ORTHOGONAL three-sided loop, west → east (opposite, clockwise)" (bends a es[1]!)
    #[⟨-10, 20⟩, ⟨-10, -10⟩, ⟨50, -10⟩, ⟨50, 10⟩]
  checkEq "hand: three-sided routingSlotCount" (holderOf a n).routingSlotCount #[0, 1, 1, 1, 1]
  let ((_, es), a) ← LayeredM.run (threeSidedCase (some .polyline))
  checkEq "hand: POLYLINE three-sided loop, west → east" (bends a es[1]!)
    #[⟨-5, 20⟩, ⟨-10, 15⟩, ⟨-10, 0⟩, ⟨0, -10⟩, ⟨40, -10⟩, ⟨50, 0⟩, ⟨50, 5⟩, ⟨45, 10⟩]
  -- four-sided loop
  let ((n, es), a) ← LayeredM.run (fourSidedCase none)
  checkEq "hand: four-sided loop type" (loopOf a n 0).selfLoopType (some .fourSides)
  checkEq "hand: four-sided loop edges in BFS order" ((loopOf a n 0).slEdges.map fun e => ((holderOf a n).slEdge e).lEdge) #[es[0]!, es[2]!, es[1]!]
  checkEq "hand: four-sided route from the first to the last port id" (((loopOf a n 0).leftmostPort.map (·.idx)), ((loopOf a n 0).rightmostPort.map (·.idx)))
    (some 0, some 3)
  checkEq "hand: ORTHOGONAL four-sided loop, north → south over EAST" (bends a es[0]!) #[⟨20, -10⟩, ⟨50, -10⟩, ⟨50, 40⟩, ⟨20, 40⟩]
  checkEq "hand: ORTHOGONAL four-sided loop, south → east (counter-clockwise)" (bends a es[1]!) #[⟨20, 40⟩, ⟨50, 40⟩, ⟨50, 15⟩]
  checkEq "hand: ORTHOGONAL four-sided loop, west → north" (bends a es[2]!) #[⟨-10, 15⟩, ⟨-10, -10⟩, ⟨20, -10⟩]
  checkEqR "hand: four-sided margins" (marginOf a n) { top := 10, right := 10, bottom := 10, left := 10 }
  let ((_, es), a) ← LayeredM.run (fourSidedCase (some .polyline))
  checkEq "hand: POLYLINE four-sided loop, south → east" (bends a es[1]!) #[⟨20, 35⟩, ⟨25, 40⟩, ⟨40, 40⟩, ⟨50, 30⟩, ⟨50, 20⟩, ⟨45, 15⟩]

-- Labels, label placer, processor -----------------------------------------------------------

def labelTests : Suite := suite "layered.intermediate.selfLoopRouter.labels" do
  -- a loop with two labels (horizontal layout, label spacing 1)
  let ((n, e, ls), a) ← LayeredM.run (do
      let (g, n) ← handNode none
      setGraphProp g LayeredOptions.DIRECTION .right
      setGraphProp g LayeredOptions.SPACING_LABEL_LABEL 1.0
      let p ← mkPort n .north 10 0
      let q ← mkPort n .north 30 0
      let e ← mkEdge p q
      let l0 ← addLabel e 10 4
      let l1 ← addLabel e 6 5
      preRestoreRoute g n
      return (n, e, #[l0, l1]))
  checkEq "hand: two-label block size (horizontal: max width, heights + spacing)" (labelBlock a n 0).size ⟨10, 10⟩
  checkEq "hand: two-label block position (centred, lane -10 - 2 - 10)" (labelBlock a n 0).position ⟨15, -22⟩
  checkEq "hand: two-label positions (stacked, centred)" (ls.map fun l => (a.label l).position) #[⟨15, -22⟩, ⟨17, -17⟩]
  checkEq "hand: two-label edge route" (bends a e) #[⟨10, -10⟩, ⟨30, -10⟩]
  checkEqR "hand: two-label margins" (marginOf a n) { top := 22 }
  -- standalone LabelPlacer.placeLabels (absolute positions, base offset 5)
  let ((n, l), a) ← LayeredM.run (do
      let (g, n, es) ← parallelNorthGraph true
      preAndRestore g n
      RoutingDirector.determineLoopRoutes n
      let _ ← RoutingSlotAssigner.assignRoutingSlotsOf n (Random.ofInt 0)
      LabelPlacer.placeLabels n 5.0
      return (n, (← getEdge es[0]!).labels[0]!))
  checkEq "hand: LabelPlacer.placeLabels absolute position (slot 0, offset 5)" (a.label l).position ⟨43, 17⟩
  checkEq "hand: LabelPlacer.placeLabels block position" (labelBlock a n 0).position ⟨43, 17⟩
  checkEq "hand: LabelPlacer.placeLabels outer loop (slot 1: 5 + 1 * (3.75 + 2))" (labelBlock a n 1).position ⟨43, 11.25⟩
  -- one-sided EAST loop: TOP alignment at the topmost port
  let ((n, l), a) ← LayeredM.run (do
      let (g, n) ← handNode none
      let p ← mkPort n .east 40 20
      let q ← mkPort n .east 40 5
      let e ← mkEdge p q
      let l ← addLabel e 8 6
      preRestoreRoute g n
      return (n, l))
  checkEq "hand: EAST one-sided label: TOP alignment at the topmost port"
    ((labelBlock a n 0).side, (labelBlock a n 0).alignment, (labelBlock a n 0).alignmentReferenceSLPort.map (·.idx)) (.east, .top, some 1)
  checkEq "hand: EAST label position (lane 50 + 2, top at y 5)" (a.label l).position ⟨52, 5⟩
  -- registration and random generator
  let router ← IntermediateProcessorStrategy.create .selfLoopRouter
  checkEq "registered processor name" router.name "SelfLoopRouter"
  checkEq "hand: router per edge routing"
    (#[EdgeRouting.orthogonal, .polyline, .splines, .undefined].map fun r => (SelfLoopRouter.routerFor r).name)
    #["OrthogonalSelfLoopRouter", "PolylineSelfLoopRouter", "SplineSelfLoopRouter", "OrthogonalSelfLoopRouter"]
  let ((g, n), a) ← LayeredM.run (do
      let (g, n, _) ← parallelNorthGraph true (some .sequenced) #[8, 20, 58, 72]
      modifyGraph g fun x => { x with internal := { x.internal with random := some (Random.ofInt 42) } }
      preRestoreRoute g n
      return (g, n))
  check "hand: graph random kept (no draws for a two-segment cycle)" (((a.graph g).internal.random.map (·.seed)) == some (Random.ofInt 42).seed)
  checkEq "hand: holder ports and routing kept with a stored random" ((slotsOf a n 0)[0]!, (slotsOf a n 1)[0]!) (0, 0)

def suites : Array Suite := #[routerRustTests, ptidesTests, polylineTests, handRouteTests, labelTests]

end Tests.Layered.IntermediateSelfLoopRouting
