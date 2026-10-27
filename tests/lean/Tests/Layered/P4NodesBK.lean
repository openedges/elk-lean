import Tests.Framework
import Elk.Alg.Layered
import Elk.Alg.Layered.P4Nodes
import Elk.Json
import Std.Data.HashMap
/-!
Tests of `org.eclipse.elk.alg.layered.p4nodes.bk` (Brandes & Köpf node placement) on hand-built
layered graphs. Expected coordinates marked "hand:" were derived by stepping through the
Java/Rust algorithm (alignment, inner shifts, compaction, threshold, balancing); the ordering
assertions port `basic_node_placement_test.rs` / `network_simplex_bk_test.rs`.
-/
namespace Tests.Layered.P4NodesBK

open Tests Elk.Graph Elk.Core.Math Elk.Core.Util Elk.Core.Options Elk.Core.Alg Elk.Alg.Layered
  Elk.Alg.Layered.Graph Elk.Alg.Layered.Options Elk.Alg.Layered.P4Nodes.BK

/-- Graph options of a test run. -/
def optProps (align : Option FixedAlignment := none) (straightening : Option EdgeStraighteningStrategy := none)
    (favor : Option Bool := none) : PropertyMap := Id.run do
  let mut p : PropertyMap := {}
  if let some a := align then p := p.set LayeredOptions.NODE_PLACEMENT_BK_FIXED_ALIGNMENT a
  if let some s := straightening then p := p.set LayeredOptions.NODE_PLACEMENT_BK_EDGE_STRAIGHTENING s
  if let some f := favor then p := p.set LayeredOptions.NODE_PLACEMENT_FAVOR_STRAIGHT_EDGES f
  return p

/-- A graph with `nLayers` empty layers and the spacings of `props`. -/
def mkGraph (props : PropertyMap) (nLayers : Nat) (withSpacings : Bool := true) : LayeredM (LGraphId × Array LayerId) := do
  let spacings := if withSpacings then some (Spacings.new props) else none
  let g ← LayeredM.createGraph { props := props, internal := { spacings := spacings } }
  let mut ls : Array LayerId := #[]
  for _ in [0:nLayers] do
    ls := ls.push (← LayeredM.createLayer g)
  LayeredM.modifyGraph g fun x => { x with layers := ls }
  return (g, ls)

/-- A node of size `w × h` appended to `layer`. -/
def mkNode (g : LGraphId) (layer : LayerId) (w h : Float) (type : NodeType := .normal) : LayeredM LNodeId := do
  let n ← LayeredM.createNode g { size := ⟨w, h⟩, type := type }
  LayeredM.setNodeLayer n (some layer)
  return n

/-- A port of `n` at relative y position `y` (anchor `(0, 0)`). -/
def mkPort (n : LNodeId) (side : PortSide) (y : Float) : LayeredM LPortId := do
  let p ← LayeredM.createPort { side := side, position := ⟨0, y⟩ }
  LayeredM.setPortNode p (some n)
  return p

/-- An edge `s → t`. -/
def mkEdge (s t : LPortId) : LayeredM LEdgeId := do
  let e ← LayeredM.createEdge
  LayeredM.setEdgeSource e (some s)
  LayeredM.setEdgeTarget e (some t)
  return e

/-- 2-layer chain `A → B`: A 30×30 with its port at y 15, B 30×40 with its port at y 20. -/
def buildChain (props : PropertyMap) : LayeredM (LGraphId × Array LNodeId) := do
  let (g, ls) ← mkGraph props 2
  let a ← mkNode g ls[0]! 30 30
  let b ← mkNode g ls[1]! 30 40
  let _ ← mkEdge (← mkPort a .east 15) (← mkPort b .west 20)
  return (g, #[a, b])

/-- 3-layer diamond `A → B, A → C, B → D, C → D` (all 30×30, ports at y 15; the graph of the
Rust BK tests). -/
def buildDiamond (props : PropertyMap) : LayeredM (LGraphId × Array LNodeId) := do
  let (g, ls) ← mkGraph props 3
  let a ← mkNode g ls[0]! 30 30
  let b ← mkNode g ls[1]! 30 30
  let c ← mkNode g ls[1]! 30 30
  let d ← mkNode g ls[2]! 30 30
  let pa ← mkPort a .east 15
  let _ ← mkEdge pa (← mkPort b .west 15)
  let _ ← mkEdge pa (← mkPort c .west 15)
  let pd ← mkPort d .west 15
  let _ ← mkEdge (← mkPort b .east 15) pd
  let _ ← mkEdge (← mkPort c .east 15) pd
  return (g, #[a, b, c, d])

/-- Layers `[P, Q] | [B, C]`, edges `Q → B` (Q port at y 10) and `Q → C` (Q port at y 100);
P, B, C 30×30 (ports at y 15), Q 30×120. C cannot join Q's block; the simple threshold
strategy moves it down to straighten `Q → C`. -/
def buildThreshold (props : PropertyMap) : LayeredM (LGraphId × Array LNodeId) := do
  let (g, ls) ← mkGraph props 2
  let p ← mkNode g ls[0]! 30 30
  let q ← mkNode g ls[0]! 30 120
  let b ← mkNode g ls[1]! 30 30
  let c ← mkNode g ls[1]! 30 30
  let _ ← mkEdge (← mkPort q .east 10) (← mkPort b .west 15)
  let _ ← mkEdge (← mkPort q .east 100) (← mkPort c .west 15)
  return (g, #[p, q, b, c])

/-- Layers `[S] | [d1, u] | [v, d2]` with the long edge `S → d1 → d2` (dummies 0×0, ports at
y 0) and the short edge `u → v` crossing its inner segment (a type 1 conflict). -/
def buildConflict (props : PropertyMap) : LayeredM (LGraphId × Array LNodeId × LEdgeId) := do
  let (g, ls) ← mkGraph props 3
  let s ← mkNode g ls[0]! 30 30
  let d1 ← mkNode g ls[1]! 0 0 .longEdge
  let u ← mkNode g ls[1]! 30 30
  let v ← mkNode g ls[2]! 30 30
  let d2 ← mkNode g ls[2]! 0 0 .longEdge
  let _ ← mkEdge (← mkPort s .east 15) (← mkPort d1 .west 0)
  let _ ← mkEdge (← mkPort d1 .east 0) (← mkPort d2 .west 0)
  let euv ← mkEdge (← mkPort u .east 15) (← mkPort v .west 15)
  return (g, #[s, d1, u, v, d2], euv)

/-- Runs the placer and returns the y positions of the listed nodes, the graph and the arena. -/
def place (build : PropertyMap → LayeredM (LGraphId × Array LNodeId)) (props : PropertyMap)
    (monitor : Option ProgressMonitor := none) : IO (Array Float × LGraphId × LGraphArena) := do
  let monitor ← match monitor with
    | some m => pure m
    | none => ProgressMonitor.basic
  let ((g, nodes), a) ← LayeredM.run (do
    let (g, nodes) ← build props
    BKNodePlacer.process g monitor
    return (g, nodes))
  return (nodes.map fun n => (a.node n).position.y, g, a)

/-- `assert_layer_node_positions_increasing`: in every layer each node starts below the bottom
of its predecessor. -/
def positionsIncreasing (a : LGraphArena) (g : LGraphId) : Bool := Id.run do
  for l in (a.graph g).layers do
    let mut lastBottom : Option Float := none
    for n in (a.layer l).nodes do
      let nd := a.node n
      if let some lb := lastBottom then
        if !(lb < nd.position.y) then return false
      lastBottom := some (nd.position.y + nd.size.y)
  return true

/-- The smallest gap between consecutive nodes of a layer (`+∞` without pairs). -/
def minGap (a : LGraphArena) (g : LGraphId) : Float := Id.run do
  let mut gap := Float.posInf
  for l in (a.graph g).layers do
    let mut lastBottom : Option Float := none
    for n in (a.layer l).nodes do
      let nd := a.node n
      if let some lb := lastBottom then gap := fmin gap (nd.position.y - lb)
      lastBottom := some (nd.position.y + nd.size.y)
  return gap

def allAlignments : Array FixedAlignment := #[.none, .leftUp, .leftDown, .rightUp, .rightDown, .balanced]
def allStraightenings : Array EdgeStraighteningStrategy := #[.none, .improveStraightness]

def neighborhoodTests : Suite := suite "layered.p4nodes.bk.NeighborhoodInformation" do
  let ((ni, nodes, layerIds, prioNi), a) ← LayeredM.run (do
    let (g, nodes) ← buildDiamond {}
    let ni ← NeighborhoodInformation.buildFor g
    let layerIds ← (← LayeredM.getGraph g).layers.mapM fun l => do return (← LayeredM.getLayer l).id
    -- priorities: A → B (prio 2), A → C (prio 1): only the maximal priority survives
    let (g2, ls) ← mkGraph {} 2
    let x ← mkNode g2 ls[0]! 30 30
    let y1 ← mkNode g2 ls[1]! 30 30
    let y2 ← mkNode g2 ls[1]! 30 30
    let px ← mkPort x .east 15
    let e1 ← mkEdge px (← mkPort y1 .west 15)
    let e2 ← mkEdge px (← mkPort y2 .west 15)
    LayeredM.setEdgeProp e1 LayeredOptions.PRIORITY_STRAIGHTNESS 1
    LayeredM.setEdgeProp e2 LayeredOptions.PRIORITY_STRAIGHTNESS 2
    let prioNi ← NeighborhoodInformation.buildFor g2
    return (ni, nodes, layerIds, (prioNi, e2)))
  checkEq "node count" ni.nodeCount 4
  checkEq "node ids assigned in layer order" (nodes.map fun n => (a.node n).id) #[0, 1, 2, 3]
  checkEq "layer ids = layer indices" layerIds #[0, 1, 2]
  checkEq "layer index" ni.layerIndex #[0, 1, 2]
  checkEq "in-layer node index" ni.nodeIndex #[0, 0, 1, 0]
  checkEq "left neighbors of D (B then C)" ((ni.leftNeighbors[3]!).map (·.1)) #[1, 2]
  checkEq "right neighbors of A (B then C)" ((ni.rightNeighbors[0]!).map (·.1)) #[1, 2]
  checkEq "A has no left neighbors" (ni.leftNeighbors[0]!).size 0
  checkEq "D has no right neighbors" (ni.rightNeighbors[3]!).size 0
  let (pni, e2) := prioNi
  checkEq "only the highest straightness priority is kept" ((pni.rightNeighbors[0]!).map (·.2)) #[e2]

def chainTests : Suite := suite "layered.p4nodes.bk.chain" do
  -- hand: block A-B; inner shift: B port (20) − A port (15) ⇒ A moves down by 5 inside the block
  for align in allAlignments do
    let (ys, _, _) ← place buildChain (optProps (align := some align))
    checkFloat s!"{align}: A.y (hand: 5)" ys[0]! 5.0
    checkFloat s!"{align}: B.y (hand: 0)" ys[1]! 0.0
    checkFloat s!"{align}: edge straight (A.y + 15 = B.y + 20)" (ys[0]! + 15.0) (ys[1]! + 20.0)

def diamondTests : Suite := suite "layered.p4nodes.bk.diamond" do
  -- hand (balanced): RD/LD give A=B=D=0, C=50; RU/LU give A=C=D=0, B=−50; widths all 80, RD is the
  -- reference, UP layouts shift by 50; medians: A=(0+50)/2, B=0, C=50, D=(0+50)/2
  let (ys, g, a) ← place buildDiamond (optProps)
  checkFloat "balanced A.y (hand: 25)" ys[0]! 25.0
  checkFloat "balanced B.y (hand: 0)" ys[1]! 0.0
  checkFloat "balanced C.y (hand: 50)" ys[2]! 50.0
  checkFloat "balanced D.y (hand: 25)" ys[3]! 25.0
  check "balanced: positions increase" (positionsIncreasing a g)
  checkFloat "balanced: node spacing 20 between B and C" (minGap a g) 20.0
  let (ysB, _, _) ← place buildDiamond (optProps (align := some .balanced))
  checkEq "BALANCED = NONE (same balanced layout)" ysB ys
  -- fixed alignments: DOWN aligns A-B-D (C below), UP aligns A-C-D (B above): mirrored results
  let (rd, _, _) ← place buildDiamond (optProps (align := some .rightDown))
  checkEq "RIGHTDOWN (hand: 0, 0, 50, 0)" rd #[0.0, 0.0, 50.0, 0.0]
  let (ld, _, _) ← place buildDiamond (optProps (align := some .leftDown))
  checkEq "LEFTDOWN (hand: 0, 0, 50, 0)" ld #[0.0, 0.0, 50.0, 0.0]
  let (ru, _, _) ← place buildDiamond (optProps (align := some .rightUp))
  checkEq "RIGHTUP (hand: 0, -50, 0, 0)" ru #[0.0, -50.0, 0.0, 0.0]
  let (lu, _, _) ← place buildDiamond (optProps (align := some .leftUp))
  checkEq "LEFTUP (hand: 0, -50, 0, 0)" lu #[0.0, -50.0, 0.0, 0.0]
  check "UP mirrors DOWN (C.y − B.y equal)" (rd[2]! - rd[1]! == ru[2]! - ru[1]!)
  -- favorStraightEdges without fixed alignment: no balancing, the first smallest layout (RIGHTDOWN)
  let (fav, _, _) ← place buildDiamond (optProps (favor := some true))
  checkEq "favorStraightEdges picks RIGHTDOWN (hand: 0, 0, 50, 0)" fav rd
  check "favorStraightEdges: A → B → D straight" (fav[0]! == fav[1]! && fav[1]! == fav[3]!)
  check "balanced: no edge of A straight" (ys[0]! != ys[1]! && ys[0]! != ys[2]!)
  let (favBal, _, _) ← place buildDiamond (optProps (align := some .balanced) (favor := some true))
  checkEq "BALANCED overrides favorStraightEdges" favBal ys

def straighteningTests : Suite := suite "layered.p4nodes.bk.straightening" do
  -- hand (RIGHTDOWN): block Q-B (inner Q=5), Q.y = 30 + 20 − 5 = 45 (block), C below B needs 95;
  -- the simple threshold of C's root edge Q → C is 45 + 5 + 100 − 15 = 135 ⇒ C.y = max(95, 135)
  let (ys, g, a) ← place buildThreshold (optProps (align := some .rightDown))
  checkFloat "P.y (hand: 0)" ys[0]! 0.0
  checkFloat "Q.y (hand: 50)" ys[1]! 50.0
  checkFloat "B.y (hand: 45)" ys[2]! 45.0
  checkFloat "IMPROVE_STRAIGHTNESS: C.y (hand: 135)" ys[3]! 135.0
  checkFloat "Q → C straight" (ys[1]! + 100.0) (ys[3]! + 15.0)
  checkFloat "Q → B straight" (ys[1]! + 10.0) (ys[2]! + 15.0)
  check "positions increase" (positionsIncreasing a g)
  let (ysNone, _, _) ← place buildThreshold (optProps (align := some .rightDown) (straightening := some .none))
  checkFloat "NONE (null threshold): C.y (hand: 95)" ysNone[3]! 95.0
  checkEq "NONE: other nodes unchanged" (ysNone.extract 0 3) (ys.extract 0 3)
  check "NONE: Q → C not straight" (ysNone[1]! + 100.0 != ysNone[3]! + 15.0)

def conflictTests : Suite := suite "layered.p4nodes.bk.conflicts" do
  let ((marked, euv, nodes), a) ← LayeredM.run (do
    let (g, nodes, euv) ← buildConflict {}
    let ni ← NeighborhoodInformation.buildFor g
    let layers := (← LayeredM.getGraph g).layers
    let a ← get
    let marked ← BKNodePlacer.markConflicts a layers ni
    return (marked, euv, nodes))
  checkEq "one type 1 conflict marked" marked.size 1
  check "the short edge u → v is marked" (marked.contains euv)
  checkEq "dummy types" ((nodes.extract 1 2).map fun n => (a.node n).type) #[NodeType.longEdge]
  -- hand (RIGHTDOWN): block S-d1-d2 (inner d1 = d2 = 15); v placed first at 0, the block below v:
  -- 30 + 10 (edge-node spacing) − 15 = 25; u below d1: 25 + 15 + 10 = 50
  let ((ys, g), a2) ← LayeredM.run (do
    let (g, nodes, _) ← buildConflict (optProps (align := some .rightDown))
    BKNodePlacer.process g (← ProgressMonitor.basic)
    return (← nodes.mapM fun n => do return (← LayeredM.getNode n).position.y, g))
  checkEq "RIGHTDOWN S, d1, u, v, d2 (hand: 25, 40, 50, 0, 40)" ys #[25.0, 40.0, 50.0, 0.0, 40.0]
  check "long edge straight (S port = d1 = d2)" (ys[0]! + 15.0 == ys[1]! && ys[1]! == ys[4]!)
  check "conflict graph: positions increase" (positionsIncreasing a2 g)
  checkFloat "edge-node spacing respected" (minGap a2 g) 10.0
  -- three layers without conflicts: nothing marked
  let ((markedDiamond), _) ← LayeredM.run (do
    let (g, _) ← buildDiamond {}
    let ni ← NeighborhoodInformation.buildFor g
    let layers := (← LayeredM.getGraph g).layers
    BKNodePlacer.markConflicts (← get) layers ni)
  checkEq "diamond: no conflicts" markedDiamond.size 0

def basicPlacementTests : Suite := suite "layered.p4nodes.bk.basicPlacement" do
  -- port of `bk_node_placement_variants_keep_nodes_ordered` on the hand-built graphs
  for align in allAlignments do
    for straightening in allStraightenings do
      let props := optProps (align := some align) (straightening := some straightening)
      let (_, g, a) ← place buildDiamond props
      check s!"diamond {align}/{straightening}: positions increase" (positionsIncreasing a g)
      check s!"diamond {align}/{straightening}: node spacing ≥ 20" (minGap a g ≥ 20.0 - 1e-9)
      let (_, g2, a2) ← place buildThreshold props
      check s!"threshold graph {align}/{straightening}: positions increase" (positionsIncreasing a2 g2)
      check s!"threshold graph {align}/{straightening}: node spacing ≥ 20" (minGap a2 g2 ≥ 20.0 - 1e-9)
      let ((g3, a3)) ← (do
        let ((g, _), a) ← LayeredM.run (do
          let (g, nodes, _) ← buildConflict props
          BKNodePlacer.process g (← ProgressMonitor.basic)
          return (g, nodes))
        return (g, a))
      check s!"conflict graph {align}/{straightening}: positions increase" (positionsIncreasing a3 g3)

def phaseTests : Suite := suite "layered.p4nodes.bk.phase" do
  -- registration via the strategy factory used by GraphConfigurator
  let factory := LayeredPhases.strategyFactory .p4NodePlacement "NodePlacementStrategy"
    (Elk.ElkEnum.ordinal NodePlacementStrategy.brandesKoepf) (Elk.ElkEnum.javaName NodePlacementStrategy.brandesKoepf)
  let phase ← factory.create
  checkEq "registered phase name" phase.name "BKNodePlacer"
  let ((cfgNone, cfgExt), _) ← LayeredM.run (do
    let (g, _) ← buildChain {}
    let cfg ← BKNodePlacer.getLayoutProcessorConfiguration g
    LayeredM.modifyGraph g fun x => { x with internal.graphProperties := x.internal.graphProperties.insert .externalPorts }
    let ext ← BKNodePlacer.getLayoutProcessorConfiguration g
    return (cfg, ext))
  check "no configuration without external ports" cfgNone.isNone
  checkEq "hierarchical port position processor before P5"
    ((cfgExt.map (·.processorsBefore .p5EdgeRouting)).getD #[])
    #[Intermediate.IntermediateProcessorStrategy.hierarchicalPortPositionProcessor]
  checkThrows "missing spacings throws" (do
    let _ ← LayeredM.run (do
      let (g, ls) ← mkGraph {} 1 (withSpacings := false)
      let _ ← mkNode g ls[0]! 10 10
      BKNodePlacer.process g (← ProgressMonitor.basic))
    pure ())
  -- an empty graph is a no-op
  let ((), _) ← LayeredM.run (do
    let (g, _) ← mkGraph {} 0
    BKNodePlacer.process g (← ProgressMonitor.basic))
  check "empty graph placed" true
  -- layout names and logging
  checkEq "layout names" ((#[(some VDirection.down, some HDirection.right), (some .up, some .left), (none, none)]).map
    fun (v, h) => toString (BKAlignedLayout.new 0 v h)) #["RIGHTDOWN", "LEFTUP", "BALANCED"]
  let monitor ← (← ProgressMonitor.basic).withLogging
  let _ ← place buildDiamond (optProps) (monitor := some monitor)
  let logs ← monitor.logs
  check "logs the layout sizes" (logs.contains "RIGHTDOWN size is 80")
  check "logs the feasibility of the balanced layout" (logs.contains "BALANCED is feasible: true")
  check "logs the chosen layout" (logs.contains "Chosen node placement: BALANCED")
  check "logs the number of marked edges" (logs.contains "Marked edges: 0")
  check "monitor done" (← monitor.isClosed)

/-! ## Optional oracle replay

`ELK_BK_ORACLE_TRACES` = `:`-separated elk-rs phase-trace directories (`--trace-dir` of the oracle
runner, one directory per model). For every `step_NNN_BKNodePlacer.json` the preceding step is
loaded into an arena (layers, node sizes/margins/types, ports with positions/anchors, edges in
trace order; default graph options with `favorStraightEdges = true` as set by the configurator for
orthogonal routing) and the placer's node y coordinates are compared with the
oracle step. Skipped when the variable is unset. Limitation: the trace does not record the order
of a port's `incomingEdges` (BK reads it from the live graph), so the replay rebuilds it from the
edge list order; graphs with several edges into one port from the same node can differ for that
reason alone. -/
namespace Replay

open Elk.Json

private def num (v : Value) (k : String) : Float := ((v.get? k).bind (·.getFloat?)).getD 0.0
private def str (v : Value) (k : String) : String := ((v.get? k).bind (·.getStr?)).getD ""
private def arr (v : Value) (k : String) : Array Value := ((v.get? k).bind (·.getArr?)).getD #[]
private def obj (v : Value) (k : String) : Value := (v.get? k).getD .null

private def mkTraceNode (g : LGraphId) (nv : Value) : LayeredM (LNodeId × Array (String × LPortId)) := do
  let type : NodeType := (Elk.ElkEnum.ofJavaName? (str nv "type")).getD .normal
  let m := obj nv "margin"
  let margin : LMargin := { top := num m "top", bottom := num m "bottom", left := num m "left", right := num m "right" }
  let n ← LayeredM.createNode g { size := ⟨num nv "width", num nv "height"⟩, type, margin, position := ⟨num nv "x", num nv "y"⟩ }
  let mut ports : Array (String × LPortId) := #[]
  for pv in arr nv "ports" do
    let side : PortSide := (Elk.ElkEnum.ofJavaName? (str pv "side")).getD .undefined
    let an := obj pv "anchor"
    let lp : LPort := { side := side, position := ⟨num pv "x", num pv "y"⟩, anchor := ⟨num an "x", num an "y"⟩ }
    let p ← LayeredM.createPort { lp with size := ⟨num pv "width", num pv "height"⟩ }
    LayeredM.setPortNode p (some n)
    ports := ports.push (str pv "id", p)
  return (n, ports)

private def buildTrace (doc : Value) : LayeredM (LGraphId × Array (String × LNodeId)) := do
  -- `GraphConfigurator.configureGraphProperties`: orthogonal routing (the default) favors straight edges
  let props : PropertyMap := ({} : PropertyMap).set LayeredOptions.NODE_PLACEMENT_FAVOR_STRAIGHT_EDGES true
  let g ← LayeredM.createGraph { props, internal := { spacings := some (Spacings.new props) } }
  let mut portMap : Std.HashMap String LPortId := {}
  let mut nodes : Array (String × LNodeId) := #[]
  let mut ls : Array LayerId := #[]
  for lv in arr doc "layers" do
    let l ← LayeredM.createLayer g
    ls := ls.push l
    for nv in arr lv "nodes" do
      let (n, ps) ← mkTraceNode g nv
      LayeredM.setNodeLayer n (some l)
      nodes := nodes.push (str nv "id", n)
      for (k, p) in ps do portMap := portMap.insert k p
  LayeredM.modifyGraph g fun x => { x with layers := ls }
  for nv in arr doc "externalNodes" do
    let (_, ps) ← mkTraceNode g nv
    for (k, p) in ps do portMap := portMap.insert k p
  for ev in arr doc "edges" do
    let e ← LayeredM.createEdge
    if let some sp := portMap.get? (str ev "sourcePort") then LayeredM.setEdgeSource e (some sp)
    if let some tp := portMap.get? (str ev "targetPort") then LayeredM.setEdgeTarget e (some tp)
  return (g, nodes)

private def readJson (path : System.FilePath) : IO Value := do
  match Elk.Json.parseString (← IO.FS.readFile path) with
  | .ok v => return v
  | .error e => throw (IO.userError s!"parse {path}: {e}")

/-- Replays every BK step of one trace directory: `(step, mismatching nodes, first mismatches)`. -/
def checkDir (dir : System.FilePath) : IO (Array (String × Nat × String)) := do
  let names := ((← dir.readDir).map (·.fileName)).filter (·.endsWith ".json")
  let names := stableSort names compare
  let mut results : Array (String × Nat × String) := #[]
  for i in [1:names.size] do
    if !(names[i]!.endsWith "_BKNodePlacer.json") then continue
    let input ← readJson (dir / names[i-1]!)
    let output ← readJson (dir / names[i]!)
    let mut expected : Std.HashMap String Float := {}
    for lv in arr output "layers" do
      for nv in arr lv "nodes" do
        expected := expected.insert (str nv "id") (num nv "y")
    let (nodes, a) ← LayeredM.run (do
      let (g, nodes) ← buildTrace input
      BKNodePlacer.process g (← ProgressMonitor.basic)
      return nodes)
    let mut mismatches := 0
    let mut detail := ""
    for (k, n) in nodes do
      let y := (a.node n).position.y
      let e := expected.getD k Float.nan
      if !((y - e).abs ≤ 1e-9) then
        if mismatches < 3 then detail := detail ++ s!" {k}: lean {y} oracle {e};"
        mismatches := mismatches + 1
    results := results.push (s!"{dir.fileName.getD ""}/{names[i]!}", mismatches, detail)
  return results

end Replay

def oracleReplayTests : Suite := suite "layered.p4nodes.bk.oracleReplay" do
  let some dirs ← IO.getEnv "ELK_BK_ORACLE_TRACES"
    | IO.println "SKIP layered.p4nodes.bk.oracleReplay: ELK_BK_ORACLE_TRACES not set"
  for d in dirs.splitOn ":" do
    if d.isEmpty then continue
    -- a model trace directory, or a `--trace-dir` root holding one directory per model
    let entries ← System.FilePath.readDir d
    let modelDirs ← if entries.any (·.fileName.startsWith "step_") then pure #[(d : System.FilePath)]
      else do
        let dirs ← entries.filterM fun (e : IO.FS.DirEntry) => e.path.isDir
        pure (dirs.map (·.path))
    for dir in stableSort modelDirs (fun x y => compare x.toString y.toString) do
      for (name, mismatches, detail) in ← Replay.checkDir dir do
        report s!"{name}: y coordinates match the oracle" (mismatches == 0) s!"{mismatches} nodes differ;{detail}"

def suites : Array Tests.Suite :=
  #[neighborhoodTests, chainTests, diamondTests, straighteningTests, conflictTests, basicPlacementTests, phaseTests,
    oracleReplayTests]

end Tests.Layered.P4NodesBK
