import Tests.Framework
import Elk.Alg.Layered
import Elk.Alg.Layered.Intermediate.WrappingProcessors
/-! Tests of `org.eclipse.elk.alg.layered.intermediate.wrapping`: the elk-rs tests
`tests/intermediate/{breaking_point_processors_test,single_edge_graph_wrapper_test}.rs` (ported on
the same hand-built graphs) plus hand-derived checks of `GraphStats`, the ARD/MSD heuristics on a
known layer-width profile, both validify strategies, the wrapper's cuts, the inserter's dummies and
cut improvement, the processor's wrapping, chain merge and dummy dropping, and the remover's bend
points for each edge routing. -/
namespace Tests.Layered.IntermediateWrapping

open Tests Elk Elk.Graph Elk.Core Elk.Core.Util Elk.Core.Math Elk.Core.Alg Elk.Core.Options
open Elk.Alg.Layered Elk.Alg.Layered.Graph Elk.Alg.Layered.Options Elk.Alg.Layered.Intermediate
open Elk.Alg.Layered.Intermediate.Wrapping

/-- A hand-built layered graph. -/
structure Built where
  graph : LGraphId
  layers : Array LayerId
  nodes : Array LNodeId
  edges : Array LEdgeId
  deriving Inhabited

/-- Node `i` goes to layer `layerOf[i]` (appended in node order), size `sizes[i]` (default
`30 × 20`) and type `types[i]`; one edge (own `EAST` source / `WEST` target port) per pair. -/
def build (layerOf : Array Nat) (edges : Array (Nat × Nat)) (sizes : Array KVector := #[])
    (types : Array NodeType := #[]) : LayeredM Built := do
  let g ← LayeredM.createGraph
  let layerCount := layerOf.foldl (fun m l => max m (l + 1)) 0
  let mut layers : Array LayerId := #[]
  for _ in [0:layerCount] do
    layers := layers.push (← LayeredM.createLayer g)
  let ls := layers
  LayeredM.modifyGraph g fun x => { x with layers := ls }
  let mut ns : Array LNodeId := #[]
  for i in [0:layerOf.size] do
    let n ← LayeredM.createNode g { size := sizes.getD i ⟨30.0, 20.0⟩, type := types.getD i .normal }
    LayeredM.setNodeLayer n (some layers[layerOf[i]!]!)
    ns := ns.push n
  let mut es : Array LEdgeId := #[]
  for (s, t) in edges do
    let ps ← LayeredM.createPort
    LayeredM.modifyPort ps (·.setSide .east)
    LayeredM.setPortNode ps (some ns[s]!)
    let pt ← LayeredM.createPort
    LayeredM.modifyPort pt (·.setSide .west)
    LayeredM.setPortNode pt (some ns[t]!)
    let e ← LayeredM.createEdge
    LayeredM.setEdgeSource e (some ps)
    LayeredM.setEdgeTarget e (some pt)
    es := es.push e
  return ⟨g, layers, ns, es⟩

/-- A path `n0 → … → n(k-1)`, one node per layer. -/
def path (k : Nat) (sizes : Array KVector := #[]) : LayeredM Built :=
  build (Array.range k) ((Array.range (k - 1)).map fun i => (i, i + 1)) sizes

@[inline] def setG {α : Type} [PropCodec α] (b : Built) (p : Property α) (v : α) : LayeredM Unit :=
  LayeredM.setGraphProp b.graph p v

/-- Runs a processor with the null monitor. -/
def runP (p : LayeredProcessor) (b : Built) : LayeredM Unit := p.process b.graph ProgressMonitor.null

/-- The layers as node names: `n<i>` for built nodes, a name from `named`, else the type. -/
def layering (a : LGraphArena) (b : Built) (named : Array (LNodeId × String) := #[]) : Array (Array String) :=
  (a.graph b.graph).layers.map fun l => (a.layer l).nodes.map fun n =>
    match b.nodes.findIdx? (· == n) with
    | some i => s!"n{i}"
    | none => match named.find? (·.1 == n) with
      | some (_, s) => s
      | none => (a.node n).type.name

def countType (a : LGraphArena) (b : Built) (t : NodeType) : Nat :=
  (a.graph b.graph).layers.foldl (fun c l => c + ((a.layer l).nodes.filter fun n => (a.node n).type == t).size) 0

def infoOf (a : LGraphArena) (n : LNodeId) : Option BreakingPointInfo :=
  (a.node n).internal.breakingPointInfo

def srcNode (a : LGraphArena) (e : LEdgeId) : Option LNodeId := (a.edge e).source.bind fun p => (a.port p).owner
def tgtNode (a : LGraphArena) (e : LEdgeId) : Option LNodeId := (a.edge e).target.bind fun p => (a.port p).owner

def noEmptyLayers (a : LGraphArena) (b : Built) : Bool :=
  (a.graph b.graph).layers.all fun l => !(a.layer l).nodes.isEmpty

/-! ## BreakingPointInfo -/

def infoTests : Suite := suite "layered.wrapping.BreakingPointInfo" do
  let i : BreakingPointInfo := { BreakingPointInfo.new ⟨3⟩ ⟨4⟩ ⟨5⟩ ⟨6⟩ ⟨7⟩ with
    startInLayerDummy := some ⟨8⟩, endInLayerEdge := some ⟨0⟩, prev := some ⟨1⟩ }
  let internals : LNodeInternals := { breakingPointInfo := some i }
  check "typed field round-trips the info" (internals.breakingPointInfo == some i)
  check "unset info is none" (({} : LNodeInternals).breakingPointInfo.isNone)

/-! ## GraphStats -/

def statsTests : Suite := suite "layered.wrapping.GraphStats" do
  -- hand: widths = size.x + 20 (between-layer spacing), heights = Σ (size.y + 20)
  let ((gs, gsDown), _) ← LayeredM.run (do
    let b ← build #[0, 1, 1, 2] #[(0, 1), (0, 2), (1, 3), (2, 3)]
      (sizes := #[⟨10, 5⟩, ⟨40, 10⟩, ⟨20, 30⟩, ⟨5, 5⟩])
    let gs ← GraphStats.new b.graph
    setG b LayeredOptions.DIRECTION Direction.down
    setG b LayeredOptions.ASPECT_RATIO 2.0
    let gsDown ← GraphStats.new b.graph
    return (gs, gsDown))
  checkEq "longestPath = layer count" gs.longestPath 3
  checkEq "widths (hand: 30, max(60, 40), 25)" gs.widths #[30.0, 60.0, 25.0]
  checkEq "heights (hand: 25, 30 + 50, 25)" gs.heights #[25.0, 80.0, 25.0]
  checkFloat "maxWidth" gs.maxWidth 60.0
  checkFloat "maxHeight" gs.maxHeight 80.0
  checkFloat "sumWidth" gs.sumWidth 115.0
  checkFloat "dar (no aspect ratio: 1 * 1)" gs.dar 1.0
  checkFloat "dar for DOWN (hand: 1 / (2 * 1))" gsDown.dar 0.5
  -- layer 1 has incoming edges only from n0 but into two targets, layer 2 from two sources
  checkEq "cuts allowed (hand: never before 0; two targets; two sources)" gs.cutsAllowed #[false, false, false]
  let ((pathStats, forbiddenStats, nsHeight), _) ← LayeredM.run (do
    let b ← path 4
    let s1 ← GraphStats.new b.graph
    setG b LayeredOptions.WRAPPING_VALIDIFY_FORBIDDEN_INDICES #[(2 : Int)]
    let s2 ← GraphStats.new b.graph
    -- a NORTH_SOUTH_PORT dummy feeding a node adds its origin's height (with margins)
    let c ← build #[0, 1] #[(0, 1)] (sizes := #[⟨1, 1⟩, ⟨1, 3⟩]) (types := #[.northSouthPort, .normal])
    let origin ← LayeredM.createNode c.graph { size := ⟨1, 7⟩, margin := { top := 1.0, bottom := 2.0 } }
    LayeredM.modifyNode c.nodes[0]! fun n => { n with internal := { n.internal with origin := some (.lNode origin) } }
    let h ← GraphStats.determineLayerHeight c.layers[1]! 20.0
    return (s1, s2, h))
  checkEq "path: every cut except 0 allowed" pathStats.cutsAllowed #[false, true, true, true]
  checkEq "forbidden indices given: all false (Java/Rust only write false)" forbiddenStats.cutsAllowed #[false, false, false, false]
  check "isCutAllowed out of range / negative is false" (!pathStats.isCutAllowed 4 && !pathStats.isCutAllowed (-1))
  checkFloat "layer height with north/south origin (hand: 3 + 20 + 7 + 2 + 1)" nsHeight 33.0

/-! ## Cut index heuristics -/

/-- The MSD profile: node widths `[100, 10, 10, 10, 10, 100]` → layer widths `[120, 30, 30, 30, 30,
120]` (total 360), heights all `40`. -/
def msdProfile : LayeredM Built :=
  path 6 (sizes := #[⟨100, 20⟩, ⟨10, 20⟩, ⟨10, 20⟩, ⟨10, 20⟩, ⟨10, 20⟩, ⟨100, 20⟩])

def heuristicTests : Suite := suite "layered.wrapping.cutIndexHeuristics" do
  let ((ard9, ard6, msd6, msd6f0, msd9, zero, manual, manualUnset), _) ← LayeredM.run (do
    let p9 ← path 9
    let gs9 ← GraphStats.new p9.graph
    let msd9 ← MSDCutIndexHeuristic.calculator.getCutIndexes p9.graph gs9
    let p6 ← msdProfile
    let gs6 ← GraphStats.new p6.graph
    let msd6 ← MSDCutIndexHeuristic.calculator.getCutIndexes p6.graph gs6
    setG p6 LayeredOptions.WRAPPING_CUTTING_MSD_FREEDOM (0 : Int)
    let msd6f0 ← MSDCutIndexHeuristic.calculator.getCutIndexes p6.graph gs6
    let flat ← path 3 (sizes := #[⟨10, 0⟩, ⟨10, 0⟩, ⟨10, 0⟩])
    setG flat LayeredOptions.SPACING_NODE_NODE 0.0
    let gsFlat ← GraphStats.new flat.graph
    let manualUnset ← ICutIndexCalculator.manual.getCutIndexes flat.graph gsFlat
    setG flat LayeredOptions.WRAPPING_CUTTING_CUTS #[(1 : Int), (7 : Int)]
    let manual ← ICutIndexCalculator.manual.getCutIndexes flat.graph gsFlat
    return (ARDCutIndexHeuristic.cutIndexes gs9, ARDCutIndexHeuristic.cutIndexes gs6, msd6, msd6f0, msd9,
      ARDCutIndexHeuristic.getChunkCount gsFlat, manual, manualUnset))
  -- hand: path 9 → widths 50 (sum 450), heights 40 → rows = round(sqrt(450 / 40)) = 3, step 3
  checkEq "ARD path 9: cuts [3, 6]" ard9 #[3, 6]
  -- hand: 360 / 40 = 9 → 3 rows, step 2
  checkEq "ARD profile: cuts [2, 4]" ard6 #[2, 4]
  -- hand: m = 1 → [3] (scale 1/180); m = 2 → [1, 5] (scale 1/120); m = 3 → [1, 4] (tie, kept m = 2)
  checkEq "MSD profile: cuts [1, 5]" msd6 #[1, 5]
  checkEq "MSD profile, freedom 0: only m = 2" msd6f0 #[1, 5]
  -- hand: m = 2 → [3, 6] (scale 1/150) beats m = 1 → [5] (1/250); m = 3 gives [3, 6] again
  checkEq "MSD path 9: cuts [3, 6]" msd9 #[3, 6]
  checkEq "ARD chunk count with zero height (Rust: longestPath)" zero 3
  checkEq "manual cuts read from WRAPPING_CUTTING_CUTS" manual #[1, 7]
  checkEq "manual cuts unset: empty" manualUnset #[]
  check "no heuristic guarantees valid cuts"
    (!ICutIndexCalculator.manual.guaranteeValid && !ARDCutIndexHeuristic.calculator.guaranteeValid
      && !MSDCutIndexHeuristic.calculator.guaranteeValid)

/-! ## Validify strategies -/

def validifyTests : Suite := suite "layered.wrapping.validify" do
  let ((pathStats, forbidStats), _) ← LayeredM.run (do
    let b ← path 5
    let s1 ← GraphStats.new b.graph
    -- path of 5 plus n0 → n2: layer 2 has incoming edges from two sources (cut before 2 forbidden)
    let c ← build #[0, 1, 2, 3, 4] #[(0, 1), (1, 2), (0, 2), (2, 3), (3, 4)]
    let s2 ← GraphStats.new c.graph
    return (s1, s2))
  -- validify_indexes_greedily_keeps_valid_cuts_for_simple_path
  checkEq "validify_indexes_greedily_keeps_valid_cuts_for_simple_path"
    (SingleEdgeGraphWrapper.validifyIndexesGreedily pathStats #[1, 3]) #[1, 3]
  checkEq "forbidden layout: cuts allowed (hand)" forbidStats.cutsAllowed #[false, true, false, true, true]
  -- hand: 2 → 3 (offset 1), then 3 + 1 = 4
  checkEq "greedy shifts a forbidden cut and its successors" (SingleEdgeGraphWrapper.validifyIndexesGreedily forbidStats #[2, 3]) #[3, 4]
  checkEq "greedy drops cuts beyond the last layer" (SingleEdgeGraphWrapper.validifyIndexesGreedily forbidStats #[4, 5]) #[4]
  -- hand: valid [-inf, 1, 3, 4, +inf]; 2 is equally far from 1 and 3 → lower
  checkEq "look back: tie selects the lower valid cut" (SingleEdgeGraphWrapper.validifyIndexesLookingBack forbidStats #[2]) #[1]
  -- hand: 2 → 1 (offset -1); 3 - 1 = 2 → next valid 3 (distLower 2 - 3 < distHigher)
  checkEq "look back: offsets carry over" (SingleEdgeGraphWrapper.validifyIndexesLookingBack forbidStats #[2, 3]) #[1, 3]
  checkEq "look back: no desired cuts" (SingleEdgeGraphWrapper.validifyIndexesLookingBack forbidStats #[]) #[]
  checkEq "look back with valids: far below +inf selects the lower cut"
    (SingleEdgeGraphWrapper.validifyIndexesLookingBackWithValids #[5] #[SingleEdgeGraphWrapper.I32_MIN, 2, SingleEdgeGraphWrapper.I32_MAX]) #[2]
  checkEq "look back with valids: saturating distance to -inf selects the higher cut"
    (SingleEdgeGraphWrapper.validifyIndexesLookingBackWithValids #[3] #[SingleEdgeGraphWrapper.I32_MIN, 10, SingleEdgeGraphWrapper.I32_MAX]) #[10]
  checkEq "saturating_sub(3, i32::MIN) = i32::MAX" (SingleEdgeGraphWrapper.saturatingSubI32 3 SingleEdgeGraphWrapper.I32_MIN) 2147483647
  let ((onlyFirst), _) ← LayeredM.run (do
    let b ← build #[0, 1, 1] #[(0, 1), (0, 2)]
    let s ← GraphStats.new b.graph
    return SingleEdgeGraphWrapper.validifyIndexesLookingBack s #[1])
  checkEq "look back: no allowed cut at all → empty" onlyFirst #[]

/-! ## SingleEdgeGraphWrapper -/

def wrapperTests : Suite := suite "layered.wrapping.SingleEdgeGraphWrapper" do
  -- manual_cut_process_marks_graph_as_cyclic
  let ((b, extras), a) ← LayeredM.run (do
    let b ← path 5
    setG b LayeredOptions.WRAPPING_CUTTING_STRATEGY CuttingStrategy.manual
    setG b LayeredOptions.WRAPPING_CUTTING_CUTS #[(2 : Int)]
    setG b LayeredOptions.WRAPPING_VALIDIFY_STRATEGY ValidifyStrategy.no
    let e12 := b.edges[1]!
    let oldSource := (← LayeredM.getEdge e12).source
    let oldTarget := (← LayeredM.getEdge e12).target
    runP SingleEdgeGraphWrapper.processor b
    return (b, (oldSource, oldTarget)))
  check "manual_cut_process_marks_graph_as_cyclic" (a.graph b.graph).internal.cyclic
  -- hand: L2 → L0 (incoming edge reversed, dummies in L0 at size - 1 and appended to L1), L3 → L1, L4 → L2
  checkEq "manual cut [2]: layering" (layering a b)
    #[#["n0", "LONG_EDGE", "n2"], #["n1", "LONG_EDGE", "n3"], #["n4"]]
  let e12 := b.edges[1]!
  check "cut edge reversed" (a.edge e12).internal.reversed
  checkEq "reversed edge leaves n2 from its former target port" (a.edge e12).source extras.2
  let d0 := (a.layer (a.graph b.graph).layers[0]!).nodes[1]!
  let d1 := (a.layer (a.graph b.graph).layers[1]!).nodes[1]!
  checkEq "reversed edge enters the in-layer dummy of L0" (tgtNode a e12) (some d0)
  checkEq "first dummy: LONG_EDGE_SOURCE = reversed source port" (a.node d0).internal.longEdgeSource extras.2
  checkEq "first dummy: LONG_EDGE_TARGET = old source port of n1" (a.node d0).internal.longEdgeTarget extras.1
  checkEq "second dummy copies the long edge ports" (a.node d1).internal.longEdgeSource extras.2
  let lastEdge := (a.node d1).ports.filterMap (fun p => (a.port p).outgoingEdges[0]?) |>.getD 0 default
  checkEq "chain ends at n1's port" (a.edge lastEdge).target extras.1
  checkFloat "dummy individual edge-node spacing (hand: 10 + 10)"
    ((((a.node d0).props.get LayeredOptions.SPACING_INDIVIDUAL).getD {}).props.getD LayeredOptions.SPACING_EDGE_NODE 0.0) 20.0
  checkFloat "dummy height = edge thickness 1" (a.node d0).size.y 1.0
  checkEq "dummy ports: WEST/EAST" ((a.node d0).ports.map fun p => (a.port p).side) #[PortSide.west, PortSide.east]
  -- early exit: dar (10) > currentAR (= longestPath 5)
  let (b2, a2) ← LayeredM.run (do
    let b ← path 5
    setG b LayeredOptions.ASPECT_RATIO 10.0
    runP SingleEdgeGraphWrapper.processor b
    return b)
  checkEq "dar above current aspect ratio: untouched" (a2.graph b2.graph).layers.size 5
  check "untouched graph not cyclic" (!(a2.graph b2.graph).internal.cyclic)
  -- ARD on path 9: cuts [3, 6] (greedy validify keeps them) → 3 rows of 3
  let (b3, a3) ← LayeredM.run (do
    let b ← path 9
    setG b LayeredOptions.WRAPPING_CUTTING_STRATEGY CuttingStrategy.ard
    runP SingleEdgeGraphWrapper.processor b
    return b)
  checkEq "ARD path 9: layering (hand)" (layering a3 b3)
    #[#["n0", "LONG_EDGE", "n3", "LONG_EDGE", "n6"], #["n1", "LONG_EDGE", "n4", "LONG_EDGE", "n7"],
      #["n2", "LONG_EDGE", "n5", "LONG_EDGE", "n8"]]
  check "ARD path 9: cyclic" (a3.graph b3.graph).internal.cyclic
  -- MSD (default) on the profile: cuts [1, 5]
  let (b4, a4) ← LayeredM.run (do
    let b ← msdProfile
    runP SingleEdgeGraphWrapper.processor b
    return b)
  checkEq "MSD profile: layering (hand: rows [n0], [n1..n4], [n5], wrapped edges get dummies)" (layering a4 b4)
    #[#["n0", "LONG_EDGE", "n1", "LONG_EDGE", "n5"], #["n2", "LONG_EDGE"], #["n3", "LONG_EDGE"], #["n4", "LONG_EDGE"]]

/-! ## BreakingPointInserter -/

/-- `setup_multi_edge_graph`: four layers, an edge from layer 0 to layer 3, manual cut `[1]`,
validify `NO`. -/
def multiEdgeGraph : LayeredM Built := do
  let b ← build #[0, 1, 2, 3] #[(0, 3)]
  setG b LayeredOptions.WRAPPING_CUTTING_STRATEGY CuttingStrategy.manual
  setG b LayeredOptions.WRAPPING_CUTTING_CUTS #[(1 : Int)]
  setG b LayeredOptions.WRAPPING_VALIDIFY_STRATEGY ValidifyStrategy.no
  return b

def inserterTests : Suite := suite "layered.wrapping.BreakingPointInserter" do
  let ((b, oldSource), a) ← LayeredM.run (do
    let b ← multiEdgeGraph
    let s := (← LayeredM.getEdge b.edges[0]!).source
    LayeredM.modifyEdge b.edges[0]! fun e => { e with internal := { e.internal with modelOrder := some 7 } }
    runP BreakingPointInserter.processor b
    return (b, s))
  let e := b.edges[0]!
  checkEq "breaking_point_inserter_splits_edge_and_creates_breaking_points: 6 layers" (a.graph b.graph).layers.size 6
  checkEq "breaking_point_inserter_splits_edge_and_creates_breaking_points: 2 breaking points" (countType a b .breakingPoint) 2
  let some t := srcNode a e | check "edge has a source" false
  checkEq "breaking_point_inserter_splits_edge_and_creates_breaking_points: source is a breaking point" (a.node t).type .breakingPoint
  let infoCount := (a.graph b.graph).layers.foldl (fun c l => c + ((a.layer l).nodes.filter fun n => (infoOf a n).isSome).size) 0
  checkEq "breaking_point_inserter_splits_edge_and_creates_breaking_points: 2 infos" infoCount 2
  checkEq "layering (hand: L0, start, end, L1, L2, L3)" (layering a b)
    #[#["n0"], #["BREAKING_POINT"], #["BREAKING_POINT"], #["n1"], #["n2"], #["n3"]]
  let some info := infoOf a t | check "end marker has info" false
  check "the edge source is the end marker" (info.endNode == t)
  let s := (a.layer (a.graph b.graph).layers[1]!).nodes[0]!
  checkEq "start marker in layer 1" info.start s
  check "same info on both markers" (infoOf a s == some info)
  checkEq "nodeStartEdge from the original source port" (a.edge info.nodeStartEdge).source oldSource
  checkEq "nodeStartEdge into the start marker" (tgtNode a info.nodeStartEdge) (some s)
  checkEq "startEndEdge start → end" (srcNode a info.startEndEdge, tgtNode a info.startEndEdge) (some s, some t)
  checkEq "original edge recorded" info.originalEdge e
  checkEq "MODEL_ORDER copied to the dummy edges"
    ((a.edge info.nodeStartEdge).internal.modelOrder, (a.edge info.startEndEdge).internal.modelOrder) (some 7, some 7)
  checkEq "marker ports WEST/EAST" ((a.node s).ports.map fun p => (a.port p).side) #[PortSide.west, PortSide.east]
  check "markers FIXED_SIDE" ((a.node s).props.get LayeredOptions.PORT_CONSTRAINTS == some PortConstraints.fixedSide)
  check "no chain" (info.prev.isNone && info.next.isNone)
  -- edge spans and cut improvement on n0→n4, n0→n1, n1→n2, n1→n3, n2→n3, n3→n4
  let ((spans, imp2, imp3, imp23, impEmpty), _) ← LayeredM.run (do
    let c ← build #[0, 1, 2, 3, 4] #[(0, 4), (0, 1), (1, 2), (1, 3), (2, 3), (3, 4)]
    let spans ← BreakingPointInserter.computeEdgeSpans c.graph
    let i2 ← BreakingPointInserter.improveCuts c.graph #[2]
    let i3 ← BreakingPointInserter.improveCuts c.graph #[3]
    let i23 ← BreakingPointInserter.improveCuts c.graph #[2, 3]
    let ie ← BreakingPointInserter.improveCuts c.graph #[]
    return (spans, i2, i3, i23, ie))
  checkEq "edge spans (hand)" spans #[0, 2, 3, 3, 2, 0]
  -- hand: score(1) = 2 + 1² = 3 is minimal (ties keep the first)
  checkEq "improveCuts [2] → [1]" imp2 #[1]
  checkEq "improveCuts [3] → [3] (score 3 at 3, tie at 4 not taken)" imp3 #[3]
  -- hand: round 1 moves cut 0 to 1 and offsets cut 1 to 2; round 2 moves it to 1 as well
  checkEq "improveCuts [2, 3] → [1, 1]" imp23 #[1, 1]
  checkEq "improveCuts [] → []" impEmpty #[]
  -- Rust apply_cuts visits the inserted layers: cuts [2, 4] on a path split edge n1→n2 twice
  let ((c, chainEdge), ca) ← LayeredM.run (do
    let c ← path 6
    setG c LayeredOptions.WRAPPING_CUTTING_STRATEGY CuttingStrategy.manual
    setG c LayeredOptions.WRAPPING_CUTTING_CUTS #[(2 : Int), (4 : Int)]
    setG c LayeredOptions.WRAPPING_MULTI_EDGE_IMPROVE_CUTS false
    runP BreakingPointInserter.processor c
    return (c, c.edges[1]!))
  checkEq "cuts [2, 4] (Rust): layering" (layering ca c)
    #[#["n0"], #["n1"], #["BREAKING_POINT"], #["BREAKING_POINT"], #["BREAKING_POINT"], #["BREAKING_POINT"],
      #["n2"], #["n3"], #["n4"], #["n5"]]
  let some t2 := srcNode ca chainEdge | check "chained edge source" false
  let some info2 := infoOf ca t2 | check "second info" false
  let some prevStart := info2.prev | check "second info has prev" false
  let some info1 := infoOf ca prevStart | check "first info" false
  check "chain: first.next = second.start" (info1.next == some info2.start)
  checkEq "chain: second nodeStartEdge leaves the first end marker" (srcNode ca info2.nodeStartEdge) (some info1.endNode)
  checkEq "edge n3→n4 not split (Rust)" (srcNode ca c.edges[3]!) (some c.nodes[3]!)

/-! ## BreakingPointProcessor -/

def processorTests : Suite := suite "layered.wrapping.BreakingPointProcessor" do
  -- breaking_point_processor_wraps_layers_and_marks_graph_cyclic
  let (b, a) ← LayeredM.run (do
    let b ← multiEdgeGraph
    setG b LayeredOptions.WRAPPING_MULTI_EDGE_IMPROVE_WRAPPED_EDGES false
    runP BreakingPointInserter.processor b
    runP BreakingPointProcessor.processor b
    return b)
  check "breaking_point_processor_wraps_layers_and_marks_graph_cyclic: cyclic" (a.graph b.graph).internal.cyclic
  check "breaking_point_processor_wraps_layers_and_marks_graph_cyclic: long edge dummies" (countType a b .longEdge > 0)
  check "breaking_point_processor_wraps_layers_and_marks_graph_cyclic: no empty layer" (noEmptyLayers a b)
  let some t := srcNode a b.edges[0]! | check "edge source" false
  let some info := infoOf a t | check "info" false
  let names := #[(info.start, "s"), (t, "t")] ++
    (match info.startInLayerDummy with | some d => #[(d, "sIL")] | none => #[]) ++
    (match info.endInLayerDummy with | some d => #[(d, "eIL")] | none => #[])
  -- hand: [E: eIL t], [L0: n0 d1], [B1: s sIL], [B2: n3] after moving L1/L2/L3 into L0/B1/B2
  checkEq "wrapped layering (hand)" (layering a b names)
    #[#["eIL", "t"], #["n0", "LONG_EDGE", "n1"], #["s", "sIL", "n2"], #["n3"]]
  checkEq "endInLayerEdge = reversed startEndEdge" info.endInLayerEdge (some info.startEndEdge)
  check "startEndEdge reversed" (a.edge info.startEndEdge).internal.reversed
  checkEq "reversed startEndEdge: end → end in-layer dummy" (srcNode a info.startEndEdge, tgtNode a info.startEndEdge)
    (some t, info.endInLayerDummy)
  checkEq "startInLayerEdge: start in-layer dummy → start" (info.startInLayerEdge.bind (srcNode a ·), info.startInLayerEdge.bind (tgtNode a ·))
    (info.startInLayerDummy, some info.start)
  check "info identical on both markers after wrapping" (infoOf a info.start == some info)
  checkEq "3 long edge dummies (hand)" (countType a b .longEdge) 3
  -- dropping parallel long edge dummies: n0 → a1 → a2 → n3 with LONG_EDGE a1, a2, cut [2]
  let (c, ca) ← LayeredM.run (do
    let c ← build #[0, 1, 2, 3] #[(0, 1), (1, 2), (2, 3)] (types := #[.normal, .longEdge, .longEdge, .normal])
    setG c LayeredOptions.WRAPPING_CUTTING_STRATEGY CuttingStrategy.manual
    setG c LayeredOptions.WRAPPING_CUTTING_CUTS #[(2 : Int)]
    setG c LayeredOptions.WRAPPING_MULTI_EDGE_IMPROVE_CUTS false
    runP BreakingPointInserter.processor c
    runP BreakingPointProcessor.processor c
    return c)
  let some ct := srcNode ca c.edges[1]! | check "drop: edge source" false
  let some ci := infoOf ca ct | check "drop: info" false
  let cnames := #[(ci.start, "s"), (ct, "t")] ++
    (match ci.startInLayerDummy with | some d => #[(d, "sIL")] | none => #[]) ++
    (match ci.endInLayerDummy with | some d => #[(d, "eIL")] | none => #[])
  -- hand: forwards drops (a2, d1) and moves eIL, t into L0; backwards drops (a1, d2) and moves s,
  -- sIL into L1; the emptied first and last layers are not removed (Rust)
  checkEq "drop dummies: layering (hand)" (layering ca c cnames)
    #[#[], #["n0", "eIL", "t"], #["s", "sIL", "n3"], #[]]
  checkEq "drop dummies: n0's edge now enters s (a1 joined)" (tgtNode ca c.edges[0]!) (some ci.start)
  checkEq "drop dummies: original edge t → n3 (a2 joined)" (tgtNode ca c.edges[1]!) (some c.nodes[3]!)
  checkEq "drop dummies: a1, a2 removed" ((ca.node c.nodes[1]!).layer, (ca.node c.nodes[2]!).layer) (none, none)
  checkEq "drop dummies: in-layer ids (hand: eIL 1, t 2, s 0, sIL 1)"
    (#[ci.endInLayerDummy.map fun n => (ca.node n).id, some (ca.node ct).id, some (ca.node ci.start).id,
       ci.startInLayerDummy.map fun n => (ca.node n).id]) #[some 1, some 2, some 0, some 1]
  -- chain merge: edge n0 → n5 split at cuts [2, 5] (Rust indexes) into two chained breaking points
  let (m, ma) ← LayeredM.run (do
    let m ← build #[0, 1, 2, 3, 4, 5] #[(0, 5)]
    setG m LayeredOptions.WRAPPING_CUTTING_STRATEGY CuttingStrategy.manual
    setG m LayeredOptions.WRAPPING_CUTTING_CUTS #[(2 : Int), (5 : Int)]
    setG m LayeredOptions.WRAPPING_MULTI_EDGE_IMPROVE_CUTS false
    runP BreakingPointInserter.processor m
    runP BreakingPointProcessor.processor m
    return m)
  let some mt := srcNode ma m.edges[0]! | check "merge: edge source" false
  let some mi := infoOf ma mt | check "merge: info" false
  check "merge: no chain left" (mi.prev.isNone && mi.next.isNone)
  check "merge: same info on start and end" (infoOf ma mi.start == some mi)
  checkEq "merge: start marker shares the layer of n5 (hand: B1 = [s1, sIL, n5])"
    ((ma.node mi.start).layer) ((ma.node m.nodes[5]!).layer)
  checkEq "merge: nodeStartEdge from n0" (srcNode ma mi.nodeStartEdge) (some m.nodes[0]!)
  checkEq "merge: startEndEdge (second) enters the first end in-layer dummy" (tgtNode ma mi.startEndEdge) mi.endInLayerDummy
  checkEq "merge: endInLayerEdge = second startEndEdge" mi.endInLayerEdge (some mi.startEndEdge)
  checkEq "merge: 2 breaking points left in layers" (countType ma m .breakingPoint) 2
  -- hand: [Em: a0 t2], [L0: n0 a1 n2 b1 n3], [L1: n1 a2 n4], [B1: s1 a3 n5]
  checkEq "merge: layer sizes (hand)" ((ma.graph m.graph).layers.map fun l => (ma.layer l).nodes.size) #[2, 5, 3, 3]

/-! ## BreakingPointRemover -/

/-- Inserter + processor on the multi edge graph with the given routing and bend points on the
nodeStartEdge, startEndEdge and original edge. -/
def removerRun (routing : EdgeRouting) : IO (Built × BreakingPointInfo × LGraphArena) := do
  let ((b, info), a) ← LayeredM.run (do
    let b ← multiEdgeGraph
    setG b LayeredOptions.EDGE_ROUTING routing
    runP BreakingPointInserter.processor b
    runP BreakingPointProcessor.processor b
    let some t ← (do match (← LayeredM.getEdge b.edges[0]!).source with
        | some p => pure (← LayeredM.getPort p).owner
        | none => pure none) | throw (IO.userError "no source")
    let some info ← BreakingPointInfo.get? t | throw (IO.userError "no info")
    LayeredM.modifyEdge info.nodeStartEdge fun e => { e with
      bendPoints := #[⟨1, 1⟩]
      props := e.props.set LayeredOptions.JUNCTION_POINTS #[⟨5, 5⟩] }
    LayeredM.modifyEdge info.startEndEdge fun e => { e with
      bendPoints := #[⟨2, 2⟩, ⟨3, 3⟩]
      props := e.props.set LayeredOptions.JUNCTION_POINTS #[⟨6, 6⟩] }
    LayeredM.modifyEdge info.originalEdge fun e => { e with
      bendPoints := #[⟨9, 9⟩]
      props := e.props.set LayeredOptions.JUNCTION_POINTS #[⟨7, 7⟩] }
    LayeredM.modifyEdge info.originalEdge fun e => { e with internal := { e.internal with splineEdgeChain := #[⟨100⟩] } }
    LayeredM.modifyEdge info.nodeStartEdge fun e => { e with internal := { e.internal with splineEdgeChain := #[⟨101⟩] } }
    LayeredM.modifyEdge info.startEndEdge fun e => { e with internal := { e.internal with splineEdgeChain := #[⟨102⟩, ⟨103⟩] } }
    LayeredM.modifyNode info.start fun n => { n with position := ⟨10, 0⟩ }
    LayeredM.modifyNode info.endNode fun n => { n with position := ⟨20, 0⟩ }
    runP BreakingPointRemover.processor b
    return (b, info))
  return (b, info, a)

def removerTests : Suite := suite "layered.wrapping.BreakingPointRemover" do
  -- breaking_point_remover_restores_original_edge_and_removes_dummies
  let (b, a) ← LayeredM.run (do
    let b ← multiEdgeGraph
    setG b LayeredOptions.EDGE_ROUTING EdgeRouting.polyline
    runP BreakingPointInserter.processor b
    runP BreakingPointRemover.processor b
    return b)
  checkEq "breaking_point_remover_restores_original_edge_and_removes_dummies: no breaking points" (countType a b .breakingPoint) 0
  checkEq "breaking_point_remover_restores_original_edge_and_removes_dummies: source restored" (srcNode a b.edges[0]!) (some b.nodes[0]!)
  -- polyline: nodeStart bends, start position, reversed startEnd bends, end position, original bends
  let (pb, pinfo, pa) ← removerRun .polyline
  checkEq "polyline bend points (hand)" (pa.edge pb.edges[0]!).bendPoints
    #[⟨1, 1⟩, ⟨10, 0⟩, ⟨3, 3⟩, ⟨2, 2⟩, ⟨20, 0⟩, ⟨9, 9⟩]
  checkEq "junction points: original, startEnd, nodeStart" ((pa.edge pb.edges[0]!).props.get LayeredOptions.JUNCTION_POINTS)
    (some #[⟨7, 7⟩, ⟨6, 6⟩, ⟨5, 5⟩])
  checkEq "dummy edges disconnected" ((pa.edge pinfo.nodeStartEdge).source, (pa.edge pinfo.startEndEdge).target) (none, none)
  checkEq "markers removed" ((pa.node pinfo.start).layer, (pa.node pinfo.endNode).layer) (none, none)
  checkEq "original edge from n0 to n3" (srcNode pa pb.edges[0]!, tgtNode pa pb.edges[0]!) (some pb.nodes[0]!, some pb.nodes[3]!)
  let (ob, _, oa) ← removerRun .orthogonal
  checkEq "orthogonal bend points (hand: without marker positions)" (oa.edge ob.edges[0]!).bendPoints
    #[⟨1, 1⟩, ⟨3, 3⟩, ⟨2, 2⟩, ⟨9, 9⟩]
  let (ub, _, ua) ← removerRun .undefined
  checkEq "undefined routing behaves like orthogonal" (ua.edge ub.edges[0]!).bendPoints
    #[⟨1, 1⟩, ⟨3, 3⟩, ⟨2, 2⟩, ⟨9, 9⟩]
  let (sb, sinfo, sa) ← removerRun .splines
  checkEq "splines: bend points untouched (Rust)" (sa.edge sb.edges[0]!).bendPoints #[⟨9, 9⟩]
  checkEq "splines: joined edge chain e1 ++ reverse(e2) ++ e3" (sa.edge sb.edges[0]!).internal.splineEdgeChain
    #[⟨101⟩, ⟨103⟩, ⟨102⟩, ⟨100⟩]
  checkEq "splines: surviving edge" (sa.edge sb.edges[0]!).internal.splineSurvivingEdge (some sb.edges[0]!)
  checkEq "splines: dummy chains cleared"
    ((sa.edge sinfo.nodeStartEdge).internal.splineEdgeChain.size, (sa.edge sinfo.startEndEdge).internal.splineEdgeChain.size) (0, 0)
  -- a chain of two breaking points (cuts [2, 5], no merge) is removed from its last end marker
  let ((m, edgesInfo), ma) ← LayeredM.run (do
    let m ← build #[0, 1, 2, 3, 4, 5] #[(0, 5)]
    setG m LayeredOptions.WRAPPING_CUTTING_STRATEGY CuttingStrategy.manual
    setG m LayeredOptions.WRAPPING_CUTTING_CUTS #[(2 : Int), (5 : Int)]
    setG m LayeredOptions.WRAPPING_MULTI_EDGE_IMPROVE_CUTS false
    setG m LayeredOptions.WRAPPING_MULTI_EDGE_IMPROVE_WRAPPED_EDGES false
    runP BreakingPointInserter.processor m
    runP BreakingPointProcessor.processor m
    let some t2 ← (do match (← LayeredM.getEdge m.edges[0]!).source with
        | some p => pure (← LayeredM.getPort p).owner
        | none => pure none) | throw (IO.userError "no source")
    let some i2 ← BreakingPointInfo.get? t2 | throw (IO.userError "no info")
    let some p := i2.prev | throw (IO.userError "no prev")
    let some i1 ← BreakingPointInfo.get? p | throw (IO.userError "no info 1")
    LayeredM.modifyEdge i1.nodeStartEdge fun e => { e with bendPoints := #[⟨1, 0⟩] }
    LayeredM.modifyEdge i1.startEndEdge fun e => { e with bendPoints := #[⟨2, 0⟩] }
    LayeredM.modifyEdge i2.nodeStartEdge fun e => { e with bendPoints := #[⟨3, 0⟩] }
    LayeredM.modifyEdge i2.startEndEdge fun e => { e with bendPoints := #[⟨4, 0⟩] }
    LayeredM.modifyEdge m.edges[0]! fun e => { e with bendPoints := #[⟨5, 0⟩] }
    runP BreakingPointRemover.processor m
    return (m, (i1, i2)))
  checkEq "chain: all breaking points removed" (countType ma m .breakingPoint) 0
  checkEq "chain: original edge n0 → n5" (srcNode ma m.edges[0]!, tgtNode ma m.edges[0]!) (some m.nodes[0]!, some m.nodes[5]!)
  -- hand: remove(second) then remove(first) prepends nodeStart1, reversed startEnd1
  checkEq "chain: bend points (hand)" (ma.edge m.edges[0]!).bendPoints #[⟨1, 0⟩, ⟨2, 0⟩, ⟨3, 0⟩, ⟨4, 0⟩, ⟨5, 0⟩]
  checkEq "chain: second nodeStartEdge disconnected" (ma.edge edgesInfo.2.nodeStartEdge).source none

/-! ## Registration -/

def registrationTests : Suite := suite "layered.wrapping.registration" do
  for (s, n) in #[(IntermediateProcessorStrategy.breakingPointInserter, "BreakingPointInserter"),
      (.breakingPointProcessor, "BreakingPointProcessor"), (.breakingPointRemover, "BreakingPointRemover"),
      (.singleEdgeGraphWrapper, "SingleEdgeGraphWrapper")] do
    check s!"{n} registered" (← IntermediateProcessorStrategy.isAvailable s)
    checkEq s!"{n} name" (← IntermediateProcessorStrategy.create s).name n

def suites : Array Tests.Suite :=
  #[infoTests, statsTests, heuristicTests, validifyTests, wrapperTests, inserterTests, processorTests,
    removerTests, registrationTests]

end Tests.Layered.IntermediateWrapping
