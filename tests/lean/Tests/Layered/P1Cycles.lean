import Tests.Framework
import Elk.Alg.Layered
import Elk.Alg.Layered.P1Cycles
/-!
Tests of `org.eclipse.elk.alg.layered.p1cycles`. The elk-rs tests (`p1_cycles/basic_cycle_breaker_test.rs`)
drive the breakers through the ElkGraph importer; here the same graphs are built directly as layerless
`LGraph`s and the Rust assertion (no cycle remains, for every strategy) is checked, plus hand-derived
expectations of which edges each breaker reverses.
-/
namespace Tests.Layered.P1Cycles

open Tests Elk.Graph Elk.Core.Util Elk.Core.Alg Elk.Alg.Layered Elk.Alg.Layered.Graph Elk.Alg.Layered.Options
  Elk.Alg.Layered.P1Cycles Elk.Alg.Layered.Intermediate
open Elk (ElkEnum)

/-- Creates a graph with `n` layerless nodes (node `i` gets `MODEL_ORDER = i` when `modelOrder`). -/
def mkGraph (n : Nat) (modelOrder : Bool := false) : LayeredM (LGraphId × Array LNodeId) := do
  let g ← LayeredM.createGraph
  let mut ns : Array LNodeId := #[]
  for i in [0:n] do
    let node ← LayeredM.createNode g { size := ⟨30, 30⟩ }
    if modelOrder then
      LayeredM.modifyNode node fun x => { x with internal := { x.internal with modelOrder := some (i : Int) } }
    ns := ns.push node
  LayeredM.modifyGraph g fun x => { x with layerlessNodes := ns }
  return (g, ns)

/-- An edge between fresh ports of `s` and `t` (like the importer does for simple edges). -/
def mkEdge (s t : LNodeId) : LayeredM LEdgeId := do
  let ps ← LayeredM.createPort
  let pt ← LayeredM.createPort
  LayeredM.setPortNode ps (some s)
  LayeredM.setPortNode pt (some t)
  let e ← LayeredM.createEdge
  LayeredM.setEdgeSource e (some ps)
  LayeredM.setEdgeTarget e (some pt)
  return e

/-- Sets `MODEL_ORDER` of a node. -/
def setModelOrder (n : LNodeId) (mo : Int) : LayeredM Unit :=
  LayeredM.modifyNode n fun x => { x with internal := { x.internal with modelOrder := some mo } }

/-- Runs a phase on a graph with a null monitor. -/
def runPhase (phase : LayeredPhase) (g : LGraphId) : LayeredM Unit := phase.process g ProgressMonitor.null

/-- `build_cyclic_graph`: A→B→C→A. -/
def cyclic (modelOrder : Bool := false) : LayeredM (LGraphId × Array LNodeId × Array LEdgeId) := do
  let (g, ns) ← mkGraph 3 modelOrder
  let e0 ← mkEdge ns[0]! ns[1]!
  let e1 ← mkEdge ns[1]! ns[2]!
  let e2 ← mkEdge ns[2]! ns[0]!
  return (g, ns, #[e0, e1, e2])

/-- `build_dense_cyclic_graph`: A→B→C→D→E→A plus A→C, B→D, C→E. -/
def dense (modelOrder : Bool := false) : LayeredM (LGraphId × Array LNodeId × Array LEdgeId) := do
  let (g, ns) ← mkGraph 5 modelOrder
  let mut es := #[]
  for (s, t) in #[(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 2), (1, 3), (2, 4)] do
    es := es.push (← mkEdge ns[s]! ns[t]!)
  return (g, ns, es)

/-- The Rust `assert_acyclic` DFS (Unvisited/Visiting/Visited over node-level outgoing edges);
self loops are ignored. -/
partial def hasCycle (a : LGraphArena) (g : LGraphId) : Bool := Id.run do
  let nodes := (a.graph g).layerlessNodes
  let mut state : Std.HashMap LNodeId Nat := {}
  let mut found := false
  for n in nodes do
    if state.getD n 0 == 0 then
      let (st, f) := visit a n state
      state := st
      if f then found := true
  return found
where
  visit (a : LGraphArena) (n : LNodeId) (state : Std.HashMap LNodeId Nat) : Std.HashMap LNodeId Nat × Bool := Id.run do
    match state.getD n 0 with
    | 1 => return (state, true)
    | 2 => return (state, false)
    | _ => pure ()
    let mut state := state.insert n 1
    for e in a.nodeOutgoingEdges n do
      if a.edgeIsSelfLoop e then continue
      let some t := (a.edge e).target.bind (fun p => (a.port p).owner) | continue
      let (st, f) := visit a t state
      state := st
      if f then return (state, true)
    return (state.insert n 2, false)

/-- The edges whose `REVERSED` flag is set, in the given order. -/
def reversedOf (a : LGraphArena) (es : Array LEdgeId) : Array Nat :=
  (es.zipIdx.filter fun (e, _) => (a.edge e).internal.reversed).map (·.2)

/-- Source and target node of an edge. -/
def endsOf (a : LGraphArena) (e : LEdgeId) : Option LNodeId × Option LNodeId :=
  ((a.edge e).source.bind (fun p => (a.port p).owner), (a.edge e).target.bind (fun p => (a.port p).owner))

def allStrategies : Array CycleBreakingStrategy :=
  #[.greedy, .depthFirst, .interactive, .modelOrder, .greedyModelOrder, .sccConnectivity, .sccNodeType,
    .dfsNodeOrder, .bfsNodeOrder]

/-- Places node `i` at `x = 50 i` (input for the interactive breaker). -/
def placeByIndex (ns : Array LNodeId) : LayeredM Unit := do
  for i in [0:ns.size] do
    LayeredM.modifyNode ns[i]! fun x => { x with position := ⟨50.0 * i.toFloat, 0.0⟩ }

def acyclicTests : Suite := suite "layered.p1cycles.acyclic" do
  -- basic_cycle_breaker_test.rs: `*_produces_acyclic_graph` / `*_handles_dense_cycle_graph`
  for strategy in allStrategies do
    for (label, build) in #[("cyclic", cyclic true), ("dense", dense true)] do
      let ((g, before), a) ← LayeredM.run (do
          let (g, ns, _) ← build
          placeByIndex ns
          let before := hasCycle (← get) g
          runPhase strategy.createPhase g
          return (g, before))
      check s!"{ElkEnum.javaName strategy} {label}: input cyclic" before
      check s!"{ElkEnum.javaName strategy} {label}: acyclic after breaking" (!hasCycle a g)
      if strategy != .interactive then
        check s!"{ElkEnum.javaName strategy} {label}: CYCLIC set" (a.graph g).internal.cyclic

def greedyTests : Suite := suite "layered.p1cycles.GreedyCycleBreaker" do
  -- hand: Java new Random(0): next(31) = 1569741360; nextInt(3) = 1569741360 % 3 = 0; nextInt(2) = (2 * next(31)) >> 31 = 1
  checkEq "Random(0).nextInt(3)" ((Random.ofInt 0).nextInt 3).1 0
  checkEq "Random(0).nextInt(2)" ((Random.ofInt 0).nextInt 2).1 1
  -- 3-cycle: all outflows 0 → random pick index 0 (A, mark 1); A's neighbours: B becomes a source
  -- (mark 2), C a sink (mark -1 → 3). Only C→A goes from a higher to a lower mark.
  let ((g, ns, es), a) ← LayeredM.run (do
      let r ← cyclic
      LayeredM.modifyGraph r.1 fun x => { x with internal := { x.internal with random := some (Random.ofInt 0) } }
      runPhase GreedyCycleBreaker.phase r.1
      return r)
  checkEq "hand: 3-cycle reverses C→A only" (reversedOf a es) #[2]
  checkEq "reversed edge now A→C (source)" (endsOf a es[2]!).1 (some ns[0]!)
  checkEq "reversed edge now A→C (target)" (endsOf a es[2]!).2 (some ns[2]!)
  check "graph CYCLIC" (a.graph g).internal.cyclic
  check "graph RANDOM advanced by one nextInt(3)" ((a.graph g).internal.random == some ((Random.ofInt 0).nextInt 3).2)
  checkEq "node ids are the layerless indices" (ns.map fun n => (a.node n).id) #[0, 1, 2]
  -- S→A, A→B, B→A, B→T: T sink (-1), S source (1); A,B tie at outflow 0 → nextInt(2) = 1 → B (mark 2);
  -- then A becomes a sink (-2). Marks S1 A4 B2 T5: A→B is reversed.
  let ((_, es2), a2) ← LayeredM.run (do
      let (g, ns) ← mkGraph 4 (modelOrder := true)
      let e0 ← mkEdge ns[0]! ns[1]!
      let e1 ← mkEdge ns[1]! ns[2]!
      let e2 ← mkEdge ns[2]! ns[1]!
      let e3 ← mkEdge ns[2]! ns[3]!
      runPhase GreedyCycleBreaker.phase g
      return (g, #[e0, e1, e2, e3]))
  checkEq "hand: random tie-break picks B, A→B reversed" (reversedOf a2 es2) #[1]
  -- model order mode: the tie goes to the smaller model order (A, mark 2), then B is a source (3): B→A reversed
  let ((g3, es3), a3) ← LayeredM.run (do
      let (g, ns) ← mkGraph 4 (modelOrder := true)
      let e0 ← mkEdge ns[0]! ns[1]!
      let e1 ← mkEdge ns[1]! ns[2]!
      let e2 ← mkEdge ns[2]! ns[1]!
      let e3 ← mkEdge ns[2]! ns[3]!
      LayeredM.modifyGraph g fun x => { x with internal := { x.internal with random := some (Random.ofInt 0) } }
      runPhase GreedyCycleBreaker.modelOrderPhase g
      return (g, #[e0, e1, e2, e3]))
  checkEq "hand: model order tie-break picks A, B→A reversed" (reversedOf a3 es3) #[2]
  check "model order mode draws no random number (RANDOM untouched)" ((a3.graph g3).internal.random == some (Random.ofInt 0))
  -- PRIORITY_DIRECTION: weighting does not change a DAG, nothing is reversed
  let ((g4, es4), a4) ← LayeredM.run (do
      let (g, ns) ← mkGraph 3
      let e0 ← mkEdge ns[0]! ns[1]!
      LayeredM.setEdgeProp e0 LayeredOptions.PRIORITY_DIRECTION 3
      let e1 ← mkEdge ns[1]! ns[2]!
      let e2 ← mkEdge ns[0]! ns[0]!
      runPhase GreedyCycleBreaker.phase g
      return (g, #[e0, e1, e2]))
  checkEq "DAG with priority and self loop: nothing reversed" (reversedOf a4 es4) #[]
  check "DAG: CYCLIC not set" (!(a4.graph g4).internal.cyclic)
  checkEq "phase names" #[GreedyCycleBreaker.phase.name, GreedyCycleBreaker.modelOrderPhase.name]
    #["GreedyCycleBreaker", "GreedyModelOrderCycleBreaker"]

def depthFirstTests : Suite := suite "layered.p1cycles.DepthFirstCycleBreaker" do
  let ((_, _, es), a) ← LayeredM.run (do let r ← cyclic; runPhase DepthFirstCycleBreaker.phase r.1; return r)
  checkEq "hand: DFS from A reaches C, C→A is the back edge" (reversedOf a es) #[2]
  -- dense: DFS A→B→C→D→E, E→A is the only back edge
  let ((_, _, es2), a2) ← LayeredM.run (do let r ← dense; runPhase DepthFirstCycleBreaker.phase r.1; return r)
  checkEq "hand: dense graph reverses E→A" (reversedOf a2 es2) #[4]
  -- A→B, A→C, B→C, C→B: A is a source; DFS visits B first (port order), then C; C→B is the back edge
  let ((_, es3), a3) ← LayeredM.run (do
      let (g, ns) ← mkGraph 3
      let es := #[← mkEdge ns[0]! ns[1]!, ← mkEdge ns[0]! ns[2]!, ← mkEdge ns[1]! ns[2]!, ← mkEdge ns[2]! ns[1]!]
      runPhase DepthFirstCycleBreaker.phase g
      return (g, es))
  checkEq "hand: edge order decides, C→B reversed" (reversedOf a3 es3) #[3]

def nodeOrderTests : Suite := suite "layered.p1cycles.NodeOrder" do
  -- same graph, model orders A0 B2 C1: the DFS-node-order breaker visits C first, so B→C is the back edge
  let build (moB moC : Int) (parallel : Bool) : LayeredM (LGraphId × Array LEdgeId) := do
    let (g, ns) ← mkGraph 3
    setModelOrder ns[0]! 0
    setModelOrder ns[1]! moB
    setModelOrder ns[2]! moC
    let mut es := #[← mkEdge ns[0]! ns[1]!, ← mkEdge ns[0]! ns[2]!, ← mkEdge ns[1]! ns[2]!, ← mkEdge ns[2]! ns[1]!]
    if parallel then es := es.push (← mkEdge ns[1]! ns[2]!)
    return (g, es)
  let ((_, es), a) ← LayeredM.run (do let r ← build 2 1 false; runPhase DFSNodeOrderCycleBreaker.phase r.1; return r)
  checkEq "hand: DFS node order (C before B) reverses B→C" (reversedOf a es) #[2]
  let ((_, es2), a2) ← LayeredM.run (do let r ← build 2 1 true; runPhase DFSNodeOrderCycleBreaker.phase r.1; return r)
  checkEq "hand: the whole target group (parallel B→C) is reversed" (reversedOf a2 es2) #[2, 4]
  let ((_, es3), a3) ← LayeredM.run (do let r ← build 1 2 false; runPhase DFSNodeOrderCycleBreaker.phase r.1; return r)
  checkEq "hand: model orders B1 C2 → C→B reversed" (reversedOf a3 es3) #[3]
  -- BFS: queue A; A enqueues B, C (model order); B enqueues C; C sees visited B (C no source, B no sink) → C→B
  let ((_, es4), a4) ← LayeredM.run (do let r ← build 1 2 false; runPhase BFSNodeOrderCycleBreaker.phase r.1; return r)
  checkEq "hand: BFS node order B1 C2 reverses C→B" (reversedOf a4 es4) #[3]
  -- BFS: queue A; A enqueues C, B; C enqueues B; B sees visited C → B→C (both parallel edges)
  let ((_, es5), a5) ← LayeredM.run (do let r ← build 2 1 true; runPhase BFSNodeOrderCycleBreaker.phase r.1; return r)
  checkEq "hand: BFS node order B2 C1 reverses both B→C" (reversedOf a5 es5) #[2, 4]
  -- BFS sink rule: A→B, B→T, A→T: T is a sink, visiting T again never reverses
  let ((_, es6), a6) ← LayeredM.run (do
      let (g, ns) ← mkGraph 3 (modelOrder := true)
      let es := #[← mkEdge ns[0]! ns[1]!, ← mkEdge ns[1]! ns[2]!, ← mkEdge ns[0]! ns[2]!]
      runPhase BFSNodeOrderCycleBreaker.phase g
      return (g, es))
  checkEq "BFS: DAG with sink untouched" (reversedOf a6 es6) #[]

def modelOrderTests : Suite := suite "layered.p1cycles.ModelOrderCycleBreaker" do
  let ((_, _, es), a) ← LayeredM.run (do let r ← cyclic true; runPhase ModelOrderCycleBreaker.phase r.1; return r)
  checkEq "hand: model orders A0 B1 C2 → C→A reversed" (reversedOf a es) #[2]
  let ((_, _, es2), a2) ← LayeredM.run (do
      let r ← cyclic
      setModelOrder r.2.1[0]! 2
      setModelOrder r.2.1[1]! 0
      setModelOrder r.2.1[2]! 1
      runPhase ModelOrderCycleBreaker.phase r.1
      return r)
  checkEq "hand: model orders A2 B0 C1 → A→B reversed" (reversedOf a2 es2) #[0]
  -- layer constraint LAST on A shifts its order by offset 3 (A = 3): A→B reversed, C→A kept
  let ((_, _, es3), a3) ← LayeredM.run (do
      let r ← cyclic true
      LayeredM.setNodeProp r.2.1[0]! LayeredOptions.LAYERING_LAYER_CONSTRAINT LayerConstraint.last
      runPhase ModelOrderCycleBreaker.phase r.1
      return r)
  checkEq "hand: LAST constraint on A → A→B reversed" (reversedOf a3 es3) #[0]

def calculatorTests : Suite := suite "layered.p1cycles.GroupModelOrderCalculator" do
  let plain : LNode := { internal := { modelOrder := some 4 } }
  let withC (c : LayerConstraint) : LNode := { plain with props := plain.props.set LayeredOptions.LAYERING_LAYER_CONSTRAINT c }
  let c := GroupModelOrderCalculator.new
  checkEq "no constraint: model order" (c.computeConstraintModelOrder plain 5).1 4
  checkEq "FIRST: -offset + mo" (c.computeConstraintModelOrder (withC .first) 5).1 (-1)
  checkEq "LAST: offset + mo" (c.computeConstraintModelOrder (withC .last) 5).1 9
  let (v1, c1) := c.computeConstraintModelOrder (withC .firstSeparate) 5
  let (v2, c2) := c1.computeConstraintModelOrder (withC .firstSeparate) 5
  checkEq "FIRST_SEPARATE: -2 offset + count + mo" (v1, v2) (-6, -5)
  let (v3, _) := c2.computeConstraintModelOrder (withC .lastSeparate) 5
  checkEq "LAST_SEPARATE: 2 offset + mo" v3 14
  checkEq "counters" (c2.firstSeparateNodes, c2.lastSeparateNodes) (2, 0)
  let grouped : LNode := { plain with props := plain.props.set LayeredOptions.GROUP_MODEL_ORDER_CYCLE_BREAKING_ID 2 }
  checkEq "group: base + group * smallOffset + mo" (c.computeConstraintGroupModelOrder grouped 20 5).1 14
  let lastOnly : LNode := { props := ({} : PropertyMap).set LayeredOptions.LAYERING_LAYER_CONSTRAINT LayerConstraint.last }
  checkEq "no model order: base only" (c.computeConstraintModelOrder lastOnly 5).1 5
  checkEq "no model order and no constraint: 0" (c.computeConstraintModelOrder {} 5).1 0

def sccTests : Suite := suite "layered.p1cycles.SCC" do
  -- SCC [C, B, A]: min A (0), max C (2); in(A) = 1 is not > out(C) = 1 → reverse C's edges into the SCC
  let ((_, ns, es), a) ← LayeredM.run (do let r ← cyclic true; runPhase SCConnectivity.phase r.1; return r)
  checkEq "hand: connectivity reverses C→A" (reversedOf a es) #[2]
  checkEq "reversed without port adaptation: new source A" (endsOf a es[2]!).1 (some ns[0]!)
  checkEq "LAYERING_LAYER_ID of the new source incremented" ((a.node ns[0]!).props.get LayeredOptions.LAYERING_LAYER_ID) (some 0)
  checkEq "other nodes keep the default" ((a.node ns[1]!).props.get? LayeredOptions.LAYERING_LAYER_ID) none
  -- in(A) = 2 > out(C) = 1 → reverse A's incoming edges from the SCC (B→A, C→A)
  let ((_, es2), a2) ← LayeredM.run (do
      let (g, ns) ← mkGraph 3 (modelOrder := true)
      let es := #[← mkEdge ns[1]! ns[0]!, ← mkEdge ns[2]! ns[0]!, ← mkEdge ns[0]! ns[1]!, ← mkEdge ns[0]! ns[2]!]
      runPhase SCConnectivity.phase g
      return (g, es))
  checkEq "hand: connectivity reverses the min node's incoming edges" (reversedOf a2 es2) #[0, 1]
  -- node type, default options: preferred source id 0 == group id 0 → min node A's incoming edges
  let ((_, _, es3), a3) ← LayeredM.run (do let r ← cyclic true; runPhase SCCNodeTypeCycleBreaker.phase r.1; return r)
  checkEq "hand: node type (default ids) reverses C→A" (reversedOf a3 es3) #[2]
  -- preferred target: all outgoing edges of the max node C are reversed, even C→D leaving the SCC (Rust)
  let buildNT (src tgt : Int) : LayeredM (LGraphId × Array LEdgeId) := do
    let (g, ns) ← mkGraph 4 (modelOrder := true)
    LayeredM.setGraphProp g LayeredOptions.GROUP_MODEL_ORDER_CB_PREFERRED_SOURCE_ID src
    LayeredM.setGraphProp g LayeredOptions.GROUP_MODEL_ORDER_CB_PREFERRED_TARGET_ID tgt
    let es := #[← mkEdge ns[0]! ns[1]!, ← mkEdge ns[1]! ns[2]!, ← mkEdge ns[2]! ns[0]!, ← mkEdge ns[2]! ns[3]!]
    runPhase SCCNodeTypeCycleBreaker.phase g
    return (g, es)
  let ((g4, es4), a4) ← LayeredM.run (buildNT 5 0)
  checkEq "hand: preferred target reverses C→A and C→D" (reversedOf a4 es4) #[2, 3]
  check "preferred target result acyclic" (!hasCycle a4 g4)
  let ((_, es5), a5) ← LayeredM.run (buildNT 5 5)
  checkEq "hand: no preference → connectivity (in(A)=1 ≤ out(C)=2) reverses C→A" (reversedOf a5 es5) #[2]

def interactiveTests : Suite := suite "layered.p1cycles.InteractiveCycleBreaker" do
  -- x: A 0, B 100, C 50 → B→C and C→A point left and are reversed in phase 1
  let ((_, _, es), a) ← LayeredM.run (do
      let r ← cyclic
      let ns := r.2.1
      LayeredM.modifyNode ns[0]! fun x => { x with position := ⟨0, 0⟩, size := ⟨10, 10⟩ }
      LayeredM.modifyNode ns[1]! fun x => { x with position := ⟨100, 0⟩, size := ⟨10, 10⟩ }
      LayeredM.modifyNode ns[2]! fun x => { x with position := ⟨50, 0⟩, size := ⟨10, 10⟩ }
      runPhase InteractiveCycleBreaker.phase r.1
      return r)
  checkEq "hand: leftward edges reversed" (reversedOf a es) #[1, 2]
  -- all at the same x: phase 2 DFS from A finds the back edge C→A
  let ((g2, _, es2), a2) ← LayeredM.run (do let r ← cyclic; runPhase InteractiveCycleBreaker.phase r.1; return r)
  checkEq "hand: equal x → DFS back edge C→A" (reversedOf a2 es2) #[2]
  check "interactive does not set CYCLIC (Rust)" (!(a2.graph g2).internal.cyclic)

def configurationTests : Suite := suite "layered.p1cycles.registration" do
  let names ← allStrategies.mapM fun s => do
    let phase ← (LayeredPhases.strategyFactory .p1CycleBreaking "CycleBreakingStrategy" (ElkEnum.ordinal s) (ElkEnum.javaName s)).create
    return phase.name
  checkEq "registered phases (Rust type names)" names
    #["GreedyCycleBreaker", "DepthFirstCycleBreaker", "InteractiveCycleBreaker", "ModelOrderCycleBreaker",
      "GreedyModelOrderCycleBreaker", "SCConnectivity", "SCCNodeTypeCycleBreaker",
      "DFSNodeOrderCycleBreaker", "BFSNodeOrderCycleBreaker"]
  checkEq "createPhase matches the registry" (allStrategies.map (·.createPhase.name)) names
  let ((cfgs, icfg), _) ← LayeredM.run (do
      let cfgs ← allStrategies.mapM fun s => s.createPhase.getLayoutProcessorConfiguration ⟨0⟩
      let icfg ← InteractiveCycleBreaker.phase.getLayoutProcessorConfiguration ⟨0⟩
      return (cfgs, icfg))
  check "every breaker restores reversed edges after P5"
    (cfgs.all fun c => (c.map (·.processorsAfter LayeredPhases.p5EdgeRouting)) == some #[IntermediateProcessorStrategy.reversedEdgeRestorer])
  check "interactive positions external ports before P1"
    ((icfg.map (·.processorsBefore LayeredPhases.p1CycleBreaking)) == some #[IntermediateProcessorStrategy.interactiveExternalPortPositioner])
  check "greedy requests nothing before P1"
    (((cfgs[0]!).map (·.processorsBefore LayeredPhases.p1CycleBreaking)) == some #[])

def suites : Array Suite :=
  #[acyclicTests, greedyTests, depthFirstTests, nodeOrderTests, modelOrderTests, calculatorTests, sccTests,
    interactiveTests, configurationTests]

end Tests.Layered.P1Cycles
