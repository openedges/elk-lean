import Tests.Framework
import Elk.Alg.Layered
import Tests.Layered.IntermediatePreserveOrder
/-!
Differential tests of the round 14 P3H fast paths of the `GraphInfoHolder` construction against their
kept references: `GraphInfoHolder.buildParts` with the fused initialisation (`FusedInit.run`) against
`buildParts … (fused := false)` (`initHolder` and the generic `Initializable.init` callback chain), for
every `CrossMinType` (barycenter also with `FORCE_NODE_MODEL_ORDER`), on random layered graphs with
north/south port dummies, nested graphs, layout units, stale and negative ids, nodes whose `layer`
is another layer or none, and nodes listed in two layers. Compared: every id and port side cache of
the arena, the holder's fields and snapshot, the generator, and the state of the counter, the
decider, the port distributor and the heuristic (with the constraint resolver's tables).
-/
namespace Tests.Layered.P3HolderInit

open Tests Elk.Graph Elk.Core.Util Elk.Core.Options Elk.Alg.Layered Elk.Alg.Layered.Graph Elk.Alg.Layered.Options
open Elk.Alg.Layered.P3Order Elk.Alg.Layered.P3Order.Counting Elk.Alg.Layered.P3Order.GraphInfoHolder
open Tests.Layered.IntermediatePreserveOrder (lcgNext rnd randomGraph sameSnapshot)

/-- A random graph for the holder (see the module doc). -/
def holderGraph (seed : UInt64) : LayeredM LGraphId := do
  let rg ← randomGraph seed
  let mut s := lcgNext (seed + 17)
  let n := rg.nodes.size
  for h : i in [0:rg.nodes.size] do
    let nd := rg.nodes[i]
    let (v, s1) := rnd s 24
    let (w, s2) := rnd s1 (n + 1)
    let (idv, s3) := rnd s2 9
    s := s3
    LayeredM.modifyNode nd fun x => { x with id := (idv : Int) - 3 }
    if v == 0 then LayeredM.modifyNode nd fun x => { x with type := .northSouthPort }
    if v == 1 then LayeredM.modifyNode nd fun x => { x with type := .externalPort }
    if v == 2 || v == 3 then
      let child ← LayeredM.createGraph
      LayeredM.modifyNode nd fun x => { x with nestedGraph := some child }
    if v == 4 || v == 5 then
      if h : w < rg.nodes.size then
        let u := rg.nodes[w]
        LayeredM.modifyNode nd fun x => { x with internal.inLayerLayoutUnit := some u }
    if v == 6 then LayeredM.modifyNode nd fun x => { x with layer := none }
    if v == 7 then
      if h : w < rg.layers.size then
        let l := rg.layers[w]
        LayeredM.modifyNode nd fun x => { x with layer := some l }
    -- listed in a second layer as well
    if v == 8 && !rg.layers.isEmpty then
      let l := rg.layers[w % rg.layers.size]!
      LayeredM.modifyLayer l fun x => { x with nodes := x.nodes.push nd }
  for p in rg.ports do
    let (v, s1) := rnd s 7
    s := s1
    LayeredM.modifyPort p fun x => { x with id := (v : Int) - 2 }
  for h : i in [0:rg.layers.size] do
    let (v, s1) := rnd s 6
    s := s1
    LayeredM.modifyLayer rg.layers[i] fun x => { x with id := (v : Int) - 1 }
  -- occasionally an empty layer
  let (e, s1) := rnd s 5
  s := s1
  if e == 0 then
    let l ← LayeredM.createLayer rg.graph
    LayeredM.modifyGraph rg.graph fun x => { x with layers := x.layers.push l }
  let (sb, _) := rnd s 2
  LayeredM.modifyGraph rg.graph fun x => { x with internal.inLayerSuccessorConstraintsBetweenNonDummies := sb == 0 }
  return rg.graph

/-- A text fingerprint of the generator. -/
def randomFp (r : Random) : String :=
  let (b, r) := r.nextBoolean
  let (l, _) := r.nextLongBits
  s!"{b}/{l}"

/-- A text fingerprint of a barycenter state. -/
def stateFp : Option BarycenterState → String
  | some st => s!"({st.node.idx},{st.summedWeight},{st.degree},{st.barycenterValue},{st.hasBarycenter},{st.visited})"
  | none => "-"

/-- A text fingerprint of a constraint group. -/
def groupFp (g : ConstraintGroup) : String :=
  s!"({g.summedWeight},{g.degree},{g.nodes.map (·.idx)},{g.outgoingConstraints},{g.incomingConstraints},{g.incomingConstraintsCount})"

/-- The fingerprint of everything the initialisation writes (see the module doc). -/
def fingerprint (h : GraphInfoHolder) (dist : PortDistributorImpl) (heur : HeuristicImpl)
    (decider : LayerSweepTypeDecider) : LayeredM String := do
  let a ← get
  let nodes := a.nodes.map fun n => s!"{n.id}:{n.portSidesCached}:{repr n.portSideIndices}"
  let ports := a.ports.map (·.id)
  let layers := a.layers.map (·.id)
  let c := h.crossingsCounter
  let counter := s!"{← c.hasNorthSouthPorts.get}|{← c.hasHyperEdgesEastOfIndex.get}|{← c.nPorts.get}|" ++
    s!"{← c.inLayerEdgeCounts.get}|{← c.crossingCounter.portPositions.get}|{(← c.crossingCounter.indexTree.get).maxNum}|" ++
    s!"{← c.crossingCounter.nodeCardinalities.get}"
  let info := repr (← decider.nodeInfo.get)
  let distFp ← match dist with
    | .barycenter d => do
      let st ← d.state.get
      pure s!"bary {st.nodePositions} {st.nPorts} {st.portRanks.data} {st.portBarycenter.data}"
    | .greedy d => do
      let cc ← match ← d.crossingsCounter.get with
        | some cc => pure (toString (← cc.portPositions.get))
        | none => pure "none"
      pure s!"greedy {← d.nPorts.get} {cc}"
  let heurFp ← match heur.barycenterBase?, heur with
    | some b, _ => do
      let r := b.constraintResolver
      let units ← r.layoutUnits.get
      let unitFp := (Array.range a.nodes.size).map fun i => (units.get? ⟨i⟩).map (·.map (·.idx))
      let states ← r.barycenterStates.get
      let groups ← r.constraintGroups.get
      let garena ← r.constraintGroupArena.get
      pure (s!"bary {(← b.portRanks.get).data} {unitFp} {units.size} {states.map (·.map stateFp)} " ++
        s!"{groups} {garena.map groupFp}")
    | none, .greedySwitch g => pure s!"greedy {← g.nPorts.get} {← g.portPositions.get} {← g.dontSweepInto.get}"
    | none, _ => pure "median"
  return s!"{nodes}\n{ports}\n{layers}\n{h.childGraphs.map (·.idx)} {h.nPorts} {h.useBottomUp} " ++
    s!"{h.hasExternalPorts} {h.parentGraphIndex}\n{counter}\n{info}\n{distFp}\n{heurFp}\n{randomFp (← h.random.get)}"

/-- Builds a holder on `a` (fused or reference) and returns its fingerprint and snapshot. -/
def buildOn (a : LGraphArena) (g : LGraphId) (type : CrossMinType) (seed : Int) (fused : Bool) :
    IO (Except String (String × CrossMinSnapshot × Nat)) := do
  let random ← IO.mkRef (Random.ofInt seed)
  let r ← (LayeredM.run (do
      let order := (← get).graphToNodeArray g
      let s ← GraphInfoHolder.readSettings g
      let (h, dist, heur, decider) ← GraphInfoHolder.buildParts g type order s random fused
      return (← fingerprint h dist heur decider, h.snapshot)) a).toBaseIO
  match r with
  | .ok ((fp, snap), a) => return .ok (fp, snap, a.nodes.size + a.ports.size + 8)
  | .error e => return .error (toString e)

/-- Fused = reference for all `CrossMinType`s on random graphs. -/
def fusedInitTests : Suite := suite "layered.p3.fusedInit" do
  let types : Array (CrossMinType × Bool) :=
    #[(.barycenter, false), (.barycenter, true), (.median, false), (.oneSidedGreedySwitch, false),
      (.twoSidedGreedySwitch, false)]
  let mut bad := 0
  let mut runs := 0
  let mut errors := 0
  let mut withUnits := 0
  for k in [0:400] do
    let seed : UInt64 := (k.toUInt64 + 5) * 0x9e3779b97f4a7c15
    for (type, force) in types do
      let (g, a) ← LayeredM.run (do
        let g ← holderGraph seed
        LayeredM.setGraphProp g LayeredOptions.CROSSING_MINIMIZATION_FORCE_NODE_MODEL_ORDER force
        return g)
      if type == .barycenter && !force && a.nodes.any (·.internal.inLayerLayoutUnit.isSome) then
        withUnits := withUnits + 1
      runs := runs + 1
      let fused ← buildOn a g type (k : Int) true
      let ref ← buildOn a g type (k : Int) false
      match fused, ref with
      | .ok (f1, s1, keys), .ok (f2, s2, _) =>
        if f1 != f2 || !sameSnapshot s1 s2 keys then
          bad := bad + 1
          if bad <= 2 then IO.println s!"fused init differs (seed {k}, {repr type}, force {force}):\n{f1}\n--\n{f2}"
      | .error e1, .error e2 =>
        errors := errors + 1
        if e1 != e2 then bad := bad + 1
      | _, _ => bad := bad + 1
  checkEq s!"fused initialisation = generic initialisation ({runs} holders, {errors} failing alike)" bad 0
  check "layout units are exercised" (withUnits > 20)

/-- `IdIndex.ofPairs` (tail loops) = `IdIndex.ofPairsRef` (the `for` loops) on random pairs: dense and
sparse ranges, duplicate keys (the later pair wins), empty input; compared on every key around the range. -/
def idIndexTests : Suite := suite "layered.p3.idIndex.ofPairs" do
  let mut bad := 0
  let mut sparse := 0
  let mut s : UInt64 := 0x2545F4914F6CDD1D
  for k in [0:600] do
    let (n, s1) := rnd s 40
    let (spread, s2) := rnd s1 4
    s := s2
    let span := match spread with
      | 0 => n + 1
      | 1 => 3 * n + 5
      | 2 => 5000
      | _ => 200000
    let mut keys : Array Nat := #[]
    let mut values : Array Nat := #[]
    for _ in [0:n] do
      let (key, s1) := rnd s span
      let (v, s2) := rnd s1 1000
      s := s2
      keys := keys.push (key + k % 7)
      values := values.push v
    let fast := IdIndex.ofPairs keys values
    let ref := IdIndex.ofPairsRef keys values
    if !fast.isDense then sparse := sparse + 1
    let hi := (keys.foldl max 0) + 3
    if fast.isDense != ref.isDense || fast.base != ref.base || fast.dense != ref.dense ||
        !((Array.range (hi + 1)).all fun x => fast.get x == ref.get x) then
      bad := bad + 1
  checkEq "ofPairs = ofPairsRef (600 key sets)" bad 0
  check "sparse indices are exercised" (sparse > 50)

def suites : Array Suite := #[fusedInitTests, idIndexTests]

end Tests.Layered.P3HolderInit
