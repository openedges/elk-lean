import Tests.Framework
import Tests.JsonCompare
import Elk.Api
import Elk.Alg.Layered
/-!
Regression tests for the layered `NodePromotion` processor and `ModelOrderBarycenterHeuristic` aligned with
ELK Java 0.12.0 (agent NIK). Java runs the Nikolov et al. heuristic (`promotionMagic`) for every strategy
other than the two model order ones; elk-rs (and elk-lean before) left the layering unchanged.

* `layered.nodePromotion.java`: `tests/fixtures/promotion/processor_cases.jsonl` holds hand-described
  layered graphs (layers of nodes with a height, an optional `MODEL_ORDER` and type, edges between fresh
  ports in creation order, the strategy, `maxIterations` and the two spacings) with the layering that the
  unmodified ELK Java 0.12.0 `NodePromotion` processor produces (`expected`, node indices per layer) or
  the exception it throws (`error`). The cases come from a random generator (proper layerings, long and
  multi-edges, every strategy) run through a Java harness that calls
  `new NodePromotion().process(graph, monitor)` on `LGraph`s built the same way.
* `layered.nodePromotion.layouts`: whole layouts (`tests/fixtures/promotion/<name>.json`) compared at
  tolerance `0` with ELK Java's (`<name>.java.json`, `scripts/run_java_baseline.sh`).
* `layered.modelOrderBarycenter.relations`: `relation_cases.jsonl`, arbitrary (also cyclic and
  self-related) `biggerThan`/`smallerThan` states with the states after Java's private
  `ModelOrderBarycenterHeuristic.updateBiggerAndSmallerAssociations(bigger, smaller)` (called by
  reflection on the unmodified class).
* `layered.p2layers.coffmanGraham.java`: `coffman_graham_cases.jsonl`, random DAGs of layerless nodes
  (one new port per edge end, layer bound) with the layering of the unmodified Java
  `CoffmanGrahamLayerer` (`PriorityQueue` heaps, `Integer` identity in `compareNodesInTopo`); the Coffman–
  Graham layering decides what node promotion starts from.
-/
namespace Tests.Api.LayeredNodePromotion

open Tests Elk.Api Elk.Json Elk.Graph Elk.Core.Util Elk.Alg.Layered Elk.Alg.Layered.Graph Elk.Alg.Layered.Options
  Elk.Alg.Layered.Intermediate

private def fixtureDir : System.FilePath := "tests/fixtures/promotion"

/-- Builds the case's graph (`NodePromotionHarness` order: layers, nodes, then one new port per edge end),
runs `NodePromotion` and returns the layers as node indices. -/
def runCase (c : Value) : IO (Except String (Array (Array Nat))) := do
  let action : LayeredM (Array (Array Nat)) := do
    let g ← LayeredM.createGraph
    let some strategyName := (c.get? "strategy").bind Value.getStr? | throw (IO.userError "case: strategy")
    let some strategy := (Elk.ElkEnum.ofJavaName? strategyName : Option NodePromotionStrategy)
      | throw (IO.userError s!"case: strategy {strategyName}")
    LayeredM.setGraphProp g LayeredOptions.LAYERING_NODE_PROMOTION_STRATEGY strategy
    if let some n := (c.get? "maxIterations").bind Value.getInt? then
      LayeredM.setGraphProp g LayeredOptions.LAYERING_NODE_PROMOTION_MAX_ITERATIONS n
    if let some s := (c.get? "spacingNodeNode").bind Value.getFloat? then
      LayeredM.setGraphProp g LayeredOptions.SPACING_NODE_NODE s
    if let some s := (c.get? "spacingEdgeNode").bind Value.getFloat? then
      LayeredM.setGraphProp g LayeredOptions.SPACING_EDGE_NODE_BETWEEN_LAYERS s
    let mut all : Array LNodeId := #[]
    let mut layers : Array LayerId := #[]
    for layerSpec in ((c.get? "layers").bind Value.getArr?).getD #[] do
      let layer ← LayeredM.createLayer g
      layers := layers.push layer
      for nodeSpec in layerSpec.getArr?.getD #[] do
        let type := ((nodeSpec.get? "type").bind Value.getStr?).bind (Elk.ElkEnum.ofJavaName? (α := NodeType)) |>.getD .normal
        let h := ((nodeSpec.get? "h").bind Value.getFloat?).getD 0.0
        let n ← LayeredM.createNode g { type, size := { x := 0.0, y := h } }
        if let some mo := (nodeSpec.get? "mo").bind Value.getInt? then
          LayeredM.modifyNode n fun x => { x with internal := { x.internal with modelOrder := some mo } }
        LayeredM.setNodeLayer n (some layer)
        all := all.push n
    let ls := layers
    LayeredM.modifyGraph g fun x => { x with layers := ls }
    for edgeSpec in ((c.get? "edges").bind Value.getArr?).getD #[] do
      let ends := (edgeSpec.getArr?.getD #[]).filterMap Value.getInt?
      let some s := ends[0]? | continue
      let some t := ends[1]? | continue
      let sp ← LayeredM.createPort
      LayeredM.setPortNode sp (some all[s.toNat]!)
      let tp ← LayeredM.createPort
      LayeredM.setPortNode tp (some all[t.toNat]!)
      let e ← LayeredM.createEdge
      LayeredM.setEdgeSource e (some sp)
      LayeredM.setEdgeTarget e (some tp)
    NodePromotion.processor.process g ProgressMonitor.null
    let a ← get
    return (a.graphToNodeArray g).map fun l => l.map fun n => (all.findIdx? (· == n)).getD 1000000
  try
    let (r, _) ← LayeredM.run action
    return .ok r
  catch e => return .error (toString e)

/-- The expected layering of a case (`expected`, node indices per layer). -/
def expectedLayers (c : Value) : Option (Array (Array Nat)) :=
  ((c.get? "expected").bind Value.getArr?).map fun ls =>
    ls.map fun l => (l.getArr?.getD #[]).map fun v => (v.getInt?.getD (-1)).toNat

def processorCases : Suite := suite "layered.nodePromotion.java" do
  let text ← IO.FS.readFile (fixtureDir / "processor_cases.jsonl")
  for line in text.splitOn "\n" do
    if line.trimAscii.isEmpty then continue
    match Elk.Json.parseString line with
    | .error e => report "processor case parses" false e
    | .ok c =>
      let name := ((c.get? "name").bind Value.getStr?).getD "?"
      let strategy := ((c.get? "strategy").bind Value.getStr?).getD "?"
      let result ← runCase c
      match (c.get? "error").bind Value.getStr?, result with
      | some err, .error e => checkEq s!"{name} ({strategy}): ELK Java's exception" e err
      | some err, .ok r => report s!"{name} ({strategy}): ELK Java's exception" false s!"got {r}, Java threw {err}"
      | none, .ok r => checkEq s!"{name} ({strategy}): ELK Java's layering" r ((expectedLayers c).getD #[])
      | none, .error e => report s!"{name} ({strategy}): ELK Java's layering" false e

/-- The layout fixtures compared with `<name>.java.json` (node promotion / model order barycenter variants of
the random `v` graphs; every one differed from ELK Java before): one per Nikolov strategy (`nikolov`,
`nikolov_pixel`, `nikolov_improved`, `nikolov_improved_pixel`, `dummynode_percentage`,
`nodecount_percentage`, `no_boundary`), Nikolov after a Coffman–Graham layering, the Coffman–Graham heap
order, `forceNodeModelOrder` with group ids outside the `Integer` cache and with an `ENFORCED` group order
of the processed graph, and the layer ids the model order promotion leaves for `SortByInputModelProcessor`. -/
def fixtures : Array String := #[
  "nikolov", "nikolov_pixel", "nikolov_improved", "nikolov_improved_pixel", "dummynode_percentage",
  "nodecount_percentage", "no_boundary", "nikolov_coffman_graham", "coffman_graham_heap",
  "model_order_barycenter_group_ids", "model_order_barycenter_enforced", "model_order_promotion_layer_ids"]

def layouts : Suite := suite "layered.nodePromotion.layouts" do
  for name in fixtures do
    let input ← IO.FS.readFile (fixtureDir / s!"{name}.json")
    match ← layoutJson input "{}" (pretty := false) (sortKeys := true) with
    | .ok out =>
      let expected ← IO.FS.readFile (fixtureDir / s!"{name}.java.json")
      checkJson s!"{name}: ELK Java layout (tol 0)" out expected
    | .error e => report s!"{name}: layout expected" false e

/-- Node index arrays of a JSON array of arrays. -/
private def indexSets (v : Option Value) : Array (Array Nat) :=
  ((v.bind Value.getArr?).getD #[]).map fun s => (s.getArr?.getD #[]).map fun x => (x.getInt?.getD (-1)).toNat

/-- `ModelOrderBarycenterRelations` of a relation case (node `i` = `LNodeId` `i`). -/
private def relationsOf (n : Nat) (bigger smaller : Array (Array Nat)) :
    Elk.Alg.Layered.P3Order.ModelOrderBarycenterRelations := Id.run do
  let mut rel : Elk.Alg.Layered.P3Order.ModelOrderBarycenterRelations := {}
  for i in [0:n] do
    let b : Std.HashSet LNodeId := (bigger[i]?.getD #[]).foldl (fun s x => s.insert ⟨x⟩) {}
    let s : Std.HashSet LNodeId := (smaller[i]?.getD #[]).foldl (fun s x => s.insert ⟨x⟩) {}
    rel := { biggerThan := rel.biggerThan.insert ⟨i⟩ b, smallerThan := rel.smallerThan.insert ⟨i⟩ s }
  return rel

/-- The sets of a relation map as sorted node indices. -/
private def sortedSets (n : Nat) (m : Std.HashMap LNodeId (Std.HashSet LNodeId)) : Array (Array Nat) :=
  (Array.range n).map fun i => stableSort ((m.getD ⟨i⟩ {}).toArray.map (·.idx)) compare

def relationCases : Suite := suite "layered.modelOrderBarycenter.relations" do
  let text ← IO.FS.readFile (fixtureDir / "relation_cases.jsonl")
  for line in text.splitOn "\n" do
    if line.trimAscii.isEmpty then continue
    match Elk.Json.parseString line with
    | .error e => report "relation case parses" false e
    | .ok c =>
      let name := ((c.get? "name").bind Value.getStr?).getD "?"
      let n := (((c.get? "n").bind Value.getInt?).getD 0).toNat
      let b := (((c.get? "b").bind Value.getInt?).getD 0).toNat
      let s := (((c.get? "s").bind Value.getInt?).getD 0).toNat
      let rel := relationsOf n (indexSets (c.get? "bigger")) (indexSets (c.get? "smaller"))
      let after := rel.updateBiggerAndSmallerAssociations ⟨b⟩ ⟨s⟩
      checkEq s!"{name}: biggerThan as ELK Java's" (sortedSets n after.biggerThan) (indexSets (c.get? "biggerAfter"))
      checkEq s!"{name}: smallerThan as ELK Java's" (sortedSets n after.smallerThan) (indexSets (c.get? "smallerAfter"))

/-- Builds a Coffman–Graham case (layerless nodes, then one new port per edge end), runs the layerer and
returns the layers as node indices. -/
def runCoffmanGrahamCase (c : Value) : IO (Except String (Array (Array Nat))) := do
  let action : LayeredM (Array (Array Nat)) := do
    let g ← LayeredM.createGraph
    if let some b := (c.get? "bound").bind Value.getInt? then
      LayeredM.setGraphProp g LayeredOptions.LAYERING_COFFMAN_GRAHAM_LAYER_BOUND b
    let n := (((c.get? "n").bind Value.getInt?).getD 0).toNat
    let mut all : Array LNodeId := #[]
    for _ in [0:n] do
      let node ← LayeredM.createNode g
      all := all.push node
    let nodes := all
    LayeredM.modifyGraph g fun x => { x with layerlessNodes := nodes }
    for edgeSpec in ((c.get? "edges").bind Value.getArr?).getD #[] do
      let ends := (edgeSpec.getArr?.getD #[]).filterMap Value.getInt?
      let some s := ends[0]? | continue
      let some t := ends[1]? | continue
      let sp ← LayeredM.createPort
      LayeredM.setPortNode sp (some all[s.toNat]!)
      let tp ← LayeredM.createPort
      LayeredM.setPortNode tp (some all[t.toNat]!)
      let e ← LayeredM.createEdge
      LayeredM.setEdgeSource e (some sp)
      LayeredM.setEdgeTarget e (some tp)
    Elk.Alg.Layered.P2Layers.CoffmanGrahamLayerer.process g ProgressMonitor.null
    let a ← get
    return (a.graphToNodeArray g).map fun l => l.map fun x => (all.findIdx? (· == x)).getD 1000000
  try
    let (r, _) ← LayeredM.run action
    return .ok r
  catch e => return .error (toString e)

def coffmanGrahamCases : Suite := suite "layered.p2layers.coffmanGraham.java" do
  let text ← IO.FS.readFile (fixtureDir / "coffman_graham_cases.jsonl")
  for line in text.splitOn "\n" do
    if line.trimAscii.isEmpty then continue
    match Elk.Json.parseString line with
    | .error e => report "Coffman-Graham case parses" false e
    | .ok c =>
      let name := ((c.get? "name").bind Value.getStr?).getD "?"
      match ← runCoffmanGrahamCase c with
      | .ok r => checkEq s!"{name}: ELK Java's Coffman-Graham layering" r ((expectedLayers c).getD #[])
      | .error e => report s!"{name}: ELK Java's Coffman-Graham layering" false e

def suites : Array Suite := #[processorCases, layouts, relationCases, coffmanGrahamCases]

end Tests.Api.LayeredNodePromotion
