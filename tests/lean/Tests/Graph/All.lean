import Tests.Framework
import Elk.Graph
/-! Test suites for `org.eclipse.elk.graph` (ported from elk-rs `plugins/org.eclipse.elk.graph/tests`):
`elk_graph_util_test.rs`, `graph_identifier_generator_test.rs`. -/
namespace Tests.Graph

open Tests Elk.Graph

/-- `create_edge_without_containment`. -/
private def edgeWithoutContainment (g : ElkGraph) (source target : Option ConnectableId) : ElkGraph × EdgeId :=
  let (g, e) := ElkGraphUtil.createEdge g none
  let g := match source with
    | some s => g.addEdgeSource e s
    | none => g
  let g := match target with
    | some t => g.addEdgeTarget e t
    | none => g
  (g, e)

def elkGraphUtilTests : Suite := suite "graph.ElkGraphUtil" do
  -- test_connectable_shape_to_node
  let (g, node) := ElkGraphUtil.createGraph
  checkEq "shape->node (node)" ((ElkGraphUtil.connectableShapeToNode g (.node node)).map (·.idx)) (some node.idx)
  let (g, port) := ElkGraphUtil.createPort g (some node)
  checkEq "shape->node (port)" ((ElkGraphUtil.connectableShapeToNode g (.port port)).map (·.idx)) (some node.idx)

  -- test_connectable_shape_to_port
  let (g0, n0) := ElkGraphUtil.createGraph
  checkNone "shape->port (node)" (ElkGraphUtil.connectableShapeToPort (.node n0))
  let (g0, parent) := ElkGraphUtil.createNode g0 none
  let (_, p0) := ElkGraphUtil.createPort g0 (some parent)
  checkEq "shape->port (port)" ((ElkGraphUtil.connectableShapeToPort (.port p0)).map (·.idx)) (some p0.idx)

  -- test_find_best_edge_containment
  let (g, graph1) := ElkGraphUtil.createGraph
  let (g, node1) := ElkGraphUtil.createNode g (some graph1)
  let (g, node2) := ElkGraphUtil.createNode g (some graph1)
  let (g, node3) := ElkGraphUtil.createNode g (some graph1)
  let (g, node3_1) := ElkGraphUtil.createNode g (some node3)
  let (g, node3_1_1) := ElkGraphUtil.createNode g (some node3_1)
  let (g, node4) := ElkGraphUtil.createNode g (some graph1)
  let (g, node4_1) := ElkGraphUtil.createNode g (some node4)
  let (g, graph2) := ElkGraphUtil.createNode g none
  let (g, nodeA) := ElkGraphUtil.createNode g (some graph2)

  let contain (g : ElkGraph) (s t : Option NodeId) : Option Nat :=
    let (g, e) := edgeWithoutContainment g (s.map .node) (t.map .node)
    (ElkGraphUtil.findBestEdgeContainment g e).map (·.idx)
  checkEq "same level edge" (contain g (some node1) (some node2)) (some graph1.idx)
  checkEq "self loop edge" (contain g (some node1) (some node1)) (some graph1.idx)
  checkEq "down level edge" (contain g (some node1) (some node3_1)) (some graph1.idx)
  checkEq "up level edge" (contain g (some node3_1) (some node2)) (some graph1.idx)
  checkEq "to child edge" (contain g (some node3) (some node3_1)) (some node3.idx)
  checkEq "to parent edge" (contain g (some node3_1) (some node3)) (some node3.idx)
  checkEq "to grand child edge" (contain g (some node3) (some node3_1_1)) (some node3.idx)
  checkEq "to grand parent edge" (contain g (some node3_1_1) (some node3)) (some node3.idx)
  checkEq "cross hierarchy edge" (contain g (some node3_1) (some node4_1)) (some graph1.idx)
  checkEq "cross graph edge" (contain g (some node1) (some nodeA)) none
  checkEq "source missing edge" (contain g none (some node2)) (some graph1.idx)
  checkEq "target missing edge" (contain g (some node2) none) (some graph1.idx)

  -- test_find_best_edge_containment_with_unconnected_edge
  -- (Rust panics with "edge must have at least one source or target"; Lean returns `none`.)
  let (g, e) := ElkGraphUtil.createEdge g none
  checkNone "unconnected edge has no containment" (ElkGraphUtil.findBestEdgeContainment g e)

private def nodeIdentifier (g : ElkGraph) (n : NodeId) : Option String := (g.node n).identifier

def graphIdentifierGeneratorTests : Suite := suite "graph.GraphIdentifierGenerator" do
  -- generates_missing_identifiers
  let (g, root) := ElkGraphUtil.createGraph
  let (g, child) := ElkGraphUtil.createNode g (some root)
  let (g, port) := ElkGraphUtil.createPort g (some child)
  let (g, edge) := ElkGraphUtil.createEdge g (some root)
  let g := g.addEdgeSource edge (.node child)
  let g := g.addEdgeTarget edge (.port port)
  let (g, label) := ElkGraphUtil.createLabel g (some (.node child))
  let (g, section_) := g.createSection (some edge)
  match (GraphIdentifierGenerator.forGraph g root).assertExists.execute with
  | .error msg => check s!"generate: unexpected error {msg}" false
  | .ok g =>
    checkEq "root id" (nodeIdentifier g root) (some "G1")
    check "child id starts with N" ((nodeIdentifier g child).any (·.startsWith "N"))
    check "port id starts with P" (((g.port port).identifier).any (·.startsWith "P"))
    check "edge id starts with E" (((g.edge edge).identifier).any (·.startsWith "E"))
    check "label id starts with L" (((g.label label).identifier).any (·.startsWith "L"))
    check "section id starts with ES" (((g.edgeSection section_).identifier).any (·.startsWith "ES"))

  -- validates_identifier_characters
  let (g, root) := ElkGraphUtil.createGraph
  let (g, child) := ElkGraphUtil.createNode g (some root)
  let (g, section_) := g.createSection none
  let g := g.modifyNode child fun n => { n with identifier := some "a b" }
  let g := g.modifySection section_ fun s => { s with identifier := some "1bad" }
  let (g, edge) := ElkGraphUtil.createEdge g (some root)
  let g := g.setSectionParent section_ (some edge)
  match (GraphIdentifierGenerator.forGraph g root).assertValid.execute with
  | .error msg => check s!"validate: unexpected error {msg}" false
  | .ok g =>
    checkEq "validated node id" (nodeIdentifier g child) (some "a_b")
    checkEq "validated section id" ((g.edgeSection section_).identifier) (some "_bad")

  -- ensures_unique_identifiers
  let (g, root) := ElkGraphUtil.createGraph
  let (g, node1) := ElkGraphUtil.createNode g (some root)
  let (g, node2) := ElkGraphUtil.createNode g (some root)
  let g := g.modifyNode node1 fun n => { n with identifier := some "dup" }
  let g := g.modifyNode node2 fun n => { n with identifier := some "dup" }
  match (GraphIdentifierGenerator.forGraph g root).assertUnique.execute with
  | .error msg => check s!"unique: unexpected error {msg}" false
  | .ok g =>
    let id1 := (nodeIdentifier g node1).getD ""
    let id2 := (nodeIdentifier g node2).getD ""
    checkEq "first duplicate kept" id1 "dup"
    check "second duplicate renamed" (id2.startsWith "dup_g")
    check "ids differ" (id1 != id2)
    checkEq "suffix is four digits" id2.length 9

/-- `ElkEnum.normalizeName` (byte-wise) agrees with the `List Char` definition it replaced. -/
def enumNormalizeTests : Tests.Suite := Tests.suite "graph.enum.normalizeName" do
  let reference (s : String) : String := String.ofList ((s.toList.filter Char.isAlphanum).map Char.toUpper)
  for s in ["H_CENTER", "hCenter", "h-center", "  Orthogonal ", "é_x1ß", "", "a1_B2-c3", "日本SPLINES", "node_size.minimum"] do
    Tests.checkEq s!"normalizeName {repr s}" (Elk.ElkEnum.normalizeName s) (reference s)
  -- the byte-wise `ofNameLoose?` / `EnumSet.parse?` agree with the string-building formulations
  let refLoose (s : String) : Option Elk.Graph.GraphFeature :=
    let t := s.trimAscii.toString
    if t.isEmpty then none
    else match t.toNat? with
      | some i => Elk.ElkEnum.ofOrdinal? i
      | none =>
        let n := Elk.ElkEnum.normalizeName t
        (Elk.ElkEnum.values : Array Elk.Graph.GraphFeature).find? (fun v => Elk.ElkEnum.normalizeName (Elk.ElkEnum.javaName v) == n)
  let refSet (s : String) : Option (Elk.EnumSet Elk.Graph.GraphFeature) := Id.run do
    let trimmed := s.trimAscii.toString
    if trimmed.isEmpty then return some Elk.EnumSet.empty
    let normalized := String.map (fun c => if c == '[' || c == ']' || c == ',' || c.isWhitespace then ' ' else c) trimmed
    let mut set : Elk.EnumSet Elk.Graph.GraphFeature := Elk.EnumSet.empty
    for tok in normalized.splitOn " " do
      let t := tok.trimAscii.toString
      if t.isEmpty then continue
      match (refLoose t) with
      | some v => set := set.insert v
      | none => return none
    return some set
  let cases := ["SELF_LOOPS", "selfLoops", " self-loops\t", "SELFLOOPS", "Self_Loops_", "_SELF_LOOPS",
    "3", "03", "0_3", "_3", "3_", "1__2", " 7 ", "8", "", "  ", "-", "é", "selfLoopsé", "self loops",
    "PORTS", "ports2", "INSIDE_SELF_LOOPS", "insideSelfLoops", "EDGE_LABELS", "日本", "disconnected\n"]
  for s in cases do
    Tests.check s!"ofNameLoose? {repr s}" ((Elk.ElkEnum.ofNameLoose? s : Option Elk.Graph.GraphFeature) == refLoose s)
  let setCases := cases ++ ["[PORTS, SELF_LOOPS]", "[]", "[ ]", "PORTS,,COMPOUND", "[PORTS, nope]", "PORTS  compound",
    "[ports,\tclusters]\r\n", "[,]", "[PORTS] [EDGE_LABELS]", "2,3", "[2, x]", "[é]"]
  for s in setCases do
    Tests.check s!"EnumSet.parse? {repr s}" ((Elk.Graph.EnumSet.parse? s : Option (Elk.EnumSet Elk.Graph.GraphFeature)) == refSet s)

def suites : Array Tests.Suite := #[elkGraphUtilTests, graphIdentifierGeneratorTests, enumNormalizeTests]

end Tests.Graph
