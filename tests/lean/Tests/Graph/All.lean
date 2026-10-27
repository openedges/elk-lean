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

def suites : Array Tests.Suite := #[elkGraphUtilTests, graphIdentifierGeneratorTests]

end Tests.Graph
