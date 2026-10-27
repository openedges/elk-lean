import Tests.Framework
import Elk.Text
/-!
# Tests for the `.elkt` parser (`Elk.Text`)

Ported from elk-rs `plugins/org.eclipse.elk.alg.layered/tests/general/elkt_loader_test.rs`.
The Rust fixtures are written in an ad-hoc line based dialect (`nodeProperty ...`,
`edgePoint ...`, `node a parent b`, `key = value`, quoted identifiers, implicit
nodes) that is not part of the ELK Text grammar; each test below keeps the *expected
values* of the Rust test but states the fixture in real `.elkt` syntax
(`ElkGraph.xtext`). Dialect-only behaviours (implicit node creation, duplicate label
identifiers as parse errors, `label` outside a block) have no counterpart; see
`Elk.Text.Loader`.

The last suite parses every `.elkt` file of the model corpus
(`external/elk-models`, or the directory in `$ELK_MODELS_DIR`).
-/
namespace Tests.Text

open Tests Elk.Text Elk.Graph Elk.Core.Options Elk.Core.Math Elk.Core.Util

/-! ### Helpers -/

def nodeByName (g : ElkGraph) (name : String) : Option NodeId :=
  (g.nodes.findIdx? (·.identifier == some name)).map (⟨·⟩)

def portByName (g : ElkGraph) (name : String) : Option PortId :=
  (g.ports.findIdx? (·.identifier == some name)).map (⟨·⟩)

def edgeByName (g : ElkGraph) (name : String) : Option EdgeId :=
  (g.edges.findIdx? (·.identifier == some name)).map (⟨·⟩)

def labelByName (g : ElkGraph) (name : String) : Option LabelId :=
  (g.labels.findIdx? (·.identifier == some name)).map (⟨·⟩)

def shapeName (g : ElkGraph) : ConnectableId → String
  | .node n => (g.node n).identifier.getD "?"
  | .port p => (g.port p).identifier.getD "?"

/-- Parses `text` and runs `k` on the result; a parse error is a test failure. -/
def withGraph (name text : String) (k : NodeId → ElkGraph → TestM Unit) : TestM Unit := do
  match ← parseElkt text with
  | .ok (root, g) => k root g
  | .error e => report s!"{name}: parse" false e

/-- Checks that parsing fails with a message containing `needle`. -/
def failsWith (name text needle : String) : TestM Unit := do
  match ← parseElkt text with
  | .ok _ => report name false "expected a parse error"
  | .error e => report name (needle.isEmpty || (e.splitOn needle).length > 1) s!"error was: {e}"

/-! ### Fixtures (real `.elkt` syntax) -/

/-- `org.eclipse.elk.alg.layered/images/example.elkt` (edges before the nodes they connect). -/
def layeredExample : String := r"
edge node1-> node2
edge node2-> node3
edge node3-> node4
edge node4-> node5
edge node5-> node6
edge node7-> node8
edge node8-> node4
edge node4-> node10
edge node10-> node11
edge node4-> node12
edge node4-> node13
edge node12-> node13
edge node2 -> node10

node node1
node node2
node node3
node node4
node node5
node node6
node node7
node node8
node node10
node node11
node node12
node node13
"

/-- `org.eclipse.elk.core/images/exampleBox.elkt`. -/
def boxExample : String := r"
algorithm: box
spacing.nodeNode: 2.0
//horizontal edges
	node node2{
		layout [ size: 30, 30 ]
	}
	node node3{
		layout [ size: 20, 20 ]
	}
	node node4{
		layout [ size: 19, 19 ]
	}
	node node5{
		layout [ size: 11, 11 ]
	}
	node node6
	node node7{
		layout [ size: 15, 15 ]
	}
	node node8
	node node10
	node node11{
		layout [ size: 18, 18 ]
	}
	node node13
"

/-- Counterpart of `elkt_parser_advanced_features.elkt`. -/
def advancedFeatures : String := r#"
algorithm: layered

node compound {
  layout [ size: 120, 80 ]
  elk.direction: RIGHT
  edgeRouting: ORTHOGONAL
  nodeLabels.placement: "[OUTSIDE, V_TOP, H_CENTER]"
  portLabels.placement: "[OUTSIDE, NEXT_TO_PORT_IF_POSSIBLE]"
  label "compound" { layout [ size: 40, 12 ] }
  node child { layout [ size: 60, 30 ] }
  edge e1: compound -> child {
    layout [ start: 10, 20 end: 80, 20 bends: 30,25 | 50,25 | 65,25 ]
    junctionPoints: "(30,25; 50,25)"
    label "head" {
      layout [ size: 20, 10 ]
      edgeLabels.placement: HEAD
    }
  }
}
"#

/-- Counterpart of `elkt_parser_nested_blocks.elkt`. -/
def nestedBlocks : String := r#"
algorithm: layered
elk.direction: DOWN
portLabels.placement: "[OUTSIDE, NEXT_TO_PORT_IF_POSSIBLE]"

node root {
  layout [ position: 10, 20 size: 220, 140 ]
  nodeLabels.placement: "[OUTSIDE, V_TOP, H_CENTER]"
  nodeLabels.padding: "[top=3,left=4,bottom=5,right=6]"

  node child_a {
    layout [ position: 30, 40 size: 50, 30 ]
    port p_out { layout [ position: 50, 12 size: 8, 8 ] ^port.side: EAST }
  }

  node child_b {
    layout [ position: 140, 40 size: 55, 30 ]
    port p_in { layout [ position: 0, 12 size: 8, 8 ] side: WEST }
  }

  edge e_nested: child_a.p_out -> child_b.p_in {
    layout [ start: 80, 55 end: 140, 55 bends: 100,55 | 120,60 | 130,58 ]
    edgeLabels.placement: CENTER
  }
}
"#

/-- Counterpart of `elkt_parser_hyperedge_and_labels.elkt`. -/
def hyperedgeAndLabels : String := r#"
algorithm: layered
elk.direction: RIGHT

node root {
  node a { layout [ size: 30, 20 ] }
  node b { layout [ size: 30, 20 ] }
  node c { layout [ size: 30, 20 ] }
  node d { layout [ size: 30, 20 ] }

  node owner {
    port p_out {
      layout [ position: 40, 12 size: 8, 8 ]
      side: EAST
      label "out" {
        layout [ size: 12, 6 ]
      }
    }
  }

  edge e_multi: a, b -> c, d {
    layout [ start: 10,10 end: 120,20 bends: 50,10 | 80,20 ]
  }
}
"#

/-- Counterpart of `elkt_parser_sections_and_label_ids.elkt`. -/
def sectionsAndLabelIds : String := r#"
algorithm: layered
elk.direction: RIGHT

node source {
  layout [ size: 40, 26 ]
  port p_source { layout [ size: 8, 8 ] ^port.side: EAST }
  label l_parent: "parent" {
    layout [ size: 12, 6 ]
    label l_child: "child" {
      layout [ size: 7, 3 ]
    }
  }
}

node target {
  layout [ size: 40, 26 ]
  port p_target { layout [ size: 8, 8 ] side: WEST }
}

edge e_sections: source.p_source -> target.p_target {
  layout [
    section s0 -> s1 [ outgoing: source.p_source start: 10,10 end: 40,10 ]
    section s1 [ incoming: target.p_target start: 40,10 end: 80,20 bends: 60,12 | 70,18 ]
  ]
}
"#

/-- Counterpart of `elkt_parser_section_chain_and_aliases.elkt`. -/
def sectionChain : String := r#"
node n_source { port p_source }
node n_target { port p_target }
edge e_chain: n_source.p_source -> n_target.p_target {
  layout [
    section s0 -> s1, s2 [ outgoing: n_source.p_source start: 10,10 end: 40,20 bends: 20,12 | 30,16 ]
    section s1 [ start: 40,20 end: 60,20 ]
    section s2 [ start: 40,24 end: 60,24 ]
    section s3 -> s0 [ incoming: n_target.p_target start: 70,22 end: 85,22 ]
  ]
}
"#

/-! ### Suites -/

def examples : Suite := suite "text.examples" do
  withGraph "layered example" layeredExample fun root g => do
    let kids := (g.node root).children
    check "nodes in loaded graph" (kids.size > 0)
    checkEq "12 nodes" kids.size 12
    checkEq "13 edges contained in the root" (g.node root).containedEdges.size 13
    let n4 := (nodeByName g "node4").getD ⟨0⟩
    checkEq "node4 outgoing edges" (g.node n4).outgoingEdges.size 4
    checkEq "node4 incoming edges" (g.node n4).incomingEdges.size 2
    let e0 := (g.node root).containedEdges[0]!
    checkEq "first edge source" (shapeName g (g.edge e0).sources[0]!) "node1"
    checkEq "first edge target" (shapeName g (g.edge e0).targets[0]!) "node2"
  withGraph "box example" boxExample fun root g => do
    let some node2 := nodeByName g "node2" | check "node2 exists" false
    checkFloat "node2 width" (g.node node2).width 30.0
    checkFloat "node2 height" (g.node node2).height 30.0
    let some node6 := nodeByName g "node6" | check "node6 exists" false
    checkFloat "node6 default width" (g.node node6).width 0.0
    checkEq "algorithm" (g.getNodeProp root Elk.Core.Options.CoreOptions.ALGORITHM) (some "box")
    checkFloat "spacing" ((g.getNodeProp root CoreOptions.SPACING_NODE_NODE).getD 0.0) 2.0

def advanced : Suite := suite "text.advanced" do
  withGraph "advanced" advancedFeatures fun root g => do
    let some compound := nodeByName g "compound" | check "compound exists" false
    checkEq "compound parent" (g.node compound).parent (some root)
    checkFloat "compound width" (g.node compound).width 120.0
    checkFloat "compound height" (g.node compound).height 80.0
    checkEq "direction" (g.getNodeProp compound CoreOptions.DIRECTION) (some Direction.right)
    checkEq "edge routing" (g.getNodeProp compound CoreOptions.EDGE_ROUTING) (some EdgeRouting.orthogonal)
    match g.getNodeProp compound CoreOptions.NODE_LABELS_PLACEMENT with
    | some s =>
      check "node label placement outside" (s.contains NodeLabelPlacement.outside)
      check "node label placement vTop" (s.contains NodeLabelPlacement.vTop)
      check "node label placement hCenter" (s.contains NodeLabelPlacement.hCenter)
    | none => check "node labels placement set" false
    match g.getNodeProp compound CoreOptions.PORT_LABELS_PLACEMENT with
    | some s =>
      check "port label placement outside" (s.contains PortLabelPlacement.outside)
      check "port label placement nextToPortIfPossible" (s.contains PortLabelPlacement.nextToPortIfPossible)
    | none => check "port labels placement set" false
    checkEq "compound label" ((g.node compound).labels.map fun l => (g.label l).text) #["compound"]
    let some e1 := edgeByName g "e1" | check "e1 exists" false
    checkEq "e1 contained in compound" (g.edge e1).containingNode (some compound)
    checkEq "one section" (g.edge e1).sections.size 1
    let sec := g.edgeSection (g.edge e1).sections[0]!
    checkFloat "start x" sec.startX 10.0
    checkFloat "start y" sec.startY 20.0
    checkFloat "end x" sec.endX 80.0
    checkFloat "end y" sec.endY 20.0
    checkEq "bend count" sec.bendPoints.size 3
    checkFloat "bend 2 x" sec.bendPoints[1]!.x 50.0
    match g.getEdgeProp e1 CoreOptions.JUNCTION_POINTS with
    | some jp => checkEq "junction point count" jp.size 2
    | none => check "junction points set" false
    let some lbl := (g.edge e1).labels[0]? | check "edge label exists" false
    checkEq "edge label text" (g.label lbl).text "head"
    checkFloat "edge label width" (g.label lbl).width 20.0
    checkEq "edge label placement" (g.getLabelProp lbl CoreOptions.EDGE_LABELS_PLACEMENT) (some EdgeLabelPlacement.head)

def nested : Suite := suite "text.nested" do
  withGraph "nested" nestedBlocks fun root g => do
    checkEq "graph direction" (g.getNodeProp root CoreOptions.DIRECTION) (some Direction.down)
    match g.getNodeProp root CoreOptions.PORT_LABELS_PLACEMENT with
    | some s =>
      check "graph port labels outside" (s.contains PortLabelPlacement.outside)
      check "graph port labels nextToPort" (s.contains PortLabelPlacement.nextToPortIfPossible)
    | none => check "graph port labels set" false
    let some r := nodeByName g "root" | check "root node exists" false
    checkFloat "root x" (g.node r).x 10.0
    checkFloat "root y" (g.node r).y 20.0
    checkFloat "root width" (g.node r).width 220.0
    checkFloat "root height" (g.node r).height 140.0
    let childIds := (g.node r).children.map fun c => (g.node c).identifier.getD ""
    check "child_a" (childIds.contains "child_a")
    check "child_b" (childIds.contains "child_b")
    match g.getNodeProp r CoreOptions.NODE_LABELS_PADDING with
    | some p => do checkFloat "padding top" p.top 3.0; checkFloat "padding right" p.right 6.0
    | none => check "node labels padding set" false
    let some pOut := portByName g "p_out" | check "p_out exists" false
    checkFloat "p_out x" (g.port pOut).x 50.0
    checkFloat "p_out y" (g.port pOut).y 12.0
    checkEq "p_out side" (g.getPortProp pOut CoreOptions.PORT_SIDE) (some PortSide.east)
    let some e := edgeByName g "e_nested" | check "nested edge exists" false
    checkEq "edge contained in root node" (g.edge e).containingNode (some r)
    checkEq "edge source" (shapeName g (g.edge e).sources[0]!) "p_out"
    checkEq "edge target" (shapeName g (g.edge e).targets[0]!) "p_in"
    let sec := g.edgeSection (g.edge e).sections[0]!
    checkFloat "start x" sec.startX 80.0
    checkFloat "start y" sec.startY 55.0
    checkFloat "end x" sec.endX 140.0
    checkFloat "end y" sec.endY 55.0
    checkEq "bends" sec.bendPoints.size 3
    checkEq "edge labels placement" (g.getEdgeProp e CoreOptions.EDGE_LABELS_PLACEMENT) (some EdgeLabelPlacement.center)

def hyperedge : Suite := suite "text.hyperedge" do
  withGraph "hyperedge" hyperedgeAndLabels fun _ g => do
    let some e := edgeByName g "e_multi" | check "hyperedge exists" false
    checkEq "sources" (g.edge e).sources.size 2
    checkEq "targets" (g.edge e).targets.size 2
    check "is hyperedge" (g.edge e).isHyperedge
    let sec := g.edgeSection (g.edge e).sections[0]!
    checkFloat "start x" sec.startX 10.0
    checkFloat "start y" sec.startY 10.0
    checkFloat "end x" sec.endX 120.0
    checkFloat "end y" sec.endY 20.0
    checkEq "bends" sec.bendPoints.size 2
    let some b := nodeByName g "b" | check "b exists" false
    check "b has the outgoing edge" ((g.node b).outgoingEdges.contains e)
    let some p := portByName g "p_out" | check "p_out exists" false
    checkEq "port side" (g.getPortProp p CoreOptions.PORT_SIDE) (some PortSide.east)
    checkEq "port labels" (g.port p).labels.size 1
    let l := g.label (g.port p).labels[0]!
    checkEq "label text" l.text "out"
    checkFloat "label width" l.width 12.0
    checkFloat "label height" l.height 6.0
    checkEq "label parent" l.parent (some (ElementId.port p))

def sections : Suite := suite "text.sections" do
  withGraph "section links and label ids" sectionsAndLabelIds fun _ g => do
    let some lp := labelByName g "l_parent" | check "l_parent exists" false
    let some lc := labelByName g "l_child" | check "l_child exists" false
    checkEq "parent text" (g.label lp).text "parent"
    checkFloat "parent width" (g.label lp).width 12.0
    checkFloat "parent height" (g.label lp).height 6.0
    checkEq "child text" (g.label lc).text "child"
    checkFloat "child width" (g.label lc).width 7.0
    checkFloat "child height" (g.label lc).height 3.0
    checkEq "child label nested in parent label" (g.label lc).parent (some (ElementId.label lp))
    let some e := edgeByName g "e_sections" | check "edge exists" false
    let secs := (g.edge e).sections
    checkEq "section count" secs.size 2
    let find (name : String) : Option SectionId := secs.find? fun s => (g.edgeSection s).identifier == some name
    let some s0 := find "s0" | check "s0 exists" false
    let some s1 := find "s1" | check "s1 exists" false
    checkEq "s0 outgoing sections" (g.edgeSection s0).outgoingSections.size 1
    checkEq "s1 incoming sections" (g.edgeSection s1).incomingSections.size 1
    checkEq "s1 incoming is s0" (g.edgeSection s1).incomingSections[0]! s0
    checkEq "s0 outgoing shape" ((g.edgeSection s0).outgoingShape.map (shapeName g)) (some "p_source")
    checkEq "s1 incoming shape" ((g.edgeSection s1).incomingShape.map (shapeName g)) (some "p_target")
    checkEq "s1 bends" (g.edgeSection s1).bendPoints.size 2
  withGraph "section chain" sectionChain fun _ g => do
    let some e := edgeByName g "e_chain" | check "edge exists" false
    let secs := (g.edge e).sections
    checkEq "four sections" secs.size 4
    let s0 := secs[0]!
    let s1 := secs[1]!
    let s2 := secs[2]!
    let s3 := secs[3]!
    checkEq "s0 -> s1, s2" (g.edgeSection s0).outgoingSections #[s1, s2]
    checkEq "s3 -> s0" (g.edgeSection s3).outgoingSections #[s0]
    checkEq "s0 incoming from s3" (g.edgeSection s0).incomingSections #[s3]
    checkEq "s1 incoming" (g.edgeSection s1).incomingSections #[s0]
    checkEq "s2 incoming" (g.edgeSection s2).incomingSections #[s0]
    checkFloat "s2 start y" (g.edgeSection s2).startY 24.0

def failures : Suite := suite "text.failures" do
  -- fail_when_section_link_target_is_missing
  failsWith "section link target missing" r#"
node n_source { port p_source }
node n_target { port p_target }
edge e0: n_source.p_source -> n_target.p_target {
  layout [ section s0 -> s_missing [ outgoing: n_source.p_source incoming: n_target.p_target ] ]
}"# "Couldn't resolve reference to ElkEdgeSection 's_missing'"
  -- fail_when_section_shape_reference_is_missing
  failsWith "section shape missing" r#"
node n_source { port p_source }
node n_target { port p_target }
edge e0: n_source.p_source -> n_target.p_target {
  layout [ section s0 [ outgoing: n_source.p_missing incoming: n_target.p_target start: 10,10 end: 20,20 ] ]
}"# "Couldn't resolve reference to ElkConnectableShape 'n_source.p_missing'"
  -- fail_when_section_link_target_is_empty
  failsWith "section link empty target" r#"
node n0
node n1
edge e0: n0 -> n1 {
  layout [ section s0 -> [ start: 0,0 end: 10,0 ] ]
}"# "mismatched input '['"
  -- fail_on_unknown_edge_reference: edge endpoints are cross references
  failsWith "unknown edge endpoint" "node n1\nedge n1 -> n2" "Couldn't resolve reference to ElkConnectableShape 'n2'"
  failsWith "error position" "node n1\nedge n1 -> n2" "2:12"
  -- label_without_parent: a root-level label is legal, an unnamed text is not
  failsWith "label needs a string" "label l_orphan: orphan" "expecting RULE_STRING"
  -- syntax errors
  failsWith "properties after elements" "node a\ndirection: DOWN" "mismatched input 'direction'"
  failsWith "unterminated block" "node a {" "expecting '}'"
  failsWith "stray closing brace" "node a }" "mismatched input '}'"
  failsWith "unknown character" "node a @" "mismatched input '@'"
  failsWith "unterminated string" "node a { label \"x }" "unterminated string"
  failsWith "unterminated comment" "node a /* x" "unterminated comment"
  failsWith "keyword as identifier" "node node" "expecting RULE_ID"
  failsWith "duplicate layout item" "node a { layout [ size: 1,2 size: 3,4 ] }" "mismatched input 'size'"
  failsWith "whitespace inside property key" "org .eclipse: 1" "expecting ':'"
  failsWith "missing arrow" "node a node b edge a b" "expecting '->'"
  failsWith "bad number" "node a { layout [ size: x, 2 ] }" "expecting RULE_SIGNED_INT or RULE_FLOAT"

def lexical : Suite := suite "text.lexical" do
  -- comments, escapes of keywords, numbers
  withGraph "caret and comments" r#"
// line comment
/* block
   comment */
graph ^g
node ^node { layout [ position: -1.5, +2 size: 1e2, 2.5E-1 ] }
node ^size
"# fun root g => do
    checkEq "graph identifier" (g.node root).identifier (some "g")
    let some n := nodeByName g "node" | check "escaped keyword identifier" false
    checkFloat "x" (g.node n).x (-1.5)
    checkFloat "y" (g.node n).y 2.0
    checkFloat "width" (g.node n).width 100.0
    checkFloat "height" (g.node n).height 0.25
    check "second node" (nodeByName g "size").isSome
  -- layout items in either order, empty layout
  withGraph "layout order" "node a { layout [ size: 3,4 position: 1,2 ] }\nnode b { layout [ ] }" fun _ g => do
    let some a := nodeByName g "a" | check "a exists" false
    checkFloat "a x" (g.node a).x 1.0
    checkFloat "a height" (g.node a).height 4.0
  -- label text escapes
  withGraph "label escapes" "node a { label \"x\\ny\\t\\\"q\\\" \\u0041\" label 'single' }" fun _ g => do
    let some a := nodeByName g "a" | check "a exists" false
    let texts := (g.node a).labels.map fun l => (g.label l).text
    checkEq "escaped text" texts #["x\ny\t\"q\" A", "single"]
  -- the root can carry layout, properties and labels
  withGraph "root layout" "layout [ size: 5, 6 ]\ndirection: LEFT\nlabel \"title\"\nnode a" fun root g => do
    checkFloat "root width" (g.node root).width 5.0
    checkEq "root direction" (g.getNodeProp root CoreOptions.DIRECTION) (some Direction.left)
    checkEq "root label" (g.node root).labels.size 1
  -- empty input is an empty graph
  withGraph "empty" "" fun root g => do
    checkEq "no children" (g.node root).children.size 0
    checkEq "one node" g.nodes.size 1

def properties : Suite := suite "text.properties" do
  withGraph "property values" r#"
org.eclipse.elk.direction: DOWN
elk.edgeRouting: "ORTHOGONAL"
spacing.nodeNode: 17
org.eclipse.elk.padding: "[top=1,left=2,bottom=3,right=4]"
unknown.option: 5
elk.direction: NOT_A_DIRECTION
node n {
  elk.^elk.direction: 'UP'
  priority: null
}
"# fun root g => do
    checkEq "qualified key" (g.getNodeProp root CoreOptions.DIRECTION) (some Direction.down)
    checkEq "string value" (g.getNodeProp root CoreOptions.EDGE_ROUTING) (some EdgeRouting.orthogonal)
    checkFloat "integer literal as double" ((g.getNodeProp root CoreOptions.SPACING_NODE_NODE).getD 0.0) 17.0
    match g.getNodeProp root CoreOptions.PADDING with
    | some p => do checkFloat "padding left" p.left 2.0; checkFloat "padding bottom" p.bottom 3.0
    | none => check "padding set" false
    -- unknown options and unparsable values are ignored (the later duplicate does not override)
    checkEq "root property count" (g.node root).props.size 4
    let some n := nodeByName g "n" | check "n exists" false
    checkEq "caret key and single quoted value" (g.getNodeProp n CoreOptions.DIRECTION) (some Direction.up)
    checkEq "null drops the entry" (g.node n).props.size 1
  -- keepUnknownOptions stores proxies under the raw key
  match ← parseElkt "unknown.option: 5\ndirection: NOT_A_DIRECTION" { keepUnknownOptions := true } with
  | .ok (root, g) =>
    checkEq "kept unknown" (g.node root).props.size 2
    check "proxy value" (match (g.node root).props.getRawById? "unknown.option" with
      | some (.proxy "5") => true
      | _ => false)
  | .error e => report "keepUnknownOptions" false e
  -- duplicate keys: last one wins
  withGraph "duplicate key" "elk.direction: DOWN\ndirection: UP" fun root g => do
    checkEq "last wins" (g.getNodeProp root CoreOptions.DIRECTION) (some Direction.up)
    checkEq "one entry" (g.node root).props.size 1

def scoping : Suite := suite "text.scoping" do
  -- relative references inside nested nodes, forward references and root ports
  withGraph "scoping" r#"
graph G
node outer {
  port op
  node inner { port ip }
  node other
  edge outer.op -> inner.ip
  edge inner -> other
  edge inner.ip -> other
}
node last
edge outer.inner -> last
edge e_back: last -> G
"# fun root g => do
    checkEq "root name" (g.node root).identifier (some "G")
    let some outer := nodeByName g "outer" | check "outer exists" false
    check "outer contains edges" ((g.node outer).containedEdges.size == 3)
    check "root contains edges" ((g.node root).containedEdges.size == 2)
    let some inner := nodeByName g "inner" | check "inner exists" false
    let some op := portByName g "op" | check "op exists" false
    let some ip := portByName g "ip" | check "ip exists" false
    let e0 := (g.node outer).containedEdges[0]!
    checkEq "outer.op source" (g.edge e0).sources #[ConnectableId.port op]
    checkEq "inner.ip target" (g.edge e0).targets #[ConnectableId.port ip]
    let e1 := (g.node outer).containedEdges[1]!
    checkEq "relative node source" (g.edge e1).sources #[ConnectableId.node inner]
    let e3 := (g.node root).containedEdges[0]!
    checkEq "qualified name through the hierarchy" (g.edge e3).sources #[ConnectableId.node inner]
    let some bk := edgeByName g "e_back" | check "e_back exists" false
    checkEq "reference to the named root" (g.edge bk).targets #[ConnectableId.node root]
    checkEq "incoming recorded on the port" (g.port ip).incomingEdges.size 1
    checkEq "outgoing recorded on the port" (g.port ip).outgoingEdges.size 1
  -- the same names in different scopes resolve to the innermost one
  withGraph "shadowing" r#"
node a { port p }
node b {
  node a { port p }
  edge a.p -> a.p
}
edge a.p -> b.a.p
"# fun _ g => do
    let some b := nodeByName g "b" | check "b exists" false
    let inner := (g.node b).children[0]!
    let innerPort := (g.node inner).ports[0]!
    let e := (g.node b).containedEdges[0]!
    checkEq "inner a.p" (g.edge e).sources #[ConnectableId.port innerPort]
    let rootEdge := g.edge ⟨1⟩
    checkEq "outer a.p" (rootEdge.sources.size, rootEdge.targets) (1, #[ConnectableId.port innerPort])
    check "outer source is the outer port" (rootEdge.sources != #[ConnectableId.port innerPort])
  -- updateContainment option re-homes edges
  match ← parseElkt "node a\nnode b\nnode p { node c node d }\nedge c -> d" {} with
  | .ok _ => report "unresolved c" false "expected an error"
  | .error _ => check "unqualified child is not visible from the root" true
  match ← parseElkt "node p { node c node d }\nedge p.c -> p.d" { updateContainment := true } with
  | .ok (_, g) =>
    let some p := nodeByName g "p" | check "p exists" false
    checkEq "edge moved into p" (g.node p).containedEdges.size 1
  | .error e => report "updateContainment" false e
  match ← parseElkt "node p { node c node d }\nedge p.c -> p.d" {} with
  | .ok (root, g) => checkEq "edge stays in the root" (g.node root).containedEdges.size 1
  | .error e => report "declared containment" false e

def defaults : Suite := suite "text.defaults" do
  withGraph "applyDefaults" "node a { port p label \"text\" }\nnode b { layout [ size: 10, 0 ] }" fun root g => do
    let g := applyDefaults g root
    let some a := nodeByName g "a" | check "a exists" false
    checkFloat "node width" (g.node a).width 30.0
    let some b := nodeByName g "b" | check "b exists" false
    checkFloat "kept width" (g.node b).width 10.0
    checkFloat "default height" (g.node b).height 30.0
    let some p := portByName g "p" | check "p exists" false
    checkFloat "port size" (g.port p).width 5.0
    let l := g.label (g.node a).labels[0]!
    checkFloat "label width" l.width 36.0
    checkFloat "label height" l.height 16.0

/-! ### Corpus -/

/-- Directory of the model corpus. -/
def corpusDir : IO System.FilePath := do
  match ← IO.getEnv "ELK_MODELS_DIR" with
  | some d => return d
  | none => return "external/elk-models"

/-- Parses every `.elkt` file below `external/elk-models` (898 in the pinned corpus); also
exports each graph to JSON as a consistency check of the arena. -/
def corpus : Suite := suite "text.corpus" do
  let dir ← corpusDir
  let files ← if ← dir.isDir then
      let all ← System.FilePath.walkDir dir
      pure (all.filter fun f => f.extension == some "elkt")
    else pure #[]
  if files.isEmpty then
    IO.println s!"text.corpus: no .elkt files below {dir} (submodule not checked out?); skipping"
  else
    let mut ok := 0
    let mut failed : Array String := #[]
    let mut edges := 0
    let mut nodes := 0
    let mut misplaced := 0
    for f in files do
      let text ← IO.FS.readFile f
      match ← parseElkt text with
      | .ok (root, g) =>
        ok := ok + 1
        nodes := nodes + g.nodes.size
        edges := edges + g.edges.size
        for i in [0:g.edges.size] do
          let e : EdgeId := ⟨i⟩
          if ElkGraphUtil.findBestEdgeContainment g e != (g.edge e).containingNode then
            misplaced := misplaced + 1
        let json ← (try
            let s ← Elk.Json.exportGraph g root
            pure (if s.isEmpty then some "empty JSON" else none)
          catch e => pure (some s!"JSON export failed: {e}"))
        if let some err := json then
          failed := failed.push s!"{f}: {err}"
      | .error e => failed := failed.push s!"{f}: {e}"
    for msg in failed do
      IO.println s!"text.corpus FAIL {msg}"
    IO.println s!"text.corpus: {ok}/{files.size} files parsed, {failed.size} failures, {nodes} nodes, {edges} edges, {misplaced} edges not declared in their best container"
    checkEq "corpus size" files.size 898
    checkEq "corpus parse failures" failed.size 0

/-! ### Cross-check against the JSON twins of the Ptolemy models -/

open Elk.Json in
/-- Compares the arena of a parsed `.elkt` with the JSON document of the same model
(`realworld/ptolemy/**/X.json` next to `X.elkt`): ids, sizes, labels, ports,
hierarchy and edge end points (the JSON twins carry no positions). Returns the first mismatches. -/
partial def compareNode (g : ElkGraph) (n : NodeId) (j : Value) (path : String) : Array String := Id.run do
  let mut errs : Array String := #[]
  let nd := g.node n
  let str (v : Value) (k : String) : Option String := (v.get? k).bind (·.getStr?)
  let flt (v : Value) (k : String) : Float := ((v.get? k).bind (·.getFloat?)).getD 0.0
  let arr (v : Value) (k : String) : Array Value := ((v.get? k).bind (·.getArr?)).getD #[]
  if str j "id" != nd.identifier then
    errs := errs.push s!"{path}: id {repr (str j "id")} vs {repr nd.identifier}"
  for (k, a, b) in [("width", flt j "width", nd.width), ("height", flt j "height", nd.height)] do
    if a != b then errs := errs.push s!"{path}: {k} {a} vs {b}"
  let cmpLabels (owner : String) (labels : Array LabelId) (js : Array Value) : Array String := Id.run do
    let mut e : Array String := #[]
    if labels.size != js.size then
      return #[s!"{owner}: {labels.size} labels vs {js.size}"]
    for h : i in [0:labels.size] do
      let l := g.label labels[i]
      let jl := js[i]!
      if str jl "text" != some l.text || str jl "id" != l.identifier || flt jl "width" != l.width || flt jl "height" != l.height then
        e := e.push s!"{owner}: label {i} differs"
    return e
  errs := errs ++ cmpLabels path nd.labels (arr j "labels")
  let jports := arr j "ports"
  if jports.size != nd.ports.size then
    errs := errs.push s!"{path}: {nd.ports.size} ports vs {jports.size}"
  else
    for h : i in [0:jports.size] do
      let p := g.port nd.ports[i]!
      let jp := jports[i]
      if str jp "id" != p.identifier || flt jp "width" != p.width || flt jp "height" != p.height then
        errs := errs.push s!"{path}: port {i} differs"
      errs := errs ++ cmpLabels s!"{path}/{i}" p.labels (arr jp "labels")
  let jkids := arr j "children"
  if jkids.size != nd.children.size then
    errs := errs.push s!"{path}: {nd.children.size} children vs {jkids.size}"
  else
    for h : i in [0:jkids.size] do
      errs := errs ++ compareNode g nd.children[i]! jkids[i] s!"{path}/{i}"
  let jedges := arr j "edges"
  if jedges.size != nd.containedEdges.size then
    errs := errs.push s!"{path}: {nd.containedEdges.size} edges vs {jedges.size}"
  else
    for h : i in [0:jedges.size] do
      let e := g.edge nd.containedEdges[i]!
      let je := jedges[i]
      let names (v : Value) (k : String) : Array String := (arr v k).filterMap (·.getStr?)
      if str je "id" != e.identifier || names je "sources" != e.sources.map (shapeName g)
         || names je "targets" != e.targets.map (shapeName g) then
        errs := errs.push s!"{path}: edge {i} differs"
      errs := errs ++ cmpLabels s!"{path}/e{i}" e.labels (arr je "labels")
  return errs

def ptolemyTwins : Suite := suite "text.ptolemyTwins" do
  let dir ← corpusDir
  let base := dir / "realworld" / "ptolemy"
  let files ← if ← base.isDir then
      let all ← System.FilePath.walkDir base
      pure (all.filter fun f => f.extension == some "elkt")
    else pure #[]
  if files.isEmpty then
    IO.println s!"text.ptolemyTwins: no Ptolemy models below {base}; skipping"
  else
    let mut compared := 0
    let mut bad : Array String := #[]
    for f in files do
      let jsonFile := f.withExtension "json"
      if !(← jsonFile.pathExists) then continue
      let text ← IO.FS.readFile f
      let jsonText ← IO.FS.readFile jsonFile
      match Elk.Json.parse jsonText, ← parseElkt text with
      | .ok j, .ok (root, g) =>
        compared := compared + 1
        let errs := compareNode g root j "root"
        if !errs.isEmpty then bad := bad.push s!"{f}: {errs[0]!} (+{errs.size - 1})"
      | _, _ => bad := bad.push s!"{f}: could not parse"
    for b in bad.extract 0 10 do IO.println s!"text.ptolemyTwins MISMATCH {b}"
    IO.println s!"text.ptolemyTwins: compared {compared} models, {bad.size} mismatches"
    check "compared models" (compared > 0)
    checkEq "mismatching models" bad.size 0

def suites : Array Tests.Suite :=
  #[examples, advanced, nested, hyperedge, sections, failures, lexical, properties, scoping, defaults, corpus, ptolemyTwins]

end Tests.Text
