import Tests.Framework
import Elk.Api
import Elk.Alg.Layered.Graph.Transform
/-!
# Tests for `ElkGraphImporter`, `ElkGraphTransformer` and `LGraphAdapters`

The graphs are imported from JSON strings (`Elk.Json.importGraph`) and then into the layered arena
with `ElkGraphImporter.importGraph`. Expected values are derived by hand from elk-rs
`elk_graph_importer.rs` / `l_graph_adapters.rs` ("hand: …" in the check names). Ported elk-rs
tests: `intermediate/elk_graph_importer_padding_test.rs`
(`importer_adds_inside_node_label_padding_to_graph_padding`) and
`intermediate/end_label_graph_properties_test.rs` (`graph_properties_include_end_labels`).

Arena ids follow the creation order of the importer (nodes in child order, ports with their node,
then the end ports created while importing edges).
-/
namespace Tests.Layered.Import

open Tests Elk Elk.Graph Elk.Core.Math Elk.Core.Options Elk.Core.Util Elk.Core.Util.Adapters
open Elk.Alg.Layered.Graph Elk.Alg.Layered.Options Elk.Alg.Layered.Graph.Transform

/-! ## Helpers -/

/-- Result of an import: the ElkGraph after the import, the arena, the root ids and the edges. -/
structure Imported where
  g : ElkGraph
  a : LGraphArena
  root : NodeId
  lgraph : LGraphId
  ledges : OriginStore

/-- Lenient JSON parse. -/
def parseJson (text : String) : IO Elk.Json.Value := do
  match Elk.Json.parse text (lenient := true) with
  | .ok v => pure v
  | .error e => throw (IO.userError s!"parse failed: {e.message}")

/-- JSON → ElkGraph. -/
def elkGraphOf (text : String) : IO (NodeId × ElkGraph) := do
  Elk.Api.ensureInitialized
  let (root, _, g) ← Elk.Json.importGraph (← parseJson text)
  return (root, g)

/-- JSON → ElkGraph → layered arena. -/
def importText (text : String) : IO Imported := do
  let (root, g) ← elkGraphOf text
  let imp ← ElkGraphImporter.new
  let ((lgraph, a), g) ← LImportM.run (imp.importGraph root) {} g
  return { g, a, root, lgraph, ledges := ← imp.ledges.get }

/-- Imports the node with identifier `ident` (a compound child) of the graph `text`. -/
def importChildText (text : String) (ident : String) : IO Imported := do
  let (_, g) ← elkGraphOf text
  let node : NodeId := ⟨(g.nodes.findIdx? (·.identifier == some ident)).getD 0⟩
  let imp ← ElkGraphImporter.new
  let ((lgraph, a), g) ← LImportM.run (imp.importGraph node) {} g
  return { g, a, root := node, lgraph, ledges := ← imp.ledges.get }

/-- The message of the exception thrown by the import, `none` on success. -/
def importError (text : String) : IO (Option String) := do
  try
    let _ ← importText text
    return none
  catch e => return some (toString e)

/-- ElkGraph node by identifier. -/
def nodeNamed (g : ElkGraph) (ident : String) : NodeId := ⟨(g.nodes.findIdx? (·.identifier == some ident)).getD 0⟩
/-- ElkGraph port by identifier. -/
def portNamed (g : ElkGraph) (ident : String) : PortId := ⟨(g.ports.findIdx? (·.identifier == some ident)).getD 0⟩
/-- ElkGraph edge by identifier. -/
def edgeNamed (g : ElkGraph) (ident : String) : EdgeId := ⟨(g.edges.findIdx? (·.identifier == some ident)).getD 0⟩

def checkVec (name : String) (actual expected : KVector) : TestM Unit := do
  checkFloat s!"{name} x" actual.x expected.x
  checkFloat s!"{name} y" actual.y expected.y

def checkPadding (name : String) (p : ElkPadding) (top right bottom left : Float) : TestM Unit := do
  checkFloat s!"{name} top" p.top top
  checkFloat s!"{name} right" p.right right
  checkFloat s!"{name} bottom" p.bottom bottom
  checkFloat s!"{name} left" p.left left

def n (i : Nat) : LNodeId := ⟨i⟩
def p (i : Nat) : LPortId := ⟨i⟩
def e (i : Nat) : LEdgeId := ⟨i⟩
def l (i : Nat) : LLabelId := ⟨i⟩

/-! ## Flat import -/

/-- Root with padding, nodes `a` (EAST port `pa`, labels `A` and an empty one), `b` (`FIXED_SIDE`,
port `pb` without side, port label), comment box `c`, `NO_LAYOUT` node `n`; edges `e1` (`pa → pb`,
HEAD + center labels), `e2` (`a → b`, node end points), `e3` (`a → n`, itself `NO_LAYOUT`, skipped;
without that option ELK Java fails on the untransformed end `n`, see `scopeErrors`). -/
def flatJson : String := "{
  \"id\": \"root\",
  \"layoutOptions\": { \"elk.padding\": \"[top=1,left=2,bottom=3,right=4]\" },
  \"children\": [
    { \"id\": \"a\", \"x\": 1, \"y\": 2, \"width\": 30, \"height\": 20,
      \"labels\": [ { \"id\": \"la\", \"text\": \"A\", \"width\": 5, \"height\": 6 }, { \"id\": \"le\", \"text\": \"\" } ],
      \"ports\": [ { \"id\": \"pa\", \"x\": 30, \"y\": 5, \"width\": 4, \"height\": 4,
                     \"layoutOptions\": { \"elk.port.side\": \"EAST\" } } ] },
    { \"id\": \"b\", \"width\": 30, \"height\": 20, \"layoutOptions\": { \"elk.portConstraints\": \"FIXED_SIDE\" },
      \"ports\": [ { \"id\": \"pb\", \"x\": -4, \"y\": 5, \"width\": 4, \"height\": 4,
                     \"labels\": [ { \"text\": \"pl\", \"width\": 3, \"height\": 2 } ] } ] },
    { \"id\": \"c\", \"width\": 10, \"height\": 10, \"layoutOptions\": { \"elk.commentBox\": \"true\" } },
    { \"id\": \"n\", \"width\": 10, \"height\": 10, \"layoutOptions\": { \"elk.noLayout\": \"true\" } }
  ],
  \"edges\": [
    { \"id\": \"e1\", \"sources\": [\"pa\"], \"targets\": [\"pb\"],
      \"labels\": [ { \"text\": \"head\", \"layoutOptions\": { \"elk.edgeLabels.placement\": \"HEAD\" } }, { \"text\": \"mid\" } ] },
    { \"id\": \"e2\", \"sources\": [\"a\"], \"targets\": [\"b\"] },
    { \"id\": \"e3\", \"sources\": [\"a\"], \"targets\": [\"n\"], \"layoutOptions\": { \"elk.noLayout\": \"true\" } }
  ]
}"

def flatImport : Suite := suite "layered.import.flat" do
  let r ← importText flatJson
  let a := r.a
  let gr := a.graph r.lgraph
  checkEq "graph count" a.graphs.size 1
  checkEq "hand: nodes a, b, c (n is NO_LAYOUT)" a.nodes.size 3
  checkEq "layerless node order" gr.layerlessNodes #[n 0, n 1, n 2]
  checkEq "hand: ports pa, pb + two edge end ports" a.ports.size 4
  checkEq "hand: edges e1, e2 (e3 skipped)" a.edges.size 2
  checkEq "hand: labels A, pl, head, mid (empty label skipped)" a.labels.size 4
  checkEqR "graph origin" gr.internal.origin (some (.elkNode r.root))
  checkPadding "hand: padding = PADDING + no inside labels" gr.padding 1.0 4.0 3.0 2.0
  check "graph options copied" (gr.props.has CoreOptions.PADDING)
  let gp := gr.internal.graphProperties
  check "hand: NON_FREE_PORTS (b is FIXED_SIDE)" (gp.contains .nonFreePorts)
  check "hand: COMMENTS (c)" (gp.contains .comments)
  check "hand: END_LABELS (head)" (gp.contains .endLabels)
  check "hand: CENTER_LABELS (mid)" (gp.contains .centerLabels)
  check "hand: no EXTERNAL_PORTS" (!gp.contains .externalPorts)
  check "hand: no SELF_LOOPS / HYPEREDGES" (!gp.contains .selfLoops && !gp.contains .hyperedges)
  checkEq "MAX_MODEL_ORDER_NODES (no model order)" gr.internal.maxModelOrderNodes 0
  -- node a
  let na := a.node (n 0)
  checkEqR "a origin" na.internal.origin (some (.elkNode (nodeNamed r.g "a")))
  checkVec "a position" na.position ⟨1.0, 2.0⟩
  checkVec "a size" na.size ⟨30.0, 20.0⟩
  checkEq "hand: a PORT_CONSTRAINTS UNDEFINED → FREE" (na.props.getD CoreOptions.PORT_CONSTRAINTS .undefined) .free
  checkEq "a ports (pa, then e2's source port)" na.ports #[p 0, p 2]
  checkEq "a labels (empty one skipped)" na.labels #[l 0]
  checkEq "label text" (a.label (l 0)).text "A"
  checkVec "label size" (a.label (l 0)).size ⟨5.0, 6.0⟩
  check "a not compound" (!na.internal.compoundNode)
  -- port pa
  let ppa := a.port (p 0)
  checkEqR "pa origin" ppa.internal.origin (some (.elkPort (portNamed r.g "pa")))
  checkEq "pa side" ppa.side .east
  checkVec "pa position" ppa.position ⟨30.0, 5.0⟩
  checkVec "hand: pa anchor (FREE: port center)" ppa.anchor ⟨2.0, 2.0⟩
  check "pa no inside connections" (!ppa.internal.insideConnections)
  -- port pb: side computed from the position (FIXED_SIDE)
  let ppb := a.port (p 1)
  checkEq "hand: pb side WEST (x < 0)" ppb.side .west
  checkVec "hand: pb anchor (0, h/2)" ppb.anchor ⟨0.0, 2.0⟩
  checkFloat "hand: pb PORT_BORDER_OFFSET -(x + w)" (ppb.props.getD CoreOptions.PORT_BORDER_OFFSET 99.0) 0.0
  checkEq "pb labels" ppb.labels #[l 1]
  checkEq "hand: b PORT_CONSTRAINTS stays FIXED_SIDE" ((a.node (n 1)).props.getD CoreOptions.PORT_CONSTRAINTS .undefined) .fixedSide
  -- edges
  let e1 := a.edge (e 0)
  checkEq "e1 source" e1.source (some (p 0))
  checkEq "e1 target" e1.target (some (p 1))
  checkEqR "e1 origin" e1.internal.origin (some (.elkEdge (edgeNamed r.g "e1")))
  checkEq "e1 NO_LAYOUT set to false" (e1.props.get? CoreOptions.NO_LAYOUT) (some false)
  checkEq "e1 labels" e1.labels #[l 2, l 3]
  checkEq "mid label placement stored CENTER" ((a.label (l 3)).props.get? CoreOptions.EDGE_LABELS_PLACEMENT) (some .center)
  checkNone "e1 coordinate origin (siblings)" e1.internal.coordinateSystemOrigin
  let e2 := a.edge (e 1)
  checkEq "hand: e2 source = new EAST port of a" e2.source (some (p 2))
  checkEq "hand: e2 target = new port of b" e2.target (some (p 3))
  checkEq "hand: e2 source side EAST (RIGHT)" (a.port (p 2)).side .east
  checkEq "hand: e2 target side WEST" (a.port (p 3)).side .west
  checkEq "ledges e1" (r.ledges.get? (edgeNamed r.g "e1")) (some (e 0))
  checkEq "ledges e2" (r.ledges.get? (edgeNamed r.g "e2")) (some (e 1))
  checkEq "ledges e3 absent" (r.ledges.get? (edgeNamed r.g "e3")) none
  -- comment box
  checkEqR "c is the third node" (a.node (n 2)).internal.origin (some (.elkNode (nodeNamed r.g "c")))

/-! ## External ports and model order -/

/-- Root `100 × 80` with `FIXED_SIDE` ports `rp1` (left of the node, edge to `x`), `rp2` (EAST,
border offset 2, edge from `x`), `rp3` (above, edgeless); model order strategy set; `y` opts out. -/
def externalJson : String := "{
  \"id\": \"root\", \"width\": 100, \"height\": 80,
  \"layoutOptions\": { \"elk.portConstraints\": \"FIXED_SIDE\",
                       \"org.eclipse.elk.alg.layered.considerModelOrder.strategy\": \"NODES_AND_EDGES\" },
  \"ports\": [
    { \"id\": \"rp1\", \"x\": -5, \"y\": 30, \"width\": 5, \"height\": 5 },
    { \"id\": \"rp2\", \"x\": 100, \"y\": 10, \"width\": 5, \"height\": 5,
      \"layoutOptions\": { \"elk.port.side\": \"EAST\", \"elk.port.borderOffset\": \"2\" } },
    { \"id\": \"rp3\", \"x\": 20, \"y\": -5, \"width\": 5, \"height\": 5 }
  ],
  \"children\": [
    { \"id\": \"x\", \"width\": 10, \"height\": 10 },
    { \"id\": \"y\", \"width\": 10, \"height\": 10,
      \"layoutOptions\": { \"org.eclipse.elk.alg.layered.considerModelOrder.noModelOrder\": \"true\" } }
  ],
  \"edges\": [
    { \"id\": \"in\", \"sources\": [\"rp1\"], \"targets\": [\"x\"] },
    { \"id\": \"out\", \"sources\": [\"x\"], \"targets\": [\"rp2\"] }
  ]
}"

def externalPorts : Suite := suite "layered.import.externalPorts" do
  -- at the layout root, Java's `transformExternalPort` reads the label spacings through
  -- `elkgraph.getParent()` and fails (agent DIS); the checks below import the same graph as a child
  checkEq "external ports of the layout root: Java's NullPointerException" (← importError externalJson)
    (some ("java.lang.NullPointerException: Cannot invoke \"org.eclipse.elk.graph.ElkNode.getProperty(" ++
      "org.eclipse.elk.graph.properties.IProperty)\" because the return value of " ++
      "\"org.eclipse.elk.graph.ElkNode.getParent()\" is null"))
  let r ← importChildText s!"\{\"id\": \"top\", \"children\": [{externalJson}]}" "root"
  let a := r.a
  let gr := a.graph r.lgraph
  check "hand: EXTERNAL_PORTS" (gr.internal.graphProperties.contains .externalPorts)
  check "hand: no HYPEREDGES" (!gr.internal.graphProperties.contains .hyperedges)
  checkPadding "hand: default padding 12" gr.padding 12.0 12.0 12.0 12.0
  checkEq "hand: dummies rp1, rp2, rp3, then x, y" gr.layerlessNodes #[n 0, n 1, n 2, n 3, n 4]
  -- ensureDefinedPortSide on the ElkGraph
  checkEq "hand: rp1 PORT_SIDE WEST (calcPortSide)" ((r.g.port (portNamed r.g "rp1")).props.get? CoreOptions.PORT_SIDE) (some .west)
  checkEq "hand: rp3 PORT_SIDE NORTH (calcPortSide)" ((r.g.port (portNamed r.g "rp3")).props.get? CoreOptions.PORT_SIDE) (some .north)
  checkFloat "hand: rp1 inferred PORT_BORDER_OFFSET -(x + w)"
    ((r.g.port (portNamed r.g "rp1")).props.getD CoreOptions.PORT_BORDER_OFFSET 99.0) 0.0
  -- dummy of rp1 (WEST)
  let d1 := a.node (n 0)
  checkEq "rp1 dummy type" d1.type .externalPort
  checkEqR "rp1 dummy origin" d1.internal.origin (some (.elkPort (portNamed r.g "rp1")))
  checkEq "rp1 extPortSide" d1.internal.extPortSide .west
  checkVec "rp1 extPortSize" d1.internal.extPortSize ⟨5.0, 5.0⟩
  checkEq "hand: rp1 dummy edge constraint OUTGOING_ONLY" d1.internal.edgeConstraint .outgoingOnly
  checkEq "rp1 dummy layer constraint FIRST_SEPARATE"
    (d1.props.get? LayeredOptions.LAYERING_LAYER_CONSTRAINT) (some .firstSeparate)
  checkEq "rp1 dummy port labels placement outside"
    (d1.props.get? CoreOptions.PORT_LABELS_PLACEMENT) (some PortLabelPlacement.outsideSet)
  checkEq "rp1 dummy port" d1.ports #[p 0]
  checkEq "hand: dummy port side EAST" (a.port (p 0)).side .east
  checkVec "hand: dummy port position (0, h/2)" (a.port (p 0)).position ⟨0.0, 2.5⟩
  check "hand: rp1 not connected to external nodes" (!(a.port (p 0)).connectedToExternalNodes)
  check "hand: rp1 dummy port INSIDE_CONNECTIONS (edge into a child)" (a.port (p 0)).internal.insideConnections
  -- dummies of rp2 (EAST) and rp3 (NORTH)
  checkEq "rp2 extPortSide" (a.node (n 1)).internal.extPortSide .east
  checkEq "rp2 edge constraint INCOMING_ONLY" (a.node (n 1)).internal.edgeConstraint .incomingOnly
  checkFloat "rp2 dummy border offset" ((a.node (n 1)).props.getD CoreOptions.PORT_BORDER_OFFSET 0.0) 2.0
  checkEq "rp3 extPortSide" (a.node (n 2)).internal.extPortSide .north
  checkVec "hand: rp3 dummy size (w, 0)" (a.node (n 2)).size ⟨5.0, 0.0⟩
  checkVec "hand: rp3 dummy port position (w/2, 0)" (a.port (p 2)).position ⟨2.5, 0.0⟩
  -- model order
  checkEq "hand: x model order 0" (a.node (n 3)).internal.modelOrder (some 0)
  checkEq "y opts out of the model order" (a.node (n 4)).internal.modelOrder none
  checkEq "MAX_MODEL_ORDER_NODES" gr.internal.maxModelOrderNodes 1
  checkEq "modelOrder stored on the ElkNode" ((r.g.node (nodeNamed r.g "x")).props.get? ElkGraphImporter.ELK_MODEL_ORDER) (some 0)
  check "modelOrder key not copied into the LNode options" (!(a.node (n 3)).props.has ElkGraphImporter.ELK_MODEL_ORDER)
  -- edges to the external ports
  let eIn := a.edge (e 0)
  checkEq "in source = rp1 dummy port" eIn.source (some (p 0))
  checkEq "hand: in target = new WEST port of x" eIn.target (some (p 3))
  checkEq "hand: in edge model order 0" eIn.internal.modelOrder (some 0)
  let eOut := a.edge (e 1)
  checkEq "hand: out source = new EAST port of x" eOut.source (some (p 4))
  checkEq "out target = rp2 dummy port" eOut.target (some (p 1))
  checkEq "hand: out edge model order 1" eOut.internal.modelOrder (some 1)
  checkEq "x ports" (a.node (n 3)).ports #[p 3, p 4]

/-! ## Hierarchical import -/

/-- `INCLUDE_CHILDREN` root (DOWN) with compound `h` (port `hp`, children `i`, `j`, edges `eij`,
`ehp`), `k`, and `z` laid out by another algorithm; root edges `ejk` (crossing into `h`) and `ehk`. -/
def hierarchyJson : String := "{
  \"id\": \"root\",
  \"layoutOptions\": { \"elk.hierarchyHandling\": \"INCLUDE_CHILDREN\", \"elk.direction\": \"DOWN\" },
  \"children\": [
    { \"id\": \"h\", \"width\": 50, \"height\": 40,
      \"layoutOptions\": { \"elk.padding\": \"[top=5,left=5,bottom=5,right=5]\" },
      \"ports\": [ { \"id\": \"hp\", \"width\": 4, \"height\": 4 } ],
      \"children\": [ { \"id\": \"i\", \"width\": 10, \"height\": 10 }, { \"id\": \"j\", \"width\": 10, \"height\": 10 } ],
      \"edges\": [ { \"id\": \"eij\", \"sources\": [\"i\"], \"targets\": [\"j\"] },
                   { \"id\": \"ehp\", \"sources\": [\"hp\"], \"targets\": [\"i\"] } ] },
    { \"id\": \"k\", \"width\": 10, \"height\": 10 },
    { \"id\": \"z\", \"width\": 10, \"height\": 10, \"layoutOptions\": { \"elk.algorithm\": \"org.eclipse.elk.box\" },
      \"children\": [ { \"id\": \"z1\", \"width\": 5, \"height\": 5 } ] }
  ],
  \"edges\": [
    { \"id\": \"ejk\", \"sources\": [\"j\"], \"targets\": [\"k\"] },
    { \"id\": \"ehk\", \"sources\": [\"h\"], \"targets\": [\"k\"] }
  ]
}"

def hierarchicalImport : Suite := suite "layered.import.hierarchical" do
  let r ← importText hierarchyJson
  let a := r.a
  checkEq "hand: graphs root + h" a.graphs.size 2
  checkEq "hand: nodes h, i, j, k, z (z1 belongs to another algorithm)" a.nodes.size 5
  -- Java order: the nodes breadth-first over the hierarchy (h, k, z, then h's children i, j)
  checkEq "root layerless nodes" (a.graph r.lgraph).layerlessNodes #[n 0, n 1, n 2]
  let g1 : LGraphId := ⟨1⟩
  checkEq "nested layerless nodes" (a.graph g1).layerlessNodes #[n 3, n 4]
  checkEq "h nested graph" (a.node (n 0)).nestedGraph (some g1)
  checkEq "nested graph parent" (a.graph g1).parentNode (some (n 0))
  check "h COMPOUND_NODE" (a.node (n 0)).internal.compoundNode
  checkEqR "nested graph origin" (a.graph g1).internal.origin (some (.elkNode (nodeNamed r.g "h")))
  checkPadding "nested graph padding" (a.graph g1).padding 5.0 5.0 5.0 5.0
  checkEq "hand: nested DIRECTION from the parent level" ((a.graph g1).props.get? CoreOptions.DIRECTION) (some .down)
  check "hand: z COMPOUND_NODE (children) without nested graph"
    ((a.node (n 2)).internal.compoundNode && (a.node (n 2)).nestedGraph.isNone)
  check "hand: hp INSIDE_CONNECTIONS" (a.port (p 0)).internal.insideConnections
  checkEq "hand: edges eij, ehp, ejk, ehk" a.edges.size 4
  -- Java order: all nodes first, then the edges graph by graph breadth-first (root: ejk, ehk; h: eij, ehp)
  -- eij inside h: node ports created with the DOWN direction
  checkEq "hand: eij source port side SOUTH" ((a.edge (e 2)).source.map fun q => (a.port q).side) (some .south)
  checkEq "hand: eij target port side NORTH" ((a.edge (e 2)).target.map fun q => (a.port q).side) (some .north)
  checkEq "hand: ehp source is h's port hp" (a.edge (e 3)).source (some (p 0))
  checkEq "ehp target owner i" ((a.edge (e 3)).target.bind fun q => (a.port q).owner) (some (n 3))
  -- ejk crosses the hierarchy
  checkEq "ejk source owner j" ((a.edge (e 0)).source.bind fun q => (a.port q).owner) (some (n 4))
  checkEq "ejk target owner k" ((a.edge (e 0)).target.bind fun q => (a.port q).owner) (some (n 1))
  checkEq "hand: ejk COORDINATE_SYSTEM_ORIGIN = root graph" (a.edge (e 0)).internal.coordinateSystemOrigin (some r.lgraph)
  checkNone "ehk coordinate origin (siblings)" (a.edge (e 1)).internal.coordinateSystemOrigin
  checkEq "h ports: hp, ehk source" (a.node (n 0)).ports #[p 0, p 3]
  -- inside self loop under INCLUDE_CHILDREN: the root's edge loop places it into the child's nested
  -- graph, once (Java; elk-rs also imported it from the child level, giving a second copy)
  let loopJson := "{ \"id\": \"root\", \"layoutOptions\": { \"elk.hierarchyHandling\": \"INCLUDE_CHILDREN\" },
    \"children\": [ { \"id\": \"c\", \"width\": 20, \"height\": 20,
      \"layoutOptions\": { \"elk.insideSelfLoops.activate\": \"true\" },
      \"ports\": [ { \"id\": \"cp1\" }, { \"id\": \"cp2\" } ] } ],
    \"edges\": [ { \"id\": \"sl\", \"sources\": [\"cp1\"], \"targets\": [\"cp2\"],
      \"layoutOptions\": { \"elk.insideSelfLoops.yo\": \"true\" } } ] }"
  let s ← importText loopJson
  let g1 : LGraphId := ⟨1⟩
  checkEq "hand: inside self loop gives c a nested graph" (s.a.node (n 0)).nestedGraph (some g1)
  check "c COMPOUND_NODE" (s.a.node (n 0)).internal.compoundNode
  checkEq "java: the inside self loop is imported once" s.a.edges.size 1
  checkEq "it connects cp1 → cp2" ((s.a.edge (e 0)).source, (s.a.edge (e 0)).target) (some (p 0), some (p 1))
  checkEq "ledges points to it" (s.ledges.get? (edgeNamed s.g "sl")) (some (e 0))
  check "hand: both end ports INSIDE_CONNECTIONS"
    ((s.a.port (p 0)).internal.insideConnections && (s.a.port (p 1)).internal.insideConnections)
  let gp1 := (s.a.graph g1).internal.graphProperties
  check "hand: SELF_LOOPS (no HYPEREDGES) on the nested graph" (gp1.contains .selfLoops && !gp1.contains .hyperedges)
  check "root graph has no SELF_LOOPS" (!(s.a.graph s.lgraph).internal.graphProperties.contains .selfLoops)

/-! ## Graph properties, hypernodes, self loops -/

def miscJson : String := "{
  \"id\": \"root\",
  \"children\": [
    { \"id\": \"s\", \"width\": 10, \"height\": 10,
      \"ports\": [ { \"id\": \"np\", \"layoutOptions\": { \"elk.noLayout\": \"true\" } } ] },
    { \"id\": \"hn\", \"width\": 10, \"height\": 10,
      \"layoutOptions\": { \"elk.hypernode\": \"true\", \"elk.portConstraints\": \"FIXED_ORDER\" } }
  ],
  \"edges\": [ { \"id\": \"loop\", \"sources\": [\"s\"], \"targets\": [\"s\"] },
               { \"id\": \"fromNp\", \"sources\": [\"np\"], \"targets\": [\"hn\"] } ]
}"

def graphProperties : Suite := suite "layered.import.graphProperties" do
  let r ← importText miscJson
  let gp := (r.a.graph r.lgraph).internal.graphProperties
  check "hand: SELF_LOOPS" (gp.contains .selfLoops)
  check "hand: HYPERNODES" (gp.contains .hypernodes)
  check "hand: HYPEREDGES (hypernode)" (gp.contains .hyperedges)
  check "hand: NON_FREE_PORTS (FIXED_ORDER before the hypernode reset)" (gp.contains .nonFreePorts)
  checkEq "hypernode PORT_CONSTRAINTS FREE" ((r.a.node (n 1)).props.get? CoreOptions.PORT_CONSTRAINTS) (some .free)
  checkEq "self loop ports on s, then the lazily transformed NO_LAYOUT port" (r.a.node (n 0)).ports #[p 0, p 1, p 2]
  checkEqR "hand: NO_LAYOUT port transformed on demand (resolve_port)" (r.a.port (p 2)).internal.origin
    (some (.elkPort (portNamed r.g "np")))
  checkEq "hand: hypernode end point uses an input collector port" (r.a.edge (e 1)).target (some (p 3))
  check "collector port flag" (r.a.port (p 3)).internal.inputCollect
  -- graph_properties_include_end_labels (end_label_graph_properties_test.rs)
  let (g, root) := ElkGraphUtil.createGraph
  let (g, n1) := g.createNode (some root)
  let (g, n2) := g.createNode (some root)
  let (g, edge) := ElkGraphUtil.createSimpleEdge g (.node n1) (.node n2)
  let (g, label) := g.createLabel (some (.edge edge)) "tail"
  let g := g.modifyLabel label fun x => { x with props := x.props.set CoreOptions.EDGE_LABELS_PLACEMENT EdgeLabelPlacement.tail }
  let imp ← ElkGraphImporter.new
  let ((lgraph, a), _) ← LImportM.run (imp.importGraph root) {} g
  check "graph_properties_include_end_labels" ((a.graph lgraph).internal.graphProperties.contains .endLabels)

/-- `importer_adds_inside_node_label_padding_to_graph_padding` (elk_graph_importer_padding_test.rs). -/
def paddingTest : Suite := suite "layered.import.padding" do
  Elk.Api.ensureInitialized
  let (g, root) := ElkGraphUtil.createGraph
  let g := g.setNodeProp root CoreOptions.PADDING (ElkPadding.ofValues 1.0 2.0 3.0 4.0)
  let spacings : IndividualSpacings := { props := (({} : PropertyMap).set CoreOptions.NODE_LABELS_PADDING
    (ElkPadding.ofValues 2.0 3.0 4.0 5.0)).set CoreOptions.SPACING_LABEL_LABEL 1.0 }
  let g := g.setNodeProp root CoreOptions.SPACING_INDIVIDUAL spacings
  let (g, label) := g.createLabel (some (.node root)) ""
  let placement : EnumSet NodeLabelPlacement := EnumSet.of #[.inside, .vTop, .hCenter]
  let g := g.modifyLabel label fun x =>
    { x with width := 10.0, height := 5.0, props := x.props.set CoreOptions.NODE_LABELS_PLACEMENT placement }
  let imp ← ElkGraphImporter.new
  let ((lgraph, a), _) ← LImportM.run (imp.importGraph root) {} g
  -- top: base(1) + labelHeight(5) + nodeLabelsPadding.top(2) + cellGap(2)
  checkPadding "importer_adds_inside_node_label_padding_to_graph_padding" (a.graph lgraph).padding 10.0 2.0 3.0 4.0

/-! ## Errors -/

def scopeErrors : Suite := suite "layered.import.errors" do
  -- ELK Java's flat import only transforms edges between children (or a child and the graph): an
  -- edge from or into a child's child is left alone without an error (checked against ELK Java;
  -- elk-rs throws "The source/target of edge … could not be found in the current layout scope")
  let src := "{ \"id\": \"root\", \"children\": [ { \"id\": \"p\", \"children\": [ { \"id\": \"q\" } ] }, { \"id\": \"r\" } ],
    \"edges\": [ { \"id\": \"bad\", \"sources\": [\"q\"], \"targets\": [\"r\"] } ] }"
  checkEq "Java: source in a child's child, edge left alone" (← importError src) none
  let r ← importText src
  checkEq "Java: the edge is not transformed" (r.ledges.get? (edgeNamed r.g "bad")) none
  checkEq "Java: no LEdge" r.a.edges.size 0
  let tgt := "{ \"id\": \"root\", \"children\": [ { \"id\": \"p\", \"children\": [ { \"id\": \"q\" } ] }, { \"id\": \"r\" } ],
    \"edges\": [ { \"id\": \"bad2\", \"sources\": [\"r\"], \"targets\": [\"q\"] } ] }"
  checkEq "Java: target in a child's child, edge left alone" (← importError tgt) none
  -- an edge to a NO_LAYOUT sibling is transformed and fails on its untransformed end (ELK Java text)
  let noLayout := "{ \"id\": \"root\", \"children\": [ { \"id\": \"a\", \"x\": 1, \"y\": 2, \"width\": 30, \"height\": 20 },
    { \"id\": \"n\", \"width\": 10, \"height\": 10, \"layoutOptions\": { \"elk.noLayout\": \"true\" } } ],
    \"edges\": [ { \"id\": \"e3\", \"sources\": [\"a\"], \"targets\": [\"n\"] } ] }"
  checkEq "Java: edge to a NO_LAYOUT sibling" (← importError noLayout)
    (some "org.eclipse.elk.core.UnsupportedGraphException: The source or the target of edge ElkEdge \"e3\" ElkNode \"a\" (1.0,2.0 | 30.0,20.0) -> ElkNode \"n\" (0.0,0.0 | 10.0,10.0) could not be found. This usually happens when an edge connects a node laid out by ELK Layered to a node in another level of hierarchy laid out by either another instance of ELK Layered or another layout algorithm alltogether. The former can be solved by setting the hierarchyHandling option to INCLUDE_CHILDREN.")
  -- with INCLUDE_CHILDREN the same edge is in scope
  let ok := "{ \"id\": \"root\", \"layoutOptions\": { \"elk.hierarchyHandling\": \"INCLUDE_CHILDREN\" },
    \"children\": [ { \"id\": \"p\", \"children\": [ { \"id\": \"q\" } ] }, { \"id\": \"r\" } ],
    \"edges\": [ { \"id\": \"fine\", \"sources\": [\"q\"], \"targets\": [\"r\"] } ] }"
  checkEq "INCLUDE_CHILDREN imports the cross-hierarchy edge" (← importError ok) none

/-! ## LGraphAdapters -/

private def addPort (owner : LNodeId) (side : PortSide) (pos : KVector) (index : Option Int := none) : LayeredM LPortId := do
  let port ← LayeredM.createPort { side, position := pos, props := match index with
    | some i => ({} : PropertyMap).set CoreOptions.PORT_INDEX i
    | none => {} }
  LayeredM.setPortNode port (some owner)
  return port

private def connect (s t : LPortId) : LayeredM LEdgeId := do
  let edge ← LayeredM.createEdge
  LayeredM.setEdgeSource edge (some s)
  LayeredM.setEdgeTarget edge (some t)
  return edge

/-- Ids of the adapter scenario. -/
structure AdapterIds where
  g : LGraphId
  n0 : LNodeId
  ns : LNodeId
  lbl : LNodeId
  n3 : LNodeId
  c0 : LNodeId
  c1 : LNodeId
  ports : Array LPortId
  q0 : LPortId
  r0 : LPortId
  e0 : LEdgeId
  e1 : LEdgeId
  lab0 : LLabelId
  lab1 : LLabelId

/-- Graph with layers `[n0, ns (NORTH_SOUTH_PORT), lbl (LABEL)]` and `[n3]`; `n0` (`FIXED_ORDER`,
compound, comments `c0` top / `c1` bottom) has ports `p1 S(x5)`, `p2 N(x10, idx1)`, `p3 N(x3, idx1)`,
`p4 N(x1, idx2)`, `p6 W(y4)`, `p7 W(y8)`, `p8 E(y1)`, `p9 S(x7)`; `ns.q0 → n3.r1` (`e0`),
`n0.p1 → n3.r0` (`e1`, labelled); `r0.PORT_DUMMY = ns`. -/
def buildAdapterGraph : LayeredM AdapterIds := do
  let g ← LayeredM.createGraph { props := ({} : PropertyMap).set CoreOptions.SPACING_NODE_NODE 7.0 }
  let l0 ← LayeredM.createLayer g
  let l1 ← LayeredM.createLayer g
  LayeredM.modifyGraph g fun x => { x with layers := #[l0, l1] }
  let c0 ← LayeredM.createNode g
  let c1 ← LayeredM.createNode g
  let n0 ← LayeredM.createNode g {
    size := ⟨30.0, 20.0⟩, position := ⟨1.0, 2.0⟩
    margin := { top := 1.0, right := 2.0, bottom := 3.0, left := 4.0 }
    padding := { top := 5.0, right := 6.0, bottom := 7.0, left := 8.0 }
    props := ({} : PropertyMap).set CoreOptions.PORT_CONSTRAINTS PortConstraints.fixedOrder
    internal := { compoundNode := true, topComments := #[c0], bottomComments := #[c1] } }
  let ns ← LayeredM.createNode g { type := .northSouthPort }
  let lbl ← LayeredM.createNode g { type := .label }
  let n3 ← LayeredM.createNode g
  for x in #[n0, ns, lbl] do LayeredM.setNodeLayer x (some l0)
  LayeredM.setNodeLayer n3 (some l1)
  let p1 ← addPort n0 .south ⟨5.0, 0.0⟩
  let p2 ← addPort n0 .north ⟨10.0, 0.0⟩ (some 1)
  let p3 ← addPort n0 .north ⟨3.0, 0.0⟩ (some 1)
  let p4 ← addPort n0 .north ⟨1.0, 0.0⟩ (some 2)
  let p6 ← addPort n0 .west ⟨0.0, 4.0⟩
  let p7 ← addPort n0 .west ⟨0.0, 8.0⟩
  let p8 ← addPort n0 .east ⟨0.0, 1.0⟩
  let p9 ← addPort n0 .south ⟨7.0, 0.0⟩
  let q0 ← addPort ns .north {}
  let r0 ← addPort n3 .west {}
  let r1 ← addPort n3 .west {}
  LayeredM.modifyPort r0 fun x => { x with internal := { x.internal with portDummy := some ns } }
  LayeredM.modifyPort p2 fun x => { x with internal := { x.internal with insideConnections := true } }
  let e0 ← connect q0 r1
  let e1 ← connect p1 r0
  let lab0 ← LayeredM.createLabel "node label" {
    props := (({} : PropertyMap).set LabelSide.LABEL_SIDE LabelSide.below), internal := { labelSide := .above } }
  LayeredM.modifyNode n0 fun x => { x with labels := #[lab0] }
  let lab1 ← LayeredM.createLabel "edge label"
  LayeredM.modifyEdge e1 fun x => { x with labels := #[lab1] }
  return { g, n0, ns, lbl, n3, c0, c1, ports := #[p1, p2, p3, p4, p6, p7, p8, p9], q0, r0, e0, e1, lab0, lab1 }

/-- What the adapter scenario observes (computed in `LayeredM`, checked in `TestM`). -/
structure AdapterResults where
  ids : AdapterIds
  nodes : Array LNodeId
  size : KVector
  n0Size : KVector
  n0Pos : KVector
  graphOfN0 : Option LGraphId
  graphOfC0 : Option LGraphId
  spacingN0 : Option Float
  spacingC0 : Option Float
  padding : ElkPadding
  margin : ElkMargin
  compound0 : Bool
  compound3 : Bool
  inc0 : Array LEdgeId
  q0Out : Array LEdgeId
  r0In : Array LEdgeId
  r0Out : Array LEdgeId
  compoundP1 : Bool
  compoundP2 : Bool
  side : LabelSide
  text : String
  edgeLabels : Array LLabelId
  portSide : PortSide
  vol : Int
  sorted : Array LPortId
  before3 : Array LPortId
  after3 : Array LPortId
  plainNodes : Array LNodeId
  plainQ0Out : Array LEdgeId
  plainR0Out : Array LEdgeId
  plainVol : Int
  simpleNodes : Array LNodeId

/-- Runs the adapter queries on the scenario of `buildAdapterGraph`. -/
def runAdapterScenario : LayeredM AdapterResults := do
  let ids ← buildAdapterGraph
  let ad ← LGraphAdapters.adapt ids.g true true fun nd => nd.type != .label
  let nodes ← ad.getNodes ids.g
  let size ← ad.graph.getSize ids.g
  let n0Size ← ad.node.getSize ids.n0
  ad.node.setPosition ids.n0 ⟨9.0, 9.0⟩
  let n0Pos := (← LayeredM.getNode ids.n0).position
  let graphOfN0 ← ad.getGraph ids.n0
  let graphOfC0 ← ad.getGraph ids.c0
  let spacingN0 ← GraphAdapters.getIndividualOrInherited ad ids.n0 CoreOptions.SPACING_NODE_NODE
  let spacingC0 ← GraphAdapters.getIndividualOrInherited ad ids.c0 CoreOptions.SPACING_NODE_NODE
  let padding ← ad.getPadding ids.n0
  let margin ← ad.getNodeMargin ids.n0
  let compound0 ← ad.isCompoundNode ids.n0
  let compound3 ← ad.isCompoundNode ids.n3
  let inc0 ← ad.nodeIncomingEdges ids.n0
  let q0Out ← ad.portOutgoingEdges ids.q0
  let r0In ← ad.portIncomingEdges ids.r0
  let r0Out ← ad.portOutgoingEdges ids.r0
  let compoundP1 ← ad.hasCompoundConnections ids.ports[0]!
  let compoundP2 ← ad.hasCompoundConnections ids.ports[1]!
  let side ← ad.labelSide ids.lab0
  let text ← ad.labelText ids.lab0
  let edgeLabels ← ad.edgeLabels ids.e1
  let portSide ← ad.portSide ids.ports[0]!
  ad.node.setVolatileId ids.n0 5
  let vol ← ad.node.getVolatileId ids.n0
  ad.sortPortList ids.n0
  let sorted := (← LayeredM.getNode ids.n0).ports
  let before3 := (← LayeredM.getNode ids.n3).ports
  ad.sortPortList ids.n3
  let after3 := (← LayeredM.getNode ids.n3).ports
  -- an opaque adapter family
  let plain ← LGraphAdapters.adapt ids.g false false fun _ => true
  let plainNodes ← plain.getNodes ids.g
  let plainQ0Out ← plain.portOutgoingEdges ids.q0
  let plainR0Out ← plain.portOutgoingEdges ids.r0
  let plainVol ← plain.node.getVolatileId ids.n0
  let simple ← LGraphAdapters.adaptSimple ids.g
  let simpleNodes ← simple.getNodes ids.g
  return { ids, nodes, size, n0Size, n0Pos, graphOfN0, graphOfC0, spacingN0, spacingC0, padding, margin,
           compound0, compound3, inc0, q0Out, r0In, r0Out, compoundP1, compoundP2, side, text, edgeLabels,
           portSide, vol, sorted, before3, after3, plainNodes, plainQ0Out, plainR0Out, plainVol, simpleNodes }

def adapters : Suite := suite "layered.import.LGraphAdapters" do
  let (r, _) ← LayeredM.run runAdapterScenario
  let ids := r.ids
  checkEq "hand: nodes = n0, top comment, bottom comment, ns, n3 (label filtered)" r.nodes
    #[ids.n0, ids.c0, ids.c1, ids.ns, ids.n3]
  checkVec "graph adapter size (0, 0)" r.size ⟨0.0, 0.0⟩
  checkVec "node size" r.n0Size ⟨30.0, 20.0⟩
  checkVec "node setPosition" r.n0Pos ⟨9.0, 9.0⟩
  checkEq "layer node has the graph" r.graphOfN0 (some ids.g)
  checkEq "hand: comment node has no graph (Rust LNodeAdapter::new)" r.graphOfC0 none
  checkEq "spacing inherited from the graph" r.spacingN0 (some 7.0)
  checkEq "hand: comment spacing falls back to the default" r.spacingC0 (some 20.0)
  checkPadding "node padding" r.padding 5.0 6.0 7.0 8.0
  checkFloat "node margin left" r.margin.left 4.0
  check "isCompoundNode n0" r.compound0
  check "isCompoundNode n3" (!r.compound3)
  checkEq "node edges are empty" r.inc0 #[]
  checkEq "hand: transparent N/S port has no edges" r.q0Out #[]
  checkEq "hand: r0 incoming = own" r.r0In #[ids.e1]
  checkEq "hand: r0 outgoing = PORT_DUMMY node's outgoing" r.r0Out #[ids.e0]
  check "hasCompoundConnections = INSIDE_CONNECTIONS" (r.compoundP2 && !r.compoundP1)
  checkEq "hand: label side from LabelSide.LABEL_SIDE (not the internal field)" r.side .below
  checkEq "label text" r.text "node label"
  checkEq "edge labels" r.edgeLabels #[ids.lab1]
  checkEq "port side" r.portSide .south
  checkEq "volatile id" r.vol 5
  checkEq "hand: sortPortList (side, PORT_INDEX, coordinate)" r.sorted
    #[ids.ports[2]!, ids.ports[1]!, ids.ports[3]!, ids.ports[6]!, ids.ports[7]!, ids.ports[0]!, ids.ports[5]!, ids.ports[4]!]
  checkEq "FREE ports are not sorted" r.after3 r.before3
  checkEq "hand: no comment nodes without transparentCommentNodes" r.plainNodes #[ids.n0, ids.ns, ids.lbl, ids.n3]
  checkEq "opaque N/S port keeps its edges" r.plainQ0Out #[ids.e0]
  checkEq "opaque r0 outgoing = own" r.plainR0Out #[]
  checkEq "fresh family volatile ids start at 0" r.plainVol 0
  checkEq "adaptSimple = all layer nodes" r.simpleNodes #[ids.n0, ids.ns, ids.lbl, ids.n3]

/-! ## Import → applyLayout round trip -/

def roundTripJson : String := "{
  \"id\": \"root\",
  \"children\": [ { \"id\": \"a\", \"width\": 10, \"height\": 10 }, { \"id\": \"b\", \"width\": 10, \"height\": 10 } ],
  \"edges\": [ { \"id\": \"e\", \"sources\": [\"a\"], \"targets\": [\"b\"] } ]
}"

/-- A hand-made "layout" of the round-trip graph: `a` at `(0, 0)`, `b` at `(40, 0)`, end ports at
`(10, 5)` / `(0, 5)`, one bend point `(25, 5)`, graph size `50 × 10`. -/
def fakeLayout (lgraph : LGraphId) : LayeredM Unit := do
  LayeredM.modifyGraph lgraph fun g => { g with size := ⟨50.0, 10.0⟩ }
  LayeredM.modifyNode (n 0) fun x => { x with position := ⟨0.0, 0.0⟩ }
  LayeredM.modifyNode (n 1) fun x => { x with position := ⟨40.0, 0.0⟩ }
  LayeredM.modifyPort (p 0) fun x => { x with position := ⟨10.0, 5.0⟩ }
  LayeredM.modifyPort (p 1) fun x => { x with position := ⟨0.0, 5.0⟩ }
  LayeredM.modifyEdge (e 0) fun x => { x with bendPoints := #[⟨25.0, 5.0⟩] }

def roundTrip : Suite := suite "layered.import.roundTrip" do
  let (root, g) ← elkGraphOf roundTripJson
  let transformer ← ElkGraphTransformer.new
  let ((_, a), g) ← LImportM.run (do
    let lgraph ← transformer.importGraph root
    liftLayered (fakeLayout lgraph)
    transformer.applyLayout lgraph
    return lgraph) {} g
  checkEq "two nodes imported" a.nodes.size 2
  let na := g.node (nodeNamed g "a")
  let nb := g.node (nodeNamed g "b")
  -- offset = graph offset (0) + padding (12)
  checkFloat "hand: a.x = 0 + 12" na.x 12.0
  checkFloat "hand: a.y = 0 + 12" na.y 12.0
  checkFloat "hand: b.x = 40 + 12" nb.x 52.0
  checkFloat "hand: b.y = 0 + 12" nb.y 12.0
  let edge := g.edge (edgeNamed g "e")
  checkEq "one section" edge.sections.size 1
  match edge.sections[0]? with
  | some s =>
    let sec := g.edgeSection s
    checkVec "hand: section start = port anchor + 12" sec.startPoint ⟨22.0, 17.0⟩
    checkVec "hand: section end" sec.endPoint ⟨52.0, 17.0⟩
    checkEq "one bend point" sec.bendPoints.size 1
    checkVec "hand: bend point (25, 5) + 12" (sec.bendPoints[0]?.getD {}) ⟨37.0, 17.0⟩
  | none => check "section exists" false
  let rootNode := g.node root
  checkFloat "hand: root width = 50 + 2 * 12" rootNode.width 74.0
  checkFloat "hand: root height = 10 + 2 * 12" rootNode.height 34.0
  -- a graph without an ElkNode origin is ignored by applyLayout
  let imp ← ElkGraphImporter.new
  let ((_, _), g2) ← LImportM.run (do
    let orphan ← LayeredM.createGraph {}
    imp.applyLayout orphan) {} g
  checkEq "orphan graph: ElkGraph untouched" (g2.node (nodeNamed g2 "a")).x 12.0

def suites : Array Suite :=
  #[flatImport, externalPorts, hierarchicalImport, graphProperties, paddingTest, scopeErrors, adapters, roundTrip]

end Tests.Layered.Import
