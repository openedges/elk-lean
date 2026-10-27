import Tests.Framework
import Elk.Api
/-!
# Tests for the JSON importer / exporter / layout transfer

Ported from the elk-rs `org.eclipse.elk.graph.json` unit tests
(`tests/all/{graph,edges,sections,id,layout_options,individual_spacings,export,transfer_layout}_test.rs`
plus the inline `metadata_cache_tests` of `json_importer.rs` and `tests` of `layout_api.rs`).

Not ported (they need a real layout algorithm; the engine is still a placeholder):
`root_external_ports_test.rs` (9 tests, layered), `edgeless_hierarchy_integration_test.rs`
(5 of 6 tests, layered; the "completes" and "deterministic" ones run with the placeholder),
`edge_coords_test.rs::edge_coords_round_trip` (layered), `transfer_layout_edge_sections_exist`
(random layout creates the sections), `layout_api` provider-comparison tests
(`shared_defaults_and_owned_values_preserve_every_registered_provider`, `test_simple_layout`
coordinates, `test_global_options_as_defaults` y-equality).
-/
namespace Tests.Json.Importer

open Tests Elk Elk.Graph Elk.Core Elk.Core.Math Elk.Core.Util Elk.Core.Options Elk.Core.Data Elk.Json

/-! ### Helpers -/

/-- Result of importing a document: root node, importer state and the arena. -/
structure Imp where
  root : NodeId
  st : ImporterState
  g : ElkGraph

/-- `json5::from_str` replacement: lenient parse. -/
def parseLenient (text : String) : IO Value := do
  match Elk.Json.parse text (lenient := true) with
  | .ok v => pure v
  | .error e => throw (IO.userError s!"lenient parse failed: {e.message}")

/-- `ElkGraphJson::for_graph(text).to_elk()`. -/
def importText (text : String) : IO Imp := do
  Elk.Api.ensureInitialized
  let doc ← parseLenient text
  let (root, st, g) ← importGraph doc
  return { root, st, g }

/-- Error message of a failing import, `none` if it succeeds. -/
def importError (text : String) : IO (Option String) := do
  try
    let _ ← importText text
    return none
  catch e => return some (toString e)

/-- Substring test. -/
def has (s sub : String) : Bool := (s.splitOn sub).length > 1

/-- `transfer_layout` on the (possibly modified) arena; returns the written model. -/
def transfer (m : Imp) (g : ElkGraph) : IO Value := do
  let (((), st), _) ← (ImportM.run JsonImporter.transferLayout m.st).run g
  return st.model

/-- `to_json_graph_and_back`: import + transfer without layout, serialised compactly. -/
def jsonAndBack (text : String) : IO String := do
  let m ← importText text
  return (← transfer m m.g).render

/-- Node whose identifier is `id` (searches the whole arena). -/
def nodeById (g : ElkGraph) (id : String) : NodeId :=
  match g.nodes.findIdx? (·.identifier == some id) with
  | some i => ⟨i⟩
  | none => ⟨g.nodes.size⟩

def sectionById (g : ElkGraph) (id : String) : SectionId :=
  match g.sections.findIdx? (·.identifier == some id) with
  | some i => ⟨i⟩
  | none => ⟨g.sections.size⟩

def hasNode (g : ElkGraph) (id : String) : Bool := g.nodes.any (·.identifier == some id)

/-- JSON array element with `"id" == id`. -/
def byId (arr : Option Value) (id : String) : Option Value :=
  arr.bind fun a => a.getArr?.bind fun xs => xs.find? fun x => x.get? "id" == some (.str id)

def setLoc (g : ElkGraph) (n : NodeId) (x y : Float) : ElkGraph :=
  g.modifyNode n fun nd => { nd with x, y }

def setNodeProp {α : Type} [PropCodec α] (g : ElkGraph) (n : NodeId) (p : Property α) (v : α) : ElkGraph :=
  g.modifyProps (.node n) (·.set p v)

def setEdgeProp {α : Type} [PropCodec α] (g : ElkGraph) (e : EdgeId) (p : Property α) (v : α) : ElkGraph :=
  g.modifyProps (.edge e) (·.set p v)

def num? (v : Option Value) : Option Float := v.bind (·.getFloat?)

def checkVec (name : String) (actual : KVector) (x y : Float) : TestM Unit := do
  checkFloat s!"{name}.x" actual.x x
  checkFloat s!"{name}.y" actual.y y

/-- Parses `"(x,y)"` style vector option strings. -/
def parseVec? (s : String) : Option KVector := (KVector.parse s).toOption

/-- Parses a vector chain option string. -/
def parseChain? (s : String) : Option KVectorChain := (KVectorChain.parse s).toOption

/-- Checks `junctionPoints[i]` of an edge object. -/
def checkJunctions (name : String) (edge : Option Value) (pts : Array (Float × Float)) : TestM Unit := do
  let arr := (edge.bind (·.get? "junctionPoints")).bind (·.getArr?)
  checkEq s!"{name} count" (arr.map (·.size)) (some pts.size)
  for h : i in [0:pts.size] do
    let p := arr.bind (·[i]?)
    checkEq s!"{name}[{i}].x" (num? (p.bind (·.get? "x"))) (some pts[i].1)
    checkEq s!"{name}[{i}].y" (num? (p.bind (·.get? "y"))) (some pts[i].2)

/-! ### graph_test.rs -/

/-- Rust `graph_test.rs`: `graph_must_be_object`, `graph_must_be_object_fail_array`,
`small_graph_import`, `reject_sloppy_json_when_not_lenient`, `accept_sloppy_json_when_lenient`. -/
def graphTests : Suite := suite "json.import.graph" do
  -- graph_must_be_object
  check "graph_must_be_object" ((← importError "{\"id\":1}").isNone)
  -- graph_must_be_object_fail_array
  let e ← importError "[]"
  check "graph_must_be_object_fail_array throws" e.isSome
  check "array error is JsonImportException" ((e.getD "").startsWith jsonImportExceptionClass)
  check "array error message" (has (e.getD "") "Top-level element of the graph must be a json object.")
  -- small_graph_import
  let m ← importText "
    {
      \"id\": \"root\",
      \"properties\": {
        \"elk.direction\": \"DOWN\"
      },
      \"children\": [{\"id\": \"n1\", \"width\": 40, \"height\": 40},
                  {\"id\": \"n2\", \"width\": 40, \"height\": 40}],
      \"edges\": [{\"id\": \"e1\", \"source\": \"n1\", \"target\": \"n2\"}]
    }"
  checkEq "small children" (m.g.node m.root).children.size 2
  checkEq "small edges" (m.g.node m.root).containedEdges.size 1
  check "small direction" ((m.g.node m.root).props.get? CoreOptions.DIRECTION == some Direction.down)
  let n1 := nodeById m.g "n1"
  checkFloat "n1 width" (m.g.node n1).width 40.0
  checkFloat "n1 height" (m.g.node n1).height 40.0
  -- reject_sloppy_json_when_not_lenient / accept_sloppy_json_when_lenient
  let sloppy := "
        {
          // the root node
          id: \"root\",
          /* Now the graph */
          \"children\": [ {\"id\": \"c\"}; {\"id\": \"c1\"} ],
          'edges': [] // Endline comment
        }"
  check "reject sloppy json when not lenient" (match Elk.Json.parse sloppy (lenient := false) with | .error _ => true | .ok _ => false)
  let m ← importText sloppy
  checkEq "sloppy root id" (m.g.node m.root).identifier (some "root")
  let ch := (m.g.node m.root).children
  checkEq "sloppy children" ch.size 2
  checkEq "sloppy child 0" (m.g.node ch[0]!).identifier (some "c")
  checkEq "sloppy child 1" (m.g.node ch[1]!).identifier (some "c1")

/-! ### edges_test.rs -/

/-- Rust `edges_test.rs`: `extended_edge_import`, `primitive_edge_import`, `edge_containment_import`. -/
def edgeTests : Suite := suite "json.import.edges" do
  for (name, edgeText) in #[("extended_edge_import", "{\"id\": \"e1\", \"sources\": [ \"n1\" ], \"targets\": [ 3 ]}"),
                            ("primitive_edge_import", "{\"id\": \"e1\", \"source\": \"n1\", \"target\": 3}")] do
    let m ← importText s!"\{\"id\": \"root\", \"children\": [\{\"id\": \"n1\"}, \{\"id\": 3}], \"edges\": [{edgeText}]}"
    checkEq s!"{name} children" (m.g.node m.root).children.size 2
    checkEq s!"{name} edges" (m.g.node m.root).containedEdges.size 1
    let n1 := nodeById m.g "n1"
    let n3 := nodeById m.g "3"
    let e := (m.g.node m.root).containedEdges[0]!
    let edge := m.g.edge e
    check s!"{name} source node" (edge.sources[0]?.bind (ElkGraphUtil.connectableShapeToNode m.g) == some n1)
    check s!"{name} target node" (edge.targets[0]?.bind (ElkGraphUtil.connectableShapeToNode m.g) == some n3)
    checkEq s!"{name} edge id" edge.identifier (some "e1")
  -- edge_containment_import
  let m ← importText "
    {
      \"id\": \"root\",
      \"children\": [
        {\"id\": \"p\"},
        {\"id\": \"q\",
          \"children\": [{\"id\": \"r\"}],
          \"edges\": [{\"id\": \"e\", \"source\": \"p\", \"target\": \"r\" }]
        }]
    }"
  checkEq "edge_containment_import root edges" (m.g.node m.root).containedEdges.size 1
  checkEq "edge_containment_import q edges" (m.g.node (nodeById m.g "q")).containedEdges.size 0
  -- error paths of the edge importer
  let err1 ← importError "{id:'r', children:[{id:'a'}], edges:[{id:'e', source:'a', target:'zz'}]}"
  check "primitive edge with unknown target fails" err1.isSome
  let err2 ← importError "{id:'r', children:[{id:'a'}], edges:[{id:'e', sources:['a'], targets:[]}]}"
  check "extended edge without target fails" (has (err2.getD "") "An edge must have at least one source and one target.")
  let err3 ← importError "{id:'r', children:[{id:'a'}], edges:[{id:'e', sources:['a'], targets:['nope']}]}"
  check "extended edge with unknown shape fails" (has (err3.getD "") "Referenced shape does not exist: nope")

/-! ### sections_test.rs -/

/-- Rust `sections_test.rs`: `edge_section_import`, `preserve_section_ids` (without layout),
`do_not_add_empty_sections_array_extended_edge`, `do_not_add_empty_sections_array_primitive_edge`. -/
def sectionTests : Suite := suite "json.import.sections" do
  let m ← importText "
    {
      \"id\": \"root\",
      \"properties\": {
        \"direction\": \"DOWN\"
      },
      \"children\": [{\"id\": \"n1\"}, {\"id\": \"n2\"}],
      \"edges\": [{\"id\": \"e1\",
        \"sources\": [ \"n1\" ],
        \"targets\": [ \"n2\" ],
        \"sections\": [{
            \"id\": \"s1\",
            \"startPoint\": {\"x\": 1, \"y\": 1},
            \"endPoint\": {\"x\": 2, \"y\": 2},
            \"incomingShape\": \"n1\",
            \"outgoingSections\": [ 44 ]
        },{
            \"id\": 44,
            \"startPoint\": {\"x\": 3, \"y\": 3},
            \"endPoint\": {\"x\": 4, \"y\": 4},
            \"incomingSections\": [ \"s1\" ],
            \"outgoingShape\": \"n2\"
        }]
      }]
    }"
  let n1 := nodeById m.g "n1"
  let n2 := nodeById m.g "n2"
  let e := (m.g.node m.root).containedEdges[0]!
  checkEq "section count" (m.g.edge e).sections.size 2
  let s1 := sectionById m.g "s1"
  let s44 := sectionById m.g "44"
  check "sections found" (s1.idx < m.g.sections.size && s44.idx < m.g.sections.size && s1 != s44)
  check "s1 incoming shape" ((m.g.edgeSection s1).incomingShape == some (.node n1))
  check "s44 outgoing shape" ((m.g.edgeSection s44).outgoingShape == some (.node n2))
  check "s1 outgoing sections" ((m.g.edgeSection s1).outgoingSections == #[s44])
  check "s44 incoming sections" ((m.g.edgeSection s44).incomingSections == #[s1])
  checkFloat "s1 start x" (m.g.edgeSection s1).startX 1.0
  checkFloat "s44 end y" (m.g.edgeSection s44).endY 4.0
  -- preserve_section_ids (no layout; the section survives the transfer)
  let text := "
    {
      id: \"root\",
      properties: {
        'elk.algorithm': 'random'
      },
      children: [
        { id: \"n1\", width: 10, height: 10 },
        { id: \"n2\", width: 10, height: 10 }
      ],
      edges: [{
        id: \"e1\", sources: [ \"n1\" ], targets: [ \"n2\" ],
        sections: [{
          id: \"xyz\",
          startPoint: { x: 0, y: 0 },
          bendPoints: [{ x: 20, y: 0 }],
          endPoint: { x: 50, y: 0 }
        }]
      }]
    }"
  let m ← importText text
  let xyz := sectionById m.g "xyz"
  check "preserve_section_ids identifier" (xyz.idx < m.g.sections.size)
  checkEq "xyz bend points" (m.g.edgeSection xyz).bendPoints.size 1
  let s := (← transfer m m.g).render
  check "preserve_section_ids serialized" (has s "\"id\":\"xyz\"")
  -- do_not_add_empty_sections_array_*
  let s ← jsonAndBack "
    {
      id: \"root\",
      children: [
        { id: \"n1\", width: 10, height: 10 },
        { id: \"n2\", width: 10, height: 10 }
      ],
      edges: [{ id: \"e1\", sources: [ \"n1\" ], targets: [ \"n2\" ] }]
    }"
  check "do_not_add_empty_sections_array_extended_edge" (!has s "\"sections\"")
  let s ← jsonAndBack "
    {
      id: \"root\",
      children: [
        { id: \"n1\", width: 10, height: 10 },
        { id: \"n2\", width: 10, height: 10 }
      ],
      edges: [{ id: \"e1\", source: \"n1\", target: \"n2\" }]
    }"
  check "do_not_add_empty_sections_array_primitive_edge" (!has s "\"sections\"")
  -- primitive edge layout members become one section with the default shapes
  let m ← importText "{id:'r', children:[{id:'a'},{id:'b'}], edges:[{id:'e', source:'a', target:'b',
      sourcePoint:{x:1,y:2}, targetPoint:{x:3,y:4}, bendPoints:[{x:5,y:6}]}]}"
  let e := (m.g.node m.root).containedEdges[0]!
  checkEq "primitive section count" (m.g.edge e).sections.size 1
  let sec := m.g.edgeSection (m.g.edge e).sections[0]!
  checkFloat "primitive start x" sec.startX 1.0
  checkFloat "primitive start y" sec.startY 2.0
  checkFloat "primitive end x" sec.endX 3.0
  checkFloat "primitive end y" sec.endY 4.0
  checkEq "primitive bend count" sec.bendPoints.size 1
  let err ← importError "{id:'r', children:[{id:'a'},{id:'b'}], edges:[{id:'e', sources:['a'], targets:['b'], sections:[{id:'s'}]}]}"
  check "section without start point fails" (has (err.getD "") "All edge sections need a start point.")

/-! ### id_test.rs -/

/-- Rust `id_test.rs`: `test_no_id`, `test_wrong_id_type_*`, `test_good_id_*`. -/
def idTests : Suite := suite "json.import.ids" do
  for (name, text) in #[("test_no_id", "{}"), ("test_wrong_id_type_number", "{ id: 1.2 }"),
                        ("test_wrong_id_type_object", "{ id: {} }"), ("test_wrong_id_type_array", "{ id: [] }"),
                        ("test_wrong_id_type_boolean", "{ id: true }")] do
    let e ← importError text
    check name e.isSome
    check s!"{name} is JsonImportException" ((e.getD "").startsWith jsonImportExceptionClass)
  check "test_good_id_string" ((← importError "{ id: 'foo' }").isNone)
  check "test_good_id_int" ((← importError "{ id: 3 }").isNone)
  let m ← importText "{ id: 3 }"
  checkEq "int id becomes identifier string" (m.g.node m.root).identifier (some "3")
  check "good_id_string registered" (m.st.nodeIdMap.get? (JsonId.int 3) == some m.root)
  let e ← importError "{ id: 1.2 }"
  check "wrong id message" (has (e.getD "") "Id must be a string or an integer: '1.2'.")

/-! ### layout_options_test.rs -/

/-- Rust `layout_options_test.rs` import tests. -/
def layoutOptionImportTests : Suite := suite "json.import.layoutOptions" do
  -- edge_label_placement_option_parses_enum
  let m ← importText "
    {
      \"id\": \"root\",
      \"children\": [{\"id\": \"n1\"}, {\"id\": \"n2\"}],
      \"edges\": [
        {\"id\": \"e1\",
         \"source\": \"n1\",
         \"target\": \"n2\",
         \"labels\": [
           {\"text\": \"tail\", \"layoutOptions\": {\"org.eclipse.elk.edgeLabels.placement\": \"TAIL\"}}
         ]
        }
      ]
    }"
  let edges := (m.g.node m.root).containedEdges
  checkEq "edge label edges" edges.size 1
  let labels := (m.g.edge edges[0]!).labels
  checkEq "edge label count" labels.size 1
  check "edge_label_placement_option_parses_enum"
    ((m.g.label labels[0]!).props.get? CoreOptions.EDGE_LABELS_PLACEMENT == some EdgeLabelPlacement.tail)
  checkEq "label text" (m.g.label labels[0]!).text "tail"
  -- import_layout_options
  let m ← importText "{\"id\": \"root\", \"layoutOptions\": {\"elk.direction\": \"DOWN\"}}"
  check "import_layout_options has" ((m.g.node m.root).props.has CoreOptions.DIRECTION)
  check "import_layout_options value" ((m.g.node m.root).props.get? CoreOptions.DIRECTION == some Direction.down)
  -- import_label_layout_options_node_labels_placement
  let m ← importText "
    {
      \"id\": \"root\",
      \"children\": [
        {
          \"id\": \"n1\",
          \"labels\": [
            {
              \"id\": \"l1\",
              \"text\": \"Node Label\",
              \"layoutOptions\": {
                \"nodeLabels.placement\": \"[H_CENTER, V_TOP, INSIDE]\"
              },
              \"width\": 40.0,
              \"height\": 15.0
            }
          ]
        }
      ]
    }"
  let n1 := nodeById m.g "n1"
  let labels := (m.g.node n1).labels
  checkEq "node labels count" labels.size 1
  match (m.g.label labels[0]!).props.get? CoreOptions.NODE_LABELS_PLACEMENT with
  | some placement =>
    check "label placement H_CENTER" (placement.contains .hCenter)
    check "label placement V_TOP" (placement.contains .vTop)
    check "label placement INSIDE" (placement.contains .inside)
    checkEq "label placement size" placement.size 3
  | none => check "label-level nodeLabels.placement should be parsed" false
  checkEq "label identifier" (m.g.label labels[0]!).identifier (some "l1")
  checkFloat "label width" (m.g.label labels[0]!).width 40.0
  checkFloat "label height" (m.g.label labels[0]!).height 15.0
  -- import_node_size_constraints_enumset
  let m ← importText "
    {
      \"id\": \"root\",
      \"children\": [
        {
          \"id\": \"n1\",
          \"layoutOptions\": {
            \"org.eclipse.elk.nodeSize.constraints\": \"[PORTS, PORT_LABELS, NODE_LABELS, MINIMUM_SIZE]\"
          }
        }
      ]
    }"
  match (m.g.node (nodeById m.g "n1")).props.get? CoreOptions.NODE_SIZE_CONSTRAINTS with
  | some c =>
    check "PORTS present" (c.contains .ports)
    check "PORT_LABELS present" (c.contains .portLabels)
    check "NODE_LABELS present" (c.contains .nodeLabels)
    check "MINIMUM_SIZE present" (c.contains .minimumSize)
  | none => check "node size constraints should parse" false
  -- import_properties_legacy
  let m ← importText "{\"id\": \"root\", \"properties\": {\"elk.direction\": \"DOWN\"}}"
  check "import_properties_legacy has" ((m.g.node m.root).props.has CoreOptions.DIRECTION)
  check "import_properties_legacy value" ((m.g.node m.root).props.get? CoreOptions.DIRECTION == some Direction.down)
  -- layout_options_have_priority
  let m ← importText "{\"id\": \"root\", \"layoutOptions\": {\"elk.direction\": \"UP\"}, \"properties\": {\"elk.direction\": \"DOWN\"}}"
  check "layout_options_have_priority" ((m.g.node m.root).props.get? CoreOptions.DIRECTION == some Direction.up)
  -- import_layout_options_kvector_and_chain
  let m ← importText "
    {
      \"id\": \"root\",
      \"children\": [
        {
          \"id\": \"n1\",
          \"layoutOptions\": { \"position\": \"(1,2)\" }
        }
      ],
      \"edges\": [
        {
          \"id\": \"e1\",
          \"sources\": [ \"n1\" ],
          \"targets\": [ \"n1\" ],
          \"layoutOptions\": { \"bendPoints\": \"(0,0; 10,10)\" }
        }
      ]
    }"
  match (m.g.node (nodeById m.g "n1")).props.get? CoreOptions.POSITION with
  | some p => checkVec "position option" p 1.0 2.0
  | none => check "position option" false
  let e := (m.g.node m.root).containedEdges[0]!
  match (m.g.edge e).props.get? CoreOptions.BEND_POINTS with
  | some b =>
    checkEq "bend points length" b.size 2
    checkVec "bend 0" b[0]! 0.0 0.0
    checkVec "bend 1" b[1]! 10.0 10.0
  | none => check "bendPoints option" false
  -- import_layout_options_port_and_label_position
  let m ← importText "
    {
      \"id\": \"root\",
      \"children\": [
        {
          \"id\": \"n1\",
          \"ports\": [
            { \"id\": \"p1\", \"layoutOptions\": { \"position\": \"(7,8)\" } }
          ],
          \"labels\": [
            { \"text\": \"L1\", \"layoutOptions\": { \"position\": \"(9,10)\" } }
          ]
        }
      ]
    }"
  let n1 := nodeById m.g "n1"
  match (m.g.port (m.g.node n1).ports[0]!).props.get? CoreOptions.POSITION with
  | some p => checkVec "port position" p 7.0 8.0
  | none => check "port position" false
  match (m.g.label (m.g.node n1).labels[0]!).props.get? CoreOptions.POSITION with
  | some p => checkVec "label position" p 9.0 10.0
  | none => check "label position" false
  -- direction option accepts ordinals and lower case names (parse_direction_option)
  check "direction ordinal" (JsonImporter.parseDirectionOption "1" == some Direction.right)
  check "direction lower case" (JsonImporter.parseDirectionOption " down " == some Direction.down)
  check "direction junk" (JsonImporter.parseDirectionOption "sideways" == none)
  -- unknown options and unparsable values are ignored
  let m ← importText "{\"id\":\"root\",\"layoutOptions\":{\"foo.bar\":\"x\",\"elk.direction\":\"SIDEWAYS\"}}"
  check "unknown option ignored" ((m.g.node m.root).props.isEmpty)

/-! ### individual_spacings_test.rs -/

/-- Rust `individual_spacings_test.rs`. -/
def individualSpacingTests : Suite := suite "json.individualSpacings" do
  Elk.Api.ensureInitialized
  -- import_individual_spacings
  let m ← importText "
    {
      \"id\": \"n0\",
      \"children\": [
        {
          \"id\": \"outer\",
          \"layoutOptions\": {
              \"nodeLabels.padding\": \"[top=0.0,left=0.0,bottom=0.0,right=0.0]\"
          },
          \"children\": [
            {
              \"id\": \"i1\",
              \"labels\": [
                { \"text\": \"Node 1\", \"width\": 40.0, \"height\": 15.0 }
              ],
              \"layoutOptions\": { \"nodeLabels.placement\": \"[H_CENTER, V_TOP, INSIDE]\" },
              \"width\": 60.0,
              \"height\": 40.0
            },
            {
              \"id\": \"i2\",
              \"layoutOptions\": { \"nodeLabels.placement\": \"[H_CENTER, V_TOP, INSIDE]\" },
              \"individualSpacings\": {
                \"nodeLabels.padding\": \"[top=10.0,left=0.0,bottom=0.0,right=0.0]\"
              },
              \"labels\": [
                { \"text\": \"Node 2\", \"width\": 40.0, \"height\": 15.0 }
              ],
              \"width\": 60.0,
              \"height\": 40.0
            }
          ]
        }
      ]
    }"
  let i1 := nodeById m.g "i1"
  let i2 := nodeById m.g "i2"
  check "i1 has no individual spacings" (!(m.g.node i1).props.has CoreOptions.SPACING_INDIVIDUAL)
  check "i2 has individual spacings" ((m.g.node i2).props.has CoreOptions.SPACING_INDIVIDUAL)
  match (m.g.node i2).props.get? CoreOptions.SPACING_INDIVIDUAL with
  | some ind =>
    check "individual has NODE_LABELS_PADDING" (ind.props.has CoreOptions.NODE_LABELS_PADDING)
    match ind.props.get? CoreOptions.NODE_LABELS_PADDING with
    | some p =>
      checkFloat "padding top" p.top 10.0
      checkFloat "padding left" p.left 0.0
    | none => check "padding parse" false
  | none => check "individual spacings of i2" false
  check "outer has nodeLabels.padding directly" ((m.g.node (nodeById m.g "outer")).props.has CoreOptions.NODE_LABELS_PADDING)
  -- import_individual_spacings_with_ports_surrounding
  let m ← importText "
    {
      \"id\": \"n0\",
      \"children\": [
        {
          \"id\": \"n1\",
          \"individualSpacings\": {
            \"spacing.portsSurrounding\": \"[top=2.0,left=8.0,bottom=6.0,right=4.0]\"
          }
        }
      ]
    }"
  match (m.g.node (nodeById m.g "n1")).props.get? CoreOptions.SPACING_INDIVIDUAL with
  | some ind =>
    match ind.props.get? CoreOptions.SPACING_PORTS_SURROUNDING with
    | some margin => check "portsSurrounding margin" (margin == { top := 2.0, right := 4.0, bottom := 6.0, left := 8.0 : ElkMargin })
    | none => check "portsSurrounding" false
  | none => check "individual spacings" false
  -- export_individual_spacings
  let (g, root) := ElkGraphUtil.createGraph
  let g := setNodeProp g root CoreOptions.SPACING_NODE_NODE 10.0
  let ind : IndividualSpacings := { props := ({} : PropertyMap).set CoreOptions.SPACING_NODE_NODE 20.0 }
  let g := setNodeProp g root CoreOptions.SPACING_INDIVIDUAL ind
  let json ← exportGraph g root
  check "export has individualSpacings" (has json "individualSpacings")
  check "export has nodeNode" (has json "nodeNode")
  check "export has 10" (has json "10")
  check "export has 20" (has json "20")
  -- export_individual_spacings_with_padding
  let (g, root) := ElkGraphUtil.createGraph
  let pad : ElkPadding := { top := 1.0, right := 2.0, bottom := 3.0, left := 4.0 }
  let ind : IndividualSpacings := { props := ({} : PropertyMap).set CoreOptions.NODE_LABELS_PADDING pad }
  let json ← exportGraph (setNodeProp g root CoreOptions.SPACING_INDIVIDUAL ind) root
  check "padding individualSpacings" (has json "individualSpacings")
  check "padding key" (has json "elk.nodeLabels.padding")
  check "padding value" (has json "[top=1,left=4,bottom=3,right=2]")
  -- export_individual_spacings_with_ports_surrounding
  let (g, root) := ElkGraphUtil.createGraph
  let margin : ElkMargin := { top := 2.0, right := 4.0, bottom := 6.0, left := 8.0 }
  let ind : IndividualSpacings := { props := ({} : PropertyMap).set CoreOptions.SPACING_PORTS_SURROUNDING margin }
  let json ← exportGraph (setNodeProp g root CoreOptions.SPACING_INDIVIDUAL ind) root
  check "ports surrounding individualSpacings" (has json "individualSpacings")
  check "ports surrounding key" (has json "elk.spacing.portsSurrounding")
  check "ports surrounding value" (has json "[top=2,left=8,bottom=6,right=4]")
  -- export_no_individual_spacings
  let (g, root) := ElkGraphUtil.createGraph
  let json ← exportGraph g root
  check "no individualSpacings" (!has json "individualSpacings")
  check "no IndividualSpacings" (!has json "IndividualSpacings")

/-! ### export_test.rs and the export tests of layout_options_test.rs -/

/-- Rust `export_test.rs` and `export_*` tests of `layout_options_test.rs`. -/
def exportTests : Suite := suite "json.export" do
  Elk.Api.ensureInitialized
  -- export_portless_edge
  let (g, root) := ElkGraphUtil.createGraph
  let (g, n1) := g.createNode (some root)
  let (g, n2) := g.createNode (some root)
  let (g, _) := ElkGraphUtil.createSimpleEdge g (.node n1) (.node n2)
  let json ← exportGraph g root
  check "export_portless_edge" (has json "\"edges\"")
  -- export_unique_ids
  let (g, root) := ElkGraphUtil.createGraph
  let (g, n1) := g.createNode (some root)
  let (g, n2) := g.createNode (some root)
  let g := g.modifyNode n1 fun n => { n with identifier := some "foo" }
  let g := g.modifyNode n2 fun n => { n with identifier := some "foo" }
  let json ← exportGraph g root
  check "export_unique_ids" (has json "foo_g")
  -- export_ids_increasing
  let (g, root) := ElkGraphUtil.createGraph
  let (g, _) := g.createNode (some root)
  let (g, n2) := g.createNode (some root)
  let g := g.modifyNode n2 fun n => { n with identifier := some "foo" }
  let (g, _) := g.createNode (some root)
  let json ← exportGraph g root
  check "ids increasing n1" (has json "n1")
  check "ids increasing foo" (has json "foo")
  check "ids increasing n2" (has json "n2")
  check "ids increasing no n3" (!has json "n3")
  -- export_omit_unknown_properties
  let (g, root) := ElkGraphUtil.createGraph
  let g := setNodeProp g root CoreOptions.DIRECTION Direction.right
  let dummy : Property Int := Property.mk' "foo.bar.dummy"
  let g := setNodeProp g root dummy 0
  let json1 ← exportGraph g root { omitUnknownLayoutOptions := true }
  check "omit unknown: direction" (has json1 "direction")
  check "omit unknown: no dummy" (!has json1 "foo.bar.dummy")
  let json2 ← exportGraph g root { omitUnknownLayoutOptions := false }
  check "keep unknown: direction" (has json2 "direction")
  check "keep unknown: dummy" (has json2 "foo.bar.dummy")
  -- export_dont_write_empty_junction_points
  let (g, root) := ElkGraphUtil.createGraph
  let (g, n1) := g.createNode (some root)
  let (g, n2) := g.createNode (some root)
  let (g, _) := ElkGraphUtil.createSimpleEdge g (.node n1) (.node n2)
  let json ← exportGraph g root { omitLayout := false }
  check "no layoutOptions" (!has json "layoutOptions")
  check "no junctionPoints" (!has json "junctionPoints")
  -- export_junction_points
  let (g, root) := ElkGraphUtil.createGraph
  let (g, n1) := g.createNode (some root)
  let (g, n2) := g.createNode (some root)
  let (g, e) := ElkGraphUtil.createSimpleEdge g (.node n1) (.node n2)
  let g := setEdgeProp g e CoreOptions.JUNCTION_POINTS #[⟨1.0, 2.0⟩, ⟨3.0, 4.0⟩]
  let v ← JsonExporter.exportValue g root { omitLayout := false }
  checkJunctions "export_junction_points" ((v.get? "edges").bind (·.getArr?) |>.bind (·[0]?)) #[(1.0, 2.0), (3.0, 4.0)]
  -- export_layout_options
  let (g, root) := ElkGraphUtil.createGraph
  let g := setNodeProp g root CoreOptions.DIRECTION Direction.up
  let v ← JsonExporter.exportValue g root
  let expected ← parseLenient "{\"id\":\"n0\",\"layoutOptions\":{\"elk.direction\":\"UP\"}}"
  check "export_layout_options" (v == expected)
  checkEq "export_layout_options render" v.render "{\"id\":\"n0\",\"layoutOptions\":{\"elk.direction\":\"UP\"}}"
  -- export_layout_options_kvector_and_chain
  let (g, root) := ElkGraphUtil.createGraph
  let (g, n1) := g.createNode (some root)
  let (g, n2) := g.createNode (some root)
  let g := g.modifyNode n1 fun n => { n with identifier := some "n1" }
  let g := g.modifyNode n2 fun n => { n with identifier := some "n2" }
  let g := setNodeProp g n1 CoreOptions.POSITION (⟨3.0, 4.0⟩ : KVector)
  let (g, e) := ElkGraphUtil.createSimpleEdge g (.node n1) (.node n2)
  let g := setEdgeProp g e CoreOptions.BEND_POINTS #[⟨0.0, 0.0⟩, ⟨10.0, 10.0⟩]
  let v ← JsonExporter.exportValue g root
  let child := byId (v.get? "children") "n1"
  let posStr := ((child.bind (·.getAt [.key "layoutOptions", .key "elk.position"])).bind (·.getStr?)).getD ""
  match parseVec? posStr with
  | some p => checkVec "exported position" p 3.0 4.0
  | none => check s!"exported position parses ({posStr})" false
  let bendStr := ((((v.get? "edges").bind (·.getArr?)).bind (·[0]?)).bind (·.getAt [.key "layoutOptions", .key "elk.bendPoints"])).bind (·.getStr?)
  match bendStr.bind parseChain? with
  | some b =>
    checkEq "exported bends length" b.size 2
    checkVec "exported bend 0" b[0]! 0.0 0.0
    checkVec "exported bend 1" b[1]! 10.0 10.0
  | none => check s!"exported bendPoints parse ({bendStr})" false
  -- export_layout_options_port_and_label_position
  let (g, root) := ElkGraphUtil.createGraph
  let (g, node) := g.createNode (some root)
  let (g, port) := g.createPort (some node)
  let (g, label) := g.createLabel (some (.node node)) "L1"
  let g := g.modifyProps (.port port) (·.set CoreOptions.POSITION (⟨7.0, 8.0⟩ : KVector))
  let g := g.modifyProps (.label label) (·.set CoreOptions.POSITION (⟨9.0, 10.0⟩ : KVector))
  let v ← JsonExporter.exportValue g root
  let child := (v.get? "children").bind (·.getArr?) |>.bind (·[0]?)
  let ps := ((child.bind (·.getAt [.key "ports", .idx 0, .key "layoutOptions", .key "elk.position"])).bind (·.getStr?)).getD ""
  let ls := ((child.bind (·.getAt [.key "labels", .idx 0, .key "layoutOptions", .key "elk.position"])).bind (·.getStr?)).getD ""
  match parseVec? ps with
  | some p => checkVec "exported port position" p 7.0 8.0
  | none => check s!"exported port position parses ({ps})" false
  match parseVec? ls with
  | some p => checkVec "exported label position" p 9.0 10.0
  | none => check s!"exported label position parses ({ls})" false
  checkEq "exported label text" ((child.bind (·.getAt [.key "labels", .idx 0, .key "text"])).bind (·.getStr?)) (some "L1")
  -- pretty printing option
  let (g, root) := ElkGraphUtil.createGraph
  let pretty ← exportGraph g root { prettyPrint := true }
  checkEq "pretty export" pretty "{\n  \"id\": \"n0\"\n}"

/-! ### transfer_layout_test.rs -/

/-- Rust `transfer_layout_test.rs` (tests adapted to set the geometry directly). -/
def transferTests : Suite := suite "json.transfer" do
  Elk.Api.ensureInitialized
  let basic := "
    {
      \"id\": \"root\",
      \"properties\": {
        \"algorithm\": \"random\",
        \"direction\": \"DOWN\"
      },
      \"children\": [{\"id\": \"n1\", \"width\": 40, \"height\": 40},
                  {\"id\": \"n2\", \"width\": 40, \"height\": 40}],
      \"edges\": [{\"id\": \"e1\", \"source\": \"n1\", \"target\": \"n2\"}]
    }"
  -- transfer_layout_ok
  let m ← importText basic
  let v ← transfer m m.g
  check "transfer_layout_ok" v.isObj
  -- transfer_layout_fail_when_graph_changes
  let m ← importText basic
  let (g, _) := ElkGraphUtil.createNode m.g (some m.root)
  let failed ← (do let _ ← transfer m g; pure false) <|> pure true
  check "transfer_layout_fail_when_graph_changes" failed
  -- transfer writes x/y/width/height (adapted from transfer_layout_edge_sections_exist)
  let m ← importText basic
  let n1 := nodeById m.g "n1"
  let n2 := nodeById m.g "n2"
  let g := setLoc m.g n1 12.0 12.0
  let g := setLoc g n2 12.0 82.5
  let v ← transfer m g
  for id in #["n1", "n2"] do
    let c := byId (v.get? "children") id
    check s!"{id} has x" (num? (c.bind (·.get? "x"))).isSome
    check s!"{id} has y" (num? (c.bind (·.get? "y"))).isSome
  let c2 := byId (v.get? "children") "n2"
  checkEq "n2 x" (num? (c2.bind (·.get? "x"))) (some 12.0)
  checkEq "n2 y" (num? (c2.bind (·.get? "y"))) (some 82.5)
  check "integral coordinate is an integer" ((c2.bind (·.get? "x")) == some (.num (.int 12)))
  check "fractional coordinate is a double" ((c2.bind (·.get? "y")) == some (.num (.float 82.5)))
  checkEq "n2 width" (num? (c2.bind (·.get? "width"))) (some 40.0)
  checkEq "n2 height" (num? (c2.bind (·.get? "height"))) (some 40.0)
  -- sections written for an edge that has a section in the arena
  let e := (m.g.node m.root).containedEdges[0]!
  let (g, sec) := g.createSection (some e)
  let g := g.modifySection sec fun s =>
    { s with startX := 52.0, startY := 32.0, endX := 12.0, endY := 82.5, incomingShape := some (.node n1), outgoingShape := some (.node n2) }
  let g := ElkGraphUtil.createBendPoint g sec 30.0 40.0
  let v ← transfer m g
  let edge := byId (v.get? "edges") "e1"
  let sections := (edge.bind (·.get? "sections")).bind (·.getArr?)
  checkEq "edge section count" (sections.map (·.size)) (some 1)
  let s0 := sections.bind (·[0]?)
  check "section has id" ((s0.bind (·.get? "id")).isSome)
  checkEq "section start x" (num? (s0.bind (·.getAt [.key "startPoint", .key "x"]))) (some 52.0)
  checkEq "section end y" (num? (s0.bind (·.getAt [.key "endPoint", .key "y"]))) (some 82.5)
  checkEq "section bend x" (num? (s0.bind (·.getAt [.key "bendPoints", .idx 0, .key "x"]))) (some 30.0)
  checkEq "section incomingShape" ((s0.bind (·.get? "incomingShape"))) (some (.str "n1"))
  checkEq "section outgoingShape" ((s0.bind (·.get? "outgoingShape"))) (some (.str "n2"))
  check "edge has container" ((edge.bind (·.get? "container")).isSome)
  checkEq "edge container is root" ((edge.bind (·.get? "container"))) (some (.str "root"))
  -- transfer_layout_compensates_fixed_order_vertical_port_surrounding_height
  let m ← importText "
    {
      \"id\": \"root\",
      \"children\": [
        {
          \"id\": \"N1\",
          \"layoutOptions\": {
            \"org.eclipse.elk.portConstraints\": \"FIXED_ORDER\",
            \"org.eclipse.elk.nodeSize.constraints\": \"[PORTS, PORT_LABELS, NODE_LABELS, MINIMUM_SIZE]\"
          },
          \"ports\": [
            { \"id\": \"P1\", \"layoutOptions\": { \"org.eclipse.elk.port.side\": \"EAST\" } },
            { \"id\": \"P2\", \"layoutOptions\": { \"org.eclipse.elk.port.side\": \"EAST\" } },
            { \"id\": \"P3\", \"layoutOptions\": { \"org.eclipse.elk.port.side\": \"EAST\" } }
          ]
        }
      ]
    }"
  let n1 := nodeById m.g "N1"
  let g := m.g.modifyNode n1 fun n => { n with x := 12.0, y := 12.0, width := 20.0, height := 20.0 }
  let mut gp := g
  let ps := (m.g.node n1).ports
  checkEq "N1 ports" ps.size 3
  for (p, y) in ps.zip #[10.0, 20.0, 30.0] do
    gp := gp.modifyProps (.port p) (·.set CoreOptions.PORT_SIDE PortSide.east)
    gp := gp.modifyPort p fun pt => { pt with x := 20.0, y, width := 0.0, height := 0.0 }
  let v ← transfer m gp
  checkEq "fixed order port surrounding height" (num? ((byId (v.get? "children") "N1").bind (·.get? "height"))) (some 40.0)
  -- transfer_layout_writes_junction_points
  let m ← importText basic
  let e := (m.g.node m.root).containedEdges[0]!
  let g := setEdgeProp m.g e CoreOptions.JUNCTION_POINTS #[⟨1.0, 2.0⟩, ⟨3.0, 4.0⟩]
  let v ← transfer m g
  checkJunctions "transfer_layout_writes_junction_points" ((v.get? "edges").bind (·.getArr?) |>.bind (·[0]?)) #[(1.0, 2.0), (3.0, 4.0)]
  -- transfer_layout_shape_coords_root
  let m ← importText "
    {
      \"id\": \"root\",
      \"children\": [
        {
          \"id\": \"parent\",
          \"layoutOptions\": { \"shapeCoords\": \"ROOT\" },
          \"children\": [
            { \"id\": \"child\" }
          ]
        }
      ]
    }"
  let g := setLoc m.g m.root 0.0 0.0
  let g := setLoc g (nodeById m.g "parent") 10.0 20.0
  let g := setLoc g (nodeById m.g "child") 5.0 6.0
  let v ← transfer m g
  let parent := byId (v.get? "children") "parent"
  let child := byId (parent.bind (·.get? "children")) "child"
  checkEq "shape_coords_root child x" (num? (child.bind (·.get? "x"))) (some 15.0)
  checkEq "shape_coords_root child y" (num? (child.bind (·.get? "y"))) (some 26.0)
  checkEq "shape_coords_root parent x" (num? (parent.bind (·.get? "x"))) (some 10.0)
  -- transfer_layout_edge_coords_root
  let m ← importText "
    {
      \"id\": \"root\",
      \"layoutOptions\": { \"edgeCoords\": \"ROOT\" },
      \"children\": [
        {
          \"id\": \"parent\",
          \"children\": [
            { \"id\": \"n1\" },
            { \"id\": \"n2\" }
          ]
        }
      ],
      \"edges\": [
        { \"id\": \"e1\", \"source\": \"n1\", \"target\": \"n2\" }
      ]
    }"
  let parent := nodeById m.g "parent"
  let edges := (m.g.node parent).containedEdges
  checkEq "edge_coords_root parent edges" edges.size 1
  let g := setLoc m.g m.root 0.0 0.0
  let g := setLoc g parent 100.0 50.0
  let g := setEdgeProp g edges[0]! CoreOptions.JUNCTION_POINTS #[⟨10.0, 20.0⟩, ⟨30.0, 40.0⟩]
  let v ← transfer m g
  checkJunctions "transfer_layout_edge_coords_root" (byId (v.get? "edges") "e1") #[(110.0, 70.0), (130.0, 90.0)]
  -- transfer_layout_edge_coords_parent
  let m ← importText "
    {
      \"id\": \"root\",
      \"children\": [
        {
          \"id\": \"a\",
          \"layoutOptions\": { \"edgeCoords\": \"PARENT\" },
          \"children\": [
            { \"id\": \"n1\" }
          ],
          \"edges\": [
            { \"id\": \"e1\", \"source\": \"n1\", \"target\": \"n2\" }
          ]
        },
        {
          \"id\": \"b\",
          \"children\": [
            { \"id\": \"n2\" }
          ]
        }
      ]
    }"
  let a := nodeById m.g "a"
  let edges := (m.g.node m.root).containedEdges
  checkEq "edge_coords_parent root edges" edges.size 1
  let g := setLoc m.g m.root 0.0 0.0
  let g := setLoc g a 100.0 50.0
  let g := setEdgeProp g edges[0]! CoreOptions.JUNCTION_POINTS #[⟨120.0, 70.0⟩, ⟨150.0, 80.0⟩]
  let v ← transfer m g
  let aObj := byId (v.get? "children") "a"
  checkJunctions "transfer_layout_edge_coords_parent" (byId (aObj.bind (·.get? "edges")) "e1") #[(20.0, 20.0), (50.0, 30.0)]
  -- transfer without the importer's root fails like elk-rs' "No input model available."
  let failed ← (do
      let ((_, _), _) ← (ImportM.run JsonImporter.transferLayout {}).run {}
      pure false) <|> pure true
  check "transfer without import fails" failed

/-! ### json_importer.rs :: metadata_cache_tests -/

/-- Rust `metadata_cache_tests` (`set_option` behaviour, defaults scope and release). -/
def metadataCacheTests : Suite := suite "json.import.defaults" do
  Elk.Api.ensureInitialized
  let g0 : ElkGraph := {}
  let setOpt (props : PropertyMap) (id value : String) : IO (PropertyMap × ImporterState) := do
    let ((p, st), _) ← (ImportM.run (JsonImporter.setOption props id value) {}).run g0
    return (p, st)
  -- only_immutable_option_values_are_shared_and_caches_reset_per_transform
  let act : ImportM (Array PropertyMap) := do
    let mut out := #[]
    for v in #["12", "23", "34", "12"] do
      out := out.push (← JsonImporter.setOption {} "elk.spacing.nodeNode" v)
    return out
  let ((props, st), _) ← (ImportM.run act {}).run g0
  for (p, expected) in props.zip #[12.0, 23.0, 34.0, 12.0] do
    checkEq "setOption nodeNode" (p.get? CoreOptions.SPACING_NODE_NODE) (some expected)
  checkEq "option cache size" st.optionCache.size 1
  let act : ImportM PropertyMap := do
    let p ← JsonImporter.setOption {} "elk.spacing.nodeNode" "invalid"
    JsonImporter.setOption p "unknown.option" "ignored"
  let ((invalid, st), _) ← (ImportM.run act {}).run g0
  check "invalid and unknown ignored" invalid.isEmpty
  checkEq "misses are cached too" st.optionCache.size 2
  let (p, _) ← setOpt {} "elk.edgeRouting" "ORTHOGONAL"
  check "edgeRouting ORTHOGONAL" (p.get? CoreOptions.EDGE_ROUTING == some EdgeRouting.orthogonal)
  let (p, _) ← setOpt {} "elk.edgeRouting" "POLYLINE"
  check "edgeRouting POLYLINE" (p.get? CoreOptions.EDGE_ROUTING == some EdgeRouting.polyline)
  let act : ImportM PropertyMap := do
    let p ← JsonImporter.setOption {} "elk.port.index" "12"
    let p ← JsonImporter.setOption p "elk.spacing.nodeNode" "12"
    let p ← JsonImporter.setOption p "elk.algorithm" "12"
    JsonImporter.setOption p "elk.separateConnectedComponents" "true"
  let ((p, _), _) ← (ImportM.run act {}).run g0
  checkEq "port.index 12" (p.get? CoreOptions.PORT_INDEX) (some 12)
  checkEq "nodeNode 12" (p.get? CoreOptions.SPACING_NODE_NODE) (some 12.0)
  checkEq "algorithm 12" (p.get? CoreOptions.ALGORITHM) (some "12")
  checkEq "separateConnectedComponents" (p.get? CoreOptions.SEPARATE_CONNECTED_COMPONENTS) (some true)
  -- the cache is dropped by the next transform
  let ((_, st), _) ← (ImportM.run (do
      let _ ← JsonImporter.setOption {} "elk.spacing.nodeNode" "1"
      JsonImporter.transform (.obj #[("id", .str "next")])) {}).run g0
  check "cache reset per transform" st.optionCache.isEmpty
  -- shared_defaults_are_released_on_success_error_and_unwind
  let defaults ← match ← GlobalOptions.parse "{\"elk.spacing.nodeNode\":35}" with
    | .ok d => pure d
    | .error e => throw (IO.userError e)
  let (root, _, g) ← importGraph (.obj #[("id", .str "root")]) (some defaults)
  checkEq "defaults applied to root" ((g.node root).props.get? CoreOptions.SPACING_NODE_NODE) (some 35.0)
  let failed ← (do let _ ← importGraph .null (some defaults); pure false) <|> pure true
  check "import of null with defaults fails" failed
  let (next, st, g) ← importGraph (.obj #[("id", .str "next")])
  check "defaults are not carried into the next import" (!(g.node next).props.has CoreOptions.SPACING_NODE_NODE)
  check "no defaults in plain import" st.defaults.isNone
  -- shared_defaults_preserve_element_scope_and_release_only_import_scratch
  let defaults ← match ← GlobalOptions.parse "{\"elk.spacing.nodeNode\":35,\"unknown.option\":\"ignored\"}" with
    | .ok d => pure d
    | .error e => throw (IO.userError e)
  let doc ← parseLenient "{
      \"id\":\"root\",
      \"individualSpacings\":{\"elk.spacing.edgeEdge\":7},
      \"children\":[{\"id\":\"a\",\"ports\":[{\"id\":\"p\"}],\"labels\":[{\"text\":\"A\"}]},{\"id\":\"b\"}],
      \"edges\":[{\"id\":\"ab\",\"sources\":[\"a\"],\"targets\":[\"b\"],
          \"sections\":[{\"id\":\"s\",\"startPoint\":{\"x\":0,\"y\":0},\"endPoint\":{\"x\":1,\"y\":1}}]}]
  }"
  let (root, st, g) ← importGraph doc (some defaults)
  check "model children keep no layoutOptions" (((doc.getAt [.key "children", .idx 0]).bind (·.get? "layoutOptions")).isNone)
  check "importer model untouched" (st.model == doc)
  let child := (g.node root).children[0]!
  let port := (g.node child).ports[0]!
  let label := (g.node child).labels[0]!
  let edge := (g.node root).containedEdges[0]!
  checkEq "root nodeNode" ((g.node root).props.get? CoreOptions.SPACING_NODE_NODE) (some 35.0)
  checkEq "child nodeNode" ((g.node child).props.get? CoreOptions.SPACING_NODE_NODE) (some 35.0)
  checkEq "port nodeNode" ((g.port port).props.get? CoreOptions.SPACING_NODE_NODE) (some 35.0)
  checkEq "label nodeNode" ((g.label label).props.get? CoreOptions.SPACING_NODE_NODE) (some 35.0)
  checkEq "edge nodeNode" ((g.edge edge).props.get? CoreOptions.SPACING_NODE_NODE) (some 35.0)
  let sec := (g.edge edge).sections[0]!
  check "section has no nodeNode" (!(g.edgeSection sec).props.has CoreOptions.SPACING_NODE_NODE)
  match (g.node root).props.get? CoreOptions.SPACING_INDIVIDUAL with
  | some ind =>
    checkEq "individual edgeEdge" (ind.props.get? CoreOptions.SPACING_EDGE_EDGE) (some 7.0)
    check "individual has no nodeNode" (!ind.props.has CoreOptions.SPACING_NODE_NODE)
  | none => check "individual spacings of root" false
  check "importer maps survive" (st.nodeIdMap.size == 3)
  let _ ← transfer { root, st, g } g
  pure ()

/-! ### layout_api.rs :: tests (global options, pipeline boundaries) -/

/-- Parses a globals string, failing the test run on error. -/
def globals (text : String) : IO GlobalOptions := do
  match ← GlobalOptions.parse text with
  | .ok d => pure d
  | .error e => throw (IO.userError e)

/-- Entries of the options object an element carries after materialisation. -/
def optionEntries (v : Value) : Array (String × Value) :=
  ((v.get? "layoutOptions").bind (·.getObj?)).getD (((v.get? "properties").bind (·.getObj?)).getD #[])

/-- Rust `layout_api.rs` tests that do not need a layout algorithm. -/
def layoutApiTests : Suite := suite "json.layoutApi" do
  Elk.Api.ensureInitialized
  -- global_aliases_keep_first_spelling_and_authored_values_on_every_element
  let gl := "{\"elk.direction\":\"DOWN\",\"org.eclipse.elk.direction\":\"UP\"}"
  let gOpts ← globals gl
  checkEq "first spelling kept" (gOpts.values.map (·.1)) #["elk.direction"]
  let graph ← parseLenient "{\"children\": [{\"properties\":{\"elk.direction\":\"LEFT\"}, \"ports\":[{},{}]}],
    \"edges\":[{}], \"labels\":[{}]}"
  let merged ← gOpts.materialize graph
  checkEq "authored properties untouched" (merged.getAt [.key "children", .idx 0, .key "properties"])
    (some (.obj #[("elk.direction", .str "LEFT")]))
  for (name, el) in #[("root", some merged), ("port 0", merged.getAt [.key "children", .idx 0, .key "ports", .idx 0]),
      ("port 1", merged.getAt [.key "children", .idx 0, .key "ports", .idx 1]),
      ("edge", merged.getAt [.key "edges", .idx 0]), ("label", merged.getAt [.key "labels", .idx 0])] do
    let opts := (el.bind (·.get? "layoutOptions")).bind (·.getObj?)
    checkEq s!"{name} layoutOptions size" (opts.map (·.size)) (some 1)
    check s!"{name} value" ((el.bind (·.getAt [.key "layoutOptions", .key "elk.direction"])) == some (.str "DOWN"))
  let again ← gOpts.materialize merged
  check "materialize is idempotent" (again == merged)
  -- repeated_global_options_resolve_once_and_preserve_recursive_alias_precedence
  let graph ← parseLenient "{
    \"layoutOptions\": {\"elk.direction\": \"RIGHT\"},
    \"children\": [
      {\"properties\": {\"elk.direction\": \"LEFT\", \"unknown.option\": \"local\"}, \"ports\": [{}], \"edges\": [{}], \"labels\": [{}]},
      {\"properties\": {\"elk.direction\": \"LEFT\", \"unknown.option\": \"local\"}, \"ports\": [{}], \"edges\": [{}], \"labels\": [{}]},
      {\"properties\": {\"elk.direction\": \"LEFT\", \"unknown.option\": \"local\"}, \"ports\": [{}], \"edges\": [{}], \"labels\": [{}]}]}"
  let globalsText := "{\"org.eclipse.elk.direction\": \"DOWN\", \"unknown.option\": \"global\"}"
  let gOpts ← globals globalsText
  let merged ← gOpts.materialize graph
  checkEq "root keeps RIGHT" (merged.getAt [.key "layoutOptions", .key "elk.direction"]) (some (.str "RIGHT"))
  check "root has no alias" ((merged.getAt [.key "layoutOptions", .key "org.eclipse.elk.direction"]).isNone)
  let globalObj ← parseLenient globalsText
  for i in [0:3] do
    let child := merged.getAt [.key "children", .idx i]
    checkEq s!"child {i} direction" ((child.bind (·.getAt [.key "properties", .key "elk.direction"]))) (some (.str "LEFT"))
    checkEq s!"child {i} unknown" ((child.bind (·.getAt [.key "properties", .key "unknown.option"]))) (some (.str "local"))
    check s!"child {i} no alias" ((child.bind (·.getAt [.key "properties", .key "org.eclipse.elk.direction"])).isNone)
    for field in #["ports", "edges", "labels"] do
      check s!"child {i} {field} gets globals" ((child.bind (·.getAt [.key field, .idx 0, .key "layoutOptions"])) == some globalObj)
  let again ← gOpts.materialize merged
  check "materialize idempotent (recursive)" (again == merged)
  -- shared_defaults_match_eager_options_and_output: effective option order/values per element
  -- TODO(phase4): the Rust test uses `elk.algorithm: layered`; switch back once the layered provider is registered.
  let optionsText := "{\"elk.algorithm\":\"box\",\"elk.direction\":\"DOWN\",\"org.eclipse.elk.direction\":\"UP\",\"unknown.option\":\"global\",\"elk.port.side\":\"EAST\",\"elk.spacing.nodeNode\":35}"
  let gOpts ← globals optionsText
  let elements ← [ "{}",
      "{\"layoutOptions\":{\"org.eclipse.elk.direction\":\"RIGHT\",\"unknown.option\":\"local\"}}",
      "{\"properties\":{\"direction\":\"LEFT\",\"elk.direction\":\"RIGHT\"}}",
      "{\"layoutOptions\":null,\"properties\":{\"elk.direction\":\"LEFT\"}}",
      "{\"properties\":false}",
      "{\"layoutOptions\":{},\"properties\":{\"elk.direction\":\"LEFT\"}}" ].mapM (fun s => (parseLenient s : TestM Value))
  for h : i in [0:elements.length] do
    let el := elements[i]
    let eagerEl ← gOpts.materialize el
    let expected := optionEntries eagerEl
    let (actual, _) ← gOpts.effectiveOptions el
    -- compare as key sets with values (the Rust test compares `visit_effective` with the sorted eager map)
    let norm (xs : Array (String × Value)) := stableSort xs (fun a b => compare a.1 b.1)
    check s!"effective options of element {i} (keys)" ((norm actual).map (·.1) == (norm expected).map (·.1))
    check s!"effective options of element {i} (values)" ((norm actual).map (·.2) == (norm expected).map (·.2))
    -- serde's sorted `Map` (no `preserve_order` in elk-rs): the visit order is key-sorted
    check s!"effective options of element {i} (order)" (actual.map (·.1) == (norm expected).map (·.1))
  -- shared_defaults_match_eager_options_and_output: layoutValue output
  let graph ← parseLenient "{
      \"id\":\"root\", \"custom\":{\"preserved\":[1,2,3]},
      \"layoutOptions\":{\"elk.algorithm\":\"box\",\"org.eclipse.elk.direction\":\"RIGHT\",\"unknown.option\":\"authored\"},
      \"children\":[
          {\"id\":\"a\",\"width\":30,\"height\":20,\"properties\":{\"direction\":\"LEFT\"},
           \"ports\":[{\"id\":\"out\",\"width\":0,\"height\":0}],
           \"labels\":[{\"text\":\"A\",\"width\":8,\"height\":8}]},
          {\"id\":\"b\",\"width\":40,\"height\":25,\"ports\":[{\"id\":\"in\",\"width\":0,\"height\":0,\"layoutOptions\":{\"elk.port.side\":\"WEST\"}}]}
      ],
      \"edges\":[{\"id\":\"ab\",\"sources\":[\"out\"],\"targets\":[\"in\"],
                \"labels\":[{\"text\":\"AB\",\"width\":16,\"height\":8}]}]
  }"
  for opts in #["", "{}", "[]", optionsText, "{\"unknown.option\":{\"preserved\":true}}",
      "{\"elk.direction\":\"invalid\",\"elk.spacing.nodeNode\":null}"] do
    -- an object-valued global option makes both pipelines fail identically (`string_val`)
    let objectValued := has opts "preserved"
    match ← Elk.Api.layoutValue graph opts, ← Elk.Api.layoutJson graph.render opts with
    | .ok _, .ok _ => check s!"layoutValue succeeds for globals '{opts}'" (!objectValued)
    | .error e, .error e' =>
      check s!"layoutValue/layoutJson agree on error for globals '{opts}'" (objectValued && e == e')
      check s!"object-valued global error text" (has e "Expected a primitive JSON value.")
    | _, _ => check s!"layoutValue and layoutJson agree for globals '{opts}'" false
  match ← Elk.Api.layoutValue graph optionsText with
  | .ok out =>
    checkEq "authored unknown option kept" (out.getAt [.key "layoutOptions", .key "unknown.option"]) (some (.str "authored"))
    checkEq "authored properties.direction kept" (out.getAt [.key "children", .idx 0, .key "properties", .key "direction"]) (some (.str "LEFT"))
    checkEq "port gets global unknown option" (out.getAt [.key "children", .idx 0, .key "ports", .idx 0, .key "layoutOptions", .key "unknown.option"]) (some (.str "global"))
    checkEq "label gets global unknown option" (out.getAt [.key "children", .idx 0, .key "labels", .idx 0, .key "layoutOptions", .key "unknown.option"]) (some (.str "global"))
    checkEq "edge gets global unknown option" (out.getAt [.key "edges", .idx 0, .key "layoutOptions", .key "unknown.option"]) (some (.str "global"))
    checkEq "edge label gets global unknown option" (out.getAt [.key "edges", .idx 0, .key "labels", .idx 0, .key "layoutOptions", .key "unknown.option"]) (some (.str "global"))
    checkEq "custom member preserved" (out.get? "custom") (graph.get? "custom")
    -- the string API agrees with the value API
    match ← Elk.Api.layoutJson graph.render optionsText with
    | .ok s => checkEq "layoutJson == layoutValue" s out.render
    | .error e => check s!"layoutJson: {e}" false
  | .error e => check s!"layoutValue: {e}" false
  -- owned_value_and_string_boundaries_preserve_layout_bytes_and_errors
  let graph ← parseLenient "{
      \"id\":\"root\", \"layoutOptions\":{\"elk.algorithm\":\"box\"},
      \"children\":[
          {\"id\":\"a\",\"width\":30.1,\"height\":20.3,\"ports\":[{\"id\":\"out\",\"width\":0,\"height\":0,\"layoutOptions\":{\"elk.port.side\":\"EAST\"}}]},
          {\"id\":\"b\",\"width\":40.5,\"height\":25.25,\"ports\":[{\"id\":\"in\",\"width\":0,\"height\":0,\"layoutOptions\":{\"elk.port.side\":\"WEST\"}}]}
      ],
      \"edges\":[{\"id\":\"ab\",\"sources\":[\"out\"],\"targets\":[\"in\"]}]
  }"
  for opts in #["{}", "{\"elk.direction\":\"DOWN\",\"org.eclipse.elk.direction\":\"RIGHT\"}"] do
    match (← Elk.Api.layoutJson graph.render opts), (← Elk.Api.layoutValue graph opts) with
    | .ok legacy, .ok owned => checkEq s!"owned == legacy ({opts})" owned.render legacy
    | _, _ => check s!"layout succeeds ({opts})" false
  let a ← Elk.Api.layoutValue (.obj #[]) "invalid"
  let b ← Elk.Api.layoutJson "{}" "invalid"
  check "invalid options error is reported" (match a with | .error _ => true | .ok _ => false)
  check "value and string boundaries report the same options error"
    (match a, b with | .error x, .error y => x == y | _, _ => false)
  check "options error text" (match a with | .error x => has x "Failed to parse options JSON" | .ok _ => false)
  -- owned_value_errors_match_the_eager_pipeline (error classes)
  for (name, bad) in #[("null", Value.null), ("array", .arr #[]),
      ("missing refs", (← parseLenient "{\"id\":\"root\",\"edges\":[{\"id\":\"e\",\"sources\":[\"missing\"],\"targets\":[\"also-missing\"]}]}"))] do
    match ← Elk.Api.layoutValue bad "{}" with
    | .error msg => check s!"layoutValue error for {name} carries an ELK exception class" (has msg "org.eclipse.elk.")
    | .ok _ => check s!"layoutValue error for {name}" false
    match ← Elk.Api.layoutJson bad.render "{}" with
    | .error _ => check s!"layoutJson error for {name}" true
    | .ok _ => check s!"layoutJson error for {name}" false
  -- layoutJson parse failure
  match ← Elk.Api.layoutJson "{ nope" "{}" with
  | .error msg => check "graph parse failure message" (msg.startsWith "Failed to parse graph JSON")
  | .ok _ => check "graph parse failure" false
  -- test_simple_layout (x present after the pipeline; TODO(phase4): drop `elk.algorithm: box` once layered lands)
  match ← Elk.Api.layoutJson "{
            \"id\": \"root\",
            \"layoutOptions\": { \"elk.algorithm\": \"box\", \"elk.direction\": \"RIGHT\" },
            \"children\": [
                { \"id\": \"n1\", \"width\": 10, \"height\": 10 },
                { \"id\": \"n2\", \"width\": 10, \"height\": 10 }
            ],
            \"edges\": [{
                \"id\": \"e1\",
                \"sources\": [\"n1\"],
                \"targets\": [\"n2\"]
            }]
        }" "{}" with
  | .ok s =>
    match Elk.Json.parse s with
    | .ok v => check "test_simple_layout x" (num? (v.getAt [.key "children", .idx 0, .key "x"])).isSome
    | .error _ => check "test_simple_layout reparse" false
  | .error e => check s!"test_simple_layout: {e}" false
  -- test_global_options_as_defaults: the concrete element option wins over the global one
  match ← Elk.Api.layoutValue (← parseLenient "{
            \"id\": \"root\",
            \"layoutOptions\": { \"elk.algorithm\": \"box\", \"elk.direction\": \"RIGHT\" },
            \"children\": [ { \"id\": \"n1\", \"width\": 10, \"height\": 10 } ]}")
      "{\"org.eclipse.elk.direction\": \"DOWN\"}" with
  | .ok out =>
    checkEq "concrete option beats global default" (out.getAt [.key "layoutOptions", .key "elk.direction"]) (some (.str "RIGHT"))
    checkEq "global default fills the child" (out.getAt [.key "children", .idx 0, .key "layoutOptions", .key "org.eclipse.elk.direction"]) (some (.str "DOWN"))
  | .error e => check s!"global defaults: {e}" false
  -- test_known_options / categories / algorithms
  let opts ← Elk.Api.knownLayoutOptionsValue
  check "test_known_options" (match opts with | .arr xs => !xs.isEmpty | _ => false)
  let cats ← Elk.Api.knownLayoutCategoriesValue
  check "test_known_categories" (match cats with | .arr xs => !xs.isEmpty | _ => false)
  let algs ← Elk.Api.knownLayoutAlgorithmsValue
  check "test_known_algorithms (array)" algs.isArr

/-! ### edgeless_hierarchy_integration_test.rs (placeholder engine) -/

/-- The two tests of `edgeless_hierarchy_integration_test.rs` that do not depend on coordinates:
`edgeless_hierarchy_layout_completes` and `edgeless_hierarchy_deterministic`. -/
def edgelessTests : Suite := suite "json.edgelessHierarchy" do
  -- TODO(phase4): the Rust test runs layered with INCLUDE_CHILDREN; restore once layered is available.
  let input := "{
  \"id\": \"root\",
  \"layoutOptions\": { \"algorithm\": \"box\", \"elk.direction\": \"RIGHT\" },
  \"children\": [
    { \"id\": \"domain\", \"width\": 400, \"height\": 300,
      \"labels\": [{ \"text\": \"Domain\", \"width\": 50, \"height\": 14 }],
      \"layoutOptions\": { \"algorithm\": \"box\", \"elk.direction\": \"RIGHT\", \"elk.portConstraints\": \"FIXED_SIDE\" },
      \"ports\": [
        { \"id\": \"dp_w0\", \"width\": 0, \"height\": 12, \"labels\": [{\"text\": \"wp0\"}], \"layoutOptions\": { \"elk.port.side\": \"WEST\" } },
        { \"id\": \"dp_s0\", \"width\": 50, \"height\": 0, \"labels\": [{\"text\": \"sp0\"}], \"layoutOptions\": { \"elk.port.side\": \"SOUTH\" } }
      ],
      \"children\": [
        { \"id\": \"leaf_a\", \"width\": 80, \"height\": 50, \"labels\": [{ \"text\": \"LeafA\", \"width\": 40, \"height\": 14 }],
          \"ports\": [ { \"id\": \"la_in\", \"width\": 0, \"height\": 10, \"layoutOptions\": { \"elk.port.side\": \"WEST\" } } ] }
      ] }
  ]
}"
  let r1 ← Elk.Api.layoutJson input "{}"
  let r2 ← Elk.Api.layoutJson input "{}"
  match r1, r2 with
  | .ok a, .ok b =>
    check "edgeless_hierarchy_layout_completes" true
    check "edgeless_hierarchy_deterministic" (a == b)
    match Elk.Json.parse a with
    | .ok v =>
      checkEq "domain id preserved" (v.getAt [.key "children", .idx 0, .key "id"]) (some (.str "domain"))
      checkEq "port id preserved" (v.getAt [.key "children", .idx 0, .key "ports", .idx 0, .key "id"]) (some (.str "dp_w0"))
    | .error _ => check "output is valid JSON" false
  | .error e, _ | _, .error e => check s!"edgeless layout: {e}" false

def suites : Array Tests.Suite :=
  #[graphTests, edgeTests, sectionTests, idTests, layoutOptionImportTests, individualSpacingTests,
    exportTests, transferTests, metadataCacheTests, layoutApiTests, edgelessTests]

end Tests.Json.Importer
