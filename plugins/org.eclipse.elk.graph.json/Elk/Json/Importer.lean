import Elk.Json.ImporterState
/-!
# JSON import (`org.eclipse.elk.graph.json.JsonImporter`, part 2: `transform`)

Builds the `ElkGraph` arena from an ELK JSON document, remembering for every
element the JSON path it came from and its JSON id, so `transferLayout` can
write the results back into the same document.
-/
/-! Float literals as global constants (FL): inside branches, loops and specialised code the compiler
shares a literal's `Nat`/`Bool` arguments with unrelated variables (CSE) and then parses it on every
evaluation (`FastFloat.ofScientificImpl`); a top-level constant is a load (PLAN §7.1 items 17, 22). -/
private def fl0p0 : Float := 0.0

namespace Elk.Json

open Elk Elk.Graph Elk.Core Elk.Core.Util Elk.Core.Math Elk.Core.Options Elk.Core.Data
open ImportM

namespace JsonImporter

/-- `parse_direction_option`: ordinal or (upper-cased) Java name of `Direction`. -/
def parseDirectionOption (value : String) : Option Direction :=
  let t := value.trimAscii.toString
  match t.toNat? with
  | some i => ElkEnum.ofOrdinal? i
  | none => ElkEnum.ofJavaName? t.toUpper

/-- Looks up option metadata by key (full id, legacy id or unique suffix), cached per import. -/
def optionDataFor (id : String) : ImportM (Option LayoutOptionData) := do
  match (← getI).optionCache.get? id with
  | some d => return d
  | none =>
    let d ← LayoutMetaDataService.getOptionDataBySuffix id
    modI fun s => { s with optionCache := s.optionCache.insert id d }
    return d

/-- Index of the `enumMemo` entry for option `oid` and value `value` from `i` (`memo.size` if none). -/
private def enumMemoIndex (memo : Array (String × String × PropValue)) (oid value : String) (i : Nat) : Nat :=
  if h : i < memo.size then
    let e := memo[i]
    if e.1 == oid && e.2.1 == value then i else enumMemoIndex memo oid value (i + 1)
  else memo.size
termination_by memo.size - i

/-- Entries kept in `enumMemo` (ENUM/ENUMSET values repeat across the elements of a graph, e.g.
`port.side`; a short list compares faster than a hash map). -/
private def ENUM_MEMO_SIZE : Nat := 16

/-- `LayoutOptionData.parseValue`, memoised per import for ENUM/ENUMSET options (pure parsers: a
memo hit returns the value a new parse would). -/
def parseOptionValue (od : LayoutOptionData) (value : String) : ImportM (Option PropValue) := do
  match od.type with
  | .enum | .enumSet =>
    -- an empty or `null` value is decided by `parseValue` itself (no parser call)
    if value.isEmpty || value == "null" then return od.parseValue value
    let memo := (← getI).enumMemo
    let i := enumMemoIndex memo od.id value 0
    if h : i < memo.size then return some memo[i].2.2
    match od.parseValue value with
    | some v =>
      if memo.size < ENUM_MEMO_SIZE then modI (·.pushEnumMemo (od.id, value, v))
      return some v
    | none => return none
  | _ => return od.parseValue value

/-- `set_option`: parses the string value with the option's parser and stores
it under the canonical id. Unknown options and unparsable values are ignored. -/
def setOption (props : PropertyMap) (id : String) (value : String) : ImportM PropertyMap := do
  if id == CoreOptions.DIRECTION.id then
    if let some d := parseDirectionOption value then
      return props.set CoreOptions.DIRECTION d
  match ← optionDataFor id with
  | some od =>
    match ← parseOptionValue od value with
    | some v => return props.setRawById od.id v
    | none => return props
  | none => return props

/-- `transform_authored_properties`: `layoutOptions` (or `properties`) of the element. -/
def transformAuthoredProperties (obj : Value) (props : PropertyMap) : ImportM PropertyMap := do
  let options := match JsonAdapter.optObject obj Key.layoutOptions with
    | some o => some o
    | none => JsonAdapter.optObject obj Key.properties
  let mut props := props
  if let some (.obj kvs) := options then
    for (k, v) in kvs do
      props ← setOption props k (← JsonAdapter.stringVal v)
  return props

/-- `transform_properties`: authored options merged with the per-call defaults. -/
def transformProperties (obj : Value) (props : PropertyMap) : ImportM PropertyMap := do
  match (← getI).defaults with
  | some g =>
    -- without defaults the effective options are the authored ones (and the cache is unchanged)
    if g.values.isEmpty then return ← transformAuthoredProperties obj props
    let (opts, g') ← g.effectiveOptions obj
    modI (·.setDefaults g')
    let mut props := props
    for (k, v) in opts do
      props ← setOption props k (← JsonAdapter.stringVal v)
    return props
  | none => transformAuthoredProperties obj props

/-- `transform_individual_spacings`: the `individualSpacings` object. -/
def transformIndividualSpacings (obj : Value) (props : PropertyMap) : ImportM PropertyMap := do
  match JsonAdapter.optObject obj Key.individualSpacings with
  | some (.obj kvs) =>
    let individual : IndividualSpacings := (props.get CoreOptions.SPACING_INDIVIDUAL).getD {}
    let mut inner := individual.props
    for (k, v) in kvs do
      inner ← setOption inner k (← JsonAdapter.stringVal v)
    return props.set CoreOptions.SPACING_INDIVIDUAL { individual with props := inner }
  | _ => return props

/-- `x`, `y`, `width`, `height` of a shape after `read_shape_layout` and `double_value_valid`, and
whether every present member was a valid number. -/
structure ShapeRead where
  x : Float
  y : Float
  w : Float
  h : Float
  ok : Bool

/-- `double_value_valid` of a present value: non-finite coordinates become `0`. -/
@[inline] private def validCoord (v : Float) : Float := if v.isFinite then v else fl0p0

/-- `optDouble` + `double_value_valid` of the member `key` (first occurrence), pure: `cur` when
absent or `null`, `false` in the second component for an invalid value. -/
@[inline] private def shapeField (kvs : Array (String × Value)) (key : String) (cur : Float) : Float × Bool :=
  let i := Value.keyIndex kvs key
  if h : i < kvs.size then
    match kvs[i].2 with
    | .num n => (validCoord n.toFloat, true)
    | .str s =>
      match parseFloat? s with
      | some f => (validCoord f, true)
      | none => (cur, false)
    | .null => (cur, true)
    | _ => (cur, false)
  else (cur, true)

/-- `readShapeLayout` and the coordinate update (absent members keep `cx`, …) as one pure function
(no `Option`/tuple results, the update closure gets plain floats). -/
def readShape (obj : Value) (cx cy cw ch : Float) : ShapeRead :=
  match obj with
  | .obj kvs =>
    let (x, okx) := shapeField kvs Key.x cx
    let (y, oky) := shapeField kvs Key.y cy
    let (w, okw) := shapeField kvs Key.width cw
    let (h, okh) := shapeField kvs Key.height ch
    ⟨x, y, w, h, okx && oky && okw && okh⟩
  | _ => ⟨cx, cy, cw, ch, true⟩

/-- `register_node`; returns the JSON id. -/
def registerNode (n : NodeId) (obj : Value) (path : JsonPath) : ImportM JsonId := do
  let id ← JsonAdapter.getId obj
  modI (·.addNode id n path)
  return id

/-- `register_port`; returns the JSON id. -/
def registerPort (p : PortId) (obj : Value) (path : JsonPath) : ImportM JsonId := do
  let id ← JsonAdapter.getId obj
  modI (·.addPort id p path)
  return id

/-- `register_edge`; returns the JSON id. -/
def registerEdge (e : EdgeId) (obj : Value) (path : JsonPath) : ImportM JsonId := do
  let id ← JsonAdapter.getId obj
  let containing := ((← getG).edge e).containingNode
  modI (·.addEdge id e path containing)
  return id

/-- `register_section`; returns the JSON id. -/
def registerSection (sec : SectionId) (obj : Value) (path : JsonPath) : ImportM JsonId := do
  let id ← JsonAdapter.getId obj
  modI (·.addSection id sec path)
  return id

/-- `idSave obj` after `getId obj` returned `id`: a string id is the member itself (`stringVal` of a
string), a numeric one is rendered again (`stringVal`'s number form). -/
@[inline] def idSaveOf (obj : Value) (id : JsonId) : ImportM (Option String) :=
  match id with
  | .str s => pure (some s)
  | .int _ => JsonAdapter.idSave obj

/-- `shape_by_id`: node or port with the given id. -/
def shapeById (id : JsonId) : ImportM ConnectableId := do
  let st ← getI
  match st.nodeIdMap.get? id with
  | some n => return .node n
  | none =>
    match st.portIdMap.get? id with
    | some p => return .port p
    | none => throwJsonImport s!"Referenced shape does not exist: {id.asString}"

/-- `transform_labels`. -/
def transformLabels (obj : Value) (parent : ElementId) (path : JsonPath) : ImportM Unit := do
  let some labels := JsonAdapter.optArray obj Key.labels | return
  for h : i in [0:labels.size] do
    let labelObj := labels[i]
    if !labelObj.isObj then continue
    let labelPath := (path.push (.key Key.labels)).push (.idx i)
    let text := (← JsonAdapter.optString labelObj Key.text).getD ""
    let l ← ElkM.createLabel (some parent) text
    let ident ← if JsonAdapter.hasKey labelObj Key.id then JsonAdapter.idSave labelObj else pure none
    modI (·.addLabelPath l labelPath)
    let lb0 := (← getG).label l
    let ident := if ident.isSome then ident else lb0.identifier
    let props ← transformProperties labelObj lb0.props
    let sh := readShape labelObj lb0.x lb0.y lb0.width lb0.height
    if !sh.ok then throwJsonImport "Invalid number value."
    modG (·.modifyLabel l fun lb => { lb with identifier := ident, props, x := sh.x, y := sh.y, width := sh.w, height := sh.h })

/-- `transform_port`. -/
def transformPort (obj : Value) (parent : NodeId) (path : JsonPath) : ImportM Unit := do
  let p ← ElkM.createPort (some parent)
  let id ← registerPort p obj path
  let ident ← idSaveOf obj id
  let pt0 := (← getG).port p
  let ident := if ident.isSome then ident else pt0.identifier
  let props ← transformProperties obj pt0.props
  let sh := readShape obj pt0.x pt0.y pt0.width pt0.height
  if !sh.ok then throwJsonImport "Invalid number value."
  modG (·.modifyPort p fun pt => { pt with identifier := ident, props, x := sh.x, y := sh.y, width := sh.w, height := sh.h })
  let firstLabel := (← getG).labels.size
  modI (·.modifyIndex (·.setPortFirstLabel p.idx firstLabel))
  transformLabels obj (.port p) path

/-- `transform_ports`. -/
def transformPorts (obj : Value) (parent : NodeId) (path : JsonPath) : ImportM Unit := do
  let some ports := JsonAdapter.optArray obj Key.ports | return
  for h : i in [0:ports.size] do
    let portObj := ports[i]
    if !portObj.isObj then continue
    transformPort portObj parent ((path.push (.key Key.ports)).push (.idx i))

/-- `transform_node` (recursively imports the children). -/
partial def transformNode (obj : Value) (path : JsonPath) (parent : Option NodeId) : ImportM NodeId := do
  let n ← ElkM.createNode parent
  let firstPort := (← getG).ports.size
  modI (·.modifyIndex (·.setNodeFirstPort n.idx firstPort))
  let id ← registerNode n obj path
  let ident ← idSaveOf obj id
  let nd0 := (← getG).node n
  let ident := if ident.isSome then ident else nd0.identifier
  let props ← transformProperties obj nd0.props
  let props ← transformIndividualSpacings obj props
  let sh := readShape obj nd0.x nd0.y nd0.width nd0.height
  if !sh.ok then throwJsonImport "Invalid number value."
  modG (·.modifyNode n fun nd => { nd with identifier := ident, props, x := sh.x, y := sh.y, width := sh.w, height := sh.h })
  transformPorts obj n path
  let firstLabel := (← getG).labels.size
  modI (·.modifyIndex (·.setNodeFirstLabel n.idx firstLabel))
  transformLabels obj (.node n) path
  if let some children := JsonAdapter.optArray obj Key.children then
    for h : i in [0:children.size] do
      let child := children[i]
      if child.isObj then
        let _ ← transformNode child ((path.push (.key Key.children)).push (.idx i)) (some n)
  let subtreeEnd := (← getG).nodes.size
  modI (·.modifyIndex (·.setNodeSubtreeEnd n.idx subtreeEnd))
  return n

/-- `transform_primitive_edge_layout`: `sourcePoint`/`targetPoint`/`bendPoints` into one section. -/
def transformPrimitiveEdgeLayout (obj : Value) (e : EdgeId) : ImportM Unit := do
  let hasSource := JsonAdapter.hasKey obj "sourcePoint"
  let hasTarget := JsonAdapter.hasKey obj "targetPoint"
  let hasBend := JsonAdapter.hasKey obj Key.bendPoints
  if !hasSource && !hasTarget && !hasBend then return
  let sec ← ElkM.createSection (some e)
  if let some sp := JsonAdapter.optObject obj "sourcePoint" then
    if let some x ← JsonAdapter.optDouble sp Key.x then
      modG (·.modifySection sec fun s => { s with startX := doubleValueValid (some x) })
    if let some y ← JsonAdapter.optDouble sp Key.y then
      modG (·.modifySection sec fun s => { s with startY := doubleValueValid (some y) })
  if let some tp := JsonAdapter.optObject obj "targetPoint" then
    if let some x ← JsonAdapter.optDouble tp Key.x then
      modG (·.modifySection sec fun s => { s with endX := doubleValueValid (some x) })
    if let some y ← JsonAdapter.optDouble tp Key.y then
      modG (·.modifySection sec fun s => { s with endY := doubleValueValid (some y) })
  if let some bends := JsonAdapter.optArray obj Key.bendPoints then
    for b in bends do
      if b.isObj then
        let x := doubleValueValid (← JsonAdapter.optDouble b Key.x)
        let y := doubleValueValid (← JsonAdapter.optDouble b Key.y)
        modG (ElkGraphUtil.createBendPoint · sec x y)

/-- `transform_primitive_edge`: `source`/`target` (+ `sourcePort`/`targetPort`). -/
def transformPrimitiveEdge (obj : Value) (parent : NodeId) (path : JsonPath) : ImportM EdgeId := do
  let e ← ElkM.createEdge (some parent)
  let id ← registerEdge e obj path
  if let some ident ← idSaveOf obj id then
    modG (·.modifyEdge e fun x => { x with identifier := some ident })
  -- source
  let some sourceIdValue := obj.get? Key.source | throwJsonImport "An edge must have a source node."
  let sourceId ← JsonAdapter.asId sourceIdValue
  let some sourceNode := (← getI).nodeIdMap.get? sourceId | throwJsonImport "An edge must have a source node."
  let sourcePort ← match obj.get? Key.sourcePort with
    | some pv => do
      let pid ← JsonAdapter.asId pv
      pure ((← getI).portIdMap.get? pid)
    | none => pure none
  match sourcePort with
  | some p =>
    if ((← getG).port p).parent != some sourceNode then
      throwJsonImport "The source port of an edge must be a port of the edge's source node."
    ElkM.addEdgeSource e (.port p)
  | none => ElkM.addEdgeSource e (.node sourceNode)
  -- target
  let some targetIdValue := obj.get? Key.target | throwJsonImport "An edge must have a target node."
  let targetId ← JsonAdapter.asId targetIdValue
  let some targetNode := (← getI).nodeIdMap.get? targetId | throwJsonImport "An edge must have a target node."
  let targetPort ← match obj.get? Key.targetPort with
    | some pv => do
      let pid ← JsonAdapter.asId pv
      pure ((← getI).portIdMap.get? pid)
    | none => pure none
  match targetPort with
  | some p =>
    if ((← getG).port p).parent != some targetNode then
      throwJsonImport "The target port of an edge must be a port of the edge's target node."
    ElkM.addEdgeTarget e (.port p)
  | none => ElkM.addEdgeTarget e (.node targetNode)
  let edge := (← getG).edge e
  if edge.sources.isEmpty || edge.targets.isEmpty then
    throwJsonImport "An edge must have at least one source and one target."
  let props ← transformProperties obj edge.props
  modG (·.modifyEdge e fun x => { x with props })
  transformPrimitiveEdgeLayout obj e
  let firstLabel := (← getG).labels.size
  modI (·.modifyIndex (·.setEdgeFirstLabel e.idx firstLabel))
  transformLabels obj (.edge e) path
  return e

/-- `fill_edge_section_coordinates`. -/
def fillEdgeSectionCoordinates (obj : Value) (sec : SectionId) : ImportM Unit := do
  let some sp := JsonAdapter.optObject obj Key.startPoint | throwJsonImport "All edge sections need a start point."
  let some ep := JsonAdapter.optObject obj Key.endPoint | throwJsonImport "All edge sections need an end point."
  if let some x ← JsonAdapter.optDouble sp Key.x then
    modG (·.modifySection sec fun s => { s with startX := doubleValueValid (some x) })
  if let some y ← JsonAdapter.optDouble sp Key.y then
    modG (·.modifySection sec fun s => { s with startY := doubleValueValid (some y) })
  if let some x ← JsonAdapter.optDouble ep Key.x then
    modG (·.modifySection sec fun s => { s with endX := doubleValueValid (some x) })
  if let some y ← JsonAdapter.optDouble ep Key.y then
    modG (·.modifySection sec fun s => { s with endY := doubleValueValid (some y) })
  if let some bends := JsonAdapter.optArray obj Key.bendPoints then
    for b in bends do
      if b.isObj then
        let x := doubleValueValid (← JsonAdapter.optDouble b Key.x)
        let y := doubleValueValid (← JsonAdapter.optDouble b Key.y)
        modG (ElkGraphUtil.createBendPoint · sec x y)

/-- `transform_edge_sections`. -/
def transformEdgeSections (obj : Value) (e : EdgeId) : ImportM Unit := do
  let mut incomingIds : Array (SectionId × Array JsonId) := #[]
  let mut outgoingIds : Array (SectionId × Array JsonId) := #[]
  if let some sections := JsonAdapter.optArray obj Key.sections then
    let edgePath := (tableGet? (← getI).edgePath e.idx).getD #[]
    for h : i in [0:sections.size] do
      let secObj := sections[i]
      if !secObj.isObj then continue
      let secPath := (edgePath.push (.key Key.sections)).push (.idx i)
      let sec ← ElkM.createSection (some e)
      let id ← registerSection sec secObj secPath
      if let some ident ← idSaveOf secObj id then
        modG (·.modifySection sec fun x => { x with identifier := some ident })
      fillEdgeSectionCoordinates secObj sec
      if let some shapeId ← JsonAdapter.optString secObj Key.incomingShape then
        let shape ← shapeById (.str shapeId)
        modG (·.modifySection sec fun x => { x with incomingShape := some shape })
      if let some shapeId ← JsonAdapter.optString secObj Key.outgoingShape then
        let shape ← shapeById (.str shapeId)
        modG (·.modifySection sec fun x => { x with outgoingShape := some shape })
      if let some ids := JsonAdapter.optArray secObj Key.incomingSections then
        let mut arr : Array JsonId := #[]
        for v in ids do arr := arr.push (← JsonAdapter.asId v)
        incomingIds := incomingIds.push (sec, arr)
      if let some ids := JsonAdapter.optArray secObj Key.outgoingSections then
        let mut arr : Array JsonId := #[]
        for v in ids do arr := arr.push (← JsonAdapter.asId v)
        outgoingIds := outgoingIds.push (sec, arr)
      let props ← transformAuthoredProperties secObj ((← getG).edgeSection sec).props
      modG (·.modifySection sec fun x => { x with props })
  let st ← getI
  for (sec, ids) in incomingIds do
    let mut resolved : Array SectionId := #[]
    for id in ids do
      let some r := st.sectionIdMap.get? id | throwJsonImport "Referenced edge section does not exist."
      resolved := resolved.push r
    modG (·.modifySection sec fun x => { x with incomingSections := resolved })
  for (sec, ids) in outgoingIds do
    let mut resolved : Array SectionId := #[]
    for id in ids do
      let some r := st.sectionIdMap.get? id | throwJsonImport "Referenced edge section does not exist."
      resolved := resolved.push r
    modG (·.modifySection sec fun x => { x with outgoingSections := resolved })
  let g ← getG
  let edge := g.edge e
  if edge.isConnected && !edge.isHyperedge && edge.sections.size == 1 then
    let sec := edge.sections[0]!
    let s := g.edgeSection sec
    if s.incomingShape.isNone && s.outgoingShape.isNone then
      let source := edge.sources[0]!
      let target := edge.targets[0]!
      modG (·.modifySection sec fun x => { x with incomingShape := some source, outgoingShape := some target })

/-- `transform_edge`: `sources`/`targets` edge with optional sections. -/
def transformEdge (obj : Value) (parent : NodeId) (path : JsonPath) : ImportM EdgeId := do
  let e ← ElkM.createEdge (some parent)
  let id ← registerEdge e obj path
  if let some ident ← idSaveOf obj id then
    modG (·.modifyEdge e fun x => { x with identifier := some ident })
  if let some sources := JsonAdapter.optArray obj Key.sources then
    for v in sources do
      let shape ← shapeById (← JsonAdapter.asId v)
      ElkM.addEdgeSource e shape
  if let some targets := JsonAdapter.optArray obj Key.targets then
    for v in targets do
      let shape ← shapeById (← JsonAdapter.asId v)
      ElkM.addEdgeTarget e shape
  let edge := (← getG).edge e
  if edge.sources.isEmpty || edge.targets.isEmpty then
    throwJsonImport "An edge must have at least one source and one target."
  let props ← transformProperties obj edge.props
  modG (·.modifyEdge e fun x => { x with props })
  transformEdgeSections obj e
  let firstLabel := (← getG).labels.size
  modI (·.modifyIndex (·.setEdgeFirstLabel e.idx firstLabel))
  transformLabels obj (.edge e) path
  return e

mutual

/-- `transform_edges` of the node object `obj` (node `node`): its edges, then recursively those of
its children. With `regular` (`ElemIndex.regular`: the node ids are unique) the child objects are
the nodes `node + 1, …` in preorder (what the id lookup of `transformEdges` finds), otherwise they
are looked up by id. -/
partial def transformEdgesOf (obj : Value) (node : NodeId) (regular : Bool) : ImportM Unit := do
  let nodePath := (tableGet? (← getI).nodePath node.idx).getD #[]
  let firstEdge := (← getG).edges.size
  modI (·.modifyIndex (·.setNodeFirstEdge node.idx firstEdge))
  if let some edges := JsonAdapter.optArray obj Key.edges then
    for h : i in [0:edges.size] do
      let edgeObj := edges[i]
      if !edgeObj.isObj then continue
      let edgePath := (nodePath.push (.key Key.edges)).push (.idx i)
      -- the edge registered last under the edge's id (`edgeIdMap`) is the one just imported
      let e ← if JsonAdapter.hasKey edgeObj Key.sources || JsonAdapter.hasKey edgeObj Key.targets then
          transformEdge edgeObj node edgePath
        else
          transformPrimitiveEdge edgeObj node edgePath
      ElkM.updateContainment e
  if let some children := JsonAdapter.optArray obj Key.children then
    if regular then
      let mut next := node.idx + 1
      for child in children do
        if child.isObj then
          transformEdgesOf child { idx := next } true
          next := (← getI).index.nodeSubtreeEnd.getD next (next + 1)
    else
      for child in children do
        if child.isObj then transformEdges child

/-- `transform_edges`: edges of a node and, recursively, of its children. -/
partial def transformEdges (obj : Value) : ImportM Unit := do
  let nodeId ← JsonAdapter.getId obj
  let some node := (← getI).nodeIdMap.get? nodeId | throwJsonImport "Unable to find elk node for json object. Panic!"
  transformEdgesOf obj node false

end

/-- Numbers of node, port and edge objects of a document (what the importer will register). -/
structure ElemCounts where
  nodes : Nat := 0
  ports : Nat := 0
  edges : Nat := 0

/-- The objects of an array from `i` on. -/
private partial def countObjects (xs : Array Value) (i acc : Nat) : Nat :=
  if h : i < xs.size then countObjects xs (i + 1) (if xs[i].isObj then acc + 1 else acc) else acc

mutual

/-- `ElemCounts` of the node object `obj` and its children added to `acc`. -/
partial def countElements (obj : Value) (acc : ElemCounts) : ElemCounts :=
  let ports := match JsonAdapter.optArray obj Key.ports with
    | some xs => countObjects xs 0 0
    | none => 0
  let edges := match JsonAdapter.optArray obj Key.edges with
    | some xs => countObjects xs 0 0
    | none => 0
  let acc := { nodes := acc.nodes + 1, ports := acc.ports + ports, edges := acc.edges + edges }
  match JsonAdapter.optArray obj Key.children with
  | some xs => countChildren xs 0 acc
  | none => acc

/-- `countElements` of the objects of `xs` from `i` on. -/
partial def countChildren (xs : Array Value) (i : Nat) (acc : ElemCounts) : ElemCounts :=
  if h : i < xs.size then
    countChildren xs (i + 1) (if xs[i].isObj then countElements xs[i] acc else acc)
  else acc

end

/-- `transform`: imports a whole document (the root must be an object). -/
def transform (root : Value) : ImportM NodeId := do
  -- the id maps get their final size up front (no rehashing while they grow)
  let counts := countElements root {}
  modI fun s => { model := root, defaults := s.defaults, nodeIdMap := .emptyWithCapacity counts.nodes,
                  portIdMap := .emptyWithCapacity counts.ports, edgeIdMap := .emptyWithCapacity counts.edges }
  if !root.isObj then throwJsonImport "Top-level element of the graph must be a json object."
  let n ← transformNode root #[] none
  modI fun s => { s with rootNode := some n }
  -- two nodes with the same JSON id: `transformEdges` attaches the edges of both objects to the node
  -- registered last (`ElemIndex.regular`)
  if (← getI).nodeIdMap.size != (← getG).nodes.size then modI (·.modifyIndex ElemIndex.markIrregular)
  if (← getI).index.regular then transformEdgesOf root n true else transformEdges root
  return n

end JsonImporter

end Elk.Json
