import Std.Data.HashSet
import Elk.Json.ImporterState
/-!
# JSON export (`org.eclipse.elk.graph.json.JsonExporter`)

Serialises an `ElkGraph` arena to the ELK JSON format (`ElkGraphJson.forGraph(...).toJson()`).
Layout option values are written as strings in their Java `toString` form;
enum constants are resolved through the metadata registry.
-/
/-! Float literals as global constants (FL): inside branches, loops and specialised code the compiler
shares a literal's `Nat`/`Bool` arguments with unrelated variables (CSE) and then parses it on every
evaluation (`FastFloat.ofScientificImpl`); a top-level constant is a load (PLAN §7.1 items 17, 22). -/
private def fl0p0 : Float := 0.0

namespace Elk.Json

open Elk Elk.Graph Elk.Core Elk.Core.Util Elk.Core.Math Elk.Core.Options Elk.Core.Data

/-- `ExportBuilder` options. -/
structure ExportOptions where
  prettyPrint : Bool := false
  shortLayoutOptionKeys : Bool := true
  omitZeroPositions : Bool := true
  omitZeroDimension : Bool := true
  omitLayout : Bool := false
  omitUnknownLayoutOptions : Bool := true
  deriving Inhabited

namespace JsonExporter

structure St where
  opts : ExportOptions
  nodeIds : Std.HashMap NodeId String := {}
  portIds : Std.HashMap PortId String := {}
  edgeIds : Std.HashMap EdgeId String := {}
  sectionIds : Std.HashMap SectionId String := {}
  nodePath : Std.HashMap NodeId JsonPath := {}
  nodeIdsUsed : Std.HashSet String := {}
  portIdsUsed : Std.HashSet String := {}
  edgeIdsUsed : Std.HashSet String := {}
  sectionIdsUsed : Std.HashSet String := {}
  nodeCounter : Nat := 0
  portCounter : Nat := 0
  edgeCounter : Nat := 0
  sectionCounter : Nat := 0
  uniqueCounter : Nat := 0

abbrev ExportM := StateT St IO

private def pad6 (n : Nat) : String :=
  let s := toString n
  String.ofList (List.replicate (6 - min 6 s.length) '0') ++ s

/-- `assert_unique`: appends `_gNNNNNN` to duplicate ids. -/
private def assertUnique (id : String) (used : Std.HashSet String) (counter : Nat) : String × Std.HashSet String × Nat := Id.run do
  if !used.contains id then return (id, used.insert id, counter)
  let mut counter := counter
  let mut candidate := ""
  let mut found := false
  while !found do
    candidate := s!"{id}_g{pad6 (counter % 1000000)}"
    counter := counter + 1
    if !used.contains candidate then found := true
  return (candidate, used.insert candidate, counter)

private def registerNode (g : ElkGraph) (n : NodeId) (path : JsonPath) : ExportM String := do
  let st ← get
  let (base, counter) := match (g.node n).identifier with
    | some i => (i, st.nodeCounter)
    | none => (s!"n{st.nodeCounter}", st.nodeCounter + 1)
  let (id, used, uc) := assertUnique base st.nodeIdsUsed st.uniqueCounter
  set { st with nodeIds := st.nodeIds.insert n id, nodePath := st.nodePath.insert n path, nodeIdsUsed := used, uniqueCounter := uc, nodeCounter := counter }
  return id

private def registerPort (g : ElkGraph) (p : PortId) : ExportM String := do
  let st ← get
  let (base, counter) := match (g.port p).identifier with
    | some i => (i, st.portCounter)
    | none => (s!"p{st.portCounter}", st.portCounter + 1)
  let (id, used, uc) := assertUnique base st.portIdsUsed st.uniqueCounter
  set { st with portIds := st.portIds.insert p id, portIdsUsed := used, uniqueCounter := uc, portCounter := counter }
  return id

private def registerEdge (g : ElkGraph) (e : EdgeId) : ExportM String := do
  let st ← get
  let (base, counter) := match (g.edge e).identifier with
    | some i => (i, st.edgeCounter)
    | none => (s!"e{st.edgeCounter}", st.edgeCounter + 1)
  let (id, used, uc) := assertUnique base st.edgeIdsUsed st.uniqueCounter
  set { st with edgeIds := st.edgeIds.insert e id, edgeIdsUsed := used, uniqueCounter := uc, edgeCounter := counter }
  return id

private def registerSection (g : ElkGraph) (s : SectionId) : ExportM String := do
  let st ← get
  let (base, counter) := match (g.edgeSection s).identifier with
    | some i => (i, st.sectionCounter)
    | none => (s!"s{st.sectionCounter}", st.sectionCounter + 1)
  let (id, used, uc) := assertUnique base st.sectionIdsUsed st.uniqueCounter
  set { st with sectionIds := st.sectionIds.insert s id, sectionIdsUsed := used, uniqueCounter := uc, sectionCounter := counter }
  return id

private def idByConnectable (st : St) : ConnectableId → Option String
  | .node n => st.nodeIds.get? n
  | .port p => st.portIds.get? p

/-- `spacing_to_string`. -/
def spacingToString (top left bottom right : Float) : String :=
  s!"[top={Float.toRustDisplay top},left={Float.toRustDisplay left},bottom={Float.toRustDisplay bottom},right={Float.toRustDisplay right}]"

/-- Java `toString` of a property value. Enum constants are resolved through
the option metadata (`choices`). -/
partial def propertyValueToString (key : String) (value : PropValue) : IO String := do
  match value with
  | .bool b => return if b then "true" else "false"
  | .int i => return toString i
  | .double d => return Float.toRustDisplay d
  | .string s => return s
  | .vector v => return toString v
  | .vectorChain c => return KVectorChain.toJavaString c
  | .padding p => return spacingToString p.top p.left p.bottom p.right
  | .margins m => return spacingToString m.top m.left m.bottom m.right
  | .enum ord =>
    match ← LayoutMetaDataService.resolveOption key with
    | some d => return (d.choices[ord]?).getD "<value>"
    | none => return "<value>"
  | .enumSet bits =>
    match ← LayoutMetaDataService.resolveOption key with
    | some d =>
      let names := (List.range d.choices.size).filterMap fun i =>
        if (bits >>> i.toUInt64) &&& 1 == 1 then d.choices[i]? else none
      return "[" ++ ", ".intercalate names ++ "]"
    | none => return "<value>"
  | .individualSpacings entries =>
    let mut parts : Array String := #[]
    for (k, v) in entries do
      parts := parts.push s!"{k.id}:{← propertyValueToString k.id v}"
    return ";,;".intercalate parts.toList
  | .intList xs => return "[" ++ ", ".intercalate (xs.toList.map toString) ++ "]"
  | .stringList xs => return "[" ++ ", ".intercalate xs.toList ++ "]"
  | .doubleList xs => return "[" ++ ", ".intercalate (xs.toList.map Float.toRustDisplay) ++ "]"
  | .proxy raw => return raw
  | .dynamic _ => return "<value>"

/-- `short_option_key`: strips `org.eclipse.`. -/
def shortOptionKey (id : String) : String :=
  if id.startsWith "org.eclipse." then (id.drop "org.eclipse.".length).toString else id

private def isKnownOption (id : String) : IO Bool := do
  return (← LayoutMetaDataService.getOptionDataBySuffix id).isSome

/-- `transform_properties`: `layoutOptions` object (individual spacings excluded). -/
private def transformProperties (props : PropertyMap) (obj : Value) : ExportM Value := do
  if props.isEmpty then return obj
  let opts := (← get).opts
  let mut json : Array (String × Value) := #[]
  for (k, v) in props.entries do
    if k.id == CoreOptions.SPACING_INDIVIDUAL.id then continue
    if opts.omitUnknownLayoutOptions && !(← isKnownOption k.id) then continue
    let outKey := if opts.shortLayoutOptionKeys then shortOptionKey k.id else k.id
    json := json.push (outKey, .str (← propertyValueToString k.id v))
  if json.isEmpty then return obj
  return obj.set "layoutOptions" (.obj json)

/-- `transform_individual_spacings`. -/
private def transformIndividualSpacings (props : PropertyMap) (obj : Value) : ExportM Value := do
  let some individual := props.get? CoreOptions.SPACING_INDIVIDUAL | return obj
  if individual.props.isEmpty then return obj
  let opts := (← get).opts
  let mut json : Array (String × Value) := #[]
  for (k, v) in individual.props.entries do
    if opts.omitUnknownLayoutOptions && !(← isKnownOption k.id) then continue
    let outKey := if opts.shortLayoutOptionKeys then shortOptionKey k.id else k.id
    json := json.push (outKey, .str (← propertyValueToString k.id v))
  if json.isEmpty then return obj
  return obj.set "individualSpacings" (.obj json)

/-- `transfer_shape_layout`. -/
private def transferShapeLayout (x y w h : Float) (obj : Value) : ExportM Value := do
  let opts := (← get).opts
  let mut obj := obj
  if !opts.omitLayout then
    if !opts.omitZeroPositions || x != fl0p0 then obj := obj.set "x" (.ofFloat x)
    if !opts.omitZeroPositions || y != fl0p0 then obj := obj.set "y" (.ofFloat y)
  if !opts.omitZeroDimension || w != fl0p0 then obj := obj.set "width" (.ofFloat w)
  if !opts.omitZeroDimension || h != fl0p0 then obj := obj.set "height" (.ofFloat h)
  return obj

private def pointObject (x y : Float) : Value := .obj #[("x", .ofFloat x), ("y", .ofFloat y)]

private def transformLabel (g : ElkGraph) (l : LabelId) : ExportM Value := do
  let label := g.label l
  let mut obj : Value := .obj #[("text", .str label.text)]
  if let some ident := label.identifier then
    if !ident.isEmpty then obj := obj.set "id" (.str ident)
  obj ← transformProperties label.props obj
  transferShapeLayout label.x label.y label.width label.height obj

private def transformPort (g : ElkGraph) (p : PortId) : ExportM Value := do
  let port := g.port p
  let id ← registerPort g p
  let mut obj : Value := .obj #[("id", .str id)]
  if !port.labels.isEmpty then
    let mut arr : Array Value := #[]
    for l in port.labels do arr := arr.push (← transformLabel g l)
    obj := obj.set "labels" (.arr arr)
  obj ← transformProperties port.props obj
  transferShapeLayout port.x port.y port.width port.height obj

partial def transformNode (g : ElkGraph) (n : NodeId) (path : JsonPath) : ExportM Value := do
  let node := g.node n
  let id ← registerNode g n path
  let mut obj : Value := .obj #[("id", .str id)]
  if !node.labels.isEmpty then
    let mut arr : Array Value := #[]
    for l in node.labels do arr := arr.push (← transformLabel g l)
    obj := obj.set "labels" (.arr arr)
  if !node.ports.isEmpty then
    let mut arr : Array Value := #[]
    for p in node.ports do arr := arr.push (← transformPort g p)
    obj := obj.set "ports" (.arr arr)
  if !node.children.isEmpty then
    let mut arr : Array Value := #[]
    for h : i in [0:node.children.size] do
      arr := arr.push (← transformNode g node.children[i] (path ++ #[.key "children", .idx i]))
    obj := obj.set "children" (.arr arr)
  obj ← transformProperties node.props obj
  obj ← transformIndividualSpacings node.props obj
  transferShapeLayout node.x node.y node.width node.height obj

private def transformSection (g : ElkGraph) (s : SectionId) : ExportM Value := do
  let sec := g.edgeSection s
  let id ← registerSection g s
  let opts := (← get).opts
  let mut obj : Value := .obj #[("id", .str id)]
  obj := obj.set "startPoint" (pointObject sec.startX sec.startY)
  obj := obj.set "endPoint" (pointObject sec.endX sec.endY)
  if !opts.omitLayout && !sec.bendPoints.isEmpty then
    obj := obj.set "bendPoints" (.arr (sec.bendPoints.map fun b => pointObject b.x b.y))
  let st ← get
  if let some shape := sec.incomingShape then
    if let some sid := idByConnectable st shape then obj := obj.set "incomingShape" (.str sid)
  if let some shape := sec.outgoingShape then
    if let some sid := idByConnectable st shape then obj := obj.set "outgoingShape" (.str sid)
  if !sec.incomingSections.isEmpty then
    obj := obj.set "incomingSections" (.arr (sec.incomingSections.filterMap fun x => (st.sectionIds.get? x).map Value.str))
  if !sec.outgoingSections.isEmpty then
    obj := obj.set "outgoingSections" (.arr (sec.outgoingSections.filterMap fun x => (st.sectionIds.get? x).map Value.str))
  transformProperties sec.props obj

private def transformEdge (g : ElkGraph) (e : EdgeId) : ExportM Value := do
  let edge := g.edge e
  let id ← registerEdge g e
  let st ← get
  let opts := st.opts
  let mut obj : Value := .obj #[("id", .str id)]
  obj := obj.set "sources" (.arr (edge.sources.filterMap fun s => (idByConnectable st s).map Value.str))
  obj := obj.set "targets" (.arr (edge.targets.filterMap fun t => (idByConnectable st t).map Value.str))
  if !edge.labels.isEmpty then
    let mut arr : Array Value := #[]
    for l in edge.labels do arr := arr.push (← transformLabel g l)
    obj := obj.set "labels" (.arr arr)
  if !opts.omitLayout && !edge.sections.isEmpty then
    let mut arr : Array Value := #[]
    for s in edge.sections do arr := arr.push (← transformSection g s)
    obj := obj.set "sections" (.arr arr)
  if !opts.omitLayout then
    if let some jps := edge.props.get? CoreOptions.JUNCTION_POINTS then
      if !jps.isEmpty then
        obj := obj.set "junctionPoints" (.arr (jps.map fun jp => pointObject jp.x jp.y))
  transformProperties edge.props obj

partial def transformEdges (g : ElkGraph) (n : NodeId) (root : Value) : ExportM Value := do
  let node := g.node n
  let mut root := root
  if !node.containedEdges.isEmpty then
    let path := ((← get).nodePath.get? n).getD #[]
    let mut arr : Array Value := #[]
    for e in node.containedEdges do arr := arr.push (← transformEdge g e)
    let edgesArr := arr
    root := root.modifyAt path.toList (·.set "edges" (.arr edgesArr))
  for c in node.children do
    root ← transformEdges g c root
  return root

/-- `export`: the JSON document of the graph below `root`. -/
def exportValue (g : ElkGraph) (root : NodeId) (opts : ExportOptions := {}) : IO Value := do
  let (v, _) ← (do
      let rootValue ← transformNode g root #[]
      transformEdges g root rootValue : ExportM Value).run { opts }
  return v

end JsonExporter

/-- `ElkGraphJson.forGraph(graph).toJson()`. -/
def exportGraph (g : ElkGraph) (root : NodeId) (opts : ExportOptions := {}) : IO String := do
  let v ← JsonExporter.exportValue g root opts
  return if opts.prettyPrint then v.renderPretty else v.render

end Elk.Json
