import Std.Data.HashSet
import Elk.Graph.Util
/-!
# `org.eclipse.elk.graph.util.GraphIdentifierGenerator`

Validates, generates and uniquifies the identifiers of all elements of a graph.
Pure builder over the `ElkGraph` arena:

```lean
let g' ← (GraphIdentifierGenerator.forGraph g root).assertValid.assertExists.assertUnique.execute
```

Deviation from Rust: the pseudo random suffixes used by `assertUnique`
(`_gNNNN`) come from a fixed-seed LCG (same recurrence as elk-rs) instead of
a time based seed, so results are reproducible.
-/
namespace Elk.Graph

/-- `GraphIdentifierGenerator`. -/
structure GraphIdentifierGenerator where
  graph : ElkGraph
  root : NodeId
  validate : Bool := false
  generate : Bool := false
  unique : Bool := false
  /-- Counters for node, port, edge, edge section and label identifiers. -/
  currentIds : Array Nat := #[0, 0, 0, 0, 0]
  existing : Std.HashSet String := {}
  rng : UInt64 := 0x2545F4914F6CDD1D

namespace GraphIdentifierGenerator

/-- Kinds of identifier prefixes (`N`, `P`, `E`, `ES`, `L`). -/
private inductive ElementType where
  | node | port | edge | edgeSection | label

private def ElementType.prefix_ : ElementType → String
  | .node => "N" | .port => "P" | .edge => "E" | .edgeSection => "ES" | .label => "L"

private def ElementType.index : ElementType → Nat
  | .node => 0 | .port => 1 | .edge => 2 | .edgeSection => 3 | .label => 4

/-- Anything carrying an identifier: a graph element or an edge section. -/
private inductive Target where
  | element (e : ElementId)
  | section_ (s : SectionId)

private def identifierOf (g : ElkGraph) : Target → Option String
  | .element e => g.identifierOf e
  | .section_ s => (g.edgeSection s).identifier

private def setIdentifier (g : ElkGraph) (t : Target) (id : Option String) : ElkGraph :=
  match t with
  | .element (.node n) => g.modifyNode n fun x => { x with identifier := id }
  | .element (.port p) => g.modifyPort p fun x => { x with identifier := id }
  | .element (.edge e) => g.modifyEdge e fun x => { x with identifier := id }
  | .element (.label l) => g.modifyLabel l fun x => { x with identifier := id }
  | .section_ s => g.modifySection s fun x => { x with identifier := id }

private def isMissing (id : Option String) : Bool :=
  match id with
  | none => true
  | some s => s.trimAscii.isEmpty

/-- `validateIdentifier`: replaces illegal characters by `_`; `none` if already valid. -/
private def validateIdentifier (id : Option String) : Option String := Id.run do
  let some s := id | return none
  if s.isEmpty then return none
  let mut valid := true
  let mut out : Array Char := #[]
  let mut index := 0
  for ch in s.toList do
    let allowed := ch.isAlpha && ch.toNat < 128 || ch == '_' || (index > 0 && ch.isDigit && ch.toNat < 128)
    if allowed then out := out.push ch
    else
      out := out.push '_'
      valid := false
    index := index + 1
  return if valid then none else some (String.ofList out.toList)

/-- Collects labels of an element recursively (the label, then its sub labels). -/
private partial def collectLabel (g : ElkGraph) (l : LabelId) (out : Array ElementId) : Array ElementId :=
  (g.label l).labels.foldl (fun acc c => collectLabel g c acc) (out.push (.label l))

private def collectPort (g : ElkGraph) (p : PortId) (out : Array ElementId) : Array ElementId :=
  (g.port p).labels.foldl (fun acc l => collectLabel g l acc) (out.push (.port p))

private def collectEdge (g : ElkGraph) (e : EdgeId) (out : Array ElementId) : Array ElementId :=
  (g.edge e).labels.foldl (fun acc l => collectLabel g l acc) (out.push (.edge e))

/-- `collectGraphElements`: labels, ports, edges, then children (each child itself included). -/
private partial def collectElements (g : ElkGraph) (n : NodeId) (includeSelf : Bool)
    (out : Array ElementId) : Array ElementId :=
  let node := g.node n
  let out := if includeSelf then out.push (.node n) else out
  let out := node.labels.foldl (fun acc l => collectLabel g l acc) out
  let out := node.ports.foldl (fun acc p => collectPort g p acc) out
  let out := node.containedEdges.foldl (fun acc e => collectEdge g e acc) out
  node.children.foldl (fun acc c => collectElements g c true acc) out

private partial def collectSections (g : ElkGraph) (n : NodeId) (out : Array SectionId) : Array SectionId :=
  let node := g.node n
  let out := node.containedEdges.foldl (fun acc e => acc ++ (g.edge e).sections) out
  node.children.foldl (fun acc c => collectSections g c acc) out

/-- `GraphIdentifierGenerator.forGraph(graph)`: records the existing identifiers. -/
def forGraph (g : ElkGraph) (root : NodeId) : GraphIdentifierGenerator := Id.run do
  let mut existing : Std.HashSet String := {}
  for el in collectElements g root false #[] do
    if let some id := g.identifierOf el then
      if !id.trimAscii.isEmpty then existing := existing.insert id
  for s in collectSections g root #[] do
    if let some id := (g.edgeSection s).identifier then
      if !id.trimAscii.isEmpty then existing := existing.insert id
  return { graph := g, root := root, existing := existing }

/-- `assertValid()`: replace illegal identifier characters. -/
def assertValid (gen : GraphIdentifierGenerator) : GraphIdentifierGenerator := { gen with validate := true }

/-- `assertExists()`: generate missing identifiers. -/
def assertExists (gen : GraphIdentifierGenerator) : GraphIdentifierGenerator := { gen with generate := true }

/-- `assertUnique()`: make duplicate identifiers unique. -/
def assertUnique (gen : GraphIdentifierGenerator) : GraphIdentifierGenerator := { gen with unique := true }

/-! ### Validation -/

private def validateTarget (t : Target) : StateM GraphIdentifierGenerator Unit :=
  modify fun gen =>
    match validateIdentifier (identifierOf gen.graph t) with
    | some id => { gen with graph := setIdentifier gen.graph t (some id) }
    | none => gen

private partial def validateLabel (l : LabelId) : StateM GraphIdentifierGenerator Unit := do
  validateTarget (.element (.label l))
  for c in ((← get).graph.label l).labels do validateLabel c

private partial def validateNode (n : NodeId) : StateM GraphIdentifierGenerator Unit := do
  validateTarget (.element (.node n))
  let node := (← get).graph.node n
  for l in node.labels do validateLabel l
  for p in node.ports do
    validateTarget (.element (.port p))
    for l in ((← get).graph.port p).labels do validateLabel l
  for e in node.containedEdges do
    validateTarget (.element (.edge e))
    let edge := (← get).graph.edge e
    for l in edge.labels do validateLabel l
    for s in edge.sections do validateTarget (.section_ s)
  for c in node.children do validateNode c

/-! ### Generation -/

private def nextIdentifier (t : ElementType) : StateM GraphIdentifierGenerator String := do
  let mut result := ""
  let mut found := false
  while !found do
    let gen ← get
    let n := gen.currentIds[t.index]! + 1
    set { gen with currentIds := gen.currentIds.set! t.index n }
    let id := s!"{t.prefix_}{n}"
    if !gen.existing.contains id then
      result := id
      found := true
  return result

private def setIfMissing (target : Target) (t : ElementType) : StateM GraphIdentifierGenerator Unit := do
  if isMissing (identifierOf (← get).graph target) then
    let id ← nextIdentifier t
    modify fun gen => { gen with graph := setIdentifier gen.graph target (some id) }

private partial def generateLabel (l : LabelId) : StateM GraphIdentifierGenerator Unit := do
  setIfMissing (.element (.label l)) .label
  for c in ((← get).graph.label l).labels do generateLabel c

private partial def generateNode (n : NodeId) : StateM GraphIdentifierGenerator Unit := do
  let gen ← get
  let node := gen.graph.node n
  if node.parent.isNone then
    if isMissing node.identifier then
      set { gen with graph := setIdentifier gen.graph (.element (.node n)) (some "G1") }
  else
    setIfMissing (.element (.node n)) .node
  for l in node.labels do generateLabel l
  for p in node.ports do
    setIfMissing (.element (.port p)) .port
    for l in ((← get).graph.port p).labels do generateLabel l
  for e in node.containedEdges do
    setIfMissing (.element (.edge e)) .edge
    let edge := (← get).graph.edge e
    for l in edge.labels do generateLabel l
    for s in edge.sections do setIfMissing (.section_ s) .edgeSection
  for c in node.children do generateNode c

/-! ### Uniqueness -/

private def fourDigitPaddedRandomNumber : StateM GraphIdentifierGenerator String := do
  let gen ← get
  let next := gen.rng * 6364136223846793005 + 1
  set { gen with rng := next }
  let v := (next >>> 32).toNat % 10000
  let s := toString v
  return "".pushn '0' (4 - s.length) ++ s

private def assertAllIdsUnique (n : NodeId) : StateM GraphIdentifierGenerator Unit := do
  let elements := collectElements (← get).graph n false #[]
  let mut known : Std.HashSet String := {}
  let mut seenNull := false
  for el in elements do
    match identifierOf (← get).graph (.element el) with
    | none =>
      if seenNull then
        let mut newId := s!"null_g{← fourDigitPaddedRandomNumber}"
        while known.contains newId do
          newId := s!"{newId}_g{← fourDigitPaddedRandomNumber}"
        modify fun gen => { gen with graph := setIdentifier gen.graph (.element el) (some newId) }
        known := known.insert newId
      else
        seenNull := true
    | some id0 =>
      let mut id := id0
      while known.contains id do
        id := s!"{id}_g{← fourDigitPaddedRandomNumber}"
      if id != id0 then
        modify fun gen => { gen with graph := setIdentifier gen.graph (.element el) (some id) }
      known := known.insert id

/-- `execute()`: validation, then generation, then uniqueness (as selected). -/
def execute (gen : GraphIdentifierGenerator) : Except String ElkGraph :=
  let act : StateM GraphIdentifierGenerator Unit := do
    if gen.validate then validateNode gen.root
    if gen.generate then generateNode gen.root
    if gen.unique then assertAllIdsUnique gen.root
  let ((), final) := act.run gen
  .ok final.graph

end GraphIdentifierGenerator

end Elk.Graph
