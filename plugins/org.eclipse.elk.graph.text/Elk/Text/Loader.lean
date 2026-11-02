import Std.Data.HashMap
import Elk.Json
import Elk.Text.Parser
/-!
# `.elkt` loader: syntax tree to `ElkGraph` (`org.eclipse.elk.graph.text`)

Builds the `ElkGraph` arena from a `RootAst`, reproducing what Xtext does when
it loads an `.elkt` resource with `ElkGraph.xtext`:

* **Model construction** (`InternalElkGraphParser` actions): every `node`,
  `port`, `label`, `edge` and `section` of the text creates the corresponding
  element in declaration order; edges are contained in the node whose body
  declares them (`containedEdges`), `layout [ position: .. size: .. ]` sets
  `x/y/width/height`, and `edge layout [ ... ]` creates `ElkEdgeSection`s.
* **Property values** (`PropertyKeyValueConverter`, `PropertyValueValueConverter`):
  a property key is resolved with `LayoutMetaDataService.getOptionDataBySuffix`
  after removing the `^` escapes; the value text (quotes stripped, no
  unescaping) is parsed with `LayoutOptionData.parseValue` (`LayoutMetaDataService.parseValueIO`:
  `spacing.individual` goes through `IndividualSpacings.parse`). Unknown options and
  unparsable values are ignored, exactly like `JsonImporter.setOption`
  (`LoadOptions.keepUnknownOptions` stores them as `PropValue.proxy`
  instead, which corresponds to Java's `LayoutOptionProxy`). `key: null` is
  dropped.
* **Linking** (`ElkGraphQualifiedNameProvider`, `ElkGraphScopeProvider`, the
  default `ImportedNamespaceAwareLocalScopeProvider`): the qualified name of a
  node/port/edge/label is the qualified name of its nearest named container
  plus its identifier (an anonymous root contributes no prefix, sections are
  named by their identifier alone). A reference `a.b` in the context of an
  element is looked up as `<container-name>.a.b` for every enclosing named
  container, innermost first, and finally as the global name `a.b`. This allows
  forward references (`edge a -> b` before `node b`) and relative references to
  siblings. `outgoingSections` of a section resolve among the sections of the
  same edge. Unresolved references are errors
  (`Couldn't resolve reference to ElkConnectableShape 'x'.`).

Differences to the hand written Rust loader of elk-rs (`elkt_test_loader.rs`):
that file implements an ad-hoc *line based dialect* (`nodeProperty ...`,
`edgePoint ...`, `node a parent b`, `key = value`, quoted identifiers,
implicit node creation, default sizes `30x30`/`10x10`, port-side inference,
a hard coded list of options). None of that is part of the real ELK Text
grammar and none of it occurs in the 898 corpus models, so it is deliberately
**not** ported; the loader implements the grammar of
`org.eclipse.elk.graph.text/ElkGraph.xtext` instead.
-/
/-! Float literals as global constants (FL): inside branches, loops and specialised code the compiler
shares a literal's `Nat`/`Bool` arguments with unrelated variables (CSE) and then parses it on every
evaluation (`FastFloat.ofScientificImpl`); a top-level constant is a load (PLAN §7.1 items 17, 22). -/
private def fl16p0 : Float := 16.0

namespace Elk.Text

open Elk Elk.Graph Elk.Core Elk.Core.Data Elk.Core.Math Elk.Core.Util

/-- Options of the loader. -/
structure LoadOptions where
  /-- Re-compute the containing node of every connected edge with
  `ElkGraphUtil.updateContainment` (what the Rust loader's `create_hyperedge` does).
  The default keeps each edge in the node whose body declares it, like Xtext. -/
  updateContainment : Bool := false
  /-- Keep unknown options and unparsable values as `PropValue.proxy` (Java `LayoutOptionProxy`). -/
  keepUnknownOptions : Bool := false
  deriving Inhabited

/-- Edge whose `sources`/`targets` and sections still have to be linked. -/
private structure PendingEdge where
  edge : EdgeId
  ast : EdgeAst
  sections : Array SectionId
  /-- Enclosing named namespaces (outermost first), including the edge's own name. -/
  chain : Array (Array String)

private structure LoadState where
  opts : LoadOptions := {}
  /-- Exported objects: qualified name (segments joined by `.`) to the first node/port with that name. -/
  table : Std.HashMap String ConnectableId := {}
  optionCache : Std.HashMap String (Option LayoutOptionData) := {}
  pending : Array PendingEdge := #[]

private abbrev LoadM := StateRefT LoadState ElkM

@[inline] private def getS : LoadM LoadState := getThe LoadState
@[inline] private def modS (f : LoadState → LoadState) : LoadM Unit := modifyThe LoadState f
@[inline] private def modG (f : ElkGraph → ElkGraph) : LoadM Unit := modifyThe ElkGraph f
@[inline] private def withG {α : Type} (f : ElkGraph → α) : LoadM α := do return f (← getThe ElkGraph)

private def joinName (xs : Array String) : String := ".".intercalate xs.toList

private def throwLoad {α : Type} (msg : String) : LoadM α := throw (IO.userError msg)

/-! ### Property conversion -/

/-- `PropertyValueValueConverter.toValue` (text part): quotes are removed from strings,
qualified ids lose their `^` escapes, numbers and booleans are kept as written. -/
private def valueString : ValueAst → Option String
  | .str raw => some (if raw.length >= 2 then ((raw.drop 1).dropEnd 1).toString else raw)
  | .qid segs => some (joinName segs)
  | .num t => some t
  | .bool b => some (toString b)
  | .null => none

private def lookupOption (keySegs : Array String) : LoadM (Option LayoutOptionData) := do
  let key := joinName keySegs
  match (← getS).optionCache[key]? with
  | some d => return d
  | none =>
    let d ← LayoutMetaDataService.getOptionDataBySuffix key
    modS fun s => { s with optionCache := s.optionCache.insert key d }
    return d

/-- Applies `properties+=Property*` to a property map. -/
private def resolveProps (props : Array PropertyAst) (init : PropertyMap) : LoadM PropertyMap := do
  let mut pm := init
  let keep := (← getS).opts.keepUnknownOptions
  for p in props do
    let some s := valueString p.value | continue
    match ← lookupOption p.keySegs with
    | some od =>
      -- `parseValueIO`: `parseValue` plus `spacing.individual` (`IndividualSpacings.parse`)
      match ← LayoutMetaDataService.parseValueIO od s with
      | some v => pm := pm.setRawById od.id v
      | none => if keep then pm := pm.setRawById od.id (.proxy s)
    | none => if keep then pm := pm.setRawById p.keyRaw (.proxy s)
  return pm

private def layoutBox (l : ShapeLayoutAst) : Float × Float × Float × Float :=
  let (x, y) := l.position.getD (0.0, 0.0)
  let (w, h) := l.size.getD (0.0, 0.0)
  (x, y, w, h)

/-! ### Model construction -/

private def register (fqn : Array String) (c : ConnectableId) : LoadM Unit := do
  let key := joinName fqn
  modS fun s => if s.table.contains key then s else { s with table := s.table.insert key c }

private partial def buildLabel (parent : ElementId) (ast : LabelAst) : LoadM Unit := do
  let l ← ElkM.createLabel (some parent) ast.text
  let pm ← resolveProps ast.props {}
  let (x, y, w, h) := layoutBox ast.layout
  modG (·.modifyLabel l fun lb =>
    { lb with identifier := ast.identifier, props := pm, x, y, width := w, height := h })
  for sub in ast.labels do
    buildLabel (.label l) sub

private def buildPort (parent : NodeId) (scope : Array String) (ast : PortAst) : LoadM Unit := do
  let p ← ElkM.createPort (some parent)
  register (scope.push ast.identifier) (.port p)
  let pm ← resolveProps ast.props {}
  let (x, y, w, h) := layoutBox ast.layout
  modG (·.modifyPort p fun pt =>
    { pt with identifier := some ast.identifier, props := pm, x, y, width := w, height := h })
  for l in ast.labels do
    buildLabel (.port p) l

private def buildSection (edge : EdgeId) (ast : SectionAst) : LoadM SectionId := do
  let s ← ElkM.createSection (some edge)
  let pm ← resolveProps ast.props {}
  let (sx, sy) := ast.start.getD (0.0, 0.0)
  let (ex, ey) := ast.stop.getD (0.0, 0.0)
  modG (·.modifySection s fun sec =>
    { sec with identifier := ast.identifier, props := pm, startX := sx, startY := sy, endX := ex, endY := ey,
               bendPoints := ast.bends.map fun (x, y) => ⟨x, y⟩ })
  return s

private def buildEdge (parent : NodeId) (scope : Array String) (chain : Array (Array String))
    (ast : EdgeAst) : LoadM Unit := do
  let e ← ElkM.createEdge (some parent)
  let chain := match ast.identifier with
    | some id => chain.push (scope.push id)
    | none => chain
  let mut sids : Array SectionId := #[]
  for s in ast.sections do
    sids := sids.push (← buildSection e s)
  let pm ← resolveProps ast.props {}
  modG (·.modifyEdge e fun ed => { ed with identifier := ast.identifier, props := pm })
  for l in ast.labels do
    buildLabel (.edge e) l
  modS fun s => { s with pending := s.pending.push { edge := e, ast, sections := sids, chain } }

private partial def buildItems (parent : NodeId) (scope : Array String) (chain : Array (Array String))
    (items : Array Item) : LoadM Unit := do
  for item in items do
    match item with
    | .label l => buildLabel (.node parent) l
    | .port p => buildPort parent scope p
    | .edge e => buildEdge parent scope chain e
    | .node _ identifier layout props sub =>
      let n ← ElkM.createNode (some parent)
      let fqn := scope.push identifier
      register fqn (.node n)
      let pm ← resolveProps props {}
      let (x, y, w, h) := layoutBox layout
      modG (·.modifyNode n fun nd =>
        { nd with identifier := some identifier, props := pm, x, y, width := w, height := h })
      buildItems n fqn (chain.push fqn) sub

/-! ### Linking -/

/-- Default scoping of `[ElkConnectableShape|QualifiedId]`: innermost enclosing namespace first, then global. -/
private def resolveShape (r : RefAst) (chain : Array (Array String)) : LoadM ConnectableId := do
  let tbl := (← getS).table
  let mut i := chain.size
  while i > 0 do
    i := i - 1
    if let some c := tbl[joinName (chain[i]! ++ r.segs)]? then return c
  match tbl[joinName r.segs]? with
  | some c => return c
  | none =>
    throwLoad s!"{r.pos.line}:{r.pos.col}: Couldn't resolve reference to ElkConnectableShape '{joinName r.segs}'."

private def linkEdge (pe : PendingEdge) : LoadM Unit := do
  for r in pe.ast.sources do
    let c ← resolveShape r pe.chain
    modG (·.addEdgeSource pe.edge c)
  for r in pe.ast.targets do
    let c ← resolveShape r pe.chain
    modG (·.addEdgeTarget pe.edge c)
  for h : i in [0:pe.ast.sections.size] do
    let s := pe.ast.sections[i]
    let sid := pe.sections[i]!
    let schain := match s.identifier with
      | some id => pe.chain.push #[id]
      | none => pe.chain
    if let some r := s.incomingShape then
      let c ← resolveShape r schain
      modG (·.modifySection sid fun x => { x with incomingShape := some c })
    if let some r := s.outgoingShape then
      let c ← resolveShape r schain
      modG (·.modifySection sid fun x => { x with outgoingShape := some c })
    for r in s.outgoingSections do
      let name := r.segs[0]!
      let mut target : Option SectionId := none
      for h2 : j in [0:pe.ast.sections.size] do
        if target.isNone && pe.ast.sections[j].identifier == some name then
          target := some pe.sections[j]!
      match target with
      | some tid =>
        modG (·.modifySection sid fun x =>
          if x.outgoingSections.contains tid then x else { x with outgoingSections := x.outgoingSections.push tid })
        modG (·.modifySection tid fun x =>
          if x.incomingSections.contains sid then x else { x with incomingSections := x.incomingSections.push sid })
      | none =>
        throwLoad s!"{r.pos.line}:{r.pos.col}: Couldn't resolve reference to ElkEdgeSection '{name}'."

/-- Builds the arena for a syntax tree; returns the root node. Throws `IO.userError` with
`"line:col: message"` on unresolved references. -/
def loadAst (ast : RootAst) (opts : LoadOptions := {}) : IO (NodeId × ElkGraph) := do
  LayoutMetaDataService.ensureInitialized
  let act : LoadM NodeId := do
    let root ← ElkM.createNode none
    let pm ← resolveProps ast.props {}
    let (x, y, w, h) := layoutBox ast.layout
    modG (·.modifyNode root fun nd => { nd with identifier := ast.identifier, props := pm, x, y, width := w, height := h })
    let scope : Array String := match ast.identifier with
      | some id => #[id]
      | none => #[]
    if let some id := ast.identifier then
      register #[id] (.node root)
    let chain : Array (Array String) := match ast.identifier with
      | some id => #[#[id]]
      | none => #[]
    buildItems root scope chain ast.items
    let pending := (← getS).pending
    modS fun s => { s with pending := #[] }
    for pe in pending do
      linkEdge pe
    if opts.updateContainment then
      let edges ← withG (·.edgeCount)
      for i in [0:edges] do
        let e : EdgeId := ⟨i⟩
        let connected ← withG fun g => !(g.edge e).sources.isEmpty || !(g.edge e).targets.isEmpty
        if connected then modG (ElkGraphUtil.updateContainment · e)
    return root
  let ((root, _), g) ← ElkM.run (act.run { opts }) {}
  return (root, g)

/-- Parses and loads `.elkt` text: the root node and the arena, or an error message
(`"line:col: message"`). Option keys are resolved through the metadata service, which is
initialised on first use. -/
def parseElkt (text : String) (opts : LoadOptions := {}) : IO (Except String (NodeId × ElkGraph)) := do
  match parseAst text with
  | .error e => return .error e
  | .ok ast =>
    try
      return .ok (← loadAst ast opts)
    catch e =>
      return .error (toString e)

/-! ### Optional defaults of the elk-live diagram generator -/

private def utf16Length (s : String) : Nat :=
  s.foldl (fun n c => n + (if c.toNat > 0xFFFF then 2 else 1)) 0

private def computeLabelSizes (g : ElkGraph) (labels : Array LabelId) : ElkGraph :=
  labels.foldl (init := g) fun g l =>
    let lb := g.label l
    if lb.text.isEmpty then g
    else
      g.modifyLabel l fun x =>
        { x with width := if x.width <= 0 then (utf16Length x.text * 9).toFloat else x.width,
                 height := if x.height <= 0 then fl16p0 else x.height }

private partial def applyDefaultsRec (g : ElkGraph) (parent : NodeId) (nodeSize portSize : Float) : ElkGraph := Id.run do
  let mut g := g
  for p in (g.node parent).ports do
    g := g.modifyPort p fun x =>
      { x with width := if x.width <= 0 then portSize else x.width,
               height := if x.height <= 0 then portSize else x.height }
    g := computeLabelSizes g (g.port p).labels
  for c in (g.node parent).children do
    g := g.modifyNode c fun x =>
      { x with width := if x.width <= 0 then nodeSize else x.width,
               height := if x.height <= 0 then nodeSize else x.height }
    g := computeLabelSizes g (g.node c).labels
    g := applyDefaultsRec g c nodeSize portSize
  for e in (g.node parent).containedEdges do
    g := computeLabelSizes g (g.edge e).labels
  return g

/-- `ElkGraphDiagramGenerator.applyDefaults` of elk-live: ports and nodes without a positive
size get `portSize`/`nodeSize` (5 and 30), labels with text get `9 * length` x `16`. Not applied by
`parseElkt`; callers that want the sizes used by the elk-live server can apply it afterwards. -/
def applyDefaults (g : ElkGraph) (root : NodeId) (nodeSize : Float := 30.0) (portSize : Float := 5.0) : ElkGraph :=
  applyDefaultsRec g root nodeSize portSize

end Elk.Text
