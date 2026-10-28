import Elk.Alg.Layered.Options.LayeredOptions
import Elk.Alg.Layered.Graph.NodeType
/-!
# `org.eclipse.elk.alg.layered.options.Spacings`

Spacing values per pair of node types, pre-resolved from the graph's properties. Pure:
the node-based lookups take the node's type and property map, so this module does not
depend on the graph arena (the `LGraph` internals hold a `Spacings`).
-/
namespace Elk.Alg.Layered.Options

open Elk.Graph Elk.Core.Options Elk.Core.Util Elk.Alg.Layered.Graph

/-- `UnspecifiedSpacingException(message)`. -/
def unspecifiedSpacing (message : Option String := none) : IO.Error :=
  IO.userError s!"org.eclipse.elk.alg.layered.options.UnspecifiedSpacingException: {message.getD "Unspecified spacing"}"

/-- `Spacings`. -/
structure Spacings where
  /-- `nodeTypeSpacingOptionsHorizontal[t1][t2]`. -/
  horizontal : Array (Array (Option (Property Float)))
  /-- `nodeTypeSpacingOptionsVertical[t1][t2]`. -/
  vertical : Array (Array (Option (Property Float)))
  /-- Graph-level value per option id (`cache_graph_values`). -/
  graphPropertyValues : Array (String × Float)
  /-- For every entry `t1 * NodeType.COUNT + t2` of `horizontal`, the index of its option's value in
  `graphPropertyValues` (out of range where there is no option): the graph values are looked up
  by position instead of by option id (no Java counterpart). -/
  horizontalSlots : Array Nat := #[]
  /-- The `graphPropertyValues` index of every entry of `vertical` (see `horizontalSlots`). -/
  verticalSlots : Array Nat := #[]
  deriving Inhabited

namespace Spacings

private def emptyTable : Array (Array (Option (Property Float))) :=
  Array.replicate NodeType.COUNT (Array.replicate NodeType.COUNT none)

private def setEntry (t : Array (Array (Option (Property Float)))) (i j : Nat) (p : Property Float) :=
  t.modify i (·.set! j (some p))

/-- `nodeTypeSpacing(nt, spacing)`: vertical self spacing only. -/
private def nodeTypeSpacingSelf (s : Spacings) (nt : NodeType) (spacing : Property Float) : Spacings :=
  let i := ElkEnum.ordinal nt
  { s with vertical := setEntry s.vertical i i spacing }

/-- `nodeTypeSpacing(nt, spacingVert, spacingHorz)`. -/
private def nodeTypeSpacingSame (s : Spacings) (nt : NodeType) (spacingVert spacingHorz : Property Float) : Spacings :=
  let i := ElkEnum.ordinal nt
  { s with vertical := setEntry s.vertical i i spacingVert, horizontal := setEntry s.horizontal i i spacingHorz }

/-- `nodeTypeSpacing(n1, n2, spacing)`: vertical, symmetric. -/
private def nodeTypeSpacingSingle (s : Spacings) (n1 n2 : NodeType) (spacing : Property Float) : Spacings :=
  let i := ElkEnum.ordinal n1
  let j := ElkEnum.ordinal n2
  { s with vertical := setEntry (setEntry s.vertical i j spacing) j i spacing }

/-- `nodeTypeSpacing(n1, n2, spacingVert, spacingHorz)`: symmetric. -/
private def nodeTypeSpacing (s : Spacings) (n1 n2 : NodeType) (spacingVert spacingHorz : Property Float) : Spacings :=
  let i := ElkEnum.ordinal n1
  let j := ElkEnum.ordinal n2
  { s with vertical := setEntry (setEntry s.vertical i j spacingVert) j i spacingVert,
           horizontal := setEntry (setEntry s.horizontal i j spacingHorz) j i spacingHorz }

/-- `precalculateNodeTypeSpacings()`. -/
private def precalculateNodeTypeSpacings (s : Spacings) : Spacings :=
  s -- normal
    |>.nodeTypeSpacingSame .normal LayeredOptions.SPACING_NODE_NODE LayeredOptions.SPACING_NODE_NODE_BETWEEN_LAYERS
    |>.nodeTypeSpacing .normal .longEdge LayeredOptions.SPACING_EDGE_NODE LayeredOptions.SPACING_EDGE_NODE_BETWEEN_LAYERS
    |>.nodeTypeSpacingSingle .normal .northSouthPort LayeredOptions.SPACING_EDGE_NODE
    |>.nodeTypeSpacingSingle .normal .externalPort LayeredOptions.SPACING_EDGE_NODE
    |>.nodeTypeSpacing .normal .label LayeredOptions.SPACING_NODE_NODE LayeredOptions.SPACING_NODE_NODE_BETWEEN_LAYERS
    -- longedge
    |>.nodeTypeSpacingSame .longEdge LayeredOptions.SPACING_EDGE_EDGE LayeredOptions.SPACING_EDGE_EDGE_BETWEEN_LAYERS
    |>.nodeTypeSpacingSingle .longEdge .northSouthPort LayeredOptions.SPACING_EDGE_EDGE
    |>.nodeTypeSpacingSingle .longEdge .externalPort LayeredOptions.SPACING_EDGE_EDGE
    |>.nodeTypeSpacing .longEdge .label LayeredOptions.SPACING_EDGE_NODE LayeredOptions.SPACING_EDGE_NODE_BETWEEN_LAYERS
    -- northsouth
    |>.nodeTypeSpacingSelf .northSouthPort LayeredOptions.SPACING_EDGE_EDGE
    |>.nodeTypeSpacingSingle .northSouthPort .externalPort LayeredOptions.SPACING_EDGE_EDGE
    |>.nodeTypeSpacingSingle .northSouthPort .label LayeredOptions.SPACING_LABEL_NODE
    -- external
    |>.nodeTypeSpacingSelf .externalPort LayeredOptions.SPACING_PORT_PORT
    |>.nodeTypeSpacing .externalPort .label LayeredOptions.SPACING_LABEL_PORT_VERTICAL LayeredOptions.SPACING_LABEL_PORT_HORIZONTAL
    -- label
    |>.nodeTypeSpacingSame .label LayeredOptions.SPACING_EDGE_EDGE LayeredOptions.SPACING_EDGE_EDGE
    -- breaking points
    |>.nodeTypeSpacingSame .breakingPoint LayeredOptions.SPACING_EDGE_EDGE LayeredOptions.SPACING_EDGE_EDGE_BETWEEN_LAYERS
    |>.nodeTypeSpacing .breakingPoint .normal LayeredOptions.SPACING_EDGE_NODE LayeredOptions.SPACING_EDGE_NODE_BETWEEN_LAYERS
    |>.nodeTypeSpacing .breakingPoint .label LayeredOptions.SPACING_EDGE_NODE LayeredOptions.SPACING_EDGE_NODE_BETWEEN_LAYERS
    |>.nodeTypeSpacing .breakingPoint .longEdge LayeredOptions.SPACING_EDGE_NODE LayeredOptions.SPACING_EDGE_NODE_BETWEEN_LAYERS

/-- The distinct options of both tables in `cache_graph_values` order (rows of `vertical`, then
of `horizontal`; first occurrence of each option id) and the slot of every table entry (index into
that list, `distinct.size` for an empty entry). -/
private def tableSlots (s : Spacings) : Array (Property Float) × Array Nat × Array Nat := Id.run do
  let mut distinct : Array (Property Float) := #[]
  for row in s.vertical do
    for p in row do
      if let some p := p then
        if !distinct.any (·.key.id == p.key.id) then distinct := distinct.push p
  for row in s.horizontal do
    for p in row do
      if let some p := p then
        if !distinct.any (·.key.id == p.key.id) then distinct := distinct.push p
  let slotsOf (table : Array (Array (Option (Property Float)))) : Array Nat := Id.run do
    let mut slots : Array Nat := #[]
    for row in table do
      for p in row do
        slots := slots.push (match p with
          | some p => (distinct.findIdx? (·.key.id == p.key.id)).getD distinct.size
          | none => distinct.size)
    return slots
  return (distinct, slotsOf s.horizontal, slotsOf s.vertical)

/-- The node type tables with their slots, the same for every graph (computed once). -/
private def precalculated : Spacings × Array (Property Float) :=
  let s := ({ horizontal := emptyTable, vertical := emptyTable, graphPropertyValues := #[] } : Spacings)
    |>.precalculateNodeTypeSpacings
  let (distinct, horizontalSlots, verticalSlots) := s.tableSlots
  ({ s with horizontalSlots, verticalSlots }, distinct)

/-- `cache_graph_values`: resolves every option of both tables against the graph's properties
(stored value, else the option default; every spacing option has a default), one entry per
option id in table order. -/
private def cacheGraphValues (s : Spacings) (distinct : Array (Property Float)) (graphProps : PropertyMap) :
    Spacings :=
  { s with graphPropertyValues := distinct.map fun p => (p.key.id, (graphProps.get p).getD 0.0) }

/-- `graph_spacing_value(property)`: the cached graph value, else the option default. -/
def graphSpacingValue (s : Spacings) (p : Property Float) : Float :=
  match s.graphPropertyValues.find? (·.1 == p.key.id) with
  | some (_, v) => v
  | none => p.default.getD 0.0

/-- `new Spacings(graph)` from the graph's property map. -/
def new (graphProps : PropertyMap) : Spacings :=
  let (s, distinct) := precalculated
  s.cacheGraphValues distinct graphProps

/-- `get_individual_or_default_f64(node, property)`: the node's individual spacing if set,
else the graph value. -/
def getIndividualOrDefaultF64 (s : Spacings) (nodeProps : PropertyMap) (p : Property Float) : Float :=
  let individual : Option Float :=
    if nodeProps.has CoreOptions.SPACING_INDIVIDUAL then
      match nodeProps.get CoreOptions.SPACING_INDIVIDUAL with
      | some ind => if ind.props.has p then ind.props.get p else none
      | none => none
    else none
  match individual with
  | some v => v
  | none => s.graphSpacingValue p

/-- `getIndividualOrDefaultF64` with the graph value of the option resolved before. -/
@[inline] private def individualOr (nodeProps : PropertyMap) (p : Property Float) (graphValue : Float) : Float :=
  let individual : Option Float :=
    if nodeProps.has CoreOptions.SPACING_INDIVIDUAL then
      match nodeProps.get CoreOptions.SPACING_INDIVIDUAL with
      | some ind => if ind.props.has p then ind.props.get p else none
      | none => none
    else none
  match individual with
  | some v => v
  | none => graphValue

/-- `graphSpacingValue` of the option of a table entry, read by its slot (`horizontalSlots` /
`verticalSlots`); the search by option id is the fallback for a slot out of range. -/
@[inline] private def slotValue (s : Spacings) (slots : Array Nat) (i j : Nat) (option : Property Float) : Float :=
  match slots[i * NodeType.COUNT + j]? with
  | some k =>
    match s.graphPropertyValues[k]? with
    | some (_, v) => v
    | none => s.graphSpacingValue option
  | none => s.graphSpacingValue option

/-- The spacing between two nodes of the given types: the larger individual-or-graph value of
the table's option (`slots`: the table's `horizontalSlots`/`verticalSlots`). -/
private def localSpacing? (s : Spacings) (table : Array (Array (Option (Property Float)))) (slots : Array Nat)
    (t1 : NodeType) (p1 : PropertyMap) (t2 : NodeType) (p2 : PropertyMap) : Option Float := do
  let i := ElkEnum.ordinal t1
  let j := ElkEnum.ordinal t2
  let option ← (table[i]?.bind (·[j]?)).bind id
  let graphValue := s.slotValue slots i j option
  return fmax (individualOr p1 option graphValue) (individualOr p2 option graphValue)

private def localSpacingForTypes? (s : Spacings) (table : Array (Array (Option (Property Float)))) (slots : Array Nat)
    (t1 t2 : NodeType) : Option Float := do
  let i := ElkEnum.ordinal t1
  let j := ElkEnum.ordinal t2
  let option ← (table[i]?.bind (·[j]?)).bind id
  return s.slotValue slots i j option

/-- `getHorizontalSpacing(n1, n2)`: `none` = Java `UnspecifiedSpacingException`. -/
def getHorizontalSpacing? (s : Spacings) (t1 : NodeType) (p1 : PropertyMap) (t2 : NodeType) (p2 : PropertyMap) : Option Float :=
  s.localSpacing? s.horizontal s.horizontalSlots t1 p1 t2 p2

/-- `getVerticalSpacing(n1, n2)`. -/
def getVerticalSpacing? (s : Spacings) (t1 : NodeType) (p1 : PropertyMap) (t2 : NodeType) (p2 : PropertyMap) : Option Float :=
  s.localSpacing? s.vertical s.verticalSlots t1 p1 t2 p2

/-- `getHorizontalSpacing(NodeType, NodeType)`. -/
def getHorizontalSpacingForTypes? (s : Spacings) (t1 t2 : NodeType) : Option Float :=
  s.localSpacingForTypes? s.horizontal s.horizontalSlots t1 t2

/-- `getVerticalSpacing(NodeType, NodeType)`. -/
def getVerticalSpacingForTypes? (s : Spacings) (t1 t2 : NodeType) : Option Float :=
  s.localSpacingForTypes? s.vertical s.verticalSlots t1 t2

/-- Throwing variants (the Java methods throw `UnspecifiedSpacingException`). -/
def getHorizontalSpacing (s : Spacings) (t1 : NodeType) (p1 : PropertyMap) (t2 : NodeType) (p2 : PropertyMap) : IO Float :=
  match s.getHorizontalSpacing? t1 p1 t2 p2 with
  | some v => pure v
  | none => throw (unspecifiedSpacing)
def getVerticalSpacing (s : Spacings) (t1 : NodeType) (p1 : PropertyMap) (t2 : NodeType) (p2 : PropertyMap) : IO Float :=
  match s.getVerticalSpacing? t1 p1 t2 p2 with
  | some v => pure v
  | none => throw (unspecifiedSpacing)
def getHorizontalSpacingForTypes (s : Spacings) (t1 t2 : NodeType) : IO Float :=
  match s.getHorizontalSpacingForTypes? t1 t2 with
  | some v => pure v
  | none => throw (unspecifiedSpacing)
def getVerticalSpacingForTypes (s : Spacings) (t1 t2 : NodeType) : IO Float :=
  match s.getVerticalSpacingForTypes? t1 t2 with
  | some v => pure v
  | none => throw (unspecifiedSpacing)

/-- `getIndividualOrDefault(graph, node, property)`: node individual value, else the graph's
stored-or-default value, else the property default; `none` = `UnspecifiedSpacingException`. -/
def getIndividualOrDefaultWithGraph? {α : Type} [PropCodec α] (graphProps : PropertyMap) (nodeProps : PropertyMap) (p : Property α) : Option α :=
  let individual : Option α :=
    if nodeProps.has CoreOptions.SPACING_INDIVIDUAL then
      match nodeProps.get CoreOptions.SPACING_INDIVIDUAL with
      | some ind => if ind.props.has p then ind.props.get p else none
      | none => none
    else none
  match individual with
  | some v => some v
  | none => match graphProps.get p with
    | some v => some v
    | none => p.default

end Spacings

end Elk.Alg.Layered.Options
