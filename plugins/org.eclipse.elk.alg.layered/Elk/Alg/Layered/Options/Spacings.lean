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

/-- `cache_graph_values`: resolves every option of both tables against the graph's properties
(stored value, else the option default; every spacing option has a default). -/
private def cacheGraphValues (s : Spacings) (graphProps : PropertyMap) : Spacings := Id.run do
  let mut values : Array (String × Float) := #[]
  let cache (values : Array (String × Float)) (p : Property Float) : Array (String × Float) :=
    if values.any (·.1 == p.key.id) then values
    else values.push (p.key.id, (graphProps.get p).getD 0.0)
  for row in s.vertical do
    for p in row do
      if let some p := p then values := cache values p
  for row in s.horizontal do
    for p in row do
      if let some p := p then values := cache values p
  return { s with graphPropertyValues := values }

/-- `new Spacings(graph)` from the graph's property map. -/
def new (graphProps : PropertyMap) : Spacings :=
  ({ horizontal := emptyTable, vertical := emptyTable, graphPropertyValues := #[] } : Spacings)
    |>.precalculateNodeTypeSpacings |>.cacheGraphValues graphProps

/-- `graph_spacing_value(property)`: the cached graph value, else the option default. -/
def graphSpacingValue (s : Spacings) (p : Property Float) : Float :=
  match s.graphPropertyValues.find? (·.1 == p.key.id) with
  | some (_, v) => v
  | none => p.default.getD 0.0

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

private def localSpacing? (s : Spacings) (table : Array (Array (Option (Property Float))))
    (t1 : NodeType) (p1 : PropertyMap) (t2 : NodeType) (p2 : PropertyMap) : Option Float := do
  let option ← (table[ElkEnum.ordinal t1]?.bind (·[ElkEnum.ordinal t2]?)).bind id
  return fmax (s.getIndividualOrDefaultF64 p1 option) (s.getIndividualOrDefaultF64 p2 option)

private def localSpacingForTypes? (s : Spacings) (table : Array (Array (Option (Property Float)))) (t1 t2 : NodeType) : Option Float := do
  let option ← (table[ElkEnum.ordinal t1]?.bind (·[ElkEnum.ordinal t2]?)).bind id
  return s.graphSpacingValue option

/-- `getHorizontalSpacing(n1, n2)`: `none` = Java `UnspecifiedSpacingException`. -/
def getHorizontalSpacing? (s : Spacings) (t1 : NodeType) (p1 : PropertyMap) (t2 : NodeType) (p2 : PropertyMap) : Option Float :=
  s.localSpacing? s.horizontal t1 p1 t2 p2

/-- `getVerticalSpacing(n1, n2)`. -/
def getVerticalSpacing? (s : Spacings) (t1 : NodeType) (p1 : PropertyMap) (t2 : NodeType) (p2 : PropertyMap) : Option Float :=
  s.localSpacing? s.vertical t1 p1 t2 p2

/-- `getHorizontalSpacing(NodeType, NodeType)`. -/
def getHorizontalSpacingForTypes? (s : Spacings) (t1 t2 : NodeType) : Option Float :=
  s.localSpacingForTypes? s.horizontal t1 t2

/-- `getVerticalSpacing(NodeType, NodeType)`. -/
def getVerticalSpacingForTypes? (s : Spacings) (t1 t2 : NodeType) : Option Float :=
  s.localSpacingForTypes? s.vertical t1 t2

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
