import Elk.Core.Exceptions
import Elk.Core.Util.Adapters.GraphAdapters
import Elk.Alg.Common.NodeSpacing.CellSystem
import Elk.Alg.Common.NodeSpacing.Internal.NodeLabelLocation
import Elk.Alg.Common.NodeSpacing.Internal.PortContext
import Elk.Core.Util.FloatConst
open Elk.Core.Util.FloatConst
/-!
# `org.eclipse.elk.alg.common.nodespacing.internal.NodeContext`

Data holder for one node during node size calculation (elk-rs `internal::NodeContext`). The
node's settings are copied once through the `GraphAdapters` record (like elk-rs; Java reads some
of them lazily), the node size is kept in `nodeSize` until it is applied.

The cell system lives in `cells : CellArena L`. `nodeContainer` (a vertical strip) and its center
cell `nodeContainerMiddleRow` (a horizontal strip) are created by `new`; the other cells are created
by the algorithm phases and registered by id in
* `insidePortLabelCells` / `outsideNodeLabelContainers`: indexed by `PortSide` ordinal
  (Java `EnumMap<PortSide, …>`; `UNDEFINED` is never used),
* `nodeLabelCells`: indexed by `NodeLabelLocation` ordinal (Java `EnumMap<NodeLabelLocation, …>`).
Because every holder shares the same `CellId`, the Java object sharing is preserved and elk-rs'
`sync_inside_port_label_cell_rectangles` is unnecessary (kept as a documented no-op).

`portContexts` reproduces Java's `TreeMultimap.create(comparePortSides, comparePortContexts)`:
one array per `PortSide` ordinal; sides iterate by ordinal (NORTH, EAST, SOUTH, WEST); within a
side NORTH/EAST contexts are in ascending and SOUTH/WEST contexts in descending volatile-id order
(elk-rs appends in port order and reverses SOUTH/WEST in `PortContextCreator`; `insertPortContext`
inserts at the sorted position directly).

Like Java, the constructor throws `UnsupportedConfigurationException("Invalid port label placement:
[..]")` / `("Invalid node label placement: [..]")` for an invalid `PORT_LABELS_PLACEMENT` /
`NODE_LABELS_PLACEMENT` (`PortLabelPlacement.isValid` / `NodeLabelPlacement.isValid`; elk-rs has no
such check and lays the node out). Deviation from Java (following elk-rs): `portAlignment*` /
`nodeSizeMinimum` are read once at construction.
-/

namespace Elk.Alg.Common.NodeSpacing.Internal

open Elk Elk.Graph Elk.Core.Math Elk.Core.Util Elk.Core.Options Elk.Core.Util.Adapters
open Elk.Alg.Common.NodeSpacing.CellSystem

/-- `NodeContext`: the node, its copied settings, its port contexts and its cell system. -/
structure NodeContext (N P L : Type) where
  /-- `node`: the node we calculate stuff for. -/
  node : N
  /-- `nodeSize`: the node size used during the algorithm (applied by `applyNodeSize`). -/
  nodeSize : KVector
  /-- `treatAsCompoundNode`: `isCompoundNode() || INSIDE_SELF_LOOPS_ACTIVATE`. -/
  treatAsCompoundNode : Bool
  /-- `NODE_SIZE_CONSTRAINTS`. -/
  sizeConstraints : EnumSet SizeConstraint
  /-- `NODE_SIZE_OPTIONS`. -/
  sizeOptions : EnumSet SizeOptions
  /-- `PORT_CONSTRAINTS`. -/
  portConstraints : PortConstraints
  /-- `PORT_LABELS_PLACEMENT`. -/
  portLabelsPlacement : EnumSet PortLabelPlacement
  /-- `PORT_LABELS_TREAT_AS_GROUP`. -/
  portLabelsTreatAsGroup : Bool
  /-- `NODE_LABELS_PLACEMENT` (default placement of node labels). -/
  nodeLabelPlacement : EnumSet NodeLabelPlacement
  /-- `NODE_LABELS_PADDING` (individual or inherited). -/
  nodeLabelsPadding : ElkPadding
  /-- `SPACING_LABEL_NODE` (individual or inherited): space between a node and its outside labels. -/
  nodeLabelSpacing : Float
  /-- `SPACING_LABEL_LABEL` (individual or inherited). -/
  labelLabelSpacing : Float
  /-- `labelCellSpacing = 2 * labelLabelSpacing`: space between two label cells. -/
  labelCellSpacing : Float
  /-- `SPACING_PORT_PORT` (individual or inherited). -/
  portPortSpacing : Float
  /-- `SPACING_LABEL_PORT_HORIZONTAL` (individual or inherited). -/
  portLabelSpacingHorizontal : Float
  /-- `SPACING_LABEL_PORT_VERTICAL` (individual or inherited). -/
  portLabelSpacingVertical : Float
  /-- `SPACING_PORTS_SURROUNDING` (individual or inherited). -/
  surroundingPortMargins : ElkMargin
  /-- `TOPDOWN_LAYOUT`. -/
  topdownLayout : Bool
  /-- `NODE_SIZE_FIXED_GRAPH_SIZE` of the parent graph (`false` without parent). -/
  nodeSizeFixedGraphSize : Bool
  /-- `NODE_SIZE_MINIMUM`. -/
  nodeSizeMinimum : KVector
  /-- `PORT_ALIGNMENT_NORTH` if explicitly set on the node. -/
  portAlignmentNorth : Option PortAlignment
  /-- `PORT_ALIGNMENT_SOUTH` if explicitly set on the node. -/
  portAlignmentSouth : Option PortAlignment
  /-- `PORT_ALIGNMENT_EAST` if explicitly set on the node. -/
  portAlignmentEast : Option PortAlignment
  /-- `PORT_ALIGNMENT_WEST` if explicitly set on the node. -/
  portAlignmentWest : Option PortAlignment
  /-- `PORT_ALIGNMENT_DEFAULT`. -/
  portAlignmentDefault : PortAlignment
  /-- `portContexts`, one array per `PortSide` ordinal (see the module doc for the order). -/
  portContexts : Array (Array (PortContext P L))
  /-- The arena holding every cell of this node's cell system. -/
  cells : CellArena L
  /-- `nodeContainer`: the main (vertical strip) cell that holds all cells of the node. -/
  nodeContainer : CellId
  /-- `nodeContainerMiddleRow`: the center (horizontal strip) cell of `nodeContainer`. -/
  nodeContainerMiddleRow : CellId
  /-- `insidePortLabelCells` (atomic cells), indexed by `PortSide` ordinal. -/
  insidePortLabelCells : Array (Option CellId)
  /-- `outsideNodeLabelContainers` (strip cells), indexed by `PortSide` ordinal. -/
  outsideNodeLabelContainers : Array (Option CellId)
  /-- `nodeLabelCells` (label cells), indexed by `NodeLabelLocation` ordinal. -/
  nodeLabelCells : Array (Option CellId)
  deriving Inhabited

namespace NodeContext

variable {N P L : Type}

/-- `NodeContext.comparePortSides(side1, side2)`: by ordinal. -/
def comparePortSides (s1 s2 : PortSide) : Ordering :=
  Ord.compare (ElkEnum.ordinal s1) (ElkEnum.ordinal s2)

/-- `NodeContext.comparePortContexts(pc1, pc2)`: by side, then ascending volatile id on
NORTH/EAST and descending volatile id on SOUTH/WEST. -/
def comparePortContexts (pc1 pc2 : PortContext P L) : Ordering :=
  match comparePortSides pc1.portSide pc2.portSide with
  | .eq =>
    match pc1.portSide with
    | .north | .east => Ord.compare pc1.volatileId pc2.volatileId
    | .south | .west => Ord.compare pc2.volatileId pc1.volatileId
    | .undefined => .eq
  | o => o

/-- The placement checks of Java's `NodeContext` constructor: throws
`UnsupportedConfigurationException("Invalid port label placement: " + portLabelsPlacement)` unless
`PortLabelPlacement.isValid(portLabelsPlacement)`, then
`UnsupportedConfigurationException("Invalid node label placement: " + nodeLabelPlacement)` unless
`NodeLabelPlacement.isValid(nodeLabelPlacement)` (Java `EnumSet.toString()`, e.g.
`[OUTSIDE, ALWAYS_SAME_SIDE, SPACE_EFFICIENT]`). -/
def validatePlacements {m : Type → Type} [Monad m] [MonadExcept IO.Error m]
    (portLabelsPlacement : EnumSet PortLabelPlacement) (nodeLabelPlacement : EnumSet NodeLabelPlacement) :
    m Unit := do
  if !PortLabelPlacement.isValid portLabelsPlacement then
    Elk.Core.throwUnsupportedConfiguration s!"Invalid port label placement: {portLabelsPlacement.toJavaString}"
  if !NodeLabelPlacement.isValid nodeLabelPlacement then
    Elk.Core.throwUnsupportedConfiguration s!"Invalid node label placement: {nodeLabelPlacement.toJavaString}"

/-- `ElementOps.getPropertyFrom` with the adapter's `defaultOverride` passed as a function (the
same decoding: the stored value, else the override's value, else the property default). -/
@[inline] def propertyFrom {α : Type} [PropCodec α] (override : PropKey → Option PropValue) (props : PropertyMap)
    (p : Property α) : Option α :=
  match props.getRaw? p.key with
  | some raw =>
    match PropCodec.dec raw with
    | some v => some v
    | none => p.default
  | none =>
    match override p.key with
    | some raw => (PropCodec.dec raw : Option α) <|> p.default
    | none => p.default

/-- `ElementOps.getPropertyDFrom` with the override passed as a function. -/
@[inline] def propertyDFrom {α : Type} [PropCodec α] (override : PropKey → Option PropValue) (props : PropertyMap)
    (p : Property α) (d : α) : α :=
  (propertyFrom override props p).getD d

/-- `GraphAdapters.getIndividualOrInheritedIn` with the graph adapter's override passed as a
function: the individual spacing if set, else the graph's value, else the property default. -/
@[inline] def individualOrInheritedIn {α : Type} [PropCodec α] (graphOverride : PropKey → Option PropValue)
    (individual : Option IndividualSpacings) (graphProps : Option PropertyMap) (p : Property α) : Option α :=
  let fromIndividual : Option α := match individual with
    | some ind => if ind.props.has p then ind.props.get p else none
    | none => none
  match fromIndividual with
  | some v => some v
  | none =>
    let fromGraph : Option α := match graphProps with
      | some gp => propertyFrom graphOverride gp p
      | none => none
    match fromGraph with
    | some v => some v
    | none => p.default

/-- The body of `new` on the values read through the adapters: the node, its size and option map,
`isCompoundNode`, the option map of its graph (`none` without graph) and the `defaultOverride`s of
the node and graph adapters. `@[specialize]`: the LGraph fast path passes constant overrides.
Throws like `new` (`validatePlacements`). -/
@[specialize] def build {m : Type → Type} [Monad m] [MonadExcept IO.Error m] (nodeOverride graphOverride : PropKey → Option PropValue)
    (node : N) (nodeSize : KVector) (props : PropertyMap) (isCompound : Bool) (graphProps : Option PropertyMap) :
    m (NodeContext N P L) := do
  -- Top-down layout
  let topdownLayout := propertyDFrom nodeOverride props CoreOptions.TOPDOWN_LAYOUT false
  -- Compound node
  let insideSelfLoops := propertyDFrom nodeOverride props CoreOptions.INSIDE_SELF_LOOPS_ACTIVATE false
  let treatAsCompoundNode := isCompound || insideSelfLoops
  -- Core size settings
  let sizeConstraints := propertyDFrom nodeOverride props CoreOptions.NODE_SIZE_CONSTRAINTS EnumSet.empty
  let sizeOptions := propertyDFrom nodeOverride props CoreOptions.NODE_SIZE_OPTIONS EnumSet.empty
  let portConstraints := propertyDFrom nodeOverride props CoreOptions.PORT_CONSTRAINTS PortConstraints.undefined
  let portLabelsPlacement := propertyDFrom nodeOverride props CoreOptions.PORT_LABELS_PLACEMENT EnumSet.empty
  let portLabelsTreatAsGroup := propertyDFrom nodeOverride props CoreOptions.PORT_LABELS_TREAT_AS_GROUP true
  let nodeLabelPlacement := propertyDFrom nodeOverride props CoreOptions.NODE_LABELS_PLACEMENT EnumSet.empty
  -- Java checks the port label placement right after reading it and the node label placement right
  -- after reading that; the reads in between have no side effects
  validatePlacements portLabelsPlacement nodeLabelPlacement
  -- Copy spacings for convenience (`getIndividualOrInherited`, the node's individual spacings and
  -- the graph's option map read once; `GraphAdapters.spacingSourceFrom`)
  let individual : Option IndividualSpacings :=
    if props.hasKey CoreOptions.SPACING_INDIVIDUAL.key then propertyFrom nodeOverride props CoreOptions.SPACING_INDIVIDUAL
    else none
  let nodeLabelsPadding :=
    (individualOrInheritedIn graphOverride individual graphProps CoreOptions.NODE_LABELS_PADDING).getD {}
  let nodeLabelSpacing :=
    (individualOrInheritedIn graphOverride individual graphProps CoreOptions.SPACING_LABEL_NODE).getD fl0p0
  let labelLabelSpacing :=
    (individualOrInheritedIn graphOverride individual graphProps CoreOptions.SPACING_LABEL_LABEL).getD fl0p0
  let portPortSpacing :=
    (individualOrInheritedIn graphOverride individual graphProps CoreOptions.SPACING_PORT_PORT).getD fl0p0
  let portLabelSpacingHorizontal :=
    (individualOrInheritedIn graphOverride individual graphProps CoreOptions.SPACING_LABEL_PORT_HORIZONTAL).getD fl0p0
  let portLabelSpacingVertical :=
    (individualOrInheritedIn graphOverride individual graphProps CoreOptions.SPACING_LABEL_PORT_VERTICAL).getD fl0p0
  let surroundingPortMargins :=
    (individualOrInheritedIn graphOverride individual graphProps CoreOptions.SPACING_PORTS_SURROUNDING).getD {}
  let labelCellSpacing := fl2p0 * labelLabelSpacing
  -- Port alignment per side
  let portAlignmentDefault := propertyDFrom nodeOverride props CoreOptions.PORT_ALIGNMENT_DEFAULT PortAlignment.justified
  let sideAlignment (p : Property PortAlignment) : Option PortAlignment :=
    if props.hasKey p.key then propertyFrom nodeOverride props p else none
  let portAlignmentNorth := sideAlignment CoreOptions.PORT_ALIGNMENT_NORTH
  let portAlignmentSouth := sideAlignment CoreOptions.PORT_ALIGNMENT_SOUTH
  let portAlignmentEast := sideAlignment CoreOptions.PORT_ALIGNMENT_EAST
  let portAlignmentWest := sideAlignment CoreOptions.PORT_ALIGNMENT_WEST
  -- Node minimum size
  let nodeSizeMinimum := propertyDFrom nodeOverride props CoreOptions.NODE_SIZE_MINIMUM KVector.zero
  -- NODE_SIZE_FIXED_GRAPH_SIZE comes from the parent graph
  let nodeSizeFixedGraphSize := match graphProps with
    | some gp => propertyDFrom graphOverride gp CoreOptions.NODE_SIZE_FIXED_GRAPH_SIZE false
    | none => false
  -- Create main cells (the others will be created later by the algorithm phases)
  let symmetry := !sizeOptions.contains .asymmetrical
  let (cells, nodeContainer) := (CellArena.empty : CellArena L).createStrip .vertical symmetry fl0p0
  let (cells, middleRow) := cells.createStrip .horizontal symmetry fl0p0
  let cells := cells.setCell nodeContainer .center (some middleRow)
  return {
    node, nodeSize, treatAsCompoundNode, sizeConstraints, sizeOptions, portConstraints,
    portLabelsPlacement, portLabelsTreatAsGroup, nodeLabelPlacement, nodeLabelsPadding,
    nodeLabelSpacing, labelLabelSpacing, labelCellSpacing, portPortSpacing,
    portLabelSpacingHorizontal, portLabelSpacingVertical, surroundingPortMargins, topdownLayout,
    nodeSizeFixedGraphSize, nodeSizeMinimum, portAlignmentNorth, portAlignmentSouth,
    portAlignmentEast, portAlignmentWest, portAlignmentDefault
    portContexts := Array.replicate (ElkEnum.count (α := PortSide)) #[]
    cells, nodeContainer
    nodeContainerMiddleRow := middleRow
    insidePortLabelCells := Array.replicate (ElkEnum.count (α := PortSide)) none
    outsideNodeLabelContainers := Array.replicate (ElkEnum.count (α := PortSide)) none
    nodeLabelCells := Array.replicate (ElkEnum.count (α := NodeLabelLocation)) none }

/-- Creates a new context for the given node, fully initialized with the node's settings (Java
`new NodeContext(parentGraph, node)`, elk-rs `NodeContext::new(node)`). Creates the node
container (vertical strip) and its middle row (horizontal strip, in the container's center), both
symmetrical unless `SizeOptions.ASYMMETRICAL` is set and without gap. Throws like Java for an
invalid port or node label placement (`validatePlacements`; elk-rs does not check). The adapter
reads (size, option map, `isCompoundNode`, graph and its option map) come first; they have no side
effects, so reading the graph before the placement check is unobservable. -/
def new {m : Type → Type} [Monad m] [MonadExcept IO.Error m] {G E : Type} (a : GraphAdapters m G N P L E)
    (node : N) : m (NodeContext N P L) := do
  let nodeSize ← a.node.getSize node
  -- The node's options are read from its option map, read once (`ElementOps.getProps`)
  let props ← a.node.getProps node
  let isCompound ← a.isCompoundNode node
  let graphProps ← match ← a.getGraph node with
    | some g => some <$> a.graph.getProps g
    | none => pure none
  build a.node.defaultOverride a.graph.defaultOverride node nodeSize props isCompound graphProps

/-! ### Cell system access -/

/-- Updates the cell arena (taken out of the context first, so that `f` can update it in place). -/
@[inline] def modifyCells (ctx : NodeContext N P L) (f : CellArena L → CellArena L) : NodeContext N P L :=
  let cells := ctx.cells
  let ctx : NodeContext N P L := { ctx with cells := {} }
  { ctx with cells := f cells }

/-- `modifyCells` for an update that also returns a value (e.g. the id of a created cell). -/
@[inline] def modifyCellsGet {α : Type} (ctx : NodeContext N P L) (f : CellArena L → CellArena L × α) :
    NodeContext N P L × α :=
  let cells := ctx.cells
  let ctx : NodeContext N P L := { ctx with cells := {} }
  let (cells, r) := f cells
  ({ ctx with cells }, r)

/-- elk-rs `NodeContext::inside_node_label_container()`: the center cell of the middle row if it
is a grid (created by `NodeLabelCellCreator`), else `none`. -/
def insideNodeLabelContainer (ctx : NodeContext N P L) : Option CellId :=
  match ctx.cells.getCell ctx.nodeContainerMiddleRow .center with
  | some c => if ctx.cells.isGrid c then some c else none
  | none => none

/-- `insidePortLabelCells.get(side)`. -/
def insidePortLabelCell (ctx : NodeContext N P L) (side : PortSide) : Option CellId :=
  (ctx.insidePortLabelCells[ElkEnum.ordinal side]?).getD none

/-- `insidePortLabelCells.put(side, cell)`. -/
def setInsidePortLabelCell (ctx : NodeContext N P L) (side : PortSide) (cell : Option CellId) :
    NodeContext N P L :=
  -- the array is taken out of the context first so that it is updated in place
  let arr := ctx.insidePortLabelCells
  let ctx : NodeContext N P L := { ctx with insidePortLabelCells := #[] }
  { ctx with insidePortLabelCells := arr.setIfInBounds (ElkEnum.ordinal side) cell }

/-- `outsideNodeLabelContainers.get(side)`. -/
def outsideNodeLabelContainer (ctx : NodeContext N P L) (side : PortSide) : Option CellId :=
  (ctx.outsideNodeLabelContainers[ElkEnum.ordinal side]?).getD none

/-- `outsideNodeLabelContainers.put(side, cell)`. -/
def setOutsideNodeLabelContainer (ctx : NodeContext N P L) (side : PortSide) (cell : Option CellId) :
    NodeContext N P L :=
  -- the array is taken out of the context first so that it is updated in place
  let arr := ctx.outsideNodeLabelContainers
  let ctx : NodeContext N P L := { ctx with outsideNodeLabelContainers := #[] }
  { ctx with outsideNodeLabelContainers := arr.setIfInBounds (ElkEnum.ordinal side) cell }

/-- `nodeLabelCells.get(location)`. -/
def nodeLabelCell (ctx : NodeContext N P L) (location : NodeLabelLocation) : Option CellId :=
  (ctx.nodeLabelCells[ElkEnum.ordinal location]?).getD none

/-- `nodeLabelCells.put(location, cell)`. -/
def setNodeLabelCell (ctx : NodeContext N P L) (location : NodeLabelLocation) (cell : Option CellId) :
    NodeContext N P L :=
  -- the array is taken out of the context first so that it is updated in place
  let arr := ctx.nodeLabelCells
  let ctx : NodeContext N P L := { ctx with nodeLabelCells := #[] }
  { ctx with nodeLabelCells := arr.setIfInBounds (ElkEnum.ordinal location) cell }

/-- elk-rs `NodeContext::sync_inside_port_label_cell_rectangles()`: a no-op. elk-rs needs it
because its `inside_port_label_cells` map holds copies of the cells in the cell tree; here both
refer to the same arena cell. Kept so call sites can be ported 1:1. -/
@[inline] def syncInsidePortLabelCellRectangles (ctx : NodeContext N P L) : NodeContext N P L := ctx

/-! ### Port contexts -/

/-- `portContexts.get(side)`: the side's contexts in `TreeMultimap` order. -/
def portContextsOf (ctx : NodeContext N P L) (side : PortSide) : Array (PortContext P L) :=
  (ctx.portContexts[ElkEnum.ordinal side]?).getD #[]

/-- `portContexts.values()`: all contexts, sides by ordinal, each side in `TreeMultimap` order. -/
def allPortContexts (ctx : NodeContext N P L) : Array (PortContext P L) := Id.run do
  let total := ctx.portContexts.foldl (fun n pcs => n + pcs.size) 0
  let mut all : Array (PortContext P L) := Array.mkEmpty total
  for pcs in ctx.portContexts do
    for pc in pcs do
      all := all.push pc
  return all

/-- Replaces the contexts of one side. -/
def setPortContextsOf (ctx : NodeContext N P L) (side : PortSide) (pcs : Array (PortContext P L)) :
    NodeContext N P L :=
  -- the array is taken out of the context first so that it is updated in place
  let arr := ctx.portContexts
  let ctx : NodeContext N P L := { ctx with portContexts := #[] }
  { ctx with portContexts := arr.setIfInBounds (ElkEnum.ordinal side) pcs }

/-- Updates the contexts of one side in place (elk-rs `port_contexts.get_mut(&side)`). -/
def modifyPortContextsOf (ctx : NodeContext N P L) (side : PortSide)
    (f : Array (PortContext P L) → Array (PortContext P L)) : NodeContext N P L :=
  -- take the arrays out of the context so that `modify` and `f` update them in place
  let pcs := ctx.portContexts
  let ctx : NodeContext N P L := { ctx with portContexts := #[] }
  { ctx with portContexts := pcs.modifyIn (ElkEnum.ordinal side) f }

/-- Updates the `i`-th context of one side (ignored if out of range). -/
def modifyPortContext (ctx : NodeContext N P L) (side : PortSide) (i : Nat)
    (f : PortContext P L → PortContext P L) : NodeContext N P L :=
  ctx.modifyPortContextsOf side (·.modify i f)

/-- Updates every context of every side, in `portContexts.values()` order. -/
def modifyAllPortContexts (ctx : NodeContext N P L) (f : PortContext P L → PortContext P L) :
    NodeContext N P L :=
  let pcs := ctx.portContexts
  let ctx : NodeContext N P L := { ctx with portContexts := #[] }
  { ctx with portContexts := pcs.map (·.map f) }

/-- elk-rs `port_contexts.entry(side).or_default().push(pc)`: appends to the context's side
(`PortContextCreator` then reverses SOUTH/WEST, see the module doc). -/
def addPortContext (ctx : NodeContext N P L) (pc : PortContext P L) : NodeContext N P L :=
  ctx.modifyPortContextsOf pc.portSide (·.push pc)

/-- Java `portContexts.put(side, pc)` on the `TreeMultimap`: inserts at the position given by
`comparePortContexts` (after contexts comparing equal; Java would drop such a duplicate, elk-rs
keeps it — volatile ids are unique in practice). -/
def insertPortContext (ctx : NodeContext N P L) (pc : PortContext P L) : NodeContext N P L :=
  ctx.modifyPortContextsOf pc.portSide fun pcs => Id.run do
    let mut pos := pcs.size
    for i in [0:pcs.size] do
      if let some other := pcs[i]? then
        if comparePortContexts other pc == .gt then
          pos := i
          break
    return pcs.insertIdxIfInBounds pos pc

/-! ### Utility methods -/

/-- `NodeContext.getPortAlignment(portSide)`: the side-specific alignment if set on the node,
else `PORT_ALIGNMENT_DEFAULT`. -/
def getPortAlignment (ctx : NodeContext N P L) (portSide : PortSide) : PortAlignment :=
  let specific := match portSide with
    | .north => ctx.portAlignmentNorth
    | .south => ctx.portAlignmentSouth
    | .east => ctx.portAlignmentEast
    | .west => ctx.portAlignmentWest
    | .undefined => none
  specific.getD ctx.portAlignmentDefault

/-- `NodeContext.applyNodeSize()`: writes `nodeSize` to the node. -/
def applyNodeSize {m : Type → Type} [Monad m] {G E : Type} (a : GraphAdapters m G N P L E)
    (ctx : NodeContext N P L) : m Unit :=
  a.node.setSize ctx.node ctx.nodeSize

end NodeContext

end Elk.Alg.Common.NodeSpacing.Internal
