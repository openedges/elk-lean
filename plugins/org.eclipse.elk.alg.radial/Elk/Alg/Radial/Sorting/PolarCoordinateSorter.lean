import Elk.Graph
import Elk.Core.Options
import Elk.Core.Util.Java
import Elk.Core.Util.Sort
import Elk.Alg.Radial.RadialUtil
import Elk.Alg.Radial.Options.SortingStrategy
import Elk.Alg.Radial.Sorting.IRadialSorter
import Elk.Alg.Radial.Sorting.IDSorter
/-!
# `org.eclipse.elk.alg.radial.sorting.PolarCoordinateSorter`

Port of `polar_coordinate_sorter.rs` (elk-rs): sorts the nodes of one radius by their polar
angle. Follows the Rust port (which differs from Java in `sort_for_parent`):

* `sort_with_offset` computes the polar angle of the `POSITION` *property* of every node
  (`(0, 0)` if unset, i.e. an offset-only angle) and sorts the indices stably with a fuzzy
  comparison (`epsilon = 1e-10`);
* `initialize` (called on the first `sort`) assigns increasing `ORDER_ID`s to the tree, ordered
  per level by `sort_with_offset` with the offset selected from the angle of the parent node
  location; `sort` then orders by `ORDER_ID` with the `IDSorter`;
* `sort_for_parent` (used by `EadesRadial`) sorts the successors directly with the offset derived
  from the parent location and does not touch the `ORDER_ID`s.

The state of the Rust struct (`id_sorter: Option<IDSorter>`) is an `IO.Ref Bool`.

This module also hosts `SortingStrategy.create`, the factory half of the Rust
`sorting_strategy.rs`.
-/
namespace Elk.Alg.Radial.Sorting

open Elk.Graph Elk.Core.Options Elk.Core.Util Elk.Alg.Radial.Options

namespace PolarCoordinateSorter

/-- `DEGREE_45`. -/
def DEGREE_45 : Float := 0.25 * Float.pi
/-- `DEGREE_90`. -/
def DEGREE_90 : Float := 0.5 * Float.pi
/-- `DEGREE_135`. -/
def DEGREE_135 : Float := 0.75 * Float.pi
/-- `DEGREE_225`. -/
def DEGREE_225 : Float := 1.25 * Float.pi
/-- `DEGREE_270`. -/
def DEGREE_270 : Float := 1.5 * Float.pi
/-- `DEGREE_315`. -/
def DEGREE_315 : Float := 1.75 * Float.pi

/-- `sort_with_offset(nodes, offset)`: the nodes stably sorted by the polar angle of their
`POSITION` property shifted by `offset`. -/
def sortWithOffset (nodes : Array NodeId) (offset : Float) : ElkM (Array NodeId) := do
  let mut arcs : Array Float := #[]
  for node in nodes do
    let n ← ElkM.getNode node
    let position := (n.props.get CoreOptions.POSITION).getD ⟨0.0, 0.0⟩
    let arc := Float.atan2 position.y position.x
    let arc := if arc < 0.0 then arc + RadialUtil.TWO_PI else arc
    let arc := arc + offset
    let arc := if arc > RadialUtil.TWO_PI then arc - RadialUtil.TWO_PI else arc
    arcs := arcs.push arc
  let indices := stableSort (Array.range nodes.size) fun a b =>
    RadialUtil.fuzzyCompare arcs[a]! arcs[b]! RadialUtil.EPSILON
  return indices.map fun i => nodes[i]!

/-- `node_arc(node)`: the polar angle of the node center (`0 .. 2 PI`). -/
def nodeArc (node : NodeId) : ElkM Float := do
  let n ← ElkM.getNode node
  let arc := Float.atan2 (n.y + n.height / 2.0) (n.x + n.width / 2.0)
  return if arc < 0.0 then arc + RadialUtil.TWO_PI else arc

/-- `set_id_for_nodes(nodes, id_offset)`: assigns `ORDER_ID`s to `nodes` and, recursively, to
their sorted successors; returns the next free id. -/
partial def setIdForNodes (nodes : Array NodeId) (idOffset : Int) : ElkM Int := do
  let mut id := idOffset
  let mut nextLayerId : Int := 0
  for node in nodes do
    ElkM.setNodeProp node RadialOptions.ORDER_ID id
    let arc ← nodeArc node
    id := id + 1
    let mut nodeSuccessors ← RadialUtil.getSuccessors node
    if !(DEGREE_45 <= arc && arc <= DEGREE_315) then
      nodeSuccessors ← sortWithOffset nodeSuccessors Float.pi
    else if arc <= DEGREE_315 && arc > DEGREE_225 then
      nodeSuccessors ← sortWithOffset nodeSuccessors DEGREE_270
    else if arc <= DEGREE_225 && arc > DEGREE_135 then
      nodeSuccessors ← sortWithOffset nodeSuccessors 0.0
    else if arc <= DEGREE_135 then
      nodeSuccessors ← sortWithOffset nodeSuccessors DEGREE_90
    nextLayerId ← setIdForNodes nodeSuccessors nextLayerId
  return id

/-- `initialize(root)`: marks the sorter initialised and assigns the `ORDER_ID`s of the tree. -/
def initializeSorter (initialized : IO.Ref Bool) (root : NodeId) : ElkM Unit := do
  initialized.set true
  let successors ← RadialUtil.getSuccessors root
  let sorted ← sortWithOffset successors 0.0
  let _ ← setIdForNodes sorted 0

/-- `sort(nodes)`: initialises from the tree root of the first node on first use, then sorts by
`ORDER_ID`. -/
def sort (initialized : IO.Ref Bool) (nodes : Array NodeId) : ElkM (Array NodeId) := do
  if nodes.isEmpty then return nodes
  if !(← initialized.get) then
    let root ← RadialUtil.findRootOfNode nodes[0]!
    initializeSorter initialized root
  IDSorter.sort nodes

/-- `sort_for_parent(nodes, parent, root, is_root_level)`: sorts the successors of `parent`
directly with the offset derived from the location of `parent`. -/
def sortForParent (nodes : Array NodeId) (parent : NodeId) (isRootLevel : Bool) :
    ElkM (Array NodeId) := do
  if nodes.isEmpty then return nodes
  let offset ← if isRootLevel then pure 0.0 else do
    let arc ← nodeArc parent
    pure (if !(DEGREE_45 <= arc && arc <= DEGREE_315) then Float.pi
      else if arc > DEGREE_225 then DEGREE_270
      else if arc > DEGREE_135 then 0.0
      else DEGREE_90)
  sortWithOffset nodes offset

/-- `PolarCoordinateSorter::default()`: a fresh, uninitialised sorter. -/
def create : IO IRadialSorter := do
  let initialized ← IO.mkRef false
  return {
    sort := fun nodes => sort initialized nodes
    init := fun root => initializeSorter initialized root
    sortForParent := fun nodes parent _ isRootLevel => sortForParent nodes parent isRootLevel }

end PolarCoordinateSorter

end Elk.Alg.Radial.Sorting

namespace Elk.Alg.Radial.Options.SortingStrategy

open Elk.Alg.Radial.Sorting

/-- `SortingStrategy::create()`: `none` has no sorter. -/
def create : SortingStrategy → IO (Option IRadialSorter)
  | .none => pure Option.none
  | .polarCoordinate => do return some (← PolarCoordinateSorter.create)
  | .id => pure (some IDSorter.sorter)

end Elk.Alg.Radial.Options.SortingStrategy
