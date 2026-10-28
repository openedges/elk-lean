import Elk.Graph
import Elk.Core.Options
import Elk.Alg.Radial.InternalProperties
import Elk.Alg.Radial.RadialUtil
import Elk.Alg.Radial.Options.RadialOptions
import Elk.Alg.Radial.Options.SortingStrategy
import Elk.Alg.Radial.Sorting.IRadialSorter
import Elk.Alg.Radial.Sorting.PolarCoordinateSorter
import Elk.Alg.Radial.Intermediate.Compaction.AbstractRadiusExtensionCompaction
import Elk.Alg.Radial.Intermediate.Compaction.IRadialCompactor
/-!
# `org.eclipse.elk.alg.radial.intermediate.compaction.RadialCompaction`

Port of `radial_compaction.rs` (elk-rs): contracts the layers radius by radius towards the root
until a node would overlap a neighbour in the layer, its tree parent, or the previous radius.

The mutable `last_radius` field of Rust is only written once per level, right before the
recursive call for the next level, so it is a parameter of the recursion here.
-/
/-! Float literals as global constants (FL): inside branches, loops and specialised code the compiler
shares a literal's `Nat`/`Bool` arguments with unrelated variables (CSE) and then parses it on every
evaluation (`FastFloat.ofScientificImpl`); a top-level constant is a load (PLAN §7.1 items 17, 22). -/
private def fl0p0 : Float := 0.0

namespace Elk.Alg.Radial.Intermediate.Compaction

open Elk.Graph Elk.Core.Options Elk.Alg.Radial.Options Elk.Alg.Radial.Sorting

namespace RadialCompaction

/-- `calculate_radius(root, node)`: the distance between the centers. -/
def calculateRadius (root node : NodeId) : ElkM Float := do
  let (xPos, yPos) ← AbstractRadiusExtensionCompaction.nodeCenter node
  let (rootX, rootY) ← AbstractRadiusExtensionCompaction.nodeCenter root
  let vectorX := xPos - rootX
  let vectorY := yPos - rootY
  return Float.sqrt (vectorX * vectorX + vectorY * vectorY)

/-- `overlapping(root, nodes)`. -/
def overlapping (base : AbstractRadiusExtensionCompaction) (lastRadius : Float) (root : NodeId)
    (nodes : Array NodeId) : ElkM Bool := do
  if ← base.overlapLayer nodes then return true
  for node in nodes do
    if let some parent ← RadialUtil.getTreeParent node then
      if ← base.overlap node parent then return true
    if (← calculateRadius root node) - base.spacing <= lastRadius then return true
  return false

/-- `contract(root, nodes)`. -/
partial def contract (base : AbstractRadiusExtensionCompaction) (sorter : Option IRadialSorter)
    (root : NodeId) (nodes : Array NodeId) (lastRadius : Float) : RadialM Unit := do
  if nodes.isEmpty then return
  let mut isOverlapping ← overlapping base lastRadius root nodes
  let mut wasContracted := false
  while !isOverlapping do
    base.contractLayer root nodes true
    wasContracted := true
    isOverlapping ← overlapping base lastRadius root nodes
  if wasContracted then base.contractLayer root nodes false
  let mut nextLevelNodes ← RadialUtil.getNextLevelNodes nodes
  if let some sorter := sorter then
    nextLevelNodes ← sorter.sort nextLevelNodes
  let newLastRadius ← calculateRadius root nodes[0]!
  contract base sorter root nextLevelNodes newLastRadius

/-- `compact(graph)`. -/
def compact (graph : NodeId) : RadialM Unit := do
  let some root ← RadialUtil.rootFromGraph graph | return
  let props := (← ElkM.getNode graph).props
  let sorter ← (props.getD RadialOptions.SORTER SortingStrategy.none).create
  let mut base : AbstractRadiusExtensionCompaction := {}
  if let some stepSize := props.get RadialOptions.COMPACTION_STEP_SIZE then
    base := { base with compactionStep := stepSize }
  base := { base with spacing := (props.get CoreOptions.SPACING_NODE_NODE).getD fl0p0 }
  let mut firstLevelNodes ← RadialUtil.getNextLevelNodes #[root]
  if let some sorter := sorter then
    firstLevelNodes ← sorter.sort firstLevelNodes
  contract base sorter root firstLevelNodes fl0p0

/-- The `IRadialCompactor` of this class. -/
def compactor : IRadialCompactor := { compact := compact }

end RadialCompaction

end Elk.Alg.Radial.Intermediate.Compaction
