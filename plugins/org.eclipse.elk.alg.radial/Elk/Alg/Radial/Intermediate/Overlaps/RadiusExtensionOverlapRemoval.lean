import Std.Data.HashMap
import Std.Data.HashSet
import Elk.Graph
import Elk.Core.Alg
import Elk.Core.Options
import Elk.Core.Util.ProgressMonitor
import Elk.Alg.Radial.InternalProperties
import Elk.Alg.Radial.RadialUtil
import Elk.Alg.Radial.Options.OverlapRemovalStrategy
import Elk.Alg.Radial.Options.RadialOptions
import Elk.Alg.Radial.Options.SortingStrategy
import Elk.Alg.Radial.Sorting.IRadialSorter
import Elk.Alg.Radial.Sorting.PolarCoordinateSorter
import Elk.Alg.Radial.Intermediate.Compaction.AbstractRadiusExtensionCompaction
import Elk.Alg.Radial.Intermediate.Overlaps.IOverlapRemoval
/-!
# `org.eclipse.elk.alg.radial.intermediate.overlaps.RadiusExtensionOverlapRemoval`

Port of `radius_extension_overlap_removal.rs` (elk-rs): for every level of the tree, expands the
layer away from the root until no neighbouring nodes of the layer overlap, then moves the next
level by the distance the first node of the layer has moved.

Parity notes (Rust is the oracle):
* the object is created with the derived `Default`, so `compaction_step` is `0` (Java: `1`).
  Expanding by `0` leaves the layer where it is (modulo the rounding of `cx + 0 - half_w`), the
  loop runs to its 10000 iteration guard whenever the layer overlaps;
* the successor cache of the whole tree is built once at the start (`get_next_level_cached`
  removes duplicates, keeping the first occurrence).
-/
/-! Float literals as global constants (FL): inside branches, loops and specialised code the compiler
shares a literal's `Nat`/`Bool` arguments with unrelated variables (CSE) and then parses it on every
evaluation (`FastFloat.ofScientificImpl`); a top-level constant is a load (PLAN §7.1 items 17, 22). -/
private def fl0p0 : Float := 0.0
private def fl2p0 : Float := 2.0

namespace Elk.Alg.Radial.Intermediate.Overlaps

open Elk.Graph Elk.Core.Alg Elk.Core.Options Elk.Core.Util Elk.Alg.Radial.Options Elk.Alg.Radial.Sorting
open Elk.Alg.Radial.Intermediate.Compaction

namespace RadiusExtensionOverlapRemoval

/-- The iteration guard of the overlap removal loop. -/
def MAX_ITERATIONS : Nat := 10000

/-- `get_next_level_cached(nodes, cache)`: the cached successors without duplicates. -/
def getNextLevelCached (nodes : Array NodeId) (cache : Std.HashMap NodeId (Array NodeId)) : Array NodeId :=
  Id.run do
    let mut successors : Array NodeId := #[]
    let mut seen : Std.HashSet NodeId := {}
    for node in nodes do
      if let some children := cache.get? node then
        for child in children do
          if !seen.contains child then
            seen := seen.insert child
            successors := successors.push child
    return successors

/-- `extend(graph, nodes, progress_monitor, successor_cache, root_cx, root_cy)`. -/
partial def extend (base : AbstractRadiusExtensionCompaction) (sorter : Option IRadialSorter)
    (graph : NodeId) (nodes : Array NodeId) (monitor : ProgressMonitor)
    (successorCache : Std.HashMap NodeId (Array NodeId)) (rootCx rootCy : Float) : RadialM Unit := do
  if nodes.isEmpty then return
  let g ← getGraph
  let mut xs : FloatArray := ⟨nodes.map fun n => (g.node n).x⟩
  let mut ys : FloatArray := ⟨nodes.map fun n => (g.node n).y⟩
  let ws : FloatArray := ⟨nodes.map fun n => (g.node n).width⟩
  let hs : FloatArray := ⟨nodes.map fun n => (g.node n).height⟩
  let oldX0 := xs.get! 0
  let oldY0 := ys.get! 0
  if ← monitor.isLoggingEnabled then monitor.logGraph "Before removing overlaps"
  let spacing := base.spacing
  let step := Float.ofInt base.compactionStep
  let mut iterations := 0
  while AbstractRadiusExtensionCompaction.overlapLayerSoa xs ys ws hs spacing do
    if iterations >= MAX_ITERATIONS then break
    let (nx, ny, changed) :=
      AbstractRadiusExtensionCompaction.contractLayerSoa rootCx rootCy xs ys ws hs step false
    xs := nx
    ys := ny
    iterations := iterations + 1
    -- A pass that leaves every coordinate bit-identical is a fixed point: the remaining passes
    -- up to the iteration guard would compute exactly the same values (e.g. `step = 0`).
    if !changed then break
  for i in [0:nodes.size] do
    let x := xs.get! i
    let y := ys.get! i
    ElkM.modifyNode nodes[i]! fun n => { n with x := x, y := y }
  if ← monitor.isLoggingEnabled then monitor.logGraph "After removing overlaps"
  let movedX := xs.get! 0 - oldX0
  let movedY := ys.get! 0 - oldY0
  let movedDistance := Float.sqrt (movedX * movedX + movedY * movedY)
  let nextLevelNodes := getNextLevelCached nodes successorCache
  if !nextLevelNodes.isEmpty then
    let g ← getGraph
    let mut cxs : Array Float := nextLevelNodes.map fun n => (g.node n).x
    let mut cys : Array Float := nextLevelNodes.map fun n => (g.node n).y
    let cws : Array Float := nextLevelNodes.map fun n => (g.node n).width
    let chs : Array Float := nextLevelNodes.map fun n => (g.node n).height
    for i in [0:nextLevelNodes.size] do
      let cx := cxs[i]! + cws[i]! / fl2p0
      let cy := cys[i]! + chs[i]! / fl2p0
      let dx := cx - rootCx
      let dy := cy - rootCy
      let length := Float.sqrt (dx * dx + dy * dy)
      let ux := dx / length
      let uy := dy / length
      cxs := cxs.set! i (cxs[i]! + ux * movedDistance)
      cys := cys.set! i (cys[i]! + uy * movedDistance)
    for i in [0:nextLevelNodes.size] do
      let x := cxs[i]!
      let y := cys[i]!
      ElkM.modifyNode nextLevelNodes[i]! fun n => { n with x := x, y := y }
    if ← monitor.isLoggingEnabled then monitor.logGraph "Child movement 1"
  let nextLevelNodes ← match sorter with
    | some sorter => sorter.sort nextLevelNodes
    | none => pure nextLevelNodes
  extend base sorter graph nextLevelNodes monitor successorCache rootCx rootCy

/-- `remove_overlaps(graph, progress_monitor)`. -/
def removeOverlaps (graph : NodeId) (monitor : ProgressMonitor) : RadialM Unit := do
  let some root ← RadialUtil.rootFromGraph graph | return
  let props := (← ElkM.getNode graph).props
  let sorter ← (props.getD RadialOptions.SORTER SortingStrategy.none).create
  let base : AbstractRadiusExtensionCompaction :=
    { spacing := (props.get CoreOptions.SPACING_NODE_NODE).getD fl0p0 }
  let (successorCache, _) ← RadialUtil.buildTreeCaches root
  let r ← ElkM.getNode root
  let rootCx := r.x + r.width / fl2p0
  let rootCy := r.y + r.height / fl2p0
  let successors := (successorCache.get? root).getD #[]
  extend base sorter graph successors monitor successorCache rootCx rootCy

/-- `process(graph, progress_monitor)`. -/
def process (graph : NodeId) (monitor : ProgressMonitor) : RadialM Unit := do
  let _ ← monitor.begin "Remove overlaps" 1.0
  if ← monitor.isLoggingEnabled then monitor.logGraph "Before"
  removeOverlaps graph monitor
  if ← monitor.isLoggingEnabled then monitor.logGraph "After"

/-- The `IOverlapRemoval` of this class. -/
def overlapRemoval : IOverlapRemoval := { removeOverlaps := removeOverlaps }

/-- The processor (`ILayoutProcessor`). -/
def processor : LayoutProcessor RadialM NodeId :=
  { name := "RadiusExtensionOverlapRemoval", process := process }

end RadiusExtensionOverlapRemoval

end Elk.Alg.Radial.Intermediate.Overlaps

namespace Elk.Alg.Radial.Options.OverlapRemovalStrategy

open Elk.Alg.Radial.Intermediate.Overlaps

/-- `OverlapRemovalStrategy::create()`. -/
def create : OverlapRemovalStrategy → IOverlapRemoval
  | .extentRadii => RadiusExtensionOverlapRemoval.overlapRemoval

end Elk.Alg.Radial.Options.OverlapRemovalStrategy
