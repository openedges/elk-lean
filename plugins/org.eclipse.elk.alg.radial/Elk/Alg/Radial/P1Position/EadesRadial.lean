import Std.Data.HashMap
import Elk.Graph
import Elk.Core.Alg
import Elk.Core.Options
import Elk.Core.Util.Java
import Elk.Core.Util.ProgressMonitor
import Elk.Alg.Radial.InternalProperties
import Elk.Alg.Radial.RadialLayoutPhases
import Elk.Alg.Radial.RadialUtil
import Elk.Alg.Radial.Options.AnnulusWedgeCriteria
import Elk.Alg.Radial.Options.RadialOptions
import Elk.Alg.Radial.Options.RadialTranslationStrategy
import Elk.Alg.Radial.Options.SortingStrategy
import Elk.Alg.Radial.P1Position.Wedge
import Elk.Alg.Radial.Sorting.IRadialSorter
import Elk.Alg.Radial.Sorting.PolarCoordinateSorter
import Elk.Alg.Radial.Intermediate.IntermediateProcessorStrategy
import Elk.Alg.Radial.Intermediate.Optimization
/-!
# `org.eclipse.elk.alg.radial.p1position.EadesRadial`

Port of `eades_radial.rs` (elk-rs): phase 1 of the radial layout. Places the root in the middle
and the successors of every node on the next radius, in an annulus wedge proportional to the
number of leaves below them (algorithm of Peter Eades, "Drawing free trees", 1991).

Java semantics (agent OPT; elk-rs, which elk-lean followed before, differs in all three points):
* the wedge of a node is divided by the space the `WEDGE_CRITERIA` assigns to it
  (`AnnulusWedgeByNodeSpace` by default: the maximum of the node diagonal and the sum over its
  successors; `AnnulusWedgeByLeafs`: the number of leaves); elk-rs always uses the leaf count;
* `tau = 2 * Math.acos(currentRadius / currentRadius + radius)` keeps Java's operator precedence,
  `acos((currentRadius / currentRadius) + radius)`, which is `NaN` for a positive radius (and at the
  root), so the `tau` branch is taken only for radius 0 off the root; elk-rs computes
  `acos(currentRadius / (currentRadius + radius))`;
* with a sorter, every node calls `sorter.initialize(root)` and then `sorter.sort(successors)`
  (elk-rs: `sort_for_parent`).
The optimal rotation offset (`OPTIMIZATION_CRITERIA`) is searched over the 360 whole degrees with the
first strictly smaller evaluation winning. The wedge spaces depend only on the tree and the node
sizes, which this phase does not change, so they are computed once per node (`wedgeCache`; the same
sums in the same order as Java's recursion).

This module also hosts the factories `AnnulusWedgeCriteria.create` and
`RadialTranslationStrategy.create` (the factory halves of the Rust option enums).
-/
/-! Float literals as global constants (FL): inside branches, loops and specialised code the compiler
shares a literal's `Nat`/`Bool` arguments with unrelated variables (CSE) and then parses it on every
evaluation (`FastFloat.ofScientificImpl`); a top-level constant is a load (PLAN §7.1 items 17, 22). -/
private def fl0p0 : Float := 0.0
private def fl1p0 : Float := 1.0
private def fl2p0 : Float := 2.0

namespace Elk.Alg.Radial.P1Position

open Elk.Graph Elk.Core.Alg Elk.Core.Util Elk.Alg.Radial.Options Elk.Alg.Radial.Sorting
open Elk.Alg.Radial.P1Position.Wedge Elk.Alg.Radial.Intermediate Elk.Alg.Radial.Intermediate.Optimization

/-- `CIRCLE_DEGREES`. -/
def CIRCLE_DEGREES : Nat := 360
/-- `DEGREE_TO_RAD`. -/
def DEGREE_TO_RAD : Float := Float.pi / 180.0

/-- `AnnulusWedgeCriteria::create()`. -/
def createAnnulusWedgeCriteria : AnnulusWedgeCriteria → IAnnulusWedgeCriteria
  | .leafNumber => AnnulusWedgeByLeafs.criteria
  | .nodeSize => AnnulusWedgeByNodeSpace.criteria

/-- `RadialTranslationStrategy::create()`: `none` has no evaluation. -/
def createEvaluation : RadialTranslationStrategy → Option IEvaluation
  | .none => Option.none
  | .edgeLength => some EdgeLengthOptimization.evaluation
  | .edgeLengthByPosition => some EdgeLengthPositionOptimization.evaluation
  | .crossingMinimizationByPosition => some CrossingMinimizationPosition.evaluation

namespace EadesRadial

/-- `IAnnulusWedgeCriteria.calculateWedgeSpace` of every node below `node` (Java recursion order:
`AnnulusWedgeByNodeSpace` sums the successors left to right and takes the maximum with
`sqrt(height * height + width * width)`; `AnnulusWedgeByLeafs` is the leaf count). -/
partial def wedgeSpaces (g : ElkGraph) (criteria : AnnulusWedgeCriteria)
    (successorCache : Std.HashMap NodeId (Array NodeId)) (leafCache : Std.HashMap NodeId Float)
    (node : NodeId) (cache : Std.HashMap NodeId Float) : Float × Std.HashMap NodeId Float :=
  match cache.get? node with
  | some v => (v, cache)
  | none =>
    match criteria with
    | .leafNumber =>
      let v := (leafCache.get? node).getD (RadialUtil.numberOfLeavesPure g node)
      (v, cache.insert node v)
    | .nodeSize =>
      let successors := (successorCache.get? node).getD (RadialUtil.successorsPure g node)
      let n := g.node node
      let nodeSize := Float.sqrt (n.height * n.height + n.width * n.width)
      let (childSpace, cache) := successors.foldl (fun (acc, c) child =>
        let (v, c) := wedgeSpaces g criteria successorCache leafCache child c
        (acc + v, c)) (fl0p0, cache)
      let v := javaMax childSpace nodeSize
      (v, cache.insert node v)

/-- `positionNodes(node, currentRadius, minAlpha, maxAlpha, optimalOffset)`: places `node` on the
circle of `currentRadius` at the middle of its wedge `[minAlpha, maxAlpha]` (rotated by
`optimalOffset`) and recurses into its (sorted) successors. -/
partial def positionNodes (node root : NodeId) (radius : Float) (sorter : Option IRadialSorter)
    (successorCache : Std.HashMap NodeId (Array NodeId)) (wedgeCache : Std.HashMap NodeId Float)
    (currentRadius minAlpha maxAlpha optimalOffset : Float) : RadialM Unit := do
  let alphaPoint := (minAlpha + maxAlpha) / fl2p0 + optimalOffset
  let xPos := currentRadius * javaCos alphaPoint
  let yPos := currentRadius * javaSin alphaPoint
  RadialUtil.centerNodesOnRadi node xPos yPos
  let numberOfLeafs := (wedgeCache.get? node).getD fl1p0
  -- Java `2 * Math.acos(currentRadius / currentRadius + radius)` (operator precedence kept)
  let tau := fl2p0 * javaAcos (currentRadius / currentRadius + radius)
  let (s, alpha0) :=
    if tau < maxAlpha - minAlpha then (tau / numberOfLeafs, (minAlpha + maxAlpha - tau) / fl2p0)
    else ((maxAlpha - minAlpha) / numberOfLeafs, minAlpha)
  let mut alpha := alpha0
  let mut successors ← match successorCache.get? node with
    | some cached => pure cached
    | none => RadialUtil.getSuccessors node
  if let some sorter := sorter then
    sorter.init root
    successors ← sorter.sort successors
  for child in successors do
    let numberOfChildLeafs := (wedgeCache.get? child).getD fl1p0
    positionNodes child root radius sorter successorCache wedgeCache (currentRadius + radius) alpha
      (alpha + s * numberOfChildLeafs) optimalOffset
    alpha := alpha + s * numberOfChildLeafs

/-- `translate(graph)`. -/
def translate (root : NodeId) (radius : Float) (sorter : Option IRadialSorter)
    (criteria : AnnulusWedgeCriteria) (optimizer : Option IEvaluation) : RadialM Unit := do
  let (successorCache, leafCache) ← RadialUtil.buildTreeCaches root
  -- `AnnulusWedgeByLeafs` is the leaf count of the tree caches; `AnnulusWedgeByNodeSpace` is filled
  -- for the whole tree below the root
  let wedgeCache ← match criteria with
    | .leafNumber => pure leafCache
    | .nodeSize => ElkM.withGraph fun g => (wedgeSpaces g criteria successorCache leafCache root {}).2
  let mut optimalOffset := fl0p0
  let mut optimalValue := Float.maxValue
  if let some optimizer := optimizer then
    for i in [0:CIRCLE_DEGREES] do
      let offset := i.toFloat * DEGREE_TO_RAD
      positionNodes root root radius sorter successorCache wedgeCache fl0p0 fl0p0 (fl2p0 * Float.pi) offset
      let translatedValue ← optimizer.evaluate root
      if translatedValue < optimalValue then
        optimalOffset := offset
        optimalValue := translatedValue
  positionNodes root root radius sorter successorCache wedgeCache fl0p0 fl0p0 (fl2p0 * Float.pi) optimalOffset

/-- `process(graph, progress_monitor)`. -/
def process (graph : NodeId) (monitor : ProgressMonitor) : RadialM Unit := do
  let _ ← monitor.begin "Eades radial" 1.0
  if ← monitor.isLoggingEnabled then monitor.logGraph "After"
  let some root ← RadialUtil.rootFromGraph graph | return
  let props := (← ElkM.getNode graph).props
  let radius := (props.get RadialOptions.RADIUS).getD 0.0
  let sorter ← (props.getD RadialOptions.SORTER SortingStrategy.none).create
  let criteria := props.getD RadialOptions.WEDGE_CRITERIA AnnulusWedgeCriteria.nodeSize
  let optimizer := createEvaluation (props.getD RadialOptions.OPTIMIZATION_CRITERIA RadialTranslationStrategy.none)
  translate root radius sorter criteria optimizer
  if ← monitor.isLoggingEnabled then monitor.logGraph "After"
  monitor.done

/-- The phase (`ILayoutPhase`) with no processor configuration. -/
def phase : LayoutPhase RadialM RadialLayoutPhases NodeId IntermediateProcessorStrategy :=
  { name := "EadesRadial"
    process := process
    getLayoutProcessorConfiguration := fun _ => pure none }

end EadesRadial

end Elk.Alg.Radial.P1Position
