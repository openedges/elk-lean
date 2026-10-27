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

Follows the Rust port: the leaf counts come from the tree caches, the sorter is asked with
`sort_for_parent`, and the optimal rotation offset (`OPTIMIZATION_CRITERIA`) is searched over the
360 whole degrees with the first strictly smaller evaluation winning. The wedge criteria object
is created but unused by `translate`, as in Rust. The Rust `RadialSoA` (node sizes extracted
once) is a performance device; sizes do not change in this phase, so the live sizes are used.

This module also hosts the factories `AnnulusWedgeCriteria.create` and
`RadialTranslationStrategy.create` (the factory halves of the Rust option enums).
-/
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

/-- `f64::clamp(-1.0, 1.0)`. -/
private def clampUnit (x : Float) : Float :=
  if x < -1.0 then -1.0 else if x > 1.0 then 1.0 else x

/-- `position_nodes_soa(...)`: places `node` on the circle of `currentRadius` at the middle of
its wedge `[minAlpha, maxAlpha]` (rotated by `optimalOffset`) and recurses into its (sorted)
successors. -/
partial def positionNodes (node root : NodeId) (radius : Float) (sorter : Option IRadialSorter)
    (successorCache : Std.HashMap NodeId (Array NodeId)) (leafCache : Std.HashMap NodeId Float)
    (currentRadius minAlpha maxAlpha optimalOffset : Float) : RadialM Unit := do
  let alphaPoint := (minAlpha + maxAlpha) / 2.0 + optimalOffset
  let xPos := currentRadius * Float.cos alphaPoint
  let yPos := currentRadius * Float.sin alphaPoint
  RadialUtil.centerNodesOnRadi node xPos yPos
  let numberOfLeafs := (leafCache.get? node).getD 1.0
  let ratio :=
    if (currentRadius + radius).abs < Float.epsilon then 1.0
    else clampUnit (currentRadius / (currentRadius + radius))
  let tau := 2.0 * Float.acos ratio
  let (s, alpha0) :=
    if tau < maxAlpha - minAlpha then (tau / numberOfLeafs, (minAlpha + maxAlpha - tau) / 2.0)
    else ((maxAlpha - minAlpha) / numberOfLeafs, minAlpha)
  let mut alpha := alpha0
  let mut successors ← match successorCache.get? node with
    | some cached => pure cached
    | none => RadialUtil.getSuccessors node
  if let some sorter := sorter then
    successors ← sorter.sortForParent successors node root (currentRadius == 0.0)
  for child in successors do
    let numberOfChildLeafs := (leafCache.get? child).getD 1.0
    positionNodes child root radius sorter successorCache leafCache (currentRadius + radius) alpha
      (alpha + s * numberOfChildLeafs) optimalOffset
    alpha := alpha + s * numberOfChildLeafs

/-- `translate(root, radius, sorter, annulus, optimizer)`. -/
def translate (root : NodeId) (radius : Float) (sorter : Option IRadialSorter)
    (optimizer : Option IEvaluation) : RadialM Unit := do
  let (successorCache, leafCache) ← RadialUtil.buildTreeCaches root
  let mut optimalOffset := 0.0
  let mut optimalValue := Float.maxValue
  if let some optimizer := optimizer then
    for i in [0:CIRCLE_DEGREES] do
      let offset := i.toFloat * DEGREE_TO_RAD
      positionNodes root root radius sorter successorCache leafCache 0.0 0.0 (2.0 * Float.pi) offset
      let translatedValue ← optimizer.evaluate root
      if translatedValue < optimalValue then
        optimalOffset := offset
        optimalValue := translatedValue
  positionNodes root root radius sorter successorCache leafCache 0.0 0.0 (2.0 * Float.pi) optimalOffset

/-- `process(graph, progress_monitor)`. -/
def process (graph : NodeId) (monitor : ProgressMonitor) : RadialM Unit := do
  let _ ← monitor.begin "Eades radial" 1.0
  if ← monitor.isLoggingEnabled then monitor.logGraph "After"
  let some root ← RadialUtil.rootFromGraph graph | return
  let props := (← ElkM.getNode graph).props
  let radius := (props.get RadialOptions.RADIUS).getD 0.0
  let sorter ← (props.getD RadialOptions.SORTER SortingStrategy.none).create
  let _annulus := createAnnulusWedgeCriteria (props.getD RadialOptions.WEDGE_CRITERIA AnnulusWedgeCriteria.nodeSize)
  let optimizer := createEvaluation (props.getD RadialOptions.OPTIMIZATION_CRITERIA RadialTranslationStrategy.none)
  translate root radius sorter optimizer
  if ← monitor.isLoggingEnabled then monitor.logGraph "After"
  monitor.done

/-- The phase (`ILayoutPhase`) with no processor configuration. -/
def phase : LayoutPhase RadialM RadialLayoutPhases NodeId IntermediateProcessorStrategy :=
  { name := "EadesRadial"
    process := process
    getLayoutProcessorConfiguration := fun _ => pure none }

end EadesRadial

end Elk.Alg.Radial.P1Position
