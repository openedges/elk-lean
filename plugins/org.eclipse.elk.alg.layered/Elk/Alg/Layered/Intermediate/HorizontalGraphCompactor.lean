import Elk.Alg.Common.Compaction.OneD.OneDimensionalCompactor
import Elk.Alg.Layered.LayeredPhases
import Elk.Alg.Layered.Options.LayeredOptions
import Elk.Alg.Layered.Intermediate.Compaction
import Elk.Alg.Layered.P5Edges.Splines.SplineEdgeRouter
import Elk.Core.Util.FloatConst
open Elk.Core.Util.FloatConst
/-!
# `org.eclipse.elk.alg.layered.intermediate.compaction.HorizontalGraphCompactor`

This processor applies additional compaction to an already routed graph (elk-rs
`intermediate/horizontal_graph_compactor.rs`; Java class in the `intermediate.compaction`
package, placed in `intermediate` like elk-rs). Nodes and vertical segments of edges are
repositioned in the specified direction where the position is minimal considering the desired
spacing between elements. Since the locking relies on the direction of incoming and outgoing
edges, the processor runs before `ReversedEdgeRestorer` (slot: after phase 5, before
`LabelDummyRemover`).

Steps (Rust `process`): nothing happens for strategy `NONE` or routing styles other than
`ORTHOGONAL`/`SPLINES` (Java throws `IllegalStateException` for those; Rust returns); the graph
is transformed into a `CGraph` (`LGraphToCGraphTransformer`), compacted with the
`OneDimensionalCompactor` (`compact`, Rust `CompactionContext::compact`) and the result is
applied back (`CompactionContext.applyLayout`).

The compactor runs in `IO` on its own state (as in `OneDimensionalComponentsCompaction`); the
strategies only read snapshots of the layered graph (`CompactionMetadata`,
`SpecialSpacingsHandler`, `NetworkSimplexCompaction.outgoingEdges`). The only arena change Rust
makes during compaction (the port moves of `NetworkSimplexCompaction`) is replayed right after
the compactor finished.

Spline routes are read from the graph's spline segment table (`splineRouteAccess`: the
`SPLINE_ROUTE_START` ids of `LEdgeInternals.splineRouteStart` index
`LGraphInternals.splineSegments`; moved bounding boxes are written back there).
-/

namespace Elk.Alg.Layered.Intermediate

open Elk.Graph Elk.Core Elk.Core.Util Elk.Core.Options Elk.Alg.Common.Compaction.OneD
open Elk.Alg.Layered Elk.Alg.Layered.Graph Elk.Alg.Layered.Options Elk.Alg.Layered.Intermediate.Compaction
open LayeredM

namespace HorizontalGraphCompactor

/-- The lock function of `LEFT_RIGHT_CONSTRAINT_LOCKING`: nodes whose group is not constrained
(`outDegreeReal == 0`) are locked. -/
def constraintLockFunction : LockFunction := .fn fun g n _ =>
  match (g.cNode n).cGroup with
  | some group => (g.cGroup group).outDegreeReal == 0
  | none => false

/-- The lock function of `LEFT_RIGHT_CONNECTION_LOCKING`: the connection locks of the
transformer (`LEFT`/`RIGHT` only). -/
def connectionLockFunction (locks : Array DirectionLocks) : LockFunction := .fn fun _ n dir =>
  match locks[n.idx]? with
  | some l =>
    match dir with
    | .left => l.left
    | .right => l.right
    | _ => false
  | none => false

/-- Rust `CompactionContext::compact(graph, strategy, constraint_strategy, spacings)`: runs the
`OneDimensionalCompactor` on the context's `CGraph` with the special spacings handler, the
selected constraint calculation and compaction strategy; returns the context holding the
compacted graph (in `LEFT` orientation). -/
def compact (ctx : CompactionContext) (graph : LGraphId) (strategy : GraphCompactionStrategy)
    (constraintStrategy : ConstraintCalculationStrategy) (spacings : Option Spacings) :
    LayeredM CompactionContext := do
  let cGraph := ctx.cGraph
  let ctx := { ctx with cGraph := {} }
  let mut compactor := OneDimensionalCompactor.new cGraph
  let metadata ← CompactionMetadata.fromContext ctx.cnodeOrigin ctx.segments graph
  let verticalEdgeEdgeSpacing := ((← getGraph graph).props.get LayeredOptions.SPACING_EDGE_EDGE).getD 0.0
  let spacingHandler ← SpecialSpacingsHandler.new ctx.cnodeOrigin ctx.segments spacings
  compactor := compactor.setSpacingsHandler spacingHandler.toSpacingsHandler
  match constraintStrategy with
  | .quadratic =>
    compactor := compactor.setConstraintAlgorithm QuadraticConstraintCalculation
  | .scanline =>
    let calculation : EdgeAwareScanlineConstraintCalculation :=
      { edgeRouting := ctx.edgeRouting, verticalEdgeEdgeSpacing, metadata }
    compactor := compactor.setConstraintAlgorithm calculation.toAlgorithm
  let mut networkSimplex : Option NetworkSimplexCompaction := none
  match strategy with
  | .none => pure ()
  | .left =>
    compactor ← compactor.compact
  | .right =>
    compactor ← compactor.changeDirection .right
    compactor ← compactor.compact
  | .leftRightConstraintLocking =>
    compactor ← compactor.compact
    compactor ← compactor.changeDirection .right
    compactor := compactor.setLockFunction (some constraintLockFunction)
    compactor ← compactor.compact
  | .leftRightConnectionLocking =>
    compactor ← compactor.compact
    compactor ← compactor.changeDirection .right
    compactor := compactor.setLockFunction (some (connectionLockFunction ctx.connectionLocks))
    compactor ← compactor.compact
  | .edgeLength =>
    let ns ← NetworkSimplexCompaction.new metadata
    compactor := compactor.setCompactionAlgorithm ns.toAlgorithm
    compactor ← compactor.compact
    networkSimplex := some ns
  compactor ← compactor.finish
  if let some ns := networkSimplex then
    ns.applyPortAdjustments
  return { ctx with cGraph := compactor.cGraph }

/-- `process(layeredGraph, progressMonitor)` with the given access to the spline routes. -/
def process (splines : SplineRouteAccess) (graph : LGraphId) (monitor : ProgressMonitor) : LayeredM Unit := do
  let props := (← getGraph graph).props
  let strategy := (props.get LayeredOptions.COMPACTION_POST_COMPACTION_STRATEGY).getD .none
  if strategy == .none then return
  let edgeRouting := (props.get LayeredOptions.EDGE_ROUTING).getD .undefined
  if edgeRouting != .orthogonal && edgeRouting != .splines then return
  let _ ← monitor.begin "Horizontal Compaction" fl1p0
  let spacings := (← getGraph graph).internal.spacings
  let constraintStrategy := (props.get LayeredOptions.COMPACTION_POST_COMPACTION_CONSTRAINTS).getD .scanline
  let ctx ← CompactionContext.transform graph edgeRouting splines
  let ctx ← compact ctx graph strategy constraintStrategy spacings
  ctx.applyLayout graph
  monitor.done

/-- The processor with the given access to the spline routes. -/
def processorWith (splines : SplineRouteAccess) : LayeredProcessor :=
  { name := "HorizontalGraphCompactor", process := process splines }

/-- The spline routes of `graph` (Rust: `SPLINE_ROUTE_START` on the edges, `SplineSegmentRef`s
locked for reading and for moving their bounding boxes): the handles are the
`SplineSegmentId.idx` of the graph's segment table. -/
def splineRouteAccess (graph : LGraphId) : SplineRouteAccess :=
  { routeStart := fun edge => do
      return (← getEdge edge).internal.splineRouteStart.map (·.map (·.idx))
    segment := fun handle => do
      let s ← P5Edges.Splines.getSplineSegment graph ⟨handle⟩
      return { edges := s.edges, isStraight := s.isStraight, boundingBox := s.boundingBox,
               initialSegment := s.initialSegment, lastSegment := s.lastSegment,
               sourceNode := s.sourceNode, targetNode := s.targetNode }
    modifyBoundingBox := fun handle f =>
      P5Edges.Splines.modifySplineSegment graph ⟨handle⟩ fun s => { s with boundingBox := f s.boundingBox } }

/-- `new HorizontalGraphCompactor()`: the spline routes of the processed graph
(`splineRouteAccess`). -/
def processor : LayeredProcessor :=
  { name := "HorizontalGraphCompactor", process := fun graph monitor => process (splineRouteAccess graph) graph monitor }

end HorizontalGraphCompactor

builtin_initialize registerHorizontalGraphCompactor : Unit ←
  IntermediateProcessorStrategy.register .horizontalCompactor HorizontalGraphCompactor.processor

end Elk.Alg.Layered.Intermediate
