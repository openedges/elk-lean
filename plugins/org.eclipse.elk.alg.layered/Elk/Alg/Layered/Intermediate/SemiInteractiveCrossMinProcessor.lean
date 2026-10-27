import Elk.Alg.Layered.LayeredPhases
import Elk.Alg.Layered.Options.LayeredOptions
import Elk.Core.Util.Sort
/-!
# `org.eclipse.elk.alg.layered.intermediate.SemiInteractiveCrossMinProcessor`

Port of elk-rs `intermediate/semi_interactive_cross_min_processor.rs` (Java
`SemiInteractiveCrossMinProcessor.java`). In every layer the `NORMAL` nodes that store a
`POSITION` are sorted by ascending `POSITION.y` (stable, `partial_cmp().unwrap_or(Equal)`), and
each of them gets the next one appended to its `IN_LAYER_SUCCESSOR_CONSTRAINTS`. When at least one
constraint was added, the graph gets `IN_LAYER_SUCCESSOR_CONSTRAINTS_BETWEEN_NON_DUMMIES := true`.

Difference to Java, following Rust: Java sets the graph flag as soon as a layer contains one
positioned node (`reduce(...).isPresent()`); Rust (and this port) only when a constraint pair was
added. Java compares with `Double.compare`, Rust with `partial_cmp` (`Float.comparePartial`).
-/
namespace Elk.Alg.Layered.Intermediate

open Elk.Graph Elk.Core Elk.Core.Alg Elk.Core.Math Elk.Core.Util Elk.Alg.Layered
  Elk.Alg.Layered.Graph Elk.Alg.Layered.Options LayeredM

namespace SemiInteractiveCrossMinProcessor

/-- The `NORMAL` nodes of a layer with a stored `POSITION`, as `(POSITION.y, node)` in layer order. -/
def positionedNodes (layer : LayerId) : LayeredM (Array (Float × LNodeId)) := do
  let mut ordered : Array (Float × LNodeId) := #[]
  for n in (← getLayer layer).nodes do
    let nd ← getNode n
    if nd.type != .normal then continue
    if !nd.props.has LayeredOptions.POSITION then continue
    if let some position := nd.props.get LayeredOptions.POSITION then
      ordered := ordered.push (position.y, n)
  return ordered

/-- `SemiInteractiveCrossMinProcessor.process(graph, monitor)`. -/
def process (graph : LGraphId) (monitor : ProgressMonitor) : LayeredM Unit := do
  let _ ← monitor.begin "Semi-Interactive Crossing Minimization Processor" 1.0
  let mut addedConstraints := false
  for layer in (← getGraph graph).layers do
    let ordered := stableSort (← positionedNodes layer) fun a b => Float.comparePartial a.1 b.1
    for i in [1:ordered.size] do
      let prev := ordered[i - 1]!.2
      let cur := ordered[i]!.2
      modifyNode prev fun x => { x with internal := { x.internal with
        inLayerSuccessorConstraints := x.internal.inLayerSuccessorConstraints.push cur } }
      addedConstraints := true
  if addedConstraints then
    modifyGraph graph fun g => { g with internal := { g.internal with
      inLayerSuccessorConstraintsBetweenNonDummies := true } }
  monitor.done

/-- `SemiInteractiveCrossMinProcessor` as a layered processor. -/
def processor : LayeredProcessor :=
  { name := "SemiInteractiveCrossMinProcessor", process := process }

end SemiInteractiveCrossMinProcessor

builtin_initialize registerSemiInteractiveCrossMinProcessor : Unit ←
  IntermediateProcessorStrategy.register .semiInteractiveCrossminProcessor SemiInteractiveCrossMinProcessor.processor

end Elk.Alg.Layered.Intermediate
