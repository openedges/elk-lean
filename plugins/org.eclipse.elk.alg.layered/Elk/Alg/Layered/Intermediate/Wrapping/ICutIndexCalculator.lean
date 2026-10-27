import Elk.Alg.Layered.Intermediate.Wrapping.GraphStats
/-!
# `org.eclipse.elk.alg.layered.intermediate.wrapping.ICutIndexCalculator`

The strategy interface (elk-rs private trait `CutIndexCalculator`, duplicated in
`breaking_point_inserter.rs` and `single_edge_graph_wrapper.rs`) as a structure of closures, plus
the inner class `ManualCutIndexCalculator`.
-/
namespace Elk.Alg.Layered.Intermediate.Wrapping

open Elk.Graph Elk.Alg.Layered.Graph Elk.Alg.Layered.Options LayeredM

/-- `ICutIndexCalculator`: calculates the indexes at which a layering is cut into chunks. -/
structure ICutIndexCalculator where
  /-- `getCutIndexes(graph, graphStats)`: the indexes *before* which the layering is split. -/
  getCutIndexes : LGraphId → GraphStats → LayeredM (Array Int)
  /-- `guaranteeValid()`: whether all returned cuts are guaranteed to be valid. -/
  guaranteeValid : Bool

namespace ICutIndexCalculator

/-- `ICutIndexCalculator.ManualCutIndexCalculator`: the cuts of `WRAPPING_CUTTING_CUTS` (empty when
unset); not guaranteed to be valid. -/
def manual : ICutIndexCalculator where
  getCutIndexes graph _ := do
    return ((← getGraph graph).props.get LayeredOptions.WRAPPING_CUTTING_CUTS).getD #[]
  guaranteeValid := false

end ICutIndexCalculator

end Elk.Alg.Layered.Intermediate.Wrapping
