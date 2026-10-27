import Elk.Graph.Enum
/-!
# `org.eclipse.elk.alg.radial.options.SortingStrategy`

Port of `sorting_strategy.rs` (elk-rs). The factory half of the Rust enum (`create`, which builds
the optional `IRadialSorter`) lives in `Elk.Alg.Radial.Sorting.PolarCoordinateSorter`, the last
module of the sorting package, because the sorters depend on the options.
-/
namespace Elk.Alg.Radial.Options

/-- `SortingStrategy`: how the nodes of one radius are ordered. -/
elk_enum SortingStrategy := none polarCoordinate id

end Elk.Alg.Radial.Options
