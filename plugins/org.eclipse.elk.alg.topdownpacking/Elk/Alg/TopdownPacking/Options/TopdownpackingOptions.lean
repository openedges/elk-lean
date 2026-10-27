import Elk.Core.Options
import Elk.Alg.TopdownPacking.NodeArrangementStrategy
import Elk.Alg.TopdownPacking.WhitespaceEliminationStrategy
/-!
# `org.eclipse.elk.alg.topdownpacking.options.TopdownpackingOptions`

Port of `topdownpacking_options.rs` (elk-rs): the option constants of the topdown packing
algorithm. The core options it re-exports are aliases of the `CoreOptions` constants.
-/
namespace Elk.Alg.TopdownPacking.Options

open Elk Elk.Graph Elk.Core.Math Elk.Core.Options

namespace TopdownpackingOptions

/-- `TopdownpackingOptions.ALGORITHM_ID`. -/
def ALGORITHM_ID : String := "org.eclipse.elk.topdownpacking"

/-- `TopdownpackingOptions.NODE_ARRANGEMENT_STRATEGY`. -/
def NODE_ARRANGEMENT_STRATEGY : Property NodeArrangementStrategy :=
  Property.withDefault "org.eclipse.elk.topdownpacking.nodeArrangement.strategy"
    NodeArrangementStrategy.leftRightTopDownNodePlacer

/-- `TopdownpackingOptions.WHITESPACE_ELIMINATION_STRATEGY`. -/
def WHITESPACE_ELIMINATION_STRATEGY : Property WhitespaceEliminationStrategy :=
  Property.withDefault "org.eclipse.elk.topdownpacking.whitespaceElimination.strategy"
    WhitespaceEliminationStrategy.bottomRowEqualWhitespaceEliminator

/-- `TopdownpackingOptions.PADDING`. -/
def PADDING : Property ElkPadding := CoreOptions.PADDING
/-- `TopdownpackingOptions.SPACING_NODE_NODE`. -/
def SPACING_NODE_NODE : Property Float := CoreOptions.SPACING_NODE_NODE
/-- `TopdownpackingOptions.TOPDOWN_HIERARCHICAL_NODE_WIDTH`. -/
def TOPDOWN_HIERARCHICAL_NODE_WIDTH : Property Float := CoreOptions.TOPDOWN_HIERARCHICAL_NODE_WIDTH
/-- `TopdownpackingOptions.TOPDOWN_HIERARCHICAL_NODE_ASPECT_RATIO`. -/
def TOPDOWN_HIERARCHICAL_NODE_ASPECT_RATIO : Property Float :=
  CoreOptions.TOPDOWN_HIERARCHICAL_NODE_ASPECT_RATIO
/-- `TopdownpackingOptions.TOPDOWN_LAYOUT`. -/
def TOPDOWN_LAYOUT : Property Bool := CoreOptions.TOPDOWN_LAYOUT
/-- `TopdownpackingOptions.TOPDOWN_NODE_TYPE`. -/
def TOPDOWN_NODE_TYPE : Property TopdownNodeTypes := CoreOptions.TOPDOWN_NODE_TYPE

end TopdownpackingOptions

end Elk.Alg.TopdownPacking.Options
