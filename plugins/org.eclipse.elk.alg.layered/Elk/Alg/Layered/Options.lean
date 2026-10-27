import Elk.Alg.Layered.Options.CenterEdgeLabelPlacementStrategy
import Elk.Alg.Layered.Options.ConstraintCalculationStrategy
import Elk.Alg.Layered.Options.CrossingMinimizationStrategy
import Elk.Alg.Layered.Options.CuttingStrategy
import Elk.Alg.Layered.Options.CycleBreakingStrategy
import Elk.Alg.Layered.Options.DirectionCongruency
import Elk.Alg.Layered.Options.EdgeConstraint
import Elk.Alg.Layered.Options.EdgeLabelSideSelection
import Elk.Alg.Layered.Options.EdgeStraighteningStrategy
import Elk.Alg.Layered.Options.FixedAlignment
import Elk.Alg.Layered.Options.GraphCompactionStrategy
import Elk.Alg.Layered.Options.GraphProperties
import Elk.Alg.Layered.Options.GreedySwitchType
import Elk.Alg.Layered.Options.GroupOrderStrategy
import Elk.Alg.Layered.Options.InLayerConstraint
import Elk.Alg.Layered.Options.InteractiveReferencePoint
import Elk.Alg.Layered.Options.LayerConstraint
import Elk.Alg.Layered.Options.LayerUnzippingStrategy
import Elk.Alg.Layered.Options.LayeringStrategy
import Elk.Alg.Layered.Options.LongEdgeOrderingStrategy
import Elk.Alg.Layered.Options.NodeFlexibility
import Elk.Alg.Layered.Options.NodePlacementStrategy
import Elk.Alg.Layered.Options.NodePromotionStrategy
import Elk.Alg.Layered.Options.OrderingStrategy
import Elk.Alg.Layered.Options.PortSortingStrategy
import Elk.Alg.Layered.Options.PortType
import Elk.Alg.Layered.Options.SelfLoopDistributionStrategy
import Elk.Alg.Layered.Options.SelfLoopOrderingStrategy
import Elk.Alg.Layered.Options.SelfLoopPlacementStrategy
import Elk.Alg.Layered.Options.SplineRoutingMode
import Elk.Alg.Layered.Options.ValidifyStrategy
import Elk.Alg.Layered.Options.WrappingStrategy
import Elk.Alg.Layered.Options.LayeredOptions
import Elk.Alg.Layered.Options.LayeredMetaDataProvider
import Elk.Alg.Layered.Options.LayeredSpacings
/-!
# `org.eclipse.elk.alg.layered.options`

Aggregator of the layered option package: the option enumerations, `LayeredOptions` (property
constants), `LayeredMetaDataProvider` (option and algorithm metadata) and `LayeredSpacings`
(spacing configuration relative to a base value). `InternalProperties` and `Spacings` are
added by the main agent.
-/
