import Elk.Alg.Layered.Intermediate.HierarchicalPortConstraintProcessor
import Elk.Alg.Layered.Intermediate.HierarchicalPortDummySizeProcessor
import Elk.Alg.Layered.Intermediate.HierarchicalPortPositionProcessor
import Elk.Alg.Layered.Intermediate.HierarchicalNodeResizingProcessor
import Elk.Alg.Layered.Intermediate.InteractiveExternalPortPositioner
import Elk.Alg.Layered.Intermediate.HierarchicalPortOrthogonalEdgeRouter
/-!
# Hierarchical (external) port processors

Aggregator of the intermediate processors that handle external port dummies and the resizing of
nested graphs (task I3a): `HierarchicalPortConstraintProcessor`, `HierarchicalPortDummySizeProcessor`,
`HierarchicalPortPositionProcessor`, `HierarchicalNodeResizingProcessor` and
`InteractiveExternalPortPositioner`. Each module registers its processor with
`IntermediateProcessorStrategy.register` at initialisation.
-/
