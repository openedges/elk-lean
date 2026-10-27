import Elk.Alg.Common.NodeSpacing.CellSystem
import Elk.Alg.Common.NodeSpacing.Internal
import Elk.Alg.Common.NodeSpacing.Internal.AlgorithmCells
import Elk.Alg.Common.NodeSpacing.Internal.AlgorithmPorts
import Elk.Alg.Common.NodeSpacing.Calculators
import Elk.Alg.Common.NodeSpacing.NodeDimensionCalculation
import Elk.Alg.Common.NodeSpacing.NodeMicroLayout
/-! Aggregator of `org.eclipse.elk.alg.common.nodespacing`. Sub-aggregators are owned by the N1 (cell system,
contexts), N2a (cell/label/node-size algorithms), N2b (port placement algorithms) and N3 (calculators) tasks. -/
