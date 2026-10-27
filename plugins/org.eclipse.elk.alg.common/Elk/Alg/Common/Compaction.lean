import Elk.Alg.Common.Compaction.Scanline
import Elk.Alg.Common.Compaction.Options.TraversalStrategy
import Elk.Alg.Common.Compaction.Options.HighLevelSortingCriterion
import Elk.Alg.Common.Compaction.Options.LowLevelSortingCriterion
import Elk.Alg.Common.Compaction.Options.PolyominoOptions
import Elk.Alg.Common.Compaction.OneD.CNode
import Elk.Alg.Common.Compaction.OneD.CGroup
import Elk.Alg.Common.Compaction.OneD.CGraph
import Elk.Alg.Common.Compaction.OneD.CompareFuzzy
import Elk.Alg.Common.Compaction.OneD.ISpacingsHandler
import Elk.Alg.Common.Compaction.OneD.ILockFunction
import Elk.Alg.Common.Compaction.OneD.ICompactionAlgorithm
import Elk.Alg.Common.Compaction.OneD.IConstraintCalculationAlgorithm
import Elk.Alg.Common.Compaction.OneD.LongestPathCompaction
import Elk.Alg.Common.Compaction.OneD.QuadraticConstraintCalculation
import Elk.Alg.Common.Compaction.OneD.ScanlineConstraintCalculator
import Elk.Alg.Common.Compaction.OneD.OneDimensionalCompactor
/-! Aggregator of `org.eclipse.elk.alg.common.compaction`. Owned by the Compaction porting task; add submodule imports here. -/
