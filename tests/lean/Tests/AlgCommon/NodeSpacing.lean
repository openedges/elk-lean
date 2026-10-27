import Tests.AlgCommon.NodeSpacing.CellSystem
import Tests.AlgCommon.NodeSpacing.AlgorithmCells
import Tests.AlgCommon.NodeSpacing.AlgorithmPorts
import Tests.AlgCommon.NodeSpacing.Calculators
import Tests.AlgCommon.NodeSpacing.All
/-! Tests of `org.eclipse.elk.alg.common.nodespacing`: one file per porting task. -/
namespace Tests.AlgCommon.NodeSpacing

def suites : Array Tests.Suite :=
  CellSystem.suites ++ AlgorithmCells.suites ++ AlgorithmPorts.suites ++ Calculators.suites ++ All.suites

end Tests.AlgCommon.NodeSpacing
