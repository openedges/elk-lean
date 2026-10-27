import Elk.Alg.RectPacking.Options
import Elk.Alg.RectPacking.Util
import Elk.Alg.RectPacking.Intermediate
import Elk.Alg.RectPacking.RectPackingLayoutPhases
import Elk.Alg.RectPacking.P1WidthApproximation
import Elk.Alg.RectPacking.P2Packing.PackingStrategy
import Elk.Alg.RectPacking.P3WhitespaceElimination.WhiteSpaceEliminationStrategy
import Elk.Alg.RectPacking.Init
/-! Root module of the `org.eclipse.elk.alg.rectpacking` plugin (rectangle packing). The packing
and whitespace elimination phases and the layout provider are added by the follow-up port (F8b). -/
