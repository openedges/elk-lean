import Elk.Alg.Layered.Components.ComponentOrderingStrategy
import Elk.Alg.Layered.Components.ComponentGroup
import Elk.Alg.Layered.Components.ModelOrderComponentGroup
import Elk.Alg.Layered.Components.AbstractGraphPlacer
import Elk.Alg.Layered.Components.Compaction.OneDimensionalComponentsCompaction
import Elk.Alg.Layered.Components.Compaction.ComponentsCompactor
import Elk.Alg.Layered.Components.SimpleRowGraphPlacer
import Elk.Alg.Layered.Components.ComponentGroupGraphPlacer
import Elk.Alg.Layered.Components.ComponentGroupModelOrderGraphPlacer
import Elk.Alg.Layered.Components.ModelOrderRowGraphPlacer
import Elk.Alg.Layered.Components.ComponentsProcessor
/-!
# `org.eclipse.elk.alg.layered.components`

Aggregator of the layered connected-components package: splitting a graph into connected
components and combining (placing, optionally compacting) them after layout
(`ComponentsProcessor`), the component groups and graph placers, the components compactor
(`Components.Compaction`, elk-rs `components/compaction`) and `ComponentOrderingStrategy`.
-/
