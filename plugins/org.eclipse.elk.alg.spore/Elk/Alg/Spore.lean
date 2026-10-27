import Elk.Alg.Common
import Elk.Alg.Spore.Options
import Elk.Alg.Spore.Graph
import Elk.Alg.Spore.SporePhases
import Elk.Alg.Spore.P1Structure
import Elk.Alg.Spore.P2ProcessingOrder
import Elk.Alg.Spore.P3Execution
import Elk.Alg.Spore.PhaseFactories
import Elk.Alg.Spore.IGraphImporter
import Elk.Alg.Spore.ElkGraphImporter
import Elk.Alg.Spore.ShrinkTree
import Elk.Alg.Spore.ShrinkTreeLayoutProvider
import Elk.Alg.Spore.OverlapRemovalLayoutProvider
import Elk.Alg.Spore.Init
/-! Root module of the `org.eclipse.elk.alg.spore` plugin (SPOrE: overlap removal `org.eclipse.elk.sporeOverlap`
and compaction `org.eclipse.elk.sporeCompaction`). Importing it registers the metadata and the layout providers. -/
