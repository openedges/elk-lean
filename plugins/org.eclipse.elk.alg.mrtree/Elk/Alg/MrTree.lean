import Elk.Alg.Common
import Elk.Alg.MrTree.Options.CompactionMode
import Elk.Alg.MrTree.Options.EdgeRoutingMode
import Elk.Alg.MrTree.Options.GraphProperties
import Elk.Alg.MrTree.Options.OrderWeighting
import Elk.Alg.MrTree.Options.TreeifyingOrder
import Elk.Alg.MrTree.Options.InternalProperties
import Elk.Alg.MrTree.Options.MrTreeOptions
import Elk.Alg.MrTree.Options.MrTreeMetaDataProvider
import Elk.Alg.MrTree.Graph.TGraphElement
import Elk.Alg.MrTree.Graph.TShape
import Elk.Alg.MrTree.Graph.TNode
import Elk.Alg.MrTree.Graph.TEdge
import Elk.Alg.MrTree.Graph.TLabel
import Elk.Alg.MrTree.Graph.TGraph
import Elk.Alg.MrTree.Graph.TArena
import Elk.Alg.MrTree.TreeUtil
import Elk.Alg.MrTree.Intermediate.RootProcessor
import Elk.Alg.MrTree.Intermediate.FanProcessor
import Elk.Alg.MrTree.Intermediate.LevelProcessor
import Elk.Alg.MrTree.Intermediate.NeighborsProcessor
import Elk.Alg.MrTree.Intermediate.LevelHeightProcessor
import Elk.Alg.MrTree.Intermediate.DirectionProcessor
import Elk.Alg.MrTree.Intermediate.NodePositionProcessor
import Elk.Alg.MrTree.Intermediate.CompactionProcessor
import Elk.Alg.MrTree.Intermediate.LevelCoordinatesProcessor
import Elk.Alg.MrTree.Intermediate.GraphBoundsProcessor
import Elk.Alg.MrTree.Intermediate.Untreeifyer
import Elk.Alg.MrTree.Intermediate.IntermediateProcessorStrategy
import Elk.Alg.MrTree.TreeLayoutPhases
import Elk.Alg.MrTree.ComponentsProcessor
import Elk.Alg.MrTree.ElkGraphImporter
import Elk.Alg.MrTree.InteractiveMrTreeGraphVisitor
import Elk.Alg.MrTree.Init
/-!
Root module of the `org.eclipse.elk.alg.mrtree` plugin (tree layout, `org.eclipse.elk.mrtree`).
Ported so far: options and metadata (registered at initialisation, see `Elk.Alg.MrTree.Init`), the
`TGraph` arena model, the importer, the components processor, the intermediate processors, `TreeUtil`
and the phase enumeration. The phases (`p1treeify`..`p4route`), `MrTree` and the layout provider follow.
-/
