import Elk.Alg.Common
import Elk.Alg.Disco.Graph.Ids
import Elk.Alg.Disco.Graph.DCDirection
import Elk.Alg.Disco.Graph.DCExtension
import Elk.Alg.Disco.Graph.DCElement
import Elk.Alg.Disco.Graph.DCComponent
import Elk.Alg.Disco.Graph.DCGraph
import Elk.Alg.Disco.Options.CompactionStrategy
import Elk.Alg.Disco.Options.DisCoOptions
import Elk.Alg.Disco.Options.DisCoMetaDataProvider
import Elk.Alg.Disco.Structures.DCPolyomino
import Elk.Alg.Disco.Transform.IGraphTransformer
import Elk.Alg.Disco.Transform.ElkGraphComponentsProcessor
import Elk.Alg.Disco.Transform.ElkGraphTransformer
import Elk.Alg.Disco.ICompactor
import Elk.Alg.Disco.DisCoPolyominoCompactor
import Elk.Alg.Disco.DisCoLayoutProvider
import Elk.Alg.Disco.Init
/-! Root module of the `org.eclipse.elk.alg.disco` plugin (disconnected components layout): the
`DCGraph` model, the ElkGraph transformer, the polyomino compactor, the options/metadata and the
layout provider. Importing it registers the `org.eclipse.elk.disco` provider and (lazily) its
metadata. -/
