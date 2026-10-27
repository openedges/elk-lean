import Elk.Alg.Layered.Intermediate.LongEdgeSplitter
import Elk.Alg.Layered.Intermediate.LongEdgeJoiner
import Elk.Alg.Layered.Intermediate.HyperedgeDummyMerger
import Elk.Alg.Layered.Intermediate.HypernodeProcessor
import Elk.Alg.Layered.Intermediate.NorthSouthPortPreprocessor
import Elk.Alg.Layered.Intermediate.NorthSouthPortPostprocessor
import Elk.Alg.Layered.Intermediate.InvertedPortProcessor
import Elk.Alg.Layered.Intermediate.PortSideProcessor
import Elk.Alg.Layered.Intermediate.PortListSorter
import Elk.Alg.Layered.Intermediate.ReversedEdgeRestorer
/-!
# Intermediate processors: long edges, hyperedges, north/south ports, port sides and order

Aggregator of the layered intermediate processors of task I6. Importing it registers
`LONG_EDGE_SPLITTER`, `LONG_EDGE_JOINER`, `HYPEREDGE_DUMMY_MERGER`, `HYPERNODE_PROCESSOR`,
`NORTH_SOUTH_PORT_PREPROCESSOR`, `NORTH_SOUTH_PORT_POSTPROCESSOR`, `INVERTED_PORT_PROCESSOR`,
`PORT_SIDE_PROCESSOR`, `PORT_LIST_SORTER` and `REVERSED_EDGE_RESTORER` with
`IntermediateProcessorStrategy.register`.
-/
