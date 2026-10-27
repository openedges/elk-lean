import Elk.Graph
/-! # `org.eclipse.elk.alg.layered.options.GraphProperties` -/
namespace Elk.Alg.Layered.Options

/-- `GraphProperties`: flags describing a layered graph (`EnumSet` members). -/
elk_enum GraphProperties := comments externalPorts hyperedges hypernodes nonFreePorts northSouthPorts selfLoops centerLabels endLabels partitions

end Elk.Alg.Layered.Options
