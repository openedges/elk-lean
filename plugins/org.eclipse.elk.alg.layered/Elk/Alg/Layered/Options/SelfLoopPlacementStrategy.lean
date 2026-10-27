import Elk.Graph.Enum
/-!
# `org.eclipse.elk.alg.layered.options.SelfLoopPlacementStrategy`

Port of `SelfLoopPlacementStrategy.java` (elk-rs has no counterpart).

The enum is unused in ELK 0.12.0 (no option or algorithm refers to it); it is kept
for the one-class-one-file correspondence.
-/
namespace Elk.Alg.Layered.Options

/-- `org.eclipse.elk.alg.layered.options.SelfLoopPlacementStrategy`: Enumeration to distinguish the
possible ways to distribute the selfLoops around a node. -/
elk_enum SelfLoopPlacementStrategy := equallyDistributed northStacked northSequence

end Elk.Alg.Layered.Options
