import Elk.Graph.Enum
/-!
# `org.eclipse.elk.alg.spore.options.StructureExtractionStrategy`

Port of `options/structure_extraction_strategy.rs` (elk-rs) and `StructureExtractionStrategy.java`.

The Java enum implements `ILayoutPhaseFactory` (`create()` builds the phase of `p1structure`); that
factory is not part of this module (it needs `Graph`, which imports this module): see
`Elk.Alg.Spore.PhaseFactories`.
-/
namespace Elk.Alg.Spore.Options

/-- `org.eclipse.elk.alg.spore.options.StructureExtractionStrategy`: this option defines what kind
of triangulation or other partitioning of the plane is applied to the vertices. -/
elk_enum StructureExtractionStrategy := delaunayTriangulation

end Elk.Alg.Spore.Options
