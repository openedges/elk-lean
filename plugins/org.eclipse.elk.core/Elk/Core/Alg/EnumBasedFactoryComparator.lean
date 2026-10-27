import Elk.Graph
/-!
# `org.eclipse.elk.core.alg.EnumBasedFactoryComparator`

Orders processor factories by their enum ordinal. The Lean configuration holds a single
factory enum type `F`, so the Java "different enumerations" failure cannot occur.
-/
namespace Elk.Core.Alg

/-- `EnumBasedFactoryComparator.compare(factory1, factory2)`. -/
def EnumBasedFactoryComparator.compare {F : Type} [ElkEnum F] (a b : F) : Ordering :=
  Ord.compare (ElkEnum.ordinal a) (ElkEnum.ordinal b)

end Elk.Core.Alg
