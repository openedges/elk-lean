import Elk.Graph
namespace Elk.Core.Math
structure KVector where
  x : Float
  y : Float
  deriving Repr, Inhabited
def KVector.add (a b : KVector) : KVector := ⟨a.x + b.x, a.y + b.y⟩
end Elk.Core.Math
