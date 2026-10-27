import Elk.Alg.Layered.Options.InternalProperties
import Elk.Alg.Layered.Graph.LPadding
/-! # `org.eclipse.elk.alg.layered.graph.LGraph` -/
namespace Elk.Alg.Layered.Graph

open Elk.Graph Elk.Core.Math Elk.Alg.Layered.Options

/-- `LGraph`: a (possibly nested) layered graph. Before layering all nodes are in
`layerlessNodes`; afterwards they are distributed over `layers`. -/
structure LGraph where
  id : Int := 0
  props : PropertyMap := {}
  size : KVector := {}
  padding : LPadding := {}
  offset : KVector := {}
  layerlessNodes : Array LNodeId := #[]
  layers : Array LayerId := #[]
  parentNode : Option LNodeId := none
  internal : LGraphInternals := {}
  deriving Inhabited

namespace LGraph

/-- `getActualSize()`: size plus padding. -/
def actualSize (g : LGraph) : KVector :=
  ⟨g.size.x + g.padding.left + g.padding.right, g.size.y + g.padding.top + g.padding.bottom⟩

/-- `indexOfLayer`. -/
def indexOfLayer (g : LGraph) (layer : LayerId) : Option Nat := g.layers.findIdx? (· == layer)

end LGraph

end Elk.Alg.Layered.Graph
