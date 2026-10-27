import Elk.Alg.Layered.Options.InternalProperties
/-! # `org.eclipse.elk.alg.layered.graph.LLabel` -/
namespace Elk.Alg.Layered.Graph

open Elk.Graph Elk.Core.Math Elk.Alg.Layered.Options

/-- `LLabel` (an `LShape` with text). -/
structure LLabel where
  /-- `LGraphElement.id` (scratch id used by algorithms). -/
  id : Int := 0
  /-- Public layout options (`MapPropertyHolder`). -/
  props : PropertyMap := {}
  position : KVector := {}
  size : KVector := {}
  text : String := ""
  internal : LLabelInternals := {}
  deriving Inhabited

end Elk.Alg.Layered.Graph
