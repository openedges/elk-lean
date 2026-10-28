import Elk.Graph.Properties
/-!
# `org.eclipse.elk.alg.common.spore.InternalProperties`

Container for property definitions for internal use (elk-rs
`spore/internal_properties.rs`).
-/
namespace Elk.Alg.Common.Spore

open Elk.Graph

namespace InternalProperties

/-- `InternalProperties.FUZZINESS`: fuzziness of fuzzy comparisons used to avoid
non-deterministic behavior caused by double imprecision. -/
def FUZZINESS : Float := 0.0001

/-- `InternalProperties.DEBUG_SVG`: enables SVG debug output (`"debugSVG"`, default `false`). -/
def DEBUG_SVG : Property Bool := Property.withDefault "debugSVG" false

/-- `InternalProperties.OVERLAPS_EXISTED`: set in `GrowTreePhase` if two nodes of an edge in
the minimum spanning tree were overlapping (`"overlapsExisted"`, default `true`). -/
def OVERLAPS_EXISTED : Property Bool := Property.withDefault "overlapsExisted" true

/-- Guava `DoubleMath.fuzzyCompare(a, b, tolerance)` (the Java callers `TTriangle`, `Node`,
`DepthFirstCompaction`, `ScanlineOverlapCheck`): `0` if `fuzzyEquals` (`|a - b| <= eps`, `a == b`
— equal infinities — or both NaN), else `-1`/`1` by `<`/`>`, else (one NaN) NaN is the larger.
(elk-rs' `fuzzy_compare` gave `1` for equal infinities and NaN.) -/
def fuzzyCompare (a b eps : Float) : Int :=
  if (a - b).abs <= eps || a == b || (a.isNaN && b.isNaN) then 0
  else if a < b then -1
  else if a > b then 1
  else if a.isNaN then 1
  else -1

end InternalProperties

end Elk.Alg.Common.Spore
