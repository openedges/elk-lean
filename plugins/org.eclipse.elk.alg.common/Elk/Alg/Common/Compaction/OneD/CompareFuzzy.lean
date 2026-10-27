import Elk.Core.Util.FastFloat
/-!
# `org.eclipse.elk.alg.common.compaction.oned.CompareFuzzy`

Fuzzy floating point comparisons with the fixed tolerance `0.0001`
(elk-rs `compare_fuzzy.rs`). The comparison forms are kept verbatim.
-/
namespace Elk.Alg.Common.Compaction.OneD

namespace CompareFuzzy

/-- `CompareFuzzy.TOLERANCE`. -/
def TOLERANCE : Float := 0.0001

/-- `CompareFuzzy.eq(d1, d2)`: `|d1 - d2| <= TOLERANCE`. -/
@[inline] def eq (d1 d2 : Float) : Bool := (d1 - d2).abs <= TOLERANCE

/-- `CompareFuzzy.gt(d1, d2)`: `d1 - d2 > TOLERANCE`. -/
@[inline] def gt (d1 d2 : Float) : Bool := d1 - d2 > TOLERANCE

/-- `CompareFuzzy.lt(d1, d2)`: `d2 - d1 > TOLERANCE`. -/
@[inline] def lt (d1 d2 : Float) : Bool := d2 - d1 > TOLERANCE

/-- `CompareFuzzy.ge(d1, d2)`: `d1 > d2 || eq(d1, d2)`. -/
@[inline] def ge (d1 d2 : Float) : Bool := d1 > d2 || eq d1 d2

/-- `CompareFuzzy.le(d1, d2)`: `d1 < d2 || eq(d1, d2)`. -/
@[inline] def le (d1 d2 : Float) : Bool := d1 < d2 || eq d1 d2

end CompareFuzzy

end Elk.Alg.Common.Compaction.OneD
