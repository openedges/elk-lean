import Elk.Core.Util.Java
import Elk.Core.Util.Ffi
/-!
# `org.eclipse.elk.core.util.ExclusiveBounds`

Markers for option bounds that exclude their own value (e.g. `> 0`). In Rust
they are stored as `Arc<dyn Any>` in the lower/upper bound of an option and
recognised by `LayoutOptionValidator` via `downcast_ref`. `PropValue` has no
constructor for them, so the Lean port keeps them as a closed `ExclusiveBound`
type that the option metadata/validator code can hold next to a `Property`.
-/
namespace Elk.Core.Util

/-- `ExclusiveBounds.ExclusiveLowerBound`: values must be strictly greater. -/
structure ExclusiveLowerBound where
  exclusiveLowerBound : Float
  deriving Inhabited

/-- `ExclusiveBounds.ExclusiveUpperBound`: values must be strictly smaller. -/
structure ExclusiveUpperBound where
  exclusiveUpperBound : Float
  deriving Inhabited

namespace ExclusiveLowerBound

/-- `compareTo(value)`: `lt` if the bound is below `value`, else `gt` (never `eq`). -/
def compareTo (b : ExclusiveLowerBound) (value : Float) : Ordering :=
  if b.exclusiveLowerBound < value then .lt else .gt

instance : BEq ExclusiveLowerBound := ⟨fun a b => a.exclusiveLowerBound == b.exclusiveLowerBound⟩
instance : Hashable ExclusiveLowerBound := ⟨fun b => hash b.exclusiveLowerBound.toBits⟩
instance : ToString ExclusiveLowerBound := ⟨fun b => s!"{Float.toShortest b.exclusiveLowerBound} (exclusive)"⟩

end ExclusiveLowerBound

namespace ExclusiveUpperBound

/-- `compareTo(value)`: `gt` if the bound is above `value`, else `lt` (never `eq`). -/
def compareTo (b : ExclusiveUpperBound) (value : Float) : Ordering :=
  if b.exclusiveUpperBound > value then .gt else .lt

instance : BEq ExclusiveUpperBound := ⟨fun a b => a.exclusiveUpperBound == b.exclusiveUpperBound⟩
instance : Hashable ExclusiveUpperBound := ⟨fun b => hash b.exclusiveUpperBound.toBits⟩
instance : ToString ExclusiveUpperBound := ⟨fun b => s!"{Float.toShortest b.exclusiveUpperBound} (exclusive)"⟩

end ExclusiveUpperBound

/-- Either kind of exclusive bound (what `layout_option_validator` downcasts to). -/
inductive ExclusiveBound where
  | lower (b : ExclusiveLowerBound)
  | upper (b : ExclusiveUpperBound)
  deriving Inhabited

namespace ExclusiveBound

instance : BEq ExclusiveBound where
  beq
    | .lower a, .lower b => a == b
    | .upper a, .upper b => a == b
    | _, _ => false

instance : ToString ExclusiveBound where
  toString
    | .lower b => toString b
    | .upper b => toString b

/-- `compareTo(value)` of the wrapped bound. -/
def compareTo : ExclusiveBound → Float → Ordering
  | .lower b, v => b.compareTo v
  | .upper b, v => b.compareTo v

end ExclusiveBound

-- `ExclusiveBounds` factory methods.
namespace ExclusiveBounds

/-- `ExclusiveBounds.greaterThan(exclusiveLowerBound)`. -/
def greaterThan (exclusiveLowerBound : Float) : ExclusiveLowerBound := ⟨exclusiveLowerBound⟩

/-- `ExclusiveBounds.lessThan(exclusiveUpperBound)`. -/
def lessThan (exclusiveUpperBound : Float) : ExclusiveUpperBound := ⟨exclusiveUpperBound⟩

end ExclusiveBounds

end Elk.Core.Util
