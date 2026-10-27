import Elk.Core.Util.FastFloat
/-!
# `org.eclipse.elk.core.util.AbstractRandomListAccessor`

A list that grows on demand: accessing or setting an index beyond the end
first fills the gap with default items. The Java abstract method
`provideDefault()` becomes a field; the value-based API returns the updated
accessor.
-/
namespace Elk.Core.Util

/-- `AbstractRandomListAccessor<T>`. -/
structure AbstractRandomListAccessor (α : Type) where
  /-- the backing list. -/
  list : Array α := #[]
  /-- `provideDefault()`. -/
  provideDefault : Unit → α

namespace AbstractRandomListAccessor

variable {α : Type}

/-- `getListSize()`. -/
@[inline] def getListSize (a : AbstractRandomListAccessor α) : Nat := a.list.size

/-- `clearList()`. -/
def clearList (a : AbstractRandomListAccessor α) : AbstractRandomListAccessor α := { a with list := #[] }

/-- `ensureListSize(size)`: appends default items until the list has `size` entries. -/
def ensureListSize (a : AbstractRandomListAccessor α) (size : Nat) : AbstractRandomListAccessor α := Id.run do
  let mut list := a.list
  while list.size < size do
    list := list.push (a.provideDefault ())
  return { a with list := list }

/-- `getListItem(index)`: the item at `index` (created if necessary) and the updated accessor. -/
def getListItem [Inhabited α] (a : AbstractRandomListAccessor α) (index : Nat) : α × AbstractRandomListAccessor α :=
  let a := a.ensureListSize (index + 1)
  (a.list[index]!, a)

/-- `setListItem(index, value)`: gaps before `index` are filled with defaults. -/
def setListItem (a : AbstractRandomListAccessor α) (index : Nat) (value : α) : AbstractRandomListAccessor α :=
  if index < a.list.size then { a with list := a.list.set! index value }
  else
    let a := a.ensureListSize index
    { a with list := a.list.push value }

end AbstractRandomListAccessor

end Elk.Core.Util
