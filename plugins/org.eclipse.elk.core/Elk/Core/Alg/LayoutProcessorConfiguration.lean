import Elk.Graph
/-!
# `org.eclipse.elk.core.alg.LayoutProcessorConfiguration`

Processor factories (enum constants `F`) slotted before/after each phase of the phase
enumeration `P`: slot `2 * ordinal` is "before phase", `2 * ordinal + 1`… — no: like the
Java/Rust implementation, slot index `ordinal(phase)` means *before* the phase and
`ordinal(phase) + 1` means *after* it (so "after phase k" and "before phase k+1" share a
slot).
-/
namespace Elk.Core.Alg

open Elk.Graph

/-- `LayoutProcessorConfiguration<P, G>`: slots of processor factories. -/
structure LayoutProcessorConfiguration (P F : Type) where
  /-- `list` of `AbstractRandomListAccessor`: slot → factories in insertion order. -/
  list : Array (Array F) := #[]
  /-- Slot selected by `before`/`after` for the next `add`. -/
  currentIndex : Option Nat := none
  deriving Inhabited

namespace LayoutProcessorConfiguration

variable {P F : Type} [ElkEnum P] [BEq F]

/-- `create()`. -/
def create : LayoutProcessorConfiguration P F := {}

/-- `createFrom(source)`. -/
def createFrom (source : LayoutProcessorConfiguration P F) : LayoutProcessorConfiguration P F := source

/-- `clear()`. -/
def clear (_c : LayoutProcessorConfiguration P F) : LayoutProcessorConfiguration P F := {}

/-- Index of `phase` in the phase enumeration (`phaseIndex`). -/
def phaseIndex (phase : P) : Nat := ElkEnum.ordinal phase

/-- `before(phase)`. -/
def before (c : LayoutProcessorConfiguration P F) (phase : P) : LayoutProcessorConfiguration P F :=
  { c with currentIndex := some (phaseIndex phase) }

/-- `after(phase)`. -/
def after (c : LayoutProcessorConfiguration P F) (phase : P) : LayoutProcessorConfiguration P F :=
  { c with currentIndex := some (phaseIndex phase + 1) }

/-- `getListSize()`. -/
def listSize (c : LayoutProcessorConfiguration P F) : Nat := c.list.size

private def ensureListSize (c : LayoutProcessorConfiguration P F) (size : Nat) : LayoutProcessorConfiguration P F :=
  if c.list.size >= size then c else { c with list := c.list ++ Array.replicate (size - c.list.size) #[] }

/-- `getListItem(index)` (empty for slots beyond the list). -/
def getListItem (c : LayoutProcessorConfiguration P F) (index : Nat) : Array F := c.list[index]?.getD #[]

/-- `doAdd(index, processor)`: appends unless the same factory (enum identity) is already in the slot. -/
def doAdd (c : LayoutProcessorConfiguration P F) (index : Nat) (processor : F) : LayoutProcessorConfiguration P F :=
  let c := c.ensureListSize (index + 1)
  if (c.list[index]!).contains processor then c
  else { c with list := c.list.modify index (·.push processor) }

/-- `add(processor)`: into the slot selected by `before`/`after`; Java throws
`IllegalStateException` when none was selected. -/
def add (c : LayoutProcessorConfiguration P F) (processor : F) : Except String (LayoutProcessorConfiguration P F) :=
  match c.currentIndex with
  | none => .error "java.lang.IllegalStateException: Did not call before(...) or after(...) before calling add(...)."
  | some index => .ok (c.doAdd index processor)

/-- `addBefore(phase, processor)` (resets the current slot). -/
def addBefore (c : LayoutProcessorConfiguration P F) (phase : P) (processor : F) : LayoutProcessorConfiguration P F :=
  { c with currentIndex := none }.doAdd (phaseIndex phase) processor

/-- `addAfter(phase, processor)` (resets the current slot). -/
def addAfter (c : LayoutProcessorConfiguration P F) (phase : P) (processor : F) : LayoutProcessorConfiguration P F :=
  { c with currentIndex := none }.doAdd (phaseIndex phase + 1) processor

/-- `addAll(configuration)`. -/
def addAll (c : LayoutProcessorConfiguration P F) (other : LayoutProcessorConfiguration P F) : LayoutProcessorConfiguration P F := Id.run do
  let mut c := c
  for index in [0:other.listSize] do
    for processor in other.getListItem index do
      c := c.doAdd index processor
  return c

/-- `processorsBefore(phase)`. -/
def processorsBefore (c : LayoutProcessorConfiguration P F) (phase : P) : Array F := c.getListItem (phaseIndex phase)

/-- `processorsAfter(phase)`. -/
def processorsAfter (c : LayoutProcessorConfiguration P F) (phase : P) : Array F := c.getListItem (phaseIndex phase + 1)

end LayoutProcessorConfiguration

end Elk.Core.Alg
