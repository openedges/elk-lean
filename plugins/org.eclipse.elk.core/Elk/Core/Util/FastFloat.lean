/-!
# Fast `Float` conversions (`@[csimp]` replacements of `Float.ofScientific`, `Float.ofNat`, `Float.ofInt`)

The compiled core implementation of `Float.ofScientific` (Lean 4.35 `Init.Data.OfScientific`)
builds the bound `2 ^ 53` of its fast path from a decimal string on every call
(`lean_cstr_to_nat("9007199254740992")`, a GMP `mpz_set_str` plus allocations), and
`Float.ofNat` / `Float.ofInt` / `Nat.toFloat` all go through it. Float literals that the compiler
does not hoist into closed terms (common after common-subexpression elimination) pay the same price
on every evaluation. Profiles of the force/stress models were dominated by it.

This module redirects the three functions, through `@[csimp]` lemmas that hold by `rfl`, to
`@[implemented_by]` versions with a C fast path (`elk_core_ffi.c`) for exactly the inputs of the core
fast path (mantissa below `2 ^ 53`, decimal exponent at most 22, scalar integers below `2 ^ 53` in
absolute value): one IEEE division or multiplication by the same exactly representable power of ten,
so the results are bit-identical. Every other input falls back to the core implementation. The C
functions signal "not handled" with NaN, which the core functions never return.

Every module that compiles float conversions must import this module (directly or transitively):
the leaf modules of all plugins import it.
-/
namespace Elk.Core.Util.FastFloat

/-- C fast path of `Float.ofScientific`; NaN when the input is outside the fast-path domain. -/
@[extern "elk_float_of_sci_fast"]
opaque ofScientificFast (m : @& Nat) (s : Bool) (e : @& Nat) : Float

/-- C fast path of `Float.ofNat` (scalar `n < 2 ^ 53`); NaN otherwise. -/
@[extern "elk_float_of_nat_fast"]
opaque ofNatFast (n : @& Nat) : Float

/-- C fast path of `Float.ofInt` (scalar `|i| < 2 ^ 53`); NaN otherwise. -/
@[extern "elk_float_of_int_fast"]
opaque ofIntFast (i : @& Int) : Float

/-! The core implementations, compiled before the `csimp` lemmas below exist (tests compare against
them; inside this module the redirection is not active yet). -/

/-- Core `Float.ofScientific` (reference). -/
def coreOfScientific (m : Nat) (s : Bool) (e : Nat) : Float := Float.ofScientific m s e
/-- Core `Float.ofNat` (reference). -/
def coreOfNat (n : Nat) : Float := Float.ofNat n
/-- Core `Float.ofInt` (reference). -/
def coreOfInt (i : Int) : Float := Float.ofInt i
/-- Core `Float.isNaN` (reference). -/
def coreIsNaN (x : Float) : Bool := x.isNaN
/-- Core `Float.isFinite` (reference). -/
def coreIsFinite (x : Float) : Bool := x.isFinite
/-- Core `Float.isInf` (reference). -/
def coreIsInf (x : Float) : Bool := x.isInf

/-- Run-time implementation of `ofScientific`: C fast path, core fallback. -/
def ofScientificImpl (m : Nat) (s : Bool) (e : Nat) : Float :=
  let r := ofScientificFast m s e
  -- `r == r` is false only for NaN; unlike `Float.isNaN` it compiles to an inline comparison
  if r == r then r else Float.ofScientific m s e

/-- Run-time implementation of `ofNat`: C fast path, core fallback. -/
def ofNatImpl (n : Nat) : Float :=
  let r := ofNatFast n
  if r == r then r else Float.ofNat n

/-- Run-time implementation of `ofInt`: C fast path, core fallback. -/
def ofIntImpl (i : Int) : Float :=
  let r := ofIntFast i
  if r == r then r else Float.ofInt i

/-- `Float.ofScientific` with the fast run-time implementation. -/
@[implemented_by ofScientificImpl]
def ofScientific (m : Nat) (s : Bool) (e : Nat) : Float := Float.ofScientific m s e

/-- `Float.ofNat` with the fast run-time implementation. -/
@[implemented_by ofNatImpl]
def ofNat (n : Nat) : Float := Float.ofNat n

/-- `Float.ofInt` with the fast run-time implementation. -/
@[implemented_by ofIntImpl]
def ofInt (i : Int) : Float := Float.ofInt i

/-- Compiled code calls `FastFloat.ofScientific` for `Float.ofScientific` (float literals). -/
@[csimp] theorem ofScientific_eq : @Float.ofScientific = @ofScientific := rfl

/-- Compiled code calls `FastFloat.ofNat` for `Float.ofNat` (`Nat.toFloat`, `OfNat Float`). -/
@[csimp] theorem ofNat_eq : @Float.ofNat = @ofNat := rfl

/-- Compiled code calls `FastFloat.ofInt` for `Float.ofInt`. -/
@[csimp] theorem ofInt_eq : @Float.ofInt = @ofInt := rfl

/-- Compiled code calls `FastFloat.ofNat` for `Nat.toFloat` (an abbreviation of `Float.ofNat` that
the compiler would otherwise inline after the `csimp` pass). -/
@[csimp] theorem natToFloat_eq : @Nat.toFloat = @ofNat := rfl

/-- Compiled code calls `FastFloat.ofInt` for the core `Int.toFloat` (`(i : Int).toFloat`, an
abbreviation of `Float.ofInt` inlined after the `csimp` pass like `Nat.toFloat`; without this lemma
those call sites keep the core GMP conversion). -/
@[csimp] theorem intToFloat_eq : @_root_.Int.toFloat = @ofInt := rfl

/-- `Float.isNaN` as an inline comparison (`x != x` holds exactly for NaN); the core function is an
out-of-line C call (`lean_float_isnan`) that showed up in profiles of `fmax`/`fmin`. -/
def isNaNImpl (x : Float) : Bool := x != x

/-- `Float.isFinite` as inline arithmetic: `x - x` is `0` for finite `x` and NaN for infinities and
NaN. -/
def isFiniteImpl (x : Float) : Bool := x - x == 0.0

/-- `Float.isInf` as inline arithmetic: not NaN, and `x - x` is NaN. -/
def isInfImpl (x : Float) : Bool := x == x && x - x != x - x

/-- `Float.isNaN` with the inline run-time implementation. -/
@[implemented_by isNaNImpl] def isNaN (x : Float) : Bool := x.isNaN
/-- `Float.isFinite` with the inline run-time implementation. -/
@[implemented_by isFiniteImpl] def isFinite (x : Float) : Bool := x.isFinite
/-- `Float.isInf` with the inline run-time implementation. -/
@[implemented_by isInfImpl] def isInf (x : Float) : Bool := x.isInf

/-- Compiled code tests NaN with `isNaNImpl`. -/
@[csimp] theorem isNaN_eq : @Float.isNaN = @isNaN := rfl
/-- Compiled code tests finiteness with `isFiniteImpl`. -/
@[csimp] theorem isFinite_eq : @Float.isFinite = @isFinite := rfl
/-- Compiled code tests infinity with `isInfImpl`. -/
@[csimp] theorem isInf_eq : @Float.isInf = @isInf := rfl

/-- Float literals (`0.5`): the core instance is inlined after the `csimp` pass, so the redirection
needs an instance of higher priority (and a higher default-instance priority for literals whose type
is only fixed by defaulting). Elaborated terms are unchanged up to this instance: `ofScientific`
unfolds to `Float.ofScientific`. -/
@[default_instance mid+2]
instance (priority := high) instOfScientificFloatFast : OfScientific Float where
  ofScientific := ofScientific

/-- Numerals at type `Float` (`(2 : Float)`), see `instOfScientificFloatFast`. -/
instance (priority := high) instOfNatFloatFast {n : Nat} : OfNat Float n := ⟨ofNat n⟩

end Elk.Core.Util.FastFloat
