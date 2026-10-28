import Elk.Graph
/-!
# `org.eclipse.elk.core.data.LayoutOptionData`

Metadata of one layout option: id, type, targets, default value, bounds,
enum choices and the parser used for string values (JSON, `.elkt`,
`IndividualSpacings`). Values are `PropValue`s; parsers for enum, enum set
and object options are closures created by the metadata providers.
-/
namespace Elk.Core.Data

open Elk Elk.Graph Elk.Core.Util Elk.Core.Math

/-- `LayoutOptionData.Type`. -/
elk_enum LayoutOptionType := undefined boolean int string double enum (enumSet "ENUMSET") object

/-- `LayoutOptionData.Target`. -/
elk_enum LayoutOptionTarget := parents nodes edges ports labels

/-- `LayoutOptionData.Visibility`. -/
elk_enum LayoutOptionVisibility := visible advanced hidden

/-- `LayoutOptionData.Dependency`: the option only applies if `optionId` has
`requiredValue` (or any value when `none`). -/
structure LayoutOptionDependency where
  optionId : String
  requiredValue : Option PropValue := none

/-- Parser for the string form of an option value. -/
abbrev OptionParser := String → Option PropValue

/-- Lower/upper bound of a numeric option: plain values are inclusive,
`ExclusiveBounds.greaterThan/lessThan` are exclusive (Java `ExclusiveBounds`). -/
inductive OptionBound where
  | inclusive (v : PropValue)
  | exclusive (v : PropValue)
  deriving Inhabited

namespace OptionBound
def value : OptionBound → PropValue
  | .inclusive v => v
  | .exclusive v => v
def isExclusive : OptionBound → Bool
  | .exclusive _ => true
  | .inclusive _ => false
/-- `ExclusiveBounds.greaterThan(x)`. -/
def greaterThan (x : Float) : OptionBound := .exclusive (.double x)
/-- `ExclusiveBounds.lessThan(x)`. -/
def lessThan (x : Float) : OptionBound := .exclusive (.double x)
/-- Inclusive double bound. -/
def atLeast (x : Float) : OptionBound := .inclusive (.double x)
def atMost (x : Float) : OptionBound := .inclusive (.double x)
/-- Inclusive integer bound. -/
def atLeastInt (x : Int) : OptionBound := .inclusive (.int x)
def atMostInt (x : Int) : OptionBound := .inclusive (.int x)
end OptionBound

structure LayoutOptionData where
  id : String
  group : String := ""
  legacyIds : Array String := #[]
  defaultValue : Option PropValue := none
  type : LayoutOptionType := .undefined
  name : String := ""
  description : String := ""
  targets : EnumSet LayoutOptionTarget := EnumSet.empty
  dependencies : Array LayoutOptionDependency := #[]
  visibility : LayoutOptionVisibility := .visible
  lowerBound : Option OptionBound := none
  upperBound : Option OptionBound := none
  /-- Enum constant names (ENUM / ENUMSET), in ordinal order. -/
  choices : Array String := #[]
  /-- Parser for ENUM / ENUMSET / OBJECT values. -/
  parser : Option OptionParser := none

namespace LayoutOptionData

instance : BEq LayoutOptionData := ⟨fun a b => a.id == b.id⟩
instance : Hashable LayoutOptionData := ⟨fun a => hash a.id⟩
instance : ToString LayoutOptionData := ⟨fun a => a.id⟩
instance : Inhabited LayoutOptionData := ⟨{ id := "" }⟩

/-- `canParseValue`. -/
def canParseValue (d : LayoutOptionData) : Bool :=
  match d.type with
  | .undefined => false
  | .enum | .enumSet | .object => d.parser.isSome
  | _ => true

/-- Digits of `s` from byte `i` (`n` = byte size) accumulated into `acc`; `none` on a non-digit or
as soon as the value exceeds `limit` (no later digit can bring it back into range). -/
private partial def int32Digits (s : String) (n i : Nat) (acc limit : Nat) : Option Nat :=
  if i < n then
    let b := ElkEnum.utf8ByteAt s i
    if b >= 48 && b <= 57 then
      let acc := acc * 10 + (b - 48).toNat
      if acc > limit then none else int32Digits s n (i + 1) acc limit
    else none
  else some acc

/-- `parseInt32?` (Rust `s.parse::<i32>()`: an optional `+`/`-`, one or more ASCII digits, within the
`i32` range) on the bytes of `s`, without the `List Char` of the reference. -/
def parseInt32Bytes? (s : String) : Option Int :=
  let n := s.utf8ByteSize
  if n == 0 then none
  else
    let b0 := ElkEnum.utf8ByteAt s 0
    let neg := b0 == 45
    let start := if neg || b0 == 43 then 1 else 0
    if start >= n then none
    else
      match int32Digits s n start 0 (if neg then 2147483648 else 2147483647) with
      | some v => some (if neg then -(v : Int) else (v : Int))
      | none => none

/-- `parseValue(String)`: elk-rs semantics (`"null"` and empty strings yield
`none`, except that an empty ENUMSET parses to the empty set via the parser). -/
def parseValue (d : LayoutOptionData) (valueString : String) : Option PropValue :=
  if valueString == "null" then none
  else if valueString.isEmpty && d.type != .enumSet then none
  else
    match d.type with
    | .boolean => (PropValue.parseBool? valueString).map PropValue.bool
    | .int => (parseInt32Bytes? valueString).map PropValue.int
    | .double => (parseFloat? valueString).map PropValue.double
    | .string => some (PropValue.string valueString)
    | .enum | .enumSet | .object => d.parser.bind fun p => p valueString
    | .undefined => none

/-- `getDefaultDefault()`: the type's natural default. -/
def defaultDefaultValue (d : LayoutOptionData) : Option PropValue :=
  match d.type with
  | .string => some (.string "")
  | .boolean => some (.bool false)
  | .int => some (.int 0)
  | .double => some (.double 0.0)
  | _ => none

/-- `getChoices()`: `["false", "true"]` for booleans, the constant names for enums. -/
def getChoices (d : LayoutOptionData) : Array String :=
  match d.type with
  | .boolean => #["false", "true"]
  | .enum | .enumSet => d.choices
  | _ => #[]

def enumValueCount (d : LayoutOptionData) : Nat :=
  match d.type with
  | .enum | .enumSet => d.choices.size
  | _ => 0

def enumValueName (d : LayoutOptionData) (index : Nat) : Option String := d.choices[index]?

/-! ### Builder helpers used by the metadata providers -/

/-- Enum constant names of an `ElkEnum`, in ordinal order. -/
def enumChoices (α : Type) [ElkEnum α] : Array String := (ElkEnum.values : Array α).map ElkEnum.javaName

/-- Parser for an ENUM option (elk-rs `parse_enum_value` semantics). -/
def enumParser (α : Type) [ElkEnum α] : OptionParser :=
  fun s => (ElkEnum.ofNameLoose? s : Option α).map PropCodec.enc

/-- Parser for an ENUMSET option (elk-rs `parse_enumset_value` semantics). -/
def enumSetParser (α : Type) [ElkEnum α] : OptionParser :=
  fun s => (EnumSet.parse? s : Option (EnumSet α)).map PropCodec.enc

/-- Parser for `KVector` object options. -/
def kvectorParser : OptionParser := fun s => (KVector.parse s).toOption.map PropValue.vector

/-- Parser for `KVectorChain` object options. -/
def kvectorChainParser : OptionParser := fun s => (KVectorChain.parse s).toOption.map PropValue.vectorChain

/-- Parser for `ElkPadding` object options. -/
def paddingParser : OptionParser := fun s =>
  (parseSpacingValue? s).map fun (t, r, b, l) => PropValue.padding ⟨t, r, b, l⟩

/-- Parser for `ElkMargin` object options. -/
def marginsParser : OptionParser := fun s =>
  (parseSpacingValue? s).map fun (t, r, b, l) => PropValue.margins ⟨t, r, b, l⟩

/-- Convenience constructor mirroring elk-rs `LayoutOptionDataBuilder`. -/
def mk' (id : String) (type : LayoutOptionType) (name description : String)
    (targets : Array LayoutOptionTarget) (defaultValue : Option PropValue := none)
    (group : String := "") (visibility : LayoutOptionVisibility := .visible)
    (lowerBound upperBound : Option OptionBound := none) (legacyIds : Array String := #[])
    (choices : Array String := #[]) (parser : Option OptionParser := none) : LayoutOptionData :=
  { id, group, legacyIds, defaultValue, type, name, description,
    targets := EnumSet.of targets, visibility, lowerBound, upperBound, choices, parser }

end LayoutOptionData

end Elk.Core.Data
