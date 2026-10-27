import Elk.Graph.Monad
import Elk.Core.Data.LayoutMetaDataService
import Elk.Core.Util.ExclusiveBounds
import Elk.Core.Util.GraphElementVisitor
import Elk.Core.Validation.GraphIssue
/-!
# `org.eclipse.elk.core.validation.LayoutOptionValidator`

Validating visitor checking every registered option value of an element against
the option's type and bounds. Unparsed (`proxy`) values are parsed with the
option's metadata first and stored back, like elk-rs.

Type checks: `STRING`/`BOOLEAN`/`INT`/`DOUBLE` require the matching `PropValue`
constructor; `ENUM`/`ENUMSET` require an enum ordinal / enum set; `OBJECT` accepts
every non-primitive value (elk-rs compares the `TypeId` registered for the option,
which `PropValue` does not carry).
-/
namespace Elk.Core.Validation

open Elk Elk.Graph Elk.Core.Data Elk.Core.Util

/-- Rust `format!("{:?}", x)` for `f64`: like `Display` but with a `.0` for integral values
and exponent notation below `1e-4` and from `1e16` on. -/
def floatToRustDebug (x : Float) : String := Id.run do
  if x.isNaN || x.isInf then return Float.toRustDisplay x
  let ax := x.abs
  if ax == 0.0 || (ax >= 1e-4 && ax < 1e16) then
    let s := Float.toRustDisplay x
    return if s.contains '.' then s else s ++ ".0"
  -- exponent form from the shortest round-trip digits
  let s := Float.toShortest ax
  let (mantissa, exp) := match s.splitOn "e" with
    | [m, e] => (m, (parseInt64? (if e.startsWith "+" then (e.drop 1).toString else e)).getD 0)
    | _ => (s, (0 : Int))
  let (intPart, fracPart) := match mantissa.splitOn "." with
    | [i, f] => (i, f)
    | _ => (mantissa, "")
  let digits := (intPart ++ fracPart).toList.dropWhile (· == '0')
  let mut e10 : Int := exp - fracPart.length
  -- strip trailing zeros
  let mut ds := digits.reverse
  while ds.head? == some '0' do
    ds := ds.tail
    e10 := e10 + 1
  let sig := ds.reverse
  let some first := sig.head? | return "0e0"
  let rest := String.ofList sig.tail
  let sciExp := e10 + (sig.length : Int) - 1
  let m := if rest.isEmpty then String.singleton first else s!"{first}.{rest}"
  return s!"{if x < 0.0 then "-" else ""}{m}e{sciExp}"

/-- `LayoutOptionValidator.isValidType` (elk-rs `is_valid_type`). -/
private def isValidType (optionData : LayoutOptionData) (value : PropValue) : Bool :=
  match optionData.type, value with
  | .string, .string _ => true
  | .string, _ => false
  | .boolean, .bool _ => true
  | .boolean, _ => false
  | .int, .int _ => true
  | .int, _ => false
  | .double, .double _ => true
  | .double, _ => false
  | .enum, .enum _ => true
  | .enum, _ => false
  | .enumSet, .enumSet _ => true
  | .enumSet, _ => false
  | .object, .bool _ | .object, .int _ | .object, .double _ | .object, .string _
  | .object, .enum _ | .object, .enumSet _ => false
  | .object, _ => true
  | .undefined, _ => true

/-- elk-rs `format_any`. -/
private def formatValue : PropValue → String
  | .string s => s
  | .bool b => if b then "true" else "false"
  | .int i => toString i
  | .double d => floatToRustDebug d
  | _ => "<value>"

/-- Formats a bound; exclusive bounds print as `ExclusiveLowerBound/UpperBound.toString()`. -/
private def formatBound : OptionBound → String
  | .inclusive v => formatValue v
  | .exclusive (.double d) => s!"{floatToRustDebug d} (exclusive)"
  | .exclusive _ => "<value>"

/-- elk-rs `compare_numeric`. -/
private def compareNumeric (bound value : PropValue) : Option Ordering :=
  match bound, value with
  | .int b, .int v => some (compare b v)
  | .int _, _ => none
  | .double b, .double v => some (Float.comparePartial b v)
  | _, _ => none

/-- elk-rs `compare_lower_bound`. -/
private def compareLowerBound (bound : OptionBound) (value : PropValue) : Option Ordering :=
  match bound with
  | .exclusive (.double b) =>
    match value with
    | .double v => some ((ExclusiveBounds.greaterThan b).compareTo v)
    | _ => none
  | .exclusive _ => none
  | .inclusive b => compareNumeric b value

/-- elk-rs `compare_upper_bound`. -/
private def compareUpperBound (bound : OptionBound) (value : PropValue) : Option Ordering :=
  match bound with
  | .exclusive (.double b) =>
    match value with
    | .double v => some ((ExclusiveBounds.lessThan b).compareTo v)
    | _ => none
  | .exclusive _ => none
  | .inclusive b => compareNumeric b value

private def optionLabel (o : LayoutOptionData) : String := if o.name.isEmpty then o.id else o.name

/-- elk-rs `option_type_name`. -/
private def optionTypeName : LayoutOptionType → String
  | .string => "String"
  | .boolean => "Boolean"
  | .int => "Integer"
  | .double => "Double"
  | .enum => "Enum"
  | .enumSet => "EnumSet"
  | .object => "Object"
  | .undefined => "Object"

/-- `LayoutOptionValidator.checkProperty(option, value, element)`: the issue for an invalid
value, if any. -/
def checkProperty (optionData : LayoutOptionData) (value : PropValue) (el : ElementId) : Option GraphIssue := Id.run do
  if !isValidType optionData value then
    return some { element := some el, severity := .error,
                  message := s!"The assigned value {formatValue value} of the option '{optionLabel optionData}' does not match the type {optionTypeName optionData.type}." }
  if let some bound := optionData.lowerBound then
    if compareLowerBound bound value == some .gt then
      return some { element := some el, severity := .error,
                    message := s!"The assigned value {formatValue value} of the option '{optionLabel optionData}' is less than the lower bound {formatBound bound}." }
  if let some bound := optionData.upperBound then
    if compareUpperBound bound value == some .lt then
      return some { element := some el, severity := .error,
                    message := s!"The assigned value {formatValue value} of the option '{optionLabel optionData}' is greater than the upper bound {formatBound bound}." }
  return none

/-- `org.eclipse.elk.core.validation.LayoutOptionValidator`. -/
structure LayoutOptionValidator where
  issuesRef : IO.Ref (Array GraphIssue)

namespace LayoutOptionValidator

/-- `new LayoutOptionValidator()`. -/
def new : IO LayoutOptionValidator := do return { issuesRef := ← IO.mkRef #[] }

/-- `getIssues()`. -/
def issues (v : LayoutOptionValidator) : IO (Array GraphIssue) := v.issuesRef.get

/-- `visit(element)`: checks all options of the element that are known to the metadata service. -/
def visit (v : LayoutOptionValidator) (el : ElementId) : ElkM Unit := do
  let entries := ((← get).props el).entries
  for (key, value) in entries do
    let resolved ← match value with
      | .proxy raw => do
        match ← LayoutMetaDataService.getOptionData key.id with
        | some optionData =>
          match optionData.parseValue raw with
          | some parsed =>
            modify (·.modifyProps el (·.setRaw key parsed))
            pure (some parsed)
          | none => pure none
        | none => pure none
      | other => pure (some other)
    let some value := resolved | continue
    let some optionData ← LayoutMetaDataService.getOptionData key.id | continue
    if let some issue := checkProperty optionData value el then
      v.issuesRef.modify (·.push issue)

/-- The validator as an `IValidatingGraphElementVisitor`. -/
def toVisitor (v : LayoutOptionValidator) : GraphElementVisitor := { visit := v.visit, issues := some v.issues }

end LayoutOptionValidator

end Elk.Core.Validation
