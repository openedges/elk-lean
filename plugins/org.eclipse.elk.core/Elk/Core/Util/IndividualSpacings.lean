import Elk.Graph.Model
import Elk.Core.Data.LayoutMetaDataService
/-!
# `org.eclipse.elk.core.util.IndividualSpacings`

A nested property map holding per-element spacing overrides
(`CoreOptions.SPACING_INDIVIDUAL`).

`CoreOptions` imports this module, so `getIndividualOrInherited` uses a local
copy of the `SPACING_INDIVIDUAL` property (same id, no default).

Deviations from elk-rs:
* `parse` returns a new value instead of mutating `self` (a failed parse
  therefore keeps no partially parsed entries).
* `toString` cannot resolve unparsed `proxy` values without the metadata
  registry; they are printed as their raw string.
-/
namespace Elk.Core.Util

open Elk Elk.Graph Elk.Core.Math Elk.Core.Data

/-- `org.eclipse.elk.core.util.IndividualSpacings`: a property holder with the
spacing options that apply to one element only. -/
structure IndividualSpacings where
  /-- The nested option values. -/
  props : PropertyMap := {}
  deriving Inhabited

instance : PropCodec IndividualSpacings where
  enc s := .individualSpacings s.props.entries
  dec
    | .individualSpacings es => some { props := { entries := es } }
    | _ => none

namespace IndividualSpacings

/-- `IndividualSpacings.SERIALIZED_OPTION_SEPARATOR`. -/
def SERIALIZED_OPTION_SEPARATOR : String := ";,;"

/-- Local copy of `CoreOptions.SPACING_INDIVIDUAL` (see the module doc). -/
private def SPACING_INDIVIDUAL_PROPERTY : Property IndividualSpacings :=
  Property.mk' "org.eclipse.elk.spacing.individual"

/-- `new IndividualSpacings()`. -/
def new : IndividualSpacings := {}

/-- `new IndividualSpacings(other)`: a copy. -/
def ofOther (other : IndividualSpacings) : IndividualSpacings := { props := other.props }

/-- `getProperties()`. -/
@[inline] def properties (s : IndividualSpacings) : PropertyMap := s.props

/-- `IndividualSpacings.getIndividualOrInherited(node, property)`: the node's individual
spacing for the property if set, otherwise the parent's value (stored or default);
`none` for a root node without individual value. -/
def getIndividualOrInherited {α : Type} [PropCodec α] (g : ElkGraph) (node : NodeId) (p : Property α) : Option α :=
  let n := g.node node
  let individual : Option α := match n.props.get SPACING_INDIVIDUAL_PROPERTY with
    | some ind => if ind.props.has p then ind.props.get p else none
    | none => none
  match individual with
  | some v => some v
  | none => match n.parent with
    | some parent => (g.node parent).props.get p
    | none => none

/-- `IndividualSpacings.parse(value)` into an existing value: `id:value;,;id:value`, option
ids are resolved by suffix and values parsed with the registered option parsers. -/
def parseInto (s : IndividualSpacings) (value : String) : IO (Except String IndividualSpacings) := do
  match ← LayoutMetaDataService.parseIndividualSpacings value with
  | .error e => return .error e
  | .ok entries => return .ok { props := entries.foldl (fun m e => m.setRaw e.1 e.2) s.props }

/-- `IndividualSpacings.parse(value)` into a fresh value. -/
def parse (value : String) : IO (Except String IndividualSpacings) := parseInto {} value

/-- Rust `spacing_to_string`. -/
private def spacingToString (top left bottom right : Float) : String :=
  s!"[top={Float.toRustDisplay top},left={Float.toRustDisplay left},bottom={Float.toRustDisplay bottom},right={Float.toRustDisplay right}]"

/-- Rust `any_value_to_string`: the string form of the serializable value kinds; `none`
for the others (enums, enum sets, lists, nested spacings, dynamic values), which
elk-rs leaves out of the serialization. -/
def valueToString? : PropValue → Option String
  | .double d => some (Float.toRustDisplay d)
  | .int i => some (toString i)
  | .bool b => some (if b then "true" else "false")
  | .string s => some s
  | .vector v => some s!"({Float.toRustDisplay v.x},{Float.toRustDisplay v.y})"
  | .vectorChain c => some (KVectorChain.toJavaString c)
  | .padding p => some (spacingToString p.top p.left p.bottom p.right)
  | .margins m => some (spacingToString m.top m.left m.bottom m.right)
  | .proxy raw => some raw
  | _ => none

/-- Rust `Display` / Java `toString()`: `id:value` entries joined with `;,;`. -/
instance : ToString IndividualSpacings where
  toString s :=
    SERIALIZED_OPTION_SEPARATOR.intercalate <| Array.toList <| s.props.entries.filterMap fun (k, v) =>
      (valueToString? v).map fun str => s!"{k.id}:{str}"

end IndividualSpacings

end Elk.Core.Util
