import Elk.Graph.Properties
/-!
# `org.eclipse.elk.core.util.IndividualSpacings`

Minimal port: a nested property map holding per-element spacing overrides
(`CoreOptions.SPACING_INDIVIDUAL`).
TODO(IndividualSpacings): string parsing / `parseValue` and the
`getIndividualOrInherited` helpers of the Java class are not ported yet.
-/
namespace Elk.Core.Util

open Elk.Graph

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

end Elk.Core.Util
