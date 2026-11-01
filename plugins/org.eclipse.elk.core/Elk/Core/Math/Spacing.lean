import Elk.Core.Util.Java
import Elk.Core.Util.FloatConst
open Elk.Core.Util.FloatConst
/-!
# `org.eclipse.elk.core.math.{Spacing, ElkPadding, ElkMargin}`

Four-sided spacings. `ElkPadding` and `ElkMargin` are distinct types (they are
distinct layout option types) with identical structure.
-/

namespace Elk.Core.Math

open Elk.Core.Util

/-- Generic four-sided spacing (`Spacing`). -/
structure Spacing where
  top : Float := 0
  right : Float := 0
  bottom : Float := 0
  left : Float := 0
  deriving Repr, Inhabited, BEq

/-- Space between a node border and its content (`ElkPadding`). -/
structure ElkPadding where
  top : Float := 0
  right : Float := 0
  bottom : Float := 0
  left : Float := 0
  deriving Repr, Inhabited, BEq

/-- Space around a node (`ElkMargin`). -/
structure ElkMargin where
  top : Float := 0
  right : Float := 0
  bottom : Float := 0
  left : Float := 0
  deriving Repr, Inhabited, BEq

/-- Shared parsing of the Java `Spacing.parse` format: either a single number,
`[top=.., left=.., bottom=.., right=..]` (keys optional, any order) or four
comma separated numbers in the order top, right, bottom, left.
Returns `(top, right, bottom, left)`. -/
def parseSpacing (s : String) : Except String (Float × Float × Float × Float) := do
  let trimmed := s.trimAscii.toString
  let body := ((trimmed.replace "[" "").replace "]" "").replace "(" ""
  let body := (body.replace ")" "").trimAscii.toString
  if body.isEmpty then throw "The given string does not contain any numbers."
  let tokens := ((body.replace ";" ",").splitOn ",").map (·.trimAscii.toString)
  let tokens := tokens.filter (!·.isEmpty)
  let mut top := fl0p0
  let mut right := fl0p0
  let mut bottom := fl0p0
  let mut left := fl0p0
  if tokens.any (·.any (· == '=')) then
    for tok in tokens do
      match tok.splitOn "=" with
      | [k, v] =>
        let value ← match parseFloat? (v.trimAscii.toString) with
          | some f => pure f
          | none => throw s!"Cannot parse spacing value {v}."
        match k.trimAscii.toString.toLower with
        | "top" => top := value
        | "right" => right := value
        | "bottom" => bottom := value
        | "left" => left := value
        | other => throw s!"Unknown spacing side {other}."
      | _ => throw s!"Invalid spacing entry {tok}."
    return (top, right, bottom, left)
  else
    let values ← tokens.mapM fun t => match parseFloat? t with
      | some f => pure f
      | none => throw s!"Cannot parse spacing value {t}."
    match values with
    | [a] => return (a, a, a, a)
    | [tb, lr] => return (tb, lr, tb, lr)
    | [t, r, b, l] => return (t, r, b, l)
    | _ => throw s!"Expected 1, 2 or 4 spacing values, found {values.length}."

/-- Java `Spacing.toString()`: `[top=1.0,left=2.0,bottom=3.0,right=4.0]`
(Rust `spacing_to_string` order). -/
def spacingToString (top left bottom right : Float) : String :=
  s!"[top={Float.toRustDisplay top},left={Float.toRustDisplay left},bottom={Float.toRustDisplay bottom},right={Float.toRustDisplay right}]"

namespace Spacing
def ofValues (top right bottom left : Float) : Spacing := ⟨top, right, bottom, left⟩
@[inline] def horizontal (s : Spacing) : Float := s.left + s.right
@[inline] def vertical (s : Spacing) : Float := s.top + s.bottom
def setLeftRight (s : Spacing) (v : Float) : Spacing := { s with left := v, right := v }
def setTopBottom (s : Spacing) (v : Float) : Spacing := { s with top := v, bottom := v }
instance : ToString Spacing := ⟨fun s => spacingToString s.top s.left s.bottom s.right⟩
end Spacing

namespace ElkPadding
/-- `new ElkPadding(any)`. -/
def ofAny (any : Float) : ElkPadding := ⟨any, any, any, any⟩
/-- `new ElkPadding(leftRight, topBottom)`. -/
def ofSides (leftRight topBottom : Float) : ElkPadding := ⟨topBottom, leftRight, topBottom, leftRight⟩
/-- `new ElkPadding(top, right, bottom, left)`. -/
def ofValues (top right bottom left : Float) : ElkPadding := ⟨top, right, bottom, left⟩
@[inline] def horizontal (p : ElkPadding) : Float := p.left + p.right
@[inline] def vertical (p : ElkPadding) : Float := p.top + p.bottom
def toSpacing (p : ElkPadding) : Spacing := ⟨p.top, p.right, p.bottom, p.left⟩
def parse (s : String) : Except String ElkPadding := do
  let (t, r, b, l) ← parseSpacing s
  return ⟨t, r, b, l⟩
instance : ToString ElkPadding := ⟨fun p => spacingToString p.top p.left p.bottom p.right⟩
end ElkPadding

namespace ElkMargin
def ofAny (any : Float) : ElkMargin := ⟨any, any, any, any⟩
def ofSides (leftRight topBottom : Float) : ElkMargin := ⟨topBottom, leftRight, topBottom, leftRight⟩
def ofValues (top right bottom left : Float) : ElkMargin := ⟨top, right, bottom, left⟩
@[inline] def horizontal (m : ElkMargin) : Float := m.left + m.right
@[inline] def vertical (m : ElkMargin) : Float := m.top + m.bottom
def toSpacing (m : ElkMargin) : Spacing := ⟨m.top, m.right, m.bottom, m.left⟩
def parse (s : String) : Except String ElkMargin := do
  let (t, r, b, l) ← parseSpacing s
  return ⟨t, r, b, l⟩
instance : ToString ElkMargin := ⟨fun m => spacingToString m.top m.left m.bottom m.right⟩
end ElkMargin

end Elk.Core.Math
