import Elk.Graph.Monad
import Elk.Core.Exceptions
import Elk.Core.Options.CoreOptions
import Elk.Core.Util.GraphElementVisitor
/-!
# `org.eclipse.elk.core.util.ElkSpacings`

Configures the core spacing options relative to a base spacing value
(`ElkSpacings.withBaseValue(base).withFactor(...).toVisitor()`).

The builder is a value; the `with*` methods that throw `IllegalArgumentException`
in Java (and panic in Rust) return `Except String` with the
`java.lang.IllegalArgumentException: <message>` convention.
-/
namespace Elk.Core.Util

open Elk Elk.Graph Elk.Core Elk.Core.Options

/-- A spacing option with its factor relative to the base spacing (`SpacingFactor`). -/
structure SpacingFactor where
  property : Property Float
  factor : Float

/-- The configured spacings ready to be applied (`ElkSpacings.AbstractSpacingsBuilder` result). -/
structure SpacingConfigurator where
  baseSpacing : Float
  overwrite : Bool
  factors : Array SpacingFactor
  noOp : Bool

namespace SpacingConfigurator

/-- `apply(holder)`: sets `factor * baseSpacing` for every option (unless the option is
already set and `overwrite` is off). -/
def applyToProperties (c : SpacingConfigurator) (props : PropertyMap) : PropertyMap := Id.run do
  if c.noOp then return props
  let mut props := props
  for entry in c.factors do
    if !c.overwrite && props.has entry.property then continue
    props := props.set entry.property (entry.factor * c.baseSpacing)
  return props

/-- Pure `apply(element)`. -/
def applyPure (c : SpacingConfigurator) (g : ElkGraph) (el : ElementId) : ElkGraph :=
  if c.noOp then g else g.modifyProps el c.applyToProperties

/-- `apply(element)`. -/
def apply (c : SpacingConfigurator) (el : ElementId) : ElkM Unit :=
  if c.noOp then pure () else modify (c.applyPure · el)

/-- `toVisitor()`. -/
def toVisitor (c : SpacingConfigurator) : GraphElementVisitor := { visit := c.apply }

end SpacingConfigurator

/-- `ElkSpacings.ElkCoreSpacingsBuilder`. -/
structure ElkCoreSpacingsBuilder where
  baseSpacing : Float
  overwrite : Bool := false
  factors : Array SpacingFactor

namespace ElkCoreSpacingsBuilder

/-- `BASE_SPACING_OPTION`. -/
def BASE_SPACING_OPTION : Property Float := CoreOptions.SPACING_NODE_NODE

/-- `DOUBLE_EQ_EPSILON` (`10e-5`). -/
def DOUBLE_EQ_EPSILON : Float := 10e-5

private def fuzzyEquals (a b epsilon : Float) : Bool := (a - b).abs <= epsilon

private def illegalArgument (msg : String) : String := s!"{illegalArgumentExceptionClass}: {msg}"

/-- The spacing options configured relative to the base spacing. -/
def dependentSpacingOptions : Array (Property Float) := #[
  CoreOptions.SPACING_COMPONENT_COMPONENT,
  CoreOptions.SPACING_EDGE_EDGE,
  CoreOptions.SPACING_EDGE_LABEL,
  CoreOptions.SPACING_EDGE_NODE,
  CoreOptions.SPACING_LABEL_LABEL,
  CoreOptions.SPACING_LABEL_NODE,
  CoreOptions.SPACING_LABEL_PORT_HORIZONTAL,
  CoreOptions.SPACING_LABEL_PORT_VERTICAL,
  CoreOptions.SPACING_NODE_SELF_LOOP,
  CoreOptions.SPACING_PORT_PORT]

/-- `new ElkCoreSpacingsBuilder(baseSpacing)`: every option gets the factor
`default / baseDefault`. The Rust check "base spacing default must be different
from 0.0" cannot fail (the default of `SPACING_NODE_NODE` is `20`). -/
def new (baseSpacing : Float) : ElkCoreSpacingsBuilder :=
  let baseDefault := BASE_SPACING_OPTION.default.getD 0.0
  let factors := dependentSpacingOptions.foldl (init := #[{ property := BASE_SPACING_OPTION, factor := 1.0 }])
    fun acc o =>
      let factor := match o.default with
        | some d => d / baseDefault
        | none => 1.0
      acc.push { property := o, factor }
  { baseSpacing, factors }

/-- Sets the factor of one entry; out of line so that `Array.modify` hands it the unshared entry
(PLAN 7.1 items 16, 59). -/
@[noinline] private def withFactorValue (factor : Float) (f : SpacingFactor) : SpacingFactor := { f with factor }

private def findFactorIndex (b : ElkCoreSpacingsBuilder) (option : Property Float) : Option Nat :=
  b.factors.findIdx? (·.property.id == option.id)

/-- `computeFactor(value)`. -/
private def computeFactor (b : ElkCoreSpacingsBuilder) (value : Float) : Except String Float :=
  if fuzzyEquals b.baseSpacing 0.0 DOUBLE_EQ_EPSILON then .error (illegalArgument "Base spacing must not be 0.0.")
  else .ok (value / b.baseSpacing)

/-- `withFactor(spacingOption, factor)`. -/
def withFactor (b : ElkCoreSpacingsBuilder) (option : Property Float) (factor : Float) :
    Except String ElkCoreSpacingsBuilder := do
  let some idx := findFactorIndex b option
    | throw (illegalArgument s!"'{option.id}' is not a configurable spacing option.")
  if factor < 0.0 then
    throw (illegalArgument s!"The factor for '{option.id}' must not be negative ({Float.toRustDisplay factor}).")
  if option.id == BASE_SPACING_OPTION.id then
    throw (illegalArgument s!"'{option.id}' is the base spacing option not allowed to use with 'with_factor'.")
  return { b with factors := b.factors.modify idx (withFactorValue factor) }

/-- `withValue(spacingOption, value)`. -/
def withValue (b : ElkCoreSpacingsBuilder) (option : Property Float) (value : Float) :
    Except String ElkCoreSpacingsBuilder := do
  let some idx := findFactorIndex b option
    | throw (illegalArgument s!"'{option.id}' is not a configurable spacing option.")
  if value < 0.0 then
    throw (illegalArgument s!"The value for '{option.id}' must not be negative ({Float.toRustDisplay value}).")
  if option.id == BASE_SPACING_OPTION.id then
    throw (illegalArgument s!"'{option.id}' is the base spacing option not allowed to use with 'with_value'.")
  let factor ← computeFactor b value
  return { b with factors := b.factors.modify idx (withFactorValue factor) }

/-- `withOverwrite(overwrite)`. -/
def withOverwrite (b : ElkCoreSpacingsBuilder) (overwrite : Bool) : ElkCoreSpacingsBuilder := { b with overwrite }

/-- `build()`: a no-op if nothing is overwritten and the base equals the default. -/
def build (b : ElkCoreSpacingsBuilder) : SpacingConfigurator :=
  let baseDefault := BASE_SPACING_OPTION.default.getD 0.0
  { baseSpacing := b.baseSpacing, overwrite := b.overwrite, factors := b.factors,
    noOp := !b.overwrite && fuzzyEquals b.baseSpacing baseDefault DOUBLE_EQ_EPSILON }

/-- `apply(element)`. -/
def apply (b : ElkCoreSpacingsBuilder) (el : ElementId) : ElkM Unit := b.build.apply el

/-- `toVisitor()`. -/
def toVisitor (b : ElkCoreSpacingsBuilder) : GraphElementVisitor := b.build.toVisitor

end ElkCoreSpacingsBuilder

namespace ElkSpacings

/-- `ElkSpacings.withBaseValue(baseSpacing)`. -/
def withBaseValue (baseSpacing : Float) : ElkCoreSpacingsBuilder := ElkCoreSpacingsBuilder.new baseSpacing

end ElkSpacings

end Elk.Core.Util
