import Elk.Core.Exceptions
import Elk.Core.Util.ElkSpacings
import Elk.Alg.Layered.Options.LayeredOptions
/-!
# `org.eclipse.elk.alg.layered.options.LayeredSpacings`

Port of `layered_spacings.rs` (elk-rs) and `LayeredSpacings.java`: configures the layered
spacing options relative to a base spacing value
(`LayeredSpacings.withBaseValue(base).withFactor(...).apply(graph)`).

Design decisions:
* The builder is a value. The `with*` methods that throw `IllegalArgumentException` in Java (and
  panic in Rust) return `Except String` carrying `java.lang.IllegalArgumentException: <message>`,
  exactly like `Elk.Core.Util.ElkCoreSpacingsBuilder`. The constructor check "base spacing
  default value must be different from 0.0" cannot fail (`SPACING_NODE_NODE` defaults to `20`)
  and is not ported.
* `SpacingFactor` and `SpacingConfigurator` are the core types of `Elk.Core.Util.ElkSpacings`
  (the Rust `SpacingConfigurator` of this file has the same fields and semantics).
* `apply(graph)` on an `LGraph` becomes `applyToProperties` on the graph's `PropertyMap` (the
  layered graph model applies it to its own property map).
-/
namespace Elk.Alg.Layered.Options

open Elk Elk.Graph Elk.Core Elk.Core.Util

/-- `LayeredSpacings.LayeredSpacingsBuilder`. -/
structure LayeredSpacingsBuilder where
  baseSpacing : Float
  overwrite : Bool := false
  factors : Array SpacingFactor

namespace LayeredSpacingsBuilder

/-- `BASE_SPACING_OPTION` (`LayeredOptions.SPACING_NODE_NODE`). -/
def BASE_SPACING_OPTION : Property Float := LayeredOptions.SPACING_NODE_NODE

/-- `DOUBLE_EQ_EPSILON` (`10e-5`). -/
def DOUBLE_EQ_EPSILON : Float := 10e-5

private def fuzzyEquals (a b epsilon : Float) : Bool := (a - b).abs <= epsilon

private def illegalArgument (msg : String) : String := s!"{illegalArgumentExceptionClass}: {msg}"

/-- `dependent_spacing_options`: the spacing options configured relative to the base spacing,
in Rust order. -/
def dependentSpacingOptions : Array (Property Float) := #[
  LayeredOptions.SPACING_COMPONENT_COMPONENT,
  LayeredOptions.SPACING_EDGE_EDGE,
  LayeredOptions.SPACING_EDGE_LABEL,
  LayeredOptions.SPACING_EDGE_NODE,
  LayeredOptions.SPACING_LABEL_LABEL,
  LayeredOptions.SPACING_LABEL_NODE,
  LayeredOptions.SPACING_LABEL_PORT_HORIZONTAL,
  LayeredOptions.SPACING_LABEL_PORT_VERTICAL,
  LayeredOptions.SPACING_NODE_SELF_LOOP,
  LayeredOptions.SPACING_PORT_PORT,
  LayeredOptions.SPACING_EDGE_EDGE_BETWEEN_LAYERS,
  LayeredOptions.SPACING_EDGE_NODE_BETWEEN_LAYERS,
  LayeredOptions.SPACING_NODE_NODE_BETWEEN_LAYERS]

/-- `new LayeredSpacingsBuilder(baseSpacing)`: the base option gets factor `1`, every dependent
option the factor `default / baseDefault` (`1` if it has no default). -/
def new (baseSpacing : Float) : LayeredSpacingsBuilder :=
  let baseDefault := BASE_SPACING_OPTION.default.getD 0.0
  let factors := dependentSpacingOptions.foldl
    (init := #[{ property := BASE_SPACING_OPTION, factor := 1.0 }])
    fun acc o =>
      let factor := match o.default with
        | some d => d / baseDefault
        | none => 1.0
      acc.push { property := o, factor }
  { baseSpacing, factors }

private def findFactorIndex (b : LayeredSpacingsBuilder) (option : Property Float) : Option Nat :=
  b.factors.findIdx? (·.property.id == option.id)

/-- `computeFactor(value)`: `value / baseSpacing`; fails for a zero base spacing. -/
private def computeFactor (b : LayeredSpacingsBuilder) (value : Float) : Except String Float :=
  if fuzzyEquals b.baseSpacing 0.0 DOUBLE_EQ_EPSILON then
    .error (illegalArgument "Base spacing must not be 0.0.")
  else .ok (value / b.baseSpacing)

/-- `factors()`: the configured factors (base option first). -/
def factorOf? (b : LayeredSpacingsBuilder) (option : Property Float) : Option Float :=
  (b.factors.find? (·.property.id == option.id)).map (·.factor)

/-- `withFactor(spacingOption, factor)`. -/
def withFactor (b : LayeredSpacingsBuilder) (option : Property Float) (factor : Float) :
    Except String LayeredSpacingsBuilder := do
  let some idx := findFactorIndex b option
    | throw (illegalArgument s!"'{option.id}' is not a configurable spacing option.")
  if factor < 0.0 then
    throw (illegalArgument
      s!"The factor for '{option.id}' must not be negative ({Float.toRustDisplay factor}).")
  if option.id == BASE_SPACING_OPTION.id then
    throw (illegalArgument
      s!"'{option.id}' is the base spacing option not allowed to use with 'with_factor'.")
  return { b with factors := b.factors.modify idx fun f => { f with factor } }

/-- `withValue(spacingOption, value)`: sets the factor to `value / baseSpacing`. -/
def withValue (b : LayeredSpacingsBuilder) (option : Property Float) (value : Float) :
    Except String LayeredSpacingsBuilder := do
  let some idx := findFactorIndex b option
    | throw (illegalArgument s!"'{option.id}' is not a configurable spacing option.")
  if value < 0.0 then
    throw (illegalArgument
      s!"The value for '{option.id}' must not be negative ({Float.toRustDisplay value}).")
  if option.id == BASE_SPACING_OPTION.id then
    throw (illegalArgument
      s!"'{option.id}' is the base spacing option not allowed to use with 'with_value'.")
  let factor ← computeFactor b value
  return { b with factors := b.factors.modify idx fun f => { f with factor } }

/-- `withOverwrite(overwrite)`. -/
def withOverwrite (b : LayeredSpacingsBuilder) (overwrite : Bool) : LayeredSpacingsBuilder :=
  { b with overwrite }

/-- `build()`: a no-op configurator if nothing is overwritten and the base spacing equals the
default of `SPACING_NODE_NODE`. -/
def build (b : LayeredSpacingsBuilder) : SpacingConfigurator :=
  let baseDefault := BASE_SPACING_OPTION.default.getD 0.0
  { baseSpacing := b.baseSpacing, overwrite := b.overwrite, factors := b.factors,
    noOp := !b.overwrite && fuzzyEquals b.baseSpacing baseDefault DOUBLE_EQ_EPSILON }

/-- `applyToProperties(props)` (and `apply(graph)` on the graph's property map): sets
`factor * baseSpacing` for every configured option that is not already set (or for all of them
with `overwrite`). -/
def applyToProperties (b : LayeredSpacingsBuilder) (props : PropertyMap) : PropertyMap :=
  b.build.applyToProperties props

end LayeredSpacingsBuilder

namespace LayeredSpacings

/-- `LayeredSpacings.withBaseValue(baseSpacing)`. -/
def withBaseValue (baseSpacing : Float) : LayeredSpacingsBuilder :=
  LayeredSpacingsBuilder.new baseSpacing

end LayeredSpacings

end Elk.Alg.Layered.Options
