import Elk.Graph
/-!
# `org.eclipse.elk.core.data.LayoutAlgorithmData`

Metadata of a layout algorithm. The layout provider instances themselves are
kept in a separate registry (`Elk.Core.ProviderRegistry`) because providers
depend on the engine types; the metadata layer stays dependency free.
-/
namespace Elk.Core.Data

open Elk Elk.Graph

structure LayoutAlgorithmData where
  id : String
  name : String := ""
  description : String := ""
  categoryId : Option String := none
  bundleName : Option String := none
  definingBundleId : Option String := none
  previewImagePath : Option String := none
  /-- Id of the graph validator to run before layout (`validatorClass`), if any. -/
  validatorId : Option String := none
  supportedFeatures : EnumSet GraphFeature := EnumSet.empty
  /-- Known options with their algorithm specific default (registration order). -/
  knownOptions : Array (String × Option PropValue) := #[]

namespace LayoutAlgorithmData

instance : BEq LayoutAlgorithmData := ⟨fun a b => a.id == b.id⟩
instance : Hashable LayoutAlgorithmData := ⟨fun a => hash a.id⟩
instance : ToString LayoutAlgorithmData := ⟨fun a => a.id⟩
instance : Inhabited LayoutAlgorithmData := ⟨{ id := "" }⟩

/-- `addKnownOption(id, default)`: replaces an existing entry in place. -/
def addKnownOptionDefault (d : LayoutAlgorithmData) (optionId : String) (default : Option PropValue) : LayoutAlgorithmData :=
  match d.knownOptions.findIdx? (fun e => e.1 == optionId) with
  | some i => { d with knownOptions := d.knownOptions.set! i (optionId, default) }
  | none => { d with knownOptions := d.knownOptions.push (optionId, default) }

def addKnownOptionId (d : LayoutAlgorithmData) (optionId : String) : LayoutAlgorithmData :=
  d.addKnownOptionDefault optionId none

/-- `knowsOption`. -/
def knowsOption (d : LayoutAlgorithmData) (optionId : String) : Bool :=
  d.knownOptions.any (fun e => e.1 == optionId)

/-- `getKnownOptionIds()`. -/
def knownOptionIds (d : LayoutAlgorithmData) : Array String := d.knownOptions.map (·.1)

/-- `getDefaultValue(optionId)` as a raw `PropValue`. -/
def defaultValueRaw (d : LayoutAlgorithmData) (optionId : String) : Option PropValue :=
  (d.knownOptions.find? (fun e => e.1 == optionId)).bind (·.2)

/-- Typed `getDefaultValue(property)`. -/
def defaultValue {α : Type} [PropCodec α] (d : LayoutAlgorithmData) (p : Property α) : Option α :=
  (d.defaultValueRaw p.id).bind PropCodec.dec

/-- `supportsFeature`. -/
def supportsFeature (d : LayoutAlgorithmData) (f : GraphFeature) : Bool := d.supportedFeatures.contains f

def addSupportedFeature (d : LayoutAlgorithmData) (f : GraphFeature) : LayoutAlgorithmData :=
  { d with supportedFeatures := d.supportedFeatures.insert f }

end LayoutAlgorithmData

/-- `org.eclipse.elk.core.data.LayoutCategoryData`. Algorithms are referenced by id. -/
structure LayoutCategoryData where
  id : String
  name : String := ""
  description : String := ""
  layouters : Array String := #[]

namespace LayoutCategoryData
instance : BEq LayoutCategoryData := ⟨fun a b => a.id == b.id⟩
instance : ToString LayoutCategoryData := ⟨fun a => a.id⟩
instance : Inhabited LayoutCategoryData := ⟨{ id := "" }⟩
end LayoutCategoryData

end Elk.Core.Data
