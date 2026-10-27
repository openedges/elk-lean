import Elk.Alg.RectPacking.Options.RectPackingMetaDataProvider
import Elk.Alg.RectPacking.RectPackingLayoutProvider
/-!
Registers the rectangle packing metadata (lazily, through the `LayoutMetaDataService` init hook,
after the core hook; rank 60 = the elk-rs registration order) and the layout provider at module
initialisation.
-/
namespace Elk.Alg.RectPacking

builtin_initialize initRectPackingMetaData : Unit ←
  Elk.Core.Data.LayoutMetaDataService.addInitHook Options.RectPackingMetaDataProvider.register (rank := 60)

builtin_initialize registerRectPackingLayoutProvider : Unit ←
  Elk.Core.LayoutProvider.register Options.RectPackingOptions.ALGORITHM_ID
    (fun _ => RectPackingLayoutProvider.provider)

end Elk.Alg.RectPacking
