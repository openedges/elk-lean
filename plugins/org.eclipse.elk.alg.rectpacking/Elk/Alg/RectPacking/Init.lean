import Elk.Alg.RectPacking.Options.RectPackingMetaDataProvider
/-!
Registers the rectangle packing metadata (lazily, through the `LayoutMetaDataService` init hook,
after the core hook; rank 60 = the elk-rs registration order). The layout provider registration
comes with the provider port (F8b).
-/
namespace Elk.Alg.RectPacking

builtin_initialize initRectPackingMetaData : Unit ←
  Elk.Core.Data.LayoutMetaDataService.addInitHook Options.RectPackingMetaDataProvider.register (rank := 60)

end Elk.Alg.RectPacking
