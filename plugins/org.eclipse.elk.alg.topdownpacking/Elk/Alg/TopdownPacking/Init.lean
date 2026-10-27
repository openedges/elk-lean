import Elk.Alg.TopdownPacking.Options
import Elk.Alg.TopdownPacking.TopdownpackingLayoutProvider
/-! Registers the topdown packing metadata (lazily, through the `LayoutMetaDataService` init hook,
after the core hook) and the layout provider at module initialisation. -/
namespace Elk.Alg.TopdownPacking

builtin_initialize initTopdownPackingMetaData : Unit ←
  Elk.Core.Data.LayoutMetaDataService.addInitHook Options.TopdownpackingMetaDataProvider.register

builtin_initialize registerTopdownPackingLayoutProvider : Unit ←
  Elk.Core.LayoutProvider.register Options.TopdownpackingOptions.ALGORITHM_ID
    (fun _ => TopdownpackingLayoutProvider.provider)

end Elk.Alg.TopdownPacking
