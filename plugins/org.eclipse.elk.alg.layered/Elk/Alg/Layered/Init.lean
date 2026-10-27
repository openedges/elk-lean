import Elk.Alg.Layered.Options
/-! Registers the layered metadata provider in the lazy initialisation of `LayoutMetaDataService`
(after the core hook). The layout provider itself is registered by `Elk.Alg.Layered.LayeredLayoutProvider`. -/
namespace Elk.Alg.Layered

builtin_initialize initLayeredMetaData : Unit ←
  Elk.Core.Data.LayoutMetaDataService.addInitHook Options.LayeredMetaDataProvider.register (rank := 10)

end Elk.Alg.Layered
