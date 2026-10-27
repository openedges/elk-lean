import Elk.Alg.Spore.Options.SporeMetaDataProvider
/-! Registers the SPOrE metadata provider in the lazy initialisation of `LayoutMetaDataService`
(after the core hook). The layout providers themselves are registered by
`Elk.Alg.Spore.OverlapRemovalLayoutProvider` and `Elk.Alg.Spore.ShrinkTreeLayoutProvider`. -/
namespace Elk.Alg.Spore

builtin_initialize initSporeMetaData : Unit ←
  Elk.Core.Data.LayoutMetaDataService.addInitHook Options.SporeMetaDataProvider.register

end Elk.Alg.Spore
