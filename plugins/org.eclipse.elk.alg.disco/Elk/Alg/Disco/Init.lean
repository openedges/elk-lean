import Elk.Core.Data
import Elk.Alg.Disco.Options.DisCoMetaDataProvider
/-! Registers the DisCo metadata provider in the lazy initialisation of `LayoutMetaDataService`
(after the core hook). The layout provider itself is registered by `Elk.Alg.Disco.DisCoLayoutProvider`. -/
namespace Elk.Alg.Disco

builtin_initialize initDisCoMetaData : Unit ←
  Elk.Core.Data.LayoutMetaDataService.addInitHook Options.DisCoMetaDataProvider.register

end Elk.Alg.Disco
