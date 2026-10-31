import Elk.Core.Data
import Elk.Alg.Common.Compaction.Options.PolyominoOptions
import Elk.Alg.Disco.Options.DisCoMetaDataProvider
/-! Registers the DisCo metadata provider in the lazy initialisation of `LayoutMetaDataService`
(after the core hook), preceded by the polyomino options (`PolyominoOptions`, which ELK Java loads
through the `ServiceLoader` entry of `org.eclipse.elk.alg.common`; elk-rs never registers them).
The layout provider itself is registered by `Elk.Alg.Disco.DisCoLayoutProvider`. -/
namespace Elk.Alg.Disco

builtin_initialize initPolyominoOptions : Unit ←
  Elk.Core.Data.LayoutMetaDataService.addInitHook
    (Elk.Core.Data.LayoutMetaDataService.registerLayoutMetaDataProvider
      Elk.Alg.Common.Compaction.Options.PolyominoOptions.metaDataProvider) (rank := 19)

builtin_initialize initDisCoMetaData : Unit ←
  Elk.Core.Data.LayoutMetaDataService.addInitHook Options.DisCoMetaDataProvider.register (rank := 20)

end Elk.Alg.Disco
