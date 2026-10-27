import Elk.Core.Data
import Elk.Core.LayoutProvider
import Elk.Alg.MrTree.Options.MrTreeMetaDataProvider
import Elk.Alg.MrTree.TreeLayoutProvider
/-!
# Registration of the tree layout metadata and provider

At module initialisation this registers `MrTreeMetaDataProvider` as an init hook of the lazily
initialised `LayoutMetaDataService` with rank 40: elk-rs registers its algorithm providers in the
order layered, disco, force, mrtree, radial, rectpacking, spore, stress, vertiflex, so mrtree runs
after force (30) and before spore (70). It also registers the layout provider
(`TreeLayoutProvider`) for `org.eclipse.elk.mrtree`.
-/
namespace Elk.Alg.MrTree

builtin_initialize initMrTreeMetaData : Unit ←
  Elk.Core.Data.LayoutMetaDataService.addInitHook Options.MrTreeMetaDataProvider.register (rank := 40)

builtin_initialize registerMrTreeLayoutProvider : Unit ←
  Elk.Core.LayoutProvider.register Options.MrTreeOptions.ALGORITHM_ID
    (fun _ => TreeLayoutProvider.provider)

end Elk.Alg.MrTree
