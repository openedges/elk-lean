import Elk.Core.Data
import Elk.Alg.MrTree.Options.MrTreeMetaDataProvider
/-!
# Registration of the tree layout metadata

At module initialisation this registers `MrTreeMetaDataProvider` as an init hook of the lazily
initialised `LayoutMetaDataService` with rank 40: elk-rs registers its algorithm providers in the
order layered, disco, force, mrtree, radial, rectpacking, spore, stress, vertiflex, so mrtree runs
after force (30) and before spore (70). The layout provider itself is registered with the tree layout
driver (`TreeLayoutProvider`), which is ported separately.
-/
namespace Elk.Alg.MrTree

builtin_initialize initMrTreeMetaData : Unit ←
  Elk.Core.Data.LayoutMetaDataService.addInitHook Options.MrTreeMetaDataProvider.register (rank := 40)

end Elk.Alg.MrTree
