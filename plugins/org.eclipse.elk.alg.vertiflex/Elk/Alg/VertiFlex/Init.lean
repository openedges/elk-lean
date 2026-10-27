import Elk.Alg.VertiFlex.Options
import Elk.Alg.VertiFlex.VertiFlexLayoutProvider
/-! Registers the VertiFlex metadata (lazily, through the `LayoutMetaDataService` init hook,
after the core hook) and the layout provider at module initialisation. -/
namespace Elk.Alg.VertiFlex

builtin_initialize initVertiFlexMetaData : Unit ←
  Elk.Core.Data.LayoutMetaDataService.addInitHook Options.VertiFlexMetaDataProvider.register (rank := 90)

builtin_initialize registerVertiFlexLayoutProvider : Unit ←
  Elk.Core.LayoutProvider.register Options.VertiFlexOptions.ALGORITHM_ID
    (fun _ => VertiFlexLayoutProvider.provider)

end Elk.Alg.VertiFlex
