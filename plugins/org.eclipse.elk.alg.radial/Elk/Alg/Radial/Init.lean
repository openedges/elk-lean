import Elk.Alg.Radial.Options
import Elk.Alg.Radial.RadialLayoutProvider
/-! Registers the radial metadata (lazily, through the `LayoutMetaDataService` init hook, after
the core hook) and the layout provider at module initialisation. -/
namespace Elk.Alg.Radial

builtin_initialize initRadialMetaData : Unit ←
  Elk.Core.Data.LayoutMetaDataService.addInitHook Options.RadialMetaDataProvider.register (rank := 50)

builtin_initialize registerRadialLayoutProvider : Unit ←
  Elk.Core.LayoutProvider.register Options.RadialOptions.ALGORITHM_ID
    (fun _ => RadialLayoutProvider.provider)

end Elk.Alg.Radial
