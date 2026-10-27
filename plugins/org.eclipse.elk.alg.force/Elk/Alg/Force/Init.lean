import Elk.Core.Data
import Elk.Core.LayoutProvider
import Elk.Alg.Force.Options.ForceMetaDataProvider
import Elk.Alg.Force.Options.StressMetaDataProvider
import Elk.Alg.Force.ForceLayoutProvider
import Elk.Alg.Force.Stress.StressLayoutProvider
/-!
# Registration of the force and stress algorithms

At module initialisation this registers

* the layout providers `org.eclipse.elk.force` and `org.eclipse.elk.stress` in the provider registry
  (`LayoutProvider.register`), and
* the metadata providers (`ForceMetaDataProvider`, then `StressMetaDataProvider`) as init hooks of the
  lazily initialised `LayoutMetaDataService` (they run after the core hook, in link order).

elk-rs registers its nine algorithm providers in the order layered, disco, force, mrtree, radial,
rectpacking, spore, stress, vertiflex. Both hooks of this plugin run back to back, so the stress options
and algorithm are listed right after the force ones instead of after the spore entries.
-/
namespace Elk.Alg.Force

open Elk.Core Elk.Core.Data Elk.Alg.Force.Options

builtin_initialize initForceMetaData : Unit ←
  LayoutMetaDataService.addInitHook ForceMetaDataProvider.register

builtin_initialize initStressMetaData : Unit ←
  LayoutMetaDataService.addInitHook StressMetaDataProvider.register

builtin_initialize registerForceLayoutProvider : Unit ←
  LayoutProvider.register ForceOptions.ALGORITHM_ID (fun _ => ForceLayoutProvider.provider)

builtin_initialize registerStressLayoutProvider : Unit ←
  LayoutProvider.register StressOptions.ALGORITHM_ID (fun _ => Stress.StressLayoutProvider.provider)

end Elk.Alg.Force
