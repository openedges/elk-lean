import Elk.Core.Util.FixedLayoutProvider
import Elk.Core.Util.RandomLayoutProvider
import Elk.Core.Util.BoxLayoutProvider
/-! Registers the core layout providers (fixed, random, box) at module initialisation. -/
namespace Elk.Core

open Elk.Core.Util Elk.Core.Options

builtin_initialize registerCoreProviders : Unit ← do
  LayoutProvider.register FixedLayouterOptions.ALGORITHM_ID (fun _ => FixedLayoutProvider.provider)
  LayoutProvider.register RandomLayouterOptions.ALGORITHM_ID (fun _ => RandomLayoutProvider.provider)
  LayoutProvider.register BoxLayouterOptions.ALGORITHM_ID (fun _ => BoxLayoutProvider.provider)

end Elk.Core
