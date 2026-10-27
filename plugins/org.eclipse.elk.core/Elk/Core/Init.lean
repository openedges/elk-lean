import Elk.Core.Data
import Elk.Core.Options
/-! Core metadata initialisation (`LayoutMetaDataService.getInstance()` lazy init):
registers the core algorithms (fixed, random, box, layered placeholder) and the
`CoreOptions`/`BoxLayouterOptions`/`LabelManagementOptions` providers through
`LayoutMetaDataService.setInitHook`. Owned by the metadata registration task. -/
