import Elk.Graph.Properties
import Elk.Core.Data.LayoutMetaDataService
import Elk.Core.Labels.LabelManager
/-!
# `org.eclipse.elk.core.labels.LabelManagementOptions`

The `labels.labelManager` option and its `ILayoutMetaDataProvider`
(elk-rs `impl ILayoutMetaDataProvider for LabelManagementOptions`).

Type mapping: the value of `LABEL_MANAGER` is a `Dynamic` (an `ILabelManager` in Java/Rust),
consistent with `CoreOptions.LABEL_MANAGER`.
-/
namespace Elk.Core.Labels

open Elk Elk.Graph Elk.Core.Data

namespace LabelManagementOptions

/-- `LabelManagementOptions.LABEL_MANAGER` (`org.eclipse.elk.labels.labelManager`). -/
def LABEL_MANAGER : Property Dynamic :=
  Property.mk' "org.eclipse.elk.labels.labelManager"

/-- `LabelManagementOptions.apply(registry)`: registers the (hidden) label manager option for
parents and labels. -/
def metaDataProvider : LayoutMetaDataProvider where
  apply r :=
    r.registerOption
      { id := LABEL_MANAGER.id
        type := .object
        name := "Label Manager"
        description := "The label manager responsible for a given part of the graph. A label manager can either be attached to a compound node (in which case it is responsible for all labels inside) or to specific labels. The label manager can then be called by layout algorithms to modify labels that are too wide to try and shorten them to a given target width."
        targets := EnumSet.of #[.parents, .labels]
        visibility := .hidden }

end LabelManagementOptions

end Elk.Core.Labels
