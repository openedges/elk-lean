import Elk.Core.Math.KVector
/-!
# `org.eclipse.elk.core.labels.ILabelManager`

A label manager can modify (typically shorten) labels that are too wide for a given
target width. It is attached to compound nodes or labels through the
`labels.labelManager` option (`LabelManagementOptions.LABEL_MANAGER`).
-/
namespace Elk.Core.Labels

open Elk.Core.Math

/-- `ILabelManager`: `manageLabelSize(label, targetWidth)` returns the new size of the label
or `none` if the label was not changed. The label is an opaque (`Dynamic`) graph label
handle, mirroring the `&dyn Any` argument of `ILabelManager::manage_label_size` in elk-rs. -/
structure ILabelManager where
  /-- `ILabelManager.manageLabelSize(label, targetWidth)`. -/
  manageLabelSize : Dynamic → Float → Option KVector

end Elk.Core.Labels
