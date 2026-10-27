import Elk.Graph.Monad
import Elk.Core.Options.CoreOptions
import Elk.Core.Util.GraphElementVisitor
/-!
# `org.eclipse.elk.core.data.DeprecatedLayoutOptionReplacer`

Graph element visitor replacing deprecated options by their successors:
* `PORT_LABELS_NEXT_TO_PORT_IF_POSSIBLE` → `PortLabelPlacement.NEXT_TO_PORT_IF_POSSIBLE`;
* `SizeOptions.SPACE_EFFICIENT_PORT_LABELS` → `PortLabelPlacement.SPACE_EFFICIENT`.
-/
namespace Elk.Core.Data

open Elk Elk.Graph Elk.Core.Options Elk.Core.Util

namespace DeprecatedLayoutOptionReplacer

/-- The replacement applied to one property map (`visit(element)`). -/
def replace (props : PropertyMap) : PropertyMap := Id.run do
  let mut props := props
  if props.has CoreOptions.PORT_LABELS_NEXT_TO_PORT_IF_POSSIBLE then
    let placement := ((props.get CoreOptions.PORT_LABELS_PLACEMENT).getD PortLabelPlacement.outsideSet).insert
      .nextToPortIfPossible
    props := props.set CoreOptions.PORT_LABELS_PLACEMENT placement
    props := props.remove CoreOptions.PORT_LABELS_NEXT_TO_PORT_IF_POSSIBLE
  if let some sizeOptions := props.get CoreOptions.NODE_SIZE_OPTIONS then
    if sizeOptions.contains .spaceEfficientPortLabels then
      props := props.set CoreOptions.NODE_SIZE_OPTIONS (sizeOptions.erase .spaceEfficientPortLabels)
      let placement := ((props.get CoreOptions.PORT_LABELS_PLACEMENT).getD PortLabelPlacement.outsideSet).insert
        .spaceEfficient
      props := props.set CoreOptions.PORT_LABELS_PLACEMENT placement
  return props

/-- `visit(element)`. -/
def visit (el : ElementId) : ElkM Unit := modify (·.modifyProps el replace)

/-- `new DeprecatedLayoutOptionReplacer()` as an `IGraphElementVisitor` (stateless). -/
def new : GraphElementVisitor := { visit := visit }

end DeprecatedLayoutOptionReplacer

end Elk.Core.Data
