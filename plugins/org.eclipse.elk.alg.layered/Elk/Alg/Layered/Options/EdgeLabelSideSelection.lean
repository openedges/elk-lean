import Elk.Graph.Enum
/-!
# `org.eclipse.elk.alg.layered.options.EdgeLabelSideSelection`

Port of `options/edge_label_side_selection.rs` (elk-rs) and `EdgeLabelSideSelection.java`.
-/
namespace Elk.Alg.Layered.Options

/-- `org.eclipse.elk.alg.layered.options.EdgeLabelSideSelection`: Possible ways to determine whether
edge labels should be placed above or below their edge. -/
elk_enum EdgeLabelSideSelection := alwaysUp alwaysDown directionUp directionDown smartUp smartDown

namespace EdgeLabelSideSelection

/-- `EdgeLabelSideSelection.transpose()`: the same strategy with up and down swapped. -/
def transpose : EdgeLabelSideSelection → EdgeLabelSideSelection
  | .alwaysUp => .alwaysDown
  | .alwaysDown => .alwaysUp
  | .directionUp => .directionDown
  | .directionDown => .directionUp
  | .smartUp => .smartDown
  | .smartDown => .smartUp

end EdgeLabelSideSelection

end Elk.Alg.Layered.Options
