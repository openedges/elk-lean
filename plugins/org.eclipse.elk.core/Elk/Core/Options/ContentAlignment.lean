import Elk.Graph.Enum
/-!
# `org.eclipse.elk.core.options.ContentAlignment`
-/
namespace Elk.Core.Options

/-- `org.eclipse.elk.core.options.ContentAlignment`. -/
elk_enum ContentAlignment := vTop vCenter vBottom hLeft hCenter hRight

namespace ContentAlignment

/-- `ContentAlignment.centerCenter()`. -/
def centerCenter : EnumSet ContentAlignment := EnumSet.of #[.vCenter, .hCenter]

/-- `ContentAlignment.topLeft()`. -/
def topLeft : EnumSet ContentAlignment := EnumSet.of #[.vTop, .hLeft]

/-- `ContentAlignment.bottomRight()`. -/
def bottomRight : EnumSet ContentAlignment := EnumSet.of #[.vBottom, .hRight]

/-- `ContentAlignment.topCenter()`. -/
def topCenter : EnumSet ContentAlignment := EnumSet.of #[.vTop, .hCenter]

end ContentAlignment

end Elk.Core.Options
