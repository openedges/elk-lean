import Elk.Core.Options.Direction
/-!
# `org.eclipse.elk.core.options.PortSide`
-/
namespace Elk.Core.Options

/-- `org.eclipse.elk.core.options.PortSide`. -/
elk_enum PortSide := undefined north east south west

namespace PortSide

/-- `PortSide.right()`: next side clockwise. -/
def right : PortSide → PortSide
  | .north => .east
  | .east => .south
  | .south => .west
  | .west => .north
  | .undefined => .undefined

/-- `PortSide.left()`: next side counter-clockwise. -/
def left : PortSide → PortSide
  | .north => .west
  | .west => .south
  | .south => .east
  | .east => .north
  | .undefined => .undefined

/-- `PortSide.opposed()`. -/
def opposed : PortSide → PortSide
  | .north => .south
  | .east => .west
  | .south => .north
  | .west => .east
  | .undefined => .undefined

/-- `PortSide.areAdjacent(other)`. -/
def areAdjacent (self other : PortSide) : Bool :=
  if self == .undefined then false else self.left == other || self.right == other

/-- `PortSide.fromDirection(direction)`. -/
def fromDirection : Direction → PortSide
  | .up => .north
  | .right => .east
  | .down => .south
  | .left => .west
  | .undefined => .undefined

/-- `PortSide.isVertical(side)`: north or south. -/
def isVertical : PortSide → Bool
  | .north | .south => true
  | _ => false

/-- `PortSide.isHorizontal(side)`: west or east. -/
def isHorizontal : PortSide → Bool
  | .west | .east => true
  | _ => false

/-- `PortSide.SIDES_NONE`. -/
def SIDES_NONE : EnumSet PortSide := EnumSet.noneOf
/-- `PortSide.SIDES_NORTH`. -/
def SIDES_NORTH : EnumSet PortSide := EnumSet.of #[.north]
/-- `PortSide.SIDES_EAST`. -/
def SIDES_EAST : EnumSet PortSide := EnumSet.of #[.east]
/-- `PortSide.SIDES_SOUTH`. -/
def SIDES_SOUTH : EnumSet PortSide := EnumSet.of #[.south]
/-- `PortSide.SIDES_WEST`. -/
def SIDES_WEST : EnumSet PortSide := EnumSet.of #[.west]
/-- `PortSide.SIDES_NORTH_SOUTH`. -/
def SIDES_NORTH_SOUTH : EnumSet PortSide := EnumSet.of #[.north, .south]
/-- `PortSide.SIDES_EAST_WEST`. -/
def SIDES_EAST_WEST : EnumSet PortSide := EnumSet.of #[.east, .west]
/-- `PortSide.SIDES_NORTH_WEST`. -/
def SIDES_NORTH_WEST : EnumSet PortSide := EnumSet.of #[.north, .west]
/-- `PortSide.SIDES_NORTH_EAST`. -/
def SIDES_NORTH_EAST : EnumSet PortSide := EnumSet.of #[.north, .east]
/-- `PortSide.SIDES_SOUTH_WEST`. -/
def SIDES_SOUTH_WEST : EnumSet PortSide := EnumSet.of #[.south, .west]
/-- `PortSide.SIDES_EAST_SOUTH`. -/
def SIDES_EAST_SOUTH : EnumSet PortSide := EnumSet.of #[.east, .south]
/-- `PortSide.SIDES_NORTH_EAST_WEST`. -/
def SIDES_NORTH_EAST_WEST : EnumSet PortSide := EnumSet.of #[.north, .east, .west]
/-- `PortSide.SIDES_EAST_SOUTH_WEST`. -/
def SIDES_EAST_SOUTH_WEST : EnumSet PortSide := EnumSet.of #[.east, .south, .west]
/-- `PortSide.SIDES_NORTH_SOUTH_WEST`. -/
def SIDES_NORTH_SOUTH_WEST : EnumSet PortSide := EnumSet.of #[.north, .south, .west]
/-- `PortSide.SIDES_NORTH_EAST_SOUTH`. -/
def SIDES_NORTH_EAST_SOUTH : EnumSet PortSide := EnumSet.of #[.north, .east, .south]
/-- `PortSide.SIDES_NORTH_EAST_SOUTH_WEST`. -/
def SIDES_NORTH_EAST_SOUTH_WEST : EnumSet PortSide := EnumSet.of #[.north, .east, .south, .west]

end PortSide

end Elk.Core.Options
