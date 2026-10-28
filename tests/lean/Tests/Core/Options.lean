import Tests.Framework
import Elk.Core.Options
/-! Test suites for `org.eclipse.elk.core.options`. -/
namespace Tests.Core.Options

open Tests Elk Elk.Graph Elk.Core.Math Elk.Core.Options Elk.Core.Util

/-- Constructor counts, ordinals and Java names of every enum. -/
def enums : Suite := suite "core.options.enums" do
  checkEq "Alignment count" (ElkEnum.count (α := Alignment)) 6
  checkEq "ContentAlignment count" (ElkEnum.count (α := ContentAlignment)) 6
  checkEq "Direction count" (ElkEnum.count (α := Direction)) 5
  checkEq "EdgeCoords count" (ElkEnum.count (α := EdgeCoords)) 4
  checkEq "EdgeLabelPlacement count" (ElkEnum.count (α := EdgeLabelPlacement)) 3
  checkEq "EdgeRouting count" (ElkEnum.count (α := EdgeRouting)) 4
  checkEq "EdgeType count" (ElkEnum.count (α := EdgeType)) 6
  checkEq "HierarchyHandling count" (ElkEnum.count (α := HierarchyHandling)) 3
  checkEq "LabelSide count" (ElkEnum.count (α := LabelSide)) 4
  checkEq "NodeLabelPlacement count" (ElkEnum.count (α := NodeLabelPlacement)) 9
  checkEq "PackingMode count" (ElkEnum.count (α := PackingMode)) 4
  checkEq "PortAlignment count" (ElkEnum.count (α := PortAlignment)) 5
  checkEq "PortConstraints count" (ElkEnum.count (α := PortConstraints)) 6
  checkEq "PortLabelPlacement count" (ElkEnum.count (α := PortLabelPlacement)) 6
  checkEq "PortSide count" (ElkEnum.count (α := PortSide)) 5
  checkEq "ShapeCoords count" (ElkEnum.count (α := ShapeCoords)) 3
  checkEq "SizeConstraint count" (ElkEnum.count (α := SizeConstraint)) 4
  checkEq "SizeOptions count" (ElkEnum.count (α := SizeOptions)) 9
  checkEq "TopdownNodeTypes count" (ElkEnum.count (α := TopdownNodeTypes)) 3
  checkEq "TopdownSizeApproximator count" (ElkEnum.count (α := TopdownSizeApproximator)) 4
  checkEq "Direction.right ordinal" (ElkEnum.ordinal Direction.right) 1
  checkEq "PortSide.west ordinal" (ElkEnum.ordinal PortSide.west) 4
  checkEq "PortAlignment.end javaName" (ElkEnum.javaName PortAlignment.«end») "END"
  checkEq "ContentAlignment.hCenter javaName" (ElkEnum.javaName ContentAlignment.hCenter) "H_CENTER"
  checkEq "NodeLabelPlacement.hPriority javaName" (ElkEnum.javaName NodeLabelPlacement.hPriority) "H_PRIORITY"
  checkEq "PortLabelPlacement.nextToPortIfPossible javaName"
    (ElkEnum.javaName PortLabelPlacement.nextToPortIfPossible) "NEXT_TO_PORT_IF_POSSIBLE"
  checkEq "SizeOptions.minimumSizeAccountsForPadding javaName"
    (ElkEnum.javaName SizeOptions.minimumSizeAccountsForPadding) "MINIMUM_SIZE_ACCOUNTS_FOR_PADDING"
  checkEq "TopdownSizeApproximator.fixedIntegerRatioBoxes javaName"
    (ElkEnum.javaName TopdownSizeApproximator.fixedIntegerRatioBoxes) "FIXED_INTEGER_RATIO_BOXES"
  check "HierarchyHandling.ofJavaName?"
    ((ElkEnum.ofJavaName? "SEPARATE_CHILDREN" : Option HierarchyHandling) == some .separateChildren)
  check "EdgeType.none is ordinal 0" (ElkEnum.ordinal EdgeType.none == 0)

def helpers : Suite := suite "core.options.helpers" do
  check "Direction.isHorizontal" (Direction.left.isHorizontal && Direction.right.isHorizontal && !Direction.up.isHorizontal)
  check "Direction.isVertical" (Direction.up.isVertical && !Direction.undefined.isVertical)
  check "Direction.opposite" (Direction.up.opposite == .down && Direction.left.opposite == .right
    && Direction.undefined.opposite == .undefined)
  check "PortSide.opposed" (PortSide.north.opposed == .south && PortSide.east.opposed == .west)
  check "PortSide.right/left" (PortSide.north.right == .east && PortSide.north.left == .west
    && PortSide.west.right == .north)
  check "PortSide.areAdjacent" (PortSide.north.areAdjacent .east && !PortSide.north.areAdjacent .south
    && !PortSide.undefined.areAdjacent .undefined)
  check "PortSide.fromDirection" (PortSide.fromDirection .up == .north && PortSide.fromDirection .left == .west
    && PortSide.fromDirection .undefined == .undefined)
  check "PortSide.isVertical/isHorizontal" (PortSide.north.isVertical && PortSide.east.isHorizontal
    && !PortSide.east.isVertical)
  check "PortConstraints.isSideFixed" (!PortConstraints.free.isSideFixed && !PortConstraints.undefined.isSideFixed
    && PortConstraints.fixedSide.isSideFixed)
  check "PortConstraints.isOrderFixed" (PortConstraints.fixedOrder.isOrderFixed && PortConstraints.fixedPos.isOrderFixed
    && !PortConstraints.fixedSide.isOrderFixed)
  check "PortConstraints.isRatioFixed/isPosFixed" (PortConstraints.fixedRatio.isRatioFixed
    && PortConstraints.fixedPos.isPosFixed && !PortConstraints.fixedRatio.isPosFixed)
  check "EdgeLabelPlacement.isEndLabelPlacement" (EdgeLabelPlacement.head.isEndLabelPlacement
    && !EdgeLabelPlacement.center.isEndLabelPlacement)
  check "LabelSide.opposite" (LabelSide.above.opposite == .below && LabelSide.inline.opposite == .inline)
  checkEq "LabelSide.LABEL_SIDE id" LabelSide.LABEL_SIDE.id "org.eclipse.elk.labelSide"
  check "LabelSide.LABEL_SIDE default" (LabelSide.LABEL_SIDE.default == some .unknown)

def enumSets : Suite := suite "core.options.enumsets" do
  check "SIDES_NONE empty" PortSide.SIDES_NONE.isEmpty
  checkEq "SIDES_NORTH_EAST_SOUTH_WEST size" PortSide.SIDES_NORTH_EAST_SOUTH_WEST.size 4
  check "SIDES_NORTH_SOUTH contents" (PortSide.SIDES_NORTH_SOUTH.contains .north
    && PortSide.SIDES_NORTH_SOUTH.contains .south && !PortSide.SIDES_NORTH_SOUTH.contains .east)
  check "SIDES_EAST_SOUTH_WEST excludes north" (!PortSide.SIDES_EAST_SOUTH_WEST.contains .north)
  check "SizeConstraint.fixed empty" SizeConstraint.fixed.isEmpty
  checkEq "SizeConstraint.free size" SizeConstraint.free.size 4
  check "SizeConstraint.minimumSizeWithPorts"
    (SizeConstraint.minimumSizeWithPorts.contains .ports && SizeConstraint.minimumSizeWithPorts.contains .minimumSize
      && SizeConstraint.minimumSizeWithPorts.size == 2)
  checkEq "SizeConstraint.minimumSizeSet size" SizeConstraint.minimumSizeSet.size 1
  check "ContentAlignment.topLeft" (ContentAlignment.topLeft.contains .vTop && ContentAlignment.topLeft.contains .hLeft
    && ContentAlignment.topLeft.size == 2)
  check "ContentAlignment.centerCenter" (ContentAlignment.centerCenter.contains .vCenter
    && ContentAlignment.centerCenter.contains .hCenter)
  check "NodeLabelPlacement.fixed empty" NodeLabelPlacement.fixed.isEmpty
  check "NodeLabelPlacement.insideTopCenter"
    (NodeLabelPlacement.insideTopCenter.contains .inside && NodeLabelPlacement.insideTopCenter.contains .vTop
      && NodeLabelPlacement.insideTopCenter.contains .hCenter && NodeLabelPlacement.insideTopCenter.size == 3)
  check "NodeLabelPlacement.outsideBottomRight"
    (NodeLabelPlacement.outsideBottomRight.contains .outside && NodeLabelPlacement.outsideBottomRight.contains .vBottom
      && NodeLabelPlacement.outsideBottomRight.contains .hRight)
  check "NodeLabelPlacement.isValid" (NodeLabelPlacement.isValid NodeLabelPlacement.insideCenter
    && !NodeLabelPlacement.isValid (EnumSet.of #[.inside, .outside])
    && !NodeLabelPlacement.isValid (EnumSet.of #[.hLeft, .hRight]))
  check "PortLabelPlacement.isFixed" (PortLabelPlacement.isFixed PortLabelPlacement.fixed
    && !PortLabelPlacement.isFixed PortLabelPlacement.outsideSet)
  check "PortLabelPlacement.isValid" (PortLabelPlacement.isValid PortLabelPlacement.insideSet
    && !PortLabelPlacement.isValid (EnumSet.of #[.inside, .outside])
    && !PortLabelPlacement.isValid (EnumSet.of #[.alwaysSameSide, .spaceEfficient]))
  checkEq "EnumSet javaString" (toString SizeConstraint.minimumSizeWithPorts) "[PORTS, MINIMUM_SIZE]"
  check "SizeOptions.valueOf" (SizeOptions.valueOf 4 == some .portsOverhang && (SizeOptions.valueOf 9).isNone)

def coreOptions : Suite := suite "core.options.coreoptions" do
  checkEq "SPACING_NODE_NODE id" CoreOptions.SPACING_NODE_NODE.id "org.eclipse.elk.spacing.nodeNode"
  checkFloat "SPACING_NODE_NODE default" (CoreOptions.SPACING_NODE_NODE.default.getD 0.0) 20.0
  check "PADDING default" (CoreOptions.PADDING.default == some (ElkPadding.ofAny 12))
  check "NODE_LABELS_PADDING default" (CoreOptions.NODE_LABELS_PADDING.default == some (ElkPadding.ofAny 5))
  checkEq "DIRECTION id" CoreOptions.DIRECTION.id "org.eclipse.elk.direction"
  check "DIRECTION default" (CoreOptions.DIRECTION.default == some Direction.undefined)
  check "ALGORITHM no default" CoreOptions.ALGORITHM.default.isNone
  checkEq "RESOLVED_ALGORITHM id" CoreOptions.RESOLVED_ALGORITHM.id "org.eclipse.elk.resolvedAlgorithm"
  check "CONTENT_ALIGNMENT default" (CoreOptions.CONTENT_ALIGNMENT.default == some ContentAlignment.topLeft)
  check "NODE_SIZE_OPTIONS default" (CoreOptions.NODE_SIZE_OPTIONS.default == some (EnumSet.of #[SizeOptions.defaultMinimumSize]))
  check "NODE_SIZE_CONSTRAINTS default" (CoreOptions.NODE_SIZE_CONSTRAINTS.default == some SizeConstraint.fixed)
  check "PORT_LABELS_PLACEMENT default" (CoreOptions.PORT_LABELS_PLACEMENT.default == some PortLabelPlacement.outsideSet)
  check "PORT_LABELS_TREAT_AS_GROUP default" (CoreOptions.PORT_LABELS_TREAT_AS_GROUP.default == some true)
  check "ANIMATE default" (CoreOptions.ANIMATE.default == some true)
  check "VALIDATE_OPTIONS default" (CoreOptions.VALIDATE_OPTIONS.default == some true)
  check "MAX_ANIM_TIME default" (CoreOptions.MAX_ANIM_TIME.default == some 4000)
  check "TOPDOWN_SIZE_CATEGORIES default" (CoreOptions.TOPDOWN_SIZE_CATEGORIES.default == some 3)
  checkFloat "TOPDOWN_HIERARCHICAL_NODE_ASPECT_RATIO default"
    (CoreOptions.TOPDOWN_HIERARCHICAL_NODE_ASPECT_RATIO.default.getD 0.0) 1.414
  check "PRIORITY no default" CoreOptions.PRIORITY.default.isNone
  checkEq "SPACING_INDIVIDUAL id" CoreOptions.SPACING_INDIVIDUAL.id "org.eclipse.elk.spacing.individual"
  checkEq "LABEL_MANAGER id" CoreOptions.LABEL_MANAGER.id "org.eclipse.elk.labelManager"
  checkEq "BOX_PACKING_MODE id" CoreOptions.BOX_PACKING_MODE.id "org.eclipse.elk.box.packingMode"
  checkEq "Box ALGORITHM_ID" BoxLayouterOptions.ALGORITHM_ID "org.eclipse.elk.box"
  checkEq "Fixed ALGORITHM_ID" FixedLayouterOptions.ALGORITHM_ID "org.eclipse.elk.fixed"
  checkEq "Random ALGORITHM_ID" RandomLayouterOptions.ALGORITHM_ID "org.eclipse.elk.random"
  checkEq "Random RANDOM_SEED id" RandomLayouterOptions.RANDOM_SEED.id "org.eclipse.elk.randomSeed"
  check "Box PADDING has the core PADDING id" (BoxLayouterOptions.PADDING.id == CoreOptions.PADDING.id)
  -- ELK Java 0.12.0 algorithm defaults (`Core.melk`; checked with `BoxLayouterOptions.X.getDefault()`)
  check "Java: Box PADDING default 15" (BoxLayouterOptions.PADDING.default == some (ElkPadding.ofAny 15.0))
  check "Java: Box SPACING_NODE_NODE default 15" (BoxLayouterOptions.SPACING_NODE_NODE.default == some 15.0)
  check "Java: Box PRIORITY default 0" (BoxLayouterOptions.PRIORITY.default == some 0)
  check "Java: Box ASPECT_RATIO default 1.3f" (BoxLayouterOptions.ASPECT_RATIO.default == some 1.2999999523162842)
  check "Java: Fixed PADDING default 15" (FixedLayouterOptions.PADDING.default == some (ElkPadding.ofAny 15.0))
  check "Box BOX_PACKING_MODE default" (BoxLayouterOptions.BOX_PACKING_MODE.default == some PackingMode.simple)

def propertyMaps : Suite := suite "core.options.properties" do
  let props : PropertyMap := ({} : PropertyMap).set CoreOptions.DIRECTION Direction.down
  check "set/get DIRECTION" (props.get CoreOptions.DIRECTION == some .down)
  check "default PADDING" (props.get CoreOptions.PADDING == some (ElkPadding.ofAny 12))
  let sp : IndividualSpacings := {}
  let props := props.set CoreOptions.SPACING_INDIVIDUAL sp
  check "SPACING_INDIVIDUAL roundtrip" ((props.get CoreOptions.SPACING_INDIVIDUAL).isSome)
  let props := props.set CoreOptions.NODE_LABELS_PLACEMENT NodeLabelPlacement.insideTopLeft
  check "EnumSet roundtrip" (props.get CoreOptions.NODE_LABELS_PLACEMENT == some NodeLabelPlacement.insideTopLeft)

def topdown : Suite := suite "core.options.topdown" do
  -- parent with 3 leaf children and one child with a child
  let (g, root) := ElkGraphUtil.createGraph
  let (g, a) := g.createNode (some root)
  let (g, b) := g.createNode (some root)
  let (g, c) := g.createNode (some root)
  let (g, _d) := g.createNode (some a)
  checkEq "getGraphSize root (hierarchical weight 4)"
    (TopdownSizeApproximatorUtil.getGraphSize g root) 6
  checkEq "getGraphSize leaf" (TopdownSizeApproximatorUtil.getGraphSize g b) 0
  let v := TopdownSizeApproximator.countChildrenSize g root
  checkFloat "countChildren x" v.x (150.0 * Float.sqrt 3.0)
  checkFloat "countChildren y" v.y (150.0 * Float.sqrt 3.0 / 1.414)
  checkFloat "multiplier of root without parent" (TopdownSizeApproximatorUtil.getSizeCategoryMultiplier g root) 1.0
  check "multiplier of leaf is power of two"
    (let m := TopdownSizeApproximatorUtil.getSizeCategoryMultiplier g c
     m == 1.0 || m == 2.0 || m == 4.0)
  check "fixedIntegerRatioBoxes defined" ((TopdownSizeApproximator.getSize .fixedIntegerRatioBoxes g c).isSome)
  check "lookaheadLayout needs layout engine" ((TopdownSizeApproximator.getSize .lookaheadLayout g c).isNone)

def suites : Array Tests.Suite := #[enums, helpers, enumSets, coreOptions, propertyMaps, topdown]

end Tests.Core.Options
