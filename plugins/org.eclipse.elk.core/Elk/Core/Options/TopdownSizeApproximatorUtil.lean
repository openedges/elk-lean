import Elk.Graph.Model
import Elk.Core.Options.CoreOptions
/-!
# `org.eclipse.elk.core.options.TopdownSizeApproximatorUtil` and `TopdownSizeApproximator.getSize`

Pure ports operating on the `ElkGraph` arena (`g`, `node`).

`TopdownSizeApproximator.getSize` lives here (not in `TopdownSizeApproximator.lean`)
because it reads `CoreOptions`, which in turn needs the enum.

TODO(TopdownSizeApproximatorUtil.lean): `LOOKAHEAD_LAYOUT` and `LAYOUT_NEXT_LEVEL` run a
layout provider (clone the hierarchy / lay out the next level) and therefore need the
layout engine and algorithm provider pool (`Elk.Core.Data`, `Elk.Core.Util.ElkUtil`);
`getSize` returns `none` for them until the engine is ported.
-/
namespace Elk.Core.Options

open Elk Elk.Graph Elk.Core.Math

namespace TopdownSizeApproximatorUtil

/-- `TopdownSizeApproximatorUtil.getGraphSize(originalGraph)`: number of children, where
children that are hierarchical themselves count with
`TOPDOWN_SIZE_CATEGORIES_HIERARCHICAL_NODE_WEIGHT`. -/
def getGraphSize (g : ElkGraph) (node : NodeId) : Int := Id.run do
  let n := g.node node
  let weight : Int := (n.props.get CoreOptions.TOPDOWN_SIZE_CATEGORIES_HIERARCHICAL_NODE_WEIGHT).getD 4
  let mut sum : Int := 0
  for child in n.children do
    if (g.node child).children.isEmpty then
      sum := sum + 1
    else
      sum := sum + weight
  return sum

/-- `TopdownSizeApproximatorUtil.getSizeCategoryMultiplier(originalGraph)`. -/
def getSizeCategoryMultiplier (g : ElkGraph) (node : NodeId) : Float := Id.run do
  let n := g.node node
  let thisGraphSize := getGraphSize g node
  let categories : Int := (n.props.get CoreOptions.TOPDOWN_SIZE_CATEGORIES).getD 3
  match n.parent with
  | none => return 1.0
  | some parent =>
    -- the minimum found size is computed but unused in the Java/Rust code
    let mut sizeMaxFound : Int := Int.negSucc 2147483647
    for child in (g.node parent).children do
      let size := getGraphSize g child
      if size > sizeMaxFound then sizeMaxFound := size
    let sizeMin : Float := 1.0
    let mut sizeMax : Float := Float.pow 4.0 (Float.ofInt categories)
    if Float.ofInt sizeMaxFound > sizeMax then
      sizeMax := Float.ofInt sizeMaxFound
    let x := (Float.log sizeMax - Float.log sizeMin) / Float.ofInt categories
    let factor := Float.exp x
    let mut cutoff := sizeMin * factor
    for i in [0:categories.toNat] do
      if Float.ofInt thisGraphSize < cutoff then
        return Float.pow 2.0 i.toFloat
      cutoff := cutoff * factor
    return Float.pow 2.0 (Float.ofInt (categories - 1))

end TopdownSizeApproximatorUtil

namespace TopdownSizeApproximator

/-- `COUNT_CHILDREN.getSize(node)`: width scaled by the square root of the child count. -/
def countChildrenSize (g : ElkGraph) (node : NodeId) : KVector :=
  let n := g.node node
  let childCount := n.children.size.toFloat
  let width := (n.props.get CoreOptions.TOPDOWN_HIERARCHICAL_NODE_WIDTH).getD 150.0
  let aspectRatio := (n.props.get CoreOptions.TOPDOWN_HIERARCHICAL_NODE_ASPECT_RATIO).getD 1.414
  let size := width * Float.sqrt childCount
  KVector.mk' size (size / aspectRatio)

/-- `FIXED_INTEGER_RATIO_BOXES.getSize(node)`. -/
def fixedIntegerRatioBoxesSize (g : ElkGraph) (node : NodeId) : KVector :=
  let n := g.node node
  let baseWidth := (n.props.get CoreOptions.TOPDOWN_HIERARCHICAL_NODE_WIDTH).getD 150.0
  let aspectRatio := (n.props.get CoreOptions.TOPDOWN_HIERARCHICAL_NODE_ASPECT_RATIO).getD 1.414
  let baseHeight := baseWidth / aspectRatio
  let multiplier := TopdownSizeApproximatorUtil.getSizeCategoryMultiplier g node
  let padding : ElkPadding := (n.props.get CoreOptions.PADDING).getD {}
  let nodeNodeSpacing : Float :=
    match n.parent with
    | some parent => ((g.node parent).props.get CoreOptions.SPACING_NODE_NODE).getD 20.0
    | none => CoreOptions.SPACING_NODE_NODE.default.getD 20.0
  let result := (KVector.mk' baseWidth baseHeight).scale multiplier
  result.addValues (-(padding.left + padding.right) - nodeNodeSpacing)
    (-(padding.top + padding.bottom) - nodeNodeSpacing)

/-- `ITopdownSizeApproximator.getSize(node)`. Returns `none` for `lookaheadLayout` and
`layoutNextLevel`, which need a layout provider (see module TODO). -/
def getSize (a : TopdownSizeApproximator) (g : ElkGraph) (node : NodeId) : Option KVector :=
  match a with
  | .countChildren => some (countChildrenSize g node)
  | .fixedIntegerRatioBoxes => some (fixedIntegerRatioBoxesSize g node)
  | .lookaheadLayout => none
  | .layoutNextLevel => none

end TopdownSizeApproximator

end Elk.Core.Options
