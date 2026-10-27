import Tests.Framework
import Elk.Alg.Common.Compaction
/-! Tests of `org.eclipse.elk.alg.common` (Compaction). Owned by the Compaction porting task.

Ports of elk-rs `tests/all/one_dimensional_compactor_test.rs` (all 17 tests) and the two inline
tests of `compaction/oned/scanline_constraint_calculator.rs`. -/
namespace Tests.AlgCommon.Compaction

open Tests Elk.Core.Math Elk.Core.Options Elk.Alg.Common.Compaction.OneD

/-- `EPSILON` of the Rust test. -/
private def EPSILON : Float := 0.0001
/-- `SPACING` of the Rust test. -/
private def SPACING : Float := 5.0

/-- `TestSpacingHandler`: `SPACING` in both dimensions. -/
private def testSpacingHandler : SpacingsHandler := ⟨fun _ _ _ => SPACING, fun _ _ _ => SPACING⟩

/-- Test helper `node(graph, x, y, w, h)` (state-passing). -/
private def mkNode (x y w h : Float) : StateM CGraph CNodeId :=
  modifyGet fun g => let (g, n) := CNode.create g (ElkRectangle.ofValues x y w h); (n, g)

/-- `CGroup::create` in the builder monad (the test groups never fail). -/
private def mkGroup (nodes : Array CNodeId) : StateM CGraph Unit :=
  modify fun g => match CGroup.create g nodes with
    | .ok (g, _) => g
    | .error _ => g

/-- Test helper `compacter(graph)`: quadratic constraint calculation. -/
private def compacter (g : CGraph) : OneDimensionalCompactor :=
  (OneDimensionalCompactor.new g).setConstraintAlgorithm QuadraticConstraintCalculation

private def hx (c : OneDimensionalCompactor) (n : CNodeId) : Float := (c.cGraph.cNode n).hitbox.x
private def hy (c : OneDimensionalCompactor) (n : CNodeId) : Float := (c.cGraph.cNode n).hitbox.y

private def close (name : String) (actual expected : Float) : TestM Unit :=
  checkFloat name actual expected (eps := EPSILON)

/-- Two nodes in a row (`0,0,20,20` and `30,0,20,20`). -/
private def twoInRow : CGraph × CNodeId × CNodeId :=
  let (r, g) := (do
    let a ← mkNode 0.0 0.0 20.0 20.0
    let b ← mkNode 30.0 0.0 20.0 20.0
    return (a, b) : StateM CGraph _).run CGraph.allDirections
  (g, r)

/-- Two nodes in a column (`0,0,20,20` and `0,30,20,20`). -/
private def twoInColumn : CGraph × CNodeId × CNodeId :=
  let (r, g) := (do
    let a ← mkNode 0.0 0.0 20.0 20.0
    let b ← mkNode 0.0 30.0 20.0 20.0
    return (a, b) : StateM CGraph _).run CGraph.allDirections
  (g, r)

def basicCompaction : Suite := suite "alg.common.compaction.OneDimensionalCompactor.basic" do
  -- test_left_compaction
  do
    let (g, left, right) := twoInRow
    let c ← (compacter g).changeDirection .left >>= (·.compact) >>= (·.finish)
    close "test_left_compaction left" (hx c left) 0.0
    close "test_left_compaction right" (hx c right) 20.0
  -- test_left_compaction_equal_y_coordinate (scanline constraints)
  do
    let ((top, bottom), g) := (do
      let a ← mkNode 0.0 0.0 20.0 20.0
      let b ← mkNode 30.0 20.0 20.0 20.0
      return (a, b) : StateM CGraph _).run CGraph.allDirections
    let c := (compacter g).setConstraintAlgorithm ScanlineConstraintCalculator
    let c ← c.changeDirection .left >>= (·.compact) >>= (·.finish)
    close "test_left_compaction_equal_y_coordinate top" (hx c top) 0.0
    close "test_left_compaction_equal_y_coordinate bottom" (hx c bottom) 0.0
  -- test_left_compaction_spacing_aware
  do
    let ((left, right), g) := (do
      let a ← mkNode 0.0 0.0 20.0 20.0
      let b ← mkNode 30.0 (20.0 + SPACING - 1.0) 20.0 20.0
      return (a, b) : StateM CGraph _).run CGraph.allDirections
    let c := (compacter g).setSpacingsHandler testSpacingHandler
    let c ← c.changeDirection .left >>= (·.compact) >>= (·.finish)
    close "test_left_compaction_spacing_aware left" (hx c left) 0.0
    close "test_left_compaction_spacing_aware right" (hx c right) 25.0
  -- test_left_compaction_spacing_aware_2
  do
    let ((left, right), g) := (do
      let a ← mkNode 0.0 0.0 20.0 20.0
      let b ← mkNode 30.0 (20.0 + SPACING + 1.0) 20.0 20.0
      return (a, b) : StateM CGraph _).run CGraph.allDirections
    let c := (compacter g).setSpacingsHandler testSpacingHandler
    let c ← c.changeDirection .left >>= (·.compact) >>= (·.finish)
    close "test_left_compaction_spacing_aware_2 left" (hx c left) 0.0
    close "test_left_compaction_spacing_aware_2 right" (hx c right) 0.0
  -- test_right_compaction
  do
    let (g, left, right) := twoInRow
    let c ← (compacter g).changeDirection .right >>= (·.compact) >>= (·.finish)
    close "test_right_compaction left" (hx c left) 10.0
    close "test_right_compaction right" (hx c right) 30.0
  -- test_up_compaction
  do
    let (g, upper, lower) := twoInColumn
    let c ← (compacter g).changeDirection .up >>= (·.compact) >>= (·.finish)
    close "test_up_compaction upper" (hy c upper) 0.0
    close "test_up_compaction lower" (hy c lower) 20.0
  -- test_down_compaction
  do
    let (g, upper, lower) := twoInColumn
    let c ← (compacter g).changeDirection .down >>= (·.compact) >>= (·.finish)
    close "test_down_compaction upper" (hy c upper) 10.0
    close "test_down_compaction lower" (hy c lower) 30.0

def groupCompaction : Suite := suite "alg.common.compaction.OneDimensionalCompactor.groups" do
  -- test_left_group_compaction
  do
    let ((left, ur, lr), g) := (do
      let a ← mkNode 0.0 0.0 20.0 20.0
      let b ← mkNode 40.0 5.0 20.0 20.0
      let c ← mkNode 30.0 25.0 20.0 20.0
      mkGroup #[b, c]
      return (a, b, c) : StateM CGraph _).run CGraph.allDirections
    let c ← (compacter g).changeDirection .left >>= (·.compact) >>= (·.finish)
    close "test_left_group_compaction left" (hx c left) 0.0
    close "test_left_group_compaction upper_right" (hx c ur) 20.0
    close "test_left_group_compaction lower_right" (hx c lr) 10.0
  -- test_right_group_compaction
  do
    let ((left, ur, lr), g) := (do
      let a ← mkNode 0.0 5.0 20.0 20.0
      let b ← mkNode 40.0 0.0 20.0 20.0
      let c ← mkNode 10.0 25.0 20.0 20.0
      mkGroup #[a, c]
      return (a, b, c) : StateM CGraph _).run CGraph.allDirections
    let c ← (compacter g).changeDirection .right >>= (·.compact) >>= (·.finish)
    close "test_right_group_compaction left" (hx c left) 20.0
    close "test_right_group_compaction upper_right" (hx c ur) 40.0
    close "test_right_group_compaction lower_right" (hx c lr) 30.0
  -- test_up_group_compaction
  do
    let ((ul, ll, right), g) := (do
      let a ← mkNode 0.0 0.0 20.0 20.0
      let b ← mkNode 5.0 40.0 20.0 20.0
      let c ← mkNode 25.0 30.0 20.0 20.0
      mkGroup #[b, c]
      return (a, b, c) : StateM CGraph _).run CGraph.allDirections
    let c ← (compacter g).changeDirection .up >>= (·.compact) >>= (·.finish)
    close "test_up_group_compaction upper_left" (hy c ul) 0.0
    close "test_up_group_compaction lower_left" (hy c ll) 20.0
    close "test_up_group_compaction right" (hy c right) 10.0
  -- test_down_group_compaction
  do
    let ((ul, ll, right), g) := (do
      let a ← mkNode 0.0 0.0 20.0 20.0
      let b ← mkNode 5.0 40.0 10.0 20.0
      let c ← mkNode 25.0 10.0 20.0 20.0
      mkGroup #[a, c]
      return (a, b, c) : StateM CGraph _).run CGraph.allDirections
    let c ← (compacter g).changeDirection .down >>= (·.compact) >>= (·.finish)
    close "test_down_group_compaction upper_left" (hy c ul) 20.0
    close "test_down_group_compaction lower_left" (hy c ll) 40.0
    close "test_down_group_compaction right" (hy c right) 30.0
  -- test_no_spacing_applied_within_groups
  do
    let (ns, g) := (do
      let one ← mkNode 0.0 0.0 20.0 20.0
      let two ← mkNode 20.0 10.0 20.0 20.0
      let three ← mkNode 40.0 20.0 20.0 20.0
      mkGroup #[one, two, three]
      let four ← mkNode 22.0 80.0 20.0 20.0
      let five ← mkNode 42.0 90.0 20.0 20.0
      let six ← mkNode 62.0 100.0 20.0 20.0
      mkGroup #[four, five, six]
      return #[one, two, three, four, five, six] : StateM CGraph _).run CGraph.allDirections
    let c := (compacter g).setSpacingsHandler testSpacingHandler
    let c ← c.changeDirection .left >>= (·.compact) >>= (·.changeDirection .right) >>= (·.compact)
      >>= (·.changeDirection .up) >>= (·.compact) >>= (·.changeDirection .down) >>= (·.compact)
      >>= (·.finish)
    let xs := #[0.0, 20.0, 40.0, 0.0, 20.0, 40.0]
    let ys := #[0.0, 10.0, 20.0, 35.0, 45.0, 55.0]
    for i in [0:6] do
      close s!"test_no_spacing_applied_within_groups x{i + 1}" (hx c ns[i]!) xs[i]!
      close s!"test_no_spacing_applied_within_groups y{i + 1}" (hy c ns[i]!) ys[i]!

def subsequentDirections : Suite :=
  suite "alg.common.compaction.OneDimensionalCompactor.subsequentDirections" do
  -- test_subsequent_directions_compaction: 256 direction sequences on the same graph
  let ((one, two, three, four), g0) := (do
    let a ← mkNode 0.0 0.0 20.0 20.0
    let b ← mkNode 25.0 0.0 20.0 20.0
    let c ← mkNode 0.0 25.0 20.0 20.0
    let d ← mkNode 25.0 25.0 20.0 20.0
    return (a, b, c, d) : StateM CGraph _).run CGraph.allDirections
  let directions : Array Direction := #[.left, .right, .up, .down]
  let mut g := g0
  for d1 in directions do
    for d2 in directions do
      for d3 in directions do
        for d4 in directions do
          let c := (compacter g).setSpacingsHandler testSpacingHandler
          let c ← c.changeDirection d1 >>= (·.compact) >>= (·.changeDirection d2) >>= (·.compact)
            >>= (·.changeDirection d3) >>= (·.compact) >>= (·.changeDirection d4) >>= (·.compact)
            >>= (·.finish)
          g := c.cGraph
          let near (a b : Float) : Bool := (a - b).abs <= EPSILON
          let ok := near (hx c one) 0.0 && near (hy c one) 0.0 && near (hx c two) 25.0 &&
            near (hy c two) 0.0 && near (hx c three) 0.0 && near (hy c three) 25.0 &&
            near (hx c four) 25.0 && near (hy c four) 25.0
          check s!"test_subsequent_directions_compaction {d1} {d2} {d3} {d4}" ok

/-- The node-dependent spacing of `test_horizontal_spacings` / `test_vertical_spacings`. -/
private def tieredSpacing (one two three : CNodeId) (fallback : Float) :
    CGraph → CNodeId → CNodeId → Float := fun _ a b =>
  if a == three || b == three then 10.0
  else if a == two || b == two then 7.0
  else if a == one || b == one then 5.0
  else fallback

def spacings : Suite := suite "alg.common.compaction.OneDimensionalCompactor.spacings" do
  -- test_horizontal_spacings
  do
    let ((one, two, three), g) := (do
      let a ← mkNode 0.0 0.0 20.0 20.0
      let b ← mkNode 50.0 0.0 20.0 20.0
      let c ← mkNode 150.0 0.0 20.0 20.0
      return (a, b, c) : StateM CGraph _).run CGraph.allDirections
    let handler : SpacingsHandler := ⟨tieredSpacing one two three SPACING, fun _ _ _ => SPACING⟩
    let mut hg := g
    for (step, dir) in #[(1, Direction.left), (2, .right), (3, .left)] do
      let c := (compacter hg).setSpacingsHandler handler
      let c ← c.changeDirection dir >>= (·.compact) >>= (·.finish)
      hg := c.cGraph
      close s!"test_horizontal_spacings {step} one" (hx c one) 0.0
      close s!"test_horizontal_spacings {step} two" (hx c two) 27.0
      close s!"test_horizontal_spacings {step} three" (hx c three) 57.0
  -- test_vertical_spacings
  do
    let ((one, two, three), g) := (do
      let a ← mkNode 0.0 0.0 20.0 20.0
      let b ← mkNode 0.0 50.0 20.0 20.0
      let c ← mkNode 0.0 150.0 20.0 20.0
      return (a, b, c) : StateM CGraph _).run CGraph.allDirections
    let handler : SpacingsHandler := ⟨fun _ _ _ => 0.0, tieredSpacing one two three 0.0⟩
    let mut vg := g
    for (step, dir) in #[(1, Direction.up), (2, .down), (3, .up)] do
      let c := (compacter vg).setSpacingsHandler handler
      let c ← c.changeDirection dir >>= (·.compact) >>= (·.finish)
      vg := c.cGraph
      close s!"test_vertical_spacings {step} one" (hy c one) 0.0
      close s!"test_vertical_spacings {step} two" (hy c two) 27.0
      close s!"test_vertical_spacings {step} three" (hy c three) 57.0
  -- test_vertical_spacing_during_horizontal_compaction
  do
    let ((one, two, three), g) := (do
      let a ← mkNode 150.0 11.0 20.0 20.0
      let b ← mkNode 0.0 40.0 20.0 20.0
      let c ← mkNode 150.0 76.0 20.0 20.0
      return (a, b, c) : StateM CGraph _).run CGraph.allDirections
    let vertical : CGraph → CNodeId → CNodeId → Float := fun _ a b =>
      if a == three || b == three then 15.0
      else if a == one || b == one then 10.0
      else if a == two || b == two then 5.0
      else 0.0
    let c := (compacter g).setSpacingsHandler ⟨fun _ _ _ => 0.0, vertical⟩
    let c ← c.changeDirection .left >>= (·.compact) >>= (·.finish)
    close "test_vertical_spacing_during_horizontal_compaction one" (hx c one) 20.0
    close "test_vertical_spacing_during_horizontal_compaction two" (hx c two) 0.0
    close "test_vertical_spacing_during_horizontal_compaction three" (hx c three) 0.0
  -- test_horizontal_spacing_during_vertical_compaction
  do
    let ((one, two, three), g) := (do
      let a ← mkNode 16.0 150.0 20.0 20.0
      let b ← mkNode 40.0 0.0 20.0 20.0
      let c ← mkNode 76.0 150.0 20.0 20.0
      return (a, b, c) : StateM CGraph _).run CGraph.allDirections
    let horizontal : CGraph → CNodeId → CNodeId → Float := fun _ a b =>
      if a == three || b == three then 15.0
      else if a == two || b == two then 10.0
      else if a == one || b == one then 5.0
      else 0.0
    let c := (compacter g).setSpacingsHandler ⟨horizontal, fun _ _ _ => 0.0⟩
    let c ← c.changeDirection .up >>= (·.compact) >>= (·.finish)
    close "test_horizontal_spacing_during_vertical_compaction one" (hy c one) 20.0
    close "test_horizontal_spacing_during_vertical_compaction two" (hy c two) 0.0
    close "test_horizontal_spacing_during_vertical_compaction three" (hy c three) 0.0

def scanlineInline : Suite := suite "alg.common.compaction.ScanlineConstraintCalculator" do
  -- zero_extent_does_not_create_cyclic_group_constraints (ELK ticket 213)
  for direction in #[Direction.left, .right, .up, .down] do
    let rects : Array (Float × Float × Float × Float) :=
      #[(49.0, 59.0, 1.0, 0.0), (41.0, 89.0, 20.0, 20.0), (41.0, 109.0, 0.0, 30.0)]
    let (nodes, g) := (do
      let mut nodes := #[]
      for (x, y, w, h) in rects do
        let n ← if direction == .up || direction == .down then mkNode y x h w else mkNode x y w h
        nodes := nodes.push n
      mkGroup (nodes.extract 0 1)
      mkGroup (nodes.extract 1 nodes.size)
      return nodes : StateM CGraph _).run CGraph.allDirections
    let c ← (OneDimensionalCompactor.new g).changeDirection direction >>= (·.compact)
    for n in nodes do
      let cn := c.cGraph.cNode n
      check s!"zero_extent_does_not_create_cyclic_group_constraints {direction} {n} hitbox finite"
        (cn.hitbox.x.isFinite && cn.hitbox.y.isFinite)
      check s!"zero_extent_does_not_create_cyclic_group_constraints {direction} {n} reached"
        cn.startPos.isFinite
  -- zero_height_events_are_paired_between_ending_and_starting_intervals
  let (nodes, g) := (do
    let mut nodes := #[]
    let specs : Array (Float × Float) := #[(0.0, 2.0), (2.0, 0.0), (2.0, 0.0), (2.0, 3.0)]
    for i in [0:specs.size] do
      let (y, h) := specs[i]!
      let n ← mkNode i.toFloat y 1.0 h
      modify fun g => g.modifyCNode n fun c => { c with id := i }
      nodes := nodes.push n
    return nodes : StateM CGraph _).run CGraph.allDirections
  let events : Array ScanlineConstraintCalculator.Timestamp :=
    #[⟨nodes[3]!, true⟩, ⟨nodes[2]!, false⟩, ⟨nodes[1]!, false⟩, ⟨nodes[2]!, true⟩,
      ⟨nodes[0]!, false⟩, ⟨nodes[1]!, true⟩]
  let sorted := Elk.Core.Util.stableSort events (ScanlineConstraintCalculator.timestampCmp g)
  let actual := sorted.map fun p => ((g.cNode p.node).id, p.low)
  let expected : Array (Int × Bool) :=
    #[(0, false), (1, true), (1, false), (2, true), (2, false), (3, true)]
  checkEq "zero_height_events_are_paired_between_ending_and_starting_intervals" actual expected

def errors : Suite := suite "alg.common.compaction.OneDimensionalCompactor.errors" do
  let (g, a, b) := twoInRow
  -- CGroup::add_c_node panics for a node that already belongs to a group
  let g := match CGroup.create g #[a] with | .ok (g, _) => g | .error _ => g
  check "add_c_node node of another group fails" (match CGroup.create g #[a, b] with
    | .error e => e == CGroup.belongsToAnotherGroupMessage
    | .ok _ => false)
  let c ← (compacter g).finish
  checkThrows "compact after finish throws" (do let _ ← c.compact)
  checkThrows "changeDirection after finish throws" (do let _ ← c.changeDirection .right)
  let horizontalOnly := (CGraph.new #[.left, .right])
  checkThrows "unsupported direction throws"
    (do let _ ← (OneDimensionalCompactor.new horizontalOnly).changeDirection .up)
  let (g2, x) := CNode.create CGraph.allDirections (ElkRectangle.ofValues 0.0 0.0 1.0 1.0)
  let (g2, removedMissing) := CGroup.removeCNode g2 ⟨0⟩ x
  check "remove_c_node from missing group" (!removedMissing && (g2.cNode x).cGroup.isNone)

def suites : Array Tests.Suite :=
  #[basicCompaction, groupCompaction, subsequentDirections, spacings, scanlineInline, errors]

end Tests.AlgCommon.Compaction
