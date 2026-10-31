import Tests.Framework
import Elk.Alg.Common.Polyomino
/-! Tests of `org.eclipse.elk.alg.common` (Polyomino). Owned by the Polyomino porting task.

* `twoBitGrid`: port of elk-rs `tests/all/two_bit_grid_test.rs` (`dimension_test`,
  `in_bounds_test`, `cell_test`) plus rendering/word-boundary checks.
* `planarGrid`, `polyomino`, `profileFill`, `pack`: own checks. The expected values of
  `profileFill`, `pack` and the grid bounds were printed by a throw-away Java program against the
  unmodified ELK 0.12.0 jars (same polyominoes, every traversal strategy, two sorting
  configurations; agent DIS). They first came from elk-rs 0.12.1, which sorts the polyominoes
  ascending where Java sorts with the low-level comparator `.reversed()`. -/
namespace Tests.AlgCommon.Polyomino

open Tests Elk.Alg.Common.Polyomino Elk.Alg.Common.Polyomino.Structures
  Elk.Alg.Common.Compaction.Options

private def WIDTH : Nat := 35
private def HEIGHT : Nat := 3

private def createGrid : TwoBitGrid := TwoBitGrid.new WIDTH HEIGHT

private def allCells (g : TwoBitGrid) (p : TwoBitGrid → Nat → Nat → Bool) : Bool := Id.run do
  for y in [0:g.height] do
    for x in [0:g.width] do
      if !p g x y then return false
  return true

private def mapCells (g : TwoBitGrid) (f : TwoBitGrid → Nat → Nat → TwoBitGrid) : TwoBitGrid := Id.run do
  let mut g := g
  for y in [0:g.height] do
    for x in [0:g.width] do
      g := f g x y
  return g

def twoBitGrid : Suite := suite "alg.common.polyomino.TwoBitGrid" do
  -- dimension_test
  let grid := createGrid
  checkEq "dimension_test width" grid.width WIDTH
  checkEq "dimension_test height" grid.height HEIGHT
  let second := TwoBitGrid.new 64 64
  checkEq "dimension_test second width" second.width 64
  checkEq "dimension_test second height" second.height 64
  -- in_bounds_test (`(-1_i32) as usize` is the maximal usize)
  let negOne : Nat := 0xFFFFFFFFFFFFFFFF
  check "in_bounds_test (0,0)" (grid.inBounds 0 0)
  check "in_bounds_test (-1,0)" (!grid.inBounds negOne 0)
  check "in_bounds_test (0,-1)" (!grid.inBounds 0 negOne)
  check "in_bounds_test (-1,-1)" (!grid.inBounds negOne negOne)
  check "in_bounds_test (34,2)" (grid.inBounds 34 2)
  check "in_bounds_test (34,3)" (!grid.inBounds 34 3)
  check "in_bounds_test (35,2)" (!grid.inBounds 35 2)
  check "in_bounds_test (35,3)" (!grid.inBounds 35 3)
  check "in_bounds_test (17,1)" (grid.inBounds 17 1)
  -- cell_test
  check "cell_test empty (0,0)" (grid.isEmpty 0 0)
  check "cell_test empty (34,2)" (grid.isEmpty 34 2)
  let grid := grid.setBlocked 0 0
  check "cell_test blocked (0,0)" (grid.isBlocked 0 0 && !grid.isEmpty 0 0 && !grid.isWeaklyBlocked 0 0)
  let grid := grid.setWeaklyBlocked 1 0
  check "cell_test after weak (0,0)" (grid.isBlocked 0 0 && !grid.isEmpty 0 0 && !grid.isWeaklyBlocked 0 0)
  check "cell_test weak (1,0)" (!grid.isBlocked 1 0 && !grid.isEmpty 1 0 && grid.isWeaklyBlocked 1 0)
  let grid := grid.setEmpty 0 0
  check "cell_test emptied (0,0)" (!grid.isBlocked 0 0 && grid.isEmpty 0 0 && !grid.isWeaklyBlocked 0 0)
  check "cell_test still weak (1,0)" (!grid.isBlocked 1 0 && !grid.isEmpty 1 0 && grid.isWeaklyBlocked 1 0)
  check "cell_test empty (33,2)" (grid.isEmpty 33 2)
  let grid := grid.setBlocked 33 2
  check "cell_test unchanged (0,0)" (!grid.isBlocked 0 0 && grid.isEmpty 0 0 && !grid.isWeaklyBlocked 0 0)
  check "cell_test unchanged (1,0)" (!grid.isBlocked 1 0 && !grid.isEmpty 1 0 && grid.isWeaklyBlocked 1 0)
  check "cell_test blocked (33,2)" (grid.isBlocked 33 2 && !grid.isEmpty 33 2 && !grid.isWeaklyBlocked 33 2)
  let second := mapCells second TwoBitGrid.setBlocked
  check "cell_test 64x64 all blocked" (allCells second TwoBitGrid.isBlocked)
  let second := mapCells second TwoBitGrid.setWeaklyBlocked
  check "cell_test 64x64 all weakly blocked" (allCells second TwoBitGrid.isWeaklyBlocked)
  let second := mapCells second TwoBitGrid.setEmpty
  check "cell_test 64x64 all empty" (allCells second TwoBitGrid.isEmpty)
  -- own checks: word boundaries and the Display format
  let g := ((createGrid.setBlocked 31 1).setWeaklyBlocked 32 1).setBlocked 33 1
  check "word boundary 31/32/33" (g.isBlocked 31 1 && g.isWeaklyBlocked 32 1 && g.isBlocked 33 1 &&
    g.isEmpty 30 1 && g.isEmpty 34 1 && g.isEmpty 31 0 && g.isEmpty 31 2)
  checkEq "two bits per cell layout" (g.grid[1 * g.words + 0]!, g.grid[1 * g.words + 1]!)
    ((1 : UInt64) <<< 62, (2 : UInt64) ||| ((1 : UInt64) <<< 2))
  let small := ((TwoBitGrid.new 3 2).setBlocked 0 0).setWeaklyBlocked 2 1
  checkEq "toString" (toString small) " 012\n0X__\n1__0"
  check "out of bounds read is empty, write ignored"
    ((small.setBlocked 3 0) == small && small.isEmpty 5 5)

def planarGrid : Suite := suite "alg.common.polyomino.PlanarGrid" do
  let g := PlanarGrid.new 5 4
  checkEq "center of 5x4" (g.centerX, g.centerY) ((2 : Int), (1 : Int))
  let e := PlanarGrid.new 0 0
  checkEq "center of empty grid" (e.centerX, e.centerY) ((-1 : Int), (-1 : Int))
  let g := match g.setBlockedCenterBased 0 0 with | .ok g => g | .error _ => g
  check "center-based set at (0,0) is cell (2,1)" (g.isBlocked 2 1)
  checkEq "isBlockedCenterBased (0,0)" (g.isBlockedCenterBased 0 0 |>.toOption) (some true)
  check "inBoundsCenterBased" (g.inBoundsCenterBased (-2) (-1) && g.inBoundsCenterBased 2 2 &&
    !g.inBoundsCenterBased (-3) 0 && !g.inBoundsCenterBased 3 0 && !g.inBoundsCenterBased 0 3)
  check "toIndex out of bounds message (Java: translated point, then the center-based one)"
    (match g.toIndex 0 3 with
      | .error m => m == "Grid is only of size 5*4. Requested point (2, 4) is out of bounds. " ++
          "Given center based coordinates were (0, 3)."
      | .ok _ => false)
  -- Java: a read right of the width inside the last 32-cell word sees an empty cell, a write fails
  checkEq "isEmptyCenterBased right of the width (Java)" (g.isEmptyCenterBased 3 0 |>.toOption) (some true)
  check "setBlockedCenterBased right of the width fails (Java)" (match g.setBlockedCenterBased 3 0 with
    | .error m => m == "Grid is only of size 5*4. Requested point (5, 1) is out of bounds. " ++
        "Given center based coordinates were (3, 0)."
    | .ok _ => false)
  check "isEmptyCenterBased below the grid fails (Java)" (match g.isEmptyCenterBased 0 3 with
    | .error m => m == "Grid is only of size 5*4. Requested point (2, 4) is out of bounds. " ++
        "Given center based coordinates were (0, 3)."
    | .ok _ => false)
  checkEq "weaklyIntersectsArea right of the width inside the word (Java)"
    (g.weaklyIntersectsArea 5 0 31 0 |>.toOption) (some false)
  check "weaklyIntersectsArea beyond the word fails (Java)" (match g.weaklyIntersectsArea 5 0 32 0 with
    | .error m => m == "Grid is only of size 5*4. Requested point (32, 0) is out of bounds."
    | .ok _ => false)
  check "weaklyBlockArea right of the width fails (Java)" (match g.weaklyBlockArea 4 0 5 0 with
    | .error m => m == "Grid is only of size 5*4. Requested point (5, 0) is out of bounds."
    | .ok _ => false)
  -- Java `int` arithmetic: no blocked cell gives (MAX, MAX, MIN - MAX + 1 = 2, 2)
  checkEq "filled bounds of empty grid (Java)" (PlanarGrid.new 4 4).filledBounds
    ((2147483647 : Int), (2147483647 : Int), (2 : Int), (2 : Int))
  let g := (g.setBlocked 4 3).setBlocked 1 2
  checkEq "filled bounds" g.filledBounds ((1 : Int), (1 : Int), (4 : Int), (3 : Int))
  let w := match g.weaklyBlockArea 0 1 4 1 with | .ok w => w | .error _ => g
  check "weaklyBlockArea keeps blocked cells" (w.isBlocked 2 1 && w.isWeaklyBlocked 0 1 &&
    w.isWeaklyBlocked 4 1 && w.isEmpty 0 0)
  checkEq "weaklyIntersectsArea hit" (w.weaklyIntersectsArea 0 0 2 1 |>.toOption) (some true)
  checkEq "weaklyIntersectsArea miss" (w.weaklyIntersectsArea 0 0 4 0 |>.toOption) (some false)
  checkEq "weaklyIntersectsArea empty area" (w.weaklyIntersectsArea 3 0 2 0 |>.toOption) (some false)
  check "weaklyIntersectsArea out of bounds fails" (match w.weaklyIntersectsArea (-1) 0 0 0 with
    | .error m => m == "Grid is only of size 5*4. Requested point (-1, 0) is out of bounds."
    | .ok _ => false)
  -- grid intersection: a 1x1 blocked other grid against the blocked center cell
  let other := (PlanarGrid.new 1 1).setBlocked 0 0
  check "intersectsWithCenterBasedGrid at center" (g.intersectsWithCenterBasedGrid other 0 0)
  check "no intersection next to it" (!g.intersectsWithCenterBasedGrid other 1 0)
  check "no intersection outside" (!g.intersectsWithCenterBasedGrid other 10 10)
  let weakOther := (PlanarGrid.new 1 1).setWeaklyBlocked 0 0
  check "weak cell vs weak cell does not intersect"
    (!w.intersectsWithCenterBasedGrid weakOther (-2) 0)
  check "weak cell vs blocked cell intersects" (w.intersectsWithCenterBasedGrid weakOther 0 0)

def polyomino : Suite := suite "alg.common.polyomino.Polyomino" do
  let p := Polyomino.new 3 2
  checkEq "size" (PolyominoLike.width p, PolyominoLike.height p) (3, 2)
  checkEq "center" (PolyominoLike.centerX p, PolyominoLike.centerY p) ((1 : Int), (0 : Int))
  let p := PolyominoLike.addExtension p .east 0 1
  let p := PolyominoLike.addExtension p .north 1 2
  checkEq "extensions" (PolyominoLike.polyominoExtensions p).size 2
  check "extension order" ((PolyominoLike.polyominoExtensions p)[1]! == (.north, 1, 2))
  let p := PolyominoLike.setY (PolyominoLike.setX p 4) (-3)
  checkEq "position" (PolyominoLike.x p, PolyominoLike.y p) ((4 : Int), (-3 : Int))
  let p := PolyominoLike.setBlocked p 2 1
  check "set via PolyominoLike" (PolyominoLike.isBlocked p 2 1 && PolyominoLike.isEmpty p 0 0)
  let p2 := Polyomino.withExtensions 2 2 #[(.west, 0, 0)]
  checkEq "withExtensions" p2.polyominoExtensions.size 1
  checkEq "Direction.isHorizontal" (#[Direction.north, .east, .south, .west].map (·.isHorizontal))
    #[false, true, false, true]
  -- placing a polyomino with an east extension weakly blocks the row to the grid border
  let grid := PlanarGrid.new 6 3
  let one := PolyominoLike.setBlocked (Polyomino.withExtensions 1 1 #[(.east, 0, 0)]) 0 0
  match grid.addFilledCellsFromPolyomino one 0 0 with
  | .ok (g, placed) =>
    checkEq "placed position" (placed.x, placed.y) ((2 : Int), (1 : Int))
    check "extension area weakly blocked" (g.isBlocked 2 1 && g.isWeaklyBlocked 3 1 &&
      g.isWeaklyBlocked 5 1 && g.isEmpty 1 1 && g.isEmpty 3 0)
    let probe := PolyominoLike.setBlocked (Polyomino.new 1 1) 0 0
    checkEq "blocked probe on a weakly blocked extension cell intersects"
      (g.intersectsWithCenterBasedPolyomino probe 2 0 |>.toOption) (some true)
    checkEq "probe below is free" (g.intersectsWithCenterBasedPolyomino probe 2 1 |>.toOption)
      (some false)
  | .error e => check s!"addFilledCellsFromPolyomino failed: {e}" false

/-- Rendering of the oracle program: rows separated (and terminated) by `|`. -/
private def render (g : PlanarGrid) : String := Id.run do
  let mut s := ""
  for y in [0:g.height] do
    for x in [0:g.width] do
      s := s.push (if g.isBlocked x y then 'X' else if g.isWeaklyBlocked x y then '0' else '_')
    s := s.push '|'
  return s

private def blockAll (p : Polyomino) (cells : Array (Nat × Nat)) : Polyomino :=
  cells.foldl (fun p (x, y) => PolyominoLike.setBlocked p x y) p

private def ring : Polyomino :=
  blockAll (Polyomino.new 4 3) #[(0, 0), (1, 0), (2, 0), (3, 0), (0, 2), (1, 2), (2, 2), (3, 2),
    (0, 1), (3, 1)]

private def makePolys : Array Polyomino :=
  let p0 := blockAll (Polyomino.new 3 3)
    #[(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]
  let p1 := blockAll (Polyomino.new 2 4) #[(0, 0), (0, 1), (0, 2), (0, 3), (1, 3)]
  let p3 := PolyominoLike.addExtension (blockAll (Polyomino.new 1 1) #[(0, 0)]) .east 0 0
  #[p0, p1, ring, p3]

def profileFill : Suite := suite "alg.common.polyomino.ProfileFill" do
  checkEq "ring is filled (Java)" (render (ProfileFill.fillPolyomino ring).grid) "XXXX|XXXX|XXXX|"
  let u := blockAll (Polyomino.new 5 4) #[(0, 0), (0, 1), (0, 2), (0, 3), (4, 0), (4, 1), (4, 2),
    (4, 3), (1, 3), (2, 3), (3, 3), (2, 1)]
  checkEq "U shape (Java)" (render (ProfileFill.fillPolyomino u).grid) "X___X|X_X_X|X_X_X|XXXXX|"
  let empty := Polyomino.new 3 3
  checkEq "empty polyomino unchanged" (render (ProfileFill.fillPolyomino empty).grid) "___|___|___|"

private def packLine (i j : Nat) (h : Polyominoes Polyomino) : String := Id.run do
  let mut line := s!"pack {i} {j}"
  for p in h.polys do
    line := line ++ s!" ({PolyominoLike.width p}x{PolyominoLike.height p}@{p.x},{p.y})"
  let (bx, byy, bw, bh) := h.grid.filledBounds
  line := line ++ s!" grid {h.grid.width}x{h.grid.height} bounds {bx} {byy} {bw} {bh}"
  return line

/-- ELK Java 0.12.0 output of the pack runs: strategy index (Java ordinal) × sorting configuration
(0 = BY_SIZE_AND_SHAPE / NUM_OF_EXTERNAL_SIDES…, 1 = BY_SIZE / CORNER_CASES…). The low-level sort is
descending (`.reversed()`), so the 4x3 ring comes first in every run. -/
private def expectedPack : Array String := #[
    "pack 0 0 (4x3@11,12) (3x3@8,14) (2x4@9,10) (1x1@10,11) grid 26x28 bounds 8 10 7 7",
    "pack 0 1 (4x3@11,12) (3x3@8,14) (2x4@9,10) (1x1@10,11) grid 26x28 bounds 8 10 7 7",
    "pack 1 0 (4x3@11,12) (3x3@8,9) (2x4@10,12) (1x1@11,11) grid 26x28 bounds 8 9 7 7",
    "pack 1 1 (4x3@11,12) (3x3@8,9) (2x4@10,12) (1x1@11,11) grid 26x28 bounds 8 9 7 7",
    "pack 2 0 (4x3@11,12) (3x3@11,9) (2x4@10,12) (1x1@12,15) grid 26x28 bounds 10 9 5 7",
    "pack 2 1 (4x3@11,12) (3x3@11,9) (2x4@10,12) (1x1@12,15) grid 26x28 bounds 10 9 5 7",
    "pack 3 0 (4x3@11,12) (3x3@11,9) (2x4@10,12) (1x1@12,15) grid 26x28 bounds 10 9 5 7",
    "pack 3 1 (4x3@11,12) (3x3@11,9) (2x4@10,12) (1x1@12,15) grid 26x28 bounds 10 9 5 7",
    "pack 4 0 (4x3@11,12) (3x3@8,9) (2x4@10,12) (1x1@12,11) grid 26x28 bounds 8 9 7 7",
    "pack 4 1 (4x3@11,12) (3x3@8,9) (2x4@10,12) (1x1@12,11) grid 26x28 bounds 8 9 7 7",
    "pack 5 0 (4x3@11,12) (3x3@11,9) (2x4@10,12) (1x1@12,15) grid 26x28 bounds 10 9 5 7",
    "pack 5 1 (4x3@11,12) (3x3@11,9) (2x4@10,12) (1x1@12,15) grid 26x28 bounds 10 9 5 7",
    "pack 6 0 (4x3@11,12) (3x3@11,9) (2x4@10,12) (1x1@12,15) grid 26x28 bounds 10 9 5 7",
    "pack 6 1 (4x3@11,12) (3x3@11,9) (2x4@10,12) (1x1@12,15) grid 26x28 bounds 10 9 5 7",
    "pack 7 0 (4x3@11,12) (3x3@8,9) (2x4@10,12) (1x1@12,11) grid 26x28 bounds 8 9 7 7",
    "pack 7 1 (4x3@11,12) (3x3@8,9) (2x4@10,12) (1x1@12,11) grid 26x28 bounds 8 9 7 7",
    "pack 8 0 (4x3@11,12) (3x3@11,9) (2x4@10,12) (1x1@12,15) grid 26x28 bounds 10 9 5 7",
    "pack 8 1 (4x3@11,12) (3x3@11,9) (2x4@10,12) (1x1@12,15) grid 26x28 bounds 10 9 5 7"]

private def expectedDefaultGrid : String :=
  "__________________________|__________________________|__________________________|" ++
  "__________________________|__________________________|__________________________|" ++
  "__________________________|__________________________|__________________________|" ++
  "________XXX_______________|________XXX_______________|________XXX_X0000000000000|" ++
  "__________XXXXX___________|__________XXXXX___________|__________XXXXX___________|" ++
  "__________XX______________|__________________________|__________________________|" ++
  "__________________________|__________________________|__________________________|" ++
  "__________________________|__________________________|__________________________|" ++
  "__________________________|__________________________|__________________________|" ++
  "__________________________|"

def pack : Suite := suite "alg.common.polyomino.PolyominoCompactor" do
  let configs : Array (LowLevelSortingCriterion × HighLevelSortingCriterion) :=
    #[(.bySizeAndShape, .numOfExternalSidesThanNumOfExtensionsLast),
      (.bySize, .cornerCasesThanSingleSideLast)]
  let strategies : Array TraversalStrategy := Elk.ElkEnum.values
  for i in [0:strategies.size] do
    for j in [0:configs.size] do
      let (low, high) := configs[j]!
      let h := Polyominoes.new makePolys 1.0 true
      let h := h.setProperty PolyominoOptions.POLYOMINO_TRAVERSAL_STRATEGY (some strategies[i]!)
      let h := h.setProperty PolyominoOptions.POLYOMINO_LOW_LEVEL_SORT (some low)
      let h := h.setProperty PolyominoOptions.POLYOMINO_HIGH_LEVEL_SORT (some high)
      let h ← PolyominoCompactor.packPolyominoesIO h
      checkEq s!"packPolyominoes {strategies[i]!} config {j} (Java)" (packLine i j h)
        (expectedPack[i * 2 + j]!)
  -- default options (property defaults: QUADRANTS_LINE_BY_LINE, BY_SIZE_AND_SHAPE, NUM_OF_...)
  let h ← PolyominoCompactor.packPolyominoesIO (Polyominoes.new makePolys 1.0 true)
  checkEq "packPolyominoes default grid (Java)" (render h.grid) expectedDefaultGrid
  checkEq "default options = config 0" (packLine 4 0 h) (expectedPack[8]!)
  -- grid sizing by aspect ratio (Java: 65x28 and 26x94)
  let h2 := Polyominoes.new makePolys 2.5 false
  let h3 := Polyominoes.new makePolys 0.3 false
  checkEq "aspect ratio sizes (Java)" (h2.grid.width, h2.grid.height, h3.grid.width, h3.grid.height)
    (65, 28, 26, 94)
  -- options metadata
  let r := PolyominoOptions.metaDataProvider.apply {}
  checkEq "registered option ids" (r.options.map (·.id))
    #["org.eclipse.elk.polyomino.traversalStrategy", "org.eclipse.elk.polyomino.lowLevelSort",
      "org.eclipse.elk.polyomino.highLevelSort", "org.eclipse.elk.polyomino.fill"]
  checkEq "option group" (r.options.map (·.group)) #["polyomino", "polyomino", "polyomino", "polyomino"]

def suites : Array Tests.Suite := #[twoBitGrid, planarGrid, polyomino, profileFill, pack]

end Tests.AlgCommon.Polyomino
