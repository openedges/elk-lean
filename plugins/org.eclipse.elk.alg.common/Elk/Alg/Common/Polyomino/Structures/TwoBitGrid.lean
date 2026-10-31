import Elk.Alg.Common.Polyomino.Structures.IThreeValueGrid
/-!
# `org.eclipse.elk.alg.common.polyomino.structures.TwoBitGrid`

A three-value grid storing two bits per cell (elk-rs `structures/two_bit_grid.rs`).

Bit layout (identical to Rust): row `y` has `words = ceil(width / 32)` 64-bit words; cell `x`
lives in word `x >> 5` at bit offset `(x & 31) * 2`, the lower bit being the LSB.
`EMPTY = 0b00`, `BLOCKED = 0b01`, `WEAKLY_BLOCKED = 0b10`. The Rust `Vec<Vec<u64>>` is stored
row-major in one flat `Array UInt64`.

Out-of-bounds accesses panic in Rust (Java: `IndexOutOfBoundsException`). The total Lean
accessors (`retrieve`, `setBits`, `isEmpty`, ...) report `EMPTY` for out-of-bounds reads and
ignore out-of-bounds writes; they serve the callers whose coordinates are in bounds. The callers
that can reach out-of-bounds cells (`PlanarGrid`'s center-based and area operations) use the
`*Java` variants, which follow Java exactly: a read fails only outside the `long[height][words]`
array (`y` outside the height, `x < 0`, `x >> 5 >= words`) — a cell right of the width inside the
last word reads `EMPTY` (it is never written) — and a write fails for `x >= width` as well;
the error is the Java message (`boundsMessage`).
-/
namespace Elk.Alg.Common.Polyomino.Structures

/-- `TwoBitGrid`. -/
structure TwoBitGrid where
  /-- The cells, `words` words per row, row-major. -/
  grid : Array UInt64 := #[]
  /-- Words per row (`ceil(xSize / 32)`). -/
  words : Nat := 0
  /-- `xSize` (width). -/
  xSize : Nat := 0
  /-- `ySize` (height). -/
  ySize : Nat := 0
  deriving Inhabited, BEq

namespace TwoBitGrid

private def TWO_LSBS_MASK : UInt64 := 0x03
private def LSB_MASK : UInt64 := 0x01
/-- Cell value `EMPTY`. -/
def EMPTY : UInt64 := 0x00
/-- Cell value `BLOCKED`. -/
def BLOCKED : UInt64 := 0x01
/-- Cell value `WEAKLY_BLOCKED`. -/
def WEAKLY_BLOCKED : UInt64 := 0x02

/-- `new TwoBitGrid(width, height)`: all cells empty. -/
def new (width height : Nat) : TwoBitGrid :=
  let words := (width + 31) / 32
  { grid := Array.replicate (words * height) 0, words, xSize := width, ySize := height }

/-- The Java/Rust out-of-bounds message. -/
def boundsMessage (width height : Nat) (x y : Int) : String :=
  s!"Grid is only of size {width}*{height}. Requested point ({x}, {y}) is out of bounds."

/-- `getWidth()`. -/
@[inline] def width (g : TwoBitGrid) : Nat := g.xSize
/-- `getHeight()`. -/
@[inline] def height (g : TwoBitGrid) : Nat := g.ySize

/-- `inBounds(x, y)`. -/
@[inline] def inBounds (g : TwoBitGrid) (x y : Nat) : Bool := x < g.xSize && y < g.ySize

/-- `checkBounds(x, y)` as an `Except` (Rust panics). -/
def checkBounds (g : TwoBitGrid) (x y : Nat) : Except String Unit :=
  if g.inBounds x y then .ok () else .error (boundsMessage g.xSize g.ySize x y)

@[inline] private def wordIndex (g : TwoBitGrid) (x y : Nat) : Nat := y * g.words + (x >>> 5)
@[inline] private def bitOffset (x : Nat) : UInt64 := UInt64.ofNat ((x &&& 0x1f) <<< 1)

/-- `retrieve(x, y)`: the two bits of the cell (`EMPTY` when out of bounds). -/
def retrieve (g : TwoBitGrid) (x y : Nat) : UInt64 :=
  if g.inBounds x y then
    ((g.grid[g.wordIndex x y]?.getD 0) >>> bitOffset x) &&& TWO_LSBS_MASK
  else EMPTY

/-- `set(x, y, msb, lsb)` (ignored when out of bounds). -/
def setBits (g : TwoBitGrid) (x y : Nat) (msb lsb : Bool) : TwoBitGrid :=
  if g.inBounds x y then
    let i := g.wordIndex x y
    let mask := LSB_MASK <<< bitOffset x
    let msbMask := mask <<< 1
    { g with grid := g.grid.modify i fun w =>
        let w := if lsb then w ||| mask else w &&& ~~~mask
        if msb then w ||| msbMask else w &&& ~~~msbMask }
  else g

/-- Java `retrieve(x, y)` (`(grid[y][x >> 5] >>> ((x & 31) << 1)) & 3`): fails outside the
array (Java `ArrayIndexOutOfBoundsException`, rethrown by the public accessors as
`IndexOutOfBoundsException` with `boundsMessage`); cells right of the width inside the last word
read `EMPTY`. -/
def retrieveJava (g : TwoBitGrid) (x y : Int) : Except String UInt64 :=
  if y < 0 || y >= (g.ySize : Int) || x < 0 || (x.toNat >>> 5) >= g.words then
    .error (boundsMessage g.xSize g.ySize x y)
  else
    .ok (((g.grid[y.toNat * g.words + (x.toNat >>> 5)]?.getD 0) >>> bitOffset x.toNat) &&& TWO_LSBS_MASK)

/-- Java `isEmpty(x, y)` (bounds of `retrieveJava`). -/
@[inline] def isEmptyJava (g : TwoBitGrid) (x y : Int) : Except String Bool :=
  return (← g.retrieveJava x y) == EMPTY
/-- Java `isBlocked(x, y)` (bounds of `retrieveJava`). -/
@[inline] def isBlockedJava (g : TwoBitGrid) (x y : Int) : Except String Bool :=
  return (← g.retrieveJava x y) == BLOCKED
/-- Java `isWeaklyBlocked(x, y)` (bounds of `retrieveJava`). -/
@[inline] def isWeaklyBlockedJava (g : TwoBitGrid) (x y : Int) : Except String Bool :=
  return (← g.retrieveJava x y) == WEAKLY_BLOCKED

/-- Java `set(x, y, msb, lsb)`: fails for `x >= width` and outside the array. -/
def setBitsJava (g : TwoBitGrid) (x y : Int) (msb lsb : Bool) : Except String TwoBitGrid :=
  if x < 0 || y < 0 || x >= (g.xSize : Int) || y >= (g.ySize : Int) then
    .error (boundsMessage g.xSize g.ySize x y)
  else .ok (g.setBits x.toNat y.toNat msb lsb)

/-- `isEmpty(x, y)`. -/
@[inline] def isEmpty (g : TwoBitGrid) (x y : Nat) : Bool := g.retrieve x y == EMPTY
/-- `isBlocked(x, y)`. -/
@[inline] def isBlocked (g : TwoBitGrid) (x y : Nat) : Bool := g.retrieve x y == BLOCKED
/-- `isWeaklyBlocked(x, y)`. -/
@[inline] def isWeaklyBlocked (g : TwoBitGrid) (x y : Nat) : Bool := g.retrieve x y == WEAKLY_BLOCKED

/-- `reinitialize(width, height)`. -/
def reinitialize (_ : TwoBitGrid) (width height : Nat) : TwoBitGrid := new width height

/-- `setEmpty(x, y)`. -/
@[inline] def setEmpty (g : TwoBitGrid) (x y : Nat) : TwoBitGrid := g.setBits x y false false
/-- `setBlocked(x, y)`. -/
@[inline] def setBlocked (g : TwoBitGrid) (x y : Nat) : TwoBitGrid := g.setBits x y false true
/-- `setWeaklyBlocked(x, y)`. -/
@[inline] def setWeaklyBlocked (g : TwoBitGrid) (x y : Nat) : TwoBitGrid := g.setBits x y true false

private def incModTen (n : Nat) : Nat := if n > 8 then 0 else n + 1

/-- `toString()`: column/row indices modulo 10, `_` empty, `X` blocked, `0` weakly blocked
(Rust `Display`, without the trailing newline). -/
def render (g : TwoBitGrid) : String := Id.run do
  let mut out := " "
  let mut count := 0
  for _ in [0:g.xSize] do
    out := out ++ toString count
    count := incModTen count
  out := out.push '\n'
  count := 0
  for y in [0:g.ySize] do
    out := out ++ toString count
    count := incModTen count
    for x in [0:g.xSize] do
      let item := g.retrieve x y
      out := out.push (if item == EMPTY then '_' else if item == BLOCKED then 'X' else '0')
    out := out.push '\n'
  if out.endsWith "\n" then
    out := (out.dropEnd 1).toString
  return out

instance : ToString TwoBitGrid := ⟨render⟩

instance : IThreeValueGrid TwoBitGrid where
  width := width
  height := height
  isEmpty := isEmpty
  isBlocked := isBlocked
  isWeaklyBlocked := isWeaklyBlocked
  inBounds := inBounds
  reinitialize := reinitialize
  setEmpty := setEmpty
  setBlocked := setBlocked
  setWeaklyBlocked := setWeaklyBlocked

end TwoBitGrid

end Elk.Alg.Common.Polyomino.Structures
