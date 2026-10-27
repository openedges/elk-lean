import Elk.Core.Math.ElkRectangle
/-!
# `org.eclipse.elk.alg.common.utils.SVGImage`

TODO(debug): the SVG debug writer (elk-rs `utils/svg_image.rs`) is not ported.
This is a minimal no-op structure with the same API: every drawing method
returns the image unchanged and the `save` variants write nothing. The
algorithms in `org.eclipse.elk.alg.common` (`BowyerWatsonTriangulation`,
`NaiveMinST`, `DepthFirstCompaction`, `ScanlineOverlapCheck`) accept an
optional debug output file name and ignore it, which is the observable
behaviour of elk-rs without debug output (`SVGImage::new(None)`).
-/
namespace Elk.Alg.Common.Utils

open Elk.Core.Math

/-- `org.eclipse.elk.alg.common.utils.SVGImage` (no-op stub, TODO(debug)). -/
structure SVGImage where
  /-- The output file name (`None` disables debug output). -/
  fileName : Option String := none
  /-- Whether debug output is enabled (always written nowhere in this port). -/
  debug : Bool := false
  deriving Repr, Inhabited

namespace SVGImage

/-- `SVGImage::new(file)`: like Rust, a blank name or one starting with `null` disables
output. -/
def new (file : Option String := none) : SVGImage :=
  match file with
  | some f =>
    let t := f.trimAscii.toString
    if !t.isEmpty && !t.startsWith "null" then { fileName := some t, debug := true } else {}
  | none => {}

/-- `g(key)`: selects a group (no-op). -/
@[inline] def g (s : SVGImage) (_key : String) : SVGImage := s
/-- `addGroups(keys)` (no-op). -/
@[inline] def addGroups (s : SVGImage) (_keys : Array String) : SVGImage := s
/-- `clearGroup(key)` (no-op). -/
@[inline] def clearGroup (s : SVGImage) (_key : String) : SVGImage := s
/-- `removeGroup(key)` (no-op). -/
@[inline] def removeGroup (s : SVGImage) (_key : String) : SVGImage := s
/-- `setViewBox(x, y, w, h)` (no-op). -/
@[inline] def setViewBox (s : SVGImage) (_x _y _w _h : Float) : SVGImage := s
/-- `clear()` (no-op). -/
@[inline] def clear (s : SVGImage) : SVGImage := s
/-- `addElementStr(element)` (no-op). -/
@[inline] def addElementStr (s : SVGImage) (_element : String) : SVGImage := s
/-- `addCircle(x, y)` (no-op). -/
@[inline] def addCircle (s : SVGImage) (_x _y : Float) : SVGImage := s
/-- `addCircle(x, y, r, attributes)` (no-op). -/
@[inline] def addCircleWithAttrs (s : SVGImage) (_x _y _r : Float) (_attributes : String) : SVGImage := s
/-- `addLine(x1, y1, x2, y2)` (no-op). -/
@[inline] def addLine (s : SVGImage) (_x1 _y1 _x2 _y2 : Float) : SVGImage := s
/-- `addLine(x1, y1, x2, y2, attributes)` (no-op). -/
@[inline] def addLineWithAttrs (s : SVGImage) (_x1 _y1 _x2 _y2 : Float) (_attributes : String) : SVGImage := s
/-- `addRect(x, y, w, h, attributes)` (no-op). -/
@[inline] def addRectWithValues (s : SVGImage) (_x _y _w _h : Float) (_attributes : String) : SVGImage := s
/-- `addRect(rect, attributes)` (no-op). -/
@[inline] def addRect (s : SVGImage) (_rect : ElkRectangle) (_attributes : String) : SVGImage := s
/-- `addPoly(attributes, points)` (no-op). -/
@[inline] def addPoly (s : SVGImage) (_attributes : String) (_points : Array KVector) : SVGImage := s
/-- `addText(x, y, text, attributes)` (no-op). -/
@[inline] def addText (s : SVGImage) (_x _y : Float) (_text _attributes : String) : SVGImage := s
/-- `save(fileName)` (writes nothing). -/
@[inline] def saveWithName (_s : SVGImage) (_fileName : String) : IO Unit := pure ()
/-- `save()` (writes nothing). -/
@[inline] def save (_s : SVGImage) : IO Unit := pure ()
/-- `isave(fileName)`: indexed save (no-op). -/
@[inline] def isaveWithName (s : SVGImage) (_fileName : String) : SVGImage := s
/-- `isave()`: indexed save (no-op). -/
@[inline] def isave (s : SVGImage) : SVGImage := s

end SVGImage

end Elk.Alg.Common.Utils
