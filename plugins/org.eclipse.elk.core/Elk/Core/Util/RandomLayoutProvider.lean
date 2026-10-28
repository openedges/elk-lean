import Elk.Core.Util.ElkUtil
import Elk.Core.LayoutProvider
import Elk.Core.Options
/-!
# `org.eclipse.elk.core.util.RandomLayoutProvider`

Ported 1:1 from elk-rs (which mirrors Java), including its quirks: the target
shape of an edge is looked up in the edge's sources and a port's centre adds
the parent's x twice. They are kept for oracle parity.
-/
/-! Float literals as global constants (FL): inside branches, loops and specialised code the compiler
shares a literal's `Nat`/`Bool` arguments with unrelated variables (CSE) and then parses it on every
evaluation (`FastFloat.ofScientificImpl`); a top-level constant is a load (PLAN §7.1 items 17, 22). -/
private def fl0p0 : Float := 0.0
private def fl1p0 : Float := 1.0
private def fl2p0 : Float := 2.0

namespace Elk.Core.Util

open Elk.Graph Elk.Core Elk.Core.Math Elk.Core.Options

namespace RandomLayoutProvider

def MAX_BENDS : Int := 5
def RAND_FACT : Float := 0.2

/-- `connectable_center`: (cx, cy, halfWidth, halfHeight) of a node or port. -/
private def connectableCenter (g : ElkGraph) : ConnectableId → Float × Float × Float × Float
  | .node n =>
    let nd := g.node n
    (nd.x + nd.width / 2.0, nd.y + nd.height / 2.0, nd.width / 2.0, nd.height / 2.0)
  | .port p =>
    let pt := g.port p
    let parentX := match pt.parent with
      | some pn => (g.node pn).x
      | none => 0.0
    -- elk-rs adds the parent's x twice (and nothing to y); kept for parity
    (pt.x + parentX + parentX + pt.width / 2.0, pt.y + pt.height / 2.0, pt.width / 2.0, pt.height / 2.0)

private def ensureSingleSection (e : EdgeId) : ElkM SectionId := do
  let sections := (← ElkM.getEdge e).sections
  if sections.isEmpty then
    ElkM.createSection (some e)
  else
    if sections.size > 1 then modify (·.retainLastEdgeSection e)
    return (← ElkM.getEdge e).sections[0]!

/-- `randomize_edge`. -/
private def randomizeEdge (e : EdgeId) (random : Random) (drawWidth drawHeight : Float) : ElkM Random := do
  let g ← get
  let edge := g.edge e
  let some sourceShape := edge.sources[0]? | return random
  let (sourceX, sourceY, sourceWidth, sourceHeight) := connectableCenter g sourceShape
  -- elk-rs takes the "target" from the sources as well (kept for parity)
  let some targetShape := edge.sources[0]? | return random
  let (targetX, targetY, targetWidth, targetHeight) := connectableCenter g targetShape
  let sec ← ensureSingleSection e
  let mut sourcePx := targetX
  if targetX > sourceX + sourceWidth then sourcePx := sourceX + sourceWidth
  else if targetX < sourceX - sourceWidth then sourcePx := sourceX - sourceWidth
  let mut sourcePy := targetY
  if targetY > sourceY + sourceHeight then sourcePy := sourceY + sourceHeight
  else if targetY < sourceY - sourceHeight then sourcePy := sourceY - sourceHeight
  if sourcePx > sourceX - sourceWidth && sourcePx < sourceX + sourceWidth
      && sourcePy > sourceY - sourceHeight && sourcePy < sourceY + sourceHeight then
    sourcePx := sourceX + sourceWidth
  let mut targetPx := sourceX
  if sourceX > targetX + targetWidth then targetPx := targetX + targetWidth
  else if sourceX < targetX - targetWidth then targetPx := targetX - targetWidth
  let mut targetPy := sourceY
  if sourceY > targetY + targetHeight then targetPy := targetY + targetHeight
  else if sourceY < targetY - targetHeight then targetPy := targetY - targetHeight
  if targetPx > targetX - targetWidth && targetPx < targetX + targetWidth
      && targetPy > targetY - targetHeight && targetPy < targetY + targetHeight then
    targetPy := targetY + targetHeight
  let mut random := random
  let (bendsNumRaw, r1) := random.nextInt MAX_BENDS
  random := r1
  let bendsNum := if sourceShape == targetShape then bendsNumRaw + 1 else bendsNumRaw
  let xdiff := targetPx - sourcePx
  let ydiff := targetPy - sourcePy
  let totalDist := Float.sqrt (xdiff * xdiff + ydiff * ydiff)
  let maxRand := totalDist * RAND_FACT
  let xincr := xdiff / (bendsNum + 1).toFloat
  let yincr := ydiff / (bendsNum + 1).toFloat
  let mut x := sourcePx
  let mut y := sourcePy
  let mut bends : Array KVector := #[]
  for _ in [0:bendsNum.toNat] do
    x := x + xincr
    y := y + yincr
    let (fx, r2) := random.nextFloat
    random := r2
    let mut randx := x + fx * maxRand - maxRand / fl2p0
    if randx < fl0p0 then randx := fl1p0 else if randx > drawWidth then randx := drawWidth - fl1p0
    let (fy, r3) := random.nextFloat
    random := r3
    let mut randy := y + fy * maxRand - maxRand / fl2p0
    if randy < fl0p0 then randy := fl1p0 else if randy > drawHeight then randy := drawHeight - fl1p0
    bends := bends.push ⟨randx, randy⟩
  let bendsFinal := bends
  ElkM.modifySection sec fun s => { s with startX := sourcePx, startY := sourcePy, endX := targetPx, endY := targetPy, bendPoints := bendsFinal }
  return random

/-- `randomize`. -/
private def randomize (parent : NodeId) (random : Random) (aspectRatio spacing : Float) (padding : ElkPadding) : ElkM Unit := do
  let g ← get
  let children := (g.node parent).children
  if children.isEmpty then return
  let mut nodesArea := 0.0
  let mut maxWidth := 0.0
  let mut maxHeight := 0.0
  let mut m : Nat := 1
  for n in children do
    m := m + (ElkGraphUtil.allOutgoingEdges g n).size
    let nd := g.node n
    maxWidth := fmax maxWidth nd.width
    maxHeight := fmax maxHeight nd.height
    nodesArea := nodesArea + nd.width * nd.height
  let nF := children.size.toFloat
  let drawArea := nodesArea + 2.0 * spacing * spacing * m.toFloat * nF
  let areaSqrt := Float.sqrt drawArea
  let drawWidth := fmax (areaSqrt * aspectRatio) maxWidth
  let drawHeight := fmax (areaSqrt / aspectRatio) maxHeight
  let mut random := random
  for n in children do
    let nd ← ElkM.getNode n
    let (dx, r1) := random.nextDouble
    let (dy, r2) := r1.nextDouble
    random := r2
    let x := padding.left + dx * (drawWidth - nd.width)
    let y := padding.left + dy * (drawHeight - nd.height)
    ElkM.modifyNode n fun x' => { x' with x := x, y := y }
  let mut totalWidth := drawWidth + padding.left + padding.right
  let mut totalHeight := drawHeight + padding.top + padding.bottom
  for source in children do
    for e in ElkGraphUtil.allOutgoingEdges (← get) source do
      if !(ElkGraphUtil.isHierarchicalEdge (← get) e) then
        random ← randomizeEdge e random totalWidth totalHeight
  totalWidth := totalWidth + (padding.left + padding.right)
  totalHeight := totalHeight + (padding.top + padding.bottom)
  let _ ← ElkUtil.resizeNodeWith parent totalWidth totalHeight false true

/-- `RandomLayoutProvider.layout`. -/
def layout (layoutGraph : NodeId) (monitor : ProgressMonitor) : ElkM Unit := do
  let _ ← monitor.begin "Random Layout" 1.0
  let node ← ElkM.getNode layoutGraph
  if node.children.isEmpty then
    monitor.done
    return
  let randomSeed := node.props.getD RandomLayouterOptions.RANDOM_SEED 0
  -- Java `getProperty(..).floatValue()` (random layouter defaults 1.6f and 15)
  let aspectRatio := Float.toF32 (node.props.getD RandomLayouterOptions.ASPECT_RATIO 1.0)
  let spacing := Float.toF32 (node.props.getD RandomLayouterOptions.SPACING_NODE_NODE 0.0)
  let padding := node.props.getD RandomLayouterOptions.PADDING {}
  let random ← if randomSeed != 0 then pure (Random.ofInt randomSeed)
    else do
      let nanos ← IO.monoNanosNow
      pure (Random.ofUInt64 nanos.toUInt64)
  randomize layoutGraph random aspectRatio spacing padding
  monitor.done

def provider : LayoutProvider := { id := RandomLayouterOptions.ALGORITHM_ID, layout := layout }

end RandomLayoutProvider

end Elk.Core.Util
