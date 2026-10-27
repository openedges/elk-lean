import Std.Data.HashMap
import Elk.Graph.Monad
import Elk.Core.Exceptions
import Elk.Core.Math.ElkRectangle
import Elk.Core.Options.CoreOptions
import Elk.Core.Data.LayoutMetaDataService
import Elk.Core.Util.ElkTrace
import Elk.Core.Util.GraphElementVisitor
/-!
# `org.eclipse.elk.core.util.ElkUtil`

Port of elk-rs `core::util::elk_util` over the `ElkGraph` arena.

* Read-only helpers are pure functions taking the graph (`calcPortSide g p dir`).
* Mutators live in `ElkM` under their Java names (`resizeNode`, `translateNode`, …);
  their pure implementations are in `ElkUtil.Pure` (`ElkGraph → … → ElkGraph`).
* The Java/Rust `translate` and `configureWithDefaultValues` overloads become
  `translateNode` / `translateEdge` / `translateSection` / `translateNodeWithSizes`
  and `configureWithDefaultValues (el : ElementId)` (+ per kind variants).
* Rust `panic!`s (Java `IllegalArgumentException`s) become `Except String` in the
  pure API and `throwIllegalArgument` in `ElkM`.

Deviations:
* `calcPortSide`/`calcPortOffset` on a port without parent return `undefined`/`0`
  (Rust panics).
* `createIdentifier` cannot use pointer addresses; it assigns the decimal string of
  `4 * idx + kind` (node 0, edge 1, port 2, label 3), unique within one graph.
-/
namespace Elk.Core.Util

open Elk Elk.Graph Elk.Core.Math Elk.Core.Options Elk.Core.Data Elk.Core.Validation

namespace ElkUtil

/-- `ElkUtil.DEFAULT_MIN_WIDTH`. -/
def DEFAULT_MIN_WIDTH : Float := 20.0
/-- `ElkUtil.DEFAULT_MIN_HEIGHT`. -/
def DEFAULT_MIN_HEIGHT : Float := 20.0

/-! ## Ports -/

/-- `ElkUtil.calcPortSide(port, direction)`: the side of the parent node the port lies on. -/
def calcPortSide (g : ElkGraph) (port : PortId) (direction : Direction) : PortSide := Id.run do
  let p := g.port port
  -- Rust panics for a port without parent node
  let some parent := p.parent | return .undefined
  let n := g.node parent
  let nodeWidth := n.width
  let nodeHeight := n.height
  if nodeWidth <= 0.0 && nodeHeight <= 0.0 then return .undefined
  let xpos := p.x
  let ypos := p.y
  let portWidth := p.width
  let portHeight := p.height
  match direction with
  | .left | .right =>
    if xpos < 0.0 then return .west
    else if xpos + portWidth > nodeWidth then return .east
  | .up | .down =>
    if ypos < 0.0 then return .north
    else if ypos + portHeight > nodeHeight then return .south
  | .undefined => pure ()
  let widthPercent := (xpos + portWidth / 2.0) / nodeWidth
  let heightPercent := (ypos + portHeight / 2.0) / nodeHeight
  if widthPercent + heightPercent <= 1.0 && widthPercent - heightPercent <= 0.0 then return .west
  else if widthPercent + heightPercent >= 1.0 && widthPercent - heightPercent >= 0.0 then return .east
  else if heightPercent < 0.5 then return .north
  else return .south

/-- `ElkUtil.calcPortOffset(port, side)`: the offset of the port from the parent's border. -/
def calcPortOffset (g : ElkGraph) (port : PortId) (side : PortSide) : Float := Id.run do
  let p := g.port port
  -- Rust panics for a port without parent node
  let some parent := p.parent | return 0.0
  let n := g.node parent
  match side with
  | .north => return -(p.y + p.height)
  | .east => return p.x - n.width
  | .south => return p.y - n.height
  | .west => return -(p.x + p.width)
  | .undefined => return 0.0

/-- Layout direction relevant for the ports of `node`: the parent's `DIRECTION`, or the
node's own for a root node. -/
private def portDirection (g : ElkGraph) (node : NodeId) : Direction :=
  let target := ((g.node node).parent).getD node
  ((g.node target).props.get CoreOptions.DIRECTION).getD .undefined

/-- `PORT_SIDE` of a port; an undefined side is computed with `calcPortSide` and stored. -/
private def ensurePortSide (g : ElkGraph) (port : PortId) (direction : Direction) : ElkGraph × PortSide :=
  let side := ((g.port port).props.get CoreOptions.PORT_SIDE).getD .undefined
  if side == .undefined then
    let calculated := calcPortSide g port direction
    (g.setPortProp port CoreOptions.PORT_SIDE calculated, calculated)
  else (g, side)

/-! ## Node size -/

/-- `ElkUtil.effectiveMinSizeConstraintFor(node)`: `NODE_SIZE_MINIMUM` (with the default
minimum if requested) when `MINIMUM_SIZE` is a size constraint, else `(0, 0)`. -/
def effectiveMinSizeConstraintFor (g : ElkGraph) (node : NodeId) : KVector := Id.run do
  let props := (g.node node).props
  let sizeConstraint := (props.get CoreOptions.NODE_SIZE_CONSTRAINTS).getD SizeConstraint.fixed
  let sizeOptions := (props.get CoreOptions.NODE_SIZE_OPTIONS).getD EnumSet.noneOf
  let minSizeRaw := (props.get CoreOptions.NODE_SIZE_MINIMUM).getD KVector.zero
  if sizeConstraint.contains .minimumSize then
    let mut minSize := minSizeRaw
    if sizeOptions.contains .defaultMinimumSize then
      if minSize.x <= 0.0 then minSize := { minSize with x := DEFAULT_MIN_WIDTH }
      if minSize.y <= 0.0 then minSize := { minSize with y := DEFAULT_MIN_HEIGHT }
    return minSize
  else
    return KVector.zero

/-- `ElkUtil.computeInsidePart(labelPosition, labelSize, portSize, portBorderOffset, portSide)`. -/
def computeInsidePart (labelPosition labelSize portSize : KVector) (portBorderOffset : Float)
    (portSide : PortSide) : Float :=
  match portSide with
  | .north => fmax (labelSize.y + labelPosition.y - (portSize.y + portBorderOffset)) 0.0
  | .south => fmax (-labelPosition.y - portBorderOffset) 0.0
  | .east => fmax (-labelPosition.x - portBorderOffset) 0.0
  | .west => fmax (labelSize.x + labelPosition.x - (portSize.x + portBorderOffset)) 0.0
  | .undefined => 0.0

/-- `ElkUtil.getLabelsBounds(port)`: union of the port's label bounds (`(0,0,0,0)` without labels). -/
def getLabelsBoundsForPort (g : ElkGraph) (port : PortId) : ElkRectangle := Id.run do
  let mut bounds : Option ElkRectangle := none
  for l in (g.port port).labels do
    let lab := g.label l
    let current := ElkRectangle.ofValues lab.x lab.y lab.width lab.height
    bounds := some (match bounds with
      | some existing => existing.union current
      | none => current)
  return bounds.getD {}

/-! ## Positions -/

/-- `ElkUtil.toAbsolute(point, parent)`: adds the positions of `parent` and all its ancestors. -/
def toAbsolute (g : ElkGraph) (point : KVector) (parent : Option NodeId) : KVector :=
  match parent with
  | none => point
  | some p =>
    (ElkGraphUtil.ancestorChain g p true).foldl (fun acc n => acc.addValues (g.node n).x (g.node n).y) point

/-- `ElkUtil.toRelative(point, parent)`: subtracts the positions of `parent` and its ancestors. -/
def toRelative (g : ElkGraph) (point : KVector) (parent : Option NodeId) : KVector :=
  match parent with
  | none => point
  | some p =>
    (ElkGraphUtil.ancestorChain g p true).foldl (fun acc n => acc.addValues (-(g.node n).x) (-(g.node n).y)) point

/-- `ElkUtil.absolutePosition(element)` (elk-rs `absolute_position`): absolute coordinates
of a node, port or label; edges use their containing node. -/
partial def absolutePosition (g : ElkGraph) : ElementId → Option KVector
  | .node n =>
    let node := g.node n
    some (toAbsolute g ⟨node.x, node.y⟩ node.parent)
  | .port p =>
    let port := g.port p
    some (toAbsolute g ⟨port.x, port.y⟩ port.parent)
  | .edge e => ((g.edge e).containingNode).bind fun n => absolutePosition g (.node n)
  | .label l =>
    let lab := g.label l
    match lab.parent.bind (absolutePosition g) with
    | some parentPos => some ⟨parentPos.x + lab.x, parentPos.y + lab.y⟩
    | none => none

/-! ## Vector chains and junction points -/

/-- `ElkUtil.createVectorChain(edgeSection)`: start point, bend points, end point. -/
def createVectorChain (g : ElkGraph) (s : SectionId) : KVectorChain :=
  let sec := g.edgeSection s
  (#[sec.startPoint] ++ sec.bendPoints).push sec.endPoint

/-- Message of the `IllegalArgumentException` thrown by `applyVectorChain`. -/
def vectorChainTooShortMessage : String := "The vector chain must contain at least a source and a target point."

/-- `ElkUtil.getPoints(section)` (private in Java): the section's points without collinear
intermediate points. -/
private def getPoints (g : ElkGraph) (s : SectionId) : Array KVector := Id.run do
  let mut points := createVectorChain g s
  let mut i := 1
  while i + 1 < points.size do
    let p1 := points[i - 1]!
    let p2 := points[i]!
    let p3 := points[i + 1]!
    if (p1.x == p2.x && p2.x == p3.x) || (p1.y == p2.y && p2.y == p3.y) then
      points := points.eraseIdx! i
    else
      i := i + 1
  return points

/-- Rust `f64::signum` (`1.0` for `+0.0`, `-1.0` for `-0.0`, NaN for NaN). -/
private def rustSignum (x : Float) : Float :=
  if x.isNaN then x else if x.toBits >= 0x8000000000000000 then -1.0 else 1.0

private def oneSectionMessage (n : Nat) : String :=
  s!"The edge needs to have exactly one edge section. Found: {n}"

/-- `ElkUtil.determineJunctionPoints(edge, port, reverse)` (private in Java). -/
private def determineJunctionPointsForPort (g : ElkGraph) (edge : EdgeId) (port : PortId) (reverse : Bool) :
    Except String KVectorChain := do
  let some edgeSection := (g.edge edge).sections[0]? | throw (oneSectionMessage 0)
  let sectionPoints := getPoints g edgeSection
  let mut pointsMap : Std.HashMap SectionId (Array KVector) := {}
  let mut offsetMap : Std.HashMap SectionId KVector := {}
  let mut allConnectedSections : Array SectionId := #[]
  for otherEdge in ElkGraphUtil.allIncidentEdgesForShape g (.port port) do
    let otherSections := (g.edge otherEdge).sections
    if otherSections.size != 1 then throw (oneSectionMessage otherSections.size)
    if otherEdge == edge then continue
    let otherSection := otherSections[0]!
    if !pointsMap.contains otherSection then
      pointsMap := pointsMap.insert otherSection (getPoints g otherSection)
    let otherPoints := pointsMap.getD otherSection #[]
    let offset :=
      if reverse then sectionPoints[sectionPoints.size - 1]! - otherPoints[otherPoints.size - 1]!
      else sectionPoints[0]! - otherPoints[0]!
    offsetMap := offsetMap.insert otherSection offset
    allConnectedSections := allConnectedSections.push otherSection
  let mut junctionPoints : KVectorChain := #[]
  if !allConnectedSections.isEmpty then
    let mut p1 := if reverse then sectionPoints[sectionPoints.size - 1]! else sectionPoints[0]!
    for i in [1:sectionPoints.size] do
      let p2 := if reverse then sectionPoints[sectionPoints.size - 1 - i]! else sectionPoints[i]!
      let mut idx := 0
      while idx < allConnectedSections.size do
        let key := allConnectedSections[idx]!
        let otherPoints := pointsMap.getD key #[]
        if otherPoints.size <= i then
          allConnectedSections := allConnectedSections.eraseIdx! idx
          continue
        let otherIndex := if reverse then otherPoints.size - 1 - i else i
        let mut p3 := otherPoints[otherIndex]!
        if let some offset := offsetMap.get? key then p3 := p3 + offset
        if p2.x != p3.x || p2.y != p3.y then
          let dx2 := p2.x - p1.x
          let dy2 := p2.y - p1.y
          let dx3 := p3.x - p1.x
          let dy3 := p3.y - p1.y
          if dx3 * dy2 == dy3 * dx2 && rustSignum dx2 == rustSignum dx3 && rustSignum dy2 == rustSignum dy3 then
            if dx2.abs < dx3.abs || dy2.abs < dy3.abs then
              junctionPoints := junctionPoints.push p2
          else if i > 1 then
            junctionPoints := junctionPoints.push p1
          allConnectedSections := allConnectedSections.eraseIdx! idx
          continue
        idx := idx + 1
      p1 := p2
  return junctionPoints

/-- `ElkUtil.determineJunctionPoints(edge)`: junction points of an edge with exactly one
section, against the other edges incident to its source and target ports.
Errors (Java `IllegalArgumentException`) when an involved edge has not exactly one section. -/
def determineJunctionPoints (g : ElkGraph) (edge : EdgeId) : Except String KVectorChain := do
  let e := g.edge edge
  if e.sections.size != 1 then throw (oneSectionMessage e.sections.size)
  let mut junctionPoints : KVectorChain := #[]
  if let some shape := e.sources[0]? then
    if let some port := ElkGraphUtil.connectableShapeToPort shape then
      junctionPoints := junctionPoints ++ (← determineJunctionPointsForPort g edge port false)
  if let some shape := e.targets[0]? then
    if let some port := ElkGraphUtil.connectableShapeToPort shape then
      junctionPoints := junctionPoints ++ (← determineJunctionPointsForPort g edge port true)
  return junctionPoints

/-! ## Element paths and names -/

/-- Container of an element for `printElementPath` (`eContainer()`). -/
private def elementContainer (g : ElkGraph) : ElementId → Option ElementId
  | .node n => (g.node n).parent.map ElementId.node
  | .port p => (g.port p).parent.map ElementId.node
  | .edge e => (g.edge e).containingNode.map ElementId.node
  | .label l => (g.label l).parent

private def elementClassName : ElementId → String
  | .node _ => "Node"
  | .edge _ => "Edge"
  | .port _ => "Port"
  | .label _ => "Label"

private def firstLabelText (g : ElkGraph) (el : ElementId) : Option String :=
  ((g.labelsOf el).map fun l => (g.label l).text).find? (!·.isEmpty)

/-- `ElkUtil.printElementPath(element, builder)`: appends a human readable path of the
element (`Root Node a > Node b > Edge (…)`) to `builder`. -/
partial def printElementPathInto (g : ElkGraph) (el : ElementId) (builder : String) : String := Id.run do
  let mut b := match elementContainer g el with
    | some parent => printElementPathInto g parent builder ++ " > "
    | none => builder ++ "Root "
  b := b ++ elementClassName el
  if let some identifier := g.identifierOf el then
    if !identifier.isEmpty then return b ++ " " ++ identifier
  if let .label l := el then
    let text := (g.label l).text
    if !text.isEmpty then return b ++ " " ++ text
  if let some text := firstLabelText g el then return b ++ " " ++ text
  if let .edge e := el then
    let edge := g.edge e
    if edge.isConnected then
      b := b ++ " ("
      for i in [0:edge.sources.size] do
        if i > 0 then b := b ++ ", "
        b := printElementPathInto g edge.sources[i]!.toElement b
      b := b ++ " -> "
      for i in [0:edge.targets.size] do
        if i > 0 then b := b ++ ", "
        b := printElementPathInto g edge.targets[i]!.toElement b
      b := b ++ ")"
  return b

/-- `ElkUtil.printElementPath(element)` into a fresh string. -/
def printElementPath (g : ElkGraph) (el : ElementId) : String := printElementPathInto g el ""

/-- `ElkUtil.debugFolderPath(subfolders...)`: `$HOME/elk/<subfolders>/` (or `USERPROFILE`). -/
def debugFolderPath (subfolders : Array String) : IO (Option String) := do
  let home ← match ← IO.getEnv "HOME" with
    | some h => pure (some h)
    | none => IO.getEnv "USERPROFILE"
  let some home := home | return none
  let sep := System.FilePath.pathSeparator
  let mut path := home
  if !path.endsWith (String.singleton sep) then path := path.push sep
  path := (path ++ "elk").push sep
  for sub in subfolders do
    path := (path ++ sub).push sep
  return some path

/-- Rust `char::is_whitespace` (Unicode `White_Space`). -/
private def isRustWhitespace (c : Char) : Bool :=
  let n := c.toNat
  (n >= 0x09 && n <= 0x0D) || n == 0x20 || n == 0x85 || n == 0xA0 || n == 0x1680 ||
  (n >= 0x2000 && n <= 0x200A) || n == 0x2028 || n == 0x2029 || n == 0x202F || n == 0x205F || n == 0x3000

/-- `ElkUtil.toSafePathName(name)`: whitespace → `_`, ASCII alphanumerics and `_` kept,
everything else → `-`. -/
def toSafePathName (name : String) : String :=
  String.map (fun c => if isRustWhitespace c then '_' else if c.isAlphanum || c == '_' then c else '-') name

/-- Identifier assigned by `createIdentifier` (see the module doc). -/
def generatedIdentifier : ElementId → String
  | .node n => toString (4 * n.idx)
  | .edge e => toString (4 * e.idx + 1)
  | .port p => toString (4 * p.idx + 2)
  | .label l => toString (4 * l.idx + 3)

/-! ## Pure implementations of the mutators -/

namespace Pure

/-- Port side computation and minimum sizes of `ElkUtil.resizeNode` (before `resizeNodeWith`). -/
private def resizeNodePortSizes (g : ElkGraph) (node : NodeId) : ElkGraph × Float × Float := Id.run do
  let n := g.node node
  let sizeConstraint := (n.props.get CoreOptions.NODE_SIZE_CONSTRAINTS).getD SizeConstraint.fixed
  let portConstraints := (n.props.get CoreOptions.PORT_CONSTRAINTS).getD .undefined
  let ports := n.ports
  let mut g := g
  let mut newWidth := 0.0
  let mut newHeight := 0.0
  if sizeConstraint.contains .ports then
    let direction := portDirection g node
    let mut minNorth := 2.0
    let mut minEast := 2.0
    let mut minSouth := 2.0
    let mut minWest := 2.0
    for port in ports do
      let p := g.port port
      let (g', portSide) := ensurePortSide g port direction
      g := g'
      if portConstraints == .fixedPos then
        match portSide with
        | .north => minNorth := fmax minNorth (p.x + p.width)
        | .east => minEast := fmax minEast (p.y + p.height)
        | .south => minSouth := fmax minSouth (p.x + p.width)
        | .west => minWest := fmax minWest (p.y + p.height)
        | .undefined => pure ()
      else
        match portSide with
        | .north => minNorth := minNorth + p.width + 2.0
        | .east => minEast := minEast + p.height + 2.0
        | .south => minSouth := minSouth + p.width + 2.0
        | .west => minWest := minWest + p.height + 2.0
        | .undefined => pure ()
    newWidth := fmax minNorth minSouth
    newHeight := fmax minEast minWest
  return (g, newWidth, newHeight)

/-- Pure `ElkUtil.resizeNode(node, newWidth, newHeight, movePorts, moveLabels)`; returns the
graph and the `(widthRatio, heightRatio)` scale vector. -/
def resizeNodeWith (g : ElkGraph) (node : NodeId) (newWidth newHeight : Float)
    (movePorts moveLabels : Bool) : ElkGraph × KVector := Id.run do
  let n := g.node node
  let oldSize := n.size
  let fixedPorts := (n.props.get CoreOptions.PORT_CONSTRAINTS).getD .undefined == .fixedPos
  let ports := n.ports
  let mut newSize := effectiveMinSizeConstraintFor g node
  if newWidth > newSize.x then newSize := { newSize with x := newWidth }
  if newHeight > newSize.y then newSize := { newSize with y := newHeight }
  -- a collapsed axis has no scale; keep its port coordinates until placement
  let widthRatio := if oldSize.x == 0.0 then 1.0 else newSize.x / oldSize.x
  let heightRatio := if oldSize.y == 0.0 then 1.0 else newSize.y / oldSize.y
  let widthDiff := newSize.x - oldSize.x
  let heightDiff := newSize.y - oldSize.y
  let mut g := g
  if movePorts then
    let direction := portDirection g node
    for port in ports do
      let (g', portSide) := ensurePortSide g port direction
      g := g'.modifyPort port fun p =>
        match portSide with
        | .north => if !fixedPorts then { p with x := p.x * widthRatio } else p
        | .east =>
          let p := { p with x := p.x + widthDiff }
          if !fixedPorts then { p with y := p.y * heightRatio } else p
        | .south =>
          let p := if !fixedPorts then { p with x := p.x * widthRatio } else p
          { p with y := p.y + heightDiff }
        | .west => if !fixedPorts then { p with y := p.y * heightRatio } else p
        | .undefined => p
  g := g.modifyNode node fun x => { x with width := newSize.x, height := newSize.y }
  -- relative label placement is undefined on a collapsed rectangle
  if moveLabels && oldSize.x != 0.0 && oldSize.y != 0.0 then
    for l in (g.node node).labels do
      g := g.modifyLabel l fun lab => Id.run do
        let midx := lab.x + lab.width / 2.0
        let midy := lab.y + lab.height / 2.0
        let widthPercent := midx / oldSize.x
        let heightPercent := midy / oldSize.y
        if widthPercent + heightPercent >= 1.0 then
          if widthPercent - heightPercent > 0.0 && midy >= 0.0 then
            return { lab with x := lab.x + widthDiff, y := lab.y + heightDiff * heightPercent }
          else if widthPercent - heightPercent < 0.0 && midx >= 0.0 then
            return { lab with x := lab.x + widthDiff * widthPercent, y := lab.y + heightDiff }
        return lab
  g := g.setNodeProp node CoreOptions.NODE_SIZE_CONSTRAINTS SizeConstraint.fixed
  return (g, ⟨widthRatio, heightRatio⟩)

/-- Pure `ElkUtil.resizeNode(node)`: `none` if the node has a fixed size. -/
def resizeNode (g : ElkGraph) (node : NodeId) : ElkGraph × Option KVector :=
  let sizeConstraint := ((g.node node).props.get CoreOptions.NODE_SIZE_CONSTRAINTS).getD SizeConstraint.fixed
  if sizeConstraint.isEmpty then (g, none)
  else
    let (g, w, h) := resizeNodePortSizes g node
    let (g, v) := resizeNodeWith g node w h true true
    (g, some v)

private def scaleLabelOrPortAnchor (props : PropertyMap) (s : Float) : PropertyMap :=
  match props.get CoreOptions.PORT_ANCHOR with
  | some anchor => props.set CoreOptions.PORT_ANCHOR ⟨anchor.x * s, anchor.y * s⟩
  | none => props

/-- Pure `ElkUtil.applyConfiguredNodeScaling(node)`: scales the node, its labels, ports and
port labels by `SCALE_FACTOR`. -/
def applyConfiguredNodeScaling (g : ElkGraph) (node : NodeId) : ElkGraph := Id.run do
  let n := g.node node
  let s := (n.props.get CoreOptions.SCALE_FACTOR).getD 1.0
  if (s - 1.0).abs < Float.epsilon then return g
  let nodeLabels := n.labels
  let ports := n.ports
  let mut g := g.modifyNode node fun x => { x with width := x.width * s, height := x.height * s }
  let portLabels := ports.foldl (fun acc p => acc ++ (g.port p).labels) #[]
  for l in nodeLabels ++ portLabels do
    g := g.modifyLabel l fun lab =>
      { lab with x := lab.x * s, y := lab.y * s, width := lab.width * s, height := lab.height * s,
                 props := scaleLabelOrPortAnchor lab.props s }
  for p in ports do
    g := g.modifyPort p fun port =>
      { port with x := port.x * s, y := port.y * s, width := port.width * s, height := port.height * s,
                  props := scaleLabelOrPortAnchor port.props s }
  return g

/-- Pure `ElkUtil.computeChildAreaDimensions(node)`: sets `CHILD_AREA_WIDTH/HEIGHT` to the
extent of the node's labels, children (with margins) and contained edges. -/
def computeChildAreaDimensions (g : ElkGraph) (node : NodeId) : ElkGraph := Id.run do
  let mut minX := Float.posInf
  let mut minY := Float.posInf
  let mut maxX := 0.0
  let mut maxY := 0.0
  let n := g.node node
  let edges := n.containedEdges
  let edgeLabels := edges.foldl (fun acc e => acc ++ (g.edge e).labels) #[]
  for l in n.labels ++ edgeLabels do
    let lab := g.label l
    let margins := (lab.props.get CoreOptions.MARGINS).getD {}
    minX := fmin minX (lab.x - margins.left)
    minY := fmin minY (lab.y - margins.top)
    maxX := fmax maxX (lab.x + lab.width + margins.right)
    maxY := fmax maxY (lab.y + lab.height + margins.bottom)
  for c in n.children do
    let child := g.node c
    let margins := (child.props.get CoreOptions.MARGINS).getD {}
    minX := fmin minX (child.x - margins.left)
    minY := fmin minY (child.y - margins.top)
    maxX := fmax maxX (child.x + child.width + margins.right)
    maxY := fmax maxY (child.y + child.height + margins.bottom)
  for e in edges do
    for s in (g.edge e).sections do
      let sec := g.edgeSection s
      minX := fmin minX sec.startX
      minX := fmin minX sec.endX
      maxX := fmax maxX sec.startX
      maxX := fmax maxX sec.endX
      minY := fmin minY sec.startY
      minY := fmin minY sec.endY
      maxY := fmax maxY sec.startY
      maxY := fmax maxY sec.endY
      for bp in sec.bendPoints do
        minX := fmin minX bp.x
        maxX := fmax maxX bp.x
        minY := fmin minY bp.y
        maxY := fmax maxY bp.y
  if !minX.isFinite || !minY.isFinite then
    minX := 0.0
    minY := 0.0
    maxX := 0.0
    maxY := 0.0
  let g := g.setNodeProp node CoreOptions.CHILD_AREA_WIDTH (maxX - minX)
  return g.setNodeProp node CoreOptions.CHILD_AREA_HEIGHT (maxY - minY)

/-- Pure `ElkUtil.translate(section, xoffset, yoffset)`. -/
def translateSection (g : ElkGraph) (s : SectionId) (xoffset yoffset : Float) : ElkGraph :=
  g.modifySection s fun sec =>
    { sec with startX := sec.startX + xoffset, startY := sec.startY + yoffset,
               endX := sec.endX + xoffset, endY := sec.endY + yoffset,
               bendPoints := sec.bendPoints.map (·.addValues xoffset yoffset) }

/-- Pure `ElkUtil.translate(edge, xoffset, yoffset)`: sections, labels and junction points. -/
def translateEdge (g : ElkGraph) (e : EdgeId) (xoffset yoffset : Float) : ElkGraph := Id.run do
  let edge := g.edge e
  let mut g := g
  for s in edge.sections do
    g := translateSection g s xoffset yoffset
  for l in edge.labels do
    g := g.modifyLabel l fun lab => { lab with x := lab.x + xoffset, y := lab.y + yoffset }
  match (g.edge e).props.get CoreOptions.JUNCTION_POINTS with
  | some jp => g := g.setEdgeProp e CoreOptions.JUNCTION_POINTS (jp.offsetValues xoffset yoffset)
  | none => pure ()
  return g

/-- Pure `ElkUtil.translate(parent, xoffset, yoffset)`: moves the children and contained edges. -/
def translateNode (g : ElkGraph) (parent : NodeId) (xoffset yoffset : Float) : ElkGraph := Id.run do
  let n := g.node parent
  let mut g := g
  for c in n.children do
    g := g.modifyNode c fun x => { x with x := x.x + xoffset, y := x.y + yoffset }
  for e in n.containedEdges do
    g := translateEdge g e xoffset yoffset
  return g

/-- Pure `ElkUtil.translate(parent, newSize, oldSize)`: moves the content of a resized
node according to its `CONTENT_ALIGNMENT`. -/
def translateNodeWithSizes (g : ElkGraph) (parent : NodeId) (newSize oldSize : KVector) : ElkGraph := Id.run do
  let contentAlignment := ((g.node parent).props.get CoreOptions.CONTENT_ALIGNMENT).getD ContentAlignment.topLeft
  let mut xTranslate := 0.0
  let mut yTranslate := 0.0
  if newSize.x > oldSize.x then
    if contentAlignment.contains .hCenter then xTranslate := (newSize.x - oldSize.x) / 2.0
    else if contentAlignment.contains .hRight then xTranslate := newSize.x - oldSize.x
  if newSize.y > oldSize.y then
    if contentAlignment.contains .vCenter then yTranslate := (newSize.y - oldSize.y) / 2.0
    else if contentAlignment.contains .vBottom then yTranslate := newSize.y - oldSize.y
  return translateNode g parent xTranslate yTranslate

/-- Pure `ElkUtil.applyVectorChain(vectorChain, section)`: errors if the chain has fewer than
two points (Java `IllegalArgumentException`). -/
def applyVectorChain (g : ElkGraph) (chain : KVectorChain) (s : SectionId) : Except String ElkGraph :=
  if chain.size < 2 then .error vectorChainTooShortMessage
  else
    let first := chain[0]!
    let last := chain[chain.size - 1]!
    .ok <| g.modifySection s fun sec =>
      { sec with startX := first.x, startY := first.y,
                 bendPoints := chain.extract 1 (chain.size - 1),
                 endX := last.x, endY := last.y }

/-- `ElkUtil.ensureLabel(element)` (private): creates a label with the identifier as text if
the element has no labels. -/
private def ensureLabel (g : ElkGraph) (el : ElementId) : ElkGraph :=
  match el with
  | .label _ => g
  | _ =>
    if !(g.labelsOf el).isEmpty then g
    else match g.identifierOf el with
      | some identifier => if identifier.isEmpty then g else (g.createLabel (some el) identifier).1
      | none => g

/-- Pure `ElkUtil.configureWithDefaultValues(ElkNode)`. -/
def configureNodeWithDefaultValues (g : ElkGraph) (node : NodeId) : ElkGraph := Id.run do
  let n := g.node node
  let sizeConstraint := (n.props.get CoreOptions.NODE_SIZE_CONSTRAINTS).getD SizeConstraint.fixed
  let mut g := g
  if sizeConstraint == SizeConstraint.fixed && n.width == 0.0 && n.height == 0.0 then
    g := g.modifyNode node fun x => { x with width := DEFAULT_MIN_WIDTH * 4.0, height := DEFAULT_MIN_HEIGHT * 4.0 }
  g := ensureLabel g (.node node)
  let placement := ((g.node node).props.get CoreOptions.NODE_LABELS_PLACEMENT).getD NodeLabelPlacement.fixed
  if placement == NodeLabelPlacement.fixed then
    g := g.setNodeProp node CoreOptions.NODE_LABELS_PLACEMENT NodeLabelPlacement.insideCenter
  return g

/-- Pure `ElkUtil.configureWithDefaultValues(ElkPort)`. -/
def configurePortWithDefaultValues (g : ElkGraph) (port : PortId) : ElkGraph :=
  let p := g.port port
  let g := if p.width == 0.0 && p.height == 0.0 then
      g.modifyPort port fun x => { x with width := DEFAULT_MIN_WIDTH / 4.0, height := DEFAULT_MIN_HEIGHT / 4.0 }
    else g
  ensureLabel g (.port port)

/-- Pure `ElkUtil.configureWithDefaultValues(ElkEdge)`. -/
def configureEdgeWithDefaultValues (g : ElkGraph) (edge : EdgeId) : ElkGraph :=
  if (g.edge edge).props.has CoreOptions.EDGE_LABELS_PLACEMENT then g
  else g.setEdgeProp edge CoreOptions.EDGE_LABELS_PLACEMENT .center

/-- Pure `ElkUtil.configureWithDefaultValues(element)` dispatching on the element kind
(labels are left unchanged). -/
def configureWithDefaultValues (g : ElkGraph) : ElementId → ElkGraph
  | .node n => configureNodeWithDefaultValues g n
  | .port p => configurePortWithDefaultValues g p
  | .edge e => configureEdgeWithDefaultValues g e
  | .label _ => g

/-- Pure `ElkUtil.configureDefaultsRecursively(graph)`. -/
partial def configureDefaultsRecursively (g : ElkGraph) (graph : NodeId) : ElkGraph := Id.run do
  let n := g.node graph
  let mut g := g
  for c in n.children do
    g := configureNodeWithDefaultValues g c
    g := configureDefaultsRecursively g c
  for p in n.ports do
    g := configurePortWithDefaultValues g p
  for e in n.containedEdges do
    g := configureEdgeWithDefaultValues g e
  return g

/-- Pure `ElkUtil.createIdentifier(element)`. -/
def createIdentifier (g : ElkGraph) (el : ElementId) : ElkGraph :=
  let identifier := some (generatedIdentifier el)
  match el with
  | .node n => g.modifyNode n fun x => { x with identifier }
  | .edge e => g.modifyEdge e fun x => { x with identifier }
  | .port p => g.modifyPort p fun x => { x with identifier }
  | .label l => g.modifyLabel l fun x => { x with identifier }

end Pure

/-! ## `ElkM` mutators -/

/-- Rust `{:.1}` formatting for the sizing trace. -/
private def fmt1 (x : Float) : String :=
  if x.isNaN || x.isInf then Float.toRustDisplay x
  else
    let tenths := (x * 10.0).round
    let neg := tenths < 0.0
    let n := (tenths.abs).toUInt64.toNat
    let s := s!"{n / 10}.{n % 10}"
    if neg && n != 0 then "-" ++ s else s

/-- `ElkUtil.resizeNode(node, newWidth, newHeight, movePorts, moveLabels)`: resizes the node
(respecting its minimum size), moves its ports and labels, fixes its size constraints and
returns the `(widthRatio, heightRatio)` scale. -/
def resizeNodeWith (node : NodeId) (newWidth newHeight : Float) (movePorts moveLabels : Bool) : ElkM KVector := do
  LayoutMetaDataService.ensureInitialized
  let oldSize := (← ElkM.getNode node).size
  let r ← modifyGet fun g => let (g, r) := Pure.resizeNodeWith g node newWidth newHeight movePorts moveLabels; (r, g)
  if ElkTrace.global.sizing then
    let newSize := (← ElkM.getNode node).size
    IO.eprintln s!"TRACE resize_node_with: old=({fmt1 oldSize.x},{fmt1 oldSize.y}) input=({fmt1 newWidth},{fmt1 newHeight}) new=({fmt1 newSize.x},{fmt1 newSize.y})"
  return r

/-- `ElkUtil.resizeNode(node)`: computes the size required by the ports (if `PORTS` is a size
constraint) and resizes; `none` if the node has a fixed size. -/
def resizeNode (node : NodeId) : ElkM (Option KVector) := do
  LayoutMetaDataService.ensureInitialized
  let sizeConstraint := ((← ElkM.getNode node).props.get CoreOptions.NODE_SIZE_CONSTRAINTS).getD SizeConstraint.fixed
  if sizeConstraint.isEmpty then return none
  let (w, h) ← modifyGet fun g => let (g, w, h) := Pure.resizeNodePortSizes g node; ((w, h), g)
  return some (← resizeNodeWith node w h true true)

/-- `ElkUtil.applyConfiguredNodeScaling(node)`. -/
def applyConfiguredNodeScaling (node : NodeId) : ElkM Unit := do
  LayoutMetaDataService.ensureInitialized
  modify (Pure.applyConfiguredNodeScaling · node)

/-- `ElkUtil.computeChildAreaDimensions(node)`. -/
def computeChildAreaDimensions (node : NodeId) : ElkM Unit := do
  LayoutMetaDataService.ensureInitialized
  modify (Pure.computeChildAreaDimensions · node)

/-- `ElkUtil.translate(parent, xoffset, yoffset)`. -/
def translateNode (parent : NodeId) (xoffset yoffset : Float) : ElkM Unit :=
  modify (Pure.translateNode · parent xoffset yoffset)

/-- `ElkUtil.translate(edge, xoffset, yoffset)`. -/
def translateEdge (edge : EdgeId) (xoffset yoffset : Float) : ElkM Unit :=
  modify (Pure.translateEdge · edge xoffset yoffset)

/-- `ElkUtil.translate(section, xoffset, yoffset)`. -/
def translateSection (s : SectionId) (xoffset yoffset : Float) : ElkM Unit :=
  modify (Pure.translateSection · s xoffset yoffset)

/-- `ElkUtil.translate(parent, newSize, oldSize)`. -/
def translateNodeWithSizes (parent : NodeId) (newSize oldSize : KVector) : ElkM Unit := do
  LayoutMetaDataService.ensureInitialized
  modify (Pure.translateNodeWithSizes · parent newSize oldSize)

/-- `ElkUtil.applyVectorChain(vectorChain, section)`; throws `IllegalArgumentException` for
chains with fewer than two points. -/
def applyVectorChain (chain : KVectorChain) (s : SectionId) : ElkM Unit := do
  if chain.size < 2 then throwIllegalArgument vectorChainTooShortMessage
  modify fun g => match Pure.applyVectorChain g chain s with
    | .ok g => g
    | .error _ => g

/-- `ElkUtil.configureWithDefaultValues(element)`. -/
def configureWithDefaultValues (el : ElementId) : ElkM Unit := do
  LayoutMetaDataService.ensureInitialized
  modify (Pure.configureWithDefaultValues · el)

/-- `ElkUtil.configureDefaultsRecursively(graph)`. -/
def configureDefaultsRecursively (graph : NodeId) : ElkM Unit := do
  LayoutMetaDataService.ensureInitialized
  modify (Pure.configureDefaultsRecursively · graph)

/-- `ElkUtil.createIdentifier(element)`. -/
def createIdentifier (el : ElementId) : ElkM Unit := modify (Pure.createIdentifier · el)

/-! ## Visitors -/

/-- `ElkUtil.applyVisitors(element, visitors)` (private recursion): all visitors visit the
element, then its labels, then (for nodes) its ports, children and contained edges. -/
partial def applyVisitorsToElement (el : ElementId) (visitors : Array GraphElementVisitor) : ElkM Unit := do
  for v in visitors do
    v.visit el
  let labels ← ElkM.withGraph (·.labelsOf el)
  for l in labels do
    applyVisitorsToElement (.label l) visitors
  if let .node n := el then
    let node ← ElkM.getNode n
    for p in node.ports do
      applyVisitorsToElement (.port p) visitors
    for c in node.children do
      applyVisitorsToElement (.node c) visitors
    for e in node.containedEdges do
      applyVisitorsToElement (.edge e) visitors

/-- `ElkUtil.applyVisitors(graph, visitors...)`: visits the root node and all its
descendants (labels, ports, children, edges) in the reference order. -/
def applyVisitors (graph : NodeId) (visitors : Array GraphElementVisitor) : ElkM Unit :=
  applyVisitorsToElement (.node graph) visitors

/-- `ElkUtil.applyVisitorsWithValidation(graph, visitors...)`: like `applyVisitors`, then
collects the issues of all validating visitors and fails with a
`GraphValidationException` if any issue is an error. -/
def applyVisitorsWithValidation (graph : NodeId) (visitors : Array GraphElementVisitor) :
    ElkM (Except GraphValidationException Unit) := do
  applyVisitors graph visitors
  let mut allIssues : Array GraphIssue := #[]
  for v in visitors do
    if let some issues ← v.getIssues then
      allIssues := allIssues ++ issues
  if allIssues.any (·.severity == .error) then
    let g ← get
    let mut message := ""
    for issue in allIssues do
      if !message.isEmpty then message := message.push '\n'
      message := message ++ s!"{issue.severity}: {issue.message}"
      message := message ++ "\n\tat "
      message := match issue.element with
        | some el => printElementPathInto g el message
        | none => message ++ "Root"
    return .error { message, issues := allIssues }
  return .ok ()

end ElkUtil

end Elk.Core.Util
