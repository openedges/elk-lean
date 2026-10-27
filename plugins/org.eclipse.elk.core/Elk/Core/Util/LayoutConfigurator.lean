import Elk.Graph.Monad
import Elk.Core.Data.LayoutMetaDataService
import Elk.Core.Util.GraphElementVisitor
/-!
# `org.eclipse.elk.core.LayoutConfigurator`

Applies options to graph elements, per element (`configureElement`) and per
element class (`configureClass`), filtered by option filters. Elements are keyed
by their arena id (elk-rs keys them by pointer). The configurator is an
immutable value: `configure*` take an update function for the property map and
return the new configurator.

Not ported: `ADD_LAYOUT_CONFIG` (a `Property<LayoutConfigurator>`; property values
cannot hold configurators, see the TODO below).
-/
namespace Elk.Core.Util

open Elk Elk.Graph Elk.Core.Data

/-- The element classes options can be configured for (`Class<? extends EObject>` keys). -/
inductive LayoutConfiguratorClass where
  | graphElement
  | shape
  | label
  | connectableShape
  | node
  | port
  | edge
  deriving BEq, Hashable, Repr, Inhabited, DecidableEq

/-- `LayoutConfigurator.IOptionFilter`: `accept(element, property)`. -/
abbrev OptionFilter := ElementId → String → ElkM Bool

/-- `LayoutConfigurator.IPropertyHolderOptionFilter`: `accept(holder, property)`. -/
abbrev PropertyHolderOptionFilter := PropertyMap → String → Bool

/-- `org.eclipse.elk.core.LayoutConfigurator`. -/
structure LayoutConfigurator where
  elementOptionMap : Array (ElementId × PropertyMap) := #[]
  classOptionMap : Array (LayoutConfiguratorClass × PropertyMap) := #[]
  clearLayout : Bool := false
  optionFilters : Array OptionFilter := #[]
  deriving Inhabited

namespace LayoutConfigurator

-- TODO(LayoutConfigurator): `ADD_LAYOUT_CONFIG` (`org.eclipse.elk.addLayoutConfig`) needs a
-- `PropValue` able to hold a configurator; it is only used by the diagram layout engine.

/-- `LayoutConfigurator.NO_OVERWRITE`: accepts options the element does not have yet. -/
def NO_OVERWRITE : OptionFilter := fun el id => do
  return !(((← get).props el).hasId id)

/-- `LayoutConfigurator.NO_OVERWRITE_HOLDER`. -/
def NO_OVERWRITE_HOLDER : PropertyHolderOptionFilter := fun holder id => !holder.hasId id

/-- `LayoutConfigurator.OPTION_TARGET_FILTER`: accepts options whose targets include the
element kind (hierarchical nodes also accept `PARENTS` options); unknown options pass. -/
def OPTION_TARGET_FILTER : OptionFilter := fun el id => do
  let some optionData ← LayoutMetaDataService.getOptionData id | return true
  let targets := optionData.targets
  match el with
  | .node n =>
    if (← ElkM.getNode n).isHierarchical then
      return targets.contains .nodes || targets.contains .parents
    else return targets.contains .nodes
  | .edge _ => return targets.contains .edges
  | .port _ => return targets.contains .ports
  | .label _ => return targets.contains .labels

/-- `new LayoutConfigurator()`. -/
def new : LayoutConfigurator := {}

/-- `isClearLayout()`. -/
def isClearLayout (c : LayoutConfigurator) : Bool := c.clearLayout

/-- `setClearLayout(doClearLayout)`. -/
def setClearLayout (c : LayoutConfigurator) (doClearLayout : Bool) : LayoutConfigurator :=
  { c with clearLayout := doClearLayout }

/-- `addFilter(filter)`. -/
def addFilter (c : LayoutConfigurator) (filter : OptionFilter) : LayoutConfigurator :=
  { c with optionFilters := c.optionFilters.push filter }

/-- `getFilters()`. -/
def filters (c : LayoutConfigurator) : Array OptionFilter := c.optionFilters

/-- `configure(element)`: updates the options stored for the element. -/
def configureElement (c : LayoutConfigurator) (el : ElementId) (f : PropertyMap → PropertyMap) : LayoutConfigurator :=
  match c.elementOptionMap.findIdx? (·.1 == el) with
  | some i => { c with elementOptionMap := c.elementOptionMap.modify i fun (k, m) => (k, f m) }
  | none => { c with elementOptionMap := c.elementOptionMap.push (el, f {}) }

/-- `configure(ElkNode)`. -/
def configureNode (c : LayoutConfigurator) (n : NodeId) (f : PropertyMap → PropertyMap) : LayoutConfigurator :=
  c.configureElement (.node n) f
/-- `configure(ElkPort)`. -/
def configurePort (c : LayoutConfigurator) (p : PortId) (f : PropertyMap → PropertyMap) : LayoutConfigurator :=
  c.configureElement (.port p) f
/-- `configure(ElkEdge)`. -/
def configureEdge (c : LayoutConfigurator) (e : EdgeId) (f : PropertyMap → PropertyMap) : LayoutConfigurator :=
  c.configureElement (.edge e) f
/-- `configure(ElkLabel)`. -/
def configureLabel (c : LayoutConfigurator) (l : LabelId) (f : PropertyMap → PropertyMap) : LayoutConfigurator :=
  c.configureElement (.label l) f

/-- `getProperties(element)`. -/
def propertiesElement? (c : LayoutConfigurator) (el : ElementId) : Option PropertyMap :=
  (c.elementOptionMap.find? (·.1 == el)).map (·.2)

/-- `configure(elementClass)`: updates the options stored for an element class. -/
def configureClass (c : LayoutConfigurator) (cls : LayoutConfiguratorClass) (f : PropertyMap → PropertyMap) : LayoutConfigurator :=
  match c.classOptionMap.findIdx? (·.1 == cls) with
  | some i => { c with classOptionMap := c.classOptionMap.modify i fun (k, m) => (k, f m) }
  | none => { c with classOptionMap := c.classOptionMap.push (cls, f {}) }

/-- `getProperties(elementClass)`. -/
def propertiesClass? (c : LayoutConfigurator) (cls : LayoutConfiguratorClass) : Option PropertyMap :=
  (c.classOptionMap.find? (·.1 == cls)).map (·.2)

/-- `applyProperties(element, properties)` (protected): copies all accepted options. -/
def applyProperties (c : LayoutConfigurator) (el : ElementId) (properties : PropertyMap) : ElkM Unit := do
  for (key, value) in properties.entries do
    let mut accept := true
    for filter in c.optionFilters do
      if !(← filter el key.id) then
        accept := false
        break
    if !accept then continue
    modify (·.modifyProps el (·.setRaw key value))

/-- `findClassOptions(element)`: the class options in the order graph element, shape,
connectable shape, node/port/label (or edge). -/
def findClassOptions (c : LayoutConfigurator) (el : ElementId) : PropertyMap := Id.run do
  let addClass (m : PropertyMap) (cls : LayoutConfiguratorClass) : PropertyMap :=
    match c.propertiesClass? cls with
    | some h => m.copyFrom h
    | none => m
  let combined := addClass {} .graphElement
  match el with
  | .label _ => return addClass (addClass combined .shape) .label
  | .node _ => return addClass (addClass (addClass combined .shape) .connectableShape) .node
  | .port _ => return addClass (addClass (addClass combined .shape) .connectableShape) .port
  | .edge _ => return addClass combined .edge

/-- `overrideWith(other)`: merges the other configurator's options into this one and takes
its `clearLayout` flag and filters. -/
def overrideWith (c other : LayoutConfigurator) : LayoutConfigurator := Id.run do
  let mut c := c
  for (key, holder) in other.elementOptionMap do
    c := c.configureElement key (·.copyFrom holder)
  for (key, holder) in other.classOptionMap do
    c := c.configureClass key (·.copyFrom holder)
  return { c with clearLayout := other.clearLayout, optionFilters := other.optionFilters }

/-- `visit(element)`: clears the element's options if requested, then applies the class
options overridden by the element options. -/
def visit (c : LayoutConfigurator) (el : ElementId) : ElkM Unit := do
  if c.clearLayout then modify (·.modifyProps el PropertyMap.clear)
  let mut combined := c.findClassOptions el
  if let some holder := c.propertiesElement? el then
    combined := combined.copyFrom holder
  c.applyProperties el combined

/-- The configurator as an `IGraphElementVisitor`. -/
def toVisitor (c : LayoutConfigurator) : GraphElementVisitor := { visit := c.visit }

end LayoutConfigurator

end Elk.Core.Util
