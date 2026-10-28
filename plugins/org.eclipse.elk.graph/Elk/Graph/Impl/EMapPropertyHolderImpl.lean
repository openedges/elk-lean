import Elk.Graph.Monad
/-!
# `org.eclipse.elk.graph.impl.EMapPropertyHolderImpl` (default storing `getProperty`)

Java's `EMapPropertyHolderImpl.getProperty(property)` (and `MapPropertyHolder.getProperty`) returns the
stored value or, when the option is unset (or a stored `LayoutOptionProxy` cannot be parsed), the
property's default; if that default is `Cloneable` (`ElkPadding`, `ElkMargin`, `KVector`,
`KVectorChain`, `EnumSet`, lists — `Property.getDefault` hands out a clone registered with
`ElkReflect`) it is **stored on the element** as a side effect. A later read of the same option
through another property constant with a different default then sees the stored value: e.g. the
engine's `CoreOptions.PADDING` read of a top-down layout node (12) before its algorithm reads
`ForceOptions.PADDING` (50), or rectangle packing's `RectPackingOptions.PADDING` before its
`BoxLayoutProvider` fallback.

`PropertyMap.get` is the read of an immutable default (Java `Double`, `Integer`, `Boolean`, enum);
`getNodePropSticky` is used at the Java read sites of cloneable options whose defaults differ between
property constants (agent OPT).
-/
namespace Elk.Graph

namespace ElkM

/-- `ElkNode.getProperty(property)` for a property with a `Cloneable` default: the stored value, or
the default (stored on the node when present). -/
def getNodePropSticky {α : Type} [PropCodec α] (n : NodeId) (p : Property α) : ElkM (Option α) := do
  match ((← get).node n).props.get? p with
  | some v => return some v
  | none =>
    match p.default with
    | some d =>
      setNodeProp n p d
      return some d
    | none => return none

end ElkM

end Elk.Graph
