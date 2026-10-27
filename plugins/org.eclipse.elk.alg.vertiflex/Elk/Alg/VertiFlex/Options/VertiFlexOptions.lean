import Elk.Core.Options
import Elk.Alg.VertiFlex.EdgeRoutingStrategy
/-!
# `org.eclipse.elk.alg.vertiflex.options.VertiFlexOptions`

Port of `vertiflex_options.rs` (elk-rs): the option constants of the VertiFlex algorithm. The
core options it re-exports are aliases of the `CoreOptions` constants.
-/
namespace Elk.Alg.VertiFlex.Options

open Elk Elk.Graph Elk.Core.Math Elk.Core.Options

namespace VertiFlexOptions

/-- `VertiFlexOptions.ALGORITHM_ID`. -/
def ALGORITHM_ID : String := "org.eclipse.elk.vertiflex"

/-- `VertiFlexOptions.VERTICAL_CONSTRAINT`: no default value. -/
def VERTICAL_CONSTRAINT : Property Float :=
  Property.mk' "org.eclipse.elk.vertiflex.verticalConstraint"

/-- `VertiFlexOptions.LAYOUT_STRATEGY`: default `STRAIGHT`. -/
def LAYOUT_STRATEGY : Property EdgeRoutingStrategy :=
  Property.withDefault "org.eclipse.elk.vertiflex.layoutStrategy" EdgeRoutingStrategy.straight

/-- `VertiFlexOptions.LAYER_DISTANCE`: default `50.0`. -/
def LAYER_DISTANCE : Property Float :=
  Property.withDefault "org.eclipse.elk.vertiflex.layerDistance" 50.0

/-- `VertiFlexOptions.CONSIDER_NODE_MODEL_ORDER`: default `true`. -/
def CONSIDER_NODE_MODEL_ORDER : Property Bool :=
  Property.withDefault "org.eclipse.elk.vertiflex.considerNodeModelOrder" true

/-- `VertiFlexOptions.SPACING_NODE_NODE`. -/
def SPACING_NODE_NODE : Property Float := CoreOptions.SPACING_NODE_NODE
/-- `VertiFlexOptions.PADDING`. -/
def PADDING : Property ElkPadding := CoreOptions.PADDING
/-- `VertiFlexOptions.INTERACTIVE`. -/
def INTERACTIVE : Property Bool := CoreOptions.INTERACTIVE
/-- `VertiFlexOptions.PORT_CONSTRAINTS`. -/
def PORT_CONSTRAINTS : Property PortConstraints := CoreOptions.PORT_CONSTRAINTS
/-- `VertiFlexOptions.EDGE_LABELS_INLINE`. -/
def EDGE_LABELS_INLINE : Property Bool := CoreOptions.EDGE_LABELS_INLINE
/-- `VertiFlexOptions.OMIT_NODE_MICRO_LAYOUT`. -/
def OMIT_NODE_MICRO_LAYOUT : Property Bool := CoreOptions.OMIT_NODE_MICRO_LAYOUT
/-- `VertiFlexOptions.MARGINS`. -/
def MARGINS : Property ElkMargin := CoreOptions.MARGINS

end VertiFlexOptions

end Elk.Alg.VertiFlex.Options
