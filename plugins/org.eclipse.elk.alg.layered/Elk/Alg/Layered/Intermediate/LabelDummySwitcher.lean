import Elk.Graph
/-!
# `org.eclipse.elk.alg.layered.intermediate.LabelDummySwitcher` (property only)

Port of the public `INCLUDE_LABEL` property of `LabelDummySwitcher.java` (elk-rs
`intermediate/label_dummy_switcher.rs`, `pub static INCLUDE_LABEL`). It is needed by
`ElkGraphLayoutTransferrer`, which copies the value from each edge `LLabel` to its `ElkLabel`.

The processor itself (`LabelDummySwitcher.process`, the label dummy placement strategies, layer
widths, node swapping) is added by the intermediate processor task. Its `assignLayer` step sets
`INCLUDE_LABEL := true` on the `props` of every `LLabel` represented by the placed label dummy
(Java `label.setProperty(INCLUDE_LABEL, true)`).

`INCLUDE_LABEL` is not an `InternalProperties` constant: in Java/Rust it is an ordinary property
of the label's property map (and it is copied to the ElkGraph), so the Lean port keeps it in
`LLabel.props` / `ElkLabel.props` instead of a typed `LLabelInternals` field.
-/
namespace Elk.Alg.Layered.Intermediate

open Elk.Graph

namespace LabelDummySwitcher

/-- `LabelDummySwitcher.INCLUDE_LABEL` (elk-rs `INCLUDE_LABEL`): "A property to communicate
with the analyses that can be run on a graph." Id `edgelabelcenterednessanalysis.includelabel`,
default `false`; set to `true` on the labels represented by a label dummy whose layer was
assigned by the switcher. -/
def INCLUDE_LABEL : Property Bool :=
  Property.withDefault "edgelabelcenterednessanalysis.includelabel" false

end LabelDummySwitcher

end Elk.Alg.Layered.Intermediate
