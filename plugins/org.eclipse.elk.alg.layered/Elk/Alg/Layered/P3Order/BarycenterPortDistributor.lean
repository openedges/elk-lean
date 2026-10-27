import Elk.Alg.Layered.P3Order.NodeRelativePortDistributor
import Elk.Alg.Layered.P3Order.LayerTotalPortDistributor
/-!
# elk-rs `p3order/barycenter_port_distributor.rs` (no Java counterpart)

The `BarycenterPortDistributor` trait: the view of a barycenter port distributor that the
barycenter heuristics use (Java passes the `AbstractBarycenterPortDistributor` itself). Since
the distributor state lives behind `IO.Ref`s, the record built from one distributor shares
that state with its `SweepPortDistributor` view, which is what the `Arc<Mutex<_>>` sharing of
the `GraphInfoHolder`'s `Shared*PortDistributor`s amounts to.
-/
namespace Elk.Alg.Layered.P3Order

open Elk.Alg.Layered.Graph Elk.Alg.Layered.Options Elk.Alg.Layered.P3Order.Counting

/-- `BarycenterPortDistributor` (trait). -/
structure BarycenterPortDistributor where
  /-- The `IInitializable` part. -/
  initializable : Initializable
  /-- `calculate_port_ranks(layer, port_type)`. -/
  calculatePortRanks : Array LNodeId → PortType → LayeredM Unit
  /-- `port_ranks()` (a copy). -/
  portRanks : BaseIO (Array Float)
  /-- `port_ranks()` as the distributor's (unboxed) array. -/
  portRanksF : BaseIO FloatArray
  /-- `set_snapshot(snapshot)` (default: ignored). -/
  setSnapshot : CrossMinSnapshot → BaseIO Unit := fun _ => pure ()

/-- `impl BarycenterPortDistributor for AbstractBarycenterPortDistributor`. -/
def AbstractBarycenterPortDistributor.toBarycenterPortDistributor (d : AbstractBarycenterPortDistributor) :
    BarycenterPortDistributor where
  initializable := d.initializable
  calculatePortRanks := d.calculatePortRanks
  portRanks := d.portRanks
  portRanksF := d.portRanksF
  setSnapshot := d.setSnapshot

/-- `impl BarycenterPortDistributor for NodeRelativePortDistributor`. -/
def NodeRelativePortDistributor.toBarycenterPortDistributor (d : NodeRelativePortDistributor) :
    BarycenterPortDistributor :=
  d.inner.toBarycenterPortDistributor

/-- `impl BarycenterPortDistributor for LayerTotalPortDistributor`. -/
def LayerTotalPortDistributor.toBarycenterPortDistributor (d : LayerTotalPortDistributor) :
    BarycenterPortDistributor :=
  d.inner.toBarycenterPortDistributor

end Elk.Alg.Layered.P3Order
