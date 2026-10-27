import Elk.Graph.Enum
/-!
# `org.eclipse.elk.alg.mrtree.options.CompactionMode`

Port of `options/compaction_mode.rs` (elk-rs) and `CompactionMode.java` (same constants, same ordinal order).
-/
namespace Elk.Alg.MrTree.Options

/-- `org.eclipse.elk.alg.mrtree.options.CompactionMode`: the compaction mode (declared by the Java plugin, not used by the algorithm). -/
elk_enum CompactionMode := none levelPreserving aggressive

end Elk.Alg.MrTree.Options
