import Elk.Graph.Enum
/-!
# `org.eclipse.elk.alg.layered.options.FixedAlignment`

Port of `options/fixed_alignment.rs` (elk-rs) and `FixedAlignment.java`.
-/
namespace Elk.Alg.Layered.Options

/-- `org.eclipse.elk.alg.layered.options.FixedAlignment`: Layout option for the choice of candidates
in the Brandes & Köpf node placement. -/
elk_enum FixedAlignment := none (leftUp "LEFTUP") (rightUp "RIGHTUP") (leftDown "LEFTDOWN") (rightDown "RIGHTDOWN") balanced

namespace FixedAlignment

/-- The enum choices of the option metadata: the Java constant names (`FixedAlignment.values()`),
which ELK Java's JSON export and `elk options` print and which `elk convert` writes. elk-rs
reports `LEFT_UP` / `RIGHT_UP` / `LEFT_DOWN` / `RIGHT_DOWN` instead (`to_upper_snake` of its Rust
variant names, an oracle deviation that was followed until 2026-11-02); parsing accepts both
spellings (`ofNameLoose` normalises to `LEFTUP`). -/
def javaChoiceNames : Array String :=
  #["NONE", "LEFTUP", "RIGHTUP", "LEFTDOWN", "RIGHTDOWN", "BALANCED"]

end FixedAlignment

end Elk.Alg.Layered.Options
