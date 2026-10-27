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

/-- The enum choices elk-rs reports for this option type (`enum_choices` in
`layered_meta_data_provider.rs`: `to_upper_snake` of the Rust variant names). They differ from
the Java constant names for the four directed alignments (`LEFT_UP` vs. `LEFTUP`); the
metadata provider uses this list so that the option metadata matches the oracle. Parsing is
unaffected (both spellings normalise to `LEFTUP`). -/
def rustChoiceNames : Array String :=
  #["NONE", "LEFT_UP", "RIGHT_UP", "LEFT_DOWN", "RIGHT_DOWN", "BALANCED"]

end FixedAlignment

end Elk.Alg.Layered.Options
