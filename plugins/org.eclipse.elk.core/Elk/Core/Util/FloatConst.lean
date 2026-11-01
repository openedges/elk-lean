import Elk.Core.Util.FastFloat
/-!
# `Elk.Core.Util.FloatConst` -- shared `Float` literal constants (PLAN section 7.1 idioms 8 and 17)

Float literals inside branches, loops and specialised code are not always extracted into closed
terms: the compiler shares a literal's `Nat`/`Bool` arguments with unrelated variables (CSE) and
then parses the literal on every evaluation (`FastFloat.ofScientificImpl`). A top-level constant
is initialised once and every use is a load of a global. Hot modules therefore use the constants
below instead of writing `0.0`, `2.0`, ... inline; modules keep their own `private def fl...`
only for values that no other module uses.

**These must stay top-level `def`s** (not `@[inline]`, not `abbrev`, not `@[reducible]`): inlining
would put the literal back into the user's code and defeat the purpose. They are declared with
the same literal syntax the modules used before, so the values are bit-identical.
Check with `sh scripts/perf/scan_generated_c.sh` (`ofSciImpl` must not grow).

Only values that were defined (privately, with the same name and literal) in two or more modules
live here.
-/
namespace Elk.Core.Util.FloatConst

/-- The `Float` constant `-2147483648.0`. -/
def flIntMin : Float := -2147483648.0

/-- The `Float` constant `0.0`. -/
def fl0p0 : Float := 0.0

/-- The `Float` constant `0.0001`. -/
def fl0p0001 : Float := 0.0001

/-- The `Float` constant `0.001`. -/
def fl0p001 : Float := 0.001

/-- The `Float` constant `0.5`. -/
def fl0p5 : Float := 0.5

/-- The `Float` constant `1.0`. -/
def fl1p0 : Float := 1.0

/-- The `Float` constant `1.6`. -/
def fl1p6 : Float := 1.6

/-- The `Float` constant `2.0`. -/
def fl2p0 : Float := 2.0

/-- The `Float` constant `4.0`. -/
def fl4p0 : Float := 4.0

/-- The `Float` constant `5.0`. -/
def fl5p0 : Float := 5.0

/-- The `Float` constant `8.0`. -/
def fl8p0 : Float := 8.0

/-- The `Float` constant `10.0`. -/
def fl10p0 : Float := 10.0

/-- The `Float` constant `20.0`. -/
def fl20p0 : Float := 20.0

/-- The `Float` constant `80.0`. -/
def fl80p0 : Float := 80.0

/-- The `Float` constant `100.0`. -/
def fl100p0 : Float := 100.0

/-- The `Float` constant `2147483647.0`. -/
def flIntMax : Float := 2147483647.0

/-- The `Float` constant `1e16`. -/
def fl1e16 : Float := 1e16

end Elk.Core.Util.FloatConst
