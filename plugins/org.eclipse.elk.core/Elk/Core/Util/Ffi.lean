import Elk.Core.Util.FastFloat
/-!
Bindings to `plugins/org.eclipse.elk.core/c/elk_core_ffi.c`.
-/
namespace Elk.Core.Util

/-- Shortest round-trip decimal representation of a double, serde_json/ryu style
(`12.0`, `0.1`, `1e21`, `1.5e-7`). `NaN`, `inf`, `-inf` for non-finite values. -/
@[extern "elk_float_to_shortest"]
opaque Float.toShortest (x : Float) : String

/-- A finite double as the elk-rs oracle writes it into JSON (serde_json 1.0.149 / zmij):
shortest round-trip digits, positional for decimal exponents `-5..15`, otherwise `1e+21`,
`1.7976931348623157e+308`, `3e-6`. -/
@[extern "elk_float_to_json"]
opaque Float.toJsonNumber (x : Float) : String

/-- Seconds since the Unix epoch (`SystemTime::now().duration_since(UNIX_EPOCH)`). -/
@[extern "elk_unix_time"]
opaque unixTimeSecs : BaseIO Nat

/-- `%.17g` formatting (debug traces). -/
@[extern "elk_float_to_g17"]
opaque Float.toG17 (x : Float) : String

/-- Correctly rounded `strtod`. Returns NaN if the prefix is not a number.
Callers must validate the lexeme first. -/
@[extern "elk_strtod"]
opaque strtodUnchecked (s : @& String) : Float

end Elk.Core.Util
