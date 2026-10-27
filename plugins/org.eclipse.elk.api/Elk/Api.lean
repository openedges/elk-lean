import Elk.Json
import Elk.Text
import Elk.Alg.Layered
import Elk.Alg.TopdownPacking
import Elk.Alg.Force
import Elk.Alg.Disco
import Elk.Alg.Spore
import Elk.Alg.VertiFlex
import Elk.Alg.Radial
import Elk.Api.LayoutApi
/-! Facade of elk-lean: algorithm registration and the elkjs-compatible string API. -/
namespace Elk.Api
/-- elk-lean package version. -/
def version : String := "0.12.0"
/-- Reference ELK / elkjs version. -/
def elkVersion : String := "0.12.0"
end Elk.Api
