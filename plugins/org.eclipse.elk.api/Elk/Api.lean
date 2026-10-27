import Elk.Json
/-! Facade of elk-lean: algorithm registration and the elkjs-compatible string API (filled in Phase 2). -/
namespace Elk.Api
/-- elk-lean package version. -/
def version : String := "0.12.0"
/-- Reference ELK / elkjs version. -/
def elkVersion : String := "0.12.0"
end Elk.Api
