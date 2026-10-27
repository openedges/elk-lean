import Std.Data.HashMap
import Elk.Alg.MrTree.Graph.TArena
/-!
# `org.eclipse.elk.alg.mrtree.intermediate.FanProcessor`

Port of `intermediate/fan_processor.rs` (elk-rs): computes the `FAN` (maximal number of descendants
of a node on one level) and `DESCENDANTS` (number of nodes in the subtree, the node included) of
every node from hierarchical identifier strings (`ID`). Level by level, starting at the first `ROOT`
node, every node gets the identifier `<parent id><index>` where the index within the sibling group
is zero padded to `floor(log10(level size)) + 1` digits; the children temporarily carry the parent's
identifier. The prefixes of all identifiers of a level are counted (Rust iterates only
`0 .. last_id.len() - digits` prefix lengths, using the last identifier of the level) and merged
into the global fan (maximum) and descendant (sum) maps. The recursion of Rust over the levels is a
loop here; the iteration order of the Rust `HashMap`s does not influence the result.
-/
namespace Elk.Alg.MrTree.Intermediate

open Elk.Core.Util Elk.Alg.MrTree.Graph

namespace FanProcessor

/-- `FanProcessor::format_right(value, len)`: `value` left padded with `0` to `len` characters. -/
def formatRight (value : Int) (len : Nat) : String := Id.run do
  let mut s := toString value
  while s.length < len do
    s := "0" ++ s
  return s

/-- One level of `calculate_fan`: assigns the identifiers of the level, returns the next level and
the updated global fan and descendant maps. -/
private def calculateFanLevel (currentLevel : Array TNodeId) (gloFan gloDesc : Std.HashMap String Int) :
    MrTreeM (Array TNodeId × Std.HashMap String Int × Std.HashMap String Int) := do
  let mut nextLevel : Array TNodeId := #[]
  let digits := (Float.ofNat currentLevel.size).log10.floor.toUInt64.toNat + 1
  let mut lastParentId : Option String := none
  let mut index : Int := 0
  let mut lastId := ""
  let mut cachedIds : Array String := #[]
  for node in currentLevel do
    let parentId := (← MrTreeM.getNode node).internal.idString
    if lastParentId != some parentId then
      lastParentId := some parentId
      index := 0
    let id := if parentId.isEmpty then formatRight index digits else parentId ++ formatRight index digits
    index := index + 1
    lastId := id
    cachedIds := cachedIds.push id
    MrTreeM.modifyNode node fun n => { n with internal.idString := id }
    for child in (← MrTreeM.children node) do
      MrTreeM.modifyNode child fun n => { n with internal.idString := lastId }
      nextLevel := nextLevel.push child
  -- prefix computation
  let mut localFan : Std.HashMap String Int := {}
  if digits > 0 && lastId.length >= digits then
    for i in [0:lastId.length - digits] do
      for id in cachedIds do
        let pre := String.ofList (id.toList.take (i + 1))
        localFan := localFan.insert pre (localFan.getD pre 0 + 1)
  let (gloFan, gloDesc) := localFan.fold (init := (gloFan, gloDesc)) fun (fan, desc) key value =>
    let desc := desc.insert key (desc.getD key 0 + value)
    let fan := if fan.getD key 0 < value then fan.insert key value else fan
    (fan, desc)
  return (nextLevel, gloFan, gloDesc)

/-- `FanProcessor::process`. -/
def process (graph : TGraphId) (monitor : ProgressMonitor) : MrTreeM Unit := do
  discard <| monitor.begin "Processor compute fanout" 1.0
  let nodes := (← MrTreeM.getGraph graph).nodes
  let a ← get
  let root := nodes.find? fun n => (a.node n).internal.root
  let mut gloFan : Std.HashMap String Int := {}
  let mut gloDesc : Std.HashMap String Int := {}
  let mut currentLevel : Array TNodeId := match root with
    | some r => #[r]
    | none => #[]
  while !currentLevel.isEmpty do
    let (next, fan, desc) ← calculateFanLevel currentLevel gloFan gloDesc
    currentLevel := next
    gloFan := fan
    gloDesc := desc
  for node in (← MrTreeM.getGraph graph).nodes do
    MrTreeM.modifyNode node fun n =>
      let key := n.internal.idString
      { n with internal.fan := gloFan.getD key 0, internal.descendants := gloDesc.getD key 0 + 1 }
  monitor.done

/-- The `FanProcessor` (`IntermediateProcessorStrategy.FAN_PROC`). -/
def processor : TreeProcessor := { name := "FanProcessor", process }

end FanProcessor

end Elk.Alg.MrTree.Intermediate
