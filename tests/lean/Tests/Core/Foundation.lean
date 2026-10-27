import Tests.Framework
/-! Tests for the Phase 1 foundation: Java helpers, sorting, Random, math, properties. -/
namespace Tests.Core.Foundation

open Tests Elk Elk.Core.Util Elk.Core.Math Elk.Graph

elk_enum Color := red green blueish (darkCyan "DARK_CYAN")

def javaSemantics : Suite := suite "core.util.java" do
  checkEq "toShortest 12.0" (Float.toShortest 12.0) "12.0"
  checkEq "toShortest 0.1" (Float.toShortest 0.1) "0.1"
  checkEq "toShortest 1e21" (Float.toShortest 1e21) "1e21"
  checkEq "toShortest 1.5e-7" (Float.toShortest 1.5e-7) "1.5e-7"
  checkEq "toShortest 1234.5" (Float.toShortest 1234.5) "1234.5"
  checkEq "toShortest -0.0" (Float.toShortest (-0.0)) "-0.0"
  checkEq "toRustDisplay 12.0" (Float.toRustDisplay 12.0) "12"
  checkEq "toRustDisplay 2.5" (Float.toRustDisplay 2.5) "2.5"
  checkFloat "parseFloat 0.1" ((parseFloat? "0.1").getD 0.0) 0.1
  checkFloat "parseFloat 1e3" ((parseFloat? "1e3").getD 0.0) 1000.0
  checkFloat "parseFloat -2.5E-2" ((parseFloat? "-2.5E-2").getD 0.0) (-0.025)
  checkNone "parseFloat junk" (parseFloat? "1.2.3")
  checkNone "parseFloat trailing" (parseFloat? "12 ")
  check "parseFloat inf" ((parseFloat? "inf").map (·.isInf) == some true)
  checkEq "parseInt32 42" ((parseInt32? "42").getD 0) 42
  checkEq "parseInt32 -7" ((parseInt32? "-7").getD 0) (-7)
  checkNone "parseInt32 overflow" (parseInt32? "2147483648")
  checkNone "parseInt32 float" (parseInt32? "1.0")
  checkEq "roundToInt 2.5" (Float.roundToInt 2.5) 3
  checkEq "roundToInt -2.5" (Float.roundToInt (-2.5)) (-3)
  checkEq "javaRound -2.5" (Float.javaRound (-2.5)) (-2)
  checkEq "toIntTrunc -3.7" (Float.toIntTrunc (-3.7)) (-3)
  checkEq "toIntTrunc NaN" (Float.toIntTrunc Float.nan) 0
  check "fmin NaN" (fmin Float.nan 1.0 == 1.0)
  check "javaMin NaN" (javaMin Float.nan 1.0).isNaN
  check "compareJava -0.0 < 0.0" (Float.compareJava (-0.0) 0.0 == .lt)
  check "compareJava NaN greatest" (Float.compareJava Float.nan Float.posInf == .gt)
  check "comparePartial NaN eq" (Float.comparePartial Float.nan 1.0 == .eq)
  checkFloat "toF32 0.1" (Float.toF32 0.1) 0.10000000149011612 1e-17
  checkEq "tdiv -7/2" (Int.tdiv (-7) 2) (-3)
  checkEq "tmod -7%2" (Int.tmod (-7) 2) (-1)
  checkEq "wrap32" (Int.wrap32 2147483648) (-2147483648)
  -- the `UInt64`-only bit comparisons/conversions agree with the `Int` formulations they replaced
  let refSigned (b : UInt64) : Int :=
    if b ≥ 0x8000000000000000 then (b.toNat : Int) - 0x10000000000000000 else (b.toNat : Int)
  let refTotal (a b : Float) : Ordering :=
    let key (x : Float) : Int :=
      let bits := x.toBits
      refSigned (if bits ≥ 0x8000000000000000 then bits ^^^ 0x7FFFFFFFFFFFFFFF else bits)
    compare (key a) (key b)
  let refJava (a b : Float) : Ordering :=
    if a < b then .lt else if a > b then .gt
    else compare (refSigned (if a.isNaN then 0x7ff8000000000000 else a.toBits))
      (refSigned (if b.isNaN then 0x7ff8000000000000 else b.toBits))
  let floats : Array Float := #[0.0, -0.0, 1.0, -1.0, 0.5, -2.5, 1e300, -1e300, 5e-324, -5e-324,
    Float.posInf, Float.negInf, Float.nan, -Float.nan, Float.ofBits 0x7ff0000000000001,
    Float.ofBits 0xfff8000000000001, 2147483647.0, 4294967296.0, -4294967296.0]
  for a in floats do
    for b in floats do
      check s!"compareTotal {a.toBits} {b.toBits}" (Float.compareTotal a b == refTotal a b)
      check s!"compareJava {a.toBits} {b.toBits}" (Float.compareJava a b == refJava a b)
  for bits in [(0 : UInt64), 1, 0x7FFFFFFF, 0x80000000, 0xFFFFFFFF, 0x100000000, 0x7FFFFFFFFFFFFFFF,
      0x8000000000000000, 0x8000000000000001, 0xFFFFFFFFFFFFFFFF] do
    checkEq s!"UInt64.toIntSigned {bits}" (UInt64.toIntSigned bits) (refSigned bits)
  for i in [(0 : Int), 1, -1, 2147483647, -2147483648, 4294967296, -4294967296, 9223372036854775807,
      -9223372036854775808, 18446744073709551615, 18446744073709551616, -18446744073709551617,
      123456789012345678901234567890, -123456789012345678901234567890] do
    checkEq s!"toUInt64Wrap {i}" (Int.toUInt64Wrap i) (UInt64.ofNat (Int.toNat (i.emod 0x10000000000000000)))
  for u in [(0 : UInt32), 1, 0x7FFFFFFF, 0x80000000, 0x80000001, 0xFFFFFFFF] do
    checkEq s!"UInt32.toIntSigned {u}" (UInt32.toIntSigned u)
      (if u ≥ 0x80000000 then (u.toNat : Int) - 0x100000000 else (u.toNat : Int))

def sorting : Suite := suite "core.util.sort" do
  let input : Array (Nat × Nat) := #[(3, 0), (1, 1), (3, 2), (2, 3), (1, 4), (3, 5), (0, 6)]
  let sorted := stableSort input (fun a b => compare a.1 b.1)
  checkEqR "stable order" (sorted.map (·.2)) #[6, 1, 4, 3, 0, 2, 5]
  let big := (Array.range 1000).map fun i => ((i * 7919) % 97, i)
  let sortedBig := stableSort big (fun a b => compare a.1 b.1)
  let mut ok := true
  for i in [1:sortedBig.size] do
    let a := sortedBig[i - 1]!
    let b := sortedBig[i]!
    if a.1 > b.1 || (a.1 == b.1 && a.2 > b.2) then ok := false
  check "stable sort 1000" ok
  checkEqR "empty" (stableSort (#[] : Array Nat) compare) #[]
  checkEqR "single" (stableSort #[5] compare) #[5]

def random : Suite := suite "core.util.random" do
  -- java.util.Random reference values
  let r := Random.ofInt 42
  let (i, r) := r.nextIntUnbounded
  checkEq "seed 42 nextInt()" i (-1170105035)
  let (d, _) := (Random.ofInt 42).nextDouble
  checkFloat "seed 42 nextDouble()" d 0.7275636800328681 1e-15
  let (b, _) := r.nextInt 100
  check "nextInt bound range" (b >= 0 && b < 100)
  let (p, _) := (Random.ofInt 7).nextInt 16
  check "nextInt power of two range" (p >= 0 && p < 16)
  let (l, _) := (Random.ofInt 42).nextLong
  checkEq "seed 42 nextLong()" l (-5025562857975149833)
  let (f, _) := (Random.ofInt 42).nextFloat
  checkFloat "seed 42 nextFloat()" f 0.7275636 1e-6

def math : Suite := suite "core.math" do
  let v : KVector := ⟨3.0, 4.0⟩
  checkFloat "length" v.length 5.0
  checkFloat "normalize x" v.normalize.x 0.6
  checkFloat "distance" (v.distance ⟨0.0, 0.0⟩) 5.0
  checkFloat "toRadians (1,0)" (KVector.mk 1.0 0.0).toRadians 0.0
  checkFloat "toRadians (0,1)" (KVector.mk 0.0 1.0).toRadians (Float.pi / 2.0) 1e-12
  checkFloat "toRadians (-1,0)" (KVector.mk (-1.0) 0.0).toRadians Float.pi 1e-12
  checkFloat "toRadians (0,-1)" (KVector.mk 0.0 (-1.0)).toRadians (3.0 * Float.pi / 2.0) 1e-12
  match KVector.parse "(1.5, 2)" with
  | .ok p => checkFloat "parse x" p.x 1.5; checkFloat "parse y" p.y 2.0
  | .error e => check s!"parse failed: {e}" false
  check "parse error" (KVector.parse "(1)" matches .error _)
  match KVectorChain.parse "(1,2; 3,4) [5 6]" with
  | .ok c => checkEq "chain size" c.size 3; checkFloat "chain last y" c.last!.y 6.0
  | .error e => check s!"chain parse failed: {e}" false
  let chain : KVectorChain := #[⟨0.0, 0.0⟩, ⟨10.0, 0.0⟩, ⟨10.0, 10.0⟩]
  checkFloat "totalLength" chain.totalLength 20.0
  checkFloat "pointOnLine 15 x" (chain.pointOnLine 15.0).x 10.0
  checkFloat "pointOnLine 15 y" (chain.pointOnLine 15.0).y 5.0
  checkFloat "pointOnLine -5 y" (chain.pointOnLine (-5.0)).y 5.0
  checkFloat "angleOnLine 15" (chain.angleOnLine 15.0) (Float.pi / 2.0) 1e-12
  let r1 : ElkRectangle := ⟨0, 0, 10, 10⟩
  let r2 : ElkRectangle := ⟨5, 5, 10, 10⟩
  check "intersects" (r1.intersects r2)
  checkFloat "union width" (r1.union r2).width 15.0
  checkEq "padding toString" (toString (ElkPadding.ofValues 1 2 3 4)) "[top=1,left=4,bottom=3,right=2]"

def enums : Suite := suite "graph.enum" do
  checkEq "javaName" (toString Color.blueish) "BLUEISH"
  checkEq "override" (toString Color.darkCyan) "DARK_CYAN"
  checkEq "ordinal" (ElkEnum.ordinal Color.green) 1
  checkEq "count" (ElkEnum.count (α := Color)) 4
  check "ofJavaName" ((ElkEnum.ofJavaName? "DARK_CYAN" : Option Color) == some .darkCyan)
  check "ofNameLoose dark-cyan" ((ElkEnum.ofNameLoose? "dark-cyan" : Option Color) == some .darkCyan)
  check "ofNameLoose darkCyan" ((ElkEnum.ofNameLoose? "darkCyan" : Option Color) == some .darkCyan)
  check "ofNameLoose ordinal" ((ElkEnum.ofNameLoose? "2" : Option Color) == some .blueish)
  check "ofNameLoose unknown" ((ElkEnum.ofNameLoose? "purple" : Option Color) == none)
  let s : EnumSet Color := EnumSet.of #[.red, .darkCyan]
  check "contains" (s.contains .red && !s.contains .green)
  checkEq "toJavaString" s.toJavaString "[RED, DARK_CYAN]"
  checkEq "size" s.size 2
  check "allOf" ((EnumSet.allOf : EnumSet Color).size == 4)
  check "parse?" ((EnumSet.parse? "[GREEN, blueish]" : Option (EnumSet Color)) == some (EnumSet.of #[.green, .blueish]))
  check "parse? empty" ((EnumSet.parse? "" : Option (EnumSet Color)) == some EnumSet.empty)
  check "parse? bad" ((EnumSet.parse? "GREEN, purple" : Option (EnumSet Color)) == none)
  check "ord" (compare Color.red Color.green == .lt)

def properties : Suite := suite "graph.properties" do
  let P_SPACING : Property Float := Property.withDefault "org.eclipse.elk.test.spacing" 20.0
  let P_COLOR : Property Color := Property.withDefault "org.eclipse.elk.test.color" .red
  let P_SET : Property (EnumSet Color) := Property.withDefault "org.eclipse.elk.test.set" EnumSet.empty
  let P_NAME : Property String := Property.mk' "org.eclipse.elk.test.name"
  let P_VEC : Property KVector := Property.mk' "org.eclipse.elk.test.vec"
  let P_PAD : Property ElkPadding := Property.mk' "org.eclipse.elk.test.pad"
  let m : PropertyMap := {}
  checkFloat "default" (m.get! P_SPACING) 20.0
  checkNone "no stored" (m.get? P_SPACING)
  check "has false" (!m.has P_SPACING)
  let m := m.set P_SPACING 5.0
  checkFloat "stored" (m.get! P_SPACING) 5.0
  check "has true" (m.has P_SPACING)
  let m := m.setOpt P_SPACING none
  check "removed" (!m.has P_SPACING)
  let m := m.setRawById "org.eclipse.elk.test.color" (.proxy "dark_cyan")
  check "proxy enum" (m.get P_COLOR == some .darkCyan)
  let m := m.setRawById "org.eclipse.elk.test.set" (.proxy "[RED,GREEN]")
  check "proxy enumset" (m.get P_SET == some (EnumSet.of #[.red, .green]))
  let m := m.setRawById "org.eclipse.elk.test.spacing" (.proxy "12.5")
  checkFloat "proxy float" (m.get! P_SPACING) 12.5
  let m := m.setRawById "org.eclipse.elk.test.name" (.proxy "hello")
  check "proxy string" (m.get P_NAME == some "hello")
  let m := m.setRawById "org.eclipse.elk.test.vec" (.proxy "(1,2)")
  check "proxy vector" (m.get P_VEC == some ⟨1.0, 2.0⟩)
  let m := m.setRawById "org.eclipse.elk.test.pad" (.proxy "[top=1,left=2,bottom=3,right=4]")
  check "proxy padding" (m.get P_PAD == some (ElkPadding.ofValues 1 4 3 2))
  let m := m.setRawById "org.eclipse.elk.test.spacing" (.string "oops")
  checkFloat "type mismatch falls back to default" (m.get! P_SPACING) 20.0
  let other : PropertyMap := ({} : PropertyMap).set P_SPACING 7.0
  let merged := m.copyFrom other
  checkFloat "copyFrom overrides" (merged.get! P_SPACING) 7.0
  checkEq "size" merged.size 6
  checkEq "keys order" (merged.keys.map (·.id))
    #["org.eclipse.elk.test.color", "org.eclipse.elk.test.set", "org.eclipse.elk.test.spacing",
      "org.eclipse.elk.test.name", "org.eclipse.elk.test.vec", "org.eclipse.elk.test.pad"]

def graph : Suite := suite "graph.model" do
  let (g, root) := ElkGraphUtil.createGraph
  let (g, a) := g.createNode root
  let (g, b) := g.createNode root
  let (g, c) := g.createNode a
  let (g, pa) := g.createPort a
  let (g, l) := g.createLabel (some (.node a)) "A"
  checkEqR "children" (g.node root).children #[a, b]
  checkEqR "nested child" (g.node a).children #[c]
  check "port parent" ((g.port pa).parent == some a)
  check "label parent" ((g.label l).parent == some (.node a))
  checkEqR "node labels" (g.node a).labels #[l]
  checkEq "label text" (g.label l).text "A"
  let (g, e) := ElkGraphUtil.createSimpleEdge g (.port pa) (.node b)
  check "edge containment root" ((g.edge e).containingNode == some root)
  checkEqR "root contained edges" (g.node root).containedEdges #[e]
  checkEqR "port outgoing" (g.port pa).outgoingEdges #[e]
  checkEqR "node incoming" (g.node b).incomingEdges #[e]
  checkEqR "all outgoing a" (ElkGraphUtil.allOutgoingEdges g a) #[e]
  check "not selfloop" (!ElkGraphUtil.isSelfloop g e)
  check "not hierarchical" (!ElkGraphUtil.isHierarchicalEdge g e)
  let (g, e2) := ElkGraphUtil.createSimpleEdge g (.node c) (.node b)
  check "hierarchical edge" (ElkGraphUtil.isHierarchicalEdge g e2)
  check "containment of c->b is root" ((g.edge e2).containingNode == some root)
  let (g, e3) := ElkGraphUtil.createSimpleEdge g (.node a) (.node c)
  check "a->c contained in a" ((g.edge e3).containingNode == some a)
  let (g, e4) := ElkGraphUtil.createSimpleEdge g (.node a) (.port pa)
  check "selfloop" (ElkGraphUtil.isSelfloop g e4)
  -- move c under root
  let g := g.setNodeParent c (some root)
  checkEqR "children after move" (g.node root).children #[a, b, c]
  checkEqR "a children after move" (g.node a).children #[]
  check "isDescendant" (ElkGraphUtil.isDescendant g c root && !ElkGraphUtil.isDescendant g root c)
  checkEqR "descendants preorder" (ElkGraphUtil.descendantNodes g root) #[a, b, c]
  check "lca" (ElkGraphUtil.findLowestCommonAncestor g a c == some root)
  check "containingGraph label" (ElkGraphUtil.containingGraph g (.label l) == some root)
  let g := g.removeEdgeTarget e (.node b)
  checkEqR "target removed" (g.edge e).targets #[]
  checkEqR "incoming removed" (g.node b).incomingEdges #[e2]
  let (g, s) := ElkGraphUtil.firstEdgeSection g e true true
  check "section created" ((g.edge e).sections == #[s])
  let (g, s') := ElkGraphUtil.firstEdgeSection g e false false
  check "section reused" (s == s')
  let g := ElkGraphUtil.createBendPoint g s 1.0 2.0
  checkEq "bend points" (g.edgeSection s).bendPoints.size 1
  -- monadic API
  let (n, g2) ← (do
      let n ← ElkM.createNode (some root)
      ElkM.modifyNode n fun x => { x with x := 3.0, width := 10.0 }
      ElkM.setNodeProp n (Property.withDefault "org.eclipse.elk.test.k" 1.0) 2.0
      return n).run g
  checkFloat "monad node x" (g2.node n).x 3.0
  check "monad prop" ((g2.node n).props.hasId "org.eclipse.elk.test.k")
  checkEq "monad child count" (g2.node root).children.size 4

def suites : Array Suite := #[javaSemantics, sorting, random, math, enums, properties, graph]

end Tests.Core.Foundation
