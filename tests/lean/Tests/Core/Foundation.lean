import Tests.Framework
/-! Tests for the Phase 1 foundation: Java helpers, sorting, Random, math, properties. -/
namespace Tests.Core.Foundation

open Tests Elk Elk.Core.Util Elk.Core.Math Elk.Graph

elk_enum Color := red green blueish (darkCyan "DARK_CYAN")

/-- `(x, Math.log(x))` bit patterns from ELK's reference JVM (Temurin 21, aarch64; `Math.log` equals
`StrictMath.log` there) for arguments where the C library's `log` differs by an ulp (FEL). -/
private def javaLogSamples : Array (UInt64 × UInt64) := #[
    (0x3FD933FFADCCF108, 0xBFEDD23FFFE32D70),
    (0x3FF8F8F331F83355, 0x3FDC7DE8EEC87460),
    (0x3FE39EA0D9D4CD61, 0xBFDF4F213C17B1FE),
    (0x3FDEFE2BB3D28676, 0xBFE7343C4D453AE0),
    (0x3FE2FC39B9361F2C, 0xBFE0B4D2EE4BF1B0),
    (0x3FFD7EF98169E930, 0x3FE392C411018080),
    (0x3FE1B59FC3B4C5B3, 0xBFE2EEAF8646ED80),
    (0x3FFA2177A03F2F2E, 0x3FDF64BC12336702),
    (0x3FEBCBE62FBA5500, 0xBFC2069A0AAA4BFE),
    (0x3FEC7FCA41806625, 0xBFBDA90A26675184),
    (0x3FE8643CF024746D, 0xBFD1603D1ACB59C0),
    (0x40051E1D631E3BE6, 0x3FEF0FB4301649B0),
    (0x400558195BC68252, 0x3FEF6719CC6C8D20),
    (0x3FDB9BF2527B337C, 0xBFEAE74D9E679A40),
    (0x3FEA6AAC8929B046, 0xBFC88AED2C6B40C0),
    (0x3FF96F70FD8D2867, 0x3FDDAACD6B69B380),
    (0x3FDB87546FFE8F66, 0xBFEAFF3BD01FAA00),
    (0x3FE5B3D1DDA17C57, 0xBFD8DA1AE881A760),
    (0x3FE290DF70753BEC, 0xBFE16BCC119CB3C0),
    (0x400132745D5E4572, 0x3FE87D5357F8C200),
    (0x3FDABF62D3B66402, 0xBFEBEB03A9210260),
    (0x3FE17D5D92AFC4F7, 0xBFE354FA47650880),
    (0x3FDB96324C3DFD24, 0xBFEAEDF87102CE70),
    (0x3FE1A4A858963C8B, 0xBFE30D668E5EEFE0),
    (0x3FFAA7C743A26110, 0x3FE0553782002740),
    (0x3FF9D396D598FCE0, 0x3FDEA4DFF422A802),
    (0x3FE28DDA6AA317BB, 0xBFE17100DDA6AC20),
    (0x3FF65521BCF6A842, 0x3FD5575954769AA0),
    (0x400328B265D53B5E, 0x3FEBF250E1B12640),
    (0x3FE3E2D9F22C9A09, 0xBFDE7214E7D30BA0),
    (0x3FE2C95ABA7F2E18, 0xBFE10B051D1D6500),
    (0x3FD7B294A59F5416, 0xBFEFCAD5BD2578A0),
    (0x3FDCEACD1F8CD33A, 0xBFE96C1BA2A08150),
    (0x4005A066655D40E4, 0x3FEFD2C950979EC0),
    (0x40040C9F871DE331, 0x3FED666D05A8B820),
    (0x400055FAED351D6D, 0x3FE6D8712D8C0810),
    (0x3FE3BA38BC393576, 0xBFDEF55DA5940D82),
    (0x3FD95C098BC3F664, 0xBFED9F921EDCB410),
    (0x3FFA49C8CBECBDA0, 0x3FDFC72F0D2F2BFE),
    (0x3FF36B4FB34DA963, 0x3FC8CA44EB584BC0),
    (0x3FE8B96A93988C62, 0xBFD08240E8A5A6C2),
    (0x400340E1C71E4098, 0x3FEC1A9C888C5960),
    (0x3FDD5702CB640D0C, 0xBFE8F53AA0E6B3C0),
    (0x3FE514EFD5EE37CE, 0xBFDAB57A4F466D9E),
    (0x3FE65B6865C91F1F, 0xBFD6F332DDDE4620),
    (0x3FD84E59E13AB54A, 0xBFEEFB25475820A0),
    (0x3FF6CB4AC0E811FC, 0x3FD6A68479CD001E),
    (0x4003EECE298E88FA, 0x3FED36B225D8B5F0)]

/-! Bit patterns of `Math.sin`/`Math.cos` (HotSpot aarch64 stubs), `Math.atan2` and `Math.acos` (fdlibm)
from ELK's reference JVM (Temurin 21.0.13, aarch64; `TrigSamples.java` of agent RJ3): selected
arguments (π multiples, the π/4 boundary, near-`k·π/2` values, the largest medium reduction argument)
and random ones where `Math` differs from `StrictMath` or from the C library. -/
private def javaSinCosSamples : Array (UInt64 × UInt64 × UInt64) := #[
  (0x3FE0000000000000, 0x3FDEAEE8744B05F0, 0x3FEC1528065B7D50),
  (0x3FF0000000000000, 0x3FEAED548F090CEE, 0x3FE14A280FB5068C),
  (0x4000000000000000, 0x3FED18F6EAD1B446, 0xBFDAA22657537205),
  (0x4008000000000000, 0x3FC210386DB6D55B, 0xBFEFAE04BE85E5D2),
  (0x400921FB54442D18, 0x3CA1A62633145C07, 0xBFF0000000000000),
  (0x401921FB54442D18, 0xBCB1A62633145C07, 0x3FF0000000000000),
  (0xBFE921FB54442D18, 0xBFE6A09E667F3BCC, 0x3FE6A09E667F3BCD),
  (0x3FE921FB54442D18, 0x3FE6A09E667F3BCC, 0x3FE6A09E667F3BCD),
  (0x3FE921FB54442D19, 0x3FE6A09E667F3BCD, 0x3FE6A09E667F3BCC),
  (0x3FF921FB54442D18, 0x3FF0000000000000, 0x3C91A62633145C07),
  (0x4012D97C7F3321D2, 0xBFF0000000000000, 0xBCAA79394C9E8A0A),
  (0x4059000000000000, 0xBFE03425B78C4DB8, 0x3FEB981DBF665FDF),
  (0x3E112E0BE826D695, 0x3E112E0BE826D695, 0x3FF0000000000000),
  (0x81A56E1FC2F8F359, 0x81A56E1FC2F8F359, 0x3FF0000000000000),
  (0x4012D97C7F3321D2, 0xBFF0000000000000, 0xBCAA79394C9E8A0A),
  (0x404921FB54442D18, 0xBCE1A62633145C07, 0x3FF0000000000000),
  (0x412921FA00000000, 0xBFE3BC41EC71C06D, 0x3FE930880DDDF826),
  (0xBFE58FDDEFF23C3E, 0xBFE3F78E79836434, 0x3FE901A10577CB76),
  (0xBFFA42C523C56C0D, 0xBFEFEBA5BD8BB68C, 0xBFB208C9357F0448),
  (0xC0837EB05AC991B4, 0xBFEF2855488D6606, 0xBFCD2D604535DF58),
  (0xBFD3176C02817C30, 0xBFD2CF423A274128, 0x3FEE9635B2F2974B),
  (0xC00B36383E0264C2, 0x3FD07222E7DEE80D, 0xBFEEECEA621CB7B6),
  (0x405BCCAD930EEFA4, 0xBFEE4A18E19AA94E, 0xBFD4A5035721AB35),
  (0x3FED71CB16DE349A, 0x3FE97644614F97E0, 0x3FE361F60A2A8278),
  (0x400A1F10E08BE9CA, 0xBFBF8E18B9962390, 0xBFEFC18777CEF6FD),
  (0xC08968927981CAA8, 0xBFE21826A3AA13E7, 0xBFEA64A1249187E4),
  (0x3FE2B9942120A9DA, 0x3FE1ACAAA7BEFFA3, 0x3FEAAD13061C7ECC),
  (0xBFFBD1B8F078015C, 0xBFEF8CCBAF2C3B46, 0xBFC5641C1C36D3DA),
  (0xC057197850B662B5, 0x3FEEC33153EA7D23, 0xBFD1A04BD0CDC10B),
  (0x3FE56F7BC49B52F2, 0x3FE3DE35EC8EF03B, 0x3FE915C903B1A753),
  (0x401847C3B5480F94, 0xBFCB12384D7406D0, 0x3FEF46B128BF00CC),
  (0x4035C8B5A68FF36F, 0x3FCA52B49AB842DE, 0xBFEF50E719E3E92E),
  (0x3FC11377BB7EB100, 0x3FC10683334BB022, 0x3FEFB735D0C89C91),
  (0x4007D5F6102D0974, 0x3FC4A916DB8BA3AC, 0xBFEF9494E4CA56F2),
  (0x4059F464D5EB0B99, 0xBFC2A24AEEB0F318, 0xBFEFA8BAA4038474),
  (0x3FE0F0913249CE5E, 0x3FE028D90F748F93, 0x3FEB9EBD3F60D1DD),
  (0xBFE02A02DFD230F0, 0xBFDEF88A826865A1, 0x3FEC00EBAF4DB69F),
  (0x407130A831C3EAEF, 0xBFEFA1E99BC01918, 0x3FC3580D7CA14FAD),
  (0xBFE92024E2FE4652, 0xBFE69F51B5C313CD, 0x3FE6A1EB0420F2C5),
  (0xC013EA0BF9EC18DA, 0x3FEEDF845C006478, 0x3FD0D5A7CD1BADF8),
  (0xC066820D369F6DF3, 0x3FEACFA98FEDE4BA, 0xBFE1780645822DEC),
  (0x3FE7B73555A0D0E6, 0x3FE59A810EC86CA9, 0x3FE79B602418C887),
  (0x4011441CF26E2A88, 0xBFED866F66FA3020, 0xBFD8ADE2E5316DDE),
  (0xC08969CE3BE32495, 0xBFDBA72FDAF73EB5, 0xBFECDBD662AB36B8),
  (0xBFD95D3059BBE45C, 0xBFD8B48B66ECD9D1, 0x3FED850AFE87E66E),
  (0x4000A1A7DEDEE8AC, 0x3FEBF4F5DF7863C0, 0xBFDF23A522B51B37),
  (0x407737F617DC4F51, 0x3FE6B92F731A3C89, 0x3FE687F290B96177),
  (0xBFE82DB18EC01EFC, 0xBFE5F154C7A10CC3, 0x3FE74AC16FEDFD50)]
private def javaAtan2Samples : Array (UInt64 × UInt64 × UInt64) := #[
  (0x0000000000000000, 0x0000000000000000, 0x0000000000000000),
  (0x8000000000000000, 0xBFF0000000000000, 0xC00921FB54442D18),
  (0x0000000000000000, 0xBFF0000000000000, 0x400921FB54442D18),
  (0x3FF0000000000000, 0x0000000000000000, 0x3FF921FB54442D18),
  (0xBFF0000000000000, 0x8000000000000000, 0xBFF921FB54442D18),
  (0x3FF0000000000000, 0x3FF0000000000000, 0x3FE921FB54442D18),
  (0xBFF0000000000000, 0xBFF0000000000000, 0xC002D97C7F3321D2),
  (0x7FF0000000000000, 0x7FF0000000000000, 0x3FE921FB54442D18),
  (0x3FF0000000000000, 0xFFF0000000000000, 0x400921FB54442D18),
  (0x7E37E43C8800759C, 0x01A56E1FC2F8F359, 0x3FF921FB54442D18),
  (0x01A56E1FC2F8F359, 0xFE37E43C8800759C, 0x400921FB54442D18),
  (0x4008000000000000, 0x3FF0000000000000, 0x3FF3FC176B7A8560),
  (0xC004000000000000, 0x3FD3333333333333, 0xBFF738CD060D0DB1),
  (0x407167D19A5788D3, 0x4072F3F3064D1B26, 0x3FE7C58C2F19D440),
  (0x4078639B659F1D25, 0x407BF31D30E9FBB5, 0x3FE6F58ACEF17F5F),
  (0x4054448744EB6D16, 0xC079D1194AD9C58A, 0x40079513A7C402E7),
  (0x40288CE70E918AA8, 0xC05114530F4BA928, 0x4007B5E29A3B2465),
  (0x4069E45AF8D5F410, 0x406E43DB71482639, 0x3FE6A5573172CC4A),
  (0xC05D84502CEECA67, 0x4052AA67C2C0EDE2, 0xBFF01C50BCAAFF7B),
  (0xC06AE5EF8975A3DE, 0x4050BE1A1B960182, 0xBFF44E23563DB13F),
  (0x407B3CE2AAC04F2A, 0xC07CFAA901991FE5, 0x400318E701286F72),
  (0xC069E38DD7244A91, 0xC0507184B36E83F0, 0xBFFE0D8426A10E7D),
  (0xC0721822A89E5FBC, 0xC05E31EE0614ABD4, 0xBFFF74DFAD37208B),
  (0x4073F76831249826, 0x407479BAA772A170, 0x3FE8BADE69FA40B8),
  (0x407EE6FAECC539C8, 0x407C51D959BBDF85, 0x3FEA86FDB6849D27),
  (0xC07739FB93BA2736, 0xC07D9CF67AEC845D, 0xC003CFD46CE4A74A),
  (0x40784FDCCFDCC30E, 0x407336FDC85BD112, 0x3FECDCF27A9A9911),
  (0x40705E9C878BB803, 0xC07E7C0F14C6F0BA, 0x400530BEF6542BBE),
  (0xC0577650CE9DBCB9, 0xC0638B07125461A1, 0xC004CECC886AF16C),
  (0x407D0049B73D1852, 0x4036C2FEBFBC808E, 0x3FF85938381B43A6),
  (0x407AAB9749BE2A01, 0xC07D5286288F418B, 0x40033A6AC509BA10),
  (0xC0699BAF3DBE8155, 0x40722C6120DE6085, 0xBFE3A40A11E1D4A8),
  (0xC07ADC2155FA5B98, 0xC05942D85B03CA98, 0xBFFCD3D9CF053EF9),
  (0xC052020FFB996922, 0xC05182FEE57EBFB1, 0xC002BCDE8D94B0E8),
  (0x4071EB0F10383389, 0x4068AB2DCDA2C5FF, 0x3FEEF9316E062B11),
  (0x40706DBB0B0A396D, 0x405A12DF5A80A631, 0x3FF316D63AC132BE),
  (0xC06CB976CC39687F, 0xC07B7E90A9FA01E0, 0xC005481C2B2212FB)]
private def javaAcosSamples : Array (UInt64 × UInt64) := #[
  (0x3FF0000000000000, 0x0000000000000000),
  (0xBFF0000000000000, 0x400921FB54442D18),
  (0x0000000000000000, 0x3FF921FB54442D18),
  (0x8000000000000000, 0x3FF921FB54442D18),
  (0x3FE0000000000000, 0x3FF0C152382D7366),
  (0xBFE0000000000000, 0x4000C152382D7366),
  (0x3FDFFFFFF543388F, 0x3FF0C1523B46F476),
  (0x3BC79CA10C924223, 0x3FF921FB54442D18),
  (0x4000000000000000, 0x7FF8000000000000),
  (0xBFF000001AD7F29B, 0x7FF8000000000000),
  (0x3FEFFFFFFAA19C47, 0x3F228950343CEF55),
  (0xBFE8000000000000, 0x400359D26F93B6C3),
  (0x3FD3333333333333, 0x3FF441F5ECBEEF59),
  (0x3FD750A43BE302E8, 0x3FF32AACA1E775C8),
  (0xBFE9F357B78D12FE, 0x400421F3F9AF4F34),
  (0x3FCDB9C64DEA8FF0, 0x3FF561FECED6B2EA),
  (0x3FE0521C44D0BCEA, 0x3FF091C110D20EA5),
  (0x3FEE6351A6898B6C, 0x3FD4669BCBF68815),
  (0xBFE813DD21E9F1F4, 0x4003615873719A10),
  (0x3FEFB3D189806BB4, 0x3FC1784F36B36CD6),
  (0xBFE8F4E035BB79F2, 0x4003B8E9CC8CF7A7),
  (0xBFE2D449D8638F46, 0x400199612F920494),
  (0x3FE5991064147C12, 0x3FEA8EB5027BDCB4),
  (0xBFEFC072D3441E12, 0x400822B717373972),
  (0xBFEF78ADEB6A474A, 0x4007AD3842389335),
  (0x3FC433E622136A18, 0x3FF698C798EFEABE),
  (0xBFE6B2AC7B45113E, 0x4002DFE134EB06F4),
  (0x3FE0A472FF88CB7E, 0x3FF061B9406AEB97),
  (0xBFC3FC701426F0A0, 0x3FFBA42A058A6291)]

def javaSemantics : Suite := suite "core.util.java" do
  for (x, y) in javaLogSamples do
    checkEq s!"javaLog {x}" (javaLog (Float.ofBits x)).toBits y
  for (x, sv, cv) in javaSinCosSamples do
    checkEq s!"javaSin {x}" (javaSin (Float.ofBits x)).toBits sv
    checkEq s!"javaCos {x}" (javaCos (Float.ofBits x)).toBits cv
  for (y, x, v) in javaAtan2Samples do
    checkEq s!"javaAtan2 {y} {x}" (javaAtan2 (Float.ofBits y) (Float.ofBits x)).toBits v
  for (c, v) in javaAcosSamples do
    if (Float.ofBits v).isNaN then check s!"javaAcos {c} = NaN" (javaAcos (Float.ofBits c)).isNaN
    else checkEq s!"javaAcos {c}" (javaAcos (Float.ofBits c)).toBits v
  check "javaSin NaN / inf" ((javaSin Float.nan).isNaN && (javaSin Float.posInf).isNaN && (javaCos Float.negInf).isNaN)
  checkEq "javaSin -0.0 keeps the sign" (javaSin (-0.0)).toBits 0x8000000000000000
  -- `DoubleStream.average()` (values from the reference JVM): Kahan summation
  checkEq "javaDoubleAverage 0.1 x3" (javaDoubleAverage #[0.1, 0.1, 0.1]) (some 0.10000000000000002)
  checkEq "javaDoubleAverage empty" (javaDoubleAverage #[]) none
  checkEq "javaDoubleAverage 1e16 + 1 + 1 (compensated)" (javaDoubleAverage #[1e16, 1.0, 1.0]) (some 3333333333333334.0)
  -- `Double.compare` order: -0.0 < 0.0, NaN above +inf; a stable sort by it
  check "javaOrderKey -0.0 < 0.0" ((-0.0 : Float).javaOrderKey < (0.0 : Float).javaOrderKey)
  check "javaOrderKey inf < NaN" (Float.posInf.javaOrderKey < Float.nan.javaOrderKey)
  checkEq "javaSortByDouble (stable, Double.compare)"
    (javaSortByDouble #[(1, 2.0), (2, Float.nan), (3, 0.0), (4, -0.0), (5, 2.0), (6, -1.0)] (·.2) |>.map (·.1))
    #[6, 4, 3, 1, 5, 2]
  checkEq "javaLog 1" (javaLog 1.0).toBits (0 : UInt64)
  check "javaLog 0 = -inf" (javaLog 0.0 == Float.negInf)
  check "javaLog -0 = -inf" (javaLog (-0.0) == Float.negInf)
  check "javaLog -1 = NaN" (javaLog (-1.0)).isNaN
  check "javaLog NaN = NaN" (javaLog Float.nan).isNaN
  check "javaLog inf = inf" (javaLog Float.posInf == Float.posInf)
  checkEq "javaLog MIN_VALUE (subnormal)" (javaLog Float.minPositive) (-744.4400719213812)
  checkEq "javaLog 2" (javaLog 2.0) 0.6931471805599453
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

/-! Bit patterns of `Math.sin`/`Math.cos` for arguments above `2^19·π/2` (the stubs' `__kernel_rem_pio2`
reduction) from ELK's reference JVM (Temurin 21.0.13, aarch64; `scripts/java/SinCosDump.java`): the
medium/large boundary, powers of two and `2^e·π/2` up to `2^1023`, decimal magnitudes up to the largest
double, and every 25,000th random argument of the 1,000,000 of the dump. -/
private def javaSinCosLargeSamples : Array (UInt64 × UInt64 × UInt64) := #[
  (0x413921FB00000000, 0xBFD4B02E5BE91E9E, 0x3FEE4831257A62DA),
  (0xC13921FB00000000, 0x3FD4B02E5BE91E9E, 0x3FEE4831257A62DA),
  (0x413921FBFFFFFFFF, 0x3FE3E479A5FF2619, 0x3FE910D18D3AA54E),
  (0xC13921FBFFFFFFFF, 0xBFE3E479A5FF2619, 0x3FE910D18D3AA54E),
  (0x413921FC00000000, 0x3FE3E479A61836EB, 0x3FE910D18D26C0D4),
  (0xC13921FC00000000, 0xBFE3E479A61836EB, 0x3FE910D18D26C0D4),
  (0x413921FA54442D18, 0xBFEAED548F0DD183, 0x3FE14A280FAD9999),
  (0xC13921FA54442D18, 0x3FEAED548F0DD183, 0x3FE14A280FAD9999),
  (0x413921FB54442D18, 0xBDD1A62633145C07, 0x3FF0000000000000),
  (0xC13921FB54442D18, 0x3DD1A62633145C07, 0x3FF0000000000000),
  (0x413921FB54442D19, 0x3DE72CECE675D1FD, 0x3FF0000000000000),
  (0xC13921FB54442D19, 0xBDE72CECE675D1FD, 0x3FF0000000000000),
  (0x7FEFFFFFFFFFFFFF, 0x3F7452FC98B34E97, 0xBFEFFFE62ECFAB76),
  (0xFFEFFFFFFFFFFFFF, 0xBF7452FC98B34E97, 0xBFEFFFE62ECFAB76),
  (0x7FE0000000000000, 0x3FE205248CBDB760, 0xBFEA719F26C232BE),
  (0xFFE0000000000000, 0xBFE205248CBDB760, 0xBFEA719F26C232BE),
  (0x4170000000000000, 0xBFE8F22F8433D6EE, 0x3FE40AD67F3F0C9A),
  (0xC170000000000000, 0x3FE8F22F8433D6EE, 0x3FE40AD67F3F0C9A),
  (0x4120000000000000, 0x3FC57481EC90FDE3, 0x3FEF8C1986CA67FA),
  (0x4440000000000000, 0xBFE5EF362C7849DB, 0x3FE74CC06D91153B),
  (0x4760000000000000, 0xBFEF66C46194BBB7, 0xBFC8A43363CFC081),
  (0x4A80000000000000, 0x3FE79850E290E6E9, 0x3FE59DD879524A22),
  (0x4DA0000000000000, 0x3FEAB84AA4B22B4C, 0xBFE19BB0CFA3ADDD),
  (0x50C0000000000000, 0x3FE875130E0F2EDA, 0x3FE4A2C8CDF7A888),
  (0x53E0000000000000, 0x3F93BF15BFA67A8F, 0x3FEFFE7A0ADC0BCE),
  (0x5700000000000000, 0xBFEF367317958071, 0x3FCC37EFFDBE1DE2),
  (0x5A20000000000000, 0x3FE54CC1A4B8C748, 0xBFE7E19DEC3BB8E5),
  (0x5D40000000000000, 0xBFED762692ADEE99, 0xBFD8FB41B992898C),
  (0x6060000000000000, 0x3FEE84CD1E05E450, 0x3FD33F1183B752B4),
  (0x6380000000000000, 0x3FE6F7087CDD644F, 0x3FE648E542520984),
  (0x66A0000000000000, 0xBFE9E9B2EF0A0E0C, 0xBFE2C68C3F0A9E16),
  (0x69C0000000000000, 0x3FE7BE6A875D6CCC, 0xBFE573F803B8DC06),
  (0x6CE0000000000000, 0x3FDCC668A3A1878F, 0x3FEC954CA127999C),
  (0x7000000000000000, 0xBFCA3A46C17E0A30, 0x3FEF522F06B5B8DE),
  (0x7320000000000000, 0xBFE99659A89A191C, 0x3FE33787B120EE81),
  (0x7640000000000000, 0x3FEFF93DFC78F779, 0x3FA4CADC8B50A401),
  (0x7960000000000000, 0xBFDD0462CF7BFB98, 0x3FEC859E5DBB4005),
  (0x7C80000000000000, 0xBFDDFB6061059543, 0xBFEC45790B69E33E),
  (0x7FA0000000000000, 0xBFCDA57A500E88B4, 0x3FEF213E8429B604),
  (0x4480F0CF064DD592, 0xBFEB453AB76BF397, 0x3FE0BE2CEF01C8F4),
  (0x7E37E43C8800759C, 0xBFEA2C16B010E385, 0xBFE2699022ADC4C1),
  (0xFE37E43C8800759C, 0x3FEA2C16B010E385, 0xBFE2699022ADC4C1),
  (0x7FEFFFFFFFFFFFFF, 0x3F7452FC98B34E97, 0xBFEFFFE62ECFAB76),
  (0x7506AC5B262CA1FF, 0x3FF0000000000000, 0xBC214AE72E6BA22F),
  (0x7506AC5B262CA1FF, 0x3FF0000000000000, 0xBC214AE72E6BA22F),
  (0x430C6BF526340000, 0x3FEB76F88136CEBA, 0xBFE06C154609D33E),
  (0x4341C37937E08000, 0x3FE8F334432EBBA5, 0xBFE40991E398DBFC),
  (0x4376345785D8A000, 0xBFDDBADC7A119FC8, 0xBFEC567C5278AFCB),
  (0x421D4223FC1F9773, 0xBF012C8FEB1CF57C, 0x3FEFFFFFFFB64348),
  (0x412921FC00000000, 0x3FD51102EFAD6266, 0x3FEE377C09C4CCE7),
  (0x412921FB33333333, 0xBFB0858BE515492B, 0x3FEFEEEBFEE47670),
  (0x412E848000000000, 0xBFD6664B2568D867, 0x3FEDF9DF9906D32C),
  (0x416312D000000000, 0x3FDAEA414A8A3352, 0xBFED085BE7A8F4A0),
  (0x4197D78400000000, 0x3FEDCFFCA623A20B, 0xBFD741B388A8C029),
  (0xEC7BA419D037FA2C, 0xBFEF3C5670A06346, 0xBFCBCEEE2BF8AD60),
  (0xC94A59B71ECB7BDF, 0xBFE7A2EE93627896, 0xBFE5923C544F8BFE),
  (0xC4EC6EFAB91C1606, 0xBFE1A761F108CC1D, 0xBFEAB0928633A9C3),
  (0x45763829DAFD646D, 0xBF668DC3916B5166, 0xBFEFFFF80D4E8B49),
  (0x624E1217FC5F8732, 0x3FD28B6C68F1C739, 0x3FEEA08EF5A4E0A3),
  (0x41EEFCC6D734AAC2, 0xBFDF83BC987E9896, 0xBFEBD9FDAB21AD06),
  (0x6DBB4606570A8FDB, 0x3FEEE2F7C394505C, 0xBFD0BC42E5EAA9B5),
  (0xF1874414BC581388, 0x3FECF23CC56ABC4D, 0x3FDB48E93F9F6CDD),
  (0x5DC4203E797EB728, 0xBFECD5B817ECCA03, 0xBFDBC0ABBB9E4B4D),
  (0xFEA2B17E47802868, 0x3FB5BC86169EC704, 0xBFEFE26AC618BC81),
  (0x6C76671D1867C944, 0xBFD73453F835FF8F, 0x3FEDD29776F188E3),
  (0x572043522968380A, 0x3FE5319DDD87FD8D, 0x3FE7F9B71729E58A),
  (0x70E9E5E2EAACD756, 0xBFE06F3006E38D2D, 0xBFEB751D0DAE509A),
  (0x5EF8A6C316DF5616, 0xBFEF39555009BEDA, 0x3FCC04B6525E689F),
  (0xC4D0C0B4A0613788, 0x3FCB4CF0F8336D60, 0xBFEF438053D9AB4C),
  (0xECF08BE7C2395B38, 0xBFEFE7AEFCEF8FAE, 0x3FB3B5C569EF0A10),
  (0x632BC89AEEB58503, 0x3FEF340E0E702CAC, 0x3FCC6230115F1771),
  (0xD0EEF9BADDBFE516, 0x3FEE0D3CB55F8D80, 0x3FD5FD8D8651CC5A),
  (0xFB62CF8288E89FF0, 0x3FEFED6853D6D8AF, 0xBFB13CE0D97BC5A9),
  (0xED27A21B2323565C, 0x3FB479311871485F, 0x3FEFE5C2AD3DBC70),
  (0x7F90FC3C2638AD77, 0x3FEC2F1E32E15AEC, 0x3FDE4F1B7C234600),
  (0xEA2935CB43EBD6B0, 0xBFEFE3EA9F313775, 0x3FB52DEB895534F1),
  (0xD0951E7C74D417C2, 0xBFD91675EEDC57D8, 0xBFED705E90ECD076),
  (0xE58FB871F2EA52BC, 0xBFEF7A48226B9007, 0xBFC708623D4B630C),
  (0xCA0602DC2DCA8DFB, 0xBFEAACB582A8EA28, 0x3FE1AD37C85DCB01),
  (0x443AD499E2A97C2B, 0xBFEC683BFF2616DB, 0x3FDD76CDB611DDB9),
  (0x5F7AC6D805FE044A, 0x3FEDC1B082218420, 0x3FD78A7F9A9A18DD),
  (0xF4D82FB1C8DEC9A4, 0xBFE9E9E26F3AB0BC, 0x3FE2C64AAF9ECA3C),
  (0xF7B72CD0A813B3D6, 0x3FD1FC9EB180A519, 0x3FEEB5D23B820778),
  (0x4B91BE0C5EDB76D0, 0xBFEFF7FDF0B4BD60, 0xBFA6A21D4A3C8818),
  (0x678BF00AD7651ACC, 0x3FEE4F5023A2D5FE, 0x3FD4864D9386D324),
  (0x455016E04EFD8458, 0x3FEF7DFF6FB10C88, 0x3FC6B68A84CBA7AF),
  (0x674B18AF3BF0FC51, 0x3FEF929E8B4E29F2, 0xBFC4D8DBEB57C258),
  (0x48B0C8485320B7E5, 0xBFE9E1DF19B2218C, 0x3FE2D1551573F1A7),
  (0xF5C04FCA8B4C6091, 0x3FEFCD35031FAAA8, 0x3FBC76A3D9BAA098),
  (0x5290AB431C0F9C21, 0xBFEE7942C1419ADF, 0x3FD387AD847E6D0C),
  (0xEDFD334D7E9394B4, 0x3FED9823D3321D43, 0xBFD8587C2EA58E4A),
  (0xF37A37B361F480B4, 0xBFD6EAC4E7B00EDE, 0x3FEDE0CC6C422E34),
  (0x6C99AA0CC15B2AE2, 0xBFEBFBEDFC4D3C6D, 0xBFDF0A90CBB1DAE7),
  (0x5027D85FD5CA7A48, 0xBFAC291D37AB6B94, 0xBFEFF39984F38F89)]

/-- Parses a hexadecimal bit pattern. -/
private def hexBitsOf (s : String) : UInt64 :=
  s.foldl (fun acc c =>
    let d := if c.isDigit then c.toNat - '0'.toNat else c.toLower.toNat - 'a'.toNat + 10
    acc * 16 + d.toUInt64) 0

/-- `javaSin`/`javaCos` for large arguments against the reference JVM, bit for bit; with
`ELK_SINCOS_CASES` set to the output of `java SinCosDump <n>` also every line of that file. -/
def javaSinCosLarge : Suite := suite "core.javaSinCos.large" do
  for (x, sv, cv) in javaSinCosLargeSamples do
    checkEq s!"javaSin {x}" (javaSin (Float.ofBits x)).toBits sv
    checkEq s!"javaCos {x}" (javaCos (Float.ofBits x)).toBits cv
  let some path ← IO.getEnv "ELK_SINCOS_CASES"
    | IO.println "SKIP core.javaSinCos.large (full): ELK_SINCOS_CASES not set"
  let mut n := 0
  let mut bad := 0
  for line in ← IO.FS.lines path do
    if let [a, b, c] := line.splitOn " " then
      n := n + 1
      let x := Float.ofBits (hexBitsOf a)
      unless (javaSin x).toBits == hexBitsOf b && (javaCos x).toBits == hexBitsOf c do
        if bad < 5 then IO.println s!"  mismatch {a}: sin {(javaSin x).toBits} vs {b}, cos {(javaCos x).toBits} vs {c}"
        bad := bad + 1
  check s!"javaSin/javaCos equal Math.sin/Math.cos on all {n} arguments of {path} ({bad} differ)" (n > 0 && bad == 0)

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

/-- `LayoutOptionData.parseInt32Bytes?` (byte-wise INT option parsing) against the `List Char`
reference `parseInt32?` on boundary cases and random strings over a digit-heavy alphabet. -/
def int32Parsing : Suite := suite "core.data.parse_int32_bytes" do
  let fixed := #["", "+", "-", "0", "-0", "+0", "007", "42", "-7", "+15", "2147483647", "2147483648",
    "-2147483648", "-2147483649", "99999999999999999999999", "-00000000000000000000001", "1.0", " 1",
    "1 ", "+-1", "--1", "1e3", "١٢", "12a", "a12"]
  let mut bad : Array String := #[]
  for s in fixed do
    if Elk.Core.Data.LayoutOptionData.parseInt32Bytes? s != parseInt32? s then bad := bad.push s
  let alphabet := "0123456789+- .x".toList.toArray
  let mut r := Random.ofInt 5
  for _ in [0:20000] do
    let (len, r1) := r.nextInt 13
    r := r1
    let mut s := ""
    for _ in [0:len.toNat] do
      let (c, r2) := r.nextInt (alphabet.size : Int)
      r := r2
      s := s.push alphabet[c.toNat]!
    if Elk.Core.Data.LayoutOptionData.parseInt32Bytes? s != parseInt32? s && bad.size < 20 then bad := bad.push s
  checkEq "byte-wise int32 parsing agrees with parseInt32?" bad #[]

def suites : Array Suite := #[javaSemantics, javaSinCosLarge, sorting, random, math, enums, properties, graph, int32Parsing]

end Tests.Core.Foundation
