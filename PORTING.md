# elk-lean 포팅 규약 (Rust/Java → Lean 4)

서브에이전트와 주 에이전트가 공통으로 따르는 구체 규약이다. 설계 배경은 `PLAN.md` 4장, 작업 방식은 `AGENTS.md` 참조. 이 문서의 예제는 모두 현재 코드베이스에서 컴파일되는 형태다.

## 1. 파일·모듈 배치
- Java 클래스 1개 = Lean 파일 1개. 경로: `plugins/org.eclipse.elk.<plugin>/Elk/<Plugin>/<Package>/<Class>.lean`, 모듈명 `Elk.<Plugin>.<Package>.<Class>`.
  - `org.eclipse.elk.core.util.ElkUtil` → `plugins/org.eclipse.elk.core/Elk/Core/Util/ElkUtil.lean`, `namespace Elk.Core.Util` 안의 `ElkUtil` 네임스페이스.
  - `org.eclipse.elk.alg.layered.p3order.LayerSweepCrossingMinimizer` → `plugins/org.eclipse.elk.alg.layered/Elk/Alg/Layered/P3Order/LayerSweepCrossingMinimizer.lean`.
- 패키지 디렉토리는 CamelCase(`p3order` → `P3Order`, `nodespacing` → `NodeSpacing`, `intermediate` → `Intermediate`).
- 새 파일은 반드시 플러그인 루트 모듈(`Elk/Core.lean` 등)에 `import`를 추가한다(루트가 모든 서브모듈을 import해야 `lake build <Lib>`가 전체를 검사한다).
- 파일 머리: `import` 목록 → `/-! # 원본 클래스명 ... -/` 모듈 doc → `namespace`.
- `import Lean` 금지. 매크로가 필요하면 `Init` 수준 API만 사용(`Elk/Graph/Enum.lean` 참고).

## 2. 이름 규칙
| 원본 | Lean |
|---|---|
| 클래스/구조체 `LNode` | `structure LNode` (CamelCase 유지) |
| 메서드 `getPorts()`, `get_ports()` | `ports` (필드) / `getPorts` 대신 `portsOf` 류 함수; 접두어 `get` 생략 |
| 옵션 상수 `CoreOptions.SPACING_NODE_NODE` | `CoreOptions.SPACING_NODE_NODE` (대문자 **그대로** — 검색성과 1:1 대응 우선) |
| 내부 속성 `InternalProperties.IN_LAYER_LAYOUT_UNIT` | typed 필드 `inLayerLayoutUnit` (대응표는 플러그인별 `PORTING.md` 또는 모듈 doc에 기록) |
| 열거형 `PortSide.NORTH` | `PortSide.north` (`elk_enum` 생성, Java 이름은 `ElkEnum.javaName`) |
| 지역 변수 `node_count` | `nodeCount` |
| 상수 `MAX_ITERATIONS` | `MAX_ITERATIONS` (대문자 유지) |

## 3. 타입 대응표
| Rust / Java | Lean |
|---|---|
| `f64` / `double` | `Float` |
| `f32` 연산(`as f32`) / `float` | `Float.toF32 x` 로 단정밀도 반올림 재현 |
| `i32`, `i64`, `usize`(음수 가능) | `Int` (`Nat` 뺄셈은 0에서 절단되므로 음수 가능 값은 `Int`) |
| `usize` 인덱스/개수 | `Nat` |
| `bool` | `Bool` |
| `String`, `&str` | `String` |
| `Option<T>` | `Option T` |
| `Vec<T>` | `Array T` (`List` 금지) |
| `VecDeque<T>` | `Array T` + 인덱스, 또는 `Std.Queue` |
| `HashMap<K,V>`/`FxHashMap` | `Std.HashMap K V` (순회 순서가 결과에 영향을 주면 `Array (K × V)` 또는 삽입 순서 유지 구조 사용) |
| `HashSet<T>` | `Std.HashSet T` |
| `BTreeMap`/`BTreeSet` (정렬 순회) | `Array` + `stableSort` 또는 `Std.TreeMap`(필요 시) |
| `LinkedHashSet` | `Array T` + `Std.HashSet T`(중복 검사) |
| `Arc<Mutex<LNode>>`, `LNodeRef`, `Rc<RefCell<..>>` | typed id (`NodeId`, `PortId`, …) |
| `Option<LNodeRef>` | `Option NodeId` |
| `Arc<dyn Any>` 속성값 | `PropValue` (닫힌 합타입, `Elk.Graph.Properties`) |
| `Property<T>` / `IProperty<T>` | `Property α` + `PropCodec α` |
| `EnumSet<T>` | `EnumSet α` (`[ElkEnum α]`) |
| `KVector`(가변) | `KVector`(불변 값; `v.add(w)` → `let v := v + w`) |
| `KVectorChain` | `KVectorChain := Array KVector` |
| `Box<dyn ILayoutProcessor<LGraph>>` | `structure LayoutProcessor where name : String; process : GraphId → LayeredM Unit` |
| 클로저 비교자 `|a,b| a.cmp(b)` | `fun a b => compare a b` (`Ordering`) |
| `panic!`, `unwrap()`(Java 예외) | `throwUnsupportedGraph/…`(`Elk.Core.Exceptions`) 또는 `Option` 처리 |

## 4. 상태 모나드
### 4.1 ElkGraph (`Elk.Graph.Monad`)
```lean
open Elk.Graph in
def example (root : NodeId) : ElkM Unit := do
  let node ← ElkM.getNode root                         -- 값 복사(작은 구조체), 이후 변경에 영향 없음
  for c in node.children do                            -- 자식 id 배열은 복사본
    ElkM.modifyNode c fun n => { n with x := n.x + 10 } -- in-place
  let w ← ElkM.getNodePropD root CoreOptions.SPACING_NODE_NODE 20.0
```
규칙:
1. `let g ← get` 후 `g`를 `modify` 이후에도 쓰면 배열이 복사된다. 필요한 값만 꺼낸다.
2. 요소 갱신은 `modifyNode/modifyPort/…` 헬퍼만 사용한다(`Array.modify`가 요소를 swap-out 해 유일성 보장).
3. 순회 중 같은 배열을 갱신해야 하면 먼저 id 배열을 꺼낸 뒤 순회한다.
4. 알고리즘 전용 모나드도 같은 형태로 만든다: `abbrev LayeredM := StateRefT LGraph IO`, 접근자는 `Elk.Alg.Layered.Graph.Monad`에 모아 둔다.

### 4.2 순수 API
`ElkGraph`의 모든 조작은 순수 함수(`ElkGraph → … → ElkGraph`)로도 제공된다(`Elk.Graph.Model`, `Elk.Graph.Util`). import/export처럼 두 상태를 동시에 다루는 코드는 순수 API를 쓴다.

## 5. 속성 시스템
```lean
-- 정의 (옵션 상수는 Java 이름 유지)
def SPACING_NODE_NODE : Property Float := Property.withDefault "org.eclipse.elk.spacing.nodeNode" 20.0
def DIRECTION : Property Direction := Property.withDefault "org.eclipse.elk.direction" .undefined
def SIZE_CONSTRAINT : Property (EnumSet SizeConstraint) := Property.withDefault "org.eclipse.elk.nodeSize.constraints" EnumSet.empty
def BEND_POINTS : Property KVectorChain := Property.mk' "org.eclipse.elk.bendPoints"   -- 기본값 없음 → get은 Option

-- 사용
let d : Direction := props.get! DIRECTION          -- 기본값 보장 시
let bp : Option KVectorChain := props.get BEND_POINTS
let props := props.set DIRECTION .right
if props.has BEND_POINTS then ...
```
- `get` = Java `getProperty`(저장값 → 기본값 → `none`). `get?`는 저장값만. `getD`는 명시 fallback. `get!`은 `Inhabited` fallback.
- Java의 "기본값을 맵에 저장하는" 부수효과(`IDataObject` 기본값)는 재현하지 않는다. elk-rs도 import/export 경로 외에서는 재현하지 않는다. import/export에서 필요하면 `getCached` 류 헬퍼를 해당 모듈에 둔다.
- `.proxy raw`(미등록 옵션 문자열)는 typed getter가 파싱한다. 알고리즘 코드가 직접 다룰 일은 없다.
- 알고리즘 내부 속성(`InternalProperties`)은 요소 구조체의 typed 필드다. 예: Rust `node.get_property(InternalProperties::IN_LAYER_LAYOUT_UNIT)` → `(← getNode n).inLayerLayoutUnit`.

## 6. 열거형
```lean
/-- `org.eclipse.elk.core.options.Direction`. -/
elk_enum Direction := undefined right left down up

namespace Direction
def isHorizontal : Direction → Bool | .left | .right => true | _ => false
def opposite : Direction → Direction | .left => .right | .right => .left | .up => .down | .down => .up | .undefined => .undefined
end Direction
```
- Java 이름이 camel→UPPER_SNAKE 규칙과 다르면 `(ctor "JAVA_NAME")`.
- 생성되는 것: `inductive`(BEq/Hashable/Repr/Inhabited/DecidableEq/Ord), `ElkEnum` 인스턴스(`values`, `ordinal`, `javaName`), `ToString`(Java 이름), `PropCodec`(공통 인스턴스), `EnumSet` 지원.
- 파싱: `ElkEnum.ofJavaName?`(정확), `ElkEnum.ofNameLoose?`(elk-rs `parse_enum_value`: 숫자면 ordinal, 아니면 영숫자만 남겨 대문자 비교).

## 7. 수치·문자열 의미론 (`Elk.Core.Util.Java`)
| 원본 | Lean |
|---|---|
| `x.round()` (Rust), `Math.round` 대신 elk-rs가 쓴 round | `x.round` (C round, half away from zero); 정수로는 `Float.roundToInt x` |
| `x as i32`, `(int) x` | `Float.toIntTrunc x` |
| `f64::min/max` | `fmin`/`fmax` (NaN 무시) |
| `Math.min/max` (Java) — elk-rs가 명시적으로 Java 의미론을 재현한 곳만 | `javaMin`/`javaMax` |
| `partial_cmp().unwrap_or(Equal)` | `Float.comparePartial` |
| `total_cmp`, `Double.compare` | `Float.compareTotal`, `Float.compareJava` |
| `f64::INFINITY`, `NAN`, `f64::MAX` | `Float.posInf`, `Float.nan`, `Float.maxValue` |
| `s.parse::<f64>()` | `parseFloat? s` |
| `s.parse::<i32>()` | `parseInt32? s` |
| `format!("{}", x)` (f64 Display) | `Float.toRustDisplay x` |
| JSON 숫자 출력 | `Elk.Json` 프린터가 처리(직접 포맷하지 않는다) |
| `s.trim()` | `s.trimAscii.toString` 또는 `String.jtrim s` (`trimAscii`는 `String.Slice` 반환) |
| `a / b` (Java int) | `Int.tdiv a b`; `a % b` → `Int.tmod a b` |
| `a as f64` | `(a : Int).toFloat` / `n.toFloat` (Nat) |
- `Float` 리터럴은 `2.0`처럼 소수점을 쓴다. `Float` 비교는 `<`, `==` 그대로.
- `Nat` 뺄셈 절단 주의: `i - 1`에서 `i = 0`이면 `0`. 역순 루프는 `while i > 0 do i := i - 1; …` 형태.

## 8. 정렬·난수
- 정렬: `stableSort arr cmp` (`Elk.Core.Util.Sort`). `Array.qsort` 금지. 비교자는 Java `compare`와 동일한 `Ordering` 반환.
  - Java `Collections.sort(list, comparator)` → `stableSort list comparator`.
  - `list.sort_by_key(|x| x.k)` → `stableSortByKey list (·.k)`.
- 난수: `Elk.Core.Util.Random` (java.util.Random 1:1). 값형이므로 상태에 보관하고 갱신한다: `let (v, rnd) := rnd.nextDouble`.

## 9. 예외
```lean
if !supported then throwUnsupportedGraph "Edges connecting different hierarchy levels are not supported."
```
- `throwUnsupportedGraph`, `throwUnsupportedConfiguration`, `throwIllegalState`, `throwIllegalArgument`(`Elk.Core.Exceptions`).
- 순수 함수에서는 `Except String` 또는 `Option`으로 돌려주고 모나드 경계에서 throw 한다.
- `panic!`/`assert!`는 포팅하지 않는다. 도달 불가 분기는 `default`/`0`을 돌려주고 주석으로 표시한다.

## 10. 제어 흐름
- `for x in arr do`, `for i in [0:n] do`, `while cond do`, `break`/`continue`/`return` 모두 `do` 블록에서 사용 가능.
- Rust `loop { … }` → `while true do … break`.
- Rust `for i in (0..n).rev()` → `let mut i := n; while i > 0 do i := i - 1; …` 또는 `for i in [0:n] do let i := n - 1 - i`.
- `Id.run do … return x`로 순수 함수 안에서도 `let mut`/`for`를 쓴다.
- 종료 증명이 어려운 재귀는 `partial def`. 큰 함수는 보조 함수로 분할한다(elaboration 시간).

## 11. 테스트
- 위치: `tests/lean/Tests/<Plugin>/<Suite>.lean`, `def suites : Array Tests.Suite`를 export 하고 `tests/lean/Tests/Main.lean`의 목록에 추가한다.
- 프레임워크(`Tests.Framework`): `suite name do …`, `check name cond`, `checkEq name actual expected`, `checkFloat name actual expected (eps := 1e-9)`, `checkThrows name action`.
- Java/Rust 테스트의 기대값은 그대로 옮긴다(수치 변경 금지). 실행: `lake test`.

## 12. 빌드·검증·보고
```sh
export PATH=$HOME/.elan/bin:$PATH
lake build <Lib>            # 담당 lib만 (예: lake build ElkCore), 경고 0
lake build && lake test     # 종료 전 전체
```
보고에 포함: 변경/추가 파일, 빌드 경고·오류 수, 테스트 결과, 포팅하지 않은 항목과 사유(TODO 위치), 규약 위반 가능성.

## 13. 자주 하는 실수
- `section`, `end`, `at`, `from`, `where` 등은 Lean 예약어 → 필드/함수명으로 쓰지 않는다(`edgeSection` 사용).
- 구조체 필드와 전역 함수 이름이 겹치면 네임스페이스 안에서 필드가 우선한다(`hash` → `Hashable.hash` 명시).
- `String.trimAscii`/`dropEnd`는 `String.Slice`를 돌려준다 → `.toString`.
- `Float.toString`은 소수 6자리 고정 → 출력에 쓰지 않는다.
- `Array.modify`는 인덱스 범위 밖이면 무시, `arr[i]!`는 범위 밖이면 panic 후 `default` → 인덱스 계산을 `Int`로 하고 `toNat` 전에 검사한다.
- `deriving Repr`가 중첩 inductive에서 실패하면 수동 `instance`를 쓴다.
- `set_option linter.* false`로 경고를 숨기지 않는다.

## 14. 알고리즘 내부 그래프 (alg.common 이후)
- 알고리즘 전용 그래프(`NGraph`, `CGraph`, polyomino `PlanarGrid`, spore `Tree`/`Node` 등)도 **arena 배열 + typed id**로 표현한다: `structure NNodeId where idx : Nat`(deriving `BEq, Hashable, Repr, Inhabited, DecidableEq`), 요소는 `graph.nodes[id.idx]`. Rust의 `Rc<RefCell<_>>`/`Weak`/`Arc<Mutex<_>>`, `Rc::ptr_eq`는 모두 id 비교로 대체한다.
- Java `Object`/Rust `Arc<dyn Any>` 타입의 `origin` 페이로드는 구조체의 **타입 매개변수**로 둔다: `structure NNode (ο : Type) where origin : Option ο …`, `structure NGraph (ο : Type)`. 알고리즘은 `ο`에 대해 다형적이며 테스트는 `Unit`/`String`을 쓴다.
- 전략 인터페이스(`ISpacingsHandler`, `ILockFunction`, `ICostFunction`, `IOverlapHandler`, `IConstraintCalculationAlgorithm`, `ICompactionAlgorithm`)는 클로저 필드를 가진 `structure`로 옮긴다. 클로저는 그래프를 인자로 받는 순수 함수(`CGraph → CNodeId → CNodeId → Float`)를 기본으로 하고, 상태 변경이 필요한 것만 모나딕으로 만든다.
- 상태를 가진 알고리즘 객체(`OneDimensionalCompactor`, `NetworkSimplex`, `DepthFirstCompaction`)는 `structure` + `abbrev XM := StateRefT X IO`로 두고, 요소 갱신은 `modifyNode id f` 류 헬퍼로 한다(상태 전체를 `let s ← get`로 묶은 채 `modify` 금지).
- Rust의 `panic!`/`expect`는 `throw (IO.userError "java.lang.IllegalStateException: <원문 메시지>")`(또는 `IllegalArgumentException`)로 옮긴다. 순수 함수에서 실패가 필요하면 `Except String`을 반환한다.
- 순회 순서가 결과를 바꾸는 컬렉션(`HashSet`, `HashMap`, `BTreeSet`, `TreeMultimap`)은 Rust 포팅이 쓰는 순서를 그대로 재현한다. `Array`+삽입 순서(중복 제거는 선형 탐색 또는 `Std.HashSet`로 "존재 여부"만) 또는 정렬 키가 명시된 `stableSort`를 사용하고, 어떤 순서를 재현했는지 docstring에 적는다.
- 부동소수점 비교: Rust `partial_cmp(..).unwrap_or(Equal)` → `Float.comparePartial`, `f64::max/min` → `fmax/fmin`, `total_cmp` → `Float.compareTotal`. `-0.0`, `NaN`, `INFINITY` 상수는 `Float` 리터럴/`(0.0/0.0)` 대신 `Elk.Core.Util.Java`의 상수를 사용한다.

## 15. layered 규약 (Phase 4)
- 모듈 배치: `plugins/org.eclipse.elk.alg.layered/Elk/Alg/Layered/<Pkg>/<JavaClass>.lean`, 네임스페이스 `Elk.Alg.Layered.<Pkg>`. 패키지 집계 모듈 `Elk/Alg/Layered/{Options,Graph,Intermediate,P1Cycles,P2Layers,P3Order,P4Nodes,P5Edges,Components,Compound}.lean`은 담당 작업이 소유한다. 테스트는 `tests/lean/Tests/Layered/<Pkg>.lean`, 집계 `Tests/Layered.lean`.
- 그래프 모델(`Elk.Alg.Layered.Graph`): **단일 arena `LGraphArena`**에 모든 중첩 그래프(`graphs`)·노드·포트·엣지·라벨·레이어를 저장한다. id는 `LGraphId, LNodeId, LPortId, LEdgeId, LLabelId, LayerId`. Rust `Arc<Mutex<_>>`/`Weak`/`LGraphRef` → id, `Arc::ptr_eq` → `==`, `Option<Weak>` → `Option id`. `LGraph.parentNode : Option LNodeId`, `LNode.nestedGraph : Option LGraphId`, `LNode.layer : Option LayerId`, `Layer.nodes : Array LNodeId`(레이어 내 순서가 곧 노드 순서).
- 모나드: `abbrev LayeredM := StateRefT LGraphArena IO`. 접근은 `Elk.Alg.Layered.Graph.Monad`의 `getGraph/getNode/getPort/getEdge/getLabel/getLayer`, `modifyGraph/modifyNode/...`, 생성 `createNode graph`, 연결 `setNodeLayer`, `setEdgeSource/Target`, `setPortNode` 등 Java/Rust의 관계 갱신 메서드와 1:1인 헬퍼만 사용한다(양쪽 리스트를 함께 갱신). 전체 상태를 바인딩한 채 `modify`하지 않는다.
- 요소 구조체 = Java 필드 + `props : PropertyMap`(공개 레이아웃 옵션, ElkGraph에서 복사) + `internal : L<Elem>Internals`(`InternalProperties`를 typed 필드로 옮긴 구조체; 대응표와 Java 기본값은 `Elk/Alg/Layered/Options/InternalProperties.lean`의 docstring). 변환 규칙: `x.get_property(InternalProperties::FOO)` → `(← getNode n).internal.foo`, `set_property(InternalProperties::FOO, Some v)` → `modifyNode n fun x => { x with internal.foo := v }`(또는 `setFoo n v` 헬퍼). 객체값은 id·`Array id`·데이터 구조체(`SelfLoopHolder`, `BreakingPointInfo`는 노드 필드에 값으로, `SplineSegment`는 arena 테이블 + id)로 둔다. `PROCESSORS`는 상태에 두지 않고 `ElkLayered`가 지역 변수로 보관한다.
- 옵션: 공개 옵션 상수는 `LayeredOptions.X`(CoreOptions 별칭 포함, Java `LayeredOptions` 생성 코드와 동일 id/기본값), 열거형은 `elk_enum`(Java ordinal 순서). `Spacings`(내부 간격 테이블)는 `LayeredOptions` 상수와 `NodeType`만 사용하는 순수 구조체.
- 프로세서/페이즈: `LayoutProcessor LayeredM LGraphId`(`name` = Java simple class name; trace 파일명과 `ELK_TRACE_PROCESSORS`에 쓰임), 페이즈는 `LayoutPhase LayeredM LayeredPhases LGraphId IntermediateProcessorStrategy`. 각 전략 열거형(`CycleBreakingStrategy` 등)의 `createPhase`는 해당 페이즈 패키지에서 정의한다.
- elk-rs의 `LArena`/`LArenaBuilder`/`ArenaSync`(CSR SoA 사본)는 성능용 내부 구조이므로 포팅하지 않는다. 그 위에서 동작하는 Rust 코드(p3order/p4nodes/p5edges 일부)는 Lean arena를 직접 쓰되, **ArenaSync가 CSR을 채운 순서**(layers → layer.nodes → node.ports → port.edges, layerless 노드 포함 여부)를 그대로 순회 순서로 쓴다. 각 루프마다 Rust 원본의 순서를 docstring에 적는다.
- 순서 민감 자료구조: Rust의 `FxHashMap`/`HashSet` 순회가 결과에 영향을 주는 곳은 Rust가 그 위에 적용하는 정렬/삽입 순서를 찾아 재현하고, 없으면 oracle trace로 확인해 `HISTORY.md`에 기록한다.
- trace: `ELK_TRACE_DIR`가 설정되면 루트 그래프의 프로세서 실행마다 `step_NNN_<Name>.json`을 기록한다(`Elk.Alg.Layered.TraceRecorder`, elk-rs `trace_recorder.rs`와 동일 스키마: 키 정렬 pretty JSON, `NaN`/`Infinity`/`-Infinity` 센티널 치환, 외부 노드 N/P id 부여 순서). `ELK_TRACE_*` 플래그는 `ElkTrace.global`에서 읽는다.
