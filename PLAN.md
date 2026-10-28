# elk-lean 포팅 계획서

- 문서 버전: 2026-10-27 (Phase 0 완료 시점)
- 대상: Eclipse Layout Kernel(ELK) **0.12.0**의 순수 Lean 4 포팅
- 관련 문서: `AGENTS.md`(작업 방식·품질 게이트·작업 할당 규칙), `HISTORY.md`(진행 이력), `TESTING.md`(검증 절차), `VERSIONING.md`(버전/핀 정책)

---

## 1. 목표

1. **기능 동등성**: ELK Java 0.12.0 / elkjs 0.12.0 / elk-rs 0.12.1이 제공하는 레이아웃 알고리즘과 옵션 메타데이터를 동일하게 제공한다.
2. **출력 동등성(기준: ELK Java 0.12.0)**: 동일한 ELK JSON 입력에 대해 노드 좌표, 엣지 섹션/벤드포인트/정션포인트, 라벨 위치, 그래프 크기를 수정하지 않은 ELK Java 0.12.0(Maven Central 아티팩트)과 값 단위로 정확히(허용오차 0) 산출한다. Java 자체가 실행 컨텍스트(identity hash 순서)에 따라 결과가 달라지는 모델은 Java가 내는 결과 중 하나(열거형 순서)로 고정한다.
3. **단계별 동등성(기준: ELK Java)**: layered 알고리즘의 모든 프로세서(20~140단계) 실행 직후 중간 상태(phase-step trace)가 ELK Java의 상태와 일치한다. elk-rs trace는 보조 기준(엄격 순서 비교)으로 유지한다.
4. **성능·메모리(기준: elk-rs)**: elk-rs 수준을 목표로 한다. 순환 참조 없는 arena 설계로 메모리 누수를 구조적으로 배제하고, hot path는 SoA 배열로 처리한다.
5. **배포**: 네이티브 CLI(`elk`), Node.js NAPI 애드온, WASM(브라우저/Node), elkjs 호환 npm 패키지(`layout()`, `knownLayoutAlgorithms()`, `knownLayoutOptions()`, `knownLayoutCategories()`, Web Worker 모드).

### 비목표
- Eclipse/EMF/Xtext 통합 플러그인(`core.service`, `*.ui`, `*.debug`, `core.meta`, `conn.gmf`)은 포팅하지 않는다(elk-rs도 최소 스텁).
- Graphviz(`alg.graphviz.*`)와 libavoid(`alg.libavoid`)는 외부 바이너리 연동이므로 메타데이터 등록과 스텁만 유지한다(elk-rs와 동일).
- Java 원본의 동작을 "개선"하지 않는다. elk-rs가 Java 기준값 생성 시 적용한 패치 3건(`../elk-rs/scripts/java/patches`)의 취급: (1) self-loop 포트 변 순서 — Java는 `HashMultimap`의 identity hash 순서라 실행마다 달라진다 → Java가 내는 결과 중 하나인 열거형 순서로 고정(elk-rs와 동일); (2) zero-size resize — Java는 중간 포트 좌표가 비유한이 되지만 뒤에 덮어써 최종 출력은 같다 → 최종 출력 기준으로 Java와 일치; (3) zero-height scanline(ticket 213) — 수정 전 Java는 최종 출력에 NaN을 낸다 → **유일한 의도적 예외**로 유한한 결과를 유지하고 `HISTORY.md`에 기록.

## 2. 기준 버전과 레퍼런스

| 레퍼런스 | 위치 | 핀 | 용도 |
|---|---|---|---|
| **ELK Java 0.12.0 (결과 기준)** | Maven Central `org.eclipse.elk:*:0.12.0` (`.reference/m2`), 드라이버 `scripts/java/` | 릴리스 아티팩트(미수정) | **결과·단계별 기준값**(`scripts/run_java_baseline.sh`, JDK 21·Maven 3.9 via mise) |
| elk-rs 0.12.1 (성능 기준) | `../elk-rs` (HEAD `eb586b6d`) | ELK 0.12.0 포팅 + elk-rs 수정 | 주 코드 레퍼런스, 성능 기준(`perf_benchmark`), 보조 trace oracle |
| oracle 바이너리 | `.reference/elk-rs-target/release/` | elk-rs 위 커밋의 release 빌드 | elk-rs 출력/trace 생성 |
| ELK Java 소스 | `external/elk` | `32331291` (v0.12.0) | 알고리즘 의미론 확인, 메타데이터(`*.melk`) |
| elkjs | `external/elkjs` | `ff5771d7` (0.12.0) | npm API/typings, JS 테스트 |
| elk-models | `external/elk-models` | `ac5af2ba` | 검증 코퍼스(1,998 모델) |
| elk-live | `external/elk-live` | `cbf63a24` | 브라우저 통합 예제, elkt 파서 참고 |
| Lean | `lean-toolchain` | v4.35.0 / Lake 5.0 | 툴체인 |

**기준의 역할 분담**: 결과(최종 출력·단계별 상태)의 기준은 수정하지 않은 ELK Java 0.12.0이다(JDK 21·Maven은 `mise`로 설치, 아티팩트는 Maven Central; `scripts/run_java_baseline.sh`가 코퍼스 기준값과 layered 단계별 trace를 생성한다). elk-rs는 코드 레퍼런스이자 성능 기준이며, elk-rs trace 비교(엄격 순서)는 Java trace가 담지 않는 저장 순서까지 보는 보조 검사로 유지한다. elk-rs가 Java 비교에 쓴 패치 3건은 적용하지 않는다(1장 비목표 참조). Java 결과가 실행 컨텍스트에 따라 달라지는 모델은 `--reverse`/`--shuffle` 실행으로 식별해 따로 집계한다.

## 3. 규모 산정 (elk-rs src 기준, 테스트 제외)

| 플러그인 | Rust 파일 | Rust 줄 | Java 줄 | 비고 |
|---|---:|---:|---:|---|
| org.eclipse.elk.graph | 11 | 3,637 | 11,449 | Java는 EMF 생성 코드 포함 |
| org.eclipse.elk.core | 135 | 21,293 | 20,414 | 옵션 메타데이터 1,966줄 포함 |
| org.eclipse.elk.graph.json | 15 | 7,269 | 244(+Xtend) | importer 3,116줄 |
| org.eclipse.elk.alg.common | 89 | 17,172 | 14,677 | nodespacing, networksimplex, compaction, polyomino, spore |
| org.eclipse.elk.alg.layered | 245 | 76,200 | 64,082 | 전체의 50% |
| org.eclipse.elk.alg.force | 27 | 3,098 | 2,236 | force + stress |
| org.eclipse.elk.alg.mrtree | 53 | 6,455 | 5,790 | |
| org.eclipse.elk.alg.radial | 53 | 3,514 | 2,752 | |
| org.eclipse.elk.alg.rectpacking | 53 | 4,897 | 4,688 | |
| org.eclipse.elk.alg.spore | 34 | 2,171 | 1,326 | |
| org.eclipse.elk.alg.disco | 25 | 2,307 | 2,409 | |
| org.eclipse.elk.alg.topdownpacking | 18 | 1,032 | 1,113 | |
| org.eclipse.elk.alg.vertiflex | 29 | 2,341 | 1,693 | |
| org.eclipse.elk.alg.libavoid | 12 | 952 | 1,548 | 스텁 |
| org.eclipse.elk.alg.graphviz.* | 24 | 1,154 | 18,281 | 스텁 |
| **합계** | **823** | **≈153,500** | | 테스트 코드 별도 ≈52,600줄 |

Lean은 Rust보다 간결한 편이지만 do-notation 상태 접근이 추가되므로 산출 코드 규모는 Rust와 비슷한 12만~15만 줄로 예상한다.

## 4. 아키텍처

### 4.1 핵심 설계 결정

**D1. 그래프 표현 = arena(배열) + typed id, 객체 참조 금지**
- Java/Rust는 노드↔포트↔엣지가 서로를 참조하는 객체 그래프다. Lean은 참조 카운팅만 하고 순환을 수집하지 않으므로 `IO.Ref` 상호 참조는 레이아웃마다 누수된다(elk-rs도 Weak 참조로 같은 문제를 수습했다).
- 모든 요소를 `Array`에 보관하고 `structure NodeId where idx : Nat` 같은 typed id로 참조한다. 순환이 없으므로 그래프를 버리면 즉시 해제된다.
- 측정(2026-10-27, Lean 4.35, `StateRefT` 상태 갱신 20만 회): naive `{ g with edges := g.edges.push i }` 6ms, 중첩 `g.nodes.modify i (fun n => {n with x := ..})` 38ms, `set!` 2ms. Lean의 reset/reuse 최적화로 유일 참조 배열은 복사 없이 in-place 갱신된다. 따라서 Rust의 `Arc<Mutex<T>>`/CSR snapshot 같은 우회가 필요 없다.
- 요소 삭제가 필요한 곳(LGraph의 더미 노드 제거 등)은 Java처럼 리스트에서 제거하고 arena 슬롯은 남긴다(`alive` 플래그 없이 레이어/그래프의 노드 리스트가 소속을 정의).

**D2. 알고리즘 모나드 = `StateRefT σ IO`**
- ElkGraph 수준: `abbrev ElkM := StateRefT ElkGraph IO`. 각 알고리즘은 자체 arena(`LGraph`, `FGraph`, `TGraph`...)를 상태로 하는 모나드를 가진다(`LayeredM := StateRefT LGraph IO`).
- `modify`는 ref에서 값을 꺼내(take) 유일 참조로 만든 뒤 갱신하므로 in-place가 보장된다.
- 예외: `throw (IO.userError "org.eclipse.elk.core.UnsupportedGraphException: ...")` 형태로 Java 예외 클래스명을 접두어로 둔다. elk-rs의 JSON API 오류 메시지 규약과 동일하다. `panic!`은 사용하지 않는다(Lean의 panic은 중단되지 않고 기본값을 반환한다).

**D3. 속성 시스템 = 닫힌 `PropValue` 합타입 + 타입 코덱**
- Java `IProperty<T>`/`Object` 맵, Rust `Arc<dyn Any>`에 대응해 `inductive PropValue | bool | int | double | string | enum (ordinal) | enumSet (bits) | vector | vectorChain | padding | margins | individualSpacings | intList | stringList | algorithm (id) | dynamic (Dynamic)`를 정의한다.
- `structure Property (α) where key : PropKey; default : Option α; lower/upper : Option α` + `class PropCodec (α)`로 타입 안전 접근. 열거형은 `ElkEnum` 타입클래스(ordinal, Java 이름, values)를 통해 공통 코덱을 쓴다.
- `PropertyMap`은 `Array (PropKey × PropValue)`(선형 탐색, 사전 계산된 해시 비교). ELK 요소의 옵션 수는 보통 10개 이하이므로 HashMap보다 빠르고 삽입 순서가 결정적이다.
- **내부 속성**(`InternalProperties`, 알고리즘 전용 `Object` 값)은 generic 맵이 아니라 요소 구조체의 **typed 필드**로 둔다(예: `LNode.inLayerLayoutUnit : Option NodeId`). Rust의 `get_property(InternalProperties::X)` 호출은 필드 접근으로 변환한다. 변환 대응표는 layered 포팅 착수 시 `plugins/org.eclipse.elk.alg.layered/PORTING.md`에 정리한다.

**D4. 중첩 그래프 = 단일 arena**
- layered의 계층 처리(`nestedGraph`/`parentNode`)는 그래프마다 별도 arena를 두지 않고, 하나의 arena 안에 `graphs : Array LGraphData`를 두고 노드가 `graph : GraphId`를 갖는다. 그래프 간 참조(외부 포트 더미, 계층 교차 엣지)가 모두 전역 id로 표현된다.

**D5. 부동소수점과 Java 의미론**
- `Float`(C double)로 계산한다. 출력 포맷은 Lean `Float.toString`(소수 6자리 고정)을 쓰지 않고 C shim `elk_float_to_shortest`(최단 round-trip, serde_json/ryu 스타일: `12.0`, `0.1`, `1e21`, `1.5e-7`)를 쓴다. 파싱은 C `strtod`(정확한 반올림).
- Java 의미론 헬퍼를 `Elk.Core.Util.Java`에 모은다: `Math.round`(floor(x+0.5), NaN→0), `Math.min/max`(NaN 전파; 단 elk-rs가 Rust 의미론을 쓴 지점은 elk-rs를 따름), int 나눗셈/나머지(`Int.tdiv`/`Int.tmod`), 32비트 wrap(`Int32`), `Double.compare`, `Math.signum`, `Math.hypot`.
- `Nat` 뺄셈 절단을 피하기 위해 음수가 될 수 있는 정수는 `Int`로 포팅한다.

**D6. 정렬**: Java `Collections.sort`(TimSort, 안정)와 Rust `sort_by`(안정)에 맞춰 `Elk.Core.Util.Sort.stableSort`(병합 정렬)를 사용한다. Lean `Array.qsort`는 불안정하므로 사용 금지. 비교자는 Java 비교자를 `α → α → Ordering`으로 1:1 이식한다.

**D7. 난수**: `java.util.Random`(48비트 LCG, `nextDouble/nextInt(bound)/nextBoolean/nextFloat/nextLong`)을 elk-rs `core/util/mod.rs::Random`과 동일하게 이식한다. `ELK_RANDOM_TRACE` 디버그 출력도 유지한다.

**D8. 메타데이터 레지스트리**: `LayoutMetaDataService`는 전역 `IO.Ref`(`builtin_initialize`)로 둔다. 알고리즘/옵션/카테고리 등록은 `Elk.Api.ensureInitialized`에서 한 번 수행한다. FFI 진입점은 C에서 모듈 initializer를 호출한 뒤 사용한다.

**D9. JSON**: 자체 `Elk.Json.Value`(객체는 삽입 순서 보존 배열, 숫자는 정수/실수 구분 보존)와 파서/프린터를 구현한다. elkjs처럼 입력 객체를 그대로 유지하면서 레이아웃 결과 키(`x`, `y`, `width`, `height`, `sections`, `junctionPoints`, 라벨 좌표)를 Java `JsonImporter.transferLayout` 순서로 추가한다. `lenient` 모드(JSON5 유사: 주석, 따옴표 없는 키, 작은따옴표, 후행 쉼표)는 elk-rs `preprocess_lenient_json`을 따른다. 출력 숫자 규칙은 oracle(elk-rs `f64_to_number`)과 동일하게 한다: 유한값이 정수와 1e-6 이내면 정수로 출력(`"x": 12`), 그 외는 최단 round-trip 실수(`27.5`). elk-rs는 serde_json 기본 맵(BTreeMap)이라 키가 정렬되어 출력되므로, 바이트 단위 비교가 필요할 때를 위해 `--sort-keys` 옵션을 제공한다(기본은 삽입 순서 = elkjs 방식).

**D10. 빌드/배포**: Lake 멀티-lib 단일 패키지. C shim은 정적 라이브러리로 링크한다. NAPI/WASM은 Lake가 생성한 모듈별 C 코드(`.lake/build/ir/**/*.c`)와 Lean 런타임(`libleanrt`, `libInit`, `libStd`)을 전용 스크립트로 링크한다(WASM은 Lean 런타임·stdlib C를 emscripten으로 빌드).

### 4.2 모듈 구조

```
elk-lean/
├─ lakefile.lean, lean-toolchain
├─ plugins/
│  ├─ org.eclipse.elk.graph/Elk/Graph/…           lib ElkGraph   (Ids, Enum, Properties, Model, Util)
│  ├─ org.eclipse.elk.core/Elk/Core/…             lib ElkCore    (Math, Util, Options, Data, Alg, Validation, Labels, Engine, Providers)
│  │   └─ c/elk_core_ffi.c                        C shim (정적 라이브러리 libelkcoreffi)
│  ├─ org.eclipse.elk.graph.json/Elk/Json/…       lib ElkJson    (Value, Parser, Printer, Importer, Exporter, Adapter, MetaDataConverter)
│  ├─ org.eclipse.elk.alg.common/Elk/Alg/Common/… lib ElkAlgCommon
│  ├─ org.eclipse.elk.alg.layered/Elk/Alg/Layered/… lib ElkAlgLayered (Graph, P1Cycles…P5Edges, Intermediate, Components, Compound, Options, Trace)
│  ├─ org.eclipse.elk.alg.{force,mrtree,radial,rectpacking,spore,disco,topdownpacking,vertiflex,libavoid,graphviz}/
│  ├─ org.eclipse.elk.api/Elk/Api/…               lib ElkApi     (등록, layoutJson, knownLayout*, trace 제어)
│  ├─ org.eclipse.elk.ffi/Elk/Ffi/…               lib ElkFfi     (@[export] C 진입점)
│  ├─ org.eclipse.elk.cli/Main.lean               exe elk
│  ├─ org.eclipse.elk.napi/                        node-addon-api C++ 셸 + 빌드 스크립트 (Phase 8)
│  ├─ org.eclipse.elk.wasm/                        emscripten 빌드 스크립트 (Phase 8)
│  └─ org.eclipse.elk.js/                          npm 패키지(elkjs 호환 로더, typings, vitest) (Phase 8)
├─ tests/lean/Tests/…                              exe elktest (`lake test`)
├─ tests/model_parity*/                            parity 산출물(대부분 gitignore)
├─ scripts/                                        oracle 실행, 입력 생성, 비교 스크립트
├─ external/{elk,elkjs,elk-models,elk-live}        서브모듈(수정 금지)
└─ .reference/                                     elk-rs oracle 빌드 산출물(gitignore)
```

레이어 규칙(import는 아래 방향으로만): `Elk.Core.Math`(leaf) ← `Elk.Graph` ← `Elk.Core` ← `Elk.Alg.Common` ← `Elk.Alg.*` ← `Elk.Json` ← `Elk.Api` ← CLI/FFI. `Elk.Core.Math`는 `Elk.Graph.Properties`가 KVector 등을 담아야 하므로 예외적으로 Graph보다 아래에 둔다(Java 패키지 위치는 유지).

Java/Rust 파일과 Lean 모듈은 1:1로 대응시킨다: `org.eclipse.elk.alg.layered.p3order.LayerSweepCrossingMinimizer` → `plugins/org.eclipse.elk.alg.layered/Elk/Alg/Layered/P3Order/LayerSweepCrossingMinimizer.lean`.

### 4.3 Rust → Lean 변환 규칙

| Rust(elk-rs) | Lean(elk-lean) |
|---|---|
| `Arc<Mutex<LNode>>`, `LNodeRef`, `Rc<RefCell<ElkNode>>` | `NodeId` (arena 인덱스) |
| `node.lock().get_property(X)` (옵션) | `(← getNode n).props.get X` 또는 typed 접근자 `nodePortConstraints n` |
| `get_property(InternalProperties::X)` | typed 필드 `(← getNode n).x` |
| `set_property(X, v)` | `modifyNode n fun nd => { nd with x := v }` |
| `Vec<T>` | `Array T` (List 사용 금지) |
| `FxHashMap<K,V>` / `HashSet` | `Std.HashMap` / `Std.HashSet`; 순회 순서가 결과에 영향을 주면 삽입 순서 구조로 대체 |
| `sort_by(cmp)` | `stableSort cmp` |
| `f64`, `i32`, `usize` | `Float`, `Int`(또는 `Int32`), `Nat` |
| `panic!/unwrap` (Java 예외) | `throw (IO.userError "<JavaExceptionClass>: msg")` |
| trait `ILayoutProcessor` | `structure LayoutProcessor where name : String; process : GraphId → LayeredM Unit` |
| enum + `impl` | `elk_enum` 매크로(ordinal/Java 이름/EnumSet 코덱 자동 생성) |
| `Option<T>` | `Option T` |
| 클로저 비교자 | `fun a b => …` (`Ordering`) |

### 4.4 데이터 모델 스케치

```lean
-- Elk.Graph (org.eclipse.elk.graph)
structure NodeId where idx : Nat      -- PortId, EdgeId, LabelId, SectionId 동일
inductive ConnectableId | node (n : NodeId) | port (p : PortId)
structure ElkNode where
  identifier : Option String; x y width height : Float
  props : PropertyMap; labels : Array LabelId
  parent : Option NodeId; children ports containedEdges incomingEdges outgoingEdges : Array …
structure ElkGraph where nodes ports edges labels sections : Array …

-- Elk.Alg.Layered.Graph
structure LNode where
  graph : GraphId; type : NodeType; pos size : KVector; margin : LMargin; padding : LPadding
  layer : Option LayerId; ports labels : Array …; nestedGraph : Option GraphId; props : PropertyMap
  -- InternalProperties (typed)
  origin : Option Origin; inLayerLayoutUnit : Option NodeId; longEdgeSource longEdgeTarget : Option PortId; …
structure LGraph where
  graphs : Array LGraphData   -- 중첩 그래프(루트는 0)
  nodes : Array LNode; ports : Array LPort; edges : Array LEdge; labels : Array LLabel; layers : Array Layer
```

### 4.5 in-place 갱신 규약 (성능 핵심)
1. 상태 전체를 바인딩한 뒤 `modify`를 호출하지 않는다. `let g ← get` 후 `g`를 갱신 이후에도 사용하면 배열이 복사된다. 필요한 값(id, 좌표)만 꺼낸다. (Lean은 마지막 사용 직후 참조를 해제하므로, 갱신 전에 `g`의 사용이 끝나면 안전하다.)
2. 요소 갱신은 `modifyNode id f` 헬퍼로만 한다(`Array.modify`가 요소를 swap-out 해 유일성을 보장).
3. 배열 필드 갱신은 `{ s with arr := s.arr.push x }` 형태를 허용한다(측정상 in-place).
4. hot loop(교차 계산, BK 배치, 네트워크 심플렉스, force 반복)는 `FloatArray`/`Array Nat` SoA 로컬 배열로 계산하고 결과를 한 번에 기록한다.
5. 프로세서 간에는 arena 외의 전역 가변 상태를 두지 않는다(trace 카운터 제외).

### 4.6 phase trace 포맷
elk-rs HEAD `trace_recorder.rs`와 동일한 `<trace_dir>/<model>/step_NNN_<Processor>.json`(nodes/layers/edges(sourceNode·sourcePort·targetNode·targetPort·bendPoints·labels)/externalNodes/graphSize/padding/offset/size, NaN·Infinity 센티널, 단일 노드 압축 보정 포함)을 `ELK_TRACE_DIR` 환경변수로 출력한다. oracle 스모크(2노드 1엣지 layered)는 19단계(`step_000_EdgeAndLayerConstraintEdgeReverser` … `step_018_ReversedEdgeRestorer`)를 생성한다. 비교는 elk-rs `compare_phase_traces.py`(위치 기반, ID 무시, tolerance 0.001)를 그대로 사용한다.

## 5. 단계별 계획

| Phase | 범위 | 산출물 | 완료 기준(게이트) |
|---|---|---|---|
| **0. 초기 설정** (완료) | 툴체인, lakefile(17 lib + 2 exe + C shim), 서브모듈 핀, oracle 빌드, 문서, 스크립트 골격 | 본 문서, `AGENTS.md`, `HISTORY.md`, `TESTING.md`, `VERSIONING.md`, `scripts/` | `lake build`·`lake test` 통과, oracle 실행 가능 |
| **1. 기반 계층** | `Elk.Graph`(ids, enum 매크로, PropValue/Property/PropertyMap, ElkGraph arena, ElkGraphUtil), `Elk.Core.Math`(KVector, KVectorChain, Spacing/Padding/Margin, Rectangle, ElkMath, BezierSpline, CubicSplineInterpolator), `Elk.Core.Util`(Random, Sort, Java 헬퍼, EnumSet, IndividualSpacings, ProgressMonitor, ElkUtil, ElkSpacings), `Elk.Core.Options`(열거형 전부, CoreOptions, 메타데이터), `Elk.Core.Data`(LayoutMetaDataService, Option/Algorithm/CategoryData, Resolver, DeprecatedReplacer), `Elk.Core.Alg`(AlgorithmAssembler, LayoutProcessorConfiguration), validation, labels | 단위 테스트(elk-rs `core/tests` 중 해당분) | `lake test` 통과, 옵션 메타데이터 수/ID/기본값이 elk-rs `known_layout_options()` 출력과 일치 |
| **2. JSON·엔진·CLI** | `Elk.Json`(Value/Parser/Printer, Importer, Exporter, Adapter, MetaDataConverter), `RecursiveGraphLayoutEngine`, Fixed/Box/Random/Topdown provider, GraphValidator, `Elk.Api.layoutJson`, CLI(`layout`, `algorithms/options/categories`, `--trace-dir`), parity 파이프라인(입력 생성→oracle→lean→비교) | `elk layout in.json` 동작, `scripts/run_model_parity.sh` | fixed/box/random 알고리즘 모델에서 model parity 100% |
| **3. alg.common** | nodespacing(cellsystem, NodeLabelAndSizeCalculator, NodeDimensionCalculation), networksimplex, compaction(oned, polyomino, recthull), spore(상호 모듈), overlaps, utils(SVGImage 제외), `ElkGraphAdapters` | 단위 테스트 | elk-rs `alg.common/tests` 이식분 통과 |
| **4. layered** | 4a 그래프 모델·importer/exporter·GraphConfigurator·ElkLayered 드라이버·trace recorder, 4b P1 cycles·P2 layers, 4c intermediate 프로세서(≈60), 4d P3 crossing minimization, 4e P4 node placement(BK, NetworkSimplex, Linear, Simple, Interactive), 4f P5 edge routing(orthogonal/polyline/splines)·self loops·components·compound·wrapping | trace parity 리포트 | 1,998 모델 중 layered 모델 전부 model parity + phase-step 일치 |
| **5. 기타 알고리즘** | force/stress, mrtree, radial, rectpacking, spore, disco, topdownpacking, vertiflex, libavoid/graphviz 스텁 | 알고리즘별 parity | 해당 알고리즘 모델 model parity 100%, `known_layout_algorithms()` 일치 |
| **6. 텍스트 포맷** | `.elkt` 파서(elk-rs `elkt_test_loader` + elk-live TS 파서 참고), CLI `convert` | `elk convert x.elkt --to json` | 898개 `.elkt` 변환 성공, Java export와 의미 동일 |
| **7. 전수 검증·최적화** (진행 중) | ELK Java 기준값·단계별 trace(`scripts/run_java_*`), elk-rs 보조 parity, 메모리 수명 검사, 성능 최적화(FastFloat·파서·zmij·force/stress·P3·P5·mrtree/rectpacking) | `HISTORY.md` 수치, `tests/perf/report.md` | Java 결과 정확 일치 1,878/1,997(나머지는 Java 컨텍스트 의존·NaN 예외), Java 단계별 1,817/1,997(나머지 Java 측 요인), elk-rs 1,447/1,447; 성능은 2차 최적화(PF2·PN·PJ·PL5·PL3b)와 전역 `Array.modifyIn`으로 합성 26개 기하평균 0.91배, 3차 라운드(PS 스플라인·PH hierarchy/공통 경로·PJ2 JSON)로 **0.82배**(26개 중 최악 routing_orthogonal 1.05배), 코퍼스 1,447개 총합 1.23배·기하평균 1.09배(7.1 참조). 남은 일: 큰 layered 그래프의 P3(elk-rs 대비 약 2.1배), 분기 안 Float 리터럴 상수화, 무작위 그래프 시간 초과/오버플로 입력의 Java 분류 |
| **7b. 무작위 입력 Java parity** (진행 중) | `scripts/run_random_java_parity.sh`(seed 1~10 × 600, s/v/d 세트)로 코퍼스 밖 입력의 ELK Java 일치율을 재고 불일치 클래스(NML·SEC·LNODE·DEF·LEDGE·POS)를 하나씩 Java 동작으로 수정, Java `TimSort`(`JavaSort`)·노드 크기 검증·오류 문구 이식 | `tests/random_parity/report.md`, `docs/robustness-random-graphs.md` | v 세트 정확 일치 616/5,761(10.7%) → 목표: Java 자체 결함(AIOOBE·NPE·StackOverflow)을 제외한 전 입력 정확 일치; 코퍼스 Java 정확 1,878/1,997 유지 |
| **8. 배포** (대부분 완료) | `Elk.Ffi`+`elk_lean.h` C API, NAPI C 애드온, WASM(emscripten, MEMORY64=2), npm 패키지(elkjs 호환 로더/Worker/typings, WASM 폴백, 깊은 재귀용 `workerStackSizeMb` Worker 모드), `node:test` 56개, `.gitlab-ci.yml` 초안·`CHANGELOG.md`·릴리스 예행 문서 | `elk-lean` npm 패키지(미게시) | NAPI vs CLI 1,447/1,448 바이트 일치, WASM 550/550; 남은 일: Linux/Windows 빌드(CI 미실행), 게시(`private` 제거), GMP 라이선스 검토(G1) |
| **9. 릴리스** | CHANGELOG, 문서, 태그 | `v0.12.0` | 품질 게이트 전항목 통과 |

병렬화: Phase 1~2는 규약을 정하는 단계이므로 직렬로 진행한다. Phase 3 이후는 플러그인/서브패키지 단위로 서브에이전트에 분배한다(각 작업은 "대응 Rust 파일 목록 + 규약 문서 + parity 명령"을 받고, 빌드 경고 0·테스트 통과·parity 수치를 보고한다).

## 6. 검증 체계

1. **코드 품질**: `lake build`(오류/경고 0), `lake test`(실패 0). Lean에는 clippy가 없으므로 린터 옵션(`linter.unusedVariables` 등 기본 린터)을 경고 0으로 유지한다.
2. **Model parity**: `scripts/run_model_parity.sh <models> <out>` — (a) `.json` 모델은 그대로, `.elkt`는 Phase 6까지 oracle 측 변환 결과로 입력 생성, (b) oracle(`model_parity_layout_runner`)로 기준 출력, (c) `elk layout`으로 Lean 출력, (d) `compare_model_parity_layouts.py`(semantic, abs-tol 1e-6)로 비교, `report.md`/`diff_details.tsv` 생성.
3. **Phase-step trace**: `ELK_TRACE_DIR`로 양측 trace 생성 후 `compare_phase_traces.py --batch`. 첫 불일치 단계를 보고한다.
4. **메타데이터 parity**: `elk algorithms|options|categories` 출력과 oracle `perf_benchmark`/elk-rs API 출력의 JSON 비교(ID, 이름, 설명, 타입, 대상, 기본값, 의존성, 지원 기능).
5. **JS parity**(Phase 8): elk-rs `test/parity/run.mjs`를 이식해 NAPI/WASM/elkjs 3자 비교.
6. **성능**: elk-rs `perf_benchmark --engine rust_native|rust_api --mode synthetic` 시나리오 26개를 Lean CLI/API로 재현(동일 LCG 그래프 생성기), 머신 정보와 함께 기록.
7. **메모리**: 반복 레이아웃(동일 입력 1,000회) 후 RSS 증가 0 확인(`/usr/bin/time -l`), Lean `LEAN_ABORT_ON_PANIC=1`로 panic 0 확인.

## 7. 성능·메모리 전략
- arena/SoA(D1), in-place 규약(4.5), `@[inline]`/`@[specialize]`로 모나드 헬퍼 오버헤드 제거.
- 속성 조회: `PropKey`에 사전 계산 해시, 자주 쓰는 옵션은 typed 캐시 필드(elk-rs Phase A-2와 동일 발상).
- 문자열 비교·생성 최소화(요소 ID 문자열은 import 시 한 번만 생성).
- `Nat`/`Float` 스칼라는 박싱되지 않으므로 구조체 필드로 유지; `Array Float`는 박싱되므로 hot path는 `FloatArray`.
- 메모리: 순환 없음 → 누수 없음. 큰 중간 구조(trace 스냅샷, SoA)는 프로세서 종료 시 해제.
- 측정 후 결정: 프로파일(`perf`/Instruments)에서 상위 항목만 최적화하고 elk-rs와 동일한 벤치마크 표로 기록한다.

### 7.1 Lean 성능 관용구 (프로파일로 확인된 함정, 2026-10-27)
측정·분석 도구: `elk bench`(시나리오별 시간), `sh scripts/perf/profile_bench.sh <scenario>`(macOS `sample`), `scripts/perf/sample_inclusive.py`(단계별 포함 시간), `scripts/perf/sample_callers.py`(할당·배열 복사 호출자), `sh scripts/perf/scan_generated_c.sh [경로]`(생성 C 정적 검사). 모든 최적화는 출력 비트 일치가 조건이다(`lake test`, 코퍼스 model parity, layered는 strict trace parity).

1. **Float 변환·리터럴**: 코어 `Float.ofScientific`/`ofNat`/`ofInt`/`Nat.toFloat`는 호출마다 GMP 문자열 파싱을 한다. `Elk.Core.Util.FastFloat`의 `@[csimp]`·고우선 인스턴스가 모든 모듈에서 이를 비트 동일한 빠른 경로로 바꾼다(leaf 모듈이 import). 새 leaf 모듈을 만들면 `import Elk.Core.Util.FastFloat`를 넣는다. 코어의 `Nat.toFloat`/`Int.toFloat`는 `Float.ofNat`/`Float.ofInt`의 abbrev라 csimp 뒤에 인라인되어 느린 경로가 드러나므로 둘 다 별도 csimp 보조정리로 잡는다(`(i : Int).toFloat` 호출 5개 모듈이 GMP 경로였음). 생성 C에서 `l_Float_ofInt(`·`l_Float_ofNat(`·`l_Float_ofScientific(` 호출이 `FastFloat.c` 밖에 없어야 한다(`scan_generated_c.sh`).
2. **2^32 이상 `Nat`/`Int` 리터럴 금지(런타임 경로)**: C 백엔드가 `lean_cstr_to_nat("…")`로 매번 파싱한다. `UInt32`/`UInt64` 연산, 시프트(`n >>> 32 != 0`)로 쓴다.
3. **`for` 루프의 가변 상태**: 가변 변수가 2개 이상이면 상태가 `MProd`로 묶여 반복마다 분해·재구성되고 `Float`는 박싱된다(`lean_box_float` 할당). 핫 루프는 상태를 인자로 받는 꼬리 재귀 `partial def`로 쓴다(`Float`/`UInt*`/`Bool` 인자는 unboxed, 결과 튜플은 끝에서 한 번). 예: `FruchtermanReingoldModel.scanForces`, `StressMajorization.newPositionSums`.
4. **변환·조회는 루프 밖으로**: `Float.ofInt`, 속성 조회(`getD`), `HashMap` 조회는 루프 전에 `FloatArray`/`Array`로 미리 만든다. id로 인덱싱하는 배열이 해시맵보다 빠르다.
5. **모나드 안의 내부 루프**: `StateRefT` 위의 반복은 반복마다 클로저 호출이 생긴다. 필요한 배열을 한 번 꺼내 순수 함수로 계산하고 결과를 한 번에 쓴다. 상태 전체를 바인딩(`let g ← get`)한 채 수정하면 배열 복사(`lean_copy_expand_array`)가 생긴다.
6. **작은 할당 줄이기**: 핫 경로에서 `Option`/튜플/`KVector` 반환을 피하고(인자로 분해), 작은 도우미에는 `@[inline]`을 붙인다. `Array`에서 원소를 꺼내 고칠 때는 `modify`(소유권 이전)를 쓴다.
7. **NaN 판정**: `Float.isNaN`/`isFinite`/`isInf`도 FastFloat가 인라인 비교로 바꾼다(코어는 out-of-line C 호출). 핫 루프에서는 `x != x`가 가장 확실하다.
8. **루프 안의 Float 리터럴**: 컴파일러가 추출하지 못한 리터럴은 반복마다 `FastFloat.ofScientificImpl`을 부른다 → 최상위 `def` 상수(단순 load)로 뺀다.
9. **`Int`와 리터럴 `0` 비교**는 평가마다 `lean_obj_once`(전역 `Int` 상수의 초기화 검사)를 거친다. `Int` 생성자 매칭(`.ofNat`/`.negSucc`)도 Lean 4.35에서는 같은 `lean_int_dec_lt(x, lean_obj_once(0))`로 컴파일되므로 대안이 아니다(PL5·주 에이전트가 생성 C로 확인). 핫 경로는 값을 `UInt64`/`Nat`로 바꾸거나 부호를 별도 `Bool`로 들고 다닌다.
10. **열거형 `BEq`**(derived)는 `ctorIdx`를 거치는 out-of-line 호출 → 핫 경로는 `match`나 `UInt8` 비교.
11. **중첩 구조체의 배열 필드를 루프/분기 안에서 `{ d with f := d.f.modify … }`로 갱신**하면 바깥·안쪽 배열이 복사될 수 있다(참조가 남는 경우). `match d with | ⟨a, b, …⟩ => ⟨…⟩`로 분해해 필드를 유일 소유로 유지한다(PL3 `BarycenterData`/`ForsterData`).
12. **전역 `stableSort`/`rustSortBy`는 특수화되지 않아** 비교마다 클로저 호출·박싱이 든다 → 핫 경로는 키를 미리 뽑아 전용 정렬(같은 비교 순서)로 처리한다(PL3 삽입 정렬, PT 키 정렬).
13. **분기·조인 뒤의 `{ s with … }` 갱신은 객체를 재사용하지 못한다**: 모든 필드를 투영해 새 객체를 할당한다(26필드 `ImporterState`는 갱신마다 재할당). 직선 코드의 `{ g with … }`(`ElkGraph.modifyNode`)는 괜찮다. 핫 갱신은 분기 없는 생성자 매치(`match s with | ⟨a, b, …⟩ => ⟨a', b, …⟩`)로 쓴다(PJ `ImporterState.addNode` 등).
14. **double 비트 패턴을 `Int`로 비교하지 않는다**: 대부분의 비트 패턴이 small-`Int` 범위 밖이라 비교마다 GMP 수가 할당된다(`Float.compareTotal`/`compareJava`, P5 정렬). 부호 비트를 뒤집은 `UInt64` 키를 비교한다. `2^64`/`2^32` 리터럴을 쓰는 부호 변환도 `~~~`(보수)로 바꾼다(PJ, 차분 테스트 `core.util.java`).
15. **증명된 인덱스로 unchecked 접근**: `USize` 인덱스와 `i < a.usize` 증명(`usize_lt_size`)으로 `uget`/`uset`을 쓰면 `Nat` 박싱 검사 없는 직접 load가 된다. 배열 크기 동치는 루프 밖에서 한 번 검사하고(`scanForces`), 실패 시 checked 복사본으로 간다(PF2 force 쌍 루프, rectpacking 스캔). 어댑터 읽기(부작용 없음)는 한 번 읽어 재사용하고, 빈 컨테이너(라벨 없는 셀·스트립)는 생성하지 않는다(PN).
16. **`Array.modify`에 인라인된 직선 갱신 람다는 원소를 매번 재할당한다**(Lean 4.35): 컴파일러가 원소의 필드 읽기와 exclusivity 검사를 `modify`가 슬롯을 비우기(`fset dummy`) *전에* 두어(배열이 아직 원소를 참조) 재사용이 항상 실패한다. 분기가 있는 갱신과 `@[noinline]` 갱신 함수는 괜찮다. 모든 arena 헬퍼(`ElkGraph.modifyNode`, `LGraphArena.modifyNode/Port/Edge/…`, 각 알고리즘 arena)는 `Array.modifyIn`(`Elk.Graph.ArrayModify`: 슬롯을 비운 뒤 경계 재검사 분기 안에서 갱신)을 쓴다 — 생성 C에서 `lean_array_fset(.., box(0))`가 `lean_is_exclusive` 앞에 와야 한다. 새 arena 헬퍼도 `modifyIn`으로 쓴다.
17. **분기 안의 Float 리터럴은 closed term에서 빠질 수 있다**(PS): `if h : j < xs.size then … 1.0 …` 같은 분기 안에서 컴파일러가 리터럴의 부호 플래그(`true`)를 참으로 알려진 비교 결과 변수로 CSE 치환하면 `FastFloat_ofScientificImpl(10, v_cond, 1)`처럼 평가마다 파싱된다(`getPointOnBezierSegment`의 `1.0`, `binomialdU`의 `0.0`, `calculateControlPointsStraight`의 `/ 2.0`). 분기 밖으로 끌어내거나(`1 - t`를 인자로) 최상위 상수로 둔다. `scan_generated_c.sh`가 `_init_` 밖의 `FastFloat_ofScientificImpl(` 호출을 `ofSciImpl`로 보고한다(FastFloat.c 자신의 폴백은 정상).
18. **`FloatArray`의 `xs[i]!`는 out-of-line 경계 검사 람다를 부른다**: `xs.get!`는 인라인 검사이고, 증명된 `USize` 인덱스의 `uget`(15번)이 가장 빠르다(효과는 작음). 프로파일 읽기 메모: 특수화된 함수 이름은 그 특수화를 처음 만든 함수를 따르므로(`…arenaIncomingEdges_spec__N`이 라우터의 `HashSet LPortId` 연산일 수 있음) 호출자 기준으로 확인한다.
19. **루프 진입마다 range 객체**(PJ2): `for h : i in [0:n]`는 들어갈 때마다 `Std.Legacy.Range`(`lean_alloc_ctor(0,3,0)`)를 할당한다 — 재귀 프린터처럼 작은 루프를 객체마다 도는 곳에서는 꼬리 재귀로 바꾼다. `Id.run do`에서 여러 `let mut`을 루프가 아닌 `if` 분기 안에서 갱신해도 join point마다 튜플이 할당된다(`parseNumber`) → `let` 체인으로.
20. **모나드 헬퍼의 `Float` 반환·`Option` 인자**: `StateRefT`에서 `Float`을 반환하는 헬퍼가 inline되지 않으면 호출마다 box/unbox(`globalX`), inline되지 않은 함수에 `some x`를 넘기면 호출마다 `some` 할당+박싱(`doubleValueValid`). 상태를 한 번 읽고 순수 함수로 계산하거나 인자를 분해한다. `let st ← get`를 쥔 채 `modify`로 모델을 갱신하면 상태와 JSON 트리가 공유되어 경로 배열이 복사된다(`transferLayoutPort` compaction 분기, 수정됨).
21. **문자열 바이트 루프**: ASCII 한 글자 `String.push`도 out-of-line UTF-8 인코더를 거친다 → 구두점은 `++ "리터럴"`로 합치거나 미리 렌더한 표로 append 횟수를 줄인다. `String.Internal.ugetUTF8Byte`에 `USize` 인덱스를 쓰면 문자열도 scalar 바이트 루프가 된다(15번의 String판; 범위 증명은 `Nat.toUSize`가 mod이므로 `Nat.mod_le`로 충분). Internal API라 `Elk.Json.Value`의 `Utf8.uget` 한 곳에만 둔다.
22. **인라인·특수화 뒤의 리터럴과 콜백**(PH): 인라인/`@[specialize]`된 코드에서는 Float 리터럴의 `Nat`/`Bool` 인자가 무관한 상수(배열 인덱스 `1`, join point를 지난 `true`)와 CSE로 공유되어 루프 밖에서도 런타임 `ofScientificImpl` 호출이 된다(셀 레이아웃 인라인으로 `CellDispatch`에 180곳) → 전역 `def` 상수(`cellZero`/`cellTwo`). 자기 자신을 넘기는 `partial def` 콜백을 받는 고차 코드는 소비자에 `@[specialize]`를 붙이면 직접 재귀 호출·unboxed `Float` 반환이 되고, 클로저로 두면 호출마다 `lean_apply`+박싱이다. `Float × Float × Float` 반환은 할당 5번, Float 필드 구조체는 1번(인라인되면 0).
23. **구조체 갱신 시 생존 참조와 해제 귀속**: `{ s with f := g s.f }`는 `s`가 아직 살아 있으면(예: 직전에 borrowed 인자로 넘김) 필드 배열을 복사하고, 그 뒤의 갱신은 16필드 `NodeContext`를 재사용하지 못하고 새로 할당한다 → 필드를 먼저 꺼낸다. 큰 노드별 구조체의 해제는 마지막 참조를 놓는 함수에 귀속되어 프로파일에 엉뚱한 함수(`applyPortPositions`)로 나타난다. `IO Float`를 반환하는 헬퍼(`Spacings.getVerticalSpacing`)는 결과가 박싱된다.
24. **리터럴 상수화의 세부**(FL): 리터럴의 부호/지수 인자는 람다 리프팅으로 클로저 인자나 join point 인자로도 전달된다(`…___lam__5(…, x_264, x_265)`가 `ofScientificImpl(20, x_264, x_265)`); 구조체 필드 기본값(`width : Float := 0.0`)은 `{ … }` 생성 지점마다 인라인되어 런타임 리터럴이 되므로 전역 상수로 둔다; 인라인된 헬퍼의 리터럴은 스캔에서 호출자 밑에 나타나므로 헬퍼를 고친다; 같은 모듈 안의 상수 사용은 `lean_float_once`(load+분기)로 다시 인라인되고 다른 모듈에서만 plain load다; 인자 없는 모나드 액션(`def initState : M Unit := do … 0.0`) 안의 리터럴은 상수가 아니라 호출마다 평가된다. 제거되는 비용은 C 빠른 경로 1회(GMP 아님)라 측정 가능한 효과는 핫 루프에서만 난다(FL 전체 효과 ≈0).
25. **핫 알고리즘 코어의 모나드와 컨테이너**(P3L): `ExceptT String (StateM σ)`로 짠 핵심(Forster)은 표를 순수 꼬리 재귀로 전달하는 것보다 약 3.4배 느렸다 — 드문 실패는 상태 플래그+실패 시점 상태로 정확히 재현할 수 있다. 호출마다 만드는 `HashSet`/`HashMap`은 객체에 보관한 scratch `ByteArray`/`Array`(arena 인덱스로 접근, 건드린 항목만 0으로)로 바꾼다. 작은 상태 구조체(`BarycenterData`+`Random`)를 원소마다 넘기면 원소당 객체 2개가 할당되므로 핫 필드만 전달하는 전용 run을 쓴다. `Array.shrink 0`은 저장 공간을 유지하지만(Rust `Vec::clear`) 원소를 하나씩 pop해 O(len)이다.
26. **`Nat` 왼쪽 시프트와 인라인 헬퍼의 join point**(P3L): `lean_nat_shiftl`은 작은 값에서도 out-of-line(GMP 경로 의심)이라 `Nat <<<`로 53비트 키를 패킹하면 느려진다(`UInt64` 시프트 사용; 오른쪽 시프트는 인라인). 인라인된 헬퍼 안의 join point(분기 있는 람다의 `Array.modify` 등)는 바깥 구조체의 생성자 재사용을 깨뜨려 `{ s with … }`가 매번 재할당된다(29필드 `CrossMinSnapshot`) → 생성자 매치 갱신을 `@[noinline]` 함수로 둔다(13·16번과 같은 계열).

## 8. 배포 설계
- **CLI**: `elk layout [-f json|elkt] [-a <algorithm>] [-o out] [--pretty] [--sort-keys] [--trace-dir DIR] [--lenient] input`, `elk convert`, `elk algorithms|options|categories`, `elk --version`.
- **FFI**: `@[export elk_layout_json] (graph options : String) : String`(오류는 JSON `{"error": "..."}`), `elk_known_layout_algorithms/options/categories`, `elk_init`(모듈 initializer + `ensureInitialized`).
- **NAPI**: Node-API C 애드온(`plugins/org.eclipse.elk.napi/src/elk_napi.c`)이 `libelklean.a`(`elk_lean.h` C API, `scripts/build_ffi.sh`)를 링크, elk-rs와 같은 6개 플랫폼 패키지 구조(`scripts/build_napi.sh`).
- **GMP(LGPL v3) 배제**(`docs/gmp-licensing.md`, G1): 툴체인 `libleanrt.a`는 GMP를 정적으로 포함하므로 배포되는 네이티브 산출물(릴리스 CLI, C 라이브러리 번들, NAPI 애드온)은 Lean v4.35.0 소스의 런타임을 `LEAN_USE_GMP` 없이 다시 컴파일한 `libleanrt_nogmp.a`로 링크한다(`scripts/build_runtime_nogmp.sh`, `ELK_NO_GMP=1`; Init/Std는 `lean.h`에 GMP 의존 코드가 없어 재생성 불필요). 큰 수 차분 테스트·코퍼스·trace·`lake test`·npm 테스트가 GMP 빌드와 바이트 동일하고 성능 차이는 측정 오차 안(0.96~1.02). 개발용 `lake build` 산출물은 배포하지 않으므로 그대로 둔다. WASM은 처음부터 GMP 없음.
- **WASM**(`plugins/org.eclipse.elk.wasm`, `scripts/build_wasm.sh`): Lean 런타임 `src/runtime`(v4.35.0 소스, 단일 스레드, GMP 없음, libuv 호환 셈 `c/uv_compat`)과 Init/Std C(툴체인 `lean -c`로 재생성, 릴리스 오브젝트와 793/793 바이트 일치 검증) + 모든 Elk 모듈 C + `elk_lean.c`를 emscripten 6.0.13으로 컴파일. **`-sMEMORY64=2`**(64비트 C를 wasm32로 낮춤): Lean 생성 C는 32비트 타깃에서 `2^31` 이상 리터럴을 매번 힙 bignum으로 만들고 해제하지 않아(누수·느림) 순수 wasm32는 쓰지 않는다. 산출물: Node CJS(동기 초기화) + 브라우저 ESM, `.wasm` 18.9 MB(brotli 2.0 MB), mimalloc. 깊은 재귀(JSON 중첩·compound 계층·mrtree/radial 트리 순회)는 호출 스레드의 JS 엔진 스택(V8 기본 약 1 MB)에 걸리므로 npm 패키지의 `workerUrl` 모드는 `worker_threads` Worker를 `resourceLimits.stackSizeMb`(옵션 `workerStackSizeMb`, 기본 64 MB)로 만들고 그래프를 JSON 문자열로 전달한다(구조화 복제는 약 1,000단계, `JSON.stringify`는 약 3,000단계가 한계; W2 측정표는 `plugins/org.eclipse.elk.js/README.md` "Limits"). 브라우저 Web Worker의 스택은 JS에서 바꿀 수 없어 응답성 확보용이다. 메모리는 `-sMAXIMUM_MEMORY=4GB -sINITIAL_HEAP=16MB`(W3; 초기 41.9 MiB, 포트 8,000개 노드까지 네이티브와 동일 출력)이고, Lean의 `lean_internal_panic`(`exit(1)`)로 죽은 인스턴스는 명확한 Error를 던지며 npm 로더·Worker가 다음 호출에서 새 인스턴스로 바꾼다. `MEMORY64=2`는 emsdk 6.0.13에서 deprecated 경고(#27952)만 있고 제거 일정이 없으며 `MEMORY64=1`(진짜 wasm64)은 1.95배로 느려서 **유지**(emsdk 올릴 때 재확인, `plugins/org.eclipse.elk.wasm/README.md`).
- **npm**: elk-rs `plugins/org.eclipse.elk.js`의 로더(플랫폼 NAPI → 로컬 .node → WASM 폴백, Worker 모드)와 typings 구조를 그대로 이식.

## 9. 리스크와 대응

| 리스크 | 영향 | 대응 |
|---|---|---|
| WASM: Lean 런타임의 emscripten 빌드가 현재 CI에서 비활성(libuv/pthread 의존) | 브라우저 배포 지연 | **해결(W1)**: libuv 호환 셈 + `MEMORY64=2`로 빌드, realworld 550/550 일치, 네이티브 대비 1.5배. `MEMORY64=2` deprecated(W2 조사): 제거 일정 없음, 대안 `MEMORY64=1`은 1.95배로 느림 → emsdk 6.0.13 고정 유지, 제거가 잡히면 `-m64` + `wasm-opt --memory64-lowering` 자체 수행 검토 |
| Lean 컴파일 시간(대형 do-block 느린 elaboration) | 개발 속도 | 파일당 1 클래스 유지, 긴 함수 분할, `maxHeartbeats` 상향, 모듈 병렬 빌드 |
| in-place 규약 위반으로 O(n²) 복사 | 성능 | 코드리뷰 체크리스트, 벤치마크 회귀 게이트(5%) |
| 안정 정렬에서 비일관 비교자의 결과 차이(TimSort vs 병합) | parity 드리프트 | drift 발생 시 해당 비교자에 한해 TimSort 동작 재현 |
| HashMap 순회 순서 의존 | 비결정성 | 삽입 순서 구조 사용, elk-rs가 정렬한 지점은 동일하게 정렬 |
| Java 부동소수점(`float` 캐스팅, `Math.round`) 미세 차이 | parity 드리프트 | Java 헬퍼 1:1, trace 비교로 단계 특정 |
| `Nat` 뺄셈 절단, 배열 범위 밖 접근 시 panic 후 계속 진행 | 잘못된 결과 | 음수 가능 값은 `Int`, 테스트 시 `LEAN_ABORT_ON_PANIC=1` |
| 내부 속성 typed 필드 전환 누락 | 포팅 오류 | 대응표 문서 + 컴파일 타임 타입 검사가 누락을 드러냄 |
| Java 기준값 부재(JDK 없음) | 3자 검증 불가 | **해결**: JDK 21·Maven을 mise로 설치, Maven Central ELK 0.12.0으로 `scripts/run_java_baseline.sh` 기준값·trace 생성(2장) |
| ELK Java 결과의 컨텍스트 의존(identity hash 순서) | 모델 ~6%에서 Java 자체가 실행마다 다른 결과 | `--reverse`/`--shuffle`/단일 실행으로 변동 모델을 식별하고, elk-lean 결과가 Java 결과 집합에 속하는지로 판정 |

## 10. 코딩 규약 요약 (상세: `AGENTS.md`)
- 파일 1개 = Java 클래스 1개, 모듈 경로는 Java 패키지 경로를 CamelCase로 변환.
- `namespace Elk.<Plugin>...`; 공개 API에는 docstring, Java 원본 클래스명을 docstring 첫 줄에 기재.
- `partial def`는 종료 증명이 비자명한 루프에 한해 허용. `panic!`, `unsafe`, `sorry` 금지(`Dynamic`의 `TypeName`은 예외).
- `List` 대신 `Array`, `String.append` 대신 보간, 재귀 대신 `for`/`while`.
- 경고 0 유지(`set_option linter.* false` 금지).

## 11. 작업 할당과 진행 기록

### 11.1 에이전트 모델·노력 추정 (규칙: `AGENTS.md` "작업 할당 규칙")
작업 시작 시 항목별로 모델과 effort를 추정해 할당하고, 결과를 `HISTORY.md`의 작업 할당표에 기록한다. Phase별 초기 추정:

| Phase / 작업 | 대응 원본 | 모델 | effort | 비고 |
|---|---|---|---|---|
| 1. 기반 규약(ids, enum 매크로, 속성 시스템, 그래프 arena, 모나드, 정렬, Random) | `graph/*`, `core/util/mod.rs` | fable(주) | max | 규약 확정 작업, 직렬 |
| 1. `Elk.Core.Options` 열거형 전부 + `CoreOptions` + 메타데이터 등록 | `core/options/*` (2.9K줄) | sonnet | high | 기계적이나 양이 많음, 메타데이터 수치 검증 필수 |
| 1. `Elk.Core.Data` 레지스트리·resolver·validation | `core/data/*`, `core/validation/*` (1.9K줄) | opus | high | 전역 상태·조회 규칙 |
| 1. `Elk.Core.Math` 나머지(ElkMath, BezierSpline, CubicSpline) | `core/math/elk_math.rs` 등 (1.2K줄) | sonnet | medium | 수치 1:1 |
| 1. `Elk.Core.Util` 나머지(ElkUtil, ElkSpacings, adapters, progress monitor, IndividualSpacings) | `core/util/*` (4K줄) | opus | high | ElkGraph arena API에 밀접 |
| 1. 단위 테스트 이식(core/graph) | `core/tests`, `graph/tests` (6K줄) | sonnet | medium | 통과 기준 동일 |
| 2. JSON Value/파서/프린터 | (자체 설계) | fable(주) | high | 출력 포맷 규약 |
| 2. JSON importer/exporter/transferLayout | `graph.json/*` (7.3K줄) | opus | xhigh | 좌표 모드·섹션 처리 세밀 |
| 2. `RecursiveGraphLayoutEngine`, Fixed/Box/Random/Topdown provider | `core/*.rs`, `core/util/*_layout_provider.rs` (2.6K줄) | opus | high | |
| 2. CLI·parity 파이프라인 스크립트 | elk-rs `scripts/` | sonnet | medium | |
| 3. alg.common nodespacing | `alg.common/nodespacing/*` (6K줄) | opus | xhigh | 라벨/포트 배치 수치 민감 |
| 3. alg.common networksimplex, compaction, polyomino, spore, utils | 나머지 11K줄 | sonnet/opus | high | 모듈별 분할 |
| 4a. layered 그래프 모델·importer/exporter·드라이버·trace | `layered/graph/*`, `elk_layered.rs`, `trace_recorder.rs` (10K줄) | fable(주)+opus | xhigh | 내부 속성 typed 필드 대응표 작성 |
| 4b. P1 cycles, P2 layers | `p1cycles/*`, `p2layers/*` (6K줄) | sonnet | high | |
| 4c. intermediate 프로세서 ≈60개 | `intermediate/*` (30K줄) | opus ×4~6 (10개씩 분할) | high~xhigh | 프로세서 간 의존 순서 고려 |
| 4d. P3 crossing minimization | `p3order/*` (12K줄) | opus | xhigh | 순서 민감 |
| 4e. P4 node placement | `p4nodes/*` (8K줄) | opus | xhigh | BK/NS 수치 민감 |
| 4f. P5 edge routing, self loops, components, compound | `p5edges/*`, `loops/*`, `components/*`, `compound/*` (12K줄) | opus ×3 | xhigh | |
| 5. force/stress, mrtree, radial, rectpacking, spore, disco, topdownpacking, vertiflex | 각 플러그인 | sonnet(소형)/opus(mrtree·rectpacking) | medium~high | 플러그인 단위 병렬 |
| 6. elkt 파서 | `elkt_test_loader.rs` (3.3K줄), elk-live TS 파서 | sonnet | high | 명세 명확 |
| 7. 전수 parity·drift 분석·성능 | 전체 | fable(주)+opus | max | |
| 8. FFI/NAPI/WASM/npm | elk-rs `js/`, `napi/`, `wasm/` | opus | xhigh | 런타임 빌드 리스크 |

### 11.2 진행 기록
- 단계 완료 시 `HISTORY.md`에 범위/수치/이슈와 작업 할당표(추정 vs 실제)를 기록하고 `AGENTS.md`의 "현재 핵심 스냅샷"을 갱신한다.
- parity 수치는 항상 "모델 수 / 비교 수 / 일치 수 / 드리프트 / 스킵"으로 기록한다.
