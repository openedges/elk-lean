# elk-lean 진행 이력

## 2026-10-27 — Phase 0: 프로젝트 초기 설정

### 결정 사항
- 기준 버전을 ELK **0.12.0**으로 확정(초기에 0.11.0으로 착수했다가 사용자 정정). 0.11.0용으로 만들었던 elk-rs worktree(`v0.11.0+rs.6`)와 external 클론은 제거/교체했다.
- oracle은 `../elk-rs` HEAD(`eb586b6d`, 0.12.1)의 release 빌드로 한다. JDK/Maven이 없어 Java 기준값은 생성하지 못하므로 elk-rs 출력을 대리 기준값으로 사용한다(`PLAN.md` 2장).
- 아키텍처: arena + typed id + `StateRefT` 모나드. 근거 측정(20만 회 갱신): naive 구조체 갱신 6ms, 중첩 `Array.modify` 38ms, `set!` 2ms → in-place 확인. 스냅샷을 갱신 이후에 사용하지 않으면 복사가 발생하지 않음도 확인(`PLAN.md` 4.1 D1).
- Lean `Float.toString`은 소수 6자리 고정이라 출력에 부적합 → C shim(`elk_float_to_shortest`: serde_json/ryu 스타일 최단 표현, `elk_strtod`)을 정적 라이브러리로 링크. 검증 출력: `12.0 0.1 1e21 1.5e-7 1234.5 -0.0 1.2345678901234568e17`.
- `Float.round`는 C `round`(half away from zero)이므로 Java `Math.round`는 별도 헬퍼로 구현 예정.
- `instance : TypeName Foo := unsafe TypeName.mk Foo ``Foo` 패턴으로 `Dynamic` 사용 가능함을 확인(탈출구 용도).
- Lean 공식 릴리스에는 wasm32 자산이 없다. 런타임 CMake에 Emscripten 분기는 남아 있으나 CI 잡은 주석 처리 상태 → WASM은 Phase 8 초기에 PoC로 검증(`PLAN.md` 9장 리스크).
- `elk_enum` 매크로 프로토타입: `import Lean` 없이 `macro_rules`만으로 작성 시 `Lean.Parser.Command.ctor` 파서 카테고리 참조와 antiquotation 구성에서 오류 발생(Phase 1에서 재작성 예정; 대안은 `inductive` + `ElkEnum` 인스턴스를 수작업/스크립트 생성).

### 환경
- elan 설치(`--no-modify-path`), Lean v4.35.0/Lake 5.0. `~/.elan/bin`을 PATH에 추가해야 한다.
- `mise trust ../elk-rs/mise.toml` 후 `mise exec -- cargo build --release --workspace --bins`로 oracle 빌드 완료(`.reference/elk-rs-target/release/`).
- external 4개를 0.12.0 핀으로 shallow 클론 후 서브모듈로 등록(`git submodule add` 기존 디렉토리 채택). 용량: elk 47M, elk-models 64M, elkjs 11M, elk-live 1M.
- elk-models 구성: examples 45 elkt, tests 193 elkt, tickets 110 elkt, realworld 550 elkt + 550 elkg + 550 json.

### 산출물
- `lakefile.lean`: 17개 `lean_lib`(플러그인 1:1) + `elk` CLI + `elktest` 테스트 드라이버 + C shim 타깃. `lake build` 21 jobs 경고 0, `lake test` 통과.
- `PLAN.md`, `AGENTS.md`(처음에는 `.rules` + 심볼릭 링크였으나 사용자 요청으로 실제 파일 `AGENTS.md` 하나로 정리, `CLAUDE.md` 제거), `HISTORY.md`, `TESTING.md`, `VERSIONING.md`, `CHANGELOG.md`, `README.md`, `LICENSE`, `NOTICE`.
- `scripts/`: `build_oracle.sh`, `oracle_layout.sh`, elk-rs 비교 스크립트 복사(`compare_model_parity_layouts.py`, `compare_phase_traces.py`), `README.md`.

### 미해결/다음
- Phase 1 착수: `Elk.Graph`(Ids/Enum/Properties/Model/Util), `Elk.Core.Math`, `Elk.Core.Util`, `Elk.Core.Options`, `Elk.Core.Data`.
- (해결) `lake build ElkFfi` 단독 호출 시 "job computation" 오류: `globs := #[.andSubmodules root]`는 루트 모듈의 서브모듈 디렉토리(`Elk/Ffi/`)가 존재해야 한다. 모든 lib에 디렉토리와 `.gitkeep`을 추가해 17개 lib 단독 빌드를 모두 확인했다.
- oracle 스모크 실행 확인: `scripts/oracle_layout.sh tests/tmp/smoke.json …` → 정렬된 키, 정수 스냅(`f64_to_number`: 정수와 1e-6 이내면 정수 출력), trace 19단계 생성(`<trace_dir>/<model>/step_NNN_*.json`).

## 2026-10-27 — 작업 규칙 추가: 에이전트 모델·노력 추정 할당
- 사용자 요청으로 `AGENTS.md`에 "작업 할당 규칙"(작업 시작 시 모델·effort 추정 → 할당 → 재검증, 브리프/보고 형식, 분할 기준)을 추가하고 `PLAN.md` 11.1에 Phase별 초기 추정표를 기록했다.
- Phase 1 착수: 주 에이전트(fable, max)가 규약 모듈(Ids, Enum/EnumSet 매크로, Java 의미론 헬퍼, stableSort, Random, KVector/KVectorChain/Spacing/Rectangle)을 작성 중. 빌드 검증 후 옵션/데이터/수학/유틸 나머지를 할당표대로 분배한다.

## 2026-10-27 — Phase 1 (1차): 기반 규약 모듈 완료, 병렬 할당 시작

### 완료
- `Elk.Graph`: `Ids`(typed id, `ConnectableId`, `ElementId`), `Enum`(`ElkEnum` 클래스, `elk_enum` 매크로, `EnumSet` 비트셋), `Properties`(`PropKey`/`PropValue`/`PropCodec`/`Property`/`PropertyMap`), `Model`(ElkGraph arena + EMF 반대참조 유지 연산), `Util`(`ElkGraphUtil` 순수 함수), `Monad`(`ElkM := StateRefT ElkGraph IO`).
- `Elk.Core`: `Exceptions`(Java 예외 클래스명 규약), `Util.Java`(Float/Int/String 의미론, Rust 문법 실수 파싱), `Util.Sort`(안정 병합 정렬), `Util.Random`(java.util.Random 1:1; Python 재구현으로 seed 42의 nextInt/nextDouble/nextLong/nextFloat 교차 검증), `Math.{KVector,KVectorChain,Spacing(ElkPadding/ElkMargin),ElkRectangle}`.
- 테스트 프레임워크 `Tests.Framework`(`lake test`), 기반 테스트 126개 통과. `PORTING.md`(Rust/Java→Lean 규약) 작성.
- 결정: enum 느슨 파싱은 elk-rs `parse_enum_value`(숫자=ordinal, 영숫자만 남겨 대문자 비교)와 동일. `Spacing` 프록시 파싱은 elk-rs `parse_spacing_value`(key=value만)와 동일. `RESOLVED_ALGORITHM`은 알고리즘 id 문자열, `LABEL_MANAGER`는 `Dynamic`으로 표현.
- Lean 4.35 특이점 기록: `String.trimAscii`/`dropEnd`는 `String.Slice` 반환, `section`은 예약어, 구조체 필드명이 네임스페이스 안에서 전역 함수를 가린다(`hash`).

### Phase 1 작업 할당표 (추정 → 결과)
| 작업 | 대응 원본 | 모델 | effort | 담당 | 결과 |
|---|---|---|---|---|---|
| 규약 모듈 + 테스트 프레임워크 + `PORTING.md` | `graph/*`, `core/util/mod.rs`, `core/math/{kvector,kvector_chain,spacing,elk_padding,elk_margin,elk_rectangle}.rs` | fable(주) | max | 주 에이전트 | 완료(126 테스트) |
| A. Options 열거형 전부 + `CoreOptions` 상수 + `TopdownSizeApproximator` | `core/options/*.rs` (`core_options_meta.rs` 제외, ≈1.3K줄) | sonnet | high | 서브에이전트 A(worktree) | 완료: 열거형 20개(생성자 수 Java 일치), `CoreOptions` 94개 상수, 테스트 ≈120, 경고 0. 편차: `SizeConstraint.minimumSizeSet`/`PortLabelPlacement.insideSet·outsideSet`(이름 충돌), `PortAlignment.«end»`, `TopdownSizeApproximator.getSize`의 lookahead/layoutNextLevel은 엔진 필요로 TODO |
| B. Math 나머지 + 테스트 | `core/math/{elk_math,bezier_spline,cubic_spline_interpolator,ispline_interpolator}.rs`, `core/tests/all/{elk_math,bezier_spline,cubic_spline_interpolator,kvector,kvector_chain}_test.rs` (≈1.4K+1K줄) | sonnet | medium | 서브에이전트 B(worktree) | 완료: 테스트 ≈200 추가, 경고 0. 편차: 팩토리얼/이항은 `Except`, `findRoots`/`bezier`는 값 반환, `maxl/minl` i32 초기값 등 Rust 특이점 유지 |
| C. Util 보조 + graph/property 테스트 이식 | `core/util/{progress_monitor,elk_trace,exclusive_bounds,abstract_random_list_accessor}.rs`, `graph/util/graph_identifier_generator.rs`, `graph/tests/*`, `core/tests/all/{basic_progress_monitor,property,util_misc}_test.rs` (≈1.2K+1K줄) | sonnet | medium | 서브에이전트 C(worktree) | 완료: 테스트 ≈90 추가, 경고 0. 편차: `ProgressMonitor.basic` 기본 maxHierarchyLevels=-1(Java/Rust 기본), 작업량 전파는 Java 방식(Rust는 전파 안 함), `subMonitors`는 항상 빈 배열, `GraphIdentifierGenerator` 접미사는 고정 seed LCG(Rust는 시계). 미이식: `util_misc_test`(DefaultFactory/Maybe/Triple/WrappedException 미존재) |
| D. `Elk.Core.Data` 레지스트리 | `core/data/{mod,layout_option_data,layout_algorithm_data,layout_category_data,i_layout_meta_data*}.rs` | fable(주) | high | 주 에이전트 | 완료: `LayoutOptionData`/`LayoutAlgorithmData`/`LayoutCategoryData`/`Registry`/`LayoutMetaDataService`(전역 `IO.Ref`, 지연 초기화 훅, 등록 순서 보존, suffix 캐시). resolver/replacer는 F로 이관 |
| E. `CoreOptionsMeta` 등록 + 코어 알고리즘 메타데이터 + 지연 초기화 훅(`Elk.Core.Init`) + `LabelManagementOptions` | `core/options/core_options_meta.rs`(1,966줄), `data/mod.rs::register_core_algorithms`, `labels/*` | sonnet | high | 서브에이전트 E(worktree) | 완료(`555ea22`): 94 옵션/7 카테고리/10 의존성 + `registerCoreAlgorithms`(fixed/random/box/layered placeholder), `Elk.Core.Init` 지연 초기화 훅. 편차: `IndividualSpacings` 파서는 `CoreOptionsMeta`에서 TODO로 두고 F1의 `IndividualSpacings.parse` 사용 |
| F1. `ElkUtil`/`ElkSpacings`/validation/resolver/replacer/`IndividualSpacings`/visitors(+`LayoutConfigurator` 검토) | `core/util/{elk_util,elk_spacings}.rs`, `core/validation/*`, `core/data/{layout_algorithm_resolver,deprecated_layout_option_replacer}.rs`, `core/layout_configurator.rs` (≈3.1K줄) | opus | high | 서브에이전트 F1(worktree) | 완료(`0474979`, 948 테스트): `ElkUtil`(순수 함수+`ElkM` 변형), `GraphValidator`/`LayoutOptionValidator`, 리졸버/대체기, `IndividualSpacings`, `GraphElementVisitor`. 편차: `LayoutOptionValidator`의 OBJECT 타입 검사는 Java보다 느슨(`elk.resolvedAlgorithm`은 주 에이전트가 예외 처리) |
| F2. `ElkGraphAdapters`(adapter 추상화 설계: alg.common nodespacing과 공유) | `core/util/adapters/*` (1K줄) | fable(주) | high | 주 에이전트, Phase 3 착수 시 | 대기 |
| G. JSON importer/exporter/layout API/CLI/parity 스크립트 | `graph.json/*` (7.3K줄) | fable(주) | xhigh | 주 에이전트 | 완료(엔진 스텁): import/transfer/export 1:1, `Elk.Api.layoutJson`, `elk layout|batch|algorithms|options|categories`, `scripts/run_model_parity.sh`. 코퍼스 `.json` 100개 왕복 오류 0 |
| H. JSON import/export 테스트 이식 | `graph.json/tests/all/*.rs` (4.8K줄) | sonnet | medium | 서브에이전트 H(worktree) | 완료(`33d06b4`): 비-layered 테스트 전부 이식(graph/edges/sections/id/layoutOptions/individualSpacings/export/transfer/metadata cache/layout API), 동작 차이 없음. layered 의존 테스트(edge_coords, root_external_ports, edgeless 4건)는 Phase 4 이후 복원 TODO |
| I. `.elkt` 파서(Phase 6 선행) | `alg.layered/tests/common/elkt_test_loader.rs` (3.3K줄), elk-live `src/elkt` | sonnet | high | 서브에이전트 I(worktree) | 완료(`f3c485c`): Rust 테스트 로더(라인 기반 방언) 대신 `ElkGraph.xtext` 문법을 구현(`Elk.Text.{Lexer,Parser,Loader}`, `parseElkt`/`loadAst`/`applyDefaults`). 코퍼스 898/898 파싱, Ptolemy `.elkt` 550개가 `.json` 쌍과 구조 일치. 미구현: Xtext validator 검사, 직렬화기. 추정 초과(≈16분, sonnet/high → 실제 opus급 난도) |

### Phase 1 (2차) — 병합 결과
- A/B/C worktree 병합(`939786e`, `e5d62fa`, `3748155`) 후 전체 `lake build` 경고 0. `lake test` 통합 결과는 아래 커밋 메시지의 수치 참조.
- 서브에이전트 공통 지적: `lake build ElkTests`가 실패(테스트 lib 루트 `tests/lean/Tests.lean` 부재) → 루트 파일 추가로 해결. 브리프의 빌드 명령도 `lake build && lake test`로 통일.
- 주 에이전트 추가 작업: `Elk.Json.{Value,Printer,Parser}`(삽입 순서 보존, 정수/실수 구분, serde_json 호환 compact/pretty, elk-rs 호환 lenient 모드) + 테스트.

### Phase 2 (1차) — JSON 계층·API·CLI·parity 파이프라인 (2026-10-27)
- `Elk.Json.{ImporterState,Importer,TransferLayout,Exporter}`: elk-rs `JsonImporter`/`JsonExporter` 1:1 포팅. `ImportM := StateRefT ImporterState ElkM`, JSON 경로는 `Array Seg`. 전역 옵션 병합(`GlobalOptions.effectiveOptions`)은 elk-rs와 같이 정렬된 키 순서로 방문한다. transfer의 elk-rs 전용 보정(inside self-loop/passthrough 노드 폭 24→4, 수직 passthrough 높이, East/South 포트 이동, FixedOrder 높이 보정)은 그대로 옮겼다. **TODO(근본 원인)**: Java 기준값 확보 시 이 보정이 왜 필요한지(elk-rs 내부 상태와 Java의 차이) 재검토.
- `Elk.Api.layoutJson`: 파싱 → `GlobalOptions.parse` → import → 엔진 → `materialize` → transfer → 직렬화. 오류는 `catchLayout`으로 Java 예외 클래스명 규약. 엔진은 F1 완료 전까지 placeholder(`RecursiveGraphLayoutEngine.layout := pure ()`).
- CLI `elk layout|batch|algorithms|options|categories`. `batch`는 elk-rs parity manifest 형식을 소비/생성한다.
- `scripts/run_model_parity.sh`: 코퍼스 `.json` → manifest → oracle 러너 → `elk batch` → 병합 → `compare_model_parity_layouts.py`. 100개 시험: oracle 100/100, lean 100/100(오류 0), 비교 total=100/compared=100/matches=0(스텁 엔진)/drift=100/skipped=0. 소요 1.3초.
- 메타데이터: `elk options` 95개(E 등록분), `elk algorithms` 4개(fixed/random/box/layered placeholder).

### Phase 2 (2차) — RecursiveGraphLayoutEngine + 코어 프로바이더 (2026-10-27, `0d95cc7`)
- `Elk.Core.RecursiveGraphLayoutEngine`: elk-rs `recursive_graph_layout_engine.rs` 1:1. 대체기 → 리졸버/옵션 검증/그래프 검증 visitor → `layoutRecursively`(NO_LAYOUT, inside self loop 수집·후처리, `INHERIT` 계층 처리, INCLUDE_CHILDREN 큐, top-down 레이아웃 `applyTopdownLayout`, `executeAlgorithm`은 `LayoutProvider.create`). 등록되지 않은 알고리즘은 `UnsupportedConfigurationException: Layout algorithm '<id>' is not available in this build.`
- 프로바이더: `Elk.Core.Util.{FixedLayoutProvider,RandomLayoutProvider,BoxLayoutProvider}`. Box의 그룹 트리(`Rc<RefCell<Group>>`)는 `StateT (Array Group) ElkM` arena로 대체. Random은 elk-rs 특이점(target을 sources[0]에서 취함, 포트 중심에 parent x 2회 가산)을 그대로 유지. `Elk.Core.Providers`가 `builtin_initialize`로 등록. `LayoutProvider.predictedGraphSize` 필드 추가(top-down 전용 프로바이더용).
- 수정: `LayoutOptionValidator.checkProperty`에서 `elk.resolvedAlgorithm`(Java는 `LayoutAlgorithmData` 인스턴스 저장)을 OBJECT 타입 검사에서 제외. CLI `-o`는 oracle 러너(`fs::write`)처럼 끝 개행 없이 기록.
- 검증: fixed/random/box(SIMPLE·GROUP_DEC·GROUP_INC·GROUP_MIXED × expandNodes, 중첩 box/fixed, interactive, 최소 크기, 포트/셀프루프/계층 간선, ORTHOGONAL junction points, top-down ROOT/HIERARCHICAL + COUNT_CHILDREN 근사) 17개 모델이 oracle과 **바이트 단위 일치**. `tests/fixtures/core/<name>.json` + `<name>.expected.json`으로 보관(회귀 테스트는 작업 J).
- 테스트: 1261 통과/0 실패. H의 layout API 테스트 중 layered 의존 부분은 `elk.algorithm: box`로 전환(TODO(phase4) 표기).
- 모델 parity(60개 샘플): oracle 60/60 ok, lean 60/60 `UnsupportedConfigurationException(layered)` → compared 0. 코퍼스 550개 모델은 전부 layered(기본값)라 Phase 4 전까지 match 0.

### Phase 3 착수 — alg.common 병렬 할당 (2026-10-27)
- 사전 준비: `Elk/Alg/Common/{Utils,Geometry,NetworkSimplex,Compaction,Polyomino,Spore,NodeSpacing}.lean` 집계 모듈과 `Tests/AlgCommon/*.lean` 자리를 미리 등록해 worktree 병합 충돌을 예방. `PORTING.md` §14(알고리즘 내부 그래프: arena+id, origin 타입 매개변수, 전략 클로저, 순회 순서 재현) 추가.
- 어댑터(`ElkGraphAdapters`)와 `core/alg`(AlgorithmAssembler)는 규약을 정하는 작업이라 주 에이전트가 직렬로 수행하고, nodespacing은 그 뒤에 할당한다.

#### Phase 3 작업 할당표
| 작업 | 대응 원본 | 모델 | effort | 담당 | 결과 |
|---|---|---|---|---|---|
| K1. networksimplex | `alg.common/networksimplex/*.rs`(1.65K줄) + `tests/all/network_simplex_test.rs` | opus | xhigh | 서브에이전트 K1(worktree) | 완료(`merge K1`): 인라인 5 + `network_simplex_deltas` 이식, elk-rs 크레이트와 265개 그래프(노드 순서/레이어/엣지 리스트 해시) 일치. 편차: `NGraph.nodeList`(순서 관찰 가능) 추가, `NEdge.other`는 `IllegalArgumentException`. 성능: 700노드 176ms vs Rust 54ms(≈3.3배) |
| K2. compaction(oned/options/scanline) + polyomino | `alg.common/compaction/**`, `polyomino/**`(2.6K줄) + `one_dimensional_compactor_test.rs`, `two_bit_grid_test.rs` | opus | high | 서브에이전트 K2(worktree) | 완료(`merge K2`, ≈2.6K줄 Rust 전부, 1934 테스트): `one_dimensional_compactor_test` 17/17(256 방향 조합 포함), `two_bit_grid_test` 3/3, polyomino 기대값은 elk-rs 크레이트 실행값. 편차: `CompactM := StateRefT CompactorState IO`(클로저 자기참조 회피), 빌더는 값 기반 `IO` 체인, grid 경계는 `Except`. **메모**: `PolyominoCompactor` 정렬이 Java(내림차순)와 elk-rs(오름차순)가 다름 — oracle(elk-rs) 기준 유지, disco 포팅 시 재확인 |
| K3. geometry(Point/TEdge/TTriangle/Tree/BowyerWatson/NaiveMinST/RectilinearConvexHull) + overlaps + spore + utils | 해당 `*.rs`(≈1.9K줄) + `rectilinear_convex_hull_test.rs` | opus | high | 서브에이전트 K3(worktree) | 완료(`merge K3`, ≈1.5K줄 Lean, 1612 테스트): elk-rs 크레이트로 교차 검증(삼각분할 엣지 집합, DFS 압축 좌표, 스캔라인 쌍 일치). `SVGImage`는 no-op 스텁. **parity 위험**: elk-rs spore는 `HashSet<TEdge>`(무작위 해시) 순회 순서에 의존해 실행마다 결과가 달라질 수 있음 → spore 모델은 oracle 2회 실행으로 비결정성 판정 필요(Phase 5 메모) |
| F2. `GraphAdapters` 레코드 + `ElkGraphAdapters`; `Elk.Core.Alg`(assembler/processor configuration) | `core/util/adapters/*`, `core/alg/*`(1.6K줄) | fable(주) | high | 주 에이전트 | 완료(`0bf1391`): 클로저 레코드 `GraphAdapters m G N P L E`(raw `PropValue` 접근 + typed 헬퍼, 어댑터별 volatile id), `LayoutProcessor/LayoutPhase/LayoutProcessorConfiguration/AlgorithmAssembler`(IO.Ref 핸들, 캐시, ElkTrace 트레이스) |
| L. core alg/adapters 테스트 이식 | `core/tests/all/{algorithm_assembler,layout_processor_configuration,elk_graph_adapters}_test.rs` + `alg_test_util.rs`(0.6K줄) | sonnet | medium | 서브에이전트 L(worktree) | 완료(`20bcd64`): 25/25 이식 + 빌드 순서·PortComparator 추가 검사, 차이 없음 |
| N1. nodespacing cellsystem + NodeContext/PortContext/NodeLabelLocation + NodeLabelAndSizeUtilities | `nodespacing/cellsystem/mod.rs`, `internal/*.rs`, `internal/algorithm/node_label_and_size_utilities.rs`(2.8K줄) | opus | xhigh | 서브에이전트 N1(worktree) | 완료(`merge N1`, ≈130 검사): 공유 `CellArena`(CellId)로 Java 참조 의미 재현, `applyLabelLayout`은 위치 반환, `NodeContext` 어댑터 레코드 제네릭. 메모: Rust `process_with_options`는 `set_node_padding` 결과를 버림 → N3는 `setNodePadding` 호출 금지; `PortContext.portRatioOrPosition`은 Rust가 설정하지 않음(N2b 주의) |
| N2a. nodespacing 셀/라벨/노드 크기 알고리즘(PortContextCreator, NodeLabelCellCreator, InsidePortLabelCellCreator, CellSystemConfigurator, LabelPlacer, NodeSizeCalculator) | `internal/algorithm/*`(1.3K줄) | opus | xhigh | 서브에이전트 N2a(worktree) | 진행 중 |
| N2b. nodespacing 포트 배치(PortPlacementCalculator, Horizontal/VerticalPortPlacementSizeCalculator, PortLabelPlacementCalculator) | `internal/algorithm/*`(1.9K줄) | opus | xhigh | 서브에이전트 N2b(worktree) | 진행 중 |
| N3. 계산기(NodeLabelAndSizeCalculator, NodeDimensionCalculation, NodeMarginCalculator, NodeMicroLayout) + `nodespacing_test.rs` 등 | `node_*_calculat*.rs`(4.6K줄), `tests/all/*`(4.3K줄) | opus | xhigh | N2a/N2b 이후 | 대기 |

### Phase 4 착수 — layered 기반 (2026-10-27)
- 설계(`PORTING.md` §15): 단일 arena `LGraphArena` + typed id, `LayeredM := StateRefT LGraphArena IO`, 공개 옵션은 `props : PropertyMap`, `InternalProperties`는 요소별 `internal` typed 필드, `PROCESSORS`는 상태 밖, elk-rs `LArena/ArenaSync`(CSR 사본)는 포팅하지 않고 순회 순서만 재현, trace recorder 스키마 동일.
- 서브패키지 집계 모듈/테스트 자리(`Elk/Alg/Layered/{Options,Graph}.lean`, `Tests/Layered/*.lean`)를 미리 등록.

#### Phase 4 작업 할당표
| 작업 | 대응 원본 | 모델 | effort | 담당 | 결과 |
|---|---|---|---|---|---|
| M-opts. layered 옵션 열거형 + `LayeredOptions` + `LayeredMetaDataProvider` + `LayeredSpacings` | `layered/options/*.rs`(≈4.4K줄, 기계적; 이름 불일치를 피하려 단일 담당) | opus | high | 서브에이전트 M-opts(worktree) | 완료(`merge M-opts`, 131 검사): 열거형 33개, `LayeredOptions` 130 상수(89 고유 + 40 core 별칭 + ALGORITHM_ID; 브리프의 297은 과대 추정), 옵션 89개 등록/옵션 지원 153개(Rust 스크립트 생성값 그대로). id는 elk-rs의 `org.eclipse.elk.alg.layered.*`(Java id는 legacy id) |
| M0. 그래프 모델(ids/arena/LayeredM/LNode·LPort·LEdge·LLabel·Layer·LGraph), `InternalProperties` typed 필드, `Spacings`, `LGraphUtil`, `Tarjan`, `TraceRecorder`, `LayeredPhases`/`IntermediateProcessorStrategy`(레지스트리), `GraphConfigurator` | `layered/graph/*.rs`(arena 제외 ≈3.3K줄), `options/{internal_properties,spacings}.rs`, `trace_recorder.rs`, `graph_configurator.rs` | fable(주) | max | 주 에이전트 | 완료(`1a4d278`~): 프로세서/페이즈는 레지스트리에 등록되며 미이식 항목은 `UnsupportedOperationException`으로 보고 → 프로세서 단위 점진 parity 가능. 메타데이터는 `LayoutMetaDataService.addInitHook`으로 등록(옵션 184개) |
| M2. `ElkGraphLayoutTransferrer` | `graph/transform/elk_graph_layout_transferrer.rs`(1.3K줄) | opus | xhigh | 서브에이전트 M2(worktree) | 진행 중 |
| M3a. `ElkLayered`/`LayeredLayoutProvider` | `elk_layered.rs`, `layered_layout_provider.rs`(1.1K줄) | fable(주) | xhigh | M3b 이후 | 대기 |
| M3b. components + compound | `components/*`, `compound/*`(4.4K줄) | opus | xhigh | 서브에이전트 M3b(worktree) | 진행 중 |
| M1. `ElkGraphImporter`/`ElkGraphTransformer`/`LGraphAdapters` | (위 참조; `NodeLabelAndSizeCalculator`에 의존) | opus | xhigh | N3 이후 | 대기 |
| P1. cycle breakers 9종 + `GroupModelOrderCalculator` | `p1cycles/*`(2K줄) | opus | high | 서브에이전트 P1(worktree) | 진행 중 |
| P2. layerers 9종(NetworkSimplexLayerer 포함) | `p2layers/*`(2.5K줄) | opus | xhigh | 서브에이전트 P2(worktree) | 진행 중 |
| P3~P5, intermediate | `p3order`(10.6K, 3분할: counting/holder, sweep+heuristics, port distributors/forster), `p4nodes`(5.3K, 2분할), `p5edges`(6.4K, 3분할), `intermediate`(28K, ≈10분할) | opus | xhigh | P1/P2 병합 후 순차 병렬 | 대기 |


#### Phase 2 (2차) 작업 할당표
| 작업 | 대응 원본 | 모델 | effort | 담당 | 결과 |
|---|---|---|---|---|---|
| 엔진 + fixed/random/box 프로바이더 + 등록 | `core/recursive_graph_layout_engine.rs`, `core/util/{fixed,random,box}_layout_provider.rs` (≈1.7K줄) | fable(주) | xhigh | 주 에이전트 | 완료: oracle 바이트 일치 17/17 |
| J. 엔진/프로바이더/util 테스트 이식 + fixture 회귀 스위트 | `core/tests/all/{recursive_graph_layout_engine(_integration),fixed_layout_provider,issue_457,issue_489,elk_util,layout_algorithm_resolver,deprecated_layout_option_replacer,individual_spacings,util_misc,property,layout_option_parse}_test.rs` (≈1.5K줄) | sonnet | high | 서브에이전트 J(worktree) | 완료(`merge J`): 엔진 4/4, 통합 5/8(TestController 3건 제외; INCLUDE_CHILDREN은 COMPOUND 기능을 가진 테스트 알고리즘 `test.engine.compound`로 대체, TODO(phase4)), fixed 1/1, issue 457/489, option parse 4/4, fixture 스위트 `core.engine.fixtures`(16/17 바이트 일치, `box.json`은 layered 대기 SKIP). `util_misc`/`property` 일부는 API 부재로 제외 |
| CLI `elk convert` + `.elkt` 입력(`layout`) | elk-rs 없음(Java `ElkModelParityExportTest`가 EMF로 변환) | fable(주) | low | 주 에이전트 | 완료: `elk convert [-o] [--pretty] [--sort-keys] [--defaults] IN.elkt`, `layout`이 `.elkt`를 자동 변환. ticket 425 모델(box 강제)이 oracle과 바이트 일치 |

