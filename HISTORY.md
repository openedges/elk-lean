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
| E. `CoreOptionsMeta` 등록 + 코어 알고리즘 메타데이터 + 지연 초기화 훅(`Elk.Core.Init`) + `LabelManagementOptions` | `core/options/core_options_meta.rs`(1,966줄), `data/mod.rs::register_core_algorithms`, `labels/*` | sonnet | high | 서브에이전트 E(worktree, 2026-10-27 시작) | 진행 중 |
| F1. `ElkUtil`/`ElkSpacings`/validation/resolver/replacer/`IndividualSpacings`/visitors(+`LayoutConfigurator` 검토) | `core/util/{elk_util,elk_spacings}.rs`, `core/validation/*`, `core/data/{layout_algorithm_resolver,deprecated_layout_option_replacer}.rs`, `core/layout_configurator.rs` (≈3.1K줄) | opus | high | 서브에이전트 F1(worktree, 2026-10-27 시작) | 진행 중 |
| F2. `ElkGraphAdapters`(adapter 추상화 설계: alg.common nodespacing과 공유) | `core/util/adapters/*` (1K줄) | fable(주) | high | 주 에이전트, Phase 3 착수 시 | 대기 |
| G. JSON importer/exporter/layout API/CLI/parity 스크립트 | `graph.json/*` (7.3K줄) | fable(주) | xhigh | 주 에이전트 | 완료(엔진 스텁): import/transfer/export 1:1, `Elk.Api.layoutJson`, `elk layout|batch|algorithms|options|categories`, `scripts/run_model_parity.sh`. 코퍼스 `.json` 100개 왕복 오류 0 |
| H. JSON import/export 테스트 이식 | `graph.json/tests/all/*.rs` (4.8K줄) | sonnet | medium | 서브에이전트 H(worktree) | 진행 중 |
| I. `.elkt` 파서(Phase 6 선행) | `alg.layered/tests/common/elkt_test_loader.rs` (3.3K줄), elk-live `src/elkt` | sonnet | high | 서브에이전트 I(worktree) | 진행 중 |

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
