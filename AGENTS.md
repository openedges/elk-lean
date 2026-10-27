# ELK Layout Kernel for Pure Lean 4 (elk-lean) — AGENTS.md

## 프로젝트 목표
- ELK Layout Kernel Java 0.12.0(및 elkjs 0.12.0, elk-rs 0.12.1)을 순수 Lean 4로 포팅한다.
- 기능, API(JSON 입출력·옵션 메타데이터), 알고리즘을 동일하게 이식하고 데이터 모델/파일 구조를 Java 플러그인 구조와 대응시킨다.
- 동일 입력에 동일 출력, layered 프로세서 단계별 중간 상태도 동일하게 유지한다(elk-rs oracle 기준).
- 빌드/테스트/parity를 항상 통과 상태로 유지하고, 성능·메모리 회귀를 방지한다.
- CLI, NAPI(Node.js), WASM(브라우저/Node), elkjs 호환 npm 패키지를 제공한다.
- 라이선스는 Java 버전과 동일하게 유지한다(EPL-2.0 OR GPL-3.0-or-later).

## 문서 운영 원칙
- `PLAN.md`: 포팅 계획(목표, 기준 버전, 아키텍처 결정, 단계, 검증, 리스크). 설계 변경 시 함께 갱신한다.
- `AGENTS.md`(이 문서): 작업 방식, 품질 게이트, 작업 할당 규칙, 현재 핵심 우선순위만 관리한다. 심볼릭 링크나 `CLAUDE.md` 사본을 두지 않는다.
- `HISTORY.md`: 단계별 구현/검증/수치 변화/이슈 분석 등 진행 이력을 모두 기록한다.
- `TESTING.md`: 검증 환경 준비, 항목 명세, 절차, 릴리즈 체크리스트.
- `VERSIONING.md`: 버전 관리, 서브모듈/oracle 고정 정책.
- 새 단계 완료 시 `HISTORY.md`를 먼저 갱신하고, 필요 시 `AGENTS.md`의 핵심 스냅샷만 동기화한다.
- 본문 설명은 한글로 작성한다(코드/명령어/식별자/경로는 원문 영문 유지).

## 자동 진행 규칙
- 사용자가 "계속 진행" 또는 "끝까지 진행"을 요청하면, `PLAN.md`의 현재 Phase 작업을 순서대로 진행한다.
- 막힘/불확실성만 짧게 질문하고, 그 외에는 추가 질문 없이 진행한다.
- 완전 구현이 어려운 항목은 최소 동작 + TODO(파일/테스트/명령 포함)를 남기고 다음 항목으로 진행한다.
- 테스트/빌드 실패 시 우선 수정하고 재시도한 뒤 계속 진행한다.
- 서브에이전트에 작업을 분배할 때는 "작업 할당 규칙"의 모델·effort 추정과 브리프 형식을 따른다.

## 작업 할당 규칙 (에이전트 모델·노력 추정)
- **작업 시작 시** 각 작업 항목을 아래 순서로 처리한다: (1) 범위·난이도·위험·의존성을 평가 → (2) 적절한 **에이전트 모델**과 **노력 수준(effort)** 을 추정해 기록 → (3) 서브에이전트에 할당(의존성 없는 항목은 병렬) → (4) 결과를 주 에이전트가 빌드·테스트·parity로 재검증한 뒤 수용.
- 추정 결과는 `HISTORY.md`의 해당 단계 "작업 할당표"(작업 / 대응 원본 파일 / 모델 / effort / 담당 / 결과)에 기록한다. 추정이 빗나가면(재작업, 시간 초과) 표에 실제값과 사유를 남기고 다음 추정에 반영한다.

| 모델 | 적합한 작업 | 기본 effort |
|---|---|---|
| `haiku` | 기계적 변환(상수/enum 목록, 파일 복사·이동, 포맷 변환), 단순 검색·집계, 스크립트 반복 실행, 문서 표 갱신 | low ~ medium |
| `sonnet` | 레퍼런스 코드와 규약이 확정된 **1:1 포팅**(한 작업당 Rust 500~3,000줄), 단위 테스트 이식, 메타데이터 등록 코드, 파서(elkt) 등 명세가 분명한 구현 | medium ~ high |
| `opus` | 복잡한 알고리즘 포팅(layered P3~P5, network simplex, spline/orthogonal routing, 노드 크기 계산), 설계 판단이 필요한 모듈, parity drift 원인 분석·디버깅, 코드리뷰 | high ~ xhigh |
| `fable`(주 에이전트) / `fork` | 아키텍처·규약 결정, 공통 기반 모듈, 서브에이전트 산출물 통합·최종 검증, 난해한 drift·성능 분석. `fork`는 현재 대화 컨텍스트(규약·결정 사항)를 공유해야 하는 작업에만 사용 | xhigh ~ max |

| effort | 기준 |
|---|---|
| `low` | 기계적 작업, 결과가 자동 검증되는 작업 |
| `medium` | 표준 1:1 포팅, 독립 모듈, 명확한 테스트 존재 |
| `high` | 여러 파일에 걸친 로직, 상태 모나드 설계가 필요한 프로세서, 테스트 보강 필요 |
| `xhigh` | 알고리즘 핵심부, 정밀 parity(단계별 trace 일치) 요구, 수치/순서 민감 코드 |
| `max` | 설계 결정, 원인 불명 drift, 성능 병목 분석 |

- **브리프 형식**(할당 시 반드시 포함): 목표와 범위, 대응 Rust/Java 파일 목록(경로), 따라야 할 규약 문서(`AGENTS.md`, `PLAN.md` 4장, 해당 플러그인 `PORTING.md`), 이미 확정된 설계·제외 사항, 빌드/테스트/parity 명령, 보고 형식.
- **보고 형식**(서브에이전트 → 주 에이전트): 변경 파일 목록, `lake build` 경고/오류 수, `lake test` 결과, parity 수치(모델 수/일치/드리프트), 남은 TODO와 사유, 규약 위반 가능성(`import Lean`, `panic!`, 불안정 정렬, 스냅샷 보유 갱신).
- 병렬화: 서로 의존하지 않는 플러그인/서브패키지는 동시에 할당한다. 규약(속성 시스템, 모나드, 그래프 모델)을 바꾸는 작업은 직렬로 주 에이전트가 수행한다.
- 하나의 할당은 한 번에 검증 가능한 크기(Rust 기준 ≤ 3,000줄, 프로세서 ≤ 10개)로 나눈다. 더 크면 분할한다.

## 단계별 상시 체크 (매 작업 단계)
1. 코드/문서 변경 직후 `lake build`를 실행한다.
2. 빌드 출력의 error/warning을 0건으로 맞춘 뒤 다음 단계로 진행한다(`set_option linter.* false`로 숨기지 않는다).
3. `lake test`를 실행한다.

## 품질 게이트 (단계 종료 시 필수)
1. 코드 변경 후 코드리뷰 실행
2. `lake build` (error/warning 0건)
3. `lake test` (failure 0건)
4. Parity 실행 및 통과률 확인 — 아래 두 가지 모두 필수 (상세: `TESTING.md`):
   - **Model parity**: 최종 레이아웃 출력 비교 (oracle elk-rs vs Lean layout JSON)
   - **Phase-step trace**: layered 프로세서별 중간 상태 비교
5. 성능 게이트: 기준선 대비 5% 이상 느려지면 원인 분석 후 진행
6. 문서 갱신: `AGENTS.md` 핵심 스냅샷의 parity 수치, `HISTORY.md` 변경 내역/수치
7. 커밋 (`<scope>: <summary>`)
8. 불가/예외 사항은 `HISTORY.md`에 사유와 대안을 기록

## Lean 코딩 규약 (핵심)
- 그래프 요소는 arena 배열 + typed id(`NodeId` 등)로만 참조한다. `IO.Ref` 상호 참조 객체 그래프 금지(순환 → 누수).
- 알고리즘 상태는 `StateRefT σ IO` 모나드로 다룬다. 상태 전체를 바인딩(`let g ← get`)한 채로 `modify`하지 않는다(배열 복사 발생). 요소 갱신은 `modifyNode id f` 류 헬퍼만 사용한다.
- `List` 대신 `Array`, 불안정 `Array.qsort` 대신 `stableSort`. 음수가 될 수 있는 정수는 `Int`.
- `panic!`/`unsafe`/`sorry` 금지, 예외는 `throw (IO.userError "<JavaExceptionClass>: msg")`.
- Java 클래스 1개 = Lean 파일 1개, 경로는 Java 패키지를 CamelCase 모듈로 변환. 공개 선언에는 docstring(원본 클래스/메서드명 포함).
- 열거형은 `elk_enum` 매크로로 선언한다(ordinal/Java 이름/`EnumSet` 코덱 자동 생성).
- 부동소수점 출력은 `Float.toShortest`(C shim), 파싱은 `strtod` 바인딩. Java 의미론이 다른 연산은 `Elk.Core.Util.Java` 헬퍼 사용.
- `import Lean` 금지(런타임 바이너리에 컴파일러가 링크됨). 매크로는 `Init` 수준 API만 사용한다.

## 현재 핵심 스냅샷 (2026-10-27, Phase 4·5 완료, 성능 최적화·Phase 8 진행)
- **버전**: elk-lean `0.12.0`(미공개), 레퍼런스 ELK/elkjs `0.12.0`, oracle elk-rs `0.12.1`(`../elk-rs` HEAD `eb586b6d`).
- **툴체인**: Lean `v4.35.0` / Lake 5.0 (`~/.elan/bin`, 셸 PATH 미수정: `export PATH=$HOME/.elan/bin:$PATH`). Node 24·Rust 1.97.1은 `../elk-rs`에서 `mise exec --`로 사용.
- **서브모듈 고정**: `external/elk` → `32331291`(v0.12.0), `external/elkjs` → `ff5771d7`(0.12.0), `external/elk-models` → `ac5af2ba`, `external/elk-live` → `cbf63a24`.
- **기준**: 결과(최종 출력·layered 단계별 상태)는 **ELK Java 0.12.0 미수정 아티팩트**(`scripts/run_java_baseline.sh`, JDK 21·Maven via mise, 기준값 `.reference/java-baseline/`), 성능은 **elk-rs**(`perf_benchmark`). elk-rs trace/model parity는 보조 검사로 유지(`.reference/elk-rs-target/release/`, `scripts/build_oracle.sh`). 스크립트는 worktree에서도 메인 체크아웃의 `.reference/`를 자동으로 찾는다.
- **완료**: Phase 0~6. layered 전 프로세서(P1~P5, intermediate 59개, components/compound/wrapping/self loops), Phase 5 전 알고리즘(force/stress, mrtree, radial, rectpacking, spore, disco, topdownpacking, vertiflex), `.elkt` 파서·`elk convert`, `elk bench`(elk-rs `perf_benchmark` rust_api와 동일 시나리오·CSV).
- **빌드 상태**: `lake build` 경고 0, `lake test` 12899 통과/0 실패(1 skip: BK oracle replay, `ELK_BK_ORACLE_TRACES` 필요).
- **Parity(ELK Java 기준)**: 코퍼스 1,998개 중 1,997개 비교(1건은 양쪽 동일 예외): 최종 출력 정확 일치(tol 0) 1,878, 나머지 119는 Java 자체가 실행 컨텍스트(identity hash 순서)에 따라 결과가 바뀌는 모델(패치 0001 적용 Java와는 전부 일치), ticket 213은 Java가 NaN을 내는 의도적 예외. 단계별 trace(tol 0, 엄격 순서): 1,817/1,997 전 단계 정확 일치, 나머지 180은 모두 Java 측 요인(170 비유한 중간 포트 좌표·7 self-loop 변 순서·3 partition 포트 순서, 상세 `HISTORY.md`).
- **Parity(elk-rs 보조)**: model parity(1e-6) 1447/1447, strict trace 1447/1447. 바이트 일치는 숫자 의미론을 Java에 맞춘 뒤(1e-6 스냅 없음, 정확 반올림 입력) 1060/1447이며 나머지 차이는 `-0.0`/스냅·≤4e-12 값 차이뿐 — elk-rs 바이트 일치는 더 이상 게이트가 아니다.
- **성능**: 합성 26개 시나리오 lean/rust_api 기하평균 **1.66배**(1차 6.41배; `tests/perf/report.md`, 5% 회귀 게이트 기준선 갱신). layered 1.4~2.8배, force/stress 2.1~2.4배, rectpacking 2.2~2.5배, mrtree 1.5배, radial 0.3~0.6배. 목표(elk-rs 수준)까지 남은 병목: P3 Forster·SweepCopy, P5 직교 라우팅, `NodeMicroLayout`, rectpacking 스캔, force 쌍 루프.
- **Phase 8**: C API(`elk_lean.h`)·NAPI 애드온·npm 패키지(JS 테스트 51/51, 애드온 vs CLI 1447/1448 바이트 일치)·WASM(realworld 550/550, 네이티브 대비 1.5배) 완료. 남은 일: npm에 WASM 로더 연결, Linux/Windows 빌드, 게시.
- **다음 우선순위**: Java 기준 단계별 전수 결과 정리 → 성능 재측정·기준선 갱신 → 남은 성능(P3 Forster, `NodeMicroLayout`, P5) → npm WASM 통합 → 릴리스 준비.
- **작업 위치 규칙**: 서브에이전트는 worktree에서만 작업한다. worktree가 사라지면 메인 체크아웃으로 옮기지 말고 보고하게 한다(공유 체크아웃에서의 동시 작업은 커밋 범위 혼동을 일으킨다).

## 기본 실행 명령
- 빌드/테스트: `lake build && lake test`
- CLI: `.lake/build/bin/elk --version`
- oracle 재빌드: `sh scripts/build_oracle.sh`
- oracle 단일 모델 실행: `sh scripts/oracle_layout.sh <input.json> <out.json> [trace_dir]`
- Java 기준값: `sh scripts/run_java_baseline.sh external/elk-models .reference/java-baseline/corpus [--trace true] [--reverse true]`
- Java 결과 parity: `sh scripts/run_java_parity.sh .reference/java-baseline/corpus tests/tmp/java_parity`; 단계별: `sh scripts/run_java_trace_parity.sh external/elk-models tests/tmp/java_trace`
- elk-rs model parity: `sh scripts/run_model_parity.sh external/elk-models tests/model_parity` + `sh scripts/compare_bytes.sh tests/model_parity`
- elk-rs phase-step trace parity: `sh scripts/run_trace_parity.sh external/elk-models tests/tmp/trace_corpus [--limit N --filter S]`(단일 모델: `scripts/run_phase_trace_parity.sh`)
- 성능: `sh scripts/run_perf_benchmark.sh [iterations] [warmup] [out_dir]`(oracle rust_api/rust_native vs `elk bench`, `tests/perf/report.md`; `baseline_lean_api.csv`가 있으면 5% 회귀 게이트)

## 외부 모듈 정책
- `external/*`는 상류 레퍼런스 서브모듈이며 수정하지 않는다.
- `../elk-rs`는 읽기 전용 레퍼런스다. 빌드 산출물은 `CARGO_TARGET_DIR=.reference/elk-rs-target`으로 격리한다.

## 진행 기록 위치
- 상세 진행 이력/완료 단계/드리프트 분석/실험 로그/TODO: `HISTORY.md`
