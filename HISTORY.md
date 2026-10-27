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
- `PLAN.md`, `.rules`(`AGENTS.md`/`CLAUDE.md` 링크), `HISTORY.md`, `TESTING.md`, `VERSIONING.md`, `CHANGELOG.md`, `README.md`, `LICENSE`, `NOTICE`.
- `scripts/`: `build_oracle.sh`, `oracle_layout.sh`, elk-rs 비교 스크립트 복사(`compare_model_parity_layouts.py`, `compare_phase_traces.py`), `README.md`.

### 미해결/다음
- Phase 1 착수: `Elk.Graph`(Ids/Enum/Properties/Model/Util), `Elk.Core.Math`, `Elk.Core.Util`, `Elk.Core.Options`, `Elk.Core.Data`.
- (해결) `lake build ElkFfi` 단독 호출 시 "job computation" 오류: `globs := #[.andSubmodules root]`는 루트 모듈의 서브모듈 디렉토리(`Elk/Ffi/`)가 존재해야 한다. 모든 lib에 디렉토리와 `.gitkeep`을 추가해 17개 lib 단독 빌드를 모두 확인했다.
- oracle 스모크 실행 확인: `scripts/oracle_layout.sh tests/tmp/smoke.json …` → 정렬된 키, 정수 스냅(`f64_to_number`: 정수와 1e-6 이내면 정수 출력), trace 19단계 생성(`<trace_dir>/<model>/step_NNN_*.json`).
