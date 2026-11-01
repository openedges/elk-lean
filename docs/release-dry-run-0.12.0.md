# 릴리스 체크리스트 예행 연습 — elk-lean 0.12.0

작성: R1(2026-10-28). 게시(`npm publish`), 태그 생성, push는 하지 않았다. 근거는 `AGENTS.md` 스냅샷,
`HISTORY.md`, 저장소 파일이며, 이 문서를 쓰는 동안 빌드·벤치마크는 다시 실행하지 않았다(다른 에이전트가 사용 중).
"재실행 필요"는 릴리스 담당자가 태그 직전에 같은 명령을 한 번 더 돌려야 한다는 뜻이다.

## 1. `TESTING.md` 3장 항목별 상태

| # | 항목 | 상태 | 근거 / 부족한 것 |
|---|---|---|---|
| 1 | `lake build`·`lake test` clean | 충족(14차 라운드 마감 병합본 `4a344e3`), 태그 직전 재실행 | `lake build` 경고 0, `lake test` 17168 통과 / 0 실패 / 1 skip(BK oracle replay, `ELK_BK_ORACLE_TRACES` 필요); 무작위 Java parity `sh scripts/run_random_java_parity.sh` v 5,711/5,761, Java 예외 문구 전부 일치 |
| 2a | ELK Java 결과 parity | 충족(스냅샷) | 1,997개 비교, 정확 일치 1,878, 나머지 119는 Java 컨텍스트 의존(패치 0001 적용 Java와 전부 일치), ticket 213은 Java NaN. `HISTORY.md` 160~161행 |
| 2b | Java 단계별 trace parity | 충족(스냅샷) | 1,817/1,997 전 단계 일치, 180은 Java 측 요인(170 비유한 포트 좌표, 7 self-loop 변 순서, 3 partition 포트 순서) |
| 2c | 컨텍스트 의존 모델 목록화 | 부분 충족 | 분석 결과는 `HISTORY.md`(172개 변동 모델, `scripts/java_outcomes.py`)에 있으나 모델 이름 목록이 릴리스 문서에는 없음. 목록 산출물 위치를 담당자가 확인 필요 |
| 2d | elk-rs parity / 바이트 일치 재생성 | 충족(스냅샷), 재실행 필요 | model parity 1447/1447, strict trace 1447/1447, 바이트 일치 1060/1447(보조 지표) |
| 3 | 메타데이터 parity | 근거 확인 필요 | `TESTING.md` 2.C가 `elk algorithms/options/categories` vs elk-rs `known_layout_*` 비교를 규정. 스냅샷 수치에 별도 항목이 없어 `HISTORY.md`의 해당 단계 기록을 릴리스 담당자가 가리켜야 함 |
| 4a | 성능 기준선 5% 이내 | 충족(14차 라운드 마감 병합본 `4a344e3`, 유휴 측정), 태그 직전 재실행 | `tests/perf/report.md`: 기하평균 lean/rust_api 0.73배, 회귀 게이트 pass; 코퍼스 `tests/perf/corpus/report.md` 총합 0.92배·기하평균 0.87배. 재실행: `sh scripts/run_perf_benchmark.sh 20 3 tests/perf`(머신 의존) |
| 4b | 메모리 검사 | 충족(`HISTORY.md` 523854c), 재실행 필요 | `elk bench --iterations 50` vs `500`의 최대 RSS 동일; 코퍼스 실행에 `PANIC` 없음 |
| 4c | FFI 스모크 | 충족(수동, macOS), 재실행 필요 | `sh scripts/build_ffi.sh --check` (CLI와 레이아웃 동일, 메타데이터·오류 경로) |
| 5a | `CHANGELOG.md` 갱신 | 충족(이번 작업) | `[0.12.0] - unreleased` 절 추가. 태그 시점에 날짜 기입 필요 |
| 5b | 태그 `vX.Y.Z` | 미수행(의도) | 첫 릴리스 규칙: `v0.12.0` (`VERSIONING.md`: 같은 버전의 빌드 전용 재발행은 `v0.12.0+lean.N`) |

## 2. 버전 일치 확인 (`VERSIONING.md`)

`lakefile.lean` `version := v!"0.12.0"`, `Elk.Api.version = "0.12.0"`, `plugins/org.eclipse.elk.js/package.json`
및 `npm/*/package.json` `0.12.0`, `optionalDependencies` 6개 모두 `0.12.0`. 일치한다.

## 3. npm 패키지 점검

### 3.1 `npm pack --dry-run` (plugins/org.eclipse.elk.js, 게시 아님)

```sh
cd plugins/org.eclipse.elk.js && npm pack --dry-run
```

결과(Node 24, `entryCount` 12, tarball 14,568 bytes, 풀면 46,417 bytes):

```
16398 LICENSE.md
 1956 NOTICE
 2992 README.md
 5447 js/elk-api.js
 5350 js/elk-worker.js
 1620 js/index.browser.js
 3005 js/index.js
 2560 js/load-native.js
  950 js/load-wasm.browser.mjs
 1284 js/load-wasm.js
 1274 package.json
 3581 typings/elk-api.d.ts
```

이상 징후:

1. **`dist/wasm/`, `dist/wasm-node/`가 포함되지 않았다.** `package.json` `files`에는 있으나 `dist/`는 gitignore
   대상(`scripts/build_wasm.sh`가 생성)이고 이 worktree에는 빌드 산출물이 없어 빠진 것이다. 릴리스 전에
   WASM 빌드 후 `npm pack --dry-run`을 다시 돌려 `dist/wasm/elk_lean.mjs`, `elk_lean_core.{mjs,wasm}`,
   `BUILD_INFO.json`, `dist/wasm-node/elk_lean.{cjs,wasm}`가 목록에 있는지 확인해야 한다(`.wasm` 약 18.9 MB:
   패키지가 수십 MB로 커진다).
2. 테스트(`test/`)와 `npm/` 템플릿은 `files` 화이트리스트와 `.npmignore`로 제외되어 있다(정상, 테스트 fixture 유입 없음).
3. 네이티브 `.node`는 메인 패키지에 들어가지 않는다(플랫폼 패키지 `npm/<triple>/`로 분리, 설계대로).
4. `"private": true`가 메인 패키지와 플랫폼 패키지 6개 모두에 있다. 이 값이 있으면 `npm publish`가 거부되므로
   릴리스 시점에 의도적으로 제거해야 한다(이번 작업에서는 건드리지 않음).
5. `README.md`가 낡았다: "WASM backend 미구현/stub", "only darwin-arm64 is built" 문구가 있으나 스냅샷상 WASM 로더는 연결 완료.
   게시 전 정리 필요(`plugins/org.eclipse.elk.js/`는 이번 라운드 다른 에이전트 소유라 수정하지 않음).

### 3.2 라이선스·NOTICE·typings

- `LICENSE.md`는 루트 `LICENSE`와 내용이 같다(EPL-2.0 전문). `package.json`의 `license`는 `EPL-2.0 OR GPL-3.0-or-later`이며,
  GPL 전문은 어느 곳에도 포함되어 있지 않다(`NOTICE`가 GPL URL을 안내; Java ELK도 보조 라이선스를 참조만 한다). 의도라면 문제 없음.
- 패키지 `NOTICE`는 루트 `NOTICE`와 **다른 파일**이다. 패키지판은 elkjs 유래 파일·typings 저작권과 Lean 런타임·**GMP(LGPL)**·libuv
  정적 링크 고지를 포함하고, 루트판에는 이 고지가 없다. 분기가 의도인지 확인 필요. 네이티브 애드온은 GMP를 정적 링크하므로
  LGPL 의무 검토가 남아 있다(라운드 3 G1). 플랫폼 패키지는 `build_napi.sh --copy-to-npm`이 루트 `LICENSE`와 패키지 `NOTICE`를 복사한다.
- typings: `types`/`exports["."].types` = `typings/elk-api.d.ts`, 파일 존재 및 pack 목록에 포함됨. `main`·`browser` 대상도 존재.

### 3.3 플랫폼 패키지

`npm/{darwin-arm64,darwin-x64,linux-x64-gnu,linux-x64-musl,linux-arm64-gnu,win32-x64-msvc}/package.json` 6개 존재.
`.node` 바이너리는 `build_napi.sh --copy-to-npm`이 채운다. 현재 빌드·검증된 것은 `darwin-arm64`뿐이다.

## 4. 릴리스 담당자가 실행할 명령 (순서)

게시·태그는 12, 13단계에서만 일어나며 이번 예행에서는 실행하지 않았다.

```sh
export PATH=$HOME/.elan/bin:$PATH
# 0. 깨끗한 체크아웃 + 서브모듈
git submodule update --init
git status --short                         # 비어 있어야 함
# 1. 빌드·테스트
lake build 2>&1 | tee /tmp/build.log; grep -cE '(warning|error):' /tmp/build.log   # 0
lake test                                   # failure 0
# 2. FFI + NAPI (macOS arm64; 다른 플랫폼은 CI 산출물) — 배포 산출물은 GMP 없는 런타임(docs/gmp-licensing.md)
sh scripts/build_runtime_nogmp.sh --check --relink elk     # 큰 수 차분 테스트 + 배포용 CLI .lake/build/runtime-nogmp/bin/elk
ELK_NO_GMP=1 sh scripts/build_ffi.sh --check
ELK_NO_GMP=1 sh scripts/build_napi.sh --copy-to-npm         # GMP가 들어간 애드온은 --copy-to-npm이 거부
for b in .lake/build/runtime-nogmp/bin/elk .lake/build/ffi/smoke plugins/org.eclipse.elk.js/dist/elk-lean.*.node; do nm "$b" | grep -c '__gmp'; done   # 전부 0
# 3. WASM
sh scripts/build_wasm.sh
# 4. Java 기준 parity (결과 + 단계별) — JDK/Maven은 mise
sh scripts/run_java_baseline.sh external/elk-models .reference/java-baseline/corpus
sh scripts/run_java_parity.sh .reference/java-baseline/corpus tests/tmp/java_parity
sh scripts/run_java_trace_parity.sh external/elk-models tests/tmp/java_trace
# 5. elk-rs 보조 parity (오라클 필요: sh scripts/build_oracle.sh)
sh scripts/run_model_parity.sh external/elk-models tests/model_parity && sh scripts/compare_bytes.sh tests/model_parity
sh scripts/run_trace_parity.sh external/elk-models tests/tmp/trace_corpus
# 6. 성능·메모리
sh scripts/run_perf_benchmark.sh 20 3 tests/perf
/usr/bin/time -l .lake/build/bin/elk bench --scenarios layered_medium,force_medium --iterations 50  --warmup 0 --output /dev/null
/usr/bin/time -l .lake/build/bin/elk bench --scenarios layered_medium,force_medium --iterations 500 --warmup 0 --output /dev/null
# 7. JS 패키지 테스트 + 애드온/CLI 바이트 parity
(cd plugins/org.eclipse.elk.js && node --test test/)
node plugins/org.eclipse.elk.js/test/parity/run.mjs --models external/elk-models --ext json --cli .lake/build/bin/elk
# 8. 패키지 내용 확인 (게시 아님)
(cd plugins/org.eclipse.elk.js && npm pack --dry-run)
for d in plugins/org.eclipse.elk.js/npm/*/; do (cd "$d" && npm pack --dry-run); done
# 9. 문서: HISTORY.md -> AGENTS.md 스냅샷 -> CHANGELOG.md(날짜) 갱신, 커밋
# 10. "private": true 제거(메인 + 플랫폼 6개 package.json), 커밋
# 11. 태그 이름 확인: v0.12.0 (재발행이면 v0.12.0+lean.N)
# --- 아래는 유지보수자가 직접, 승인 후에만 ---
# 12. git tag -a v0.12.0 -m "elk-lean 0.12.0" && git push origin main v0.12.0
# 13. 플랫폼 패키지 6개를 먼저, 메인 패키지를 마지막에: (cd <dir> && npm publish --access public)
```

## 5. 부족한 것 (우선순위순)

1. 비-macOS 빌드: Linux x64/arm64 glibc, musl, Windows 전부 미검증. `.gitlab-ci.yml`은 초안뿐이다. musl과 Windows는 현재 스크립트로 불가능
   (Lean 공식 릴리스에 musl 호스트 툴체인이 없고(확인하지 못함, 미검증 가정), `build_napi.sh`에 Windows 분기가 없으며
   Lean의 Windows 릴리스는 MinGW 계열이라 `msvc` 패키지명과 맞지 않음. 초안 주석 참조).
2. GMP(LGPL) 정적 링크: 검토 완료(G1, `docs/gmp-licensing.md`) — 배포되는 네이티브 산출물은 모두 `ELK_NO_GMP=1`(GMP 없는 Lean 런타임)로 만들고 `nm | grep __gmp` 0건을 게이트로 둔다(위 4장 2단계). CI(`.gitlab-ci.yml`)는 `ELK_NO_GMP: "1"`을 전역 변수로 두었으나 Linux에서의 런타임 빌드는 미검증.
3. WASM 깊은 재귀용 Worker 모드: 완료(W2, `workerStackSizeMb`, `npm test` 56/56). `dist/` 포함 pack 재검증은 남음.
4. npm 게시 준비: `private` 제거, 패키지 이름 선점 여부(`elk-lean`, `elk-lean-*`) 확인, README 정리, 레지스트리/권한 결정.
5. 컨텍스트 의존 119개 모델 목록을 릴리스 노트에 첨부할지 결정.
6. 메타데이터 parity 최신 수치를 스냅샷에 명시.
7. CI 러너 태그, Docker 이미지 레지스트리 결정(`.gitlab-ci.yml`의 `RUNNER_TAG_*`, `CI_IMAGE_*`).
