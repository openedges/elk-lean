# 빌드·런타임 수준 최적화 (16차 BLD, 2026-11-01)

코드 수준 라운드(합성 0.73배·코퍼스 0.92배, elk-rs 대비) 뒤에 처음으로 **빌드 수준**을 다뤘다. 결과 바이트
동일·순수 Lean 원칙은 그대로 두고, 컴파일러·링커 플래그, LTO, PGO, TLS 모델, Lean 런타임(mimalloc) 옵션,
WASM 링크 옵션을 재고 채택 여부를 정했다. Lean 알고리즘 소스는 한 줄도 바꾸지 않았다.

## 1. 요약

| 산출물 | 이전 | 채택 | 효과(이 기계, Apple M1) |
|---|---|---|---|
| 릴리스 CLI | `lake build` 객체 + no-GMP 런타임 재링크(`build_runtime_nogmp.sh --relink elk`) | **`scripts/build_release.sh`**: Lake가 만든 C를 Lake와 같은 플래그 + `-flto=thin` + `-fprofile-use`로 다시 컴파일, no-GMP 런타임도 ThinLTO 비트코드 + PGO, 툴체인 clang + ld64.lld ThinLTO 링크 | 합성 26개 기하평균 벽시계 **0.857배**·명령 수 **0.833배**(26개 시나리오 전부 1 미만), 코퍼스 1,447개 총합 **0.80배**·기하평균 **0.77배**·명령 수 0.78배, 학습에 쓰지 않은 무작위 세트(seed 5) 0.79~0.80배 |
| PGO 프로파일 | 없음 | **`scripts/build_pgo.sh`** → 메인 체크아웃 `.reference/pgo/elk-lean-<lean>-<os>-<arch>.profdata`(git 미포함, 재생성); force/stress 모듈(`Elk/Alg/Force/`)은 프로파일 없이 컴파일(`ELK_PGO_EXCLUDE`, §3) | 위 수치에 포함(ThinLTO 단독은 0.93배·코퍼스 0.86배) |
| NAPI 애드온 | `libelklean.a`(Apple `cc`) 링크 | **`scripts/build_napi.sh --release`**: 같은 릴리스 객체 + LTO 런타임을 툴체인 clang + ld64.lld로 링크 | realworld 큰 모델 40개 애드온 시간 **0.80~0.82배**(첫 통과 550개 총합 0.71배), 550/550 CLI와 바이트 동일, npm 67/68(1 skip) |
| `libelklean.a`(C 라이브러리 번들) | 일반 기계어 | 변경 없음(임의의 호스트 컴파일러로 링크할 수 있어야 하므로 비트코드를 넣지 않는다) | — |
| 개발용 `lake build` | `-O3 -DNDEBUG -fPIC` | **변경 없음**(`lakefile.lean`) | — |
| WASM | `-O3` 컴파일·링크 | **링크만 `-Oz`**(`tools/build.py`; LTO는 깨짐·closure는 실패, §6) | `.wasm` 21.4 → 20.1 MB(−6.1%, gzip −2.0%), 속도는 측정 잡음 안, realworld 550/550 |

결과 바이트 동일 게이트(§7)는 릴리스 CLI에서 전부 통과: Java 매니페스트 코퍼스 1,998개(레이아웃·오류 문구),
`--trace-dir` 단계 trace 196,407개 파일, 합성 26개 × compact/`--pretty --sort-keys`, 무작위 세트 s·v·w
seed 1~10 18,000개(레이아웃·결과 종류·예외 문구·스택 오버플로 14건까지) 모두 `elk_base`와 SHA-256 일치.

## 2. 측정 방법

- 기준 이진 `elk_base` = 이 브랜치 기준점(`aff7de7`)의 `LEAN_NUM_THREADS=3 lake build` 산출물(툴체인 `libleanrt.a`, GMP 포함).
- 실험 빌드는 Lake의 `.lake/build/ir/**.c`를 Lake와 **같은 명령**(툴체인 clang, `leanc --print-cflags` + `--sysroot`
  /`-nostdinc`/`-isystem <prefix>/include/clang` + `-O3 -DNDEBUG -fPIC -DLEAN_EXPORTING`)으로 다시 컴파일해 만들었다.
  추가 플래그가 없을 때 `__text`가 `elk_base`와 비트 단위로 같음을 먼저 확인했다(`otool -t` SHA-1 동일).
- 합성: 시나리오마다 별도 프로세스로 `elk bench --scenarios S`(약 300 ms 분량 반복 + 20% 워밍업)를 이진들 사이에
  번갈아 3라운드 실행, 벽시계는 CSV `avg_ms` 중앙값, 명령 수는 `/usr/bin/time -l`의 `instructions retired`
  (프로세스 전체 ÷ 반복 수) 중앙값. 비율은 `elk_base` 대비.
- 코퍼스: `elk bench --mode models`(elk-rs 코퍼스 1,447개, 3회 + 워밍업 1)를 이진별로 번갈아 4회(정·역순 2쌍),
  모델별 최솟값의 총합과 기하평균.
- 공유 기계(8코어, 다른 에이전트 동시 실행, load average 5~17)라 벽시계에는 ±3~5% 잡음이 있다. 명령 수는 부하에
  거의 영향을 받지 않으므로 판단은 두 값을 같이 봤다.

## 3. 시도한 구성 (합성 26개 기하평균, `elk_base` 대비)

| 구성 | 바이트 동일 | 벽시계 | 명령 수 | 코퍼스 총합 / 기하평균 | 링크 시간 | `elk` 크기 | 판정 |
|---|---|---|---|---|---|---|---|
| `b0` 같은 플래그로 재컴파일(검증용) | `__text` 동일 | — | — | — | 0.6 s | 25,880,256 | 드라이버 검증 |
| `-fno-stack-clash-protection` | `__text` 동일 | 1.00 | 1.00 | — | — | 25,880,256 | 효과 없음(arm64 Darwin에서 no-op) |
| `-fomit-frame-pointer` | (미측정) | 1.03(잡음) | 0.993 | — | — | 26,573,680 | 기각: 0.7%, 크기 +2.7%, `sample` 백트레이스 손상 |
| no-GMP 런타임 재링크(`ng`, 기존 릴리스 CLI) | 기존 검증 | 0.983 | 0.993 | 0.909 / 0.911 | 0.6 s | 25,752,608 | 이미 채택돼 있던 경로(기준점) |
| ThinLTO, Elk C만(툴체인 런타임) | 코퍼스·합성 동일 | 0.979 | 0.976 | — | 58 s | 24,604,736 | 런타임 포함판에 흡수 |
| full LTO, Elk C만 | (미측정) | 0.987 | 0.975 | — | 180 s | 24,293,504 | 기각: ThinLTO보다 느리고 링크 3배 |
| **ThinLTO, Elk C + no-GMP 런타임** | (최종판에서 검증) | **0.931~0.938** | **0.910** | 0.859 / 0.869 | 75 s | 28,552,992 | 채택(PGO와 함께) |
| full LTO, Elk C + 런타임 | (미측정) | 0.936 | 0.908 | — | 140 s | 27,785,120 | 기각: ThinLTO와 같고 링크 2배 |
| PGO만(LTO 없음, 런타임 포함) | (미측정) | 0.922 | 0.941 | — | 0.7 s | 27,094,784 | 비교용 |
| **ThinLTO + PGO**(실험 프로파일) | (최종판에서 검증) | **0.868** | **0.835** | **0.740 / 0.717** | 112 s | 30,441,504 | 채택 |
| 릴리스 1판(`build_release.sh`, `build_pgo.sh` 프로파일, 전 모듈 PGO) | **전부 동일**(§7과 같은 게이트) | 0.867~0.868 | 0.834 | 0.801 / 0.773 | 111 s | 30,459,168 | force/stress 회귀로 2판으로 대체 |
| **최종 릴리스**(1판 + `Elk/Alg/Force/`는 PGO 제외) | **전부 동일**(§7) | **0.857** | **0.833** | §7b | 3 s(ThinLTO 캐시) / 처음 111 s | 30,416,304 | **채택** |
| mimalloc 런타임 옵션(`PURGE_DELAY=-1`, `ARENA_EAGER_COMMIT=1`, `ALLOW_LARGE_OS_PAGES=1`, `PAGE_FULL_RETAIN=8`) | 출력 무관 | 0.995~0.998 | 1.009(래퍼 셸 비용) | — | — | — | 기각: 효과 없음 |

그룹별(ThinLTO+PGO 실험판, 벽시계/명령 수): layered 0.80/0.79, mrtree 0.85/0.80, radial 0.87/0.86,
rectpacking 0.81/0.79, routing 0.82/0.80, crossmin 0.85/0.77, hierarchy 0.80/0.78, **force/stress 1.02/0.96**
(`force_xlarge` 1.11/1.02, `stress_xlarge` 1.05/0.99, `force_large` 1.03/0.95). force/stress의 회귀는 PGO가
`FruchtermanReingoldModel.scanForcesU`(force_xlarge 표본의 98%)를 `layout`의 `repeatM` 루프에 인라인하면서
부동소수점 내부 루프의 코드가 나빠진 것이다(프로파일: `scanForcesU___redArg` 2,760 표본 → 인라인된
`WHILE@…FruchtermanReingoldModel_layout_spec__9` 2,858 표본). ThinLTO만 쓴 판은 force 0.97~1.00이다. Lean 소스를
바꾸지 않고 빌드에서 고치는 방법으로 `org.eclipse.elk.alg.force` 플러그인 모듈(`Elk/Alg/Force/`)만 프로파일 없이
컴파일하도록 했다(`build_release.sh`의 `ELK_PGO_EXCLUDE`, 기본값 `Elk/Alg/Force/`; ThinLTO는 그대로). 같은
시각 A/B(load 3): force/stress 그룹 벽시계 1판 1.020 → 최종 0.958(`force_xlarge` 1.095 → 0.982, `stress_xlarge`
1.047 → 0.982), 다른 그룹은 그대로(전체 0.868 → 0.857). 출력은 바이트 동일(§7).

## 4. 플래그별 분석

- **`-O3 -DNDEBUG`**: leanc 기본. `-ffp-contract=off`(leanc), 런타임의 `-ffp-contract=off`는 그대로 두었다. LTO
  백엔드는 IR에 `contract` 플래그나 `fmuladd`가 없으면 융합하지 않으므로(컴파일 단계의 `off`가 IR에 남는다) LTO·PGO
  모두 부동소수점 의미가 바뀌지 않는다 — 바이트 동일 게이트가 이를 확인했다.
- **`-fstack-clash-protection`**(leanc 기본): arm64 Darwin에서는 코드가 바뀌지 않는다(제거해도 `__text` 동일).
- **`-fomit-frame-pointer`**: 명령 수 −0.7%뿐이고 프레임 포인터 기반 `sample` 프로파일이 깨져 기각.
- **`-fno-semantic-interposition`, `-fno-plt`**: ELF 전용 의미라 Mach-O에서는 무의미하다. 생성 C는 이미
  `-fvisibility=hidden`(leanc)이고 링크는 `-Wl,-dead_strip`(Lake)이다. Linux CI 빌드에서 다시 볼 항목(§8).
- **`-mcpu`**: 툴체인 clang의 arm64-apple 기본 타깃 CPU가 `apple-m1`이고 이 기계도 M1이라 `-mcpu=native`는 같은
  코드를 낸다. 배포 산출물은 기본 타깃을 유지하고, 로컬 빌드용 `ELK_NATIVE_CPU=1`(`build_release.sh`)만 두었다.
- **TLS 모델**: Mach-O에는 initial-exec/local-exec가 없다. 모든 `__thread` 접근은 TLV 기술자의 썽크
  (`ldr x8,[x0]; blr x8` → `_tlv_get_addr`)를 거치며 `-ftls-model`은 무시된다(런타임은 이미 `local-exec`로
  컴파일돼 있는데도 `lean_alloc_small_object_core`가 썽크를 호출한다). 생성 C는 `lean.h`에 TLS 접근이 없어
  TLS 모델과 무관하고, 할당 경로(`lean_g_tls`: heartbeat + mimalloc theap 캐시)만 TLS를 쓴다. `sample` 측정:
  `layered_small`에서 `_tlv_get_addr` 자체 표본이 `elk_base` 124/2,544(4.9%), ThinLTO+런타임판 165(호출 지점이
  인라인으로 늘어 썽크 호출은 줄지 않는다). 이 비용을 없애려면 런타임 소스(`mimalloc.cpp`의 `lean_g_tls`)를
  Darwin에서 mimalloc처럼 `tpidrro_el0` 직접 슬롯으로 바꾸는 패치가 필요해 이번 범위(플래그)에서 제외했다(§8).
  Linux에서는 런타임이 `-fPIC -ftls-model=local-exec`(Lean 릴리스 `leanrt`와 같음)인데, local-exec TLS는 공유
  객체(NAPI 애드온 `.node`)에 링크할 수 없다 — Linux 애드온 빌드를 검증할 때 `initial-exec` 또는 기본 모델로
  바꿔야 할 가능성이 높다(미검증, §8).
- **LTO**: Elk C만 LTO하면 −2.4% 명령 수, 런타임까지 넣으면 −9%: 이득의 대부분은 `lean_alloc_small_object_core`
  (호출 지점 34,698 → 6,719), `mi_free`, `lean_dec_ref_cold`가 생성 코드와 런타임 안으로 인라인되는 데서 온다.
  ThinLTO와 full LTO는 같은 성능이고 full LTO는 링크가 2~3배 길어 ThinLTO를 택했다.
- **PGO**: §5.

## 5. PGO

- 툴체인(Lean v4.35.0의 clang 23.1, LLVM `ea7d852a`)에는 프로파일 런타임(`libclang_rt.profile`)이 없다. Xcode
  CLT(LLVM 21)의 런타임은 raw 프로파일 버전이 10이라 clang 23 계측(버전 11)을 거부한다
  (`Runtime and instrumentation version mismatch : expected 10, but get 11`), Homebrew `llvm@21`도 같다.
- 해결: `build_pgo.sh`가 툴체인 clang의 `--version`에서 LLVM 커밋을 읽어 `compiler-rt/lib/profile`만
  sparse fetch(`.lake/pgo-deps/llvm-project`, blob 필터·depth 1)하고 툴체인 clang으로 런타임을 빌드한다.
  `llvm-profdata`는 이미 고정 참조로 쓰는 emsdk(`.reference/emsdk/upstream/bin/llvm-profdata`, LLVM 24git)의 것이
  raw 버전 11을 읽고 clang 23이 받아들이는 인덱스를 쓴다(`LLVM_PROFDATA`로 바꿀 수 있다).
- 학습(약 1분): `elk bench` 합성 26개(3회 + 워밍업 1), ELK Java 코퍼스 매니페스트 1,998개 `elk batch`,
  무작위 세트 s1·v1·w1 각 200개 `elk layout --pretty --sort-keys`(프로세스별). 계측 이진은 Elk C와 런타임 모두
  계측(`-fprofile-generate`)한 ThinLTO 릴리스 빌드(`.lake/build/release-pgogen`).
- 재현성: 같은 계측 이진으로 학습을 다시 돌리면 간선 카운트 겹침 99.997%, 간접 호출 값 프로파일 81.9%,
  memop 99.86%(`llvm-profdata overlap`) — 값 프로파일은 ASLR 주소에 따라 달라져 프로파일 파일 바이트는 실행마다
  다르다. 결과 바이트에는 영향이 없다(PGO는 코드 배치·인라인만 바꾼다). 바이트 재현이 필요하면
  `-mllvm -disable-vp`가 있지만 간접 호출 승격(`lean_apply_*`)을 잃으므로 쓰지 않았다.
- 과적합 확인: 학습에 쓰지 않은 무작위 세트(seed 5)에서 `elk bench --mode models --input-dir`:
  s5(성공 109개) 총합 0.799·기하평균 0.789, w5(568개) 0.815·0.805(ThinLTO 단독은 0.95·0.93); 최종판은 s5
  0.792·0.786, w5 0.802·0.796 — 학습에 포함된 코퍼스(0.80배)와 같은 크기라 과적합은 보이지 않는다.
- 프로파일 위치: 툴체인별 이진 데이터라 git에 넣지 않고 다른 재현 가능한 참조 데이터처럼 **메인 체크아웃의
  `.reference/pgo/`**(worktree에서도 자동으로 찾음)에 둔다. 파일 옆 `.txt`에 생성 시각·elk-lean 커밋·툴체인·학습
  내용·SHA-256을 남긴다. Lean 소스가 바뀐 뒤의 오래된 프로파일도 빌드는 된다(바뀐 함수만 프로파일 없이
  컴파일, 관련 경고는 끈다). 릴리스 전에는 `sh scripts/build_pgo.sh`로 다시 만든다.

## 6. 런타임과 WASM

- **toolchain `libleanrt.a` vs 재빌드 `libleanrt_nogmp.a`**: 합성 0.983(명령 수 0.993), 코퍼스 0.909 — 재빌드판이
  같거나 약간 빠르다(`docs/gmp-licensing.md` 5장의 이전 측정 0.96~1.02와 같은 방향).
- **mimalloc 컴파일 옵션**: `MI_PADDING`은 `NDEBUG`·`MI_SECURE=0`에서 이미 0(`types.h`: `MI_DEBUG>=1` 또는
  `MI_SECURE>=3`일 때만 켜짐), `MI_STAT`도 0이라 바꿀 것이 없다. 실행 시 옵션(아레나 eager commit, purge 지연,
  large OS page, page retain)은 모두 ±0.5% 안이라 기본값(`MI_DEFAULT_*`)을 바꾸지 않았다.
- **`build_runtime_nogmp.sh`**: `RT_OUT`(출력 디렉터리), `RT_EXTRA_CXXFLAGS`(모든 런타임 객체에 추가),
  `RT_STAMP_EXTRA`(PGO 프로파일 해시 등 재빌드 스탬프), `AR`(LTO 비트코드는 툴체인 `llvm-ar`) 환경 변수를 추가했다.
  기본 동작·산출물은 같다. `__gmp` 검사 0건 유지.
- **WASM**(`plugins/org.eclipse.elk.wasm/tools/build.py`의 `--extra-cflags/--extra-ldflags`로 실험, 기본 산출물 불변):
  | 구성 | realworld 550 | WASM/네이티브 시간 | `.wasm` 크기(gzip -9) | 판정 |
  |---|---|---|---|---|
  | 기본(`-O3`) | 550/550 | 1.59배(같은 시각 측정; 유휴 시 약 1.4배) | 21,404,035 (4,020,701) | 유지 |
  | 링크만 `-Oz` | 550/550 | 1.56배 | 20,101,250 (3,941,809) | 보류: 속도 같음, 원본 −6.1%·gzip −2.0% |
  | `-flto` 컴파일·링크 | **10/550**(11번째 모델부터 `unreachable` 트랩, 인스턴스 사망) | — | 23,560,877 | 기각 |
  | `--closure 1` | 링크 실패(`__filename` 미선언, `js/elk_lean_api.js`) | — | — | 기각: JS 글루 67 KB의 축소뿐 |
  `-sASSERTIONS=0`은 `-O1` 이상에서 이미 기본값이다(`tools/link.py`). `MEMORY64=2`·`INITIAL_HEAP=16MB`·
  `MAXIMUM_MEMORY=4GB`는 W3 결정대로 두었다. WASM LTO의 트랩은 원인을 좁히지 않았다(MEMORY64 낮춤과 런타임
  C++ 인라인의 조합으로 추정, §8).
- **런타임 초기화**: CLI의 `main`(Lake 생성)은 모듈 초기화 → `lean_init_task_manager()`(작업자 스레드는 첫
  `Task` 때 만들어지므로 `LEAN_NUM_THREADS`는 비용이 없다), FFI의 `elk_lean_init`은 `lean_initialize_runtime_module`
  → 초기화 중 `lean_set_panic_messages(false)` → `true`로 Lake의 `main`과 같다. FFI는 task manager를 만들지
  않으므로 `Task.spawn`이 호출 스레드에서 동기 실행된다(`object.cpp` `if (!g_task_manager) return lean_task_pure(...)`)
  — 병렬 레이아웃(PAR)을 애드온/WASM에서 쓰려면 `elk_lean_init`에 task manager 초기화가 필요하다(PAR 이후:
  `elk_lean_init_threads`가 시작하고 애드온이 쓴다, WASM은 순차; `docs/parallel-layout.md` §5). 프로세스 시작
  비용(`elk --version`)은 명령 수 7,020만 → 릴리스판 5,910만(모듈 초기화가 대부분, 약 6~8 ms).

## 7. 최종 릴리스 산출물의 게이트

- 빌드: `lakefile.lean` 변경 없음 → `lake build` 경고 0·오류 0, `LEAN_NUM_THREADS=3 lake test` 17,189 통과·0 실패.
- 바이트 동일(`elk_base` 대비 SHA-256 매니페스트): Java 코퍼스 1,999개 파일(레이아웃 1,997 + 오류 1 + 매니페스트),
  trace 198,406개 파일(단계 trace 196,407 포함), 합성 104개(26 × compact/pretty·sorted × 출력/stderr), 무작위
  s·v·w seed 1~10 12,648개(레이아웃 12,618 + 결과표 30; ok 12,618·exception 5,368·overflow 14) — **전부 동일**.
- elk-rs: model parity(1e-6) 1447/1447, 바이트 일치 1060/1447(기존과 같은 목록), strict trace parity §7a.
- GMP: 릴리스 CLI `nm | grep -c __gmp` = 0, 릴리스 애드온 0, `ELK_NO_GMP=1 sh scripts/build_ffi.sh --check` 통과
  (smoke `__gmp` 0).
- NAPI: 릴리스 애드온으로 `node --test test/` 68개 중 67 통과·1 skip, `test/parity/run.mjs` realworld 550/550
  CLI(`elk_base`)와 바이트 동일; 기본 애드온(`ELK_NO_GMP=1`, `--skip-ffi`)도 550/550.
- WASM(`-Oz` 링크 채택판): realworld 550/550 바이트 동일(`elk_base`·최종 릴리스 CLI 둘 다와), npm 테스트의 WASM
  3모드 포함 67/68. WASM/네이티브 시간 비율은 `elk_base` 대비 1.54~1.69배, **최종 릴리스 CLI 대비 1.98배**
  (네이티브가 빨라진 만큼 벌어진다; WASM은 LTO·PGO를 쓸 수 없다, §6).
- 성능: §7b.

### 7a. elk-rs strict trace parity

릴리스 1판으로 `scripts/run_trace_parity.sh`(elk-models 1,447개, strict order, tol 0): **1447/1447** 전 단계 일치
(18분). 최종판은 1판과 force 모듈 객체만 다르고, Java 코퍼스 trace 196,407개가 `elk_base`와 바이트 동일하므로
같은 결과다. model parity(1e-6) 1447/1447과 바이트 1060/1447은 최종판으로도 다시 쟀다.

### 7b. 최종 A/B (load average 약 3, `elk_base` 대비 벽시계/명령 수)

| 시나리오 | base ms | 최종 ms | 벽시계 | 명령 수 | 시나리오 | base ms | 최종 ms | 벽시계 | 명령 수 |
|---|---|---|---|---|---|---|---|---|---|
| layered_small | 0.400 | 0.300 | 0.750 | 0.779 | mrtree_medium | 0.290 | 0.231 | 0.795 | 0.795 |
| layered_medium | 3.391 | 2.831 | 0.835 | 0.791 | mrtree_large | 1.190 | 0.997 | 0.838 | 0.796 |
| layered_large | 17.245 | 14.925 | 0.865 | 0.793 | mrtree_xlarge | 6.064 | 5.300 | 0.874 | 0.798 |
| layered_xlarge | 277.509 | 246.544 | 0.888 | 0.782 | radial_medium | 0.223 | 0.179 | 0.803 | 0.791 |
| force_medium | 2.783 | 2.639 | 0.948 | 0.946 | radial_large | 1.212 | 1.029 | 0.849 | 0.847 |
| force_large | 11.572 | 11.013 | 0.952 | 0.948 | radial_xlarge | 12.090 | 11.758 | 0.973 | 0.934 |
| force_xlarge | 125.169 | 122.971 | 0.982 | 0.983 | rectpacking_medium | 0.155 | 0.118 | 0.762 | 0.782 |
| stress_medium | 3.911 | 3.672 | 0.939 | 0.948 | rectpacking_large | 0.621 | 0.495 | 0.797 | 0.785 |
| stress_large | 15.976 | 15.109 | 0.946 | 0.948 | rectpacking_xlarge | 3.686 | 3.066 | 0.832 | 0.810 |
| stress_xlarge | 187.152 | 183.727 | 0.982 | 0.977 | routing_polyline | 3.031 | 2.494 | 0.823 | 0.801 |
| crossmin_layer_sweep | 3.379 | 2.841 | 0.841 | 0.791 | routing_orthogonal | 3.375 | 2.859 | 0.847 | 0.791 |
| crossmin_none | 2.020 | 1.645 | 0.814 | 0.750 | routing_splines | 3.557 | 3.012 | 0.847 | 0.816 |
| hierarchy_flat | 1.671 | 1.353 | 0.810 | 0.785 | hierarchy_nested | 0.840 | 0.645 | 0.767 | 0.781 |

기하평균 벽시계 **0.857**·명령 수 **0.833**; 그룹별 layered 0.833/0.786, force/stress 0.958/0.958, mrtree 0.835/0.796,
radial 0.872/0.855, rectpacking 0.796/0.792, routing 0.839/0.802, crossmin 0.828/0.770, hierarchy 0.788/0.783.
기존 릴리스 경로(no-GMP 재링크 `ng`)는 같은 시각 0.979/0.993이었다. elk-rs 대비 수치(현재 합성 0.73배)로
환산하면 약 0.63배다(같은 기계 rust_api는 다시 재지 않았다: `tests/perf/**`는 이 라운드에서 커밋하지 않는다).

코퍼스(1,447개, 4회 교차, 모델별 최솟값; load 6~9): 총합 3,444.6 → 2,765.1 ms **0.803**, 모델별 기하평균
**0.776**, 프로세스 명령 수 160.2 G → 125.4 G **0.783**(1판도 같은 시각대 0.801/0.773/0.783). 기존 릴리스
경로 `ng`는 0.978/0.971/0.991.

trace 모드(`elk batch --trace-dir`, Java 코퍼스 앞 300개, 2회): `elk_base` 104/165 s, 최종 1판 87/118 s(명령 수
1.454 T → 1.328 T, 0.913) — 학습에 trace 모드가 없어도 느려지지 않는다. 프로세스 시작(`elk --version`) 명령 수
7,020만 → 5,910만.

## 8. 남은 아이디어

- force/stress: 지금은 플러그인 전체를 PGO에서 뺐다(§3). 더 정밀하게는 `scanForcesU`만 인라인을 막으면
  (Lean 쪽 `@[noinline]`, 이번 범위 밖) force/stress에도 PGO 이득을 줄 수 있다. 다른 알고리즘에 새로 생긴
  hot 루프가 같은 식으로 나빠지는지 프로파일 재생성 때마다 합성 A/B로 확인해야 한다.
- Darwin TLS: 런타임 패치(`lean_g_tls`를 `tpidrro_el0` 슬롯으로)로 할당당 썽크 호출 제거, 예상 최대 약 5%.
- Init/Std까지 LTO: WASM 빌드처럼 툴체인 Init/Std C를 다시 만들어(`tools/stdlib_c.py`) 비트코드로 넣으면
  `Array`/`HashMap` 등 툴체인 함수도 인라인 대상이 된다(현재 `libInit.a`/`libStd.a`는 기계어).
- Linux(CI) 빌드: `-fno-plt`·`-fno-semantic-interposition`·`--gc-sections`/`--icf`, 애드온용 TLS 모델, ld.lld
  ThinLTO 캐시(`--thinlto-cache-dir`)를 검증해야 한다. `build_napi.sh --release`는 현재 macOS 전용이다.
- 배포 메모: Apple `cc`로 만든 현재 애드온의 최소 macOS는 빌드 호스트 버전(`minos 27.0`), Lake 이진은 `99.0`
  (`MACOSX_DEPLOYMENT_TARGET=99.0`)이다 — 배포 전에 `-mmacosx-version-min`을 정해야 한다(이번 변경과 무관한 기존 상태).
- WASM: `-Oz` 링크(크기 −6%)는 속도가 같다는 측정이 한 번뿐이라 보류했다. WASM LTO 트랩의 원인 분석.

## 9. 사용법

```sh
sh scripts/build_pgo.sh            # (선택) 프로파일 재생성: 약 7분(계측 ThinLTO 링크 4~5분 + 학습 1분)
sh scripts/build_release.sh --check  # .lake/build/release/bin/elk (ThinLTO + PGO, no GMP); 처음 약 4분
sh scripts/build_napi.sh --release   # 같은 객체로 애드온 (macOS); 약 1분
```

빌드 시간(3작업, 공유 기계): Lake 기본 C 컴파일 약 90~100 s(752개), 릴리스 컴파일 71~87 s(비트코드라 더 짧다)
+ ThinLTO 링크 111 s(캐시: `.lake/build/release/lto-cache`, 바뀐 모듈만 다시 코드 생성) + LTO 런타임 약 40 s.
크기: `elk` 25.9 MB → 30.5 MB(+18%, 인라인), 애드온 19.8 MB → 24.1 MB.
