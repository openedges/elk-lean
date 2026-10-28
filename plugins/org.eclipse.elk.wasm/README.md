# org.eclipse.elk.wasm

elk-lean의 WebAssembly 빌드(emscripten). elk-rs `plugins/org.eclipse.elk.wasm`(wasm-bindgen)과 같은 네 함수
`layout_json`, `known_layout_algorithms`, `known_layout_options`, `known_layout_categories`를 JavaScript에
노출한다. 결과는 JSON 문자열(elk-rs `serde_json::to_string`과 같은 compact·키 정렬)이고, 실패하면
`Error(message)`를 던진다. 하나의 `.wasm`이 Node.js와 브라우저(메인 스레드·Worker) 모두에서 동작한다.

## 빌드

```sh
sh scripts/build_wasm.sh                  # 증분 빌드, 산출물은 dist/
sh scripts/build_wasm.sh --verify-stdlib  # (macOS) 재생성한 Init/Std C를 릴리스 객체와 대조
```

필요 조건(메인 체크아웃의 `.reference/`, gitignore, worktree 공유):

| 항목 | 고정 버전 | 준비 |
|---|---|---|
| emsdk | `6.0.13` (emscripten `e13ee988`, clang 24.0.0git `83ee0779`, 번들 node 24.19.0·python 3.13.3) | `git clone https://github.com/emscripten-core/emsdk.git .reference/emsdk && cd .reference/emsdk && ./emsdk install 6.0.13 && ./emsdk activate 6.0.13` (emsdk 스크립트는 python ≥ 3.10 필요: `EMSDK_PYTHON=...`) |
| Lean 소스 | `v4.35.0` (`eb6cafb7`, 툴체인과 같은 커밋) | `git clone --depth 1 --branch v4.35.0 https://github.com/leanprover/lean4 .reference/lean4-v4.35.0` |

`EMSDK_DIR`, `LEAN_SRC_DIR`, `JOBS`로 경로·병렬도를 바꿀 수 있다. 스크립트는 먼저
`lake build elk ElkFfi:static`을 실행하고, 실행한 트리의 `.lake/build/ir`와 C shim
(`plugins/org.eclipse.elk.core/c/elk_core_ffi.c`, `plugins/org.eclipse.elk.ffi/c/elk_lean.c`)을 그대로 쓴다.
중간 산출물은 `build/`(증분; 지우면 클린 빌드, M1 8코어 `JOBS=6`에서 약 10분), 버전·플래그·크기는
`dist/BUILD_INFO.json`에 남는다.

## 산출물 (`dist/`, gitignore)

| 파일 | 용도 |
|---|---|
| `wasm-node/elk_lean.cjs` + `elk_lean.wasm` | Node.js CommonJS. `require` 시 동기 컴파일·초기화(`-sWASM_ASYNC_COMPILATION=0`) |
| `wasm/elk_lean.mjs` | 브라우저/Worker ES 모듈 래퍼: `default` = 비동기 `init(moduleArg)`, 네 함수는 named export |
| `wasm/elk_lean_core.mjs` + `elk_lean_core.wasm` | 위 래퍼가 쓰는 emscripten 모듈(`-sMODULARIZE -sEXPORT_ES6`, `.wasm`은 `new URL(..., import.meta.url)`로 찾음) |

```js
// Node.js
const backend = require('./dist/wasm-node/elk_lean.cjs').createBackend();
const out = backend.layout_json(JSON.stringify(graph), '{}');

// 브라우저 (번들러가 없으면 .wasm을 elk_lean_core.mjs 옆에 둔다; 아니면 init({ locateFile }) / init({ wasmBinary }))
import init, { layout_json } from './dist/wasm/elk_lean.mjs';
await init();
const out = layout_json(JSON.stringify(graph), '{}');
```

`js/load-wasm.js`는 이 플러그인의 `dist/wasm-node/`를 읽는 Node 로더로 `test/*`가 쓴다. npm 패키지
(`plugins/org.eclipse.elk.js`)는 같은 인터페이스(elk-rs `load-wasm.js`)의 자체 로더
`js/load-wasm.js`(Node, 네이티브 애드온이 없을 때의 폴백)·`js/load-wasm.browser.mjs`(브라우저·Web Worker)를
가지며, `scripts/build_wasm.sh`가 두 빌드를 패키지의 `dist/wasm-node/`·`dist/wasm/`에 복사한다.

## 구성

- **대상**: 64비트 C(`size_t`·포인터 64비트)를 Binaryen이 wasm32로 낮춘다(`-sMEMORY64=2`). 모든 wasm32
  엔진에서 돌고, Lean 생성 C가 가정하는 객체 표현(2^63 미만 스칼라 `Nat`, 64비트 `USize`)이 네이티브와
  같다. 순수 wasm32는 쓰지 않는다(아래 "32비트 문제").
- **Lean 런타임**: Lean 소스의 `src/runtime/*.cpp`(`RUNTIME_OBJS`에서 `uv/*` 제외)를 `-DLEAN_EMSCRIPTEN`으로
  컴파일한다. 단일 스레드(`LEAN_MULTI_THREAD`·`-pthread` 없음 → SharedArrayBuffer/COOP·COEP 불필요),
  GMP 없음(Lean 내장 `mpn` 큰 수), `LEAN_MIMALLOC` 없음(작은 객체도 `malloc`; 링크는 emscripten
  `-sMALLOC=mimalloc`, dlmalloc보다 약 13% 빠름), libuv 없음. Lean 4.35의 `io.cpp`가 `<uv.h>`를 무조건
  포함하므로 `c/uv_compat/uv.h` + `c/lean_wasm_compat.c`가 io.cpp가 쓰는 libuv 부분집합(오류 코드,
  동기 `uv_fs_*`, `uv_os_tmpdir`, `uv_strerror`)을 POSIX로 제공한다. Lean 소스 패치는 없다.
- **Init/Std C**: 릴리스는 Init/Std를 네이티브 아카이브로만 배포하므로 `tools/stdlib_c.py`가 툴체인 자신의
  `lean -c`로 툴체인 소스(`<prefix>/src/lean`, 태그 소스와 동일)에서 다시 만든다. 대상은 Elk C가 참조하는
  초기화 함수(`Init`, `Std.Data.HashMap`, `Std.Data.HashSet`)의 `lean --deps` 폐포(793 모듈, 약 4분).
  `tools/verify_stdlib_c.py`(`--verify-stdlib`)는 생성 C를 번들 clang·릴리스 플래그로 다시 컴파일해
  `libInit.a`/`libStd.a`의 객체와 비교한다: 793/793 바이트 일치(Mach-O 헤더 제외).
- **Elk C**: `Elk.Ffi`의 import 폐포(생성 C의 `// Imports:` 헤더 기준, 744 모듈)만 링크한다.
  Lean C는 네이티브와 같은 `-O3 -DNDEBUG -ffp-contract=off`로 컴파일한다.
- **링크**: `em++ -O3 --no-entry -Wl,--stack-first -sMALLOC=mimalloc -sALLOW_MEMORY_GROWTH=1
  -sMAXIMUM_MEMORY=4GB -sINITIAL_HEAP=16MB -sSTACK_SIZE=16MiB`. `--stack-first`로 선형 메모리 스택 넘침이
  정적 데이터를 덮지 않고 트랩이 된다. 최대 메모리는 wasm32 주소 공간 전체(4 GB, 아래 "메모리"),
  초기 메모리는 스택 + 정적 데이터 + 16 MiB = 42 MiB(emscripten은 `MAXIMUM_MEMORY`를 주면 기본
  `INITIAL_HEAP`을 버리고 스택보다 작은 16 MiB `INITIAL_MEMORY`로 링크에 실패하므로 명시한다).
- **JS**: `js/elk_lean_api.js`(`--post-js`)가 C API(`plugins/org.eclipse.elk.ffi/include/elk_lean.h`)를 감싸
  `Module.createBackend()`를 제공한다(문자열은 TextEncoder/TextDecoder, 엔진 오류 시 wasm 스택 포인터 복원,
  C `exit()` 시 `backend.failed`, 아래 "메모리").

## 검증

```sh
node plugins/org.eclipse.elk.wasm/test/parity.cjs --models <elk-models>/realworld [--report out.tsv]
node plugins/org.eclipse.elk.wasm/test/memory.cjs --models <elk-models>/realworld [--rounds 3]
node plugins/org.eclipse.elk.wasm/test/web_smoke.mjs        # 브라우저 빌드를 Node에서 (wasmBinary 전달)
node plugins/org.eclipse.elk.wasm/test/browser_smoke.cjs    # 브라우저 빌드를 headless Chrome에서 (HTTP)
```

- `parity.cjs`: 각 `.json` 모델을 WASM 백엔드로 배치하고 네이티브 `elk layout MODEL --sort-keys` 출력과
  바이트 단위로 비교한다(오류는 메시지 비교). 시간은 20개 단위로 네이티브 `elk bench --mode models`
  (프로세스 내 `layoutJson`)와 WASM 호출을 번갈아 재서(공유 머신 부하 보정) 비율을 낸다.
- `memory.cjs`: 같은 인스턴스에서 코퍼스를 여러 번 배치하고 선형 메모리가 첫 회 이후 자라지 않는지 본다.

## 32비트 문제 (wasm32를 쓰지 않는 이유)

Lean 4.35 컴파일러가 64비트 호스트에서 만드는 C는 32비트에서 깨끗하지 않다. RC 단계가 2^32 미만 `Nat`
리터럴을 tagged 스칼라로 취급하고(`LCNF/ToImpure.lean` `litValueImpureType`), 2^63 미만 리터럴은
해제하지 않는다(2^63 이상만 closed term으로 추출, `LCNF/ExtractClosed.lean`). 32비트에서 2^31 이상은 힙
큰 수라서 매 평가가 누수된다. 예: `Float.ofScientific`(Init)의 `lean_cstr_to_nat("9007199254740992")`,
Elk의 `lean_unsigned_to_nat(2147483648u)`. 순수 wasm32 빌드에서는 코퍼스 1회(550 모델)마다 선형
메모리가 약 380 MiB씩 늘었고(LSan으로 확인), 2^31 이상 정수 연산이 큰 수 경로를 타서 느렸다.
`-sMEMORY64=2`에서는 메모리가 일정하고(코퍼스 반복 시 42 MiB 유지) 더 빠르다.
같은 이유로 Lean C에는 `LEAN_EMSCRIPTEN`을 정의하지 않는다(lean.h에서 정적 객체 초기화
`LEAN_SCALAR_PTR_LITERAL`을 32비트 포인터용으로 바꾸는 것이 유일한 효과).

## `-sMEMORY64=2` 폐기 예고 (결정 노트, 2026-10-28)

emsdk 6.0.13에서 링크할 때 다음 경고가 난다(`tools/build.py`는 성공한 명령의 출력을 보이지 않으므로
빌드 로그에는 없다):

```
emcc: warning: MEMORY64=2 is deprecated (under consideration for removal (https://github.com/emscripten-core/emscripten/issues/27952)). Please open a bug if you have a continuing need for this setting [-Wdeprecated]
```

- 근거: `ChangeLog.md` 6.0.13 "`MEMORY64=2` was marked as deprecated. (#27952)", `tools/settings.py`
  `DEPRECATED_SETTINGS['MEMORY64=2']` = "under consideration for removal". `-sMEMORY64` 자체도 폐기 예고되어
  `-m64`/`--target=wasm64`(= `MEMORY64=1`)로 대체된다. 제거 시점은 정해지지 않았고 대체 플래그(낮춤 모드)도
  없다. 낮춤 자체는 Binaryen 패스(`--memory64-lowering --table64-lowering`)이며 emscripten도 내부에서
  계속 쓴다(`tools/link.py`의 embind TS 생성 경로).
- 측정(같은 객체 파일, 링크만 `-sMEMORY64=1`로 바꾼 진짜 wasm64, Node 24.22, realworld 550 모델):
  바이트 일치 550/550, 하지만 WASM/네이티브 총 시간 비율 **1.95배**(같은 시각 `MEMORY64=2` 1.52배; 공유
  머신이라 절대값은 기준선 1.34배보다 높다). wasm64는 가드 페이지 대신 명시적 경계 검사를 하므로 느리다.
  깊은 재귀 한계는 비슷하고(메인 스레드 체인 1,000 통과·2,000 `RangeError`), 2 GB 기본 최대 메모리도 같다.
  wasm64는 memory64 지원 엔진(Chrome 133+, Firefox 134+, Node 24)만 돌며, Safari 지원은 확인하지 못했다.
- 대안 검토: (1) `-m64`: 느리고 엔진 제약이 생긴다. (2) Lean C를 32비트 clean하게: Lean 컴파일러
  (`LCNF/ToImpure.lean`, `ExtractClosed.lean`)의 리터럴 처리 문제라 elk-lean 쪽에서 고칠 수 없다(위
  "32비트 문제"). (3) `-m64`로 링크한 뒤 직접 `wasm-opt --memory64-lowering --table64-lowering`: JS 글루가
  wasm64용(BigInt 포인터, `address: 'i64'` 가정)으로 생성되므로 글루 패치가 필요해 지금은 하지 않는다.
- **결정**: 지금은 유지한다(emsdk `6.0.13` 고정, 동작·성능 변화 없음). emsdk를 올릴 때마다 위 경고와
  #27952를 확인하고, 실제 제거가 예정되면 (3)을 시험하거나 그때 엔진 지원·성능을 다시 재서 `-m64`로
  옮긴다.

## 알려진 제한

- **깊은 재귀**: Lean 생성 C는 곳곳이 재귀다(`Elk.Json.Parser.parseValue` 중첩 단계당,
  `JsonImporter.transformNode`/`transformEdges` 계층 단계당, `EadesRadial.positionNodes` 트리 단계당,
  `MrTree.EdgeRouter.sortByFloat`의 특수화되지 않은 `Array.foldl`(`Id` 모나드 bind, 노드당 wasm 프레임 약 5개)).
  wasm 프레임은 JS 엔진의 네이티브 스택을 쓰므로 Node·Chrome 기본(약 1 MB, `--stack-size=984`)에서
  중첩 JSON 깊이 약 6,000(compound 계층 약 1,500), mrtree 체인 약 1,500~2,000, radial 체인 약 2,000을 넘으면
  `RangeError: Maximum call stack size exceeded`가 난다. 오류 뒤에도 인스턴스는 계속 쓸 수 있지만 중단된
  호출의 객체는 해제되지 않는다(실패 1회당 수 MB). 대책은 npm 패키지의 Worker 모드다(`new ELK({ workerUrl })`가
  `worker_threads` Worker를 `resourceLimits.stackSizeMb` = `workerStackSizeMb`, 기본 64로 만든다: JSON 깊이
  256,000, mrtree 체인 32,000 통과). 입력별 표와 네이티브 애드온(스택 초과 시 프로세스 종료)·CLI(Lean `main`이
  1 GB 스레드에서 돈다) 비교는 `plugins/org.eclipse.elk.js/README.md` "Limits".
- **브라우저**: JS에서 스택 크기를 정할 수 없다. Chrome 156의 Web Worker는 메인 스레드보다 한계가 낮다(JSON
  깊이 4,000·mrtree 체인 1,000에서 Worker만 실패). Web Worker는 응답성용이며 깊은 입력은 Node Worker 모드나
  네이티브가 필요하다.
- **`-sSTACK_SIZE`(선형 메모리 그림자 스택)는 한계 요인이 아니다**: `-sSTACK_SIZE=65536
  -sSTACK_OVERFLOW_CHECK=2` 실험 빌드도 2 GB Worker 스택에서 100만 단계 중첩 JSON을 통과했고(`parseValue`는
  그림자 스택을 쓰지 않음), mrtree 체인만 1,000~2,000 노드에서 `Aborted(stack overflow ...)`가 났다(단계당
  약 32~64 바이트). 16 MiB면 약 25만 단계 이상으로 256 MB Worker 스택이 닿는 깊이보다 깊다. 기본 빌드
  (`STACK_OVERFLOW_CHECK=0`, `--stack-first`)에서 그림자 스택이 넘치면 주소가 음수로 감겨 경계 밖 접근
  트랩(`RuntimeError: memory access out of bounds`)이 된다. `STACK_OVERFLOW_CHECK`/`ASSERTIONS`는 그림자
  스택 넘침을 진단 메시지로 바꿀 뿐 JS 엔진 스택의 `RangeError`와는 무관하므로 릴리스 빌드에서는 켜지 않는다.
- **메모리 최대 4 GB** (`-sMAXIMUM_MEMORY=4GB`, 2026-10-28): emscripten 기본값 2 GB에서는 포트 N개가 각각
  다른 노드로 이어진 layered 노드 하나(직교 라우팅이 세그먼트 의존성을 O(N²)개 만든다)가 N = 4,250에서
  `INTERNAL PANIC: out of memory`로 끝났다(4,000 통과; Node 직접·Worker 모드 같음, Chrome도 5,000 실패).
  4 GB에서는 8,000 통과(선형 메모리 4,085 MiB, 네이티브 CLI와 바이트 일치), 8,500·9,000·10,000 실패.
  5,000은 Node 직접·Worker·Chrome 메인 스레드·Web Worker 모두 네이티브와 같은 결과(최대 2,452 MiB).
  노드 수는 한계가 아니다: 평평한 DAG 100,000 노드·200,000 간선도 2 GB 빌드에서 1.2 GB·198초였다.
  - 비용 없음: `.wasm` 크기는 같고(19,337,024 바이트, 메모리 섹션 최댓값만 다름) 초기 메모리 42 MiB,
    인스턴스화 약 40~60 ms·초기화 약 105~135 ms도 같다. realworld 550/550 바이트 일치, WASM/네이티브 총 시간
    비율 1.39·1.46배(같은 시각 2 GB 빌드 1.43배, 공유 머신 잡음 범위). 코퍼스 반복 시 메모리 41.9 MiB 유지.
  - `MEMORY64=2` 특이점: Node 플래그는 필요 없다. 내보낸 함수의 포인터는 i64(BigInt → `Number`)라 2 GB 이상
    주소도 양수로 온다. 다만 emscripten은 `MEMORY64`일 때 `CAN_ADDRESS_2GB`를 켜지 않아(`tools/link.py`)
    시스템 라이브러리 JS(`fd_write`의 iovec, `clock_gettime`, `__cxa_throw` 등)가 힙 인덱스를 부호 있는
    `>>`로 계산한다. 이 빌드에서 그런 포인터는 스택(`--stack-first`, 하위 주소)에 있거나 `Number`로 바로
    쓰여 레이아웃 경로에서는 문제가 없었지만, 2 GB 위 힙 주소를 받는 시스템 호출이 생기면 깨질 수 있다
    (`js/elk_lean_api.js`는 `>>>`를 쓴다).
  - 브라우저: wasm32 메모리 65,536 페이지(4 GB)는 Chrome(V8)·Firefox가 지원하고 Chrome 156에서 확인했다.
    64비트 엔진은 wasm32 메모리마다 4 GB 이상 주소 공간을 미리 예약하므로 최댓값을 올려도 예약량은 같다.
    Safari는 확인하지 못했다.
  - **실패 후**: Lean 런타임의 `lean_internal_panic`은 C `exit(1)`을 부르고, emscripten은 이를
    `ExitStatus`(Error가 아님; Node에서는 `process.exitCode = 1`도 설정)로 던진다. 작은 입력은 그 뒤에도
    배치되지만 중단된 호출의 객체는 해제되지 않고 런타임 상태도 보장되지 않는다. 그래서
    `js/elk_lean_api.js`는 `process.exitCode`를 되돌리고 `backend.failed`에 메시지를 남긴 뒤
    `Error('elk-lean: the WASM instance terminated (Program terminated with exit(1)), most likely out of
    memory (N MiB in use); create a new instance')`를 던지며, 이후 모든 호출도 같은 오류를 던진다. npm
    패키지의 로더와 Worker는 실패한 인스턴스를 새 인스턴스로 바꾼다(`plugins/org.eclipse.elk.js/README.md`
    "Limits").
- 파일 시스템 API(Lean `IO.FS`)는 emscripten MEMFS 위에서만 동작한다(elk-lean API는 쓰지 않음).
