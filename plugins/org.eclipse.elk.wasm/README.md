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

`js/load-wasm.js`는 npm 패키지(`plugins/org.eclipse.elk.js`)용 Node WASM 폴백 로더 제안본이다(elk-rs
`load-wasm.js`와 같은 인터페이스, 패키지의 `dist/wasm-node/`를 가리킨다).

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
  -sSTACK_SIZE=16MiB`. `--stack-first`로 선형 메모리 스택 넘침이 정적 데이터를 덮지 않고 트랩이 된다.
- **JS**: `js/elk_lean_api.js`(`--post-js`)가 C API(`plugins/org.eclipse.elk.ffi/include/elk_lean.h`)를 감싸
  `Module.createBackend()`를 제공한다(문자열은 TextEncoder/TextDecoder, 엔진 오류 시 wasm 스택 포인터 복원).

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

## 알려진 제한

- **깊은 재귀**: wasm 프레임은 JS 엔진의 네이티브 스택(Node·Chrome 기본 약 1 MB)을 쓴다. Node 메인
  스레드 기본값에서 mrtree 체인 깊이 약 500~1000, 중첩 JSON 깊이 약 2000~4000을 넘으면
  `RangeError: Maximum call stack size exceeded`가 난다(네이티브 CLI는 8 MB 스택으로 처리).
  `node --stack-size=7000`이면 체인 4000, Worker `resourceLimits.stackSizeMb: 64`이면 32000 이상 통과한다.
  오류 뒤에도 인스턴스는 계속 쓸 수 있지만 중단된 호출의 객체는 해제되지 않는다(실패 1회당 수 MB).
- 파일 시스템 API(Lean `IO.FS`)는 emscripten MEMFS 위에서만 동작한다(elk-lean API는 쓰지 않음).
