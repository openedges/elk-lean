# org.eclipse.elk.napi

elk-lean Node.js 네이티브 애드온. elk-rs `plugins/org.eclipse.elk.napi/src/lib.rs`의 이식으로,
`org.eclipse.elk.ffi`의 C API(`include/elk_lean.h`) 위에 Node-API C 인터페이스만으로 작성했다
(`src/elk_napi.c`, C++/node-addon-api 불필요).

## Exports

| 함수 | 의미 |
|---|---|
| `layout_json(graphJson, optionsJson)` | elk-rs `layout_api::layout_json`; 결과 JSON 문자열(키 정렬, compact). `optionsJson`은 생략/`""` 가능 |
| `known_layout_algorithms()` / `known_layout_options()` / `known_layout_categories()` | 메타데이터 JSON 배열 문자열 |
| `convert_elkt(elkt, flags = 0)` | elk-lean 추가: ELK Text → ELK JSON 문자열(`elk_lean_convert_elkt_flags`). `flags`는 `elk_lean.h`의 `ELK_LEAN_CONVERT_*` 비트(1 `--defaults`, 2 `--pretty`, 4 `--sort-keys`), 0이면 `elk convert X.elkt`와 바이트 동일. 구문 오류는 `Error('ELK Text parse error: <행>:<열>: …')` |
| `version` | `"0.12.0"` |

엔진 오류는 JavaScript `Error(message)`로 던지고(`napi::Error::from_reason`과 동일), 문자열이 아닌
인자는 `TypeError`로 거부한다.

## Threading

- 모듈은 context-aware(`NAPI_MODULE_INIT`)이므로 `worker_threads`에서도 로드할 수 있다.
- `elk_lean_init()`은 프로세스당 한 번, 애드온을 처음 로드한 스레드에서 실행한다. 실패하면 `require`가 예외를 던진다.
- 다른 스레드는 첫 호출 전에 `elk_lean_thread_init()`으로 Lean 런타임에 등록하고(thread-local 플래그),
  Node 환경 종료 시(`napi_add_env_cleanup_hook`) `elk_lean_thread_finalize()`로 해제한다.
- 엔진이 프로세스 전역 레지스트리를 가지므로 모든 호출은 프로세스 전역 mutex로 직렬화된다
  (여러 worker의 호출은 병렬로 실행되지 않는다).
- Lean 런타임은 초기화 시 SIGSEGV/SIGBUS 핸들러(스택 오버플로 감지)를 설치한다. V8(WebAssembly trap
  처리)과의 충돌을 피하려고 애드온은 `elk_lean_init`/`elk_lean_thread_init` 전후로 기존 핸들러를 복원한다.

## Build

```sh
sh scripts/build_napi.sh            # build_ffi.sh 후 plugins/org.eclipse.elk.js/dist/elk-lean.<triple>.node
ELK_NO_GMP=1 sh scripts/build_napi.sh --copy-to-npm   # GMP 없는 런타임으로 빌드해 npm/<triple>/에 애드온·LICENSE·NOTICE 복사(배포용)
sh scripts/build_release.sh && sh scripts/build_napi.sh --release [--copy-to-npm]   # ThinLTO + PGO 애드온(macOS)
```

- `--release`(macOS): `scripts/build_release.sh`의 릴리스 객체(Elk C·`elk_lean.c`를 ThinLTO 비트코드로, PGO
  프로파일이 있으면 `-fprofile-use`)와 ThinLTO no-GMP 런타임을 툴체인 clang + ld64.lld로 링크한다
  (`docs/build-optimization.md`). realworld 큰 모델 40개에서 애드온 시간 0.82배, 550/550 CLI와 바이트 동일,
  npm 테스트 67/68(1 skip). `libelklean.a`(다른 호스트용 C 라이브러리)는 이 경로와 무관하게 일반 기계어로 남는다.

- 배포용 애드온은 `ELK_NO_GMP=1`로 빌드한다: Lean 런타임을 v4.35.0 소스에서 GMP 없이 다시 컴파일한
  `libleanrt_nogmp.a`(`scripts/build_runtime_nogmp.sh`)를 링크하므로 GMP(LGPL v3) 코드가 들어가지 않는다
  (근거·검증: `docs/gmp-licensing.md`). `--copy-to-npm`은 GMP 런타임으로 만든 애드온을 거부한다.
  기본 빌드(툴체인 `-lleanrt -lgmp`)는 로컬 개발용이다.

- `NODE`(헤더를 찾을 node 바이너리) 또는 `NODE_INCLUDE_DIR`(`node_api.h` 위치)로 헤더를 지정한다.
- macOS: `cc -bundle -undefined dynamic_lookup`, `napi_register_module_v1`·`node_api_module_get_api_version_v1`만 export.
- Linux(미검증): `cc -shared -fPIC -Wl,-Bsymbolic -Wl,--exclude-libs,ALL -Wl,--version-script=...`.
  Lean 런타임에 정적 링크된 libuv가 node 실행 파일이 export하는 libuv 심볼에 바인딩되지 않도록 한다.
  Lean 툴체인의 정적 라이브러리(`libInit.a`, `libStd.a`, `libuv.a`; 기본 빌드는 `libleanrt.a`, `libgmp.a`도)가
  PIC여야 한다(`libleanrt_nogmp.a`는 `-fPIC`로 컴파일).
- Windows: 미지원(node.lib/delay-load hook과 MSVC 또는 mingw Lean 툴체인 필요).
