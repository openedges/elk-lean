# org.eclipse.elk.napi

elk-lean Node.js 네이티브 애드온. elk-rs `plugins/org.eclipse.elk.napi/src/lib.rs`의 이식으로,
`org.eclipse.elk.ffi`의 C API(`include/elk_lean.h`) 위에 Node-API C 인터페이스만으로 작성했다
(`src/elk_napi.c`, C++/node-addon-api 불필요).

## Exports

| 함수 | 의미 |
|---|---|
| `layout_json(graphJson, optionsJson)` | elk-rs `layout_api::layout_json`; 결과 JSON 문자열(키 정렬, compact). `optionsJson`은 생략/`""` 가능 |
| `known_layout_algorithms()` / `known_layout_options()` / `known_layout_categories()` | 메타데이터 JSON 배열 문자열 |
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
sh scripts/build_napi.sh --copy-to-npm   # npm/<triple>/에 애드온·LICENSE·NOTICE 복사(배포용)
```

- `NODE`(헤더를 찾을 node 바이너리) 또는 `NODE_INCLUDE_DIR`(`node_api.h` 위치)로 헤더를 지정한다.
- macOS: `cc -bundle -undefined dynamic_lookup`, `napi_register_module_v1`·`node_api_module_get_api_version_v1`만 export.
- Linux(미검증): `cc -shared -fPIC -Wl,-Bsymbolic -Wl,--exclude-libs,ALL -Wl,--version-script=...`.
  Lean 런타임에 정적 링크된 libuv가 node 실행 파일이 export하는 libuv 심볼에 바인딩되지 않도록 한다.
  Lean 툴체인의 정적 라이브러리(`libleanrt.a`, `libInit.a`, `libStd.a`, `libuv.a`, `libgmp.a`)가 PIC여야 한다.
- Windows: 미지원(node.lib/delay-load hook과 MSVC 또는 mingw Lean 툴체인 필요).
