# GMP(LGPL v3) 정적 링크 검토와 GMP 없는 네이티브 Lean 런타임

> 이 문서는 배포 산출물에 무엇이 링크되는지와 그에 따른 선택지를 정리한 **엔지니어링 검토**다.
> 법률 자문이 아니며, 게시 전 최종 판단은 프로젝트 책임자(필요하면 법률 검토)가 내린다.

## 1. 요약

| 산출물 | 현재(툴체인 런타임) | 권장 | 권장 후 GMP |
|---|---|---|---|
| CLI `elk` (배포용 바이너리) | `libgmp.a` 정적 포함(`__gmp*` 심볼 160개) | **(c)** GMP 없는 런타임으로 재링크(`build_runtime_nogmp.sh --relink elk`) | 없음 |
| CLI `elk` (개발자가 `lake build`로 직접 만든 것) | 정적 포함 | **(d)** 그대로 둔다(배포하지 않으면 LGPL 의무가 생기지 않음) | 있음(비배포) |
| C API `libelklean.a` + `ldflags` | 아카이브 자체엔 없음, 소비자가 `-lleanrt -lgmp`로 링크 | **(c)** `ELK_NO_GMP=1`, 런타임은 `libleanrt_nogmp.a`를 함께 배포 | 없음 |
| NAPI 애드온 `.node` (npm 플랫폼 패키지) | 정적 포함 | **(c)** `ELK_NO_GMP=1 sh scripts/build_napi.sh` | 없음 |
| WASM (`dist/wasm*`) | 처음부터 GMP 없음(mpn) | 변경 없음 | 없음 |

권장 결론: **배포되는 네이티브 산출물은 모두 (c) GMP 없는 런타임**으로 만든다. WASM 빌드가 이미 같은
방식(Lean 내장 `mpn` 큰 수)으로 검증돼 있고, 성능 영향은 측정 오차 수준이며(5장), 결과는 코퍼스 전체에서
바이트 동일하다.

## 2. 무엇이 GMP를 링크하는가

Lean 릴리스 툴체인(v4.35.0)은 `USE_GMP=ON`으로 빌드되어 `lib/lean/libleanrt.a`가 `-D LEAN_USE_GMP`로
컴파일돼 있고, 정적 `lib/libgmp.a`(GMP 6.3.0)를 함께 배포한다. `leanc --print-ldflags`는
`... -lleanrt -lc++ ... -lgmp -luv -lssl -lcrypto -Wl,-dead_strip`이다.

- `libleanrt.a`에서 GMP를 직접 참조하는 멤버는 `mpz.cpp.o`(GMP 함수 40개)와 `sharecommon.cpp.o`(1개)뿐이다.
  하지만 `mpz` 클래스의 레이아웃 자체가 `LEAN_USE_GMP`에 따라 다르므로(`mpz_t` vs
  `m_sign/m_size/m_digits`), `object.cpp` 등 `mpz`를 다루는 모든 멤버가 GMP 구성에 묶여 있다.
  → 런타임은 통째로 다시 컴파일해야 한다.
- `libInit.a`/`libStd.a`: GMP 심볼 0개. Lean C는 `lean.h`만 포함하고, `lean.h`에는 `LEAN_USE_GMP`
  조건부 코드가 없다(툴체인 `include/lean/lean.h`와 v4.35.0 소스의 `src/include/lean/lean.h`가 동일,
  `mpz` 관련은 `LeanMPZ` 태그와 `lean_is_mpz`뿐). 큰 수 연산은 모두 런타임의 out-of-line 함수
  (`lean_nat_big_add`, `lean_int_big_mul`, `lean_cstr_to_nat`, ...)를 부르므로 Init/Std(그리고 Elk) 객체는
  런타임의 큰 수 구현에 독립적이다. → **Init/Std 재생성 불필요**(WASM은 대상 아키텍처가 달라 재생성).
- C 수준 export 비교: 툴체인 `libleanrt.a`와 GMP 없는 `libleanrt_nogmp.a`의 C 심볼 차이는
  `lean_alloc_mpz`, `lean_extract_mpz_value` 두 개뿐이다(`lean_gmp.h`의 GMP 전용 API, `mpz_t`를 인자로 받음;
  elk-lean·Init·Std 어디서도 참조하지 않음).

산출물별:

| 산출물 | 링크 경로 | GMP 포함 여부(검증) |
|---|---|---|
| `.lake/build/bin/elk` | Lake가 툴체인 clang + `elk.rsp`(위 ldflags)로 링크 | `nm`: `__gmp*` 160개 |
| `.lake/build/ffi/libelklean.a` | Elk 객체 + `elk_lean.o`만 담은 아카이브; 소비자가 `ldflags`(`-lInit -lStd -lleanrt -lgmp -luv`)로 링크 | 아카이브 자체엔 없음, 링크 결과(`smoke`)엔 있음 |
| `plugins/org.eclipse.elk.js/dist/elk-lean.<triple>.node` | `libelklean.a` + `ldflags`로 `-bundle` | strip 전 `nm`: `__gmp*` 있음 |
| WASM | `tools/build.py`가 Lean 런타임 소스를 `LEAN_USE_GMP` 없이 emscripten으로 컴파일 | 없음 |

OpenSSL(`-lssl -lcrypto`)은 ldflags에 있지만 `openssl.cpp.o`가 버전 상수만 쓰므로 아무 멤버도 링크되지
않는다(`elk`에 SSL 심볼 0개). libuv(MIT)와 mimalloc(MIT, `libleanrt.a`의 `mimalloc.cpp.o`에 포함)는
두 구성 모두에 남는다.

## 3. LGPL v3 정적 링크 의무 (§4 Combined Works)

elk-lean 바이너리 + GMP는 LGPL v3의 "Combined Work"다. 배포(conveying)할 때 §4는 다음을 요구한다.

- (a) 각 사본에 GMP가 사용되었고 LGPL v3의 적용을 받는다는 **눈에 띄는 고지**.
- (b) **GPL v3와 LGPL v3 전문**을 함께 제공.
- (c) 실행 중 저작권 고지를 표시한다면 GMP 고지와 라이선스 문서 참조를 포함.
- (d) 다음 중 하나:
  - (0) **Minimal Corresponding Source**(GMP 소스)와 **Corresponding Application Code**(사용자가 수정한
    GMP와 다시 링크해 Combined Work를 만들 수 있는 형태, 즉 elk-lean 객체 코드/아카이브와 링크 방법)를 제공, 또는
  - (1) 실행 시점에 사용자 시스템의 라이브러리를 쓰고 인터페이스 호환 버전과 동작하는 **공유 라이브러리
    메커니즘**(동적 링크) 사용.
- (e) User Product라면 설치 정보(데스크톱/npm 배포에는 사실상 해당 없음).
- 그리고 Combined Work의 조건이 GMP 부분의 수정과 그 디버깅을 위한 리버스 엔지니어링을 막지 않아야 한다.
  EPL-2.0/GPL-3.0은 이를 금지하지 않는다.
- GMP 객체 코드 자체를 함께 배포하므로 GMP 소스 제공(또는 서면 제안) 의무가 따른다.

프로젝트 라이선스 관점: GPL-3.0-or-later 쪽을 택한 수령자에게는 LGPL v3가 호환되지만, EPL-2.0을 택한
수령자에게 바이너리를 줄 때도 위 의무는 GMP 부분에 대해 그대로 남는다. 즉 **라이선스 조합 자체는 가능하나,
모든 바이너리 배포(npm 플랫폼 패키지, GitHub 릴리스, C API 번들)마다 relink 가능한 형태를 유지해야 하는 운영
부담**이 생긴다. (GMP는 "LGPL v3 또는 GPL v2" 이중 라이선스이며 GPL v2 쪽은 GPL-3.0과 호환되지 않으므로
LGPL v3 경로가 유일한 현실적 선택지다.)

## 4. 선택지

### (a) 동적 `libgmp`
- macOS에는 시스템 GMP가 없다. Homebrew `gmp`에 의존하면 npm 설치가 외부 패키지 관리자에 묶이고, 대신
  `libgmp.dylib`을 패키지에 넣으면 install_name/`@loader_path`, 코드 서명, 사용자 교체 가능성, GMP 소스 동봉을
  모두 관리해야 한다. Linux는 glibc 배포판엔 `libgmp.so.10`이 있지만 musl/컨테이너/버전(Lean은 6.3.0 미만을
  unsound로 거부) 문제가 있다. Windows는 별도.
- Lean 툴체인의 `libleanrt.a`는 GMP 정적 링크를 전제로 하므로 결국 런타임 재빌드가 필요하고, 그렇다면 (c)보다 나을 게 없다.

### (b) relink 가능한 객체 동봉 (§4(d)(0))
- npm 플랫폼 패키지에 `libelklean.a`(수십 MB)·`elk_napi.o`·링크 스크립트·GMP 소스를 넣어야 한다. 패키지가
  커지고, 사용자가 실제로 relink하려면 C 툴체인과 Node 헤더가 필요하다. CLI 릴리스도 마찬가지.
- 법적으로 가능한 경로지만 매 릴리스마다 relink 재현성을 검증해야 하는 지속 비용이 든다.

### (c) GMP 없이 네이티브 Lean 런타임 빌드 (권장)
- WASM 빌드와 같은 접근: Lean 소스 `src/runtime`을 `LEAN_USE_GMP` 없이 컴파일하면 Lean 자체 `mpn` 큰 수
  구현(`mpn.cpp`, `mpz.cpp`의 non-GMP 분기)이 쓰인다. Lean의 CMake도 이 구성을
  "`-DUSE_GMP=OFF`: use Lean's built-in bignum implementation (safest; some performance cost)"로 안내한다.
- 남는 서드파티 코드는 Lean 런타임·Init·Std(Apache-2.0), mimalloc(MIT), libuv(MIT)뿐이며 모두 고지만
  필요하다(relink 의무 없음).
- 비용: 빌드 입력이 늘어난다(Lean 소스 체크아웃, mimalloc 태그, libuv 헤더; 스크립트가 버전을 툴체인에서
  읽어 고정). 릴리스 런타임과 컴파일러가 다르다(Apple clang vs 릴리스 빌드 컴파일러) → 테스트로 보증(5장).
- elk-lean의 핫 패스는 성능 라운드에서 큰 수 연산을 모두 제거했으므로(`scripts/perf/scan_generated_c.sh`:
  남은 큰 리터럴 1곳은 trace 출력 `RandomTrace.formatFixed`, `Float.ofInt`/`ofScientific` 코어 호출은
  `FastFloat`의 폴백뿐) 느린 큰 수 구현은 성능에 영향을 주지 않는다(측정 5장).

### (d) 현 상태 유지
- 개발용 `lake build` 산출물은 배포하지 않으므로 의무가 없다. 배포 CLI에 대해 유지하려면 (b)의 relink
  자료를 릴리스마다 함께 내야 한다 → 배포 CLI에는 권장하지 않는다.

## 5. 프로토타입 (c): `scripts/build_runtime_nogmp.sh`

```sh
sh scripts/build_runtime_nogmp.sh                  # .lake/build/runtime-nogmp/lib/libleanrt_nogmp.a
sh scripts/build_runtime_nogmp.sh --check          # 큰 수 차분 테스트(GMP vs mpn)
sh scripts/build_runtime_nogmp.sh --relink elk --relink elktest   # Lake 실행 파일 재링크(+ -gmp 대조군)
ELK_NO_GMP=1 sh scripts/build_ffi.sh --check       # libelklean.a ldflags/smoke를 no-GMP 런타임으로
ELK_NO_GMP=1 sh scripts/build_napi.sh              # NAPI 애드온
```

### 구성
- **소스**: 툴체인 태그의 Lean 소스(`.reference/lean4-v4.35.0`, `lean --githash`와 커밋 일치 확인,
  `lean.h`가 툴체인 것과 동일한지 확인). `src/runtime/CMakeLists.txt`의 `RUNTIME_OBJS` 34개(`uv/*`·
  `openssl.cpp` 포함) + `mimalloc.cpp` = 35개 객체. WASM과 달리 `uv/*`를 빼지 않는다(툴체인 `libuv.a`를
  그대로 링크).
- **define/플래그**(릴리스 `leanrt` 타깃과 동일, `-D LEAN_USE_GMP`만 제외): `-std=c++20 -D LEAN_MULTI_THREAD
  -ffp-contract=off -DLEAN_BUILD_TYPE="Release" -DLEAN_EXPORTING -D__CLANG__ -fvisibility=hidden
  -fvisibility-inlines-hidden -O3 -DNDEBUG -ftls-model=local-exec`, 추가로 `-fPIC`(애드온용).
  작은 객체 할당기는 툴체인 `include/lean/config.h`의 `LEAN_MIMALLOC` 그대로, `mimalloc.cpp`는
  `add_mimalloc_variant`의 `MIMALLOC_OPTS`(`-DMI_SHARED_LIB -DMI_SHARED_LIB_EXPORT -DMI_MAX_ALIGN_SIZE=8
  -DMI_SECURE=0 ...`)로 컴파일.
- **의존 소스**(`.lake/runtime-nogmp-deps/`에 필요 시 clone): mimalloc은 툴체인 `CMakeLists.txt`의
  `FetchContent` 태그(v3.4.5; `include/mimalloc.h`가 툴체인 `lean/mimalloc.h`와 동일한지 확인), libuv 헤더는
  툴체인 `libuv.a`의 버전 문자열(1.52.1). `openssl.cpp`는 `OPENSSL_VERSION_NUMBER`만 쓰므로 툴체인
  `libcrypto.a` 버전(3.6.1)으로 만든 스텁 헤더를 쓴다(OpenSSL 코드는 컴파일·링크되지 않음).
- **Init/Std**: 툴체인 `libInit.a`/`libStd.a`를 그대로 재사용(2장 근거). Elk 객체도 그대로.
- **재링크**: Lake는 `<clang> -o BIN @BIN.rsp`로 링크한다. `--relink`는 이 응답 파일에서 `-lleanrt`를
  `libleanrt_nogmp.a`로 바꾸고 `-lgmp`를 지운다. 대조군 `BIN-gmp`는 원래 응답 파일 그대로 같은 방식으로 링크한다.

- **컴파일러**: macOS 기본값은 툴체인 자신의 clang(23.1, Lean C를 컴파일하는 것과 같은 컴파일러)에 SDK의
  libc++ 헤더와 툴체인 `include/clang` 내장 헤더(resource dir)를 붙여 쓴다. `CXX`로 바꿀 수 있다(Apple clang
  `c++`도 동작 확인). 릴리스 `libleanrt.a`는 다른 환경(libc++ 20 헤더)에서 빌드되어 어느 쪽과도 객체가 바이트
  일치하지는 않는다(GMP 무관 멤버 `utf8.cpp.o`로 확인).

### 검증 결과 (macOS arm64, 2026-10-28)

| 항목 | 결과 |
|---|---|
| 재링크 정확성 | `--relink`의 대조군(원래 `elk.rsp` 그대로)이 Lake의 `.lake/build/bin/elk`와 바이트 동일(출력 이름이 같을 때; 이름은 `LC_UUID`·ad-hoc 서명에 들어감) → no-GMP 변형은 런타임 아카이브만 다르다 |
| C 심볼 | `libleanrt.a` 대비 `libleanrt_nogmp.a`의 C export 차이: `lean_alloc_mpz`, `lean_extract_mpz_value`만 없음 |
| GMP 심볼(`nm \| grep __gmp`) | `elk`: 160 → **0**, `elktest`: 160 → **0**, `smoke`: 162 → **0**; 애드온(strip 후)의 `GNU MP` 문자열 4 → **0** (`build_napi.sh`는 strip 전 `nm`으로 검사) |
| 동적 의존성(`otool -L`) | 세 산출물 모두 `libc++`, `libSystem`뿐(변화 없음) |
| 크기 | `elk` 23,482,032 → 23,353,872 B, 애드온 17,717,160 → 17,616,376 B |
| 큰 수 차분 테스트(`--check`) | `tests/runtime/BignumDiff.lean`: Nat/Int 사칙·`ediv/emod/tdiv/tmod/fdiv/fmod/bmod`·gcd/lcm·비트 연산·시프트·거듭제곱, 문자열 변환, `Float.ofInt/ofNat/ofScientific`·`toUInt64`, 0~1,280비트 피연산자(양/음, `2^k±1` 경계 포함), 400!, 메르센 수 등 8,005줄(8.8 MB) **GMP와 바이트 동일** |
| `lake test` 바이너리 재링크 | no-GMP `elktest`: **13777 통과 / 0 실패**(1 skip, `ELK_MODELS_DIR` 지정), 출력 로그가 GMP 대조군과 바이트 동일. `core.util.java`의 `2^64` 범위 차분 테스트(`toUInt64Wrap` 등, small-`Int` 밖 값)가 큰 수 경로를 탄다 |
| 코퍼스(`elk batch`, Java 기준 manifest 1,998개) | 레이아웃 1,997/1,997 **바이트 동일**, 예외 1건(588)도 같은 메시지, manifest 동일 |
| 코퍼스 + `--trace-dir`(4개 중 1개 표본 499개) | 레이아웃+layered 단계 trace 48,934개 파일 **전부 바이트 동일** |
| `build_ffi.sh --check` | GMP·no-GMP 두 모드 모두 통과(`elk layout --sort-keys`와 동일, 알고리즘 14, 오류 경로) |
| NAPI | no-GMP 애드온 로드·`node --test test/` **51/51**; `test/parity/run.mjs` 애드온(no-GMP) vs CLI(GMP) **898/898**(897 동일 + 1 양쪽 같은 예외) |
| 성능(`elk bench` 합성 26개, 20회+워밍업 3, 교차 실행, 시나리오별 중앙값) | no-GMP(clang 23)/GMP 기하평균 **0.964**(3라운드), **0.980**(5라운드); Apple clang 변형은 0.984, 1.018 |

성능 메모: 같은 이진 쌍(GMP vs Apple clang 변형)을 다른 에이전트들의 빌드가 몰린 시점(load average 약 26)에
처음 쟀을 때는 1.117이 나왔지만 부하가 줄어든 뒤 같은 이진이 0.984/1.018로 재현되어 소음으로 판단했다.
시나리오별 편차(±10%)도 라운드마다 부호가 바뀐다. 결론적으로 GMP 제거에 따른 성능 저하는 없고, 툴체인
clang으로 컴파일한 런타임이 Apple clang보다 2~4% 빠른 경향이라 기본값으로 삼았다. 생성 C의 남은 큰 수 진입점은
`scripts/perf/scan_generated_c.sh` 기준 `RandomTrace.formatFixed`(trace 출력 전용)의 큰 리터럴 1곳과
`FastFloat`의 코어 폴백뿐이다.

### Init/Std 재생성이 필요 없는 이유 (정리)
1. 툴체인 `lean.h` = 소스 `lean.h`, `LEAN_USE_GMP` 조건부 코드 없음 → Init/Std/Elk 객체가 보는 객체 레이아웃·
   inline 함수는 두 런타임에서 같다.
2. 큰 수는 `LeanMPZ` 태그의 불투명 객체이고 모든 연산이 런타임의 out-of-line 함수다. `mpz` 레이아웃을 아는
   코드는 런타임(`object.cpp`, `mpz.cpp`, `sharecommon.cpp`, `compact.cpp` 등)뿐이며 이것은 통째로 다시 컴파일한다.
3. `libInit.a`/`libStd.a`에는 GMP 심볼이 없고, 링크 결과는 위 테스트들로 GMP 빌드와 출력이 동일하다.

WASM 빌드는 대상(wasm64→wasm32)이 달라 툴체인 아카이브를 쓸 수 없어서 재생성하는 것이며, 이번 변경으로
WASM 빌드(`scripts/build_wasm.sh`, `tools/build.py`)는 바뀌지 않는다.

## 6. 남은 일
- Linux(`-pthread`, `--start-group`)는 스크립트에 분기만 있고 미검증. 특히 Linux 툴체인은 Lean C를 번들
  libc++/glibc sysroot로 링크하므로, 런타임을 시스템 `c++`(libstdc++)로 컴파일해 섞어도 되는지, 아니면 툴체인
  clang + 번들 sysroot로 컴파일해야 하는지 확인이 필요하다. Windows는 툴체인 자체가 미지원.
- 배포용 CLI의 릴리스 절차(`--relink elk` 산출물 `.lake/build/runtime-nogmp/bin/elk`를 패키징)는 아직 스크립트로
  묶여 있지 않다(릴리스/CI 작업에서 연결).
- 배포 파이프라인(CI)에서 `ELK_NO_GMP=1`을 기본으로 하고, `nm ... | grep __gmp` 0건을 게이트로 둔다.
- 툴체인을 올릴 때: mimalloc 태그·libuv 버전·OpenSSL 버전은 스크립트가 툴체인에서 읽지만, `RUNTIME_OBJS`나
  `MIMALLOC_OPTS`, 릴리스 플래그가 바뀌면 스크립트의 플래그 목록을 다시 대조해야 한다.
