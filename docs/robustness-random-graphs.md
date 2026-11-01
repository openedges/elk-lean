# 무작위 그래프 견고성 분류 (HX, 2026-10-28)

> elk-lean이 무작위 그래프에서 멈추거나(hang) 스택이 넘치거나(overflow) 예외를 던지는 입력을
> ELK Java 0.12.0(결과 기준)·elk-rs `eb586b6d`(보조 기준)와 비교해 **계승 동작**과 **Lean 단독 결함**으로
> 나누고, Lean 단독 결함은 parity를 유지하며 고친 기록이다. 픽스처: `tests/fixtures/robustness/`,
> 회귀 테스트: `tests/lean/Tests/Api/Robustness.lean`.

## 1. 요약

- 입력 12,000개: `scripts/gen_nodesize_graphs.py` 시드 1~10 × 600개(**s 집합**, 생성기 그대로)와, 같은 그래프를
  ELK Java의 노드 크기 계산기가 받아들이도록 고친 사본(**v 집합**, 3절).
- **수정 전** elk-lean(15초 제한): s 집합 hang 45 / overflow 12 / 예외 159, v 집합 hang 93 / overflow 12 / 예외 159.
- **수정 후**: hang **0**. v 집합에서 Lean과 Java가 둘 다 예외인 216건은 클래스와 메시지가 **전부 일치**
  (JSON API 래퍼 제외, 6.2절). 남은 비일치는 계승 overflow 12(세 구현 동일), Java 자체 결함 11(Lean·elk-rs 성공)뿐이다.
- 수정 4건(모두 Java와 같은 결과로 맞추는 방향, 코퍼스 출력 바이트 동일):
  1. ELK 노드 마이크로 레이아웃 경로의 라벨 쌓기 무한 루프(elk-rs 계승, Java는 성공) — hang 138건 전부.
  2. radial `The given graph is not a tree!`의 예외 클래스(`UnsupportedConfigurationException` → Java의 `IllegalArgumentException`).
  3. layered 계층 처리 검사의 예외 클래스·문구(`UnsupportedGraphException`, `LGraph.toString()` 포함).
  4. `fixed` + `ORTHOGONAL`에서 섹션 없는 간선의 누락된 예외(`IllegalArgumentException: The edge needs to have exactly one edge section. Found: 0`; Java·elk-rs는 던지고 Lean만 삼켰다).
- **열린 항목**(HX 시점, 7절): 생성기 그대로의 입력 4,561건은 Java가 노드 크기 계산기 검증으로 거부하고
  elk-lean·elk-rs는 레이아웃한다(검증 미이식). 또 Java가 성공하는 v 집합 5,761건 중 elk-lean 출력이 Java와
  정확히 같은 것은 약 10%뿐이다(코퍼스는 1878/1997) — 무작위 노드 크기·포트 구성에서 큰 결과 격차가 있다.
  → **RJ1(8절)에서 해결**: 노드 마이크로 레이아웃을 Java의 전체 셀 시스템으로 바꾸고 Java 검증을 이식해 s 집합의 Java
  예외 4,783건 중 4,777건(나머지 6건은 Java 자체 결함)이 클래스·메시지까지 같고, v 집합 정확 일치는 616 → 1,995/5,761(1e-6: 623 → 2,026).

## 2. 방법

### 2.1 실행

| 구현 | 실행 방식 | 제한 |
|---|---|---|
| elk-lean | `elk layout g.json --pretty --sort-keys -o out.json`, 입력마다 프로세스 1개, 3개 병렬 | 15초(초과 = hang). 종료 메시지 `Stack overflow detected. Aborting.` = overflow, 그 밖의 0이 아닌 종료 = 예외(첫 줄) |
| ELK Java 0.12.0 | `ElkJavaBaseline`(`scripts/run_java_baseline.sh`와 같은 클래스·클래스패스, 미수정 Maven 아티팩트), 집합마다 JVM 1개, 전체에 900초 경보 | 모델별 제한 기능이 스크립트에 없어 전체를 감쌌다. 20개 집합 모두 제한 안에 끝났다(Java hang 0). `StackOverflowError` = overflow |
| elk-rs | `model_parity_layout_runner`, 입력마다 프로세스 1개, `MODEL_PARITY_TIMEOUT_SECS=10` | 러너 시간 초과 = hang, `overflowed its stack` = overflow, panic = 예외 |

hang 입력은 `sample <pid>`로 6초 뒤 호출 스택을 떠서 위치를 찾았고, Java 예외는 작은 보조 클래스
(`Trace.java`, `ElkJavaBaseline.initialize()` 뒤 `RecursiveGraphLayoutEngine`)로 스택 상위 프레임을 확인했다.
elk-rs는 Lean이 실패했거나 Lean·Java의 성공 여부가 다른 입력 548개에만 돌렸다.

### 2.2 v 집합(Java가 받아들이는 사본)

생성기 그대로의 입력은 Java가 80% 가까이 노드 크기 계산기 단계에서 거부한다(7.1절). Lean의 실패가 Java에서
어떻게 되는지 보려면 그 검증을 통과하는 입력이 필요하므로, 같은 그래프에 다음만 바꿨다.

- 변(`elk.port.side`)이 없는 포트에 포트 id의 CRC32로 정한 변을 준다.
- 포트 라벨 배치에 `ALWAYS_SAME_SIDE`/`ALWAYS_OTHER_SAME_SIDE`/`SPACE_EFFICIENT` 중 둘 이상이 있으면 `SPACE_EFFICIENT`를
  빼고, 그렇게 되게 만드는 폐기 크기 옵션 `SPACE_EFFICIENT_PORT_LABELS`(`DeprecatedLayoutOptionReplacer`가
  `SPACE_EFFICIENT`로 옮긴다)를 지운다.

## 3. 결과 수치

### 3.1 집합별 결과(입력 6,000개씩)

| 집합 | 구현 | ok | 예외 | hang | overflow |
|---|---|---:|---:|---:|---:|
| s | elk-lean 수정 전 | 5,784 | 159 | 45 | 12 |
| s | elk-lean 수정 후 | 5,772 | 216 | 0 | 12 |
| s | ELK Java | 1,205 | 4,793 | 0 | 2 |
| v | elk-lean 수정 전 | 5,736 | 159 | 93 | 12 |
| v | elk-lean 수정 후 | 5,772 | 216 | 0 | 12 |
| v | ELK Java | 5,761 | 227 | 0 | 12 |

ELK Java 예외 내역 — s: `IllegalArgumentException: Label and node size calculator can only be used with ports that have port sides assigned.` 2,126,
`UnsupportedConfigurationException: Invalid port label placement: [..]` 1,767, `IllegalStateException: Port side is undefined` 820,
`UnsupportedGraphException: The hierarchy aware processor LAYER_SWEEP in child node ..` 32, `The edge needs to have exactly one edge section` 25,
`The given graph is not a tree!` 17, `ArrayIndexOutOfBoundsException` 6. v: `not a tree` 95, `LAYER_SWEEP` 64, `edge section` 57,
`ArrayIndexOutOfBoundsException` 10, `NullPointerException` 1.

### 3.2 문제 입력 분류(v 집합)

| 클래스 | 건수 | elk-lean 수정 전 | elk-lean 수정 후 | elk-rs | ELK Java | 판정 |
|---|---:|---|---|---|---|---|
| A. 라벨 쌓기 루프 | 93 | hang | ok | hang | ok | elk-rs 계승 결함, **수정**(4.1) |
| B. radial 루트 없음 | 95 | `UnsupportedConfigurationException: The given graph is not a tree!` | `IllegalArgumentException: …`(Java 동일) | `UnsupportedConfigurationException` panic | `IllegalArgumentException: The given graph is not a tree!` | 예외 클래스 불일치, **수정**(4.2) |
| C. 자식 그래프만 `LAYER_SWEEP` | 64 | `UnsupportedConfigurationException: … in a child graph is only allowed if the root graph uses the same processor.` | Java와 같은 클래스·문구 | `UnsupportedConfigurationException`(`LayerSweep`, elk-rs 문구) panic | `UnsupportedGraphException: The hierarchy aware processor LAYER_SWEEP in child node G-unlayered[…] is only allowed if the root node specifies the same hierarchical processor.` | 클래스·문구 불일치, **수정**(4.3) |
| D. `fixed` + `ORTHOGONAL`, 섹션 없는 간선 | 57 | ok(오류를 삼킴) | `IllegalArgumentException: The edge needs to have exactly one edge section. Found: 0` | 같은 문구 panic | 같은 예외 | Lean 단독 예외 누락, **수정**(4.4) |
| E. radial 사이클 재귀 | 12 | overflow | overflow | overflow | `StackOverflowError` | **계승 동작**(5장) |
| F. Java 교차 계수기·greedy switch 결함 | 11 | ok | ok | ok | `ArrayIndexOutOfBoundsException`(10) / `NullPointerException`(1) | **Java 결함**, 재현하지 않음(5장) |

s 집합의 문제 입력도 같은 클래스로 나뉜다: hang 45(전부 A, Java는 노드 크기 검증 예외), 예외 159(B 95·C 64; Java는
그중 49건만 같은 예외이고 110건은 그보다 먼저 노드 크기 검증에서 실패), overflow 12(E; Java는 2건만 overflow이고
10건은 그보다 먼저 검증 예외), 7.1절의 검증 미이식 4,561건(Lean 성공, Java 검증 예외), Java 교차 계수기 결함 6건(Lean 성공).

## 4. 수정 사항

### 4.1 라벨 쌓기 무한 루프 (`NodeDimensionCalculation.resolveHorizontalOverlaps`)

- 위치: `plugins/org.eclipse.elk.alg.common/Elk/Alg/Common/NodeSpacing/NodeDimensionCalculation.lean`. elk-rs가 Java의
  `NodeLabelAndSizeCalculator` 대신 쓰는 ELK 경로(`calculate_label_and_node_sizes_for_elk`, `NodeMicroLayout`이 호출 —
  force/stress/radial/rectpacking/mrtree/box 등과 그 자식)의 `stack_horizontal_side_labels` 루프. Java에는 없는 코드다.
- 원인: 음의 방향(SOUTH 쪽 INSIDE 라벨 등을 위로 쌓을 때) 새 좌표 `p.y - labelSize.y - gapY`가 반올림 때문에 겹침 검사
  `absoluteY + labelSize.y > p.y - gapY`를 다시 만족한다. 예(픽스처 `label_stack_hang.json`): `p.y = -15.8`,
  `labelSize.y = 8.6`, `gapY = 1` → 새 좌표 `-25.4`, `-25.4 + 8.6 = -16.799999999999997 > -16.8`. 한 바퀴가 시작 좌표로
  끝나므로 elk-rs와 수정 전 Lean은 영원히 반복한다.
- 수정: 조정이 있었는데도 한 바퀴가 시작 좌표로 끝나면 멈춘다(`absoluteY == sweepStart`). 그런 바퀴는 상태가 같아
  똑같이 반복될 수밖에 없으므로, elk-rs가 끝나는 모든 입력의 결과는 그대로다(코퍼스·합성 바이트 동일로 확인).
  주기 2 이상의 순환은 이 검사로 잡히지 않지만 12,000개에서 관찰되지 않았다.
- 결과: hang 138건(s 45 + v 93) 전부 해결. 단, 이 경로 자체가 Java와 다른 근사여서 결과는 Java와 다르다
  (`label_stack_hang`: Java 노드 0×0·라벨 y −24.4/−15.8, Lean 62×0·−25.4/−15.8; 7.2절).

### 4.2 radial 루트 없음의 예외 클래스

- `plugins/org.eclipse.elk.alg.radial/Elk/Alg/Radial/RadialLayoutProvider.lean`: Java `RadialLayoutProvider.layout`은
  `IllegalArgumentException("The given graph is not a tree!")`을 던진다(elk-rs는 `UnsupportedConfigurationException`).
  `throwIllegalArgument`로 바꿨다. vertiflex는 Java도 `UnsupportedConfigurationException`이라 그대로 둔다.
- 테스트 `radial.errors`의 기대값도 Java 클래스로 바꿨다.

### 4.3 layered 계층 처리 검사(`reviewAndCorrectHierarchicalProcessors`)

- Java: `UnsupportedGraphException("The hierarchy aware processor " + childCms + " in child node " + child + " is only allowed if the root node specifies the same hierarchical processor.")`,
  `child`는 `LGraph.toString()`(`G-unlayered[n_<designation>, …]`). `LNode.getDesignation()`은 첫 라벨 텍스트, 없으면
  `ElkGraphTransformer.getOriginIdentifier`(ElkNode 식별자를 조상과 `.`으로 이은 경로, 예 `n_root.n4.n4_n0.n4_n0_n4`), 없으면 층 안 인덱스다.
- 수정:
  - `ElkLayered.lean`: 검사를 `hierarchicalProcessorViolation`으로 분리하고 Java 문구(`hierarchicalProcessorMessage`)와
    `UnsupportedGraphException`으로 던진다.
  - `Graph/LGraphQueries.lean`: `nodeDesignationWith`/`nodeToStringWith`/`layerToStringWith`/`graphToStringWith`(origin 식별자
    해석 함수를 받는 판). 기존 `nodeDesignation` 등은 해석 함수 없이 그대로다(디버그 출력 불변).
  - `Graph/Transform/ElkGraphTransformer.lean`: `nodeIdentifier`/`getOriginIdentifier`(Java `getIdentifier`와 같은 규칙).
  - `LayeredLayoutProvider.lean`: layered 아레나에는 ElkGraph가 없으므로, `doCompoundLayout`이 이 예외로 실패하면 같은
    아레나 상태에서 식별자를 넣어 메시지를 다시 만든다(`withHierarchicalProcessorMessage`, 오류 경로에서만 동작).
- 결과: v 64건·s 32건 메시지가 Java와 바이트 단위로 같다.

### 4.4 `FixedLayoutProvider.generateJunctionPoints`의 누락 예외

- `plugins/org.eclipse.elk.core/Elk/Core/Util/FixedLayoutProvider.lean`: `ElkUtil.determineJunctionPoints`의 오류를 빈 접합점으로
  바꾸던 처리를 Java·elk-rs처럼 `IllegalArgumentException`으로 던지게 했다. `fixed` 알고리즘 + `elk.edgeRouting: ORTHOGONAL`에서
  `bendPoints`가 없는(섹션이 없는) 간선이 있으면 Java는 `The edge needs to have exactly one edge section. Found: 0`으로 실패한다.

## 5. 계승 동작과 Java 결함

| 동작 | 증거 | 처리 |
|---|---|---|
| radial이 루트에서 도달하는 사이클에서 무한 재귀 | Java `StackOverflowError`, 스택 1024프레임이 `AnnulusWedgeByNodeSpace.calculateWedgeSpace`(`RadialUtil.getSuccessors`) 반복; elk-rs `thread … has overflowed its stack`; Lean `Stack overflow detected. Aborting.` (픽스처 `radial_cycle_overflow.json`, r→a→b→a) | 고치지 않음. `HISTORY.md` 오라클 특이점(radial 비트리 입력)과 같은 계열. GitHub `eclipse-elk/elk`에서 radial `StackOverflowError` 이슈는 찾지 못했다 |
| Java 교차 계수기 `BinaryIndexedTree.add/rank`의 `ArrayIndexOutOfBoundsException`(10건, `CrossingsCounter.countCrossingsOnPorts`, layered `LayerSweepCrossingMinimizer`/계층 처리) | Java 스택(픽스처 `java_crossing_counter_aioobe.json` = v9/g0025: `Index 5 out of bounds for length 2`); elk-rs·Lean 성공 | Java 결함으로 분류, 재현하지 않음(ticket 213 NaN과 같은 의도적 예외). P3 코드는 이번 라운드 P3L 담당이라 손대지 않았다 |
| Java greedy switch `BetweenLayerEdgeTwoNodeCrossingsCounter$AdjacencyList.addAdjacencyOf`의 `NullPointerException`(1건, v9/g0273) | Java 스택; elk-rs·Lean 성공 | 같음 |

## 6. 검증

### 6.1 게이트(수정 후)

- `lake build` 경고 0·오류 0, `lake test` **13812 통과 / 0 실패**(기존 13806 + `robustness.*` 6건; `radial.errors` 기대값 변경).
- 코퍼스 바이트 동일: 수정 전 바이너리와 `scripts/run_model_parity.sh`의 `lean/**` 1,447개 전부 동일(`diff -rq` 0), elk-rs model parity 1447/1447.
- 합성 26개(`elk bench --dump-dir` 입력) 26/26 바이트 동일.
- ELK Java parity(`scripts/run_java_parity.sh`): 정확 일치 1878 / 드리프트 119, `details_exact.tsv`가 수정 전과 경로 외 동일(같은 집합·같은 차이 수).
- 무작위 12,000개: 위 3.1절. 수정 후 Lean 예외 216건(v)은 Java 메시지와 전부 같다.

### 6.2 JSON API 래퍼

`Elk.Api.catchLayout`(elk-rs `catch_layout`)은 `org.eclipse.elk.core.`이 없는 오류를 `UnsupportedConfigurationException: `으로
감싼다. 그래서 `java.lang.*` 예외는 API·CLI에서 `org.eclipse.elk.core.UnsupportedConfigurationException: java.lang.IllegalArgumentException: …`처럼
보인다. 비교는 이 접두를 떼고 했다. Java(`Throwable.toString()`)와 같게 하려면 `catchLayout`이 `java.` 클래스도 통과시키면 되지만,
API 규약(elk-rs·elkjs 호환) 결정이라 바꾸지 않았다(7.3절).

**RJ2 후속(해결)**: `catchLayout`은 이제 완전한 Java 예외 클래스 이름(`java.…`/`org.eclipse.…`, `…Exception`/`…Error`)으로
시작하는 오류를 그대로 내보낸다(`isJavaThrowableText`). API·CLI·NAPI 오류 문구가 Java `Throwable.toString()`과 같다
(`java.lang.IllegalArgumentException: …`, `org.eclipse.elk.graph.json.JsonImportException: …`). 이 무작위 비교는 이제
`scripts/run_random_java_parity.sh`로 반복 실행하며(`TESTING.md` 2B), 최신 결과는 `tests/random_parity/report.md`에 있다.

## 7. 열린 항목

### 7.1 노드 크기 계산기 검증 미이식(s 집합 4,561건) — RJ1에서 이식(8절)

Java `NodeMicroLayout.execute()`는 `sortPortLists` → `NodeLabelAndSizeCalculator.process`(노드마다 `NodeContext` 생성 시
`PortLabelPlacement.isValid`/`NodeLabelPlacement.isValid` → `UnsupportedConfigurationException("Invalid port label placement: [..]")`,
`PortContextCreator.createPortContexts`의 변 없는 포트 → `IllegalArgumentException`)를 돌고, 순서 고정 포트 제약 노드의 정렬
비교자(`ElkGraphAdapters.PortComparator`)는 변이 `UNDEFINED`인 두 포트를 비교하면 `IllegalStateException("Port side is undefined")`을 던진다.
elk-rs의 ELK 경로는 이 검증이 없고 elk-lean도 따라서 레이아웃한다(layered의 generic 경로는 변 없는 포트 검사가 있다).
Java와 맞추려면 (a) 배치 유효성 검사, (b) 변 없는 포트 검사, (c) Java `TimSort`(`ECollections.sort` → `Arrays.sort`)의 비교 순서를
흉내 내 `Port side is undefined`가 나는지 판정하는 일이 필요하다(어느 예외가 먼저인지는 노드 순서와 정렬 비교 순서에 달렸다).
elkjs도 같은 Java 코드라 이 입력을 거부한다. 코퍼스는 Java가 모두 통과하므로 영향이 없을 것으로 보이나, 사용자 입력에
대한 동작이 바뀌는 설계 결정이라 별도 작업으로 남긴다. 관련 상류 이슈: eclipse-elk/elk#296(종료).

### 7.2 무작위 노드 크기 그래프의 Java 결과 격차 — RJ1에서 노드 마이크로 레이아웃 몫 해결(8절)

v 집합에서 Java·Lean이 모두 성공한 입력의 정확 일치(tol 0)는 집합당 56~71/567~584(약 10%)다(tol 1e-6도 57~72).
차이는 좌표 70%·라벨 13%·섹션 13%이며, 예로 force의 포트 3개 노드(v1/g0019 `n0`, `PORTS` 크기 제약)는 Java가 46×0 크기에 포트를
배치하지만 Lean(=elk-rs ELK 경로)은 크기와 포트를 바꾸지 않는다. 실험으로 `NodeMicroLayout.execute`를 generic 경로
(`calculateLabelAndNodeSizes`, 전체 셀 시스템)로 바꾸면 코퍼스 Java parity는 1878/119로 같은 집합·같은 차이 수를 유지하고
v1 62→97, v2 56→107로 늘었다(elk-rs parity는 확인하지 않음, 커밋하지 않음). 노드 마이크로 레이아웃 외에도 차이가 크게 남으므로
별도 조사가 필요하다.

### 7.3 기타

- ~~JSON API가 `java.lang.*` 예외를 `UnsupportedConfigurationException`으로 감싸는 규약(6.2절)을 유지할지~~ — RJ2에서 Java 문구로 바꿨다.
- ~~layered `LayerConstraintPreprocessor`/`Postprocessor`의 예외 메시지~~ — RJ2에서 해결(`LGraphArena.errorNode` + `LayeredLayoutProvider`가
  오류 경로에서 식별자 경로를 넣는다; postprocessor 문구의 Java 이중 공백 `that  does`도 맞췄다). 원래 기록: 예외 메시지(`Node '…' has its layer constraint …`)도 Java는
  `getDesignation()`(식별자 경로 포함)을 쓰지만 Lean은 식별자 없는 `nodeDesignation`이다. 무작위 입력에서는 나오지 않아 두었다.
- `elk batch`는 overflow 입력에서 프로세스 전체가 중단된다(Lean 런타임의 스택 오버플로 처리). 무작위 Java parity를 돌릴 때는
  overflow 입력을 매니페스트에서 빼야 했다.
- Java가 실패하는 v 집합 결함(5장)을 Lean이 재현해야 하는지(현재 정책: 재현하지 않음).


## 8. 반복 실행 파이프라인과 첫 차이 분류 (RJ2, 2026-10-28)

### 8.1 파이프라인

`sh scripts/run_random_java_parity.sh <out> [--seeds 1-10] [--sets s,v] [--with-oracle]`(상세 `TESTING.md` 2B):
생성(`gen_nodesize_graphs.py`, 시드 의미 그대로라 HX의 집합과 바이트 동일) → Java용 정리(`sanitize_for_java.py`) →
ELK Java(집합마다 JVM 1개, 모델별 무진행 감시 60초·집합 경보 1800초) → elk-lean(입력마다 프로세스, 15초) →
선택적으로 elk-rs → 비교(tol 0·1e-6, 예외 클래스+문구, 결과 행렬) → 분류(`classify_random_parity.py`).
산출물은 `<out>/report.md`·`details.tsv`·`classification.md`·`classes.tsv`, 추적 사본은 `tests/random_parity/report.md`.
시드 1~10 전체(12,000개)는 이 Mac에서 생성·실행 약 4분과 비교·분류 몇 분, `--with-oracle`이면 약 15분이 더 든다(elk-rs가 라벨 쌓기 루프 입력
약 140개에서 제한 시간까지 돈다). 실험용 `d` 집합(`--sets s,v,d`)은 `v`에 Java의 알고리즘별 옵션 기본값을 명시적으로
써 넣은 사본이다(`sanitize_for_java.py --explicit-defaults`).

### 8.2 첫 결과(수정 후 바이너리, 시드 1~10, 집합당 6,000개)

| 집합 | Lean ok/예외/timeout/overflow | Java ok/예외/timeout/overflow | 둘 다 ok | 정확 일치(tol 0) | 1e-6 | 둘 다 예외 | 문구 일치 | elk-rs=Java 정확 |
|---|---|---|---:|---:|---:|---:|---:|---:|
| s | 5,772/216/0/12 | 1,205/4,793/0/2 | 1,205 | 417 | 418 | 216 | 74 | 307 |
| v | 5,772/216/0/12 | 5,761/227/0/12 | 5,761 | 616 | 623 | 216 | **216** | 416 |
| d(실험) | 5,772/216/0/12 | 5,761/227/0/12 | 5,761 | **1,067** | 1,079 | 216 | 216 | 762 |

- 수정 전 바이너리와 결과·레이아웃은 같고 예외 문구만 다르다: v 집합 문구 일치 64 → **216/216**(152건은 API 래퍼만 달랐다),
  s 집합 32 → 74(나머지 142건은 Java가 노드 크기 검증 예외를 먼저 던지는 입력 — 7.1절, RJ1 담당).
- 결과가 다른 입력: v 집합 Lean ok·Java 예외 11(5장 Java 결함), s 집합 Lean ok·Java 예외 4,567(검증 미이식 4,561 + Java 결함 6),
  Lean overflow·Java 예외 10(Java가 검증에서 먼저 실패). 양쪽 hang/timeout 0.
- elk-rs는 Lean보다 Java와 덜 맞는다(v 416 vs 616) — Lean이 이미 고친 Java 정렬·수치 의미론 차이 때문이다.

### 8.3 차이 분류(둘 다 성공한 12,727개 중 정확 불일치 10,627개)

차이를 "자기 결과가 다른 가장 깊은 레이아웃 단위"(알고리즘 1회 실행)에 귀속시킨 플래그다. 한 입력이 여러 플래그를 가질 수 있다.
`rs=lean`은 elk-rs가 Lean과 같은 출력을 낸 수(= elk-rs에서 물려받은 차이). 최신 수치는 `tests/random_parity/report.md`.

| 플래그 | 입력 수 | rs=lean | 알고리즘별 | 가설 / 다음 작업 |
|---|---:|---:|---|---|
| `NML` 비layered 노드 마이크로 레이아웃(자식 노드 크기·포트·라벨) | 7,601 | 7,183 | force 1,854, stress 1,825, mrtree 1,788, rectpacking 1,756, radial 1,574, box 323, fixed 277 | elk-rs의 단순화 ELK 경로가 포트를 아예 배치하지 않는다(예: `s1/g0123` force 루트의 자식 `n1` SOUTH 포트가 Java는 y 20.1에, Lean은 (0,0)에 남는다). Java `NodeMicroLayout` → `NodeLabelAndSizeCalculator` 경로로 전환(**RJ1 진행 중**). 복합 자식의 포트·라벨도 부모 비layered 알고리즘의 마이크로 레이아웃이 놓는다. |
| `SEC` 한쪽에만 간선 섹션 | 2,838 | 2,661 | box 708, fixed 693, rectpacking 603, radial 578, force/mrtree/stress 약 275씩 | Java는 알고리즘이 경로를 만들지 않은 간선에 `sections`를 쓰지 않는데 Lean은 직선 섹션을 만든다(3,565 단위 전부 `edge-extra-section`, 반대 방향 0). box/fixed 단위의 모든 간선, 포트가 있는 radial 그래프 등. 담당 후보: JSON `transferLayout`/각 provider의 간선 처리(예: `d1/g0011` `n2_n3`[fixed], `v1/g0015` `n1`[radial]). |
| `LNODE` layered 노드 크기·포트·라벨 | 2,178 | 2,056 | — | layered 단독 입력 1,999개 중 27.9%가 불일치; 복합·`INCLUDE_CHILDREN`·포트 정렬(`portAlignment.default`)·포트 라벨 배치에서 lift 1.3~1.65. `LabelAndNodeSizeProcessor`(Java 셀 시스템)·`HierarchicalPortConstraintProcessor`·외부 포트 배치 조사(예: `d1/g0007` `n2_n1`의 자식 폭 Java 0 vs Lean 50, `d1/g0009`). |
| `DEF` 비layered 알고리즘의 Java 기본값 미적용 | 1,551(s+v) | 1,489 | box 845, fixed 659, force 49, mrtree 43, rectpacking 9 | Java는 `.melk`의 `supports <option> = <값>`을 알고리즘별 `Options` 상수의 기본값으로 읽는다: box padding 15·nodeNode 15·aspectRatio 1.3, fixed padding 15, force padding 50·nodeNode 80·edgeLabel 5, mrtree padding 20·nodeNode 20·edgeNode 3, rectpacking padding 15·nodeNode 15. elk-lean/elk-rs는 `CoreOptions` 기본값(12/20)을 쓴다 — 옵션 없는 3노드 그래프만으로도 box/fixed/force/mrtree가 Java와 다르다. `d` 실험에서 이 값을 명시하면 v 616 → **1,067** 정확 일치(+451). 각 `<Alg>Options`의 재선언 기본값 이식(옵션 메타데이터 `ForceMetaDataProvider` 등에는 이미 있다). |
| `LEDGE` layered 간선 경로·간선 라벨만 | 922 | 853 | — | 예: `d1/g0018` 굽은 점 x 141.9000015258789 vs 141.89999389648438 — float(f32) 반올림 경로 차이로 보인다(포트 크기·라벨이 f32인 값). 스플라인·직교 라우팅 조사. |
| `LPOS` layered 노드 위치만 | 104 | 92 | — | P4 노드 배치(BK/NS), 소수. |
| `POS` 비layered 위치만(기본값으로 설명 안 됨) | 73 | 67 | radial 24, stress 19, mrtree 17 | radial 위치(옵션 없는 3노드 그래프도 다름: `radial_edge` 프로브), stress/mrtree 소수. |
| `T` 1e-6 이내 | 20 | 18 | — | 부동소수점 잡음. |

옵션 기능별 lift는 무작위 생성기가 대부분의 옵션을 그래프 어딘가에 넣기 때문에 1 근처라 정보가 적다(보고서의 layered 단독 표가 더 유용하다).
다음 라운드 브리프 단위: (1) `NML`(RJ1), (2) `DEF` 알고리즘별 기본값, (3) `SEC` 경로 없는 간선의 섹션(해결, §8.1), (4) `LNODE` layered 노드/포트,
(5) `LEDGE`/`LPOS` layered 라우팅·배치, (6) `POS:radial`.
### 8.1 SEC 결과 (SEC, 2026-10-28, 병합 `5662ad5`)

원인은 exporter나 provider가 아니라 layered `ElkGraphLayoutTransferrer`의 elk-rs 전용
`applyFallbackSections`/`applyFallbackSectionsRecursive`였다. layered 컨테이너와 **모든 자손**(앞서
box/fixed/rectpacking/radial/force/stress/mrtree로 배치된 자식 포함)의 section 없는 간선에 직선 section을
붙였고, ELK Java의 `applyLayout`은 `LEdge`가 있는 간선만 적용한다(importer가 거른 계층 간선·inside self
loop·`NO_LAYOUT` 간선에는 아무것도 쓰지 않음). fallback을 제거하고, 여러 section을 가진 간선의 Java 규칙을
맞췄다: force/stress/mrtree/vertiflex/spore는 `firstEdgeSection(e, true, true)`의 **첫** section(elk-rs는
마지막 또는 전부), fixed/random은 Java의 `IllegalStateException`을 그대로 재현, box/rectpacking/
topdownpacking은 간선 불변, radial은 루트에서 닿는 비계층 트리 간선만. 결과(seed 1~10): SEC 입력
s 75 → 0, v 1,404 → 0, d 1,409 → 0; 정확 일치 s 912 → 963, v 1,995 → 2,383, d 2,268 → 2,748; 정확 →
비정확으로 바뀐 입력 0, 코퍼스 출력 변화 0. 테스트 `Tests/Api/Sections.lean`(fixture `tests/fixtures/sections/`).
남은 관련 항목: layered importer가 `SEPARATE_CHILDREN` 실행의 교차 계층 간선에서 예외를 던지는 문제(Java는
형제/그래프 간선만 변환하고 나머지는 무시; LNODE), mrtree AVOID_OVERLAP 라우터의 bend(OPT의 `edgeNode`
기본값과 함께).

## 9. RJ1: 노드 마이크로 레이아웃의 Java 경로 전환과 노드 크기 검증 (2026-10-28)

### 8.1 변경

- `NodeMicroLayout.execute`(force/stress/mrtree/radial/rectpacking/vertiflex와 그 자식 그래프)가 Java처럼
  `sortPortLists` → 노드마다 `NodeLabelAndSizeCalculator.process(graph, node, true, false)`(전체 셀 시스템,
  `NodeDimensionCalculation.calculateLabelAndNodeSizesJava`) → `calculateNodeMargins`를 돈다. elk-rs의 ELK 경로
  (`calculateLabelAndNodeSizesForElk`: `processNode` + 포트를 옮기지 않는 단순 포트 라벨 배치)는 더 이상 쓰지 않는다
  (테스트에서만 호출, 4.1절의 hang 수정도 그 경로에만 남음).
- Java 검증 이식(클래스·메시지 Java와 동일): `NodeContext` 생성 시 `UnsupportedConfigurationException: Invalid port label
  placement: [..]` / `Invalid node label placement: [..]`(layered 임포터의 `computeInsideNodeLabelPadding`에서도),
  `PortContextCreator`의 `IllegalArgumentException: Label and node size calculator can only be used with ports that have port
  sides assigned.`, `ElkGraphAdapters.PortComparator`의 `IllegalStateException: Port side is undefined`(포트 정렬은
  `javaSortByM` = JDK 21 `TimSort`, `Double.compare`·Java `int` 뺄셈).
- elk-rs가 Java와 다르던 셀 시스템 세부(코퍼스 출력 바이트 동일):
  `MINIMUM_SIZE` + `MINIMUM_SIZE_ACCOUNTS_FOR_PADDING`에서 가운데 행의 너비 기여를 켜지 않음(Java는 높이 플래그만 두 번
  설정 — v 집합 node-size 차이의 대부분, Java 너비 0 대 elk-rs 30/50/110), 표 형식 그리드의 열 너비 배열 누적 갱신,
  `COMPUTE_PADDING`의 패딩 적용(`setNodePadding`), `DoubleMath.fuzzyEquals`의 `<=` 허용오차.
- rectpacking `MinSizePreProcessor`: 부모가 있는 그래프는 Java처럼 `process(parent, node, false, true)`의 라벨·포트 기반
  최소 크기와 최댓값을 취한다(검증 예외도 여기서 난다; elk-rs는 최소 크기 제약만).
- box/fixed 옵션 기본값을 Java(`Core.melk`)로: box 패딩 15·간격 15·우선순위 0·종횡비 `1.3f`(=1.2999999523162842),
  fixed 패딩 15(elk-rs는 코어 기본값 12/20).
- 성능: 포트·라벨이 없고 크기 제약이 고정(`areSizeConstraintsFixed`)이며 `COMPUTE_PADDING`이 없는 노드는 셀 시스템이 할
  일이 없으므로 검증만 하고 크기를 그대로 둔다(`trivialNodeSize?`, Java와 같은 결과).

### 8.2 결과(ELK Java 기준, HX의 Java 기준값 재사용)

| 집합 | 정확 일치(tol 0) 전 → 후 | 1e-6 일치 전 → 후 | 비교 수(둘 다 성공) |
|---|---:|---:|---:|
| v1 | 62 → 183 | 63 → 187 | 566 |
| v2 | 56 → 202 | 57 → 207 | 578 |
| v3 | 57 → 189 | 57 → 192 | 576 |
| v4 | 63 → 213 | 64 → 215 | 581 |
| v5 | 57 → 188 | 57 → 189 | 574 |
| v6 | 68 → 203 | 69 → 207 | 584 |
| v7 | 60 → 212 | 60 → 216 | 574 |
| v8 | 57 → 197 | 58 → 202 | 577 |
| v9 | 65 → 210 | 66 → 211 | 576 |
| v10 | 71 → 198 | 72 → 200 | 575 |
| 합계 | 616 → 1,995 | 623 → 2,026 | 5,761 |

루트 알고리즘별 정확 일치(v 집합): box 0 → 310/574, fixed 51 → 284/532, rectpacking 6 → 324/615, radial 1 → 248/584,
stress 4 → 79/560, layered 554 → 750/1,715, force 0 → 0/614, mrtree 0 → 0/567(8.3절 1번).

- s 집합(Java가 4,783건 거부): 클래스·메시지 일치 74 → 4,777. 나머지 6건은 Java가 노드 크기 검증보다 먼저 자체 결함
  (`CrossingsCounter`의 `ArrayIndexOutOfBoundsException`, 5장)으로 실패하는 입력이다. Java·Lean 둘 다 성공한 s 입력의 정확
  일치는 집합당 34~50 → 79~111(비교 107~137).
- 코퍼스: Java 정확 1878/119(차이 집합 동일), elk-rs model 1447/1447, `lean/**` 1,447개·합성 26개 바이트 동일.

### 8.3 남은 차이(v 집합, 가장 깊은 차이 그래프의 알고리즘별)

1. **알고리즘별 옵션 기본값 미이식**(force 1,019·mrtree 896·stress 658 모델): Java는 `ForceOptions.PADDING = 50`,
   `SPACING_NODE_NODE = 80`, mrtree 패딩 20·간격 20·`spacing.edgeNode` 3 등 알고리즘 메타데이터의 기본값을 쓰는데
   elk-lean(=elk-rs)은 코어 기본값(12/20)을 쓴다. `tests/fixtures/nodemicro/force.json`에 패딩 50·간격 80을 명시하면
   Lean 출력이 Java와 완전히 같다. stress는 비대화형일 때 force를 먼저 돌리므로 같은 원인을 공유한다. Java는 `Cloneable`
   기본값(`ElkPadding` 등)을 읽을 때 요소에 저장하는 부작용도 있다(`EMapPropertyHolderImpl.getProperty`).
2. layered 내부(간선 444·포트 110·노드 위치 63): 예 v1/g0225 — 크기 0×0 노드의 SOUTH 포트 순서.
3. radial 노드 위치(139), mrtree 간선 경로(32): 알고리즘 몫.
4. 노드 마이크로 레이아웃 잔여(10건 미만): 라벨 달린 NORTH/SOUTH 포트를 가진 복합 노드의 둘째 포트 위치(예 v5/g0260
   `n2`만 남긴 그래프: Java 31.7, Lean 30 — 자식을 지우면 일치), 라벨 x의 1e-15 반올림 차이.
5. Java만 던지는 예외: rectpacking `TARGET_WIDTH` 근사의 `A target width has to be set …`(Lean은 레이아웃).

## 10. OPT: Java 옵션 의미론 — 알고리즘별 기본값·열거형 옵션 파서·radial/mrtree/vertiflex 경로 (2026-10-28)

### 10.1 Java 메커니즘

- `.melk`의 `supports X = value`는 생성된 `<Algorithm>Options`에서 `new Property<>(CoreOptions.X, X_DEFAULT)`로
  **같은 id·다른 기본값의 속성 상수**를 재선언한다(값 없는 `supports X`는 `CoreOptions.X` 재노출). 기본값은
  호출 지점의 상수가 정한다: `getProperty(ForceOptions.PADDING)`은 50, 같은 노드의 `getProperty(CoreOptions.PADDING)`은 12.
  `LayoutAlgorithmData.getDefaultValue`(레지스트리의 `addOptionSupport` 기본값)는 레이아웃 경로에서 읽히지 않는다
  (`LayoutConfigurationManager`, UI 전용). 그래서 vertiflex의 `padding = 5`는 메타데이터뿐이고(코드는 `CoreOptions.PADDING`),
  stress의 `edgeLabels.inline = true`도 쓰이지 않는다(`FLabel`은 `ForceOptions`).
- `EMapPropertyHolderImpl`/`MapPropertyHolder.getProperty`는 기본값이 `Cloneable`(`ElkPadding`·`KVector`·`EnumSet`…)이면
  그 복제본을 **요소에 저장**한다. top-down 엔진이 레이아웃 전에 `CoreOptions.PADDING`(12)을 읽으면 자식 알고리즘은
  자기 기본값(예 rectpacking 15) 대신 12를 본다. Lean: `ElkM.getNodePropSticky`(`Elk.Graph.Impl.EMapPropertyHolderImpl`).
- 열거형 옵션은 `LayoutOptionData.parseValue`가 enum 클래스로 파싱한다(`Enum.valueOf`, 아니면 서수). elk-rs는 force·stress·
  mrtree·radial·rectpacking·SPOrE·DisCo·VertiFlex의 열거형 옵션에 파서가 없어 JSON 문자열을 무시했다.

### 10.2 결과(시드 1~10 × 600, s/v/d; 기준 = RJ1+SEC 병합본 `2ad1aa5`, Java 결과는 같은 입력)

| 집합 | 정확 일치 전 → 후 | 1e-6 전 → 후 |
|---|---:|---:|
| s | 963 → 1,082 / 1,205 | 968 → 1,086 |
| v | 2,383 → **4,374** / 5,761 | 2,423 → 4,431 |
| d(기본값 명시) | 2,748 → 4,374 / 5,761 | 2,796 → 4,431 |
| o(새 옵션 집합, 시드 1~3 × 400, SEC 이전 측정) | 146 → 886 / 1,020·1,048 | 156 → 975 |

d 집합이 v와 같아졌다(기본값을 명시해도 결과가 바뀌지 않음 = Lean의 기본값이 Java와 같다). 분류(s+v+d): DEF 1,728 → 465
(mrtree 867 → 371, force 908 → 93, rectpacking 2 → 2), POS 2,653 → 631(stress 1,140 → 177, mrtree 851 → 356, force 452 → 91,
radial 288 → 8), NML 1,308 → 50. 남은 DEF/POS: mrtree는 거의 전부 `AVOID_OVERLAP` 간선 경로(elk-rs의 재구성 라우터),
force/stress는 간선 라벨 위치만. SEC가 지적한 mrtree의 "출발점 아래 3 지점 굽힘"은 `LEVEL_PROC` 이식(`TREE_LEVEL` 계산)으로
Java와 같아졌다. 코퍼스 Java parity 1878/119(집합·차이 동일), elk-rs model parity 1447/1447.
## 11. LNODE: layered 노드 크기·포트·라벨과 임포터 간선 선택의 Java 경로 (2026-10-28)

방법: 기준 바이너리(병합본 `7310832`)로 파이프라인(seed 1~10, s/v/d) → `LNODE`/`LSIZE` 입력 137개(s+v)를 Java
단계별 trace(`ElkJavaBaseline --trace true`)와 Lean trace로 비교해 처음 갈라지는 프로세서를 모은 뒤, 프로세서별로
Java와 다르게 이식된 지점을 고쳤다(처음 갈라짐: `SelfLoopPortRestorer` 64, `HierarchicalPortOrthogonalEdgeRouter` 12,
`PortListSorter` 6, 나머지는 비layered 자식의 크기(DEF/NML)·P3·P5 f32 등 다른 클래스).

### 10.1 변경(전부 ELK Java가 기준, elk-rs와는 달라짐)

- `SelfLoopPortRestorer`: 한 변 self loop의 포트를 Java `SelfLoopPort.getSLNetFlow()`(self loop 간선 in − out)로
  정렬한다. elk-rs는 `LPort.getNetFlow()`를 쓰는데 `SelfLoopPreProcessor`가 self loop를 떼어낸 뒤라 순수 self loop
  포트는 전부 0이 되어 정렬이 일어나지 않았다(예 `v1/g0225` 0×0 노드의 SOUTH 포트 순서) — LNODE의 절반.
- `HierarchicalPortOrthogonalEdgeRouter.restoreDummy`: 되돌린 북/남 외부 포트 더미의 여백을 Java처럼 그 더미에서
  계산한다(`getNodeMarginCalculator(adapt(graph)).processNode(adapt(dummy))`). elk-rs는 층 노드 스냅샷에서 더미를
  찾다 못 찾아 여백 0 — `assignAscendingCoordinates`가 라벨 폭만큼 더미를 밀지 않았다(예 `v6/g0330`).
- `PortListSorter`: `Collections.sort`를 JDK 21 `TimSort`(`javaSortBy`)로. `FIXED_ORDER`에서 일부 포트만
  `PORT_INDEX`를 가지면 `CMP_COMBINED`가 일관 순서가 아니어서 결과가 비교 순서에 달려 있다(예 `v8/g0080`). 위치는
  `Double.compare`, 인덱스는 Java `int` 뺄셈, `UNDEFINED` 변은 Java처럼 `IllegalStateException: Port side is undefined`.
- `LabelAndNodeSizeProcessor`: Java의 `calculateLabelAndNodeSizes`(노드마다 셀 시스템 `process`)만 돈다. elk-rs의
  `needsProcessNodeForFixedPortLabels` 사전 패스(고정 크기·고정 포트 라벨의 복합 노드에 단순화 `processNode`로 크기를
  키움)는 Java에 없다.
- 셀 시스템 `FIXED_RATIO`: `PortContext.portRatioOrPosition`을 포트의 `PORT_RATIO_OR_POSITION`에서 읽는다
  (`GraphAdapters.portRatioOrPosition`; layered `LPort`는 `initializePort`가 저장한 비율, `ElkPort`는 0). elk-rs는
  항상 0이라 layered의 `FIXED_RATIO` 포트가 변의 시작에 몰렸다. 무작위 입력은 포트 좌표가 없어 비율이 0이므로
  영향이 없고, 픽스처 `fixed_ratio_ports`로 고정했다.
- `ElkGraphImporter.calculateMinimumGraphSize`: 라벨 셀을 부모 ElkNode의 `DIRECTION`(있을 때, Java `process`가
  `graph.hasProperty(DIRECTION)`일 때만 읽음)으로 배치, 고정 포트 라벨이어도 계산(elk-rs의 조기 반환 없음), 그리고
  Java `copyProperties`의 값 공유 — `MINIMUM_SIZE`가 더해진 `EnumSet`과 최솟값 `KVector`는 ElkNode가 명시한 값
  그 자체라 ElkNode에 다시 쓴다(부모 실행이나 `INCLUDE_CHILDREN`의 복합 `LNode`가 그 값을 본다, 예 `v8/g0359`·`v8/g0219`).
- 임포터 간선 선택(코디네이터 추가 요청, SEC 발견): 평면 임포트(`importFlatGraphEdgesJava`)는 Java처럼 자식끼리 또는
  자식과 그래프를 잇는 간선만 변환하고, 자식의 자식으로 가는 간선은 어느 실행에도 속하지 않은 채 오류 없이 남긴다
  (elk-rs: `UnsupportedGraphException ... could not be found in the current layout scope`). 끝 노드의 `NO_LAYOUT`은
  보지 않으므로 `NO_LAYOUT` 형제로 가는 간선은 Java처럼 `transformEdge`에서 실패하고, 문구는 Java 그대로(EMF
  `toString`: `ElkEdge "e0" ElkNode "x" (0.0,0.0 | 30.0,30.0) -> …`, Java `Double.toString` = 새 `Float.toJavaString`).
  하이퍼엣지는 평면 임포트에서 `IllegalArgumentException: Passed edge is not 'simple'.`, 계층 임포트·`transformEdge`에서
  `checkEdgeValidity`의 `UnsupportedGraphException`. 코퍼스 `tickets/layered/588_hierarchicalLayoutNPE`(양쪽 예외)의
  오류 문구가 이제 Java와 글자까지 같다.

### 10.2 결과

SEC 병합본(`2ad1aa5`) 기준, 전 = 그 바이너리, 후 = SEC 병합 후의 LNODE:

| 집합 | 정확 일치 전 → 후 | LNODE 전 → 후 | LSIZE 전 → 후 | 루트 layered 정확 전 → 후 |
|---|---:|---:|---:|---:|
| s | 963 → 975 / 1,205 | 14 → 1 | 2 → 0 | 471 → 477 / 547 |
| v | 2,383 → 2,423 / 5,761 | 133 → 18 | 2 → 0 | 981 → 999 / 1,715 |
| d | 2,748 → 2,796 / 5,761 | 134 → 18 | 2 → 0 | 1,060 → 1,079 / 1,715 |

(SEC 이전 `7310832` 위에서: v 1,995 → 2,026, LNODE v 121 → 15 — SEC가 같은 단위의 간선 섹션 차이를 없애자 LNODE로 드러난
입력 3개가 더해졌다: `v5/g0246`·`v4/g0522`는 P4 `NetworkSimplexPlacer`/`BKNodePlacer`가 처음 갈라지고, `v2/g0273`은 force
자식 크기.) layered만 쓰는 입력(분류기 기준 1,999개)의 불일치 266 → 244. 코퍼스: Java 정확 1878/119(차이 집합·레이아웃 바이트 동일),
ticket 588 오류 문구 Java와 동일. 테스트: `tests/lean/Tests/Api/LayeredNodeJava.lean`(+ `tests/fixtures/lnode/` 12개 입력,
10개 Java 출력), `Tests/Layered/Import.lean`의 elk-rs 기대값(범위 밖 간선 예외, `NO_LAYOUT` 끝 건너뛰기)을 Java로 교체.

### 10.3 남은 LNODE(v 18) — 이 클래스 밖의 원인

- Java 실행 맥락 의존(코퍼스 119개와 같은 종류): `v3/g0291`, `v5/g0480`, `v9/g0359` — 새 JVM 하나에서 돌린 Java 출력은
  Lean과 같거나(g0291) f32 굽은 점만 다르다. 같은 입력이 JVM 안의 앞선 작업(TestController 유무 등)에 따라 높이가
  10씩 달라진다.
- P3 포트/노드 순서(`LayerSweepCrossingMinimizer` — `v7/g0445` FIXED_SIDE 노드의 EAST 포트 순서, `v3/g0150`,
  `v4/g0300`, `v7/g0258`; `InteractiveCrossingMinimizer`): 교차 최소화의 포트 분배·노드 순서.
- self loop 경로(`SelfLoopRouter`의 경로 방향·여백, LPOS에도 11개: 예 `d6/g0282`는 Java가 서쪽으로 돌고 Lean은 동쪽,
  `d1/g0052` 여백 38.6 vs 51.9), self loop 라벨(`SelfLoopPostProcessor`, `v4/g0515`), `LabelSideSelector`(`v5/g0151`),
  P4 `NetworkSimplexPlacer`(`v7/g0511`)·`BKNodePlacer` 1e-14, P5 f32 굽은 점 — 간선 경로 클래스(LEDGE).
- 비layered 자식의 크기(DEF·NML)가 부모 layered 실행으로 번진 것(`v10/g0216`·`v10/g0534`·`v2/g0186` 등).

## 12. FEL: force/stress의 반복 간선·라벨(Java 객체 동일성)과 Eades 모델 (2026-10-29)

### 12.1 원인과 변경(전부 ELK Java가 기준, elk-rs와는 달라짐)

- **반복 간선**: `ComponentsProcessor.dfs`는 `last`에서 온 간선만 건너뛰므로 사이클을 닫는 간선이 컴포넌트의 간선 목록에
  두 번 들어가고, 그 라벨도 `getLabels().addAll`로 두 번 들어간다. Java에서는 **같은 객체**가 두 번 나열된다. elk-rs(그리고
  이전 Lean)는 두 개의 독립 복사본을 만들었다. Java 결과에 미치는 영향:
  - force: 라벨 입자가 `getParticles()`에 두 번 → 다른 입자에 두 번 힘을 주고, 자기 변위는 두 번 누적된 뒤 첫 항목에서 한 번
    이동(둘째 항목은 0 벡터를 더함). 복사본 두 개는 서로 같은 위치에서 `avoidSamePosition`으로 흔들려 난수열까지 달라졌다
    (예: `s1/g0392` 라벨 x 0.05 차이, `v2/g0075` 노드 1 ulp).
  - `REPULSIVE_POWER`: `initialize`가 간선 목록을 돌며 굽은 점을 만들므로 반복 간선은 굽은 점이 두 배(한 간선에 고르게 분배).
  - `recombine.moveGraph`: 간선 목록 항목마다 그 간선의 굽은 점을, 라벨 목록 항목마다 라벨을 옮기므로 반복 라벨·굽은 점은
    **두 번 이동**한다(여러 컴포넌트일 때 라벨이 크게 어긋나던 force/stress 차이의 대부분, 예 `v1/g0292` 1458 vs 2794).
    또 굽은 점은 결과 그래프의 굽은 점 목록에 추가되지 않아 `applyLayout`의 경계 상자에서 빠진다.
  - Lean: `buildComponent`/`moveGraph`는 복사본 하나를 두고 id를 반복(`edges`·`labels`), `ParticleIdentity`(첫 항목·그룹)로
    FR 평면 루프와 일반 루프가 Java의 객체 의미(자기 자신의 다른 항목 건너뛰기, 변위는 첫 항목에 누적, 이동 후 위치 공유)를 따른다.
- **Eades 모델**(`elk.force.model = EADES`): Java `calcDisplacement`는 매 쌍마다 `avoidSamePosition`을 부른다(elk-rs는 생략 —
  같은 위치의 입자는 힘이 없고 난수도 안 씀). 일반 `layout`을 Java 순서로 이식(같은 위치일 때만 모나드 분리, 나머지는 순수 스캔).
  `Math.log`는 기준 JVM(aarch64 HotSpot)에서 `StrictMath.log`(fdlibm)와 같고 C 라이브러리 `log`와는 약 1%의 인자에서 1 ulp
  다르다 → `Elk.Core.Util.Java.javaLog`(fdlibm `__ieee754_log` 이식, Java 값 200,000개 전부 일치).
- `avoidSamePosition`: Java 루프 조건 `pu.x - pv.x == 0 && ...`, 길이 0 간선의 직교 벡터는 NaN(elk-rs는 무한 루프).
- 남긴 편차(퇴화 좌표만, FR 내부 루프에서 Java 형태가 약 10% 느려 유지): 거리가 0으로 언더플로하는 쌍, NaN 거리의 `Math.max`,
  무한 좌표의 같은 위치 검사(분리 직전에 Java 조건으로 다시 검사).

### 12.2 결과(R6 병합본 `23059ea`의 Java 기준값 재사용)

| 집합 | 정확 일치 전 → 후 | force/stress 클래스 전 → 후 |
|---|---:|---|
| s(시드 1~10) | 1,177 → 1,180 / 1,205 | DEF:force 2 → 0, POS:stress 1 → 0 |
| v(시드 1~10) | 5,090 → **5,287** / 5,761 | DEF:force 100 → 0, POS:stress 100 → 0, NML:force/stress 2 → 0 |
| d(시드 1~10) | 5,090 → 5,287 / 5,761 | POS:force 101 → 0, POS:stress 100 → 0, NML 2 → 0 |
| o(시드 1~3 × 400) | 886 → 899 / 1,048 | force/stress의 1e-6 일치 13 → 정확 일치 13(Eades `log`) |

정확 → 비정확 0, 바뀐 Lean 출력 212(v/s)·13(o)는 전부 force/stress를 쓰는 입력이고 그중 force/stress 단위는 모두 Java와 같다
(12개는 다른 알고리즘의 기존 차이 — mrtree 경로·layered·rectpacking — 가 남음). 코퍼스 Lean 출력 1,447개·합성 26개 바이트
동일, Java 코퍼스 1878/119(집합 동일), elk-rs model 1447/1447. 테스트: `force.fixtures.java`(+ `tests/fixtures/force/java/`
입력 10개와 Java 출력), `force.import`의 반복 간선 검사, `core.util.java`의 `javaLog`(Java 값 48개 + 특수값); force/force_enum
기대값 12개를 Java와 정확히 같은 값으로 재고정(`opt_java_status.tsv`의 java_differs 3·java_equal 7 → java_exact).

## 13. P3J: layered 교차 최소화(P3)와 그 앞 프로세서의 Java 경로 (2026-10-29)

방법: 라운드 6 병합본(`0fe9df9`)으로 파이프라인(시드 1~10, s/v)을 돌려 layered 단위가 다른 입력 70개(LPOS/LNODE/LEDGE)를
Java·Lean 단계별 trace로 비교했다(처음 갈라짐: `LayerSweepCrossingMinimizer` 11, 나머지 57은 전 단계 일치). 무작위 생성기가
교차 최소화 옵션을 거의 쓰지 않으므로(전략 3종만), v 세트의 layered 루트 그래프 1,802개에 P3 옵션(전략 4종, greedy switch
종류·문턱, model order 전략·영향도·`portModelOrder`, `forceNodeModelOrder`, thoroughness, 시드, semi-interactive, node
promotion, interactive 기준점, interactive일 때 노드 위치와 굽은 점 있는 section)을 무작위로 준 변형 세트(`p3a`)를 만들어
같은 방식으로 분석했다. Java 내부 확인은 스크래치의 그림자 클래스(서명 제거한 layered jar 사본 + 계측한
`LayerSweepCrossingMinimizer`/`BarycenterHeuristic`/`GreedyPortDistributor`/`SwitchDecider`/`CrossingsCounter`, 추적
`Random`)로 했고, 결과 기준값은 항상 수정하지 않은 Java(`ElkJavaBaseline`)다.

### 13.1 변경(전부 ELK Java가 기준, elk-rs와는 달라짐)

- `BarycenterHeuristic.calculateBarycenter`(스냅숏 경로): 노드의 **현재** 포트 순서(`node.getPorts()`, 포트 분배기가 바꾼
  순서)를 돈다. elk-rs는 스냅숏을 만들 때의 순서를 돌아서, 같은 층 이웃으로의 재귀 순서 — 곧 어느 노드가 어느 섭동 난수를
  받는지 — 와 순위 합의 순서가 Java와 달랐다(`s5/g0032`·`s5/g0255`·`v3/g0150`·`v4/g0300`·`v7/g0258`·`v7/g0445` 등 8개).
- `GreedyPortDistributor.switchPorts`: Java는 `getPortSideView`(남/서는 `Lists.reverse`) 하위 목록에 쓰므로 교환은 두 **보기
  위치**가 가리키는 노드 목록 칸을 바꾼다. elk-rs는 칸 인덱스도 함께 바꿔, 두 번 움직인 포트의 다음 교환이 엉뚱한 칸을
  바꿨다(`v5/g0228`·`v4/g0293`·`v9/g0020`; ELK Java 자체 테스트 `GreedyPortDistributorTest.
  distributePorts_GivenMultipleCrossingsOnWesternSide_RemoveCrossing`의 기대값 `[1, 2, 0]`과도 이제 일치 — elk-rs 기대값은 `[2, 0, 1]`).
- `LayerSweepCrossingMinimizer`: `FIRST_TRY_WITH_INITIAL_ORDER`와 `SECOND_TRY_WITH_INITIAL_ORDER`는 **같은 속성 id**
  (`"firstTryWithInitialOrder"`)로 선언되어 한 값이다 → 무작위 반복의 첫 번째만 초기 순서를 쓴다(elk-rs는 두 번째도). 또 이
  값은 `LGraph`에 남아, 초기 순서의 교차가 0이라 일찍 끝난 실행이 `true`로 남긴 값을 같은 그래프의 다음 실행(예: greedy
  switch 처리기)이 읽는다.
- greedy switch: `SwitchDecider`의 두 층 내 계수기는 heuristic의 포트 위치 배열 **하나**를 공유하고(다른 층·다른 쪽 위치가
  남음), 부모 계수기는 부모 `GraphInfoHolder`의 배열을 공유한다(elk-rs: 계수기마다 복사본). `CrossingsCounter`의
  `connected…PortsSortedByPosition`은 Java `TreeSet`처럼 **위치가 같은** 포트를 버린다(elk-rs: 동일성). 남은 위치가 트리를
  넘으면 Java는 `BinaryIndexedTree`에서 `ArrayIndexOutOfBoundsException`을 던진다 — 트리가 범위 밖 `add`/`removeAll`을
  표시하면(범위 밖 `rank` 뒤에는 늘 같은 `add`가 옴) 두 순서 계수가 Java의 접근 순서로 첫 실패 지점을 다시 찾아 같은 문구로
  던진다(전에는 잘린 값으로 계속 세다가 greedy switch 루프가 끝나지 않았다; 추가 패스가 없어 비용 ≈ 0).
- `InteractiveCrossingMinimizer`: 긴 간선 더미는 `ORIGIN` 간선의 `ORIGINAL_BENDPOINTS`(importer가 interactive 전략일 때
  section의 시작점·굽은 점·끝점으로 설정 — 새 내부 속성)를 따라 보간하고, 뒤집히지 않은 간선은 Java처럼 그 사슬 객체를
  제자리에서 늘린다(분할된 긴 간선 조각들이 같은 객체를 공유); x 거리 0 보호 없음(NaN/∞는 `Double.compare`로), 정렬은 TimSort.
- `MedianHeuristic`: `weightComparator`(가중치 없는 첫 노드는 항상 큼 — 비일관)와 TimSort, `Double.MIN_VALUE`,
  `Math.min/max`, 중앙값 노드에 가중치가 없으면 Java의 NPE 문구. `ModelOrderBarycenterHeuristic.setFirstLayerOrder`는
  Java의 가상 호출대로 첫 층을 model order 삽입 정렬(제약 해소 없음). 무게중심·포트 무게중심 비교는 `Double.compareTo`/
  `Float.compare`(NaN·`-0.0`).
- `SweepCopy`: 재정렬은 `Collections.sort(ports, PortListSorter.CMP_COMBINED)`(TimSort + `PortListSorter` 비교자),
  `FIXED_POS` 원점도 변 교정(elk-rs는 건너뜀).
- `SortByInputModelProcessor`: 포트는 노드마다 새 `ModelOrderPortComparator`로 `Collections.sort`(TimSort; 상태 있는
  비교자라 비교 순서가 결과를 정함 — elk-rs는 삽입 정렬). 비교자는 만들 때 앞 층을 복사하므로 층 0의 포트 비교자와 두 번째
  노드 비교자는 첫 정렬 **뒤**의 층 0을 본다.
- `NorthSouthPortPreprocessor`: `sortPortList`는 고정 변의 normal 노드에서만(elk-rs는 모든 노드, 자유 노드의 섞인 포트도
  재정렬). `modelOrderNorthSouthInputReversing`은 Java가 실제로 계산하는 값 — `Lists.reverse(incoming).addAll(outgoing)`은
  뒤집힌 보기 끝, 곧 원 목록 **앞**에 넣으므로 결과는 들어오는 간선 없는 포트를 거꾸로, 그다음 들어오는 포트를 원래 순서로.
- `NodePromotion`(model order): Java 루프 그대로 — 승격 뒤 같은 인덱스를 다시 보고, 층 경계는 매번 `keySet().size()`,
  최대/최소 키는 동적, 1층 그래프도 정렬·재구성, 층 정렬은 TimSort(`int` 뺄셈), 키 비교는 Java `Integer ==`(캐시 범위 밖은
  상자 동일성), 간선 없는 경우의 `NoSuchElementException`. elk-rs 방식은 `p3a`에서 103개 입력이 끝나지 않았다.
- `ElkGraphImporter.transformEdge`: 고정 변 노드에 바로 붙은 간선 끝의 포트는 첫 section의 시작/끝점에서 만든다(절대 좌표
  → `elkparent` 기준, 자손으로 가는 간선은 source를 INPUT으로 노드 위치만큼 이동) — 변이 그 점으로 정해진다.
- `LGraphToCGraphTransformer`: `VerticalSegment.compareTo`는 Guava `DoubleMath.fuzzyCompare` + `Double.compare`(비이행),
  정렬은 TimSort.

`rustSortBy` → `javaSortBy`: `NodePromotion`, `InteractiveCrossingMinimizer`(이제 layered에 `rustSortBy` 없음). 그 밖의
TimSort 전환: `MedianHeuristic`, `SweepCopy`, `SortByInputModelProcessor` 포트, `LGraphToCGraphTransformer`.
`HyperedgeCrossingsCounter`의 마지막 키는 Java에서 `hashCode()`(identity hash, `this.hashCode() - other.hashCode()` 넘침
포함)라 재현할 수 없다 — Lean은 첫 source 포트의 arena 인덱스(elk-rs: 주소)를 쓴다.

### 13.2 결과

| 측정 | 전 | 후 |
|---|---:|---:|
| 무작위 v 정확(시드 1~10, origin/main `63797fa` 기준) | 5,287 / 5,761 | **5,297** |
| 무작위 s 정확 | 1,180 / 1,205 | 1,182 |
| 루트 layered v / s | 1,629 / 1,715 · 542 / 547 | 1,634 · 544 |
| `p3a`(P3 옵션 변형 1,802개, 라운드 6 병합본 기준) 정확 | 904 | 1,302(병합 후; 병합 전 1,281) |
| `p3a` drift / Lean 시간 초과 | 369 / 103 | 74 / 0 |

정확 → 비정확 0. 무작위 s/v에서 바뀐 12개는 모두 drift → 정확이고, P3에서 처음 갈라지던 입력이 0개가 됐다. 남은 layered
차이 58개(LPOS 46·LEDGE 8·LNODE 3 등)는 모두 단계별 trace가 Java와 같고, 그 입력 70개만 새 JVM에서 돌린 Java와는 65개가
정확히 같다(파이프라인의 600개 단위 JVM 실행 맥락 의존 — LEDGE가 본 것과 같은 종류). 새 JVM에서도 다른 5개: `v3/g0156`(P4
`LinearSegmentsNodePlacer`), `v8/g0471`·`v9/g0173`(trace는 같고 최종 간선 경로), `v5/g0424`·`v10/g0216`(mrtree 자식).
`p3a`의 남은 차이: Java 자신의 결함(NPE `MAX_MODEL_ORDER_NODES` 언박싱 15, `CrossingsCounter` AIOOBE의 다른 지점 등 Java만
실패 39 — 재현하지 않음), 오류 문구만 다른 11(그중 9는 HotSpot `OmitStackTraceInFastThrow`가 같은 JVM에서 반복된 AIOOBE의
문구를 지운 것, 2는 다른 지점), self-loop 라우팅·P4/P5 등 P3 밖.

코퍼스: Lean 출력 1,447개 바이트 동일(`lean/**`; 병합 후 origin/main과도 동일), elk-rs model 1447/1447·strict trace
1447/1447이며 Lean trace 파일도 전부 바이트 동일(oracle 특이점 없음 — 코퍼스는 바뀐 경로가 결과를 바꾸지 않음), Java 정확
1878/119(집합 동일), Java 단계별 trace 1,743/1,997(LEDGE의 새 Java 실행 기준값, 전후 동일 — layered 강제 trace 파일 바이트
동일), 합성 26개 바이트 동일·Java 23/26. 성능(origin/main 대비, 교차 6회 중앙값): 합성 layered 4종 합 1.007배(crossmin
0.996·hierarchy_flat 1.006·layered_large 1.010·layered_medium 1.005), P3L 코퍼스 부분집합 30개 합 1.005배(모델별 0.996~1.017;
스냅숏 경로가 현재 포트 순서를 읽는 비용). 남은 `p3a` 오류 문구 차이 중 2건은 Java가 `AllCrossingsCounter`의 층 내 계수
(스냅숏 경로, 검사 없음)에서 먼저 던지는 AIOOBE다(같은 예외 클래스, 다른 인덱스). 테스트 `layered.p3Java`(+
`tests/fixtures/p3java/` 입력 12개, Java 출력 11개, Java 예외 문구 1개); elk-rs 기대값을 Java로 바꾼 검사: greedy 포트 분배
`[2,0,1]` → `[1,2,0]`(Java 자체 테스트), interactive의 x 거리 0(`9` → NaN)·NaN 비교(`eq` → `gt`), median의
`f64::MIN_POSITIVE` → `Double.MIN_VALUE`·정렬 함수, `SweepCopy`의 `FIXED_POS` 변 교정(안 함 → 함), node promotion 1층 정렬
(안 함 → 함).

## 14. NIK: node promotion(Nikolov 전략)·`ModelOrderBarycenterHeuristic`·Coffman–Graham의 Java 경로 (2026-10-29)

방법: elk-lean이 아직 elk-rs 의미론을 따르던 layered 지점을 Java 0.12.0 소스대로 옮기고, 처리기 단위로는 수정하지 않은
Java 클래스를 직접 호출하는 하네스(같은 `LGraph`를 만들어 `new NodePromotion().process(..)`, `new CoffmanGrahamLayerer()
.process(..)`, 리플렉션으로 private `updateBiggerAndSmallerAssociations`)와 차분 비교했다. 무작위 생성기(s/v/d)는 node
promotion·layering 전략·group model order를 쓰지 않으므로, v 집합의 layered 루트 그래프 1,802개에 옵션을 준 변형 세트
4개로 전체 레이아웃을 Java(`ElkJavaBaseline`, 600개 단위가 아닌 1,802개 한 JVM)와 비교했다: `npa`(node promotion 9전략·
`maxIterations`·layering 전략·간격, 30%는 `forceNodeModelOrder`와 group model order — 하위 알고리즘은 원본 그대로),
`npb`(같은 생성기, 모든 compound 노드를 layered로), `mob`(루트에 `forceNodeModelOrder`·`cmGroupOrderStrategy`, 자식에
crossing minimisation group id 0~300만), P3J의 `p3a`.

### 14.1 변경(전부 ELK Java가 기준, elk-rs와는 달라짐)

- `NodePromotion`의 Nikolov 계열(`NIKOLOV`, `NIKOLOV_PIXEL`, `NIKOLOV_IMPROVED(_PIXEL)`, `DUMMYNODE_PERCENTAGE`,
  `NODECOUNT_PERCENTAGE`, `NO_BOUNDARY`·기본 분기): elk-rs는 아무것도 하지 않았다(I7의 "oracle 특이점"). Java의
  `precalculateAndSetInformation`(역순 layer id, node id, 차수, 폭 추정: `int` 노드+더미 수, `double` 픽셀 폭 =
  `size.y + spacing.nodeNode`, 더미 `spacing.edgeNodeBetweenLayers`, `Math.max`), `promotionMagic`, 재귀 `promoteNode`
  (`layers[node]`는 재귀 뒤에 기록 — 두 경로로 닿는 선행 노드는 두 번 승격될 수 있음), 전략 분기, `setNewLayering`(새 layer
  `maxHeight + 1`개, id `maxHeight - i`, 빈 layer 제거)을 줄 단위로 옮겼다. Java의 부기 결함도 그대로: `currentWidthBackup =
  currentWidth`가 **같은 리스트**라 첫 채택·복원 전까지 "백업"이 함께 바뀌어 첫 복원은 기각된 승격의 폭을 남기고(리스트가
  `maxHeight`보다 길어질 수 있고 이후 `get(nodeLayerPos)`는 그 낡은 칸을 읽음), 채택 시 `dummyBackup = dummyNodeCount +
  promotionPair.getFirst()`(차이를 두 번 뺌)와 `reducedDummies += dummyBackup - dummyNodeCount`. 백분율 전략은
  `(int) Math.ceil(n * promoteUntil / 100.0)`(`int` 곱), IMPROVED는 `NO_BOUNDARY` 실행 뒤 폭 리스트 전체의 최댓값이 처음
  최댓값을 넘으면 `NIKOLOV(_PIXEL)`로 한 번 더. 처리기 차분: 무작위 layered 그래프 5,500개(10전략, `maxIterations`, 간격,
  label 더미·model order 포함)에서 레이어링·예외(`NoSuchElementException`) 전부 Java와 같다.
- `NodePromotion`(model order): Java가 남기는 `layer.id`(새 layer의 id = **키**, 빈 키는 건너뜀)와 `node.id`를 설정한다.
  `SortByInputModelProcessor`의 `ModelOrderNodeComparator`/`ModelOrderPortComparator`가 아직 번호를 다시 매기지 않은 뒤
  layer의 id를 비교하므로 관찰된다(`p3a/v2_g0201`, `npa/v9_g0207`).
- `ModelOrderBarycenterHeuristic`: (1) `CMGroupModelOrderCalculator`의 group order 옵션과 offset(`MAX_MODEL_ORDER_NODES`)을
  `n1.getGraph()`에서 읽는다 — elk-rs는 처리 중인 그래프를 잠근 채 `try_lock`이 실패해 기본값을 써서 루트의 `ENFORCED`가
  무시됐다(`LayerSweepCrossingMinimizer`의 model order 계수도 같은 수정). (2) `ONLY_WITHIN_GROUP`의
  `n1.getProperty(ID) != n2.getProperty(ID)`는 `Integer` 동일성 — 캐시 `[-128, 127]` 밖의 같은 id는 다른 그룹. (3) 관계
  집합: Java는 살아 있는 `HashSet`을 돌며 고치고 elk-rs는 두 집합을 먼저 복사하지만, 루프 중에 커지는 집합은 그 루프가 어차피
  더하는 원소만 얻으므로 결과는 같다(순환·자기 관계를 포함한 임의 상태 3,000개를 리플렉션으로 Java 메서드와 비교해 전부 일치;
  `insertionSort` 한 번 안에서는 관계가 항상 추이 폐포라 순환 자체가 생기지 않는다). Lean은 Java 순서대로 다시 썼다.
  `CMGroupModelOrderCalculator`의 group 값은 `int` 산술(`Int.wrap32`).
- `CoffmanGrahamLayerer`(P2): 두 우선순위 큐를 `java.util.PriorityQueue` 이진 힙(JDK 21 `siftUp`/`siftDown`)으로,
  `compareNodesInTopo`를 Java 비교자로 — `Integer !=`(캐시 밖 같은 값은 `Integer.compare` = 0), 한쪽 목록이 비면 node id,
  둘 다 비지 않고 끝까지 같으면 `1`. 일관된 순서가 아니어서 힙 구조가 결과를 정한다(elk-rs: 리스트의 첫 최솟값
  `pop_best_by`, 값 비교, id 대체). node promotion이 Coffman–Graham 레이어링에서 출발할 때 차이가 드러났다(`npa/v8_g0337`:
  기존 Lean의 CG 결과가 우연히 Java의 CG + 승격 결과와 같아 일치했다). 처리기 차분: 무작위 DAG 3,000개(454개는 노드 128개
  초과) 전부 Java와 같다.

### 14.2 결과

| 측정(정확 일치, tol 0) | 전(`757c7c0`) | 후 |
|---|---:|---:|
| `npa` node promotion 변형(1,802개, 양쪽 성공 1,378) | 1,144 | **1,266** |
| `npb` 같은 변형, 전부 layered(양쪽 성공 1,151) | 937 | **1,142** |
| `mob` model order barycenter 변형(양쪽 성공 1,715) | 1,602 | **1,634** |
| `p3a` P3 옵션 변형(양쪽 성공 1,415) | 1,302 | 1,303 |

네 세트 모두 정확 → 비정확 0. 단계별로는 Nikolov+MOBH 이식 +179(`npb`)·+112(`npa`: +113, `v8_g0337` −1은 Coffman–Graham
이식 뒤 복구), Coffman–Graham +26·+9, model order layer id +1(`npa`)·+1(`p3a`); `mob`의 +32는 MOBH 수정만의 몫이다. 남은 차이: `npb` 9개 — 6개는 새 JVM의 Java와 정확히 같음(실행 맥락 의존), 2개는
모든 단계 trace가 같고 최종 간선 section만 다름, 1개 `SortByInputModelProcessor` 포트 순서; `npa` 57개 중 55개는 hierarchy에
layered가 아닌 알고리즘이 있고(node promotion 옵션을 지워도 56개가 그대로 다름 — 다른 원인), 2개 `SelfLoopRouter`, 1개
`SortByInputModelProcessor`(`ModelOrderPortComparator`가 아직 elk-rs를 따르는 지점: 네 번째 추이 검사, 앞 layer 검사의 조기
반환 등). Java만 실패하는 입력은 재현하지 않았다: 중첩 그래프의 `MAX_MODEL_ORDER_NODES`가 `null`이라 나는 언박싱 NPE
(MOBH·`SortByInputModelProcessor`·model order cycle breaker), `CrossingsCounter`/`BinaryIndexedTree`의 AIOOBE.

코퍼스에는 node promotion·`COFFMAN_GRAHAM`·group model order를 쓰는 모델이 없다(`forceNodeModelOrder`는 1개, group 옵션
없음). Lean 출력 1,998개 바이트 동일, Java 정확 1878/119(집합 동일), Java 단계별 trace 1,743/1,997(P3J와 같음), 합성 26개
바이트 동일, 무작위 s/v 세트 결과 불변. 테스트 `layered.nodePromotion.java`(처리기 424), `layered.nodePromotion.layouts`
(fixture 12), `layered.modelOrderBarycenter.relations`(400), `layered.p2layers.coffmanGraham.java`(520) —
`tests/fixtures/promotion/`; elk-rs 기대값을 Java로 바꾼 검사: Nikolov no-op(→ 승격), 잠긴 그래프의 group order(→ 그래프 값),
Coffman–Graham star의 힙 순서(`[[0],[2,1],[4,3]]` → `[[0],[3,1],[4,2]]`)와 `compareNodesInTopo`.

## 15. RJ3: mrtree·radial·layered P4의 Java 경로와 옵션 세트의 파이프라인 편입 (2026-10-29)

방법: 라운드 7 병합본(`757c7c0`, `elk_base`)으로 파이프라인을 `--sets s,v,d,o,p`(시드 1~10)로 돌리고(s·v의 Java 결과는
라운드 6 기준값 재사용, d·o·p는 새로 실행), 차이 입력을 Java 소스·단계별 trace·새 JVM 단일 실행으로 확인했다. Java 내부
확인은 스크래치의 그림자 클래스(서명 제거한 ELK jar 사본 + 수정한 `RadialUtil`/`SelfHyperLoop`, 결과 기준값에는 쓰지
않음)와 스택 트레이스 하네스로 했다. 결과 기준값은 항상 수정하지 않은 Java(`ElkJavaBaseline`)다.

### 15.1 파이프라인: `o`·`p` 세트

- `p`(`scripts/gen_p3_graphs.py`, P3J의 `gen_p3.py`): 시드 `k`의 `v<k>`에서 layered 루트 그래프만 골라 교차 최소화·
  layering 옵션(전략 4종, greedy switch 종류·문턱, model order 전략·영향도·`portModelOrder`, `forceNodeModelOrder`,
  thoroughness, 난수 시드, semi-interactive, 포트 정렬, node promotion, interactive 기준점, interactive일 때 노드 위치와
  굽은 점 section)을 준 사본(시드 1~10 합계 1,802개; 생성 완료 표시 `gen/.p<k>.done`). `o`(`gen_option_graphs.py`,
  OPT)는 이미 세트 종류였고, 두 세트 모두 추적 보고서에 들어간다. 기본 `--sets s,v`는 그대로(빠른 확인용), 추적
  보고서 `tests/random_parity/report.md`는 `--sets s,v,d,o,p` 전체 실행에서 게시한다(`TESTING.md` 2B).
- elk-lean이 Java의 끝나지 않는 재귀를 감지해 던지는 `java.lang.StackOverflowError`(15.2)는 Java의 스택 넘침과 같은
  `overflow` 결과로 센다(`random_java_parity.py`).

### 15.2 mrtree (전부 ELK Java가 기준, elk-rs와는 달라짐)

- `EdgeRouter`(`AVOID_OVERLAP`): `TreeUtil.getAllOutgoingEdges`/`getAllIncomingEdges`는 노드 **`id`**가 같은 끝점의 간선을
  모으고(노드 동일성이 아님), 두 끝의 `TREE_LEVEL` `Integer`를 `!=`(참조 비교 — 캐시 범위 `-128..127` 밖에서는 같은 값도
  다름)로 비교하며, 이미 담은 간선과 **`toString()`(`n_<라벨 또는 id>->n_<라벨 또는 id>`)이 같은 간선은 버린다** — 평행
  간선(같은 두 노드 사이의 둘째 간선, 포트 간선 포함)과 첫 라벨 글자가 같은 노드 사이의 간선은 시작/끝 점을 받지 못해
  가운데-가운데 대체 경로가 된다(무작위 mrtree 차이의 대부분, 예 `v6/g0266`). 목록은 다른 끝의 **x**로 먼저 정렬한 뒤
  라우터가 첫/끝 점으로 다시 정렬한다(안정 `List.sort`, `Double.compare`). 여러 층을 건너는 간선의 "불필요한 층 옆 굽은 점
  건너뛰기" 판정은 간선의 **현재 마지막 굽은 점**(시작 굽은 점이나 앞 틈새의 둘째 굽은 점; elk-rs는 출발 노드 위치와
  `(0,0)` 자리표시자)을 쓰고, 수평 판정의 `start.y < first.x`는 Java 오타 그대로다. 층의 노드는 노드 목록 순서(아래
  `CompactionProcessor`가 바꾼 순서)에서 `Double.compare` 안정 정렬, 사이클 유발 간선의 트리 중심은 `DoubleStream.average()`
  (Kahan 합, 새 `javaDoubleAverage`), 극값은 `Double.compare`, `MultiLevelEdgeNodeNodeGap`의 재정렬도 `Double.compare`
  안정 정렬, 아래쪽 레이아웃에서 굽은 점 없는 사이클 유발 들어오는 간선은 `getLast()`의 `NoSuchElementException`.
- `TNode.getChildren()`은 현재 나가는 간선들의 목표다: elk-rs의 자식 캐시는 간선을 지울 때 그 목표의 **첫** 항목을
  지워 평행 간선이 있는 노드의 자식 순서가 바뀌었다(`DFSTreeifyer`가 둘째 평행 간선을 지울 때, 예 `v7/g0238`) — 간선의
  위치에서 지운다.
- `NodePlacer`: elk-rs는 Java의 Walker 알고리즘(`LevelHeightProcessor`·`NeighborsProcessor` 속성 위의 `firstWalk`/
  `apportion`/`secondWalk`, 이어지는 `DirectionProcessor`·`NodePositionProcessor`)을 "각 노드를 한 번만 만나는" 너비 우선
  복사본 위의 Reingold-Tilford로 바꿨다. Java는 자식 목록을 그대로 걷는다: `BFS` 트리화가 남긴 평행 간선과 두 번째 부모는
  자식 목록에 중복으로 나타나 한 노드를 여러 번 방문하고, 층(앞 층 자식 목록의 연결)의 마지막 대입이 `LEVELHEIGHT`·이웃·
  형제를 정하며, 한 층에 연달아 두 번 나오는 노드는 **자기 자신의 형제**가 된다 → `secondWalk`가 끝없이 재귀해 Java는
  `java.lang.StackOverflowError`(o 세트 17건; Lean은 첫 자식/오른쪽 형제 단계의 순환을 걷기 전에 찾아 같은 예외를
  던진다). 위치는 `(int) Math.round`(음의 반은 올림; elk-rs `round`는 0에서 멀어짐, 예 `v6/g0278`의 1픽셀), 방향 변환은 그
  `int`에서, 위치 복사는 루트에서 자식 목록으로 닿는 노드, 크기 절반 빼기는 그래프의 **모든** 노드. 새 구현은 노드별
  배열(`Walker`)에 같은 알고리즘을 옮겼다(왼쪽 형제 사슬이 순환이면 Java는 `apportion`에서 멈추지 않는다 — Lean은
  `StackOverflowError`로 끊는다).
- `CompactionProcessor`(`compaction`): 스윕 점은 노드 순서의 모든 시작점 뒤에 모든 끝점(elk-rs는 노드마다 번갈아),
  활성 집합은 위치 투영으로 정렬한 `TreeSet`(같은 투영의 노드는 넣지 않고, `headSet`/`tailSet`/`remove`는 투영 기준),
  의존 노드 뒤에서 `RIGHT`/`DOWN`은 `parent + spacing > newPos`일 때(부모 크기는 판정에 없고 새 위치에만 있음 — Java
  코드 그대로) 부모가 이기며, `UNDEFINED`는 `switch` 분기가 없어 새 위치 0(파이프라인에서는 `NodePlacer`가 이미 `DOWN`으로
  바꿈), `AVOID_OVERLAP`에서 층 안에 들어간 노드는 **새 위치를 유지**하고(elk-rs는 층 시작으로 붙임) 못 들어간 노드만 다음
  층 시작으로, 층 번호는 `levels.indexOf`(`Pair.equals`), 그리고 그래프의 노드 목록을 **그 자리에서** 투영 순으로 정렬한다
  (뒤 프로세서와 라우터가 그 순서를 본다). `getLowestParent`는 그래프 노드 순서의 첫 최댓값.
- `FanProcessor`(문자열 경로, DAG일 때만): `pId != tNode.getProperty(ID)`는 `String` **참조** 비교(같은 값의 다른 객체는
  새 무리), 접두사 키는 층 루프가 끝난 뒤의 식별자(두 번 나온 노드는 마지막 것)이고 접두사보다 짧은 식별자는
  `substring`의 `StringIndexOutOfBoundsException`(o 세트 3건, 문구까지 일치).
- `ElkGraphImporter`: 하이퍼엣지를 원천 노드마다 첫 목표로 가는 트리 간선으로 가져오고(같은 `ORIGIN`, 마지막으로 라우팅된
  것이 section을 씀; elk-rs는 건너뜀), 한 노드의 여러 포트가 나열하는 간선은 항목마다 하나씩, 크기 하한과 결과 상자는
  `Math.max`/`Math.min`과 `Integer.MAX_VALUE`/`MIN_VALUE`.

### 15.3 radial

- 삼각함수: 기준 JVM(Temurin 21.0.13, aarch64)에서 `Math.atan2`·`Math.acos`·`Math.asin`은 `StrictMath`(fdlibm)와 같고
  (200만 표본 0 차이), C 라이브러리와는 약 16%의 인자에서 1 ulp 다르다. `Math.sin`/`Math.cos`는 HotSpot aarch64 스텁
  (`macroAssembler_aarch64_trig.cpp`)이며 fdlibm과 5%, C와 7% 다르다 — 스텁을 읽어 보니 fdlibm 알고리즘에 다항식과 중간
  인자 축소가 **FMA**(`fmadd`/`fmsub`/`fnmsub`)이고, `__kernel_cos`가 축소 **전** 인자의 상위 워드(`ix`, 레지스터 재사용)로
  분기해 축소된 인자는 늘 `qx = 0.28125` 경로를 탄다. 이를 `Elk.Core.Util.Java`에 옮겼다: `javaSin`/`javaCos`(스텁; C로
  먼저 모형을 만들어 JVM 덤프 100만+100만 개 — 일반·`k·π/2` 근처·`2^19·π/2`까지 — 와 비트 단위 0 차이), `javaAtan`/
  `javaAtan2`/`javaAcos`(JDK `FdLibm`). `|x| > 2^19·π/2`의 큰 인자 축소(스텁의 벡터화 `__kernel_rem_pio2`, FMA 포함)는
  옮기지 않았다(C `sin`/`cos`; ELK의 각도에는 나오지 않음). radial의 호출 지점(`EadesRadial` 위치·`acos`, 극좌표 정렬,
  `EdgeAngleCalculator`, `AngleRotation`의 회전·`KVector.angle`)을 바꿨다. 코어 `KVector.rotate/angle`, layered
  `SplinesMath`, DisCo는 담당 밖이라 그대로다.
- `CalculateGraphSize`: Java는 최댓값을 `Double.MIN_VALUE`(가장 작은 양수)에서 시작하고 `Math.min`/`Math.max`(NaN 전파)를
  쓴다 — 한 노드가 NaN이면 Java는 모든 노드가 NaN(`v5/g0528`), 이제 Lean도 같다(Lean은 비유한 수를 `null`로 쓰고 Java Gson은
  `NaN`이라 비교기는 `drift:structure`로 센다 — 수치는 같음, 표현 차이). `findLargestNodeInGraph`·wedge 공간도 `Math.max`.
- **재현 불가 — 다음 레벨 노드의 `HashSet` 순서**: `RadiusExtensionOverlapRemoval.extend`의 다음 층은
  `RadialUtil.getNextLevelNodeSet`(`HashSet<ElkNode>`, EMF 객체의 identity hash)이고, 그 첫 노드의 이동 거리로 다음 층 전체를
  옮긴다. 같은 입력도 JVM 실행 맥락마다 결과가 다르다. 근거: 두 `HashSet`을 `LinkedHashSet`으로 바꾼 그림자 클래스로 돌린
  Java는 합성 벤치마크 `radial_medium/large/xlarge` 3개와 o 세트의 남은 radial 차이 4개(`o3/g0298`, `o3/g0349`, `o4/g0481`,
  `o7/g0566`)에서 Lean과 정확히 같다. 합성 3개는 그래서 수정하지 않은 Java와 계속 다르다(23/26).
- `WEDGE_COMPACTION`이 끝나지 않는 입력: o 세트 2건(`o7/g0337` 노드 3개, `o7/g0560`)은 Java도 끝나지 않는다(`o7/g0337`을
  새 JVM에서 600초까지 돌려도 끝나지 않음; 파이프라인에서는 양쪽 `timeout_both`). PR이 보고한 350/600 노드 입력
  (`opt2_081_radial_broad_350`, `opt2_119_radial_broad_600`)은 Java 2초, 이제 Lean도 0.1/0.5초에 끝난다(350은 Java와 정확히
  같고 600은 위 `HashSet` 순서 차이).

### 15.4 layered P4

- `LinearSegmentsNodePlacer`(`v3/g0156`): 순환을 끊으려고 나눈 선형 세그먼트는 앞 세그먼트의 의존 목록에서 **한 번만**
  빠지고(`List.remove(Object)`; elk-rs `retain`은 전부 지움) 들어오는 수는 조건 없이 줄어든다(elk-rs는 양수일 때만 — 두
  가지가 겹쳐 세그먼트가 위상 정렬에서 빠졌다). 같은 층 판정은 층 동일성, 층 배열 인덱스는 `Layer.getIndex()`, 초기 총
  편향·여유 공간·변위는 `Integer.MAX_VALUE`(elk-rs `f64::MAX`), `Math.min`/`Math.max`, 빈 층의 `NoSuchElementException`,
  가중치 0 영역 병합의 NaN(Java는 `assert`만).
- `NetworkSimplexPlacer.markCrossingEdges`(P3 변형 `v10_g0319`): 닫는 간선은 포트 **자신의** 들어오는 간선 목록 순서이고
  (elk-rs는 `ArenaSync` 발견 순서), Java `ListIterator` 반복은 열린 간선 목록의 0번 항목을 표시하지도 지우지도 않는다
  (elk-rs는 0번까지).

### 15.5 재현하지 않는 것·Java 실행 맥락 의존

- **layered 실행 맥락 의존**: s·v·p 세트에 남은 layered 차이(LPOS/LEDGE/LNODE) 72개 중 37개는 입력 하나만 새 JVM에서 돌린
  Java와 정확히 같다(파이프라인은 세트당 한 JVM). 나머지 35개 중 33개는 `SelfHyperLoop`의 변별 `ArrayListMultimap`
  (`PortSide` 열거형 키의 identity hash 순서)을 열거형 순서로 바꾼 Java(elk-rs 패치 0001과 같은 한 줄, 스크래치 오버레이)와
  같고, 그중 23개는 수정 없는 Java를 다른 순서(역순)로 돌린 실행과도 같다 — 코퍼스 119개와 같은 종류. 결정적으로 남은 것은
  2개(15.6). P3J의 변형 세트(`p3a`, 1,802개)에 남은 23개(NIK 병합 후) 중 22개도 다른 JVM 맥락(한 JVM 일괄·역순·셔플 2종) 중 하나와 같다.
  "최종 간선만 다르다"던 `v8/g0471`·`v9/g0173`은 mrtree 루트의 라우팅이었고(15.2) 이제 새 JVM 단일 실행과 같다 —
  파이프라인 실행과의 남은 차이는 안쪽 layered 자식의 self-loop 맥락 의존이다.
- **Java 자체 결함(재현 안 함)**: `CrossingsCounter`/`BinaryIndexedTree`의 `ArrayIndexOutOfBoundsException`(v 2건, mrtree
  루트 안의 layered 자식, p 세트 다수), `forceNodeModelOrder` NPE 등 — 5장·13장.
- **표현 차이**: Java Gson의 `NaN` 대 elk-lean `null`(radial 9건, 수치는 같음).

### 15.6 남은 것

- `NetworkSimplexPlacer` 1건(`p2/v2_g0421`, 단계별 trace의 첫 차이: 라벨 더미의 y — 비용이 같은 최적해 중 다른 해; 보조
  그래프 구성 순서 조사 필요), `SortByInputModelProcessor` 1건(`p5/v5_g0464`: 층 안 포트 순서; P3 담당 영역 — 같은 단계에서 갈라지던
  `p3a/v2_g0201`은 NIK 병합 후 Java와 같다), `OrthogonalEdgeRouter` 1건(`p3a/v5_g0360`: 두 간선의 세그먼트 x 교환 — 사이클 깨기 난수 상태 또는 세그먼트
  순서).
- 담당 밖: SPOrE(`sporeOverlap` 75·`sporeCompaction` 9, o 세트), VertiFlex 10, rectpacking 4.
- → 위 layered 3건과 담당 밖 세 클래스는 SPV에서 전부 Java와 같아졌다(16장).

### 15.7 결과(시드 1~10; Java 기준값은 같은 입력 — s·v는 라운드 6 실행, d·o·p는 이 라운드 실행)

| 세트 | 둘 다 성공 | 정확 일치 전(`757c7c0`) → 후 | 1e-6 전 → 후 |
|---|---:|---:|---:|
| s | 1,205 | 1,182 → **1,197** | 1,182 → 1,197 |
| v | 5,761 | 5,297 → **5,709**(99.1%) | 5,308 → 5,709 |
| d | 5,761 | 5,298 → 5,709 | 5,309 → 5,709 |
| o | 5,236 | 4,488 → **5,130** | 4,829 → 5,133 |
| p | 1,373 | 1,308 → **1,357** | 1,310 → 1,357 |
| P3J `p3a`(별도, 1,802개) | 1,376 | 1,302 → 1,353 | 1,303 → 1,353 |

정확 → 비정확 0, 비정확 → 정확 1,549(그 밖에 Java의 스택 넘침 17건이 `overflow_both`, 예외 3건이 `error_equal`로). 분류(전 →
후): DEF:mrtree 752 → 0, POS:mrtree 394 → 0, NML:mrtree 15 → 0, T 365 → 3(radial `HashSet`), POS:radial 21 → 11(`HashSet` 1, NaN 표현
8 등), LPOS 96 → 93·LEDGE 18·LNODE 9(15.5), 담당 밖 SPOrE 84·VertiFlex 10·rectpacking 4는 그대로. 결과 행렬(o 세트): Lean ok·Java
overflow 14 → 0, Lean 예외·Java overflow 3 → 0. 코퍼스와 기타 검증은 `HISTORY.md`의 RJ3 행.

테스트: `rj3.java`/`rj3.java.errors`(`tests/fixtures/rj3/` 입력 12개, 새 JVM Java 출력 10개·예외 문구 2개, 기준 바이너리에서 전부
실패), `core.util.java`의 삼각함수 표본(기준 JVM의 비트 값: `sin`/`cos` 48개, `atan2` 37개, `acos` 29개)과 `javaDoubleAverage`·
`javaSortByDouble`, mrtree 단위 테스트의 Java 기대값(자식 캐시, 압축 `UNDEFINED`·제자리 정렬, `(int) Math.round`, 하이퍼엣지
가져오기, Fan 차분 테스트의 예외 일치), Java와 대조해 다시 고정한 mrtree fixture 26개(`tests/fixtures/opt_java_status.tsv`의
`RJ3 re-pin` 행: 24개 `java_exact`, 2개 `java_error_equal`).

## 16. SPV: SPOrE·VertiFlex·rectpacking의 Java 경로, layered 결정적 3건, 삼각함수 통일 (2026-10-29)

방법: 라운드 8 병합본(`38fae55`, `elk_base`)의 `o` 세트 SPOrE 84·VertiFlex 10, `v`·`d` 세트 rectpacking 4(`v8/g0580`,
`v10/g0460`), 15.6의 layered 3건을 Java 소스와 새 JVM 단일 실행, 그림자 클래스(서명 제거한 ELK jar 사본 + 덤프를 넣은
`ElkGraphImporter`/`OrthogonalRoutingGenerator`/`HyperEdgeCycleDetector`, 결과 기준값에는 쓰지 않음)로 확인했다. 결과
기준값은 항상 수정하지 않은 Java(`ElkJavaBaseline`)다. 전부 ELK Java가 기준이고 elk-rs와는 달라진다.

### 16.1 SPOrE(`sporeOverlap`·`sporeCompaction`)

- **`HashSet` 순회 순서**: `BowyerWatsonTriangulation`의 `HashSet<TTriangle>`·`HashSet<TEdge>`, 겹침 제거의 겹침 간선 집합,
  `Graph.tEdges`는 Java `HashSet`이고 원소의 `hashCode`가 값 기반이다(`KVector` = `Double.hashCode(x) +
  Integer.reverse(Double.hashCode(y))`, `TEdge` = 두 끝의 합, `TTriangle` = 세 꼭짓점의 합). 그 순서가 `NaiveMinST`의 같은
  비용 간선 순서(안정 정렬)를 정해 신장 트리와 결과가 바뀐다 — elk-rs는 `std` 집합(무작위 순서)이었고 Lean은 삽입 순서였다.
  새 `Elk.Core.Util.JavaHashSet`이 JDK 21 `HashMap`의 빈 배열(16에서 두 배, 적재율 0.75, `resize`의 lo/hi 분할), 빈 안
  삽입 순서, `clear()`가 용량을 유지하는 것, 트리 빈(9개 이상·용량 64 이상, `TreeNode` 적흑 트리, `moveRootToFront`,
  `removeTreeNode`, 분할·`untreeify`), 반복자 제거(`movable = false`), `AbstractSet.removeAll`의 두 분기를 옮겼다.
  `java.util.HashSet`과의 차분(`scripts/java/HashSetOrder.java`, `scripts/gen_hashset_ops.py`): 무작위 연산 열 128개(그중
  20개는 트리 빈 최대 6개)에서 모든 순회 순서가 같다. 겹침 간선 집합은 반복마다 같은 객체를 `clear()`하고 그래프의
  간선 집합이 되며, Delaunay 단계는 그 집합에 `addAll`한다(같은 객체).
- `ScanlineOverlapCheck`: 활성 집합은 `TreeSet`(같다고 비교되는 노드는 추가 실패 → Java `IllegalStateException: Invalid
  hitboxes for scanline overlap calculation.`, 크기 0 노드 등; elk-rs는 그냥 넣음), 비교자 `Double.compare`. `NaiveMinST`:
  `Double.compare` 정렬, 가중치 NaN 간선은 건너뜀. `fuzzyCompare`는 Guava(`a == b`·둘 다 NaN도 같음).
- 하위 알고리즘(`underlyingLayoutAlgorithm` = `box`/`fixed`/`random`)이 그래프를 먼저 배치할 때 Java `getProperty`는 그
  알고리즘 메타데이터의 **기본 padding(15)을 노드에 저장**한다(`EMapPropertyHolderImpl`의 복제 기본값). 뒤에 읽는 SPOrE·
  DisCo의 padding이 12가 아니라 15가 된다 — box/fixed/random 공급자에 `ElkM.getNodePropSticky`를 썼다.
- **재현 불가**: SPOrE 임포터는 중심이 같은 노드에 `Math.random()` 흔들림(±0.0005)을 더한다(`ElkGraphImporter` 169행). 같은
  위치의 노드가 있는 입력은 Java 실행마다 결과가 다르다(두 JVM 실행이 서로 다름; Lean은 흔들림 없이 결정적). 트리 빈 안의
  **같은 hash** 원소 순서(`System.identityHashCode`의 `tieBreakOrder`)도 재현하지 않는다(SPOrE 입력에서는 트리 빈 자체가
  생기지 않았다).

### 16.2 VertiFlex

- `RelativeXPlacer.splitGroup`: Java 루프는 `i`를 늘리지 않는다 — 음수 폭이 아니면 루프에 들어가지 않거나(들어가면 Java는
  끝나지 않음 → Lean은 `IllegalStateException`으로 끊음) 결과가 `-1`이어서, 높이가 같은 자식 무리는 통째로 오른쪽으로 간다
  (`o1/g0513`; elk-rs는 `i`를 늘렸다).
- 루트 이동의 `CONSIDER_NODE_MODEL_ORDER`는 레이아웃 그래프가 아니라 **트리 노드**에서 읽는다(노드에 없으면 기본 `true`;
  `o7/g0218`).
- 트리 순회는 노드 **자신의** 간선(`getOutgoingEdges()`/`getIncomingEdges()`)이다: 포트의 간선은 자식이 아니고(elk-rs는
  `allOutgoingEdges`), 목표가 포트인 간선은 `(ElkNode)` 형변환의 `ClassCastException`, 목표 없는 간선은
  `IndexOutOfBoundsException`. `findRoot`만 포트 포함(`ElkGraphUtil.allIncomingEdges`). 부모 수는 노드의 들어오는 간선 수,
  `Math.max`, 오류 문구의 식별자 `null`, Java의 IOOBE 문구.

### 16.3 rectpacking

- `RowFillingAndCompaction`: 행을 다시 압축해야 하면 Java는 **같은 행**을 다시 압축한다(`rowIdx--` + `rowIdx++`; elk-rs는
  앞 행으로 돌아가 뒤 행을 앞 행에 붙였다 — `v10/g0460`).
- 강한 참조: 블록은 행 목록에서 빠진 행과 초기화된 스택을 계속 부모로 가진다(elk-rs `Weak`는 `None`). 빠진 다음 행에서 온
  블록은 다시 압축할 때 `wasFromNextRow`로 보여 행에 **두 번** 들어가고, `RectRow.removeBlock`은 첫 항목만 지우며(
  `List.remove(Object)`) 높이는 `Double.MIN_VALUE`에서 `Math.max`(`v8/g0580`). `notifyAboutNodeChange`는 모든 블록에서 다시
  계산한다(elk-rs `RefCell` 차용 실패 시 "defer" 없음). `Block.setLocation`의 Java 계산 순서(`row.x + x - blk.x`),
  `Math.min/max`, 빈 블록 평균 높이 NaN, 빈 목록의 IOOBE.
- `InteractiveNodeReorderer`: 같은 위치에 `-1`을 내는 비교자는 JDK TimSort(`javaSortBy`)로, 음수 `desiredPosition`은 EMF
  `BasicEList.addUnique`의 `System.arraycopy` 예외 `ArrayIndexOutOfBoundsException: arraycopy: source index <위치> out of
  bounds for object array[<용량>]`(용량은 `c + c/2 + 4`로 자란 자식 배열; elk-rs는 0으로 잘랐다). 기존 fixture 3개(`g2_168`,
  `g2_364`, `enum/g4_155`)가 Java처럼 예외가 되고 2개는 Java 문구로 바뀌었다.

### 16.4 layered 결정적 3건과 교차 계수

- `NetworkSimplexPlacer`(`p2/v2_g0421`): Java `LNode.getPortSideView`는 캐시된 인덱스 범위(`cachePortSides()`)를 다시 검증하지
  않는다 — `PortListSorter` 뒤에 북/남 포트가 더해진 노드에서 뷰가 밀려 다른 변의 포트를 담거나 빠뜨리고, 캐시가 없으면
  `findPortIndices()`(변마다 마지막 연속 구간). elk-rs는 범위가 어긋나면 변으로 걸렀다. `LGraphArena.nodePortSideView`를
  Java대로 바꾸고 NSP의 `getPortSideView` 지점(`transformFixedOrderNode`, 북/남 보조 간선, `markCrossingEdges`)을 그것으로,
  P3 교차 계수(`CrossMinUtil.sideView`, `CrossingsCounter`의 live·snapshot 경로)도 같은 의미로 맞췄다(P3 시작에
  `GraphInfoHolder`가 모든 노드를 다시 캐시하므로 포트가 변별로 정렬돼 있으면 같은 범위다). `improveTwoPath`는 Guava
  `fuzzyEquals`(같은 무한대 포함), 직선 간선 가중치는 Java의 `Math.max(old, old + (w - old))`.
- `SortByInputModelProcessor`(`p5/v5_g0464`): `ModelOrderPortComparator`/`ModelOrderNodeComparator`의 네 번째 추이 검사는
  Java에서 둘째 검사의 복사라 결정하지 않고, 앞 layer 검사는 `checkReferenceLayer`(먼저 발견된 원천 노드가 결정), group
  model order는 두 원소 모두의 group id(`int` 산술), long edge 목표의 model order 맵은 목표마다 따로.
- `OrthogonalEdgeRouter`(P3 변형 `v5_g0360`): `HyperEdgeSegment.insertSorted`는 원소의 **`floatValue()`**를 `double`과 비교한다
  — `float`이 아닌 좌표(`-60.2`)는 같은 값이 두 번 들어가 의존 가중치(교차 수)에 들어간다. elk-rs는 `f64::EPSILON` 비교.
- `AllCrossingsCounter`: Java `initAfterTraversal`은 `HyperedgeCrossingsCounter`와 `CrossingsCounter`에 **같은 `portPos`
  배열**을 준다 — in-layer 계수는 스스로 번호를 매기지 않는 먼 끝(다른 변의 포트)의 위치를 이전 계수(하이퍼엣지 계수 포함)가
  남긴 값으로 읽는다. elk-rs는 하이퍼엣지 계수기에 따로 배열을 줬다. 공유로 바꿨다(무작위·변형 세트의 결과는 그대로).

### 16.5 삼각함수 통일

Java `Math.sin/cos/atan2/acos/asin`의 나머지 호출 지점을 기준 JVM 함수로 바꿨다(15.3): 코어 `KVector`(`new KVector(angle)`,
`rotate`, `angle`, `toRadians` — 새 `javaAsin`, JDK `FdLibm.Asin`: 기준 JVM `Math.asin`과 인자 400,026개에서 비트 동일,
`scripts/java/AsinDump.java`), layered `SplinesMath`(`acos`·`cos`, 스플라인 자기 루프의
`KVector.fromAngle`), DisCo `ElkGraphTransformer`(`atan2`·`sin`·`cos`). 이제 ELK Java 소스의 삼각함수 호출 24곳 전부가
`Elk.Core.Util.Java`를 쓴다. 코퍼스 Lean 출력은 바이트 동일.

### 16.6 재현하지 않는 것·남은 것

- SPOrE의 `Math.random()` 흔들림(같은 중심의 노드, 16.1): Java 자체가 실행마다 다르다. 같은 위치 노드가 있는 SPOrE
  fixture 4개(`co_dup_positions`, `ov_identical`, `ov_identical3`, `ov_same_center`)는 Java 두 실행이 서로 달라 Lean 출력
  그대로 둔다(`opt_java_status.tsv`의 `java_differs`).
- Lean CLI는 옵션 범위를 검증한다(`desiredPosition` 음수 → `GraphValidationException`). ELK Java 엔진(`RecursiveGraphLayoutEngine`)
  은 검증하지 않아 위 AIOOBE까지 간다 — 기존 차이로 고치지 않았고(JSON fixture 대신 단위 테스트로 AIOOBE 경로를 검사),
  무작위 세트에는 나오지 않는다.
- 남은 무작위 차이(둘 다 성공 19,336개 중 134개): layered LPOS 93·LEDGE 17·LNODE 8(15.5의 실행 맥락 의존 — 새 JVM 단일
  실행 또는 `SelfHyperLoop` 패치 Java와 같다; 15.5의 결정적 2건은 이번에 고쳐졌다), radial `HashSet` 순서·NaN 표현(POS:radial 11, T 3, NML:radial 2; 15.3). 비-layered
  알고리즘의 남은 차이는 radial뿐이다(o 세트 12개 전부).
- DisCo fixture 42개 중 Java와 정확히 같은 것은 5개(`tests/fixtures/disco/README.md`): 나머지는 DisCo 패킹 자체(담당 밖),
  무작위 세트에는 DisCo가 없다.

### 16.7 결과(시드 1~10, Java 기준값은 같은 입력 — RJ3 실행 재사용)

| 세트 | 둘 다 성공 | 정확 일치 전(`38fae55`) → 후 | 1e-6 전 → 후 |
|---|---:|---:|---:|
| s | 1,205 | 1,197 → 1,197 | 1,197 → 1,197 |
| v | 5,761 | 5,709 → **5,711** | 5,709 → 5,711 |
| d | 5,761 | 5,709 → 5,711 | 5,709 → 5,711 |
| o | 5,236 | 5,130 → **5,224**(99.8%) | 5,133 → 5,227 |
| p | 1,373 | 1,357 → **1,359** | 1,357 → 1,359 |
| NIK `npa`(1,802개) | 1,323 | 1,316 → 1,317 | |
| NIK `npb` | 1,151 | 1,142 → 1,143 | |
| NIK `mob` | 1,715 | 1,698 → 1,698 | |
| P3J `p3a` | 1,376 | 1,353 → **1,354** | |

정확 → 비정확 0, 비정확 → 정확 100(s·v·d·o·p: SPOrE 84 = `sporeOverlap` 75·`sporeCompaction` 9, VertiFlex 10, rectpacking
`v8/g0580`·`v10/g0460`(v·d), `p2/v2_g0421`, `p5/v5_g0464`) + 변형 세트 3(`npa/v10_g0253`, `npb/v3_g0181`, `p3a/v5_g0360`), 결과
종류(ok/예외/시간 초과/스택 넘침) 변화 0. 분류(전 → 후): POS:sporeOverlap 75 → 0, POS:sporeCompaction 9 → 0, POS:vertiflex
10 → 0, POS:rectpacking 2 → 0, DEF:rectpacking 2 → 0, LEDGE 18 → 17, LNODE 9 → 8, LPOS 93·POS:radial 11·T 3·NML:radial 2는
그대로(둘 다 성공 19,336개 중 남은 차이 234 → 134). SPOrE를 쓰는 입력 1,118개·VertiFlex 268개는 전부 정확, rectpacking이
들어 있는 1,930개 중 남은 19개는 다른(layered) 단위의 차이다. 변형 세트의 결과 종류 변화 1건: `npb/v1_g0132`는 Java가
`AllCrossingsCounter`의 in-layer 계수에서 `BinaryIndexedTree.rank`의 `ArrayIndexOutOfBoundsException: Index 7 out of bounds for
length 2`를 내고, 전에는 Lean이 성공했으며 이제 Lean도 같은 트리(크기 1)에서 예외를 내지만 다른 칸(`Index 1 out of bounds
for length 1`, `add`)이다 — Lean의 단계별 trace는 Java가 남긴 188단계와 전부 같고(기준 바이너리는
`SortByInputModelProcessor`에서 갈라졌다) 실패하는 P3 단계 안에서, 앞선 계수가 남긴 먼 끝 위치만 다르다(`portPos` 공유 후에도
같음; 더 조사하지 않음).

테스트: `spv.java`/`spv.java.errors`(`tests/fixtures/spv/` 입력 16개, 새 JVM Java 출력 14개·예외 문구 2개, 15개는 기준 바이너리에서
실패, `vertiflex_constraint_before_cast`는 형변환 순서의 회귀 검사), `spv.javaHashSet`(`java.util.HashSet` 순서 재생), `spv.javaAsin`(JVM 표본 42개, `ELK_ASIN_CASES`로 전체),
`layered.p3counting.all_crossings_counter`의 `portPos` 공유, `alg.common`·`spore`·`rectpacking` 단위 테스트의 Java 값(`KVector`/
`TEdge`/`TTriangle` hash, Bowyer–Watson 결과, `NaiveMinST` NaN 가중치, `INVALID_HITBOXES`, 스택 강한 참조·중복 블록·
`MIN_VALUE`, 음수 위치 AIOOBE와 EMF 용량), Java와 대조해 다시 고정한 fixture(`tests/fixtures/opt_java_status.tsv`의 `SPV` 행:
SPOrE 7·VertiFlex 8·rectpacking 1개 `java_exact`, 예외 4개·문구 2개 `java_error_equal`, DisCo 35개는 padding 15에 맞춘 Lean 출력,
그중 5개 `java_exact`), 쓸모없어진 SPOrE 대체 출력(`.alt<k>.json`) 33개 삭제. VertiFlex의 수직 제약 검사는 간선마다 형변환한다
(앞 자식의 제약 위반이 뒤 간선의 `ClassCastException`보다 먼저, `vertiflex_constraint_before_cast`). `lake build` 경고 0,
`lake test` 16,830 통과/0 실패(기준 16,754).

코퍼스(ELK Java 기준): Lean 출력 1,998개 기준 바이너리와 바이트 동일, 정확 일치 1878/119(집합 동일), Java 단계별 trace 1,743/1,997(요약 — 갈라지는 254개 모델과 첫 차이 단계 — 이 기준과 같음). elk-rs 보조 검사(spv14 바이너리, `portPos` 공유 포함): model parity(1e-6) 1447/1447, strict trace 1447/1447 — 떨어진 것 없음.

성능(`elk bench` 합성 26개, 기준 바이너리와 번갈아 5회, 중앙값, 최종 바이너리): 기하평균 0.992배, rectpacking 0.96~0.97배
(`Weak`/차용 흉내 제거), 나머지 0.97~1.01배(최대 `mrtree_xlarge` 1.008, 잡음 범위 — mrtree 코드는 바뀌지 않음).

## 17. LM: 교차 최소화의 elk-rs 잔여, 교차 계수 예외 인덱스, 큰 인자 `sin`/`cos`, `MAX_MODEL_ORDER_NODES`의 `null` (2026-10-31)

방법: 라운드 9 병합본(`3d6242f`, `elk_base`)과 Java 소스·새 JVM 단일 실행, 그림자 클래스(서명 제거한 layered jar 사본 +
`AllCrossingsCounter`/`CrossingsCounter`에 위치 배열·호출 지점 덤프, 결과 기준값에는 쓰지 않음)로 확인했다. 결과 기준값은
항상 수정하지 않은 Java(`ElkJavaBaseline`)다. 전부 ELK Java가 기준이고 elk-rs와는 달라진다.

### 17.1 `countModelOrderNodeChanges`/`countModelOrderPortChanges`

Java는 층 0의 "이전 층"으로 `layers[0]` 자신을 넘기고(`previousLayer == -1 ? layers[0] : …`; elk-rs: 빈 층), 층마다(포트는
노드마다) 새 비교자를 만들며, `longEdgeTargetNodePreprocessing`을 포트가 둘 미만인 노드에도 부른다(elk-rs는 그런 노드를
먼저 건너뛰어 `TARGET_NODE_MODEL_ORDER`/`LONG_EDGE_TARGET_NODE`를 남기지 않았다). Lean은 이 셋을 Java대로 바꿨다(비교자는
SPV가 Java와 같게 만든 `ModelOrderNodeComparator`/`ModelOrderPortComparator`를 층·노드마다 초기화해 재사용).
`countCurrentNumberOfCrossingsNodePortOrder`도 Java 순서로: model order 계수 → 시작 그래프 교차 → 자식 그래프의 교차를
`double`로 Java의 덧셈 순서(`total += crossings + influence`, 자식마다 `total += …`). 층 0의 노드가 이전 층과 이어지려면
층 id가 −1인 노드가 있어야 하고, 전처리의 부작용은 이미 정렬된 노드에서 다시 읽히지 않아서, 코퍼스·무작위·변형 세트 어디에서도
출력이 달라지지 않았다(재현 가능한 차이를 찾지 못함 — 결정적 이식으로 둠).

### 17.2 `npb/v1_g0132`의 예외 인덱스(`CrossingsCounter`의 낡은 먼 끝 위치)

Java: 중첩 그래프(포트 17개)의 첫 계수(`minimizeCrossingsWithCounter`의 초기 교차, 위치 배열 전부 0)는 성공하고, 첫 sweep 뒤의
계수에서 마지막 층 `EAST` 쪽 in-layer 계수가 포트 13의 in-layer 간선의 먼 끝(포트 11, `WEST` 쪽 — 이 계수는 번호를 매기지
않음)을 읽는다. 그 위치는 앞 계수의 층 사이 계수가 남긴 `7`이고, 트리 크기는 1이라 `BinaryIndexedTree.rank(7)`이
`ArrayIndexOutOfBoundsException: Index 7 out of bounds for length 2`를 낸다. Lean은 `countAllCrossings`의 in-layer·층 사이
계수(스냅숏 경로의 묶음 트리, 살아 있는 경로의 `BinaryIndexedTree`)가 범위 밖 인덱스를 조용히 무시해 성공했고, 같은 상태가
뒤의 greedy switch 양방향 계수(`withTreeChecked`, 유일하게 검사하던 곳)에서 `Index 1 … length 1`로 터졌다.

- `countInLayerCrossingsOnSide`·`countCrossingsBetweenLayers`가 두 경로 모두 Java의 트리 경계를 검사한다: 스냅숏 경로는
  묶음 트리에 표시 칸 하나(`t[2n+1]`)를 더해 범위 밖 `add`를 표시하고, 표시되면 같은 번호 매기기를 살아 있는 경로로 다시 해
  `javaTreeIndexError`(Java 순서로 처음 실패하는 접근: 먼 끝 > n이면 `rank`의 `Index e … length n+1`, = n이면 `add`의
  `Index n … length n`)를 던진다. 살아 있는 경로는 `withTreeChecked`. 정상 입력에서는 표시 검사 하나만 더해진다.
- `countCurrentNumberOfCrossings`: elk-rs의 그래프별 교차 수 캐시(`cached_crossings_by_graph`·dirty 집합)를 없애고 Java처럼
  매번 다시 센다 — 공유 위치 배열 때문에 바뀌지 않은 순서를 다시 세는 것도 관찰된다(앞 계수가 남긴 먼 끝 위치가 다르다).
  자식 그래프는 Java의 재귀 순서(`childGraphs` 순서)로 센다.

결과: `npb/v1_g0132` Java와 같은 예외 문구. 같은 원인으로 Java만 실패하던 무작위·변형 입력이 대거 Java와 같아졌다:
`robustness/java_crossing_counter_aioobe`(“Java 결함, 재현하지 않음”으로 두었던 fixture — 이제 `robustness.exceptions`),
무작위 s 6·v 10·d 10·p 26(17.5).

### 17.3 HotSpot `sin`/`cos`의 큰 인자 축소

RJ3은 `|x| ≤ 2^19·π/2`만 스텁대로 옮기고 그 위는 C 라이브러리를 썼다. `generate__ieee754_rem_pio2`의 큰 인자 분기와
`generate__kernel_rem_pio2`(HotSpot `macroAssembler_aarch64_trig.cpp`, RJ3이 받아 둔 소스)를 `hsRemPio2Large`로 옮겼다:
`e0 = (ix >> 20) − 1046`, `z`의 24비트 조각 `x[0..2]`(펼친 루프, `nx` 판정), `jv = (e0 − 3) / 24`(`sdiv`, 음수면 0),
`2/π` 표를 `double`로, `q[i]`를 스텁의 벡터 순서대로 융합 곱셈-덧셈(`f[i]·x[jx]`부터 `fmla`), 재계산의 `q`도
`fmadd`(`x[0]·f`부터), `2^q0`/`2^-q0`/`fw`는 지수 비트로, 재계산 항 수 `k`는 `iq[3..0]`를 펼쳐 최대 4, `PIo2[k]·q[i+k]`를
`fmadd`로 누적, `fq` 압축은 fdlibm `prec = 2`. JVM 덤프(`scripts/java/SinCosDump.java`: 경계 `0x413921fb…`, `2^19`~`2^1023`의
거듭제곱과 이웃·`2^e·π/2`, 1e6~1e300 십진 크기, 무작위 1,000,000개 — 합계 1,006,063개, Temurin 21.0.13 aarch64)와 `sin`·`cos`
모두 비트 동일(차이 0). 이제 `javaSin`/`javaCos`는 모든 유한 인자에서 기준 JVM과 같다. 테스트 `core.javaSinCos.large`(표본
94개, `ELK_SINCOS_CASES=<덤프>`로 전체). 코퍼스·무작위 출력은 바뀌지 않았다(그런 인자를 쓰는 입력이 없음).

### 17.4 `MAX_MODEL_ORDER_NODES`의 `null`과 간선 `MODEL_ORDER`의 `null` — 결정적이므로 재현

`ElkGraphImporter.importHierarchicalGraph`는 `MAX_MODEL_ORDER_NODES`를 **최상위 그래프에만** 설정하고(`createLGraph`로 만든
중첩 그래프에는 없음, 기본값도 없는 `Property`), `int`로 읽는 곳이 언박싱 NPE를 낸다: `ModelOrderNodeComparator`(두 노드 모두
`MODEL_ORDER`일 때의 마지막 비교), `ModelOrderPortComparator`(`PREFER_NODES`의 long edge 목표 비교),
`ModelOrderBarycenterHeuristic`, `ModelOrderCycleBreaker`·`GreedyModelOrderCycleBreaker`·`SCCModelOrderCycleBreaker`(처리 시작),
`DFS`/`BFSNodeOrderCycleBreaker`(`ENFORCED`이고 목표에 model order가 있을 때). 같은 임포터는 간선 model order를 계층 전체에
걸친 BFS 하나의 인덱스로, **최상위 그래프**가 필요로 할 때만 준다(`needsModelOrderBasedOnParent(elkgraph)`) — 중첩 그래프가
model order 전략을 켜도 최상위가 아니면 그 간선에는 값이 없어, `longEdgeTargetNodePreprocessing`의 `Math.min(edge.getProperty(
MODEL_ORDER), …)`와 `getModelOrderFromConnectedEdges`가 NPE를 낸다. 어느 쪽도 실행 맥락과 무관한 결정적 결과이고 사용자에게
보이는 예외이므로(ticket 213의 NaN 출력과 달리 레이아웃 자체가 실패) Java 문구를 재현한다:

- `LGraphInternals.maxModelOrderNodesNull`(계층 임포트의 중첩 그래프에 설정, 컴포넌트 분할은 그대로 물려받음)과
  `ModelOrderGraphContext.maxModelOrderNodesNull`; 위 읽기 지점마다 `maxModelOrderNodesNullError`(`Cannot invoke
  "java.lang.Integer.intValue()" because the return value of "org.eclipse.elk.alg.layered.graph.LGraph.getProperty(…)" is null`).
  `ModelOrderBarycenterHeuristic`의 순수 정렬은 관계 상태의 표시로 멈추고 호출자가 던진다.
- 간선 model order: `assignHierarchicalEdgeModelOrders`(Java BFS 순서, 최상위 기준; elk-rs: 층마다 0부터, 층마다 판정),
  값이 없는 간선의 두 읽기 지점은 `edgeModelOrderNullError`(`… LEdge.getProperty(…)" is null`).
- 덤으로 `ModelOrderCycleBreaker`의 `bigOffset = offset * CB_NUM_MODEL_ORDER_GROUPS`(Java; elk-rs `max(…, 1)`).

결과(변형 세트의 Java NPE 407개): `LGraph` 문구 349/349, `LEdge` 문구 54/54 Java와 같음(전에는 Lean 성공 또는 다른 예외).
남은 4개는 greedy switch `BetweenLayerEdgeTwoNodeCrossingsCounter`의 `Map.get` NPE(이 라운드 범위 밖). fixture
`tests/fixtures/lm/`(4개, `lm.java.errors`), 기존 단위 테스트 하나(`sortByInputModelProcessor`의 model order 없는 간선 — Java면
NPE)는 값을 주고 NPE 검사를 따로 뒀다.

### 17.5 결과(시드 1~10; 기준 = `3d6242f`, Java 기준값은 RJ3·NIK·P3J 실행 재사용, 변형 세트는 추적되는 생성기로 만든 기존 입력)

| 세트 | 둘 다 성공 | 정확 일치 전 → 후 | Java 예외 | 예외 문구 일치 전 → 후 |
|---|---:|---:|---:|---:|
| s | 1,205 | 1,197 → 1,197 | 4,793 | 4,787 → **4,793** |
| v | 5,761 | 5,711 → 5,711 | 227 | 216 → **226** |
| d | 5,761 | 5,711 → 5,711 | 227 | 216 → 226 |
| o | 5,236 | 5,224 → 5,224 | 745 | 745 → 745 |
| p | 1,373 | 1,359 → 1,359 | 428 | 379 → **426** |
| NIK `npa`(1,802개) | 1,323 | 1,317 → 1,317 | 479 | 91 → **139** |
| NIK `npb` | 1,151 | 1,143 → 1,143 | 651 | 138 → **605** |
| NIK `mob` | 1,715 | 1,698 → 1,698 | 87 | 81 → 84 |
| P3J `p3a` | 1,376 | 1,354 → 1,354 | 426 | 376 → 412 |

모든 세트에서 정확 → 비정확 0, 예외 문구 일치 → 불일치 0, Java가 성공하는 입력이 Lean에서 실패로 바뀐 것 0. 바뀐 입력은 전부
"Java만 예외/다른 예외 → 같은 예외"이다(무작위 s·v·d·p 71개: 교차 계수 트리의 AIOOBE 52·model order NPE 19, 루트 알고리즘이 box/force/mrtree/
radial/stress인 입력은 그 안의 layered 자식 그래프). s 세트의 Java 예외는 이제 전부 문구까지 같고, v 세트에 남은 것은 위
greedy switch `Map.get` NPE 1개다. 기본 세트(s, v)가 바뀌어 `tests/random_parity/report.md`를 기본 실행으로 다시 게시했다.

코퍼스(ELK Java 기준): Lean 출력 1,998개와 elk-rs trace·Java trace용 Lean trace 모두 기준 바이너리와 바이트 동일, 정확 일치
1878/119(집합 동일), Java 단계별 trace 1,743/1,997(기준과 같음). elk-rs 보조: model parity(1e-6) 1447/1447, strict trace
1447/1447. 합성 26개 Lean 출력 바이트 동일. `lake build` 경고 0, `lake test` 17,023 통과/0 실패(기준 16,830: 큰 인자 삼각함수
189, `lm.*` 4 등).

성능(`elk bench --scenarios layered_medium,crossmin_layer_sweep,radial_large --iterations 20 --warmup 3`, 기준 바이너리와 번갈아
5회, 중앙값): `crossmin_layer_sweep` 1.010배, `layered_medium` 1.014배(무작위 반복마다 Java처럼 다시 세는 계수 1회),
`radial_large` 1.003배 — 5% 게이트 안.

### 17.6 남은 것

- greedy switch `BetweenLayerEdgeTwoNodeCrossingsCounter.AdjacencyList.addAdjacencyOf`의 `Map.get` 언박싱 NPE(변형 세트 4·v 1).
- 계층 임포트의 노드 model order는 elk-rs처럼 층마다 0부터다(Java: 계층 전체 BFS 인덱스, `MAX_MODEL_ORDER_NODES`는 최상위의
  전체 개수). 한 그래프 안의 상대 순서와 최상위의 offset 비교 결과는 같아 관찰되지 않았다.
## 18. DIS: DisCo 패킹의 Java parity와 옵션 검증 순서 (2026-10-31)

방법: 라운드 9 병합본(`3d6242f`, `elk_base`)과 DisCo fixture 58개(`tests/fixtures/disco/`)를 Java 소스와 비교하고, 새 무작위
세트 `c`(`scripts/gen_disco_graphs.py`, `--sets c`; 시드 1~10 × 600)를 수정하지 않은 ELK Java 0.12.0과 대조했다. 다른 생성기는
DisCo를 고르지 않아 이전 무작위 세트에는 DisCo 입력이 없었다. `c` 세트는 DisCo를 루트(약 6/7) 또는 `fixed` 루트의 복합 자식에
두고, 무작위 컴포넌트(위치가 주어진 노드, 라벨, 포트·포트 라벨, 섹션·bend point가 있거나 없는 간선, 간선 라벨, 가끔 self loop와
하이퍼엣지), DisCo 노드의 포트와 자식을 잇는 간선(확장), 컴포넌트 레이아웃 알고리즘(없음·`fixed`·`box`·`layered`·`random`·
`rectpacking`), `aspectRatio`·간격·padding·간선 두께·`polyomino.*`를 바꾼다. 결과 기준은 항상 ELK Java이고 elk-rs와는 달라진다.

### 18.1 DisCo(`alg.disco`, `alg.common.polyomino`)

- **정렬 방향**(주원인): `PolyominoCompactor.packPolyominoes`는 low-level 비교자를 `.reversed()`로 정렬한다(큰 polyomino
  먼저, 안정 `List.sort`), 이어 high-level 비교자들은 오름차순. elk-rs는 low-level을 오름차순으로 정렬했다. 비교자 값은 Java
  `int` 산술(`w * w`).
- **polyomino 옵션 등록**: ELK Java는 `org.eclipse.elk.alg.common` jar의 `ServiceLoader` 항목으로 `PolyominoOptions`를 등록하므로
  JSON의 `org.eclipse.elk.polyomino.fill`이 파싱되어 `fill = false`가 적용된다. elk-rs(와 이전 Lean)는 이 provider를 적용하지
  않아 옵션을 무시했다. `Elk.Alg.Disco.Init`이 DisCo 앞(rank 19)에서 등록한다 — `elk options`에 4개 추가(251개).
  `lowLevelSort`·`highLevelSort`·`traversalStrategy`는 Java에서도 빈 `Polyominoes` 홀더에서 읽혀 항상 기본값이다(변화 없음).
  DisCo의 option support 기본값은 Java처럼 각 옵션의 기본값(`aspectRatio` 없음, `padding` 12; elk-rs 1.0·0).
- **루트에서 오는 간선**: `ElkGraphComponentsProcessor.computeIncidences`의 `getSourceNode(edge).getParent().equals(...)`는
  레이아웃 루트에서 시작하는 간선(루트 포트 → 자식)에서 `NullPointerException`을 던진다. 루트로 들어가는 간선(자식 → 루트 포트)은
  확장으로 레이아웃된다. 이전 Lean은 둘 다 레이아웃했다(`c` 세트 Java 예외 269건 중 대부분).
- **grid 경계**: `TwoBitGrid`는 `long[height][ceil(width / 32)]`이다. 읽기는 배열 밖(`y` 범위 밖, `x < 0`, `x >> 5 >= words`)에서만
  실패하고 너비 오른쪽의 같은 워드 칸은 비어 있다고 읽으며, 쓰기는 `x >= width`에서도 실패한다. 중심 기준 접근의 메시지는
  변환된 점 + ` Given center based coordinates were (x, y).`이다. 이전 Lean은 모든 접근을 너비로 검사하고 중심 기준 좌표를
  보고했다(`weaklyIntersectsArea`가 Java보다 먼저 실패할 수 있었다).
- **`getFilledBounds`**: 막힌 칸이 없으면 Java `int` 산술로 `(MAX_VALUE, MAX_VALUE, 2, 2)`(이전 Lean `(0, 0, 0, 0)`), 위치 차도
  `int` 감산.
- **aspect ratio**: `null`만 1.0이다(이전 Lean은 0도 1.0으로 바꿨다). 0·NaN은 무한/NaN 셀 높이로 Java와 같은 NaN·거대 좌표를,
  음수는 `DCPolyomino.reinitialize`의 `NegativeArraySizeException: <높이>`를 낸다. `1e-9`·`1e9` 같은 극단 값의 grid는 Java가
  `OutOfMemoryError: Requested array size exceeds VM limit`(차원 `MAX_VALUE`)·`Java heap space`로 실패한다 — elk-lean은 2^26
  워드를 넘는 grid를 할당하지 않고 같은 문구를 던진다(이전에는 수십 GB를 할당하려다 멈췄다; Java의 heap 한계 자체는 JVM 설정
  의존).

### 18.2 DisCo 경로에서 드러난 다른 단위의 Java 동작

DisCo의 컴포넌트 레이아웃 알고리즘은 엔진을 거치지 않고 provider를 직접 부른다. `c` 세트가 처음으로 건드린 Java 동작:

- `RandomLayoutProvider.RAND_FACT = 0.2f`(double로 넓힌 `0.20000000298023224`; elk-rs 0.2) — bend point 흔들림이 ~1e-9 달랐다
  (`random` 컴포넌트 레이아웃 484건이 1e-6 일치만).
- `FixedLayoutProvider`는 들어오는 간선마다 `getSourceNode(edge)`를 불러 하이퍼엣지에서 `IllegalArgumentException`을 던지고,
  루트에서 오는 간선(`getParent() == null != layoutNode`)도 처리한다(이전 Lean은 둘 다 건너뛰었다).
- layered `ElkGraphImporter.transformExternalPort`는 라벨 간격을 `elkgraph.getParent()`에서 읽어, 외부 포트가 있는 **레이아웃
  루트**에서 `NullPointerException`을 던진다(DisCo의 `layered` 컴포넌트 레이아웃 + 루트 포트 59건; 엔진 경로의 layered 루트도 같다,
  코퍼스·다른 무작위 세트에는 없다). 단위 테스트 `layered.import.externalPorts`는 같은 그래프를 복합 자식으로 가져온다.
- force: `iterations = 0`(17.3)에서 FR의 `threshold = temperature / 0 = ∞`(한 번 반복, 온도 `-∞`)이고 bounding box는 Java처럼
  `Integer.MAX/MIN_VALUE` 시작값과 NaN 전파 `Math.min/max`, `ElkUtil.resizeNode`도 `Math.max` — Java처럼 전부 NaN이 된다.

### 18.3 옵션 검증 순서(결정)

ELK Java의 JSON 경로(`JsonImporter` → `RecursiveGraphLayoutEngine.layout`)는 옵션의 `lowerBound`/`upperBound`를 검사하지 않는다:
`LayoutOptionValidator`·`GraphValidator`를 쓰는 곳은 Eclipse의 `DiagramLayoutEngine`(`elk.validateOptions`/`elk.validateGraph`를
읽음)뿐이고, `RecursiveGraphLayoutEngine.layout`은 `DeprecatedLayoutOptionReplacer`와 `LayoutAlgorithmResolver`만 적용한다.
elkjs도 같은 엔진이다. elk-rs는 엔진에 두 validator를 넣었고(`validateOptions` 기본 `true`), elk-lean은 그것을 이어받아
`force.iterations = 0`·rectpacking `desiredPosition < -1`·`aspectRatio <= 0` 같은 입력을 `GraphValidationException`으로 거부했다.
**결정**: Lean 엔진도 검증하지 않는다(`RecursiveGraphLayoutEngine.layout`). 범위 밖 값은 알고리즘까지 가서 Java와 같은 결과나
예외를 낸다: `force_iter0`(Java가 레이아웃, NaN 좌표 포함 — `tests/fixtures/force/force_iter0_seed3.expected.json`), rectpacking
음수 `desiredPosition`(작은 그래프는 레이아웃, SPV의 EMF 용량 AIOOBE 경로), DisCo `aspectRatio` 0/음수(17.1). validator 자체는
`Elk.Core.Validation`에 그대로 있다. 무작위 s·v·o·p 세트(19,802개)에는 범위 밖 옵션이 없어 출력이 바이트 동일하다.

### 18.4 재현하지 않는 것·남은 것

- **포트에 확장 간선이 둘 이상**: `applyLayout`은 `incomingExtensionsMapping`/`outgoingExtensionsMapping`(identity hash 키
  `HashMap<ElkEdge, …>`)의 첫 간선으로 포트 위치를 정한다. 같은 입력이 새 JVM에서 앞선 레이아웃 수에 따라 두 결과를 낸다(`c1/g0211`:
  0·3·20·1·2·7·13개 앞섬 → 두 결과). Lean은 삽입 순서. `c` 세트 31건(전부 이 경우).
- **병렬 스트림 예외 문구**: `computeIncidences`의 `StreamSupport.stream(..., true)`에서 술어가 던지면, 작업이 `ForkJoinPool` 작업자
  스레드에서 돌았을 때 `ForkJoinTask`가 다시 만든 예외가 전파된다: NPE는 메시지 없는 `java.lang.NullPointerException`(54건),
  IAE는 `IllegalArgumentException: java.lang.IllegalArgumentException: Passed edge is not 'simple'.`(12건). 호출 스레드에서 돌면
  원래 문구 — 스레드 경쟁이라 재현하지 않는다(Lean은 원래 문구).
- **확장 grid 경계 오류의 순서**: `DCComponent`의 요소는 `HashSet<DCElement>`(identity hash)라 어느 확장의 경계 오류가 먼저인지
  실행 맥락 의존(1건, 클래스는 같음).
- **Java layered의 P3 계수기 예외**(14건): DisCo의 `layered` 컴포넌트 레이아웃에서 Java가 `CrossingsCounter.countCrossingsOnPorts`의
  `BinaryIndexedTree.add` AIOOBE·`BetweenLayerEdgeTwoNodeCrossingsCounter.AdjacencyList`의 NPE를 낸다(같은 그래프를 엔진의 layered
  루트로 돌려도 같다) — layered P3 계수기의 일이라 이 라운드 밖(LM 담당 영역).
- 극단 aspect ratio의 OOM은 Java heap 설정 의존(17.1).

### 18.5 결과(시드 1~10; Java 기준값은 같은 입력)

| 세트 | 입력 | 둘 다 성공 | 정확 일치 전(`3d6242f`) → 후 | 1e-6 전 → 후 | 둘 다 예외 / 문구 같음 전 → 후 | Lean ok·Java 예외 전 → 후 |
|---|---:|---:|---:|---:|---:|---:|
| c | 6,000 | 5,104 | 1,154 → **5,073**(99.4%) | 1,263 → 5,073 | 627/607 → 882/815 | 269 → 14 |
| s | 6,000 | 1,205 | 1,197 → 1,197 | 1,197 → 1,197 | 4,792/4,787 → 같음 | 1 → 1 |
| v | 6,000 | 5,761 | 5,711 → 5,711 | 5,711 → 5,711 | 216/216 → 같음 | 11 → 11 |
| o | 6,000 | 5,236 | 5,224 → 5,224 | 5,227 → 5,227 | 745/745 → 같음 | 0 → 0 |
| p | 1,802 | 1,373 | 1,359 → 1,359 | 1,359 → 1,359 | 386/379 → 같음 | 42 → 42 |

s·v·o·p는 Lean 출력이 기준 바이너리와 바이트 동일(19,802개). `c` 세트의 남은 차이는 전부 17.4(31 + 67 + 14). DisCo fixture 58개는
Java로 다시 고정했다(Java와 같은 것 7 → 58: 레이아웃 42개 tol 0, 예외 16개 문구까지; `tests/fixtures/disco/README.md`,
`opt_java_status.tsv`의 `DIS` 행). 새 테스트 `disco.java`(`tests/fixtures/disco/java/` 32개: 이전 Lean이 Java와 달랐던 무작위 입력 25개와
aspect ratio 5개(이전 Lean은 검증으로 거부하거나 거대 grid 할당에서 멈춤), 회귀 검사 2개 — `hyperedge_fixed_c7_g0560`은 이전에도
DisCo 자신의 IAE로 같았고 루트 NPE 이식 뒤 `FixedLayoutProvider`의 IAE가 먼저여야 같다, `empty_grid_int_bounds`는 셀 크기 0이라
`int` 경계가 결과에 드러나지 않는다), Java 값으로 바꾼 기대값: polyomino 패킹 18개·기본 grid(`alg.common.polyomino.PolyominoCompactor`,
Java 프로그램 출력), `PlanarGrid` 경계·메시지·빈 `getFilledBounds`, DisCo 메타데이터(support 기본값, polyomino 옵션 등록), 옵션 수
247 → 251, 엔진이 `validateGraph`를 무시하는 것, DisCo 루트 포트 간선의 NPE, `force_iter0_seed3`(오류 → Java 레이아웃).

코퍼스(ELK Java 기준): Lean 출력 1,998개 기준 바이너리와 바이트 동일, 정확 일치 1878/119(집합 동일). elk-rs 보조: model
parity(1e-6) 1447/1447.

성능(`elk bench` 합성 26개, 기준 바이너리와 번갈아 5회, 중앙값): 기하평균 1.001배, 0.987~1.016배(잡음 범위 — 합성 시나리오에는
DisCo가 없고 바뀐 코드는 NaN·범위 밖 경로뿐). DisCo fixture 8개 × 20회 `elk batch`(번갈아 5회 중앙값): 1.94 s → 1.51 s(0.78배) —
큰 polyomino를 먼저 놓으면 뒤의 작은 것들이 시험하는 후보 위치가 줄어든다.

## 19. GS: greedy switch `addAdjacencyOf` NPE, 계층 임포트(model order·간선 순서·`NO_LAYOUT`), 외부 포트 위치 전달 (2026-11-01)

방법: 라운드 10 병합본(`299f2c9`, `elk_base`)과 Java 디버그 섀도 클래스(`BetweenLayerEdgeTwoNodeCrossingsCounter`에 누락 키
출력)로 원인을 확인하고, 계층 model order 탐색용 새 생성기 `scripts/gen_hierarchical_mo_graphs.py`(INCLUDE_CHILDREN 2~3단,
model order 옵션·`NO_LAYOUT`(복합 포함, `ALGORITHM` 있음/없음)·`noModelOrder`·그룹 id·층 제약·self loop·계층 횡단 간선; 시드 1·2 ×
2,000)를 수정하지 않은 ELK Java 0.12.0과 대조했다.

### 19.1 greedy switch `BetweenLayerEdgeTwoNodeCrossingsCounter.AdjacencyList.addAdjacencyOf` NPE

Java는 자유 층의 이웃 층에서 서쪽 층의 **동쪽** 포트와 동쪽 층의 **서쪽** 포트만 번호(`portPositions`)를 매기고,
`addAdjacencyOf`는 `int adjacentPortPosition = portPositions.get(adjacentPort)`로 언박싱한다. 포트 제약이 없는 노드
(`UNDEFINED` → `FREE`, `NON_FREE_PORTS` 없음)의 포트가 들어오는 간선 1개·나가는 간선 1개를 가지면(`HYPEREDGES`도 없음)
`InvertedPortProcessor`가 예약되지 않고, `PortSideProcessor`가 순유량 0으로 그 포트를 `WEST`에 둔다. 그 포트의 나가는 간선이
다음 층으로 가고 다음 층에 노드가 둘 이상이면 greedy switch가 그 층의 두 노드를 비교할 때 서쪽 인접 리스트가 번호 없는 서쪽
포트를 만나 `NullPointerException: Cannot invoke "java.lang.Integer.intValue()" because the return value of
"java.util.Map.get(Object)" is null`(다음 층에 노드가 하나면 greedy switch가 비교하지 않고 P3 계수기의 AIOOBE가 먼저 난다 — LM에서
이미 일치). Lean(elk-rs 상속)은 그 간선을 건너뛰었다 → `AdjacencyList.new`가 `Option`을 돌려주고 `ensureAdjacencies`가 Java처럼
첫 질의(그 쪽의 리스트를 처음 만들 때)에 같은 문구를 던진다. 대상: 무작위 v·d·p `9/g0273`, 변형 세트 4(`v9_g0273`), DisCo 세트 8
(`c3/g0142, c4/g0120, c5/g0198, c6/g0075, c6/g0407, c7/g0589, c9/g0091, c10/g0306`). DIS가 함께 적은 나머지 6건
(`c1/g0007, c4/g0451, c5/g0244, c6/g0078, c6/g0208, c9/g0494`)은 같은 원인의 P3 계수기 AIOOBE로 LM 병합 뒤 이미 같은 문구다.

### 19.2 계층 임포트의 노드 model order(과제 2)

Java `importHierarchicalGraph`는 노드를 하나의 BFS 큐로 읽으며(최상위 자식, 그다음 중첩 그래프를 얻은 노드의 자식) 하나의
인덱스로 번호를 매기고(`NO_LAYOUT` 확인 전이라 제외 노드도 번호를 쓴다), `MAX_MODEL_ORDER_NODES`·`CB_NUM_MODEL_ORDER_GROUPS`는
최상위 그래프에만 전체 수로 둔다 → `assignHierarchicalNodeModelOrders`로 이식(중첩 그래프는 LM의 `maxModelOrderNodesNull`).
관찰 가능한 차이 탐색: 변형 세트(npa/npb/mob/p3a 6,000여 개), 무작위 p 세트, 새 생성기 시드 1(2,000개) 모두 이 변경만으로는 Lean
출력 바이트 동일(한 그래프 안의 상대 순서는 같고, 중첩 그래프의 절대값을 읽는 Java 지점은 전부 `MAX_MODEL_ORDER_NODES` null NPE가
먼저다). 코퍼스도 바이트 동일.

### 19.3 생성기가 찾은 계층 임포트·주변의 결정적 Java 차이

| 차이 | Java | 수정 |
|---|---|---|
| 계층 간선의 순서와 범위 | 모든 노드를 만든 뒤 간선을 그래프 BFS 순서(최상위 먼저)로 읽는다; 큐에는 같은 실행에 속한 자식 그래프(`usesElkLayered` && `INCLUDE_CHILDREN`)를 `NO_LAYOUT`이나 중첩 그래프 여부와 무관하게 넣는다 → `NO_LAYOUT` 복합 노드 안의 간선은 끝 노드를 찾지 못해 "could not be found" `UnsupportedGraphException` | `importHierarchicalEdges`(elk-rs: 층마다 노드 직후, 깊은 층 먼저; 자식 층이 부모의 inside self loop을 한 번 더 가져와 두 번 임포트) |
| `NO_LAYOUT` + `ALGORITHM` 자식 | `LayoutAlgorithmResolver`가 `NO_LAYOUT` 노드를 건너뛰어 `RESOLVED_ALGORITHM`이 없으므로 `!algorithmData.equals(null)` → 엔진이 분리(`SEPARATE_CHILDREN`), 안쪽은 아무도 배치하지 않음 | `RecursiveGraphLayoutEngine`의 algorithm switch `getD true`, 임포터의 `partOfSameLayoutRun` |
| 외부 포트 위치 전달 | `graphLayoutToNode`가 `getExternalPortPosition` 값을 그대로 부모 포트에 둔다 | elk-rs의 "pure self loop" 동쪽 더미 y 보정 제거(복합 노드의 바깥 간선 포트가 계층 포트 옆으로 옮겨졌다; 최소 예: 복합 `b`(자식 `c`)와 `b→a`, `c→a`) |
| BF/DF model order 층 배정 | "requires all real nodes to have a model order"는 정렬 비교자에서만 → 실노드가 둘 이상일 때만 | 미리 검사하던 것을 비교자 의미로 |
| `sortPortsByDummyPositionsInLastLayer` | 마지막 층을 외부 포트 더미로 가정하고 `(LPort) ORIGIN` → 일반 노드면 `ClassCastException`(`ElkNodeImpl` … `loader 'app'`), 층을 넘으면 `ArrayIndexOutOfBoundsException` | 같은 예외(elk-rs: 포트가 아닌 origin은 소비하지 않고 넘어감; 범위 밖 문구의 클래스도 `ArrayIndexOutOfBoundsException`으로) |

새 생성기 결과(Java와 같은 것 = 정확 일치 레이아웃 또는 같은 예외 문구):

| 시드 | 입력 | 기준(`299f2c9`) | GS | 나빠진 것 |
|---|---:|---:|---:|---:|
| 1 | 2,000 | 1,656 | **1,993** | 0 |
| 2 | 2,000 | 1,644 | **1,985** | 0 |

남은 22개: Java 실행 컨텍스트 의존(단일 JVM·역순 실행에서 Java 결과가 바뀜, 메시지 없는 `ArrayIndexOutOfBoundsException` = HotSpot
fast throw, 계층 그래프 처리 순서에 따른 `LGraph`/`LEdge` NPE 순서), Java `StackOverflowError` vs Lean timeout, 그리고 결정적인 소수
(시드 1 `h0008` 드리프트, `h1104`/`h1314`의 P3 계수기 AIOOBE 인덱스(BF model order 층 배정의 역방향·층 내 간선), 시드 2 드리프트
몇 개와 `h0323`의 예외 순서) — 다음 라운드 후보.

### 19.4 결과

무작위 세트(시드 1~10; Java 기준값은 같은 입력, Lean 출력은 기준 바이너리와 비교): 바뀐 입력은 19.1의 NPE 11개뿐
(`c` 8, `v`·`d`·`p` 각 1) — 정확 일치 수 불변(s 1,197·v 5,711·d 5,711·o 5,224·p 1,359·c 5,073), Java 예외 문구 일치 v 226 →
**227/227**·d 226 → 227·p 426 → 427·c 821 → 829(남은 67은 17.4의 병렬 스트림 워커 문구), s 4,793/4,793 그대로. 변형 세트 npa
139 → 140·npb 605 → 606·mob 84 → 85·p3a 412 → 413(각각 `v9_g0273`), 정확 일치 수 불변(1,317·1,143·1,698·1,354), 다른 입력 바이트 동일.
`tests/random_parity/report.md` 갱신(기본 실행 s,v).

코퍼스(ELK Java 기준): Lean 출력 1,998개, elk-rs trace·Java trace용 Lean trace 모두 기준 바이너리와 바이트 동일, 정확 일치
1878/119(집합 동일), Java 단계별 trace 1,743/1,997(같음). elk-rs 보조: model parity(1e-6) 1447/1447, strict trace 1447/1447.
합성 26개 Lean 출력 바이트 동일. `lake build` 경고 0, `lake test` 17,088 통과/0 실패(기준 17,077 + `gs.*` 11; elk-rs 구조를 고정하던
단위 테스트 `layered.import.hierarchical`(간선 순서·inside self loop 2회 임포트)와 `hierarchicalNodeResizing.selfLoops`(y 보정)는 Java
값으로 바꿈).

성능(`elk bench --scenarios layered_medium,crossmin_layer_sweep,hierarchy_nested --iterations 20 --warmup 3`, 기준 바이너리와
번갈아 5회, 중앙값): `crossmin_layer_sweep` 1.001배, `layered_medium` 1.001배, `hierarchy_nested` 1.005배 — 잡음 범위.

### 19.5 남은 것

- 새 생성기 시드 1·2의 결정적 소수(19.3 끝): 드리프트 몇 개(시드 1 `h0008`), BF model order 층 배정 뒤 P3 계수기 AIOOBE의 인덱스
  (`h1104`·`h1314`), 예외 순서(`h0323`). 생성기는 `run_random_java_parity.sh`에 편입하지 않았다(수동: 생성 → `ElkJavaBaseline` → 비교).
- 계층 임포트의 노드 변환 순서는 여전히 재귀(DFS)다(Java: BFS). arena id 순서만 다르고 관찰된 출력 차이는 없다.

## 20. HMO: 계층 model order 세트 `h`의 남은 차이, 파이프라인 편입, 계층 노드 변환 BFS (2026-11-01)

방법: 라운드 11 병합본(`78f1794`, `elk_base`)으로 GS의 생성기(`scripts/gen_hierarchical_mo_graphs.py`) 시드 1·2 × 2,000을 새
파이프라인 세트 `h`로 돌리고(`--sets h --seeds 1,2 --count 2000`; Java는 세트마다 JVM 하나), Java와 다른 입력마다 Java를 여러
실행 컨텍스트 — 파이프라인의 순방향 배치 JVM, 세트 전체의 역순 배치 JVM(`ElkJavaBaseline --reverse true`), 입력마다 새 JVM,
새 JVM + identity hash 생성 방식 `-XX:+UnlockExperimentalVMOptions -XX:hashCode=0/2/3/4`, 새 JVM + GS의 플래그
(`-Xss64m --add-opens java.base/java.util=ALL-UNNAMED`) — 에서 다시 돌려 비교했다. 컨텍스트마다 Java 결과가 갈리면 "Java 실행
컨텍스트 의존", 모두 같으면 결정적 차이로 보고 Java 디버그 섀도 클래스(`BKCompactor`·`SortByInputModelProcessor`에 출력,
하네스에 스택 트레이스; 서명 없는 ELK jar 사본 앞에 둠)와 Java/Lean 단계별 trace로 원인을 찾았다. 고정 입력은 Java 결과를
유지하는 탐욕 축소(노드·간선·옵션 제거)로 줄여 `tests/fixtures/hmo/`에 두었다(`Tests/Api/RandomJavaHmo.lean`, `hmo.*` 8개).
`-XX:hashCode` 모드는 identity hash 의존을 가장 싸게 드러낸다: 같은 입력이 모드에 따라 다른 결과를 내면 그 차이는 Java 쪽
`HashMap`/`HashSet`(키가 `hashCode`를 재정의하지 않은 객체) 순회 순서에서 온다.

### 20.1 GS가 남긴 22개와 기준 바이너리의 분류

GS의 수치(시드 1 1,993/2,000·시드 2 1,985/2,000)는 GS의 Java 실행(위 GS 플래그, 다른 입력 경로) 기준이고, 기준 바이너리로 같은
Java 출력과 비교하면 22개가 그대로 재현된다. 같은 입력을 파이프라인 JVM으로 다시 돌리면 Java 자신이 레이아웃 96개·예외 문구
여러 개를 다르게 내므로 파이프라인 기준 불일치는 112개(시드 1 50·시드 2 62)였다. 분류(기준 바이너리, 시드 1·2):

| 분류 | 입력 | 처리 |
|---|---|---|
| 결정적: `SCCNodeTypeCycleBreaker`의 선호 group id 비교 | 시드 1 `h0008`(드리프트)·`h1104`(Java "could not be found" vs Lean AIOOBE: 분리 레이아웃 `n13`에서 Lean만 실패)·`h1314`(AIOOBE 인덱스), 시드 2 `h0234`·`h0732`·`h1489`·`h1949`(드리프트)·`h0323`(BF model order 예외 vs Lean `LAST_SEPARATE` 예외) | 20.2 |
| 결정적: BK 클래스 그래프 순환 | 시드 2 `h0687`(Java NPE vs Lean AIOOBE, SCC 수정 뒤에는 Lean 레이아웃) | 20.3 |
| 결정적: Coffman–Graham DFS의 순환(Java `StackOverflowError`, Lean timeout) | 시드 1 `h1143`, 시드 2 `h0207` | 20.4 |
| Java 실행 컨텍스트 의존 — 레이아웃 | 시드 1 44개·시드 2 51개(역순·새 JVM·GS 실행 중 둘 이상이 서로 다름; 시드 1 `h0916`은 세 컨텍스트가 모두 다름) | 문서화 |
| Java 실행 컨텍스트 의존 — 예외 | `h1/h1012`(예외 문구 속 `ElkNode` 좌표: 앞선 분리 레이아웃의 결과가 컨텍스트마다 다름), `h1/h1049`(`LGraph`/`LEdge` NPE: 기본 JVM은 `LGraph`, `-XX:hashCode=0/2/3/4`는 Lean과 같은 `LEdge`), `h2/h1257`·`h2/h1429`·`h2/h1688`·`h2/h1921`(메시지 없는 `ArrayIndexOutOfBoundsException` = HotSpot fast throw; 새 JVM·역순에서는 Lean과 같은 `Index i out of bounds for length n`) | 문서화 |

SCC 수정 뒤에는 컨텍스트 의존이던 `h1/h0916`·`h1/h1177`·`h2/h0284`·`h2/h1731`도 파이프라인 Java와 같아졌다(Java의 여러 결과 중
하나가 SCC 차이로 가려져 있었다). `h1049`는 중첩 그래프의 `SortByInputModelProcessor`에서 층마다 노드 정렬(비교자가 중첩 그래프의
`MAX_MODEL_ORDER_NODES` = `null`을 언박싱 → `LGraph` NPE)과 포트 정렬 전처리(`longEdgeTargetNodePreprocessing`이 model order 없는 간선을
언박싱 → `LEdge` NPE) 중 어느 쪽이 먼저 오는지가 Java 쪽 층 내용에 달려 있고, 그것이 identity hash 생성 방식에 따라 바뀐다(노드 8개
축소본도 기본 JVM `LEdge`, 서명 없는 jar 경로·`-XX:hashCode=0` `LGraph`, `hashCode=2/3/4` `LEdge`).

레이아웃이 갈리는 입력에서 Java 두 컨텍스트(배치 trace 실행 vs 새 JVM trace 실행)의 단계별 trace를 맞대 보면 첫 차이는
`SelfLoopRouter`(9)·`InLayerConstraintProcessor`(4)·`SelfLoopPortRestorer`(2)였다(시드 1의 44개 중 두 traced 컨텍스트에서 최종 결과가
갈린 16개; 1개는 trace에 없는 중첩 그래프에서) — 코퍼스의 self-loop 실행 컨텍스트 의존(identity hash 순서)과 같은 범주다.

### 20.2 `SCCNodeTypeCycleBreaker`: 선호 group id는 박싱된 `Integer`의 `==`

Java `findNodes`는 `min.getProperty(CYCLE_BREAKING_ID) == graph.getProperty(CB_PREFERRED_SOURCE_ID)`(대상 쪽도 같음)로 `Integer`
객체를 비교한다. `cbPreferredSourceId`/`cbPreferredTargetId`는 기본값이 없어 설정하지 않으면 `null`이고 절대 같지 않으므로 연결도
(최소 노드의 들어오는 간선 수 vs 최대 노드의 나가는 간선 수)가 정한다. elk-rs(그리고 Lean)는 `unwrap_or(0)`으로 두 선호 id를 `0`으로
두어, 기본 옵션의 모든 강연결 성분이 "선호 source" 가지(최소 노드의 들어오는 간선 뒤집기)로 갔다. 설정된 값끼리는 JSON 임포트가
노드와 그래프에서 따로 `Integer.valueOf`를 부르므로 `Integer` 캐시 `[-128, 127]` 안에서만 같은 객체다 → `javaBoxedIdEq`. 고정:
`scc_node_type_no_preferred_ids`(3-순환, 시드 1 `h1104`의 분리 레이아웃 `n13`에서 축소), `..._preferred_source_uncached`(둘 다 `200` →
연결도), `..._cached`(둘 다 `1` → 선호 source; 이전과 같은 결과). trace 단계 이름은 Java 클래스 이름 `SCCNodeTypeCycleBreaker`다
(TRN에서 elk-rs 이름 `SccNodeTypeCycleBreaker`에서 변경; `scripts/compare_phase_traces.py`가 별칭 표로 elk-rs 이름과 맞춘다. 코퍼스에는 이 전략이 없다).

### 20.3 `BKCompactor`: 놓이지 않은 클래스의 `null` 시프트

`placeClasses`는 클래스 그래프를 들어오는 차수 0인 클래스부터 위상 순서로 훑는다. 클래스 그래프에 순환이 있으면 순환 위·뒤의
클래스는 한 번도 꺼내지지 않아 `classShift == null`로 남고, Java는 그 `null`을 `bal.shift[sink.id]`에 쓴다. 최종 좌표 루프가 블록
루트마다 `double sinkShift = bal.shift[bal.sink[v.id].id]`로 언박싱하므로 `NullPointerException: Cannot invoke
"java.lang.Double.doubleValue()" because "bal.shift[bal.sink[v.id].id]" is null`. elk-rs/Lean은 정의된 시프트만 쓰고 초기값(±∞)을
남겨 레이아웃을 끝냈다 → `placeClasses`가 놓이지 않은 sink 집합을 돌려주고, 최종 루프 전에 그 sink를 가진 블록 루트가 있으면 같은
문구를 던진다(루프의 y 대입은 루트·sink를 바꾸지 않으므로 미리 검사해도 같다). 어떤 클래스가 남는지는 `sinkNodes`(`HashMap`)
순회 순서와 무관하므로 결정적이다(7개 컨텍스트 동일). 고정: `bk_class_graph_cycle_npe`(시드 2 `h0687`에서 축소, 노드 8개;
`SCC_NODE_TYPE` + `BF_MODEL_ORDER`의 계층 그래프, 루트 그래프의 `UP`/`RIGHT` 정렬에서 실패).

### 20.4 층 배정의 무한 재귀: Coffman–Graham과 longest path

`MODEL_ORDER` 등 model order 순환 제거기는 `noModelOrder` 노드가 낀 순환을 남긴다. Coffman–Graham의 transitive reduction
`dfs(start, v)`와 `LongestPathLayerer`/`LongestPathSourceLayerer`의 `visit(node)`는 노드를 반환할 때만 표시하므로, 실행 중인 노드를 다시
만나면 같은 재귀를 끝없이 되풀이해 `java.lang.StackOverflowError`. Lean의 명시적 스택은 같은 경로를 끝없이 쌓아(메모리 증가) 15초
제한에 걸렸다 → 실행 중인 노드를 다시 만나면(그 뒤 Java는 반드시 같은 순환을 되풀이한다) `java.lang.StackOverflowError`를 던진다
(mrtree `NodePlacer.secondWalk`와 같은 방식; 파이프라인은 Java와 같은 `overflow`로 센다). 고정: `coffman_graham_cycle_stack_overflow`
(시드 1 `h1143`에서 축소: 노드 2개, 한쪽이 `noModelOrder`인 2-순환), `longest_path_cycle_stack_overflow`(시드 6 `h0433`에서 축소). 대상:
시드 1·2 × 2,000의 `h1/h1143`·`h2/h0207`(Coffman–Graham), 시드 1~10 × 600의 `h2/h0207`·`h9/h0113`·`h9/h0162`·`h10/h0387`·`h10/h0394`
(Coffman–Graham)과 `h3/h0214`·`h6/h0433`·`h7/h0268`(longest path).

### 20.5 시드 1~10 × 600에서 더 찾은 결정적 차이

| 차이 | Java | 수정 | 대상 |
|---|---|---|---|
| 계층 레이어 스윕의 빈 중첩 그래프 | `sweepInHierarchicalNode`가 `nestedGraphNodeOrder[startIndex][0]`을 검사 없이 읽는다: 층이 없으면 `Index 0`(역방향 `-1`) `out of bounds for length 0`, 첫 층이 비면 `Index 0 out of bounds for length 0` | 같은 `ArrayIndexOutOfBoundsException`(elk-rs는 첫 층 정렬을 건너뛰고 빈 그래프를 훑었다) | P3 변형 `p2/v2_g0045`(GS 이전부터 Lean ok / Java 예외; 고정 `hierarchical_sweep_empty_nested_order_aioobe`) |
| 계층 간선의 좌표계 오프셋 합 | `calculateHierarchicalOffset`: `result.add(position).add(offset).add(padding.left, padding.top)`(왼쪽부터) | 같은 순서로 더함(elk-rs는 세 항을 먼저 묶어 마지막 비트가 달랐다) | `h3/h0190`(두 단계 위 그래프 좌표의 간선, 1e-6 안 차이; 고정 `hierarchical_edge_offset_summation`) |

### 20.6 계층 노드 변환 순서(과제 3)

`importHierarchicalGraph`의 노드 루프를 Java처럼 하나의 BFS 큐로 바꿨다(최상위 자식, 그다음 중첩 그래프를 얻은 노드의 자식을 그
노드를 변환할 때 큐 뒤에 붙임; 부모 `LNode`의 중첩 그래프에 변환; 중첩 그래프의 `DIRECTION`은 최상위 그래프 값). 그래프마다 노드가
만들어지는 순서는 같고 arena의 `LNode`/`LGraph` 번호만 달라진다(단위 테스트 `layered.import.hierarchical`의 노드 id를 Java 순서로
바꿈). 바이트 비교(수정 20.2~20.4를 넣은 바이너리 vs 여기에 BFS를 더한 바이너리): 코퍼스 Lean 출력 1,997개와 Java trace용 Lean
trace 196,407개 동일, 합성 26개 동일, 무작위 `v`·`p`(시드 1~10; BFS 바이너리와 기준 바이너리 비교) 동일, `h` 시드 1~10 × 600·시드 1·2 × 2,000과 변형 세트
npa/npb/mob/p3a(7,208개) 16,008개 동일 → 관찰 가능한 차이 없음(Java 실행 불필요).

### 20.7 파이프라인 세트 `h`

`run_random_java_parity.sh --sets h`: gen 단계가 `gen_hierarchical_mo_graphs.py <dir> <count> <seed>`를 부르고(그래프 k는 COUNT와
무관하므로 `--count 600`은 GS의 2,000개 세트의 앞부분), Java·Lean·분류·보고서의 세트별/`h (all)` 행은 다른 세트와 같다. `TESTING.md`
2B와 `scripts/README.md`에 적었고, 추적 전체 실행은 `--sets s,v,d,o,p,c,h`다. 기본 시드 1~10 × 600(6,000개)은 Java 약 1분(JVM 둘),
Lean 약 70초(3 프로세스), 보고서 수십 초다. 입력의 약 62%는 양쪽 모두 예외(간선 "could not be found", model order 층 배정의 요구
조건, `LAST_SEPARATE` 등)로 끝나고 그 문구를 비교한다.

### 20.8 결과

`h` 세트(Java와 같은 것 = 정확 일치 레이아웃, 같은 예외 문구, 양쪽 `StackOverflowError`; Java는 파이프라인 배치 JVM):

| 세트 | 입력 | 기준(`78f1794`) | HMO | 나빠진 것 | 남은 것 |
|---|---:|---:|---:|---:|---|
| 시드 1 × 2,000 | 2,000 | 1,950 | **1,956** | 0 | 44, 모두 Java 실행 컨텍스트 의존 |
| 시드 2 × 2,000 | 2,000 | 1,938 | **1,947** | 0 | 53, 모두 Java 실행 컨텍스트 의존 |
| 시드 1~10 × 600 | 6,000 | 5,886 | **5,901** | 0* | 99, 모두 Java 실행 컨텍스트 의존 |

GS의 Java 출력 기준으로는 시드 1 1,993 → **1,999**(남은 `h1049`는 20.1의 NPE 순서), 시드 2 1,985 → **1,992**. *시드 5 `h0520`은
기준 바이너리가 파이프라인 Java와 같았지만 SCC 수정 뒤에는 새 JVM·`-XX:hashCode=2/3/4`·GS 플래그의 Java와 같고 파이프라인 JVM과만
다르다(컨텍스트 의존). 남은 99개는 8개 컨텍스트(파이프라인 배치·역순 배치·새 JVM·`hashCode` 4종·GS 플래그) 중 Java 결과가 갈리는
입력이고 Lean은 그중 하나 이상과 같다. 시드 1~10 × 600의 세부: 정확 일치 2,175/2,271(1e-6 2,175), 예외 문구 3,718/3,721(남은 3개는
메시지 없는 fast throw AIOOBE 2·컨텍스트에 따라 바뀌는 NPE 1), `StackOverflowError` 8/8, timeout 0.

다른 세트: 무작위 `v`(시드 1~10) Lean 출력 바이트 동일(정확 일치 5,711/5,761, 예외 문구 227/227), `p`는 `p2/v2_g0045`(20.5)만
바뀌어 Lean ok/exc 1,373/428 = Java(이전 1,374/427), 예외 문구 427/428(남은 1개 `p3/v3_g0491`은 fast throw AIOOBE), 정확 일치
1,359/1,373 그대로; `p`의 남은 15개도 모두 컨텍스트 의존이다(`p9/v9_g0493`은 8개 컨텍스트에서 같았지만 `-XX:hashCode=1 -Xint`에서는
Lean과 같고, 원인 단위 `n4_n2`만 떼면 `SelfLoopRouter`의 self-loop 쪽이 `hashCode` 모드마다 바뀐다). 코퍼스(ELK Java 기준): Lean 출력 1,997개(1개는 양쪽 예외)와 Java trace용 Lean trace 모두 기준 바이너리와 바이트
동일, 정확 일치 1878/119(드리프트 집합 동일), Java 단계별 trace 1,743/1,997(같음). 합성 26개 바이트 동일(23/3). elk-rs 보조: model parity(1e-6) 1447/1447, strict trace 1447/1447.
`lake build` 경고 0, `lake test` 17,096 통과/0 실패(기준 17,088 + `hmo.*` 8; `layered.import.hierarchical`의 노드 id 6개는 BFS 순서로 바꿈).
성능(`elk bench --scenarios hierarchy_nested,hierarchy_flat,layered_medium --iterations 20 --warmup 3`, 기준 바이너리와 번갈아 5회,
중앙값): `hierarchy_flat` 0.998배, `layered_medium` 0.997배, `hierarchy_nested` 1.026배 → `hierarchy_nested`만 `--iterations 50`으로
7회 다시 재면 최종 1.000배(BFS만 넣은 중간 바이너리 1.004배) — 잡음 범위.

### 20.9 남은 것

- 재현하지 않는 것(Java 실행 컨텍스트 의존): `h` 세트의 self-loop 처리 순서(`SelfLoopRouter`·`SelfLoopPortRestorer`)와 node
  promotion에서 갈리는 레이아웃, 메시지 없는 fast throw AIOOBE, 컨텍스트에 따라 순서가 바뀌는 `LGraph`/`LEdge` NPE, 앞선 분리
  레이아웃 결과가 들어가는 예외 문구 좌표(`h1/h1012`).
- trace 단계 이름: TRN에서 elk-rs 이름(`BfsNodeOrderCycleBreaker`·`DfsNodeOrderCycleBreaker`·`SccNodeTypeCycleBreaker`·`ScConnectivityCycleBreaker`·`HypernodeProcessor`)을
  Java 클래스 이름(`BFSNodeOrderCycleBreaker`·`DFSNodeOrderCycleBreaker`·`SCCNodeTypeCycleBreaker`·`SCConnectivity`·`HypernodesProcessor`)으로 바꿨다.
  elk-rs trace 비교는 `scripts/compare_phase_traces.py`의 `_PROCESSOR_ALIASES` 별칭 표가 양쪽을 Java 이름으로 정규화한다.
- `LongestPathLayerer`류에서 `LNode.id`가 범위를 벗어나는 경우(Java는 `nodeHeights[node.id]`에서 AIOOBE) — 관찰된 입력 없음.

## 21. COV: layered 커버리지 세트 `w` — wrapping·comment box·hypernode·edge label·spline·BK 정렬·merged edge (2026-11-01)

방법: 코퍼스(1,998개)와 무작위 세트 s/v/d/o/p/c/h는 wrapping(0개)·hypernode(0개)·label management(0개)·comment box(5개)·inline
edge label(1개)을 거의 다루지 않고, 바로 그 영역의 Lean 모듈 17개가 "elk-rs의 Java 차이를 따른다"는 주석을 달고 있었다. 새 생성기
`scripts/gen_wrapping_graphs.py`(파이프라인 세트 `w`, `--sets w`)로 시드 1~10 × 600 = 6,000개의 layered 그래프를 만들었다. 옵션 id는 Java
id이고 JSON 경로는 범위를 검사하지 않으므로 범위 밖·퇴화 값을 일부러 뽑는다: wrapping(`wrapping.strategy` SINGLE_EDGE/MULTI_EDGE/OFF,
`cutting.strategy` ARD/MSD/MANUAL, `msd.freedom` −5~10, `correctionFactor` 0·−1·1e-9 포함, `additionalEdgeSpacing`, `multiEdge.improveCuts`/
`distancePenalty`/`improveWrappedEdges`, `validify.strategy`, `elk.aspectRatio` 0·−1·1e-6·1e9 포함, wrapping 그래프의 70%는 경로 모양),
comment box(노드·네 변 포트에 한 간선, 두 노드, 사슬, 연결 없음), hypernode(여러 간선, 대개 직교 라우팅), edge label(inline,
HEAD/CENTER/TAIL, side selection, center label placement strategy, 간선당 1~3개, self loop 라벨), 노드·포트 라벨 배치, spline
(CONSERVATIVE/SLOPPY, `sloppy.layerSpacingFactor` 0·음수 포함), BK `fixedAlignment` 전 값·`edgeStraightening`, `mergeEdges`/
`mergeHierarchyEdges`(15%는 `INCLUDE_CHILDREN` 복합 자식과 계층 간선), thoroughness(0·−1 포함), edge thickness, 그리고 그래프의 3.5%에
Java JSON 임포터가 받지 않는 `OBJECT` 옵션 하나(`wrapping.cutting.cuts`·`wrapping.validify.forbiddenIndices`·`labels.labelManager`·
`cmEnforcedGroupOrders`). `STRETCH_WIDTH` 층 배정은 이 그래프들에서 Java와 Lean 모두 끝나지 않는 경우가 많아(첫 시험의 시드 1에서
12개) 뽑지 않는다. 그래프 k는 COUNT와 무관하다(그래프마다 `random.Random("seed/k")`). Java와 다른 입력마다 Java/Lean 단계별 trace로 첫
차이 프로세서를 찾고, Java 쪽 원인은 스택 트레이스 하네스(`ElkGraphJson` + `RecursiveGraphLayoutEngine`, 실패 시 프레임 25개)로
확인했다. Java 실행 컨텍스트 의존 여부는 §20의 컨텍스트(입력마다 새 JVM, `-XX:+UnlockExperimentalVMOptions -XX:hashCode=0/2/3/4`,
`-Xint`)에 더해 **같은 JVM에서 다른 입력을 먼저 배치**하는 방법으로 갈랐다: identity hash는 스레드별 생성기의 상태로 정해지므로 앞선
입력이 바뀌면 같은 입력의 Java 결과가 바뀐다. 고정 입력은 Java 결과와 "COV 이전 바이너리 ≠ Java"를 유지하는 탐욕 축소(노드·간선·
포트·라벨·옵션 제거, 후보마다 한 JVM 배치)로 줄여 `tests/fixtures/cov/`에 두었다(`Tests/Api/RandomJavaCov.lean`, `cov.java` 14개).

### 21.1 결정적 차이와 수정(전부 ELK Java가 기준)

| 차이 | Java | 수정(모듈) | 고정 |
|---|---|---|---|
| `OBJECT` 옵션의 JSON 파싱 | `LayoutOptionData.parseValue` → `createDataInstance`가 `IDataObject`가 아닌 클래스(`List`, `ILabelManager`, `ITopdownSizeApproximator`, `LayoutAlgorithmData`, DisCo debug)에 `IllegalStateException: IDataType class expected for layout option <Java id>`(값이 `null`/빈 문자열이 아니면 언제나; `JsonImporter.setOption`은 잡지 않는다) | 같은 예외(`Elk/Json/Importer.lean`; 메시지의 id는 Java id `org.eclipse.elk.layered.*`). 결과: manual cuts·forbidden indices·label manager는 JSON으로 설정할 수 없다 | `object_option_cuts`, `object_option_label_manager`; `core/topdown_box` 입력에서 `sizeApproximator` 제거(출력 불변) |
| layered `ASPECT_RATIO` 기본값 | `Layered.melk`의 `1.6f` → `double` `1.600000023841858` | `LayeredOptions.ASPECT_RATIO_DEFAULT`를 wrapping `GraphStats`(elk-rs `1.0`)와 컴포넌트 배치 3곳(`1.6`)에 사용 | `wrapping_default_aspect_ratio` |
| `BreakingPointInserter.applyCuts` | `ListIterator.add`로 넣은 두 층을 건너뛰고 원래 층 번호로 `idx + 1 == cut` | 같은 순회(elk-rs는 넣은 층을 방문해 둘째 이후 컷을 2층씩 앞당김) | `apply_cuts_original_layer_indexes` |
| `ARDCutIndexHeuristic.getChunkCount` | `(int) Math.round(Math.sqrt(x / 0))` = `(int) Long.MAX_VALUE` = −1 행; 반올림은 `Math.round` | Java 반올림·`int` 절단(elk-rs: `longestPath`, 포화 `i32`) | 단위 테스트 |
| `MSDCutIndexHeuristic` | `1d / width`, `(1d / dar) / height`(IEEE), `Math.max/min`, `int` 랩 | 같은 산술(elk-rs: 분모 `0`이면 `+∞`) | — |
| `validifyIndexesLookingBack` | `current - Integer.MIN_VALUE`가 넘쳐 음수 → `-inf` 보초 자체를 컷으로 고름(이후 컷은 하나도 적용되지 않음) | `int` 랩 산술(elk-rs: 포화) | 단위 테스트 |
| `GraphStats` | 층 폭 `size.x + margin.right + margin.left + spacing`(이 순서), `Math.max`, `reduce` | 같은 덧셈 순서·`javaMax` | — |
| `SingleEdgeGraphWrapper` 조기 종료 | `currentAR = (maxWidth·L) / maxWidth`(`maxWidth = 0`이면 `NaN` → 끝내지 않음) | 같은 식(elk-rs: `0`) | — |
| `BreakingPointProcessor` | 역방향 개선 패스의 `Lists.reverse(nodes)` 결과를 버려 노드를 층 순서로 방문; `LNode.setLayer(int, Layer)`의 `IllegalArgumentException`/`IndexOutOfBoundsException`; 인덱스 밖 `get(i)` | 같은 순서와 예외(elk-rs: 노드 역순, 인덱스 클램프, `false`) | — |
| `BreakingPointRemover`(spline) | 시작 간선이 아닌 간선의 `null` 경로에 `addAll`/`forEach` NPE; 원래 간선의 bend point를 비움 | 같은 NPE·비움(elk-rs: 빈 목록, bend point 유지) | `breaking_point_remover_null_spline_route` |
| `CommentPreprocessor` 포트 스캔 | 라벨 붙은 `break portLoop`: 첫 북쪽 **또는 남쪽** 연결에서 끝 | 같음(elk-rs: 남쪽 뒤에도 북쪽을 찾음) | `comment_box_port_scan_south` |
| `EndLabelSorter` | 끝 라벨 셀을 간선별로 묶어 source port id·target node id·target port id(역순)로 정렬(id는 그래프 전체에 층/노드/포트 순서로 다시 매김); 정렬이 필요한 포트에 셀이 없으면 NPE | Java 클래스를 처음으로 이식(elk-rs는 label dummy의 `REPRESENTED_LABELS`를 텍스트로 정렬 = 정규 파이프라인에서 no-op) | `end_label_sorter_groups`, `end_label_sorter_port_without_cell` |
| `LabelDummySwitcher` | 사슬을 `iterator().next()`로 따라감(`NoSuchElementException`); 층 범위·`totalDummyCount`·중앙값·`ithDummyNode`가 `int`(wrapping으로 되돌아간 긴 간선에서 음수·부족 → `NegativeArraySize`/`ArrayIndexOutOfBounds`/`IndexOutOfBounds`/`subList`의 `IllegalArgument`) | 같은 `int` 의미론과 예외(elk-rs: 중단·포화 `usize`) | `label_dummy_chain_no_incoming_edge`, `label_dummy_switcher_turned_back_edge` |
| `LongEdgeJoiner.joinAt` | 들어오는 간선마다 남은 첫 나가는 간선을 `get(0)`(부족하면 `IndexOutOfBoundsException`) | 같음(elk-rs: `min(in, out)`) | `long_edge_joiner_fewer_outgoing_edges` |
| P3 초기화의 빈 층 | `LayerSweepTypeDecider.initAtLayerLevel`의 `nodeOrder[l][0]`(열린 간선 없는 컷의 빈 breaking point 층 → AIOOBE) | 같은 예외(`GraphInfoHolder`) | `layer_sweep_empty_layer` |
| `Spacings.getLocalSpacing` | 표에 옵션이 없는 노드 타입 쌍(`BREAKING_POINT` 등)은 `getProperty(null)` NPE | 같은 NPE(elk-rs: `UnspecifiedSpacingException`) | `spacing_null_option_breaking_point` |
| `PolylineEdgeRouter` | `Math.min(1, edgeSpacing / nodeSpacing)`(층간 노드 간격 0 → 1, 둘 다 0이면 `NaN`) | 같음(elk-rs: `0`) | `polyline_zero_node_spacing` |
| `LabelSideSelector` | 포트를 옮기는 두께는 `ORIGIN` 간선의 `EDGE_THICKNESS`; 면은 dummy에만 기록 | 같음 | 단위 테스트 |
| `HypernodesProcessor` | `KVectorChain.remove(Object)`: 같은 junction point 중 첫 하나만 제거 | 같음 | — |
| `BKNodePlacer` 균형 레이아웃 | `min`/`max` 시작값 `Integer.MAX_VALUE`/`MIN_VALUE`, `Math.min/max` | 같음 | — |
| `EndLabelPreprocessor` | `port.id = portIndex` | 같음(이전에도 관찰 불가) | — |

### 21.2 17개 모듈 주석의 정리

| 모듈 | 처리 |
|---|---|
| `Wrapping/BreakingPointInserter` | Java로 변경(`applyCuts`); `improveCuts`의 `null` 검사는 Java에도 있고 `null` hit는 생길 수 없음; 빈 층 배치 조기 반환은 도달 불가 |
| `Wrapping/BreakingPointProcessor` | Java로 변경(역방향 노드 순서, `setLayer`·`get(i)` 예외, 층 참조 비교); 병합 시 이웃 재연결은 관찰 불가(사슬은 머리부터 끝까지 병합되고 `next`만 따라감); 대상 층 범위 검사·누락 정보 중단은 도달 불가 |
| `Wrapping/CuttingUtils` | Java로 변경(음수 삽입 위치 → `IllegalArgumentException`, 파이프라인에서는 생기지 않음); 끝 노드·층 누락 가드는 도달 불가 |
| `Wrapping/SingleEdgeGraphWrapper` | Java로 변경(`NaN` 조기 종료, look-back `int` 랩); greedy의 음수 컷과 `performCuts` 범위 검사는 도달 불가(ARD/MSD 컷 ≥ 1, manual cuts는 JSON으로 설정 불가) |
| `Wrapping/ARDCutIndexHeuristic` | Java로 변경 |
| `Wrapping/MSDCutIndexHeuristic` | Java로 변경; 빈 폭 배열은 도달 불가 |
| `CommentPreprocessor` | Java로 변경 |
| `HypernodeProcessor` | Java로 변경 |
| `LabelManagementProcessor` | 공개 API에서 도달 불가: Java는 `LABEL_MANAGER`가 있을 때만 이 프로세서를 넣고(`GraphConfigurator`), 그 옵션은 JSON으로 설정할 수 없다(Java·elk-lean `IllegalStateException`, elkjs는 `ElkReflect` 팩토리가 없어 역시 예외; CLI의 JSON 경로도 같은 임포터). elk-rs 동작(중심 모드의 표현 라벨 없는 dummy)은 Lean 단위 테스트 경로에만 남음 |
| `LabelSideSelector` | Java로 변경(`ORIGIN` 두께, dummy에만 면 기록); 간선 라벨 간격은 Java도 처리 그래프의 값 |
| `EndLabelPreprocessor` | Java로 변경(`port.id`); 이전에도 관찰 불가(이후 프로세서는 포트 id를 스스로 매김) |
| `HyperedgeDummyMerger` | 관찰 불가: 성분 id는 별도 맵(이후 포트 id를 읽는 프로세서 없음), 병합된 노드의 `layer` 필드(간선 없음, 어느 층 목록에도 없음) |
| `Compaction/CompactionMetadata` | 표현 차이만(원점 측면 표 = Java `instanceof`) |
| `BK/BKNodePlacer` | Java로 변경 |
| `BK/ThresholdStrategy` | 도달 불가: 모든 층의 노드에 id가 매겨지고 층 노드의 간선은 층 노드에서 끝남 |
| `Splines/NubSpline` | 도달 불가: 파이프라인은 clamped spline(`new true 3`)과 `getBezierCP`만 쓴다; `insertKnot`(→ `getPointOnCurve`만)·unclamped `toBezier`(`NubsSelfLoop`, Java에서도 파이프라인 밖)는 elk-rs 그대로. `getTFromPolar`는 Java처럼 `0.0`에서 합산 |
| `RectPacking/P2Packing/Compaction` | 이미 Java와 같음(Java `|=`도 단락하지 않음); 주석을 바로잡음 |

### 21.3 Java 실행 컨텍스트 의존(재현하지 않음)과 Java 결함

- `SelfHyperLoop.slPortsBySide`는 `ArrayListMultimap`(`HashMap`)이고 키 `PortSide`는 identity hash를 쓰는 enum이다. 두 변 마주보기 self loop의
  두 경로 벌점이 같으면(포트 두 개짜리 노드에서는 늘 같다) `keySet()`의 첫 변이 경로(위/아래, 왼쪽/오른쪽)를 정한다. 그 순서는 PortSide
  상수 identity hash의 버킷 순서이고, 그 값은 처음 해시가 요청될 때까지 그 스레드가 만든 identity hash 수에 달려 있다: 같은 입력이 앞에
  배치된 입력과 hashCode 모드에 따라 결과를 바꾼다(`w5/w0430`: 앞선 입력 6가지에 결과 2가지, `w3/w0122`: 8가지에 4가지, 측정 하네스의
  새 JVM은 W, N, S, E 순서). Lean은 N, E, S, W 순서로 고정(elk-rs와 같음).
- `EndLabelSorter.createLabelGroups`의 `HashMap<LEdge, LabelGroup>`: 비교자가 같다고 보는 그룹(같은 포트 사이의 병렬 간선, `mergeEdges`)은
  identity hash 순서로 남는다. Lean은 셀 안 첫 라벨의 순서.
- 위 두 가지가 세트 `w`의 남은 레이아웃 차이 171개의 전부다: 154개는 Java를 다른 배치(trace 실행 JVM)로 다시 돌리면 단계별 trace까지
  Lean과 같고, 나머지 17개도 새 JVM·hashCode 모드·앞선 입력 중 적어도 둘에서 Java 결과가 갈린다(대부분 그중 하나가 Lean과 같다). 세트별로
  몰리는 것(`w3` 65·`w8` 53·`w10` 45, 다른 세트 0~3)도 같은 원인이다: 세트 JVM마다 PortSide 해시 순서가 하나로 정해진다.
- `PolylineEdgeRouter`에서 층간 노드 간격과 간선 간격이 모두 0이면 `0 / 0 = NaN` 좌표: Java `NaN`, Lean 출력 `null`(표기 차이, 2개).
- `w9/w0558`: Java는 메시지 없는 `NullPointerException`(HotSpot fast throw), Lean은 helpful NPE 문구(1개, 같은 예외 클래스).

### 21.4 결과(시드 1~10 × 600, Java는 세트마다 배치 JVM; 같은 Java 결과로 기준·COV 바이너리 비교)

| 세트 | Java ok/exc | 기준(`8508e66`) Lean ok/exc | COV Lean ok/exc | 정확 일치(양쪽 ok) | 예외 문구 일치(양쪽 예외) |
|---|---|---|---|---|---|
| w1 | 566/34 | 594/6 | 566/34 | 517/562 → **564/566** | 1/2 → **34/34** |
| w2 | 562/38 | 591/9 | 562/38 | 518/555 → **562/562** | 0/2 → **38/38** |
| w3 | 562/38 | 594/6 | 562/38 | 463/558 → **497/562** | 1/2 → **38/38** |
| w4 | 563/37 | 588/12 | 563/37 | 524/557 → **563/563** | 2/6 → **37/37** |
| w5 | 568/32 | 589/11 | 568/32 | 524/561 → **566/568** | 3/4 → **32/32** |
| w6 | 568/32 | 594/6 | 568/32 | 515/563 → **566/568** | 0/1 → **32/32** |
| w7 | 572/28 | 592/8 | 572/28 | 533/567 → **571/572** | 0/3 → **28/28** |
| w8 | 566/34 | 593/7 | 566/34 | 479/560 → **513/566** | 0/1 → **34/34** |
| w9 | 566/34 | 590/10 | 566/34 | 513/562 → **563/566** | 2/6 → **33/34** |
| w10 | 559/41 | 593/7 | 559/41 | 484/556 → **514/559** | 1/4 → **41/41** |
| 합 | 5,652/348 | 5,918/82 | **5,652/348** | 5,070/5,601 → **5,479/5,652** | 10/31 → **347/348** |

timeout·overflow는 양쪽 0. 결과(ok/예외) 불일치는 368개(Lean ok/Java 예외 317, Lean 예외/Java ok 51)에서 0개가 되었다. 남은 174개는
21.3의 컨텍스트 의존 171·`NaN` 표기 2·fast throw 1이다.

다른 검증(COV 바이너리 vs 기준 바이너리, 같은 Java 결과):
- 무작위 s/v/d/o/p/c/h(시드 1~10, 41,802개): Lean 출력(결과·예외 문구·레이아웃 바이트) **전부 동일** → 정확 일치 s 1,197·v 5,711·d 5,711·
  o 5,224·p 1,359·c 5,070·h 2,175, 예외 문구 4,793·227·227·745·424·813·3,716 그대로.
- 코퍼스(ELK Java 기준): Lean 출력 1,997개 바이트 동일, 정확 일치 1,878/119(드리프트 집합 `corpus_drift_set.txt`와 동일; comment box 모델
  5개도 바뀌지 않음). 합성 26개 바이트 동일(23/26).
