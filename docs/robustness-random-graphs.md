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
다음 라운드 브리프 단위: (1) `NML`(RJ1), (2) `DEF` 알고리즘별 기본값, (3) `SEC` 경로 없는 간선의 섹션, (4) `LNODE` layered 노드/포트,
(5) `LEDGE`/`LPOS` layered 라우팅·배치, (6) `POS:radial`.
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

### 10.2 결과(시드 1~10 × 600, s/v/d; RJ1 병합본 대비)

| 집합 | 정확 일치 전 → 후 | 1e-6 전 → 후 |
|---|---:|---:|
| s | 912 → 1,016 / 1,205 | 917 → 1,020 |
| v | 1,995 → **3,437** / 5,761 | 2,026 → 3,476 |
| d(기본값 명시) | 2,268 → 3,437 / 5,761 | 2,302 → 3,476 |
| o(새 옵션 집합, 시드 1~3 × 400) | 146 → 886 / 1,020·1,048 | 156 → 975 |

d 집합이 v와 같아졌다(기본값을 명시해도 결과가 바뀌지 않음 = Lean의 기본값이 Java와 같다). 분류(s+v+d): DEF 1,625 → 418
(mrtree 819 → 337, force 852 → 80, rectpacking 2 → 2), POS 2,481 → 566(stress 1,071 → 155, mrtree 792 → 322, force 416 → 78,
radial 280 → 12), NML 1,268 → 46. 남은 DEF/POS: mrtree는 거의 전부 `AVOID_OVERLAP` 간선 경로(elk-rs의 재구성 라우터, 253/337),
force/stress는 간선 라벨 위치만. 코퍼스 Java parity 1878/119(집합·차이 동일), elk-rs model parity 1447/1447.
