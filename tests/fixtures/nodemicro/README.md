# 노드 마이크로 레이아웃 픽스처 (ELK Java 기준)

`NodeMicroLayout`(포트 정렬 → `NodeLabelAndSizeCalculator.process` 전체 셀 시스템 → 노드 여백)과 Java의 노드 크기
검증을 ELK Java 0.12.0 결과로 고정한다. 테스트: `tests/lean/Tests/Api/NodeMicroLayout.lean`.

- 입력 `<name>.json`, Java 출력 `<name>.java.json`(`ElkJavaBaseline`, 미수정 Maven 아티팩트). 모든 그래프는 같은 네 자식
  노드를 쓴다: 라벨·포트가 있는 `FIXED_ORDER` 노드(변·`PORT_INDEX`·좌표 순 정렬), `MINIMUM_SIZE` +
  `MINIMUM_SIZE_ACCOUNTS_FOR_PADDING` + `COMPUTE_PADDING` 노드(Java는 가운데 행 너비 기여를 켜지 않아 너비 0), 표 형식
  노드 라벨 노드(`FORCE_TABULAR_NODE_LABELS`, Java는 열 너비 배열을 행마다 누적 갱신), `DISTRIBUTED` 포트 정렬·음수
  `borderOffset` 노드.
- 전체 일치(`nodemicro.java.layout`): `stress`, `rectpacking`, `rectpacking_child`(rectpacking 자식 그래프 — Java
  `MinSizePreProcessor`가 그래프 노드의 라벨·포트로 최소 크기를 잡는다), `box`, `fixed`(둘 다 패딩 기본값 15).
- 노드 크기·포트·라벨만 일치(`nodemicro.java.sizing`): `force`, `mrtree`, `radial`. 노드 배치는 알고리즘 몫이고 아직 Java와
  다르다(알고리즘별 옵션 기본값 등, 노드 마이크로 레이아웃 밖). 루트 패딩은 명시했다(force 50·mrtree 20 같은 Java의
  알고리즘별 패딩 기본값이 아직 이식되지 않음).
- 예외(`nodemicro.java.exceptions`, 입력만 있고 기대 예외는 테스트 안): `invalid_port_label_placement`,
  `invalid_node_label_placement`(`NodeContext`), `layered_graph_invalid_placement`(layered 임포터의
  `computeInsideNodeLabelPadding`), `port_without_side`, `port_without_side_indexed`(`PortContextCreator`; 서로 다른
  `PORT_INDEX`라 정렬 비교자가 변 검사에 닿지 않음), `rectpacking_child_port_without_side`(`MinSizePreProcessor`),
  `port_side_undefined`(`FIXED_ORDER` 노드의 변 없는 포트 둘: Java `TimSort` 중 `PortComparator`의
  `IllegalStateException: Port side is undefined`).
- 재생성: 입력은 RJ1 작업의 생성 스크립트(스크래치)로 만들었고, Java 출력은 `scripts/run_java_baseline.sh`와 같은
  `ElkJavaBaseline` 클래스로 얻었다.
