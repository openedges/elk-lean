# 무작위 그래프 견고성 픽스처

`docs/robustness-random-graphs.md`의 분류에서 클래스마다 하나씩 고른 입력이다. 결과 열은 수정 후
elk-lean / elk-rs `eb586b6d` / ELK Java 0.12.0 순서다. 테스트: `tests/lean/Tests/Api/Robustness.lean`.

- `label_stack_hang.json`: elk-rs의 단순화 ELK 경로(`calculateLabelAndNodeSizesForElk`)의 NORTH/SOUTH 라벨 쌓기 루프가 반올림 때문에 같은 좌표로 되돌아와 무한 반복하던 입력(SOUTH 포트, INSIDE 라벨 2개). 그 경로는 종료하도록 고쳤고(테스트가 라벨 y −25.4/−15.8을 직접 확인), RJ1부터 노드 마이크로 레이아웃은 Java의 전체 셀 시스템을 쓰므로 결과가 Java와 같다(`label_stack_hang.java.json` = ELK Java 출력, 노드 크기 0×0·라벨 y −24.4/−15.8; force 패딩 기본값 차이 때문에 노드 위치는 비교하지 않음) / elk-rs 무한 루프 / Java 성공.
- `radial_not_a_tree.json`: radial, 루트 없는 2-사이클. Java와 같은 `java.lang.IllegalArgumentException: The given graph is not a tree!`(이전 elk-lean·elk-rs는 `UnsupportedConfigurationException`).
- `layer_sweep_in_child.json`: `INCLUDE_CHILDREN`에서 자식 그래프만 `LAYER_SWEEP`. Java와 같은 `UnsupportedGraphException`과 `LGraph.toString()`(노드 식별자 경로 포함) 메시지(이전 elk-lean·elk-rs는 다른 클래스·문구).
- `fixed_edge_without_section.json`: `fixed` + `ORTHOGONAL`, 섹션 없는 간선. Java·elk-rs와 같은 `IllegalArgumentException: The edge needs to have exactly one edge section. Found: 0`(이전 elk-lean은 오류를 삼키고 성공).
- `radial_cycle_overflow.json`: radial, 루트에서 도달하는 사이클. 세 구현 모두 스택 오버플로(Java `StackOverflowError`, 계승 동작). 프로세스가 중단되므로 테스트에서 실행하지 않는다.
- `java_crossing_counter_aioobe.json`(생성기 v9/g0025): Java만 `ArrayIndexOutOfBoundsException`(`BinaryIndexedTree.rank`, `CrossingsCounter.countCrossingsOnPorts`); elk-lean·elk-rs 성공. Java 결함으로 분류, 재현하지 않음.
- `port_without_side.json`: force, 변이 없는 포트. Java는 `NodeLabelAndSizeCalculator`의 검증(`PortContextCreator`)으로 `IllegalArgumentException: Label and node size calculator can only be used with ports that have port sides assigned.`; RJ1부터 elk-lean도 같은 예외(elk-rs는 검증 없이 성공).
