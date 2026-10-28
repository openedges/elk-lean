# layered 노드·포트·라벨 픽스처 (ELK Java 기준, LNODE)

무작위 그래프 Java parity의 `LNODE` 클래스(layered 노드 크기·포트 위치·라벨 위치)와 layered 임포터의 간선 선택을 ELK
Java 0.12.0 결과로 고정한다. 테스트: `tests/lean/Tests/Api/LayeredNodeJava.lean`.

- 입력 `<name>.json`, Java 출력 `<name>.java.json`(`ElkJavaBaseline`, 미수정 Maven 아티팩트). 전부 값 정확 일치(tol 0).
- `selfloop_port_order`: 한 변 self loop 포트를 Java `SelfLoopPort.getSLNetFlow()`(self loop 간선 in − out)로 정렬
  (`SelfLoopPortRestorer`; elk-rs는 숨긴 self loop를 빼고 센 `LPort` net flow라 전부 0). 무작위 `v1/g0225`의 `n9_n0`.
- `port_index_partial`: `FIXED_ORDER` 노드에서 일부 포트만 `PORT_INDEX`를 가진 경우 — 비교자가 일관 순서가 아니라 Java
  `TimSort` 비교 순서대로 결과가 정해진다(`PortListSorter`, `javaSortBy`). 무작위 `v8/g0080`의 `n3_n2`에서 줄임.
- `fixed_ratio_ports`: `FIXED_RATIO` 포트를 `LPort`의 `PORT_RATIO_OR_POSITION` 비율로 배치(셀 시스템; elk-rs는 0).
- `external_ns_port_margins`: 북/남 외부 포트 더미를 되돌릴 때 더미 자신의 여백 계산
  (`HierarchicalPortOrthogonalEdgeRouter.restoreDummy`; elk-rs는 계산하지 않음). 무작위 `v6/g0330`의 `n2_n5` 부분 그래프.
- `min_graph_size_separate`, `min_graph_size_include`: `calculateMinimumGraphSize` — 라벨 셀은 부모의 `DIRECTION`
  (있을 때)으로 배치, 고정 포트 라벨이어도 계산, `copyProperties`가 값 객체를 공유하므로 ElkNode 자신의
  `NODE_SIZE_CONSTRAINTS`(+`MINIMUM_SIZE`)와 명시된 `NODE_SIZE_MINIMUM`이 바뀌어 부모 실행의 노드가 그 값을 본다.
- `fixed_port_labels_compound`: 고정 포트 라벨을 가진 복합 노드에 elk-rs의 `processNode` 사전 패스가 없다
  (`LabelAndNodeSizeProcessor`는 Java처럼 셀 시스템만).
- `edge_cross_hierarchy_separate`, `edge_cross_hierarchy_layered_child`: Java 평면 임포트는 자식끼리(또는 자식과 그래프)를
  잇는 간선만 변환하고, 자식의 자식으로 들어가는 루트 간선은 어느 실행에도 속하지 않은 채 오류 없이 남긴다(섹션 없음).
- `edge_inside_self_loop_separate`: 따로 배치되는 복합 노드의 inside self loop(그 노드의 실행만 경로를 만든다).
- 예외(입력만, 기대 문구는 테스트 안): `edge_to_no_layout_node`(평면 간선의 끝이 `NO_LAYOUT` 형제 — Java
  `transformEdge`의 `UnsupportedGraphException: The source or the target of edge ElkEdge "e0" ElkNode "x" (0.0,0.0 |
  30.0,30.0) -> …`, EMF `toString`과 Java `Double.toString`), `edge_hyperedge_flat`(평면 그래프의 하이퍼엣지 —
  `ElkGraphUtil.getSourceNode`의 `IllegalArgumentException: Passed edge is not 'simple'.`).
- 재생성: 입력은 LNODE 작업의 생성 스크립트(스크래치 `tools/mkfx.py`, `tools/sub.py`)로 만들었고, Java 출력은
  `scripts/run_java_baseline.sh`와 같은 `ElkJavaBaseline` 클래스로 얻었다.
