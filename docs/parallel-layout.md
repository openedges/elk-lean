# 구조적 병렬 레이아웃 (16차 3웨이브 PAR, 2026-11-02)

독립적인 하위 그래프를 Lean `Task`로 동시에 레이아웃하되, 모든 출력과 단계별 trace를 순차 실행과 **바이트 단위로
같게** 유지한다. 순수 Lean 원칙은 그대로이며 새 C는 런타임 초기화 글루(`elk_lean_init_threads`: task manager
시작)뿐이다. 구현: `plugins/org.eclipse.elk.core/Elk/Core/Parallel/{Settings,SubtreeFork,SiblingLayout}.lean`,
연결: `RecursiveGraphLayoutEngine.layoutRecursively`.

## 1. 요약

| 적용 지점 | 결과 |
|---|---|
| `RecursiveGraphLayoutEngine`의 형제 루프(SEPARATE_CHILDREN 노드의 자식들) | **적용.** 독립 형제 하위 트리를 청크로 나눠 task에서 레이아웃하고, 형제 순서대로 검사·병합한다(§3). |
| layered 연결 요소(`ComponentsProcessor.split` → 요소별 처리 → `combine`) | **불가(적용하지 않음).** 요소들이 Java와 같이 원래 그래프의 `Random` 하나를 공유하므로, 요소 k의 결과는 앞 요소들이 뽑은 난수 개수에 달려 있다(§2). |
| `INCLUDE_CHILDREN` 노드의 BFS 안에서 따로 레이아웃되는 노드 | 적용하지 않음(TODO, §9). |

결과(§6~§7): 모든 출력·trace·예외 문구가 `elk_base`와 바이트 동일(순차·기본·강제 모드); ptolemy 계층 모델 256개 총 시간
**1.39배**(20 ms 이상 모델 1.93배), Java 매니페스트 코퍼스 1.16배, 생성한 큰 계층 2.3~3.2배; 순차 모드와 단위 하나 그래프의
레이아웃당 명령 수는 기준의 ±0.5 % 안(합성 26개), 기본 모드 최대 RSS는 병렬 구간이 있는 모델에서 늘어난다(최대 계층 모델
+22 %). 임계값 25 요소(§8).

진입점별 기본값:

| 진입점 | 기본 | 조절 |
|---|---|---|
| CLI `elk` (`layout`, `batch`, `convert`, …) | **병렬**: `ELK_LEAN_THREADS` 또는 `min(하드웨어 스레드, 8)` | `--threads N`(어느 위치든, 마지막 값), `1` = 순차 |
| CLI `elk bench` | 순차(elk-rs `perf_benchmark --engine rust_api`가 단일 스레드라 기존 성능 기록과 비교 가능하게) | `--threads N` 또는 `ELK_LEAN_THREADS` |
| C API `elk_lean_init` | 순차(이전과 같음) | — |
| C API `elk_lean_init_threads(n)` | 병렬(`n` = 0이면 위 기본값) | 호출별 `elk_lean_layout_json_threads(…, threads, …)` |
| Node-API 애드온 | **병렬**(로드 시 `elk_lean_init_threads(0)`) | `layout_json(g, o, threads)`, npm `new ELK({ threads })`·`layout(g, { threads })` |
| WASM(Node·브라우저) | 순차(단일 스레드 런타임, task manager 없음) | 무시 |
| Lean 라이브러리 직접 사용(`lake test` 포함) | 순차(`Elk.Core.Parallel.configure`/`withThreads`를 부르지 않으면 상한 0) | `configure n`, `withThreads n act` |
| trace 모드(`ELK_TRACE_DIR`, `elk batch --trace-dir`) | 항상 순차(§4.5) | — |

## 2. layered 연결 요소: 병렬화할 수 없는 이유

1. **난수 공유.** Java `ComponentsProcessor.split`은 `newGraph.copyProperties(graph)`로 `InternalProperties.RANDOM`의
   *참조*를 복사하므로 모든 요소가 같은 `java.util.Random` 객체에서 뽑는다. Lean도 이를 그대로 따른다
   (`Components/ComponentsProcessor.lean`의 `randomOwner := some randomHolder`, `LayeredM.graphRandom?`/`setGraphRandom`).
   노드가 둘 이상인 요소는 `LayerSweepCrossingMinimizer.initializeRandom`에서 반드시 `nextLong`을 뽑고, 그 뒤 스윕
   횟수(교차가 0이 되면 조기 종료), `GreedyCycleBreaker`(순환이 있을 때), `OrthogonalRoutingGenerator`·
   `SplineEdgeRouter`·`SelfLoopRouter`도 데이터에 따라 뽑는다. 따라서 요소 k의 시작 상태는 요소 0…k−1을 끝까지
   실행해야만 알 수 있다. 투기 실행(모든 요소를 같은 시작 상태로 돌린 뒤 검증)은 노드가 둘 이상인 요소가 둘만 있어도
   항상 실패한다.
2. **arena 공유.** 요소들은 한 `LGraphArena` 안의 그래프(D4)이고 더미 노드·포트·간선이 arena 끝에 추가된다. 병렬로
   돌리려면 요소별 arena를 만들고 모든 typed 필드(`LNode`/`LPort`/`LEdge`의 내부 속성)의 id를 재번호해야 한다.

1이 결정적이라 2는 시도하지 않았다. `tickets/layered/213_componentsCompaction`, `tests/layered/connected_components/*`,
합성 `hierarchy_flat`(평평한 그래프)·`hierarchy_nested`(`INCLUDE_CHILDREN`, 한 단위)는 병렬화 대상이 아니며 순차
경로의 비용만 확인한다(§7).

## 3. 형제 루프의 병렬화

순차 루프(Java와 같음)는 `for child in children: layoutRecursively child; applyConfiguredNodeScaling child`이다.
`Elk.Core.Parallel.layoutSiblings?`가 이 루프를 대신할 수 있을 때만 대신하고, 아니면 `none`을 돌려 원래 루프가
**그대로** 돈다.

1. **값싼 거절**(순차 경로의 추가 비용은 여기까지): 자식 2개 미만, 진행 모니터가 null이 아님(하위 모니터·로그는
   순서가 있다), 스레드 상한 ≤ 1, 자식이 있는 자식이 2개 미만, 빈 보조 슬롯 없음, 순차 가드(§4.5), task manager 없음
   (§5), `minWork`(기본 25 요소) 이상인 하위 트리가 2개 미만, 그중 적격인 것이 2개 미만(§3 2단계 뒤).
2. **단위·도메인·적격성**(`computeOwnership`, arena 전체 O(N)): 자식 하나가 단위 `Cᵤ`이다. 소유 표는 모든 요소에
   단위(`u + 1`) 또는 0을 준다.
   - 노드: `sub(Cᵤ)` = `Cᵤ`와 자손; 포트: 그 노드들의 포트;
   - 간선: `sub(Cᵤ)` 노드에 포함된 간선, 또는 끝점이 하나 이상이고 끝점(노드, 포트는 부모 노드)이 모두 `sub(Cᵤ)`인
     간선 — 부모에 포함된 `Cᵤ`의 inside self loop도 여기 든다;
   - 라벨(라벨의 라벨까지): 소유 노드·포트·간선의 라벨; 섹션: 소유 간선의 섹션(포크 전 arena 기준이라, 레이아웃이
     떼어 낸 섹션도 포함).

   **적격(closed)**: `sub(Cᵤ)`에 포함되었거나 끝점이 `Cᵤ` 안쪽(자손 또는 자손의 포트)에 있는 모든 간선의 끝점이
   전부 `sub(Cᵤ)` 안에 있다(계층을 가로지르는 간선이 하위 트리를 떠나지 않는다). `Cᵤ` 자신이나 그 포트의 간선은
   어디로든 갈 수 있다(부모 레이아웃의 몫). 여기에 알고리즘 조건이 붙는다(§4.2): 하위 트리의 해석된 알고리즘이
   감사 목록 밖이면 부적격, radial·vertiflex·disco·spore가 있으면 자손과 `Cᵤ`(또는 `Cᵤ`의 포트) 사이의 간선이
   없어야 적격.
3. **구간**: 부적격 단위는 **장벽**이다. 그 자리에서, 앞 구간이 모두 병합된 arena 위에서 혼자 순서대로 돈다. 장벽
   사이의 적격 단위 연속 구간 중 무거운 단위가 둘 이상인 구간만 병렬로 돈다. 장벽 뒤 구간은 그 시점 arena로 소유
   표를 다시 계산한다.
4. **포크**: 보조 슬롯 `t`개를 원자적으로 얻고(§5), 구간을 작업량(하위 트리의 노드+포트+포함 간선)이 비슷한
   `t + 1`개의 연속 청크로 나눈다(`balancedCuts`). 청크 1…t는 `IO.asTask`(Lean 작업자 풀)로, 청크 0은 호출 스레드가
   직접 돈다. 모든 청크는 포크 직전 arena *값*을 받는다. `ElkGraph`는 영속 배열 5개이므로 첫 쓰기 때 배열·요소가
   복사되고(참조 카운팅), 원본은 그대로 남는다. 청크는 자기 단위들을 순서대로 실행하고 첫 예외에서 멈춘다.
5. **순서대로 합치기**(`joinChunks`): 청크 0, 1, …의 순서로 기다리며
   - 청크의 첫 예외 → 그 청크까지 검사·병합한 arena를 상태로 두고 그 예외를 던진다(§4.4).
   - `checkChunk`/`mergeChunk`: 청크 밖 도메인의 모든 요소가 원본과 **같은 객체**인지 본다(`withPtrEq`; 포인터가
     다를 때만 지문 비교 — float는 비트, 문자열은 길이 접두, 내용이 같게 다시 만든 요소는 변경 없음으로 본다). 하나라도
     다르면 구간 전체를 원본 arena에서 순차로 다시 돈다(`fallback`).
   - 청크 도메인의 요소는 레코드 전체(좌표, 속성, `children`/`ports` 순서, `sections` 배열…)를 병합 arena로 복사하고,
     청크가 만든 요소(배열 끝에 추가된 섹션, rectpacking의 복제 노드 등)는 청크 순서대로 덧붙이며 id를 재번호한다
     (`Remap`: 포크 크기 이상의 id에 앞 청크들이 만든 개수를 더한다). 순차 실행에서도 앞 청크의 단위들이 먼저
     만들었을 것이므로 병합 arena는 순차 arena와 요소 단위로 같다.
   - 단위 결과(inside self loop 목록)는 형제 순서로 이어 붙인다.

## 4. 결정성 논증

### 4.1 목표 명제
병렬 구간의 결과 arena = 같은 구간을 순차로 돈 결과 arena(요소 단위 동일, 생성 요소의 id 포함). 그러면 이후
레이아웃(부모의 알고리즘)·JSON 전달·출력은 같은 입력을 보므로 바이트가 같다.

증명 골격(단위 `a < b`, 도메인 `D_a`, `D_b`, 각 단위의 쓰기 집합 `W`, 읽기 집합 `R`):
1. 도메인은 서로소다. 노드·포트는 하위 트리가 서로소라서. 간선 `e ∈ D_a ∩ D_b`라면 (i) 두 하위 트리에 동시에 포함될 수
   없고, (ii) `D_a`에 포함되고 끝점이 모두 `sub(C_b)`라면 `C_a`의 적격성 때문에 끝점이 `sub(C_a) ∩ sub(C_b) = ∅`에
   있어야 하니 끝점이 없는데 (ii)의 정의는 끝점 하나 이상을 요구하고, (iii) 끝점이 모두 양쪽에 있을 수도 없다.
   라벨·섹션은 소유자를 따른다.
2. `W_a ⊆ D_a ∪ 새 요소`는 **실행 시 검사**한다(§3 5단계). 위반하면 순차로 돌아가므로 이 가정 없이도 결과는 순차와
   같다.
3. `R_a ∩ W_b = ∅`(서로 다른 단위가 상대의 도메인을 읽지 않음)는 정적 논증이다: 적격 단위의 레이아웃이 도메인 밖에서
   읽는 것은 조상(부모 `P`와 그 위)의 속성·좌표, `Cᵤ` 포트에 걸린 바깥 간선의 구조·`INSIDE_SELF_LOOPS_YO`·섹션뿐이고
   (§4.2 감사), 이것들은 어느 적격 단위의 도메인에도 들지 않으며(2에 의해 아무도 쓰지 않는다), 순차 루프에서도 형제
   사이에 바뀌지 않는다(루프 몸체는 자식과 그 하위만 건드린다).
4. 그러므로 단위들의 실행 순서를 바꿔도 각 단위가 보는 상태(자기 도메인 + 불변 영역)는 같고, 쓰기는 서로소이며,
   생성 순서는 재번호로 복원된다. 단위 안의 동작은 같은 입력에 대한 같은 순수 계산이다(전역 상태는 §4.5).

### 4.2 공급자 감사(읽기·쓰기·전역 상태·id 의존)

| 공급자 | 도메인 밖 쓰기 | 도메인 밖 읽기 | 비고 |
|---|---|---|---|
| layered(평면·`INCLUDE_CHILDREN`) | 없음(자식·포트·하위 트리 포함 간선, `Cᵤ`의 포트 `PORT_SIDE`·`PORT_BORDER_OFFSET`, `Cᵤ` 속성, 원점이 매핑된 요소만 전달) | `P`의 `DIRECTION`·라벨 간격·NodeContext 속성, 조상 좌표(`toAbsolute`), `Cᵤ` 포트 바깥 간선의 구조와 `INSIDE_SELF_LOOPS_YO`, `P.containedEdges`의 구조 | 변환기·임포터·GraphConfigurator·어셈블러는 호출마다 새로 만들고 `Random`은 속성의 seed로 만든다 |
| force, stress | 없음 | `P`의 `DIRECTION` | seed 0은 Java처럼 시계 기반(순차에서도 비결정) |
| mrtree, box, topdownpacking | 없음 | `P`의 `DIRECTION`(box) | — |
| rectpacking | 없음(자식 순서 재배치, 부모 없는 복제 노드 생성 → 새 요소로 재번호) | `P`의 `DIRECTION`·속성 | 행 저장소 키는 그래프 id, 서로 다르기만 하면 됨 |
| fixed, random | 없음 | fixed는 `Cᵤ` 포트 바깥 간선의 섹션(junction point) | random seed 0은 시계 기반 |
| sporeOverlap, sporeCompaction, disco | 없음 | disco: `Cᵤ` 포트 바깥 간선 구조 | 다른 알고리즘에 위임(disco `componentLayoutAlgorithm`, spore 하위 알고리즘) → 조건부 목록 |
| **radial, vertiflex** | **있음**: 트리 순회가 `allOutgoingEdges`를 따라가며 포트를 노드로 바꾸고 계층 검사를 하지 않아, 자손→`Cᵤ`(또는 그 포트) 간선이 있으면 `Cᵤ`를 지나 형제·부모로 나간다(좌표·`ORDER_ID`·바깥 간선 섹션 쓰기, 형제 크기 읽기) | 같음 | **조건부 적격**: 하위 트리에 이들(또는 위임하는 disco·spore)이 있으면 자손과 `Cᵤ`/`Cᵤ` 포트 사이 간선이 없어야 한다. 적격성 조건 아래에서 하위 트리를 떠나는 순회는 반드시 그런 간선을 지나므로 이것으로 모든 탈출이 막힌다 |
| 목록 밖 알고리즘(테스트가 등록한 것 등) | 알 수 없음 | 알 수 없음 | 부적격(장벽) |

엔진 쪽: `evaluateHierarchyHandlingInheritance`는 루프 전에 정해진 `P`의 값을 읽고 `Cᵤ`에 쓴다; `applyTopdownLayout`은
`P`의 top-down 단계가 루프 전에 쓴 `Cᵤ` 크기를 읽는다; `applyConfiguredNodeScaling`은 `Cᵤ`·라벨·포트·포트 라벨만;
`getNodePropSticky`는 레이아웃 노드 자신에게만 기본값을 쓴다. 라이브러리 libavoid/graphviz는 아무것도 등록하지 않는다.

id·크기 의존: 기존 요소의 id는 task와 순차에서 같다. Elk id를 키로 하는 HashMap/HashSet은 조회에만 쓰인다. 새 요소는
섹션(fixed, random, layered 전달기, `firstEdgeSection`을 쓰는 force·mrtree·radial·spore·vertiflex·disco)과 rectpacking
복제 노드이며, JSON overlay는 가져오기 표 밖의 섹션을 `<edgeId>_s<간선 안 위치>`로 이름 짓는다(재번호 뒤 순차와 같음).
vertiflex의 보조 표 크기가 `g.nodes.size`를 따르지만 결과에는 영향이 없다. 예외 문구에 arena 인덱스는 들어가지 않는다.

### 4.3 레이아웃 단위 안의 결정성
단위는 자기 arena 사본에서 순차 코드 그대로 돈다(중첩된 형제 루프도 같은 규칙으로 병렬화될 수 있다). 난수: layered는
그래프마다 `randomSeed`로 `Random`을 만들고(`GraphConfigurator`), seed 0은 elk-rs처럼 `Random(0)`이다(Java의
`new Random()`은 시간 기반이라 Java 자신이 비결정); force·random의 seed 0은 시계 기반이라 순차 실행에서도 결과가
매번 다를 수 있다(병렬과 무관). 레이아웃 실행 사이에 공유되는 생성기는 없다.

### 4.4 실패 순서
Java는 처음 실패한 자식에서 멈추고 뒤 자식은 실행하지 않는다. 병렬 구간은 청크를 순서대로 기다리므로, 예외를 보고하는
청크 앞의 청크는 모두 성공하고 검사·병합된 상태다. 청크 안에서는 단위가 순서대로 돌고 첫 예외에서 멈춘다. 그 단위의
예외는 자기 도메인과 불변 영역에만 의존하므로(§4.1) 순차에서 같은 단위가 던질 예외와 클래스·문구가 같다. 실패한 청크의
arena(앞 단위들과, 던진 단위가 던지기 전까지 한 일)도 같은 검사를 거쳐 병합해 `ElkM` 상태로 남기므로, 예외를 잡아 arena를
계속 쓰는 호출자도 순차와 같은 상태를 본다(`parallel.failures`의 arena 비교; 검사에 걸리면 순차 재실행). 그 뒤
청크는 `IO.cancel`(협조적, 레이아웃 코드는 확인하지 않음)하고 **기다리지 않는다**: 순차에서는 시작조차 하지 않았을
단위라 끝나지 않을 수도 있다(radial `WEDGE_COMPACTION` 비종료). CLI는 끝날 때 아직 도는 보조 작업이 있으면 출력을
비우고 `IO.Process.exit`로 끝낸다(생성된 `main`의 `lean_finalize_task_manager`가 작업자를 join하지 않게). 애드온에서는
버려진 작업이 자기 사본에서 끝날 때까지 돌며 보조 슬롯만 차지한다(끝나지 않는 작업은 프로세스가 끝날 때까지 슬롯 하나를
차지하므로 그만큼 이후 호출의 병렬도가 줄어든다; 결과에는 영향이 없다). 예외로 끝난 레이아웃의 arena는 버려지므로(API의
`catchLayout`) 병합하지 않은 상태도 관측되지 않는다. 앞 청크가 검사에 걸리면(쓰기 위반) 예외와 무관하게 구간 전체를
순차로 다시 돌아 순차와 같은 결과(같은 예외 포함)를 낸다.

**남은 위험**: 앞 단위가 예외를 던지고 뒤 단위가 Lean 스택을 넘치게 하는(무한 재귀) 입력에서는, 순차는 예외를 보고하지만
병렬에서는 이미 돌고 있던 뒤 단위가 프로세스를 중단시킬 수 있다(Lean의 스택 오버플로는 `abort`라 잡을 수 없다). 이런
입력은 적격 형제 둘 이상 + 앞 형제의 예외 + 뒤 형제의 무한 재귀가 모두 필요하다. 1 GB 스택을 채우는 데 시간이 걸리므로
앞 형제가 빨리 던지면 CLI는 그 예외를 보고하고 `IO.Process.exit`로 먼저 끝난다(합성 입력 `throw_then_overflow`: 순차·병렬
모두 같은 예외; 반대 순서 `overflow_then_throw`: 모두 overflow). 무작위 세트 h·w·v 18,000개를 임계값 0(모든 형제를 task로,
병렬 구간 4,270개 중 예외로 끝난 것 99개)으로 돌렸을 때 결과 종류·문구가 달라진 입력은 0건이었다(§6).

### 4.5 전역·공유 가변 상태
| 상태 | 판정 |
|---|---|
| `TraceRecorder.layoutDepth` | 병렬 layered 실행이 서로의 깊이를 덮어쓰지 않도록 `modifyGet`/`modify`로 원자적 증감(순차 의미 동일). 이전 `get`/`set`은 두 스레드가 섞이면 깊이가 0으로 돌아오지 않았다 |
| `stepCounter`, `runTraceDir`, trace 디렉터리 | trace 모드에서만 의미 있음 → **trace 모드는 순차 강제**(`registerTraceSequentialGuard`: `ELK_TRACE_DIR` 또는 `--trace-dir` override). 단계 번호·파일이 순차와 같다 |
| `ElkTrace.global`(`ELK_TRACE_*`/`ELK_DEBUG_*` 60개) | 불변이지만 디버그 출력 순서가 바뀌므로 하나라도 켜지면 순차(`ElkTrace.anyEnabled`) |
| `RandomTrace`(`CROSSMIN_RANDOM_TRACE`), `ELK_RANDOM_TRACE` | 켜지면 순차. 꺼져 있으면 카운터 리셋만 일어나고 출력에 영향 없음 |
| `LayoutMetaDataService`(레지스트리, 접미사 메모) | `layout` 시작 시 초기화 끝; 메모는 `modifyGet`으로 원자적·멱등 |
| `LayoutProvider.registryRef`, `LayeredPhases.registry`/`phaseRegistry`, `GraphValidator` 팩토리 | 초기화 뒤 읽기 전용; 프로세서는 순수 값, 페이즈는 `IO` 팩토리, 내부 `IO.Ref`는 호출마다 생성(GraphInfoHolder 등) |
| `NodeDimensionFlags.global`, `LabelAndNodeSizeFlags.global`, `disableGreedySwitch`, `disableNs` | 불변 |
| 진행 모니터 | null 모니터만 병렬(기본 모니터는 하위 작업을 부모에 기록) |
| C shim(`elk_core_ffi.c`) | 스택 버퍼만 사용 |
| `Elk.Core.Parallel` 자신 | 상한·임계값은 진입점 스레드만 쓰고, 보조 슬롯 카운터·통계는 `modifyGet`/`modify`; 난수 디버그 환경 변수는 시작 시 한 번 읽는다 |

Lean `IO.Ref`는 영속(초기화 시 생성)이거나 MT로 표시되면 `exchange` 기반으로 접근하므로 동시 읽기·`modify`가 안전하다.
task로 넘어간 값은 Lean이 MT로 표시해 참조 카운트가 원자적으로 바뀐다(`alloc_task`의 `lean_mark_mt`가 처음 한 번 arena 전체를
훑는다; 이미 MT인 객체에서 멈추므로 같은 arena의 다음 포크는 바뀐 부분만 훑는다). MT 객체는 배타적이지 않으므로 다음 쓰기에서
한 번 복사되고, 그 사본은 다시 단일 스레드 객체다. 그래서 병렬 구간 뒤의 부모 레이아웃·JSON 전달은 MT 객체를 읽을 때 원자적
참조 카운트를 쓴다 — 기본 모드 코퍼스 총 명령 수 +1.6%(스레드 합)의 일부가 이것이다(§7).

지문 비교의 한계: `Dynamic` 속성 값(`LABEL_MANAGER`, disco 디버그 속성)은 타입 이름으로만 비교한다(`DecidableEq` 없음).
포인터가 같으면 지문을 보지 않으므로 이것이 문제가 되는 것은 단위가 도메인 밖 요소의 `Dynamic` 값을 같은 타입의 다른 값으로
바꾼 경우뿐이고, 지금 어떤 레이아웃도 `Dynamic` 값을 쓰지 않는다. `ElkTrace.anyEnabled`는 `ElkTrace`의 필드를 손으로 나열하므로
플래그를 추가하면 함께 추가해야 한다.

## 5. 런타임 배관
- **CLI**: Lake가 만든 `main`이 모듈 초기화 뒤 `lean_init_task_manager()`(작업자 수 `LEAN_NUM_THREADS` 또는 하드웨어
  스레드)를 부르므로 task가 실제로 다른 스레드에서 돈다. `Main.main`은 `--threads N`을 떼어 `configure`하고, 끝날 때
  남은 보조 작업이 있으면 `IO.Process.exit`.
- **C API**: `elk_lean_init_threads(n)` = `elk_lean_init` + (처음 한 번만) `lean_init_task_manager()` + `elk_ffi_set_threads(n)`.
  두 번째 호출은 아무것도 바꾸지 않는다. `elk_lean_layout_json_threads(g, o, threads, &err)`는 호출별 상한
  (`withThreads`; 호출은 원래 직렬화되어야 한다). `elk_lean_init`만 쓰면 이전처럼 순차.
- **Node-API**: 로드 시 `elk_lean_init_threads(0)`. 모든 호출은 원래대로 전역 mutex 안이고, Lean 작업자는 Node
  `worker_threads`와 별개인 Lean 자체 스레드다. `worker_threads`가 각자 애드온을 불러도 초기화는 프로세스당 한 번.
- **WASM**: 런타임이 `LEAN_MULTI_THREAD` 없이 빌드되어 task manager가 없고, JS 글루는 `elk_lean_init`만 부른다(상한 0).
  상한이 설정되더라도 **task manager 탐침**(`taskManagerAvailable`: dedicated task 하나를 띄워 스레드 id 비교, 결과는
  `configure` 때까지 캐시)이 같은 스레드를 보고 순차를 고른다. `Task.spawn`이 task manager 없이 동기 실행되는 것
  (`lean_task_spawn_core`)에 우연히 기대지 않는다.
- **스택**: Lean 작업자는 `lthread`(기본 1 GB 예약; Lean 실행 파일에서는 `lean_run_main`이 `LEAN_STACK_SIZE_KB`로 바꾼다)이고,
  CLI의 `main`도 `lean_run_main`이 같은
  크기의 `lthread`에서 돌린다. 그래서 CLI에서는 순차·병렬 모두 같은 스택 한도이며 차이는 단위가 시작할 때 이미 쓴 깊이
  (조상 레벨의 `layoutRecursively` 프레임 몇 개)뿐이다. 따로 설정할 필요가 없었다. 애드온에서는 호출 스레드(Node 메인
  8 MB, `worker_threads` 기본 4 MB)보다 Lean 작업자 스택이 크므로, 호출 스레드 스택을 넘칠 깊은 하위 그래프가 병렬에서는
  성공할 수 있다(성공한 결과는 같다). 애드온은 `lean_run_main`을 거치지 않으므로 `LEAN_STACK_SIZE_KB`가 작업자에 적용되지
  않는다; 같은 한도가 필요하면 `threads: 1`(순차)을 쓴다.
- **보조 슬롯과 메모리**: 동시에 도는 보조 task는 프로세스 전체에서 `상한 − 1`개 이하(중첩 레벨·호출을 합쳐, 원자적
  카운터). 슬롯을 못 얻은 레벨은 순차다. 병렬 단위마다 자기 사본의 바뀐 배열(포인터 배열)과 알고리즘 내부 구조를
  가지므로 최대 메모리는 대략 동시 단위 수만큼 늘 수 있다(§7).

## 6. 검증

기준 이진 `elk_base` = 기준점 `733782c`의 `LEAN_NUM_THREADS=3 lake build` 산출물. 새 이진은 최종 커밋의 같은 빌드.
모드: **순차**(`ELK_LEAN_THREADS=1`), **기본**(상한 8, 임계값 25), **강제**(`ELK_LEAN_PAR_MIN_WORK=0`: 모든 형제를 task로,
병렬 경로를 최대한 태우는 검증용). 비교는 출력 파일의 SHA-256 매니페스트.

| 게이트 | 순차 | 기본 | 강제 |
|---|---|---|---|
| Java 매니페스트 코퍼스 1,998개(`elk batch`, compact 레이아웃 1,997 + 오류 문구 1) | 동일 | 동일(병렬 구간 456·청크 1,400) | 동일(구간 795·청크 4,417) |
| 단계 trace(`--trace-dir`, 196,407 파일 + 레이아웃) | 동일 | 동일(trace 모드는 순차: 구간 0) | — |
| 합성 26개 × (compact, `--pretty --sort-keys`) × (출력, stderr) = 104 파일 | 동일 | 동일 | 동일 |
| 무작위 h·w·v seed 1~10, 18,000개(레이아웃 13,684·예외 4,296·스택 오버플로 20 = v의 실제 오버플로 12 + h의 `StackOverflowError` 8; 결과 종류·첫 줄 문구) | 동일 | 동일(구간 1,868, 그중 예외 47) | 동일(구간 4,295, 그중 예외 99) |

- `lake build` 경고 0·오류 0, `LEAN_NUM_THREADS=3 lake test` **17,296 통과·0 실패**(기존 17,197 + 새 `parallel.*` 99:
  소유 표·적격성·컷, 재번호 병합·쓰기 검사, 무작위 계층 60개와 다중 요소 그래프의 상한 1 대 4 차분, 던지는 자식을 모든
  위치·쌍에 둔 22가지의 예외 문구와 예외 뒤 arena). 기준점 기록의 17,202와 기존 몫 17,197의 차이 5는 조사하지
  않았다(이 worktree에는 `external/elk-models` 서브모듈이 없어 그것을 읽는 테스트가 빠졌을 가능성이 크다).
- elk-rs(기본 모드): model parity(1e-6) **1447/1447**, 바이트 일치 1060/1447(기존과 같음), strict trace parity
  **1447/1447**(trace 모드라 순차).
- FFI: `ELK_NO_GMP=1 sh scripts/build_ffi.sh --check` 통과(smoke에 `elk_lean_init_threads` 두 번 호출 + 상한 1·4가
  `elk layout --sort-keys`와 바이트 동일 추가), smoke·애드온 `__gmp` 0. NAPI(`build_napi.sh --skip-ffi`, no-GMP) 빌드,
  npm `node --test test/` **72 통과·1 skip**(기존 67 + `testThreads.test.mjs` 5: 상한 1·2·3·8·기본 바이트 동일, ELK API
  `threads`, 던지는 자식 순서, `TypeError`, 동시 `worker_threads` 4개 × 2파 각자 병렬 레이아웃). WASM(`build_wasm.sh`)
  realworld **550/550**이 병렬 CLI와 바이트 동일(WASM은 순차). `plugins/org.eclipse.elk.live`의 `npm test`는 의존성 설치가
  필요해 돌리지 않았다(WASM 경로라 바뀐 것이 없다).
- 위험 입력: `throw_then_overflow`(앞 형제 예외, 뒤 형제 radial 무한 재귀)는 순차·병렬 모두 같은 예외(강제 모드에서 예외로
  끝난 병렬 구간 1, CLI가 뒤 작업을 기다리지 않고 종료), `overflow_then_throw`는 모두 스택 오버플로; 깊이 11의 이진 compound
  트리(compound 4,095개)는 순차·기본(구간 76)·강제(구간 67, 중첩 병렬) 바이트 동일.

## 7. 성능

측정은 같은 기계(Apple M1 8코어)에서 EXT 에이전트와 동시에 했다(load 5~14); 벽시계는 그만큼 잡음이 있고, 같은 이진의 순차
대조(`t1`)가 기준과의 잡음 폭을 보여 준다. `elk bench --mode models`는 모델별 평균의 라운드별 최솟값을 쓴다.

**속도 향상(기본 모드 vs `elk_base`, 벽시계)**

| 모델군 | 총 시간 | 비율 | 기하평균 | 비고 |
|---|---|---|---|---|
| ptolemy 계층 256개(`realworld/ptolemy/hierarchical`) | 861 → 621 ms | **0.721(1.39배)** | 0.898 | 기준 ≥ 20 ms 7개 0.518(1.93배), 5~20 ms 24개 0.659, 1~5 ms 152개 0.924, < 1 ms 73개 0.989; 순차 대조 0.995 |
| Java 매니페스트 코퍼스(이름 기준 1,447개) | 3,339 → 2,890 ms | 0.866(1.16배) | 0.967 | ≥ 20 ms 0.742, 5~20 ms 0.795; 순차 대조 1.002 |
| 연결 요소 13개(`tickets/layered/213_componentsCompaction`, `connected_components/*` 등) | 6.4 → 6.3 ms | 0.995 | 0.993 | §2: 병렬화 대상 아님 |
| 합성 26개(모두 단위 하나; `hierarchy_flat`·`hierarchy_nested` 포함) | — | — | 0.993 | `hierarchy_flat` 0.994, `hierarchy_nested` 0.994; 순차 대조 0.996 |
| 생성한 계층 8 × 300 노드(layered) | 0.16 → 0.05 s | 3.2배 | — | CLI 프로세스 전체(시작·JSON 포함) |
| 생성한 계층 4 × 600 / 16 × 100 / 8 × 300(mrtree) | 0.19 → 0.07 / 0.09 → 0.04 / 0.03 → 0.02 s | 2.7 / 2.3 / 1.5배 | — | 〃 |
| 이진 compound 트리 깊이 11(4,095개) | 0.38 → 0.14 s | 2.7배 | — | 중첩 병렬 |
| 코퍼스 최대 계층 모델 `de_trilateration_Trilateration` | 0.06 → 0.03 s | 2배 | — | 〃; 애드온 in-process 57 → 26 ms(2.2배) |

**순차 모드·단위 하나 그래프의 비용(명령 수)**: 합성 26개의 레이아웃 1회당 명령 수(`elk bench`의 반복 횟수 두 가지 차이로
시작·입력 생성 상쇄, 각 2회 최솟값)는 순차(`ELK_LEAN_THREADS=1`) 기하평균 **1.0006**·최대 편차 0.32 %, 상한 8
기하평균 **1.0007**·최대 편차 0.35 %(26개 모두 ±0.5 % 안). 코퍼스 `elk batch` 프로세스 전체(모든 스레드 합, 2회 최솟값):
기준 61.70 G → 순차 61.68 G(**0.9997**) → 기본 62.70 G(+1.6 %: 병렬 구간 456개의 소유 표·검사·병합, 첫 포크의 MT 표시와
그 뒤의 원자적 참조 카운트). 같은 이진 두 번의 차이가 최대 2 %여서 프로세스 단위 명령 수는 그 정도 잡음이 있다.
프로세스 시작(`elk --version`)은 이진 크기 차이로 약 0.5 M 명령(0.7 %) 늘었다(코드 경로와 무관; 통합 브랜치 이진도 같은 정도).

**메모리(최대 RSS)**: 병렬 단위마다 자기 사본의 바뀐 배열과 알고리즘 내부 구조를 가지므로 늘어난다. 코퍼스 최대 계층 모델
23.6 → 28.8 MB(+22 %), 8 × 300 노드 30.9 → 47.9 MB, 깊은 트리 46.1 → 69.6 MB, 코퍼스 `elk batch` 전체 41.3 → 51.9 MB.
순차 모드는 기준과 같다(±0.5 %). 상한이 동시 단위 수를 묶는다.

## 8. 임계값

`minWork` = **25**(하위 트리의 노드 + 포트 + 포함 간선; 무거운 단위가 2개 이상이고 그중 적격이 2개 이상일 때만 병렬).
`ELK_LEAN_PAR_MIN_WORK`로 바꿀 수 있다(테스트·검증은 0). ptolemy 계층 모델 256개(`elk bench --mode models`, 모델별 최솟값,
EXT와 함께 돌아 load 5~14, 순차 대조 `t1`의 전체 비율 0.998~1.002)에서 고른 값이다:

| 임계값 | 총 시간 비율(속도 향상) | 기하평균 | 기준 < 1 ms 모델 78개 | 1~5 ms 147개 | 5~20 ms 24개 | ≥ 20 ms 7개 |
|---|---|---|---|---|---|---|
| 200 | 0.907 (1.10배) | 0.990 | 1.004 | 1.000 | 0.986 | 0.703 |
| 50 | 0.780 (1.28배) | 0.955 | 1.012 | 0.994 | 0.727 | 0.556 |
| **25** | 0.721 (1.39배) | 0.901 | 0.997 | 0.925 | 0.653 | 0.510 |
| 10 | 0.715 (1.40배) | 0.880 | 0.976 | 0.894 | 0.668 | 0.524 |
| 0 | 0.722~0.745 (1.34~1.38배) | 0.875~0.910 | 0.965~1.002 | 0.885~0.924 | 0.678~0.707 | 0.538~0.543 |

10과 25는 측정 잡음 안에서 같고, 0은 5 % 이상 느려진 모델이 13~35개(25는 9개, 순차 대조 4~6개)라 25를 택했다. 구간의
고정 비용(소유 표 O(N), task 생성, 청크마다 검사·병합 O(N), 첫 포크의 MT 표시)은 arena 크기에 비례하고 작은 단위의 레이아웃
시간과 비교된다.

## 9. 남은 일
- `INCLUDE_CHILDREN` 노드의 BFS 안에서 따로 레이아웃되는 노드(`stopHierarchy || algorithmSwitch`)도 같은 방식으로
  병렬화할 수 있다. BFS가 단위 뒤의 노드에 `HIERARCHY_HANDLING`을 쓰는 순서를 앞당겨야 하므로 별도 논증이 필요하다.
- 연결 요소(§2)는 Java 의미를 바꾸지 않는 한 불가.
- 애드온의 작업자 스택을 호출 스레드에 맞추는 선택지(지금은 문서화만).
- 구간마다 소유 표·검사·병합이 arena 전체(O(N))를 훑는다. 병렬 레벨이 많은 깊은 계층에서는 하위 트리만 훑는 표(노드 →
  단위 사상을 부모 구간에서 물려받기)와, 청크가 건드릴 수 있는 요소만 보는 검사로 줄일 수 있다.
- 청크 균형은 작업량(요소 수)의 선형 합으로 잡는다. layered의 비용은 초선형이라 큰 단위 하나가 청크를 지배할 수 있다
  (예: 작업량² 가중).
- Linux(CI) 빌드에서 task manager·애드온 동작은 확인하지 않았다(macOS arm64만).
