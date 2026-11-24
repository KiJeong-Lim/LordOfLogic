# LoL을 편집기에 연결하기

[English](editor.md) · **한국어**

편집기는 아직 저장하지 않은 버퍼에서도 명령을 하나씩 검사할 수 있다. 사용자가 다음 명령으로 진행하면 서버에 `next`를 보내고, 응답의 `proof`에서 가정과 목표를 읽어 화면에 표시한다.

저장소 루트에서 `cabal build lol`로 빌드하고, 같은 디렉터리에서 `"$(cabal list-bin lol)" --server`를 실행한다. 서버의 표준 입력으로 요청을 쓰고 표준 출력에서 응답을 읽는다. 두 방향 모두 UTF-8 JSON 객체 하나가 한 줄을 차지한다. 서버는 첫 요청을 받기 전에 `ready` 이벤트를 보낸다. 표준 오류는 별도 스트림으로 받는다. 소스에 줄바꿈이 있어도 요청 전체가 한 줄에 담기도록 JSON 인코더를 사용한다.

## 증명을 진행하고 한 단계 되돌린 뒤 다시 실행하기

아래 예제를 `editor_demo.py`로 저장하고 저장소 루트에서 `python3 editor_demo.py`를 실행한다. 클라이언트가 `open` 요청에 소스를 담아 보내므로, 파일을 저장하기 전에도 `Demo.lol`을 문서 경로로 쓸 수 있다.

```python
import itertools
import json
import subprocess

binary = subprocess.check_output(["cabal", "list-bin", "lol"], text=True).strip()
source = """Theorem copy : forall P : Prop, P -> P.
Proof.
    intros P h.
    exact h.
Qed.
"""

with subprocess.Popen([binary, "--server"], stdin=subprocess.PIPE,
                      stdout=subprocess.PIPE, text=True, encoding="utf-8") as server:
    ready = json.loads(server.stdout.readline())
    assert ready["event"] == "ready" and ready["protocol"] == 2
    ids = itertools.count(1)

    def request(method, **fields):
        identity = next(ids)
        message = {"protocol": 2, "id": identity, "method": method, **fields}
        print(json.dumps(message), file=server.stdin, flush=True)
        reply = json.loads(server.stdout.readline())
        assert reply["id"] == identity
        if reply["status"] == "error":
            raise RuntimeError(reply["error"]["message"])
        return reply

    def reference(reply):
        return {key: reply[key] for key in ("document", "incarnation", "revision", "state")}

    doc = request("open", document="tutorial", revision=1, path="Demo.lol", source=source)
    for _ in range(3):  # Theorem, Proof, intros
        doc = request("next", **reference(doc))

    goal = request("show", **reference(doc))["proof"]
    for binding in reversed(goal["locals"]):
        print(binding["name"], ":", binding["typeDisplay"])
    print("Goal:", goal["display"])

    before_exact = doc["state"]
    doc = request("next", **reference(doc))  # exact h.
    assert request("show", **reference(doc))["proof"]["complete"]
    assert before_exact in doc["retainedStates"]

    doc = request("undo", **reference(doc), target=before_exact)
    print("Goal after undo:", doc["proof"]["display"])
    doc = request("next", **reference(doc))  # exact h. again
    print("Complete after next:", doc["proof"]["complete"])
    doc = request("next", **reference(doc))  # Qed.
    print(*doc["output"])
    request("close", **reference(doc))
    request("shutdown")
```

실행하면 다음 여섯 줄이 출력된다.

```text
P : Prop
h : P
Goal: P
Goal after undo: P
Complete after next: True
The theorem was admitted.
```

`intros P h.` 뒤에는 목표가 `P`이고, 타입이 `P`인 지역 가정 `h`가 있다. 클라이언트는 `exact h.`를 적용하기 전에 현재 **문서 상태**를 저장한다. 적용 직후 `show`를 보내면 `proof.complete`가 참인 것을 확인할 수 있고, 실행 커서는 그대로다. 이때 저장해 둔 상태를 `undo`로 복원하면 목표가 다시 열리고 커서는 `exact h.`의 시작점으로 돌아간다. **`undo` 응답의 새 문서 참조**로 `next`를 보내면 같은 명령을 한 번 더 검사한다.

`Qed.`가 정리를 환경에 등록하면 서버가 `proof: null`을 반환한다. 편집기에 ‘끝까지 실행’ 기능을 넣으려면 `atEnd: true`를 받을 때까지 `next`를 한 번씩 보낸다. 위 예제에서는 `Qed.`를 실행한 뒤 `next`를 한 번 더 보내야 파일 끝에 도달했다는 응답이 온다.

## 버퍼 편집하기

연결이 유지되는 동안 요청 ID에는 이전보다 큰 양의 정수를 쓴다. 최댓값은 `9007199254740991`이다. 열린 문서에 요청을 보낼 때는 그 문서의 최신 응답에서 다음 네 필드를 복사한다.

| 필드 | 의미 |
| --- | --- |
| `document` | 편집기가 버퍼에 붙인 이름이다. |
| `incarnation` | 문서를 연 요청의 ID다. 같은 이름으로 문서를 다시 열면 새 값이 생긴다. |
| `revision` | 편집기가 소스 텍스트에 매기는 버전 번호다. |
| `state` | 서버가 기록한 명령 실행 상태다. 요청에는 응답 최상위의 값을 쓴다. 하위 필드 `proof.state`는 증명 내부의 상태를 가리킨다. |

| 편집기에서 할 일 | 보낼 요청 |
| --- | --- |
| 버퍼 끝에 텍스트 추가 | `append`에 문서 참조, 현재 버전보다 큰 `nextRevision`, 덧붙일 `source`를 담는다. |
| 실행 커서 뒤의 명령 고치기 | `replace`에 문서 참조, 현재 버전보다 큰 `nextRevision`, **커서부터 버퍼 끝까지를 대체할 새 텍스트 전체**를 담는다. |
| 이미 검사한 명령 고치기 | `undo`에 문서 참조를 담고, `retainedStates`에서 고른 이전 문서 상태를 `target`으로 준다. 응답으로 받은 참조로 `replace`를 보낸다. |
| 다른 버퍼로 전환 | 현재 참조로 `close`를 보낸 뒤 `open`으로 다른 버퍼를 연다. 서버 프로세스 하나가 문서 하나를 연다. |

예제에서 `before_exact = doc["state"]` 바로 앞에 다음 호출을 넣어 보자. 편집한 뒤 첫 `next`와 되돌린 뒤 첫 `next`는 이제 각각 `assumption.`을 실행한다.

```python
    doc = request("replace", **reference(doc), nextRevision=doc["revision"] + 1,
                  source="\nassumption.\nQed.\n")
```

맨 앞의 `\n`은 새 전술과 `intros P h.` 끝의 마침표를 구분한다. 마침표에 `assumption.`을 바로 붙이면 앞 명령의 토큰 경계가 바뀐다. 이 경우 서버는 `document-boundary`를 반환한다.

## 진단 표시와 요청 취소

- 응답이 `status: "error"`이면 `error.message`를 표시한다. 소스 진단에는 `error.range`가 올 수 있다. 줄과 열은 1부터 세고, 열의 단위는 유니코드 스칼라값이다. 응답에 문서 참조가 있으면 다음 요청에 그 값을 쓴다. `stale-incarnation`, `stale-revision`, `stale-state`는 참조에서 어느 값이 오래됐는지 알려 준다.
- 일반 요청은 한 번에 하나씩 보낸다. 오래 걸리는 `next`를 중단하려면 새 ID로 `cancel`을 보내고 실행 중인 **요청 ID**를 `target`에 넣는다. 두 응답은 각각의 ID로 구별한다. `cancel`의 성공 응답은 취소 요청을 접수했다는 뜻이다. 최종 실행 결과와 문서 상태는 원래 요청의 응답에서 확인한다. `busy`는 다른 일반 요청과 겹쳤다는 뜻이다. `not-cancellable`은 대상 요청이 이미 끝났거나 중간에 끊을 수 없는 연산을 마치는 중이라는 뜻이다.
- `ready` 이벤트의 `requestByteLimit`은 인코딩한 요청 한 줄의 바이트 한도다. 한도를 넘으면 서버는 `frame-too-large` 오류를 보내고 종료한다. 큰 버퍼는 `append`로 나누어 보낼 수 있다. 소스 전체의 한도는 524,288자다. 큰 목표를 표시할 때는 `proof.truncated`를 확인하고, 표시 문자열이 `null`일 수도 있음을 고려한다.
- 편집기에서 커널 실행 시간을 짧게 제한하려면 서버를 시작할 때 `--timeout-ms=5000`처럼 지정한다. `--work-limit=N`으로 실행 작업량을, `--memory-mib=N`으로 네이티브 메모리를, `--host-allocation-mib=N`으로 호스트의 메모리 할당량을 제한할 수 있다.
- 편집기를 닫을 때는 `shutdown`을 보낸 뒤 응답을 읽고 서버 프로세스가 종료될 때까지 기다린다.

[저장소 레퍼런스 북(영문)](reference.md)
