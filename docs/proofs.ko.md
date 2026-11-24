# 터미널에서 정리 증명하기

[VS Code에서 한 단계 진행, 되돌리기, 커서까지 검사하기](v1.ko.md#vs-code)

[English](proofs.md) · **한국어**

## 목표를 읽고 전술을 시도한 뒤 되돌리기

저장소 루트에서 빈 세션을 연다.

```sh
cabal run -v0 lol -- --interactive
```

`LoL>` 프롬프트에 다음 명령을 입력한다. 증명할 정리는 `P`에서 `Q`로 가는 함수와 `P`의 증명이 주어지면 `Q`를 증명할 수 있다는 것이다.

```text
Theorem compose : forall P Q : Prop, (P -> Q) -> P -> Q.
Proof.
intros P Q f p.
Show.
```

`intros`는 명제와 가정을 지역 문맥에 도입한다. `Show.`는 현재 상태를 다시 보여 준다.

```text
Proof compose - Step 1

P : Prop
Q : Prop
f : P -> Q
p : P
--------------------
Q
```

선 위에는 지금 쓸 수 있는 이름과 그 타입이 있고, 선 아래에는 증명할 목표가 있다. 다음 명령을 **한 줄씩** 입력하면서 목표가 어떻게 바뀌는지 살펴보자.

```text
exact p.
apply f.
Undo.
Show.
exact (f p).
Qed.
Print Assumptions compose.
```

| 명령 | 화면에서 확인할 내용 |
| --- | --- |
| `exact p.` | `[P-StepFailed]`가 뜬다. `p`의 타입이 `P`이므로 목표 `Q`는 그대로다. 곧바로 다른 전술을 시도할 수 있다. |
| `apply f.` | 목표가 `P`로 바뀐다. `f`로 `Q`를 얻으려면 `P`의 증명을 인자로 주어야 한다. |
| `Undo.` | `The previous document state was restored.`가 뜨고 목표가 다시 `Q`가 된다. |
| `Show.` | 지역 문맥과 복원된 목표 `Q`가 보인다. 이전 목표로 돌아와도 프롬프트의 증명 상태 번호는 증가한다. |
| `exact (f p).` | `No goals remain.`이 뜬다. `f p`의 타입이 `Q`이므로 목표를 해결했다. |
| `Qed.` | 커널이 완성된 증명을 검사해 `compose`를 등록하고 `LoL>` 프롬프트로 돌아간다. |
| `Print Assumptions compose.` | `(* No assumptions. *)` |

이제 세션 기록을 새 파일에 저장하고 종료한다.

```text
:save Compose.lol
:quit
```

`Compose.lol`에는 `apply f.`와 `Undo.`를 비롯해 성공한 소스 명령이 순서대로 들어간다. 직접 입력했다가 실패한 명령은 빠진다. 셸에서 다음 명령을 실행하면 저장한 기록을 배치 모드로 다시 검사할 수 있다.

```sh
cabal run -v0 lol -- Compose.lol
```

## 파일을 한 명령씩 읽으며 증명 바꾸기

첫 실습에서 저장한 파일을 다시 연다.

```sh
cabal run -v0 lol -- --interactive Compose.lol
```

파일을 열면 커서는 **첫 명령 앞**에 있다. `:next`는 소스 명령 하나를 실행한다. `:run`은 오류가 나거나 파일 끝에 도달할 때까지 남은 명령을 실행한다. 터미널 명령은 마침표 없이 한 줄에 하나씩 입력한다. `Show.`나 `Undo.` 같은 소스 명령은 마침표로 끝낸다. `...>`가 보이면 입력하던 소스 명령을 마저 쓴다.

| 입력 | 실행 결과 |
| --- | --- |
| `:next` | 정리의 선언문을 읽는다. 프롬프트가 `compose[0]>`로 바뀐다. |
| `:next` | `Proof.`를 읽는다. 목표는 그대로다. |
| `:next` | `intros P Q f p.`를 실행한다. 목표가 `Q`가 된다. |
| `:next` | 파일에 저장된 `Show.`를 읽어 같은 목표와 가정을 다시 표시한다. |
| `:next` | `apply f.`를 실행한다. 목표가 `P`로 바뀐다. |
| `Undo.` | 파일에 읽지 않은 명령이 남아 있어 `[P-PendingSource]`가 뜬다. 목표는 여전히 `P`다. |
| `:discard` | 현재 세션에서 파일의 읽지 않은 뒷부분을 지운다. 목표는 여전히 `P`다. |
| `Undo.` | `apply f.` 직전 상태로 돌아온다. 목표는 `Q`다. |
| `:next` | 더 읽을 명령이 없어서 목표 `Q`가 그대로 보인다. `apply f.`를 다시 시도하려면 직접 입력한다. |
| `exact (f p).` | 방금 입력한 전술로 목표를 해결한다. |
| `Qed.` | 정리가 등록된다. 이 버전을 보관하려면 `:save Edited.lol`을 입력한 다음 `:quit`로 나간다. |

`:save PATH`는 읽지 않은 명령을 포함한 **현재 문서 전체**를 저장한다. 남은 명령을 보관하려면 `:discard`를 실행하기 **전에** 다른 이름으로 저장한다. 기존 파일 이름을 지정하면 그 파일의 내용을 덮어쓴다. 원래 파일 이름으로 저장하기 전까지는 `:next`나 `:discard`를 써도 현재 세션에만 영향을 준다.

### 어디까지 되돌릴 수 있나?

`Undo.`는 **문서 상태를 바꾼 명령**을 하나 되돌린다. `Show.`는 목표를 읽기만 하므로 되돌릴 단계가 생기지 않는다. `Qed.`를 되돌리면 완성한 증명이 다시 열리고, `Abort.`를 되돌리면 포기한 증명이 다시 열린다. 빈 세션에서 처음부터 `Undo.`를 입력하면 `[P-NoHistory]`가 뜬다.

터미널은 이전 문서 상태를 최대 15개 보관하며, `Undo.`로 돌아갈 가장 최근 상태 일곱 개를 우선 보관한다. 오래된 상태는 만료될 수 있다(`[P-ExpiredState]`). 증명을 다시 열려면 해당 증명을 처리하던 실행기의 저장 상태도 복원할 수 있어야 한다. 초반 단계로 돌아갈 계획이라면 소스를 저장해 둔다. 나중에 `--interactive`로 파일을 열어 `:next`로 원하는 단계까지 진행할 수 있다.

### 파일에서 실패한 전술 고치기

[틀린 등식이 들어 있는 예제](../example/rejected/Proof.lol)를 연다.

```sh
cabal run -v0 lol -- --interactive example/rejected/Proof.lol
```

1. `:run`을 입력한다. 첫 정리 `right`는 성공한다. 두 번째 정리 `wrong`에서는 목표 `1 + 1 = 3`에 `reflexivity.`를 적용하면 실패한다.
2. `:discard`를 입력한다. 읽지 않은 뒷부분에는 실패한 `reflexivity.`와 그다음 `Qed.`가 들어 있다. 이를 지우면 현재 목표에서 다른 전술을 입력할 수 있다.
3. 이 예제에서는 등식이 성립하지 않으므로 `Abort.`로 `wrong`을 포기한다. 앞서 등록한 `right`는 계속 쓸 수 있다. `:quit`로 나가면 원본 예제 파일은 그대로다.

## 여러 목표 다루기

다음 내용을 `Branches.lol`로 저장하고 `cabal run -v0 lol -- Branches.lol`로 실행한다. 첫 줄에서 가져온 모듈이 논리곱 `and`를 제공한다.

```text
Import lol.theories.Logic.

Theorem pair_swapped : forall P Q : Prop, P -> Q -> and Q P.
Proof.
    intros P Q p q.
    split.
    - exact q.
    - exact p.
Qed.

Theorem duplicate : forall P : Prop, P -> and P P.
Proof.
    intros P p.
    split; exact p.
Qed.
```

첫 증명에서 `split.`은 `Q`와 `P` 두 목표를 이 순서대로 만든다. 각 글머리표(`-`)에서 한 갈래의 증명을 시작한다. 두 번째 증명에서는 양쪽 목표가 모두 `P`다. 세미콜론으로 전술을 이어 쓰면 `split`이 만든 **각각의** 목표에 `exact p`를 적용한다.

## 진행 중인 증명의 우주 확인하기

빈 대화형 세션에서 다음 명령을 입력한다.

```text
Polymorphic Theorem poly@{u} : forall A : Type@{u}, A -> A.
Proof.
intros A x.
Show Universes.
exact x.
Qed.
```

이 예제에서 `Show Universes.`를 실행하면 `Universes of the proof: @{u}`가 뜨고 목표는 그대로다. 이 명령은 아직 확정되지 않은 레벨을 포함한 현재 우주 이름과, 증명에서 선언되거나 기록된 제약을 보여 준다. 앞서 본 `compose`의 증명 중에는 `This proof has no universe.`가 뜬다. `LoL>`에서 증명을 열지 않고 입력하면 `[P-NoProof]`가 뜬다.

## 등식으로 고쳐 쓰기와 사용자 전술 불러오기

- **가정의 타입 고치기.** `transport`의 가정에는 `e : a = b`와 `pb : P b`가 있다. `rewrite <- e in pb.`로 `pb`의 타입을 `P a`로 바꾸면 `exact pb.`로 목표를 닫을 수 있다. 목표 안에서 등식을 왼쪽에서 오른쪽으로 적용할 때는 `rewrite e.`를 쓴다. [Equality.lol](../example/Equality.lol)
- **귀납 가정 사용하기.** `plus_zero_tactics`에서 `induction n.`은 기저 사례와 후속자 사례를 만든다. 후속자 사례에서는 `simpl.`로 덧셈을 펼치고 `rewrite IHn.`으로 귀납 가정을 적용한다. [Basics.lol](../example/Basics.lol)
- **Hol로 쓴 전술 사용하기.** 저장소 루트에서 정리를 시작하기 전에 `Load Tactics "example/UserTactics.hol".`를 실행한다. `give`는 증명 항 후보를 받는 전술이다. 예제의 `tactic give (conj P Q p _).`는 비워 둔 두 번째 성분을 목표로 남긴다. `tactic hypothesis.`가 그 자리에 들어갈 가정을 찾고, `Qed.`에서 완성된 증명을 검사한다. [증명 스크립트](../example/UserTactics.lol) · [전술 정의](../example/UserTactics.hol)

```sh
cabal run -v0 lol -- example/Equality.lol
cabal run -v0 lol -- example/UserTactics.lol
```

[저장소 레퍼런스 북(영문)](reference.md)
