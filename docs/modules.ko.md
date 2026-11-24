# 모듈 사용과 검사된 객체 배포, Rocq로 내보내기

[English](modules.md) · **한국어**

이 실습에서는 자연수를 두 배로 만드는 함수를 정의한다. 다른 모듈에서 이 함수를 쓰고, 검사된 객체를 전달하고, 같은 정리를 Rocq에서도 검사해 본다. 셸 명령은 `lol.cabal`이 있는 디렉터리에서 실행한다.

## 모듈 작성하고 검사하기

`mkdir -p Workshop`을 실행한 뒤 아래 내용을 `Workshop/Double.lol`로 저장한다.

```lol
Import lol.theories.Logic.
Import lol.theories.Nat.
Numerals O S.

Definition twice (n : nat) : nat := n + n.
Check twice.
Compute twice 2.

Theorem twice_two : twice 2 = 4.
Proof.
    reflexivity.
Qed.
Print Assumptions twice_two.
```

```bash
cabal build exe:lol
LOL=$(cabal list-bin exe:lol)
"$LOL" Workshop/Double.lol
```

실행하면 네 줄이 출력된다.

```text
nat -> nat
S (S (S (S O)))
The theorem was admitted.
(* No assumptions. *)
```

`Check`는 `twice`의 타입을 출력한다. `Compute`의 결과는 0을 나타내는 `O`에 후속자 `S`를 네 번 적용한 값이다. 정리의 양변을 계산하면 이 값이 되므로 `reflexivity.`로 목표를 닫을 수 있다. 세 번째 줄은 커널이 `Qed.`에서 완성된 증명 항을 검사하고 정리를 등록했다는 뜻이다. `Print Assumptions`는 정리가 의존하는 공리를 보여 준다. 이 정리는 공리에 의존하지 않는다.

## 다른 모듈에서 함수 쓰기

다음 내용을 `Workshop/Use.lol`로 저장하고 `"$LOL" Workshop/Use.lol`을 실행한다. 결과는 `S (S O)`다.

```lol
Import Workshop.Double.
Import lol.theories.Nat.

Compute twice (S O).
```

`Workshop.Double`은 프로젝트 루트를 기준으로 `Workshop/Double.lol`을 가리킨다. 첫 줄에서 이 모듈을 가져오면 `twice`를 쓸 수 있다. `S`와 `O`를 쓰려면 둘째 줄처럼 이들을 정의한 모듈을 직접 가져온다.

모듈을 가져오면 그 모듈에서 선언한 이름과 공개 표기를 쓸 수 있다. `Local Notation`과 `Local Tactic Notation`으로 정의한 표기는 선언한 모듈 안에서만 쓴다. 직접 가져온 두 모듈에 이름이 같은 상수가 있으면 모듈 이름을 앞에 붙여 구별한다. 어느 인자를 생략할 수 있는지는 해당 상수를 정의한 모듈에서 `Arguments`로 지정한다. 두 파일에 걸쳐 표기를 선언하고 쓰는 예는 [타입과 함수 정의하기](language.ko.md)에 있다.

## 정리의 문장과 증명 항 읽기

```bash
mkdir -p build
"$LOL" --statements Workshop/Double.lol
"$LOL" --explicit Workshop/Double.lol > build/DoubleExplicit.lol
"$LOL" build/DoubleExplicit.lol
```

`--statements`는 정리가 무엇을 주장하는지 보여 준다. `--explicit`은 그 정리를 증명하는 항까지 출력한다. `build/DoubleExplicit.lol`에서 `twice_two`의 증명에 쓰인 `@eq_refl`을 찾아보자. 같은 프로젝트 루트에서 이 파일을 다시 검사하면 출력 없이 종료한다.

## 검사한 객체 전달하기

```bash
mkdir -p build/objects
"$LOL" --emit-object=build/objects/Double.lolo Workshop/Double.lol
"$LOL" --check-only build/objects/Double.lolo
```

숨김 디렉터리 `.lolo/`를 포함해 `build/objects` 전체를 전달한다. `Double.lolo`는 `.lolo/`에 있는 의존 객체를 해시값으로 참조한다. 받는 사람은 이 릴리스의 `lol/hol`이 있는 프로젝트 루트에서 복사한 `Double.lolo`의 경로를 `--check-only`에 준다. 커널은 원본 `Workshop/*.lol` 파일 없이도 주 객체와 의존 객체를 다시 검사한다. 성공하면 출력 없이 종료한다.

## Rocq로 내보내기

`"$LOL" --rocq Workshop/Double.lol`은 주 모듈의 Rocq 소스를 표준 출력에 쓴다. 다른 모듈을 가져온 파일을 Rocq에서 검사하려면 소스 트리 전체를 내보내고, 의존하는 모듈부터 컴파일한다. 다음 명령은 Rocq 9.2.0을 기준으로 한다.

```bash
"$LOL" --rocq-dir=build/rocq Workshop/Double.lol
rocq compile -noinit -Q build/rocq '' build/rocq/lol/theories/Logic.v
rocq compile -noinit -Q build/rocq '' build/rocq/lol/theories/Nat.v
rocq compile -noinit -Q build/rocq '' build/rocq/Workshop/Double.v
```

`-Q`의 빈 인자 `''`는 `build/rocq`를 논리 모듈 경로의 루트에 대응시킨다. 내보낸 코드에서 `lol.theories.Nat`을 가져오면 Rocq는 `build/rocq/lol/theories/` 아래에서 컴파일된 모듈을 찾는다.

[저장소 레퍼런스 북(영문)](reference.md)
