# LoL에서 타입과 함수 정의하기

[V1 표기 스코프, custom entry와 절 변수](v1.ko.md)

[English](language.md) · **한국어**

프로젝트 루트에 `Walkthrough.lol`을 만들고 아래 LoL 예제를 차례로 추가한다. 중간에 `ReadPublic.lol`로 표시한 예제만 두 번째 파일에 쓴다. 각 단계를 마칠 때마다 프로젝트 루트에서 다음 명령으로 결과를 확인한다. `Check`는 식의 타입을, `Compute`는 식을 계산한 값을 출력한다.

```sh
cabal run -v0 lol -- Walkthrough.lol
```

## 귀납형과 재귀 함수

```lol
Inductive Height : Set := | base : Height | up : Height -> Height.
Numerals base up.

Fixpoint addHeight (n m : Height) {struct n} : Height :=
    match n with
    | base => m
    | up p => up (addHeight p m)
    end.

Infix "+" := addHeight (at level 50, left associativity).
Definition three : Height := 2 + 1.
Check addHeight.
Compute three.
```

`Height`의 값은 `base`에 생성자 `up`을 0번 이상 적용해서 만든다. `Numerals base up.`을 선언하면 LoL은 `2`를 `up (up base)`로 읽는다. `Infix` 선언 덕분에 `addHeight 2 1`을 `2 + 1`로 쓸 수 있다.

`{struct n}`은 재귀 호출 때마다 어느 인자가 작아져야 하는지 지정한다. `up p` 분기에서 `p`는 `n`의 바로 아래에 있는 부분항이다. 위의 `Check`와 `Compute`를 실행하면 다음 두 줄이 차례로 나온다.

```text
Height -> Height -> Height
up (up (up base))
```

## 암시적 인자와 명시적 적용

```lol
Definition keep (A : Set) (x y : A) : A := x.
Arguments keep {A} x y.
Check @keep.
Compute keep three 1.
Compute @keep Height three 1.
```

`keep`의 첫 번째 인자는 타입이다. `Arguments keep {A} x y.`를 선언하면 `keep three 1`에서 LoL이 `three`의 타입을 보고 `A`를 추론한다. 타입을 직접 지정하려면 `@keep`을 쓴다. 두 `Compute`의 결과는 모두 `up (up (up base))`다.

처음부터 인자를 암시적으로 받으려면 정의에서 `(A : Set)` 자리에 `{A : Set}`을 쓴다. 기존 상수의 암시적 인자를 바꾸려면 그 상수를 정의한 모듈에 `Arguments`를 쓴다. 이 모듈을 가져오는 쪽에는 해당 상수에 대한 마지막 `Arguments` 선언이 적용된다.

## 항 표기와 전술 표기

```lol
Local Notation "'taller' x" := (up x) (at level 9, right associativity).
Local Tactic Notation "closewith $term" := exact.

Compute taller base.

Theorem retain : forall P : Prop, P -> P.
Proof.
    intros P h.
    closewith h.
Qed.
Print Assumptions retain.
```

항에서 `taller base`의 계산 결과는 `up base`다. 이 값은 현재 활성화된 표기로 `taller base`라고 출력된다. 증명 안에서 `closewith h.`는 `exact h.`를 실행한다. `Qed.` 뒤에 `Print Assumptions retain.`을 실행하면 `(* No assumptions. *)`가 나온다.

다른 모듈에서 앞서 정의한 덧셈을 쓰려면 `Walkthrough.lol`과 같은 디렉터리에 **별도 파일 `ReadPublic.lol`**을 만들고 다음 두 줄을 넣는다. `cabal run -v0 lol -- ReadPublic.lol`을 실행하면 `up (up (up base))`가 나온다. `Local`로 선언한 `taller`와 `closewith`는 `Walkthrough.lol` 안에서만 쓸 수 있다.

```lol
Import Walkthrough.
Compute 2 + 1.
```

`Notation`이나 `Tactic Notation`을 `Local` 없이 선언하면 이 모듈을 직접 가져오는 쪽에서도 그 표기를 쓸 수 있다. `example.Notations`는 항 표기 `~~`와 전술 `finish`를 공개한다. 이를 가져오는 `example/Syntax.lol`을 실행하면 `Compute ~~ Low.`는 `High`를, `Compute ~~ ~~ Low.`는 `Low`를 출력한다. [표기를 선언하는 예제](../example/Notations.lol) · [가져온 표기를 사용하는 예제](../example/Syntax.lol)

## 앞 필드에 의존하는 레코드

다시 `Walkthrough.lol`로 돌아가 아래 선언을 추가한다. `Package`에는 타입 하나와 그 타입에 속하는 값 하나를 함께 담는다.

```lol
#[projections(primitive)]
Record Package : Type@{1} := pack { carrier : Set ; point : carrier }.

Definition unpack (p : Package) : p.(carrier) := p.(point).
Definition sample : Package := pack Height three.
Check unpack.
Compute unpack sample.
```

`pack Height three`에서 `carrier`에 넣은 타입은 `Height`다. 따라서 `point`에는 `Height`의 값을 넣어야 한다. 임의의 `p : Package`에 대해 `p.(point)`의 타입은 `p.(carrier)`다. `Check unpack.`은 `forall x : Package, x.(carrier)`를, `Compute unpack sample.`은 지역 표기를 써서 `taller taller taller base`를 출력한다.

`#[projections(primitive)]`는 이 레코드에 원시 투영을 지정한다. 모든 필드를 투영한 값으로 레코드를 다시 만들면 원래 레코드와 정의적으로 같다. 이 성질을 레코드의 η(에타)라고 한다. `swap_swap` 예제는 이 성질 덕분에 `intros` 다음에 `reflexivity.`만으로 증명을 마친다. [레코드와 투영 예제](../example/Records.lol)

## 여러 우주에서 같은 정의 사용하기

```lol
Polymorphic Definition ident@{u} (A : Type@{u}) (x : A) : A := x.
Check ident@{0}.
Compute ident@{1} Set Height.
```

`Set`은 `Type@{0}`이다. `ident@{0}`에는 `Height`처럼 작은 타입과 그 타입의 값을 넘길 수 있다. `Set` 자체를 넘길 때는 `ident@{1}`을 쓴다. 위 `Compute`의 결과는 `Height`다. [우주 다형성과 누적성 예제](../example/Universes.lol)

귀납형을 적용한 결과가 인자에 따라 다른 우주에 속하도록 하려면 그 귀납형 선언에 `#[universes(template)]`를 붙인다.

```lol
#[universes(template)]
Inductive Box (A : Type) : Type := | box : A -> Box A.

Check (Box Height).
Check (Box Set).
```

`Box Height`의 타입은 `Type@{0}`이고 `Box Set`의 타입은 `Type@{1}`이다. 두 경우 모두 `Box`에 넘긴 인자가 우주를 결정한다.

## 귀납형이나 재귀 함수의 정의를 거부할 때

- **`[I-Pos]` (엄격 양성 조건)**. 생성자 `wrap : (Bad -> Empty) -> Bad`에는 `Bad`를 입력으로 받는 함수가 필드로 들어간다. 이 위치에 나타나는 `Bad`는 엄격 양성 조건을 어긴다. 재귀 자료를 담으려면 `up : Height -> Height`처럼 하위 값을 직접 저장한다. 그 값을 처리하는 함수는 `addHeight`처럼 따로 정의할 수 있다. [거부되는 생성자 예제](../example/rejected/Positivity.lol)
- **`[F-Guard]` (구조적 재귀)**. `forever (S n)`으로 재귀 호출하면 인자가 더 커진다. `{struct n}`으로 지정한 인자를 `match`로 분해하고, 각 분기에서 그 인자의 부분항을 넘겨 재귀 호출하는지 살펴본다. 위 예제의 `up p` 분기에서 호출하는 `addHeight p m`이 그 예다. [거부되는 재귀 호출 예제](../example/rejected/Guard.lol)

## 표준 라이브러리 사용하기

라이브러리 예제에서는 `lol.theories.Nat`과 `lol.theories.List`를 가져와 `nat`, `list`, `length`, `rev`를 쓴다. 첫 번째 `Compute`는 원소가 셋인 리스트의 길이를 `S (S (S O))`로 출력한다. 프로젝트 루트에서 다음 명령으로 실행한다. [표준 라이브러리 예제](../example/Library.lol)

```sh
cabal run -v0 lol -- example/Library.lol
```

길이를 인덱스로 쓰면 수열의 길이가 타입에 나타난다. `vec`의 `match v in vec _ k return ...` 절에서는 결과 타입이 길이 인덱스 `k`에 어떻게 의존하는지 적는다. [길이를 인덱스로 갖는 벡터](../example/Vectors.lol) · [상호 귀납형과 상호 재귀](../example/Mutual.lol)

[저장소 레퍼런스 북(영문)](reference.md)
