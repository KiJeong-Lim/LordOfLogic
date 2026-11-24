# LoL

[V1 표기 스코프와 custom entry, Search, Section, VS Code 증명 편집기](docs/v1.ko.md)

[English](README.md) · **한국어**

LoL은 귀납적 구성 계산(Calculus of Inductive Constructions)에 기반한 증명 보조기다. 커널은 λProlog로 작성했고 이 저장소의 λProlog 엔진인 Hol이 실행한다. Haskell 호스트는 사용자의 명령을 읽고 모듈과 객체를 관리하며 Hol을 호출한다. 환원·변환·타이핑 규칙은 커널이 담당한다. [커널 소스](lol/hol/kernel.hol)

LoL의 표면 문법은 Rocq를 따른다. `Inductive`, `Record`, `Fixpoint`, `match`, `Theorem … Proof. … Qed.`를 쓸 수 있고, 표기와 전술을 정의할 수 있다. 검사를 마친 모듈은 Rocq 소스로 내보낼 수 있다.

커널의 판단은 Hol 컴파일러와 C 가상 기계, 단일화·GC·FFI, 엄격 양성과 가드
오라클, 우주 제약 결정 절차와 항·환경의 번역에도 의존한다. 로컬 릴리스 검사는 라이브러리와
양성 예제의 export를 Rocq 9.2.0으로 다시 검사하고, 정상 예제를 ASan·UBSan으로
검사한다. [릴리스 검사 재현](docs/verification.ko.md)

처음 증명을 써 본다면 [터미널 증명 실습](docs/proofs.ko.md)에서 `:next`로 파일을 한 명령씩 실행하고 `Undo.`로 전술을 되돌려 보자. 기능별 사용법은 [타입과 함수 정의하기](docs/language.ko.md), [모듈·객체·Rocq 내보내기](docs/modules.ko.md), [편집기 연동](docs/editor.ko.md)에 있다. 전체 명령과 구현 파일의 위치는 [저장소 레퍼런스 북(영문)](docs/reference.md)에서 찾을 수 있다.

## 빌드하기

패키지는 `filepath >= 1.4`를 사용하며 로컬 새니타이저 검사에서 1.4로도 빌드한다. V1은 절과
문맥을 지원하고 sort로 `Prop`, `Set`, `Type`을 쓴다. 공귀납 선언,
cofixpoint와 엄격 명제 `SProp`의 타이핑은 이 버전의 범위 밖이다.
`Admitted` 명령과 우주 검사를 끄는 옵션은 제공하지 않는다.

Linux에서 GHC 9.6.7과 cabal-install 3.14.2로 빌드를 확인했다. 엔진의 C 코드를 빌드하려면 C11 컴파일러가 필요하다.

```bash
cabal build lol
```

`stack.yaml`은 Stackage 스냅숏 `lts-24.41`을 지정한다. 이 저장소에서 검증한 빌드 방식은 Cabal이다.

## 파일 실행하기

저장소 루트에서 LoL을 실행한다. LoL은 현재 디렉터리 아래의 `lol/hol`에서 커널과 정교화기, 전술을 읽는다. `Import a.b.C.`는 같은 디렉터리를 기준으로 `a/b/C.lol`을 읽는다.

```bash
cabal run -v0 lol -- example/Basics.lol
```

이 예제는 타입 검사, 계산, 정리 등록, 정리가 의존하는 공리 조회 결과를 차례로 출력한다.

```text
Nat -> Nat -> Nat
Succ (Succ (Succ (Succ Zero)))
The theorem was accepted.
(* No assumptions. *)
```

명령이 실패하면 앞서 성공한 명령들의 출력에 이어 오류 위치와 원인이 나오고 종료 코드 1을 반환한다.

```text
example/rejected/Positivity.lol:10:1-10:55: error: [LoL-KernelError]
    |
 10 | Inductive Bad : Type := | wrap : (Bad -> Empty) -> Bad.
    | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
[I-Pos] the oracle rejected this command
  the oracle says: a family of the block occurs where it is not strictly positive
```

`cabal list-bin lol`로 실행 파일 경로를 확인해 직접 실행할 수도 있다.

## 예제

각 예제의 첫 주석에 실행 방법이 있다. 정리를 증명하는 예제 끝의 `Print Assumptions`는 그 정리가 의존하는 공리를 보여 준다.

| 파일 | 살펴볼 내용 |
| --- | --- |
| [`Basics.lol`](example/Basics.lol) | 귀납형과 재귀 함수를 정의하고 `Check`와 `Compute`로 살펴본다. 같은 정리를 증명 항과 전술로 각각 증명한다. |
| [`Logic.lol`](example/Logic.lol) | 증명 모드에서 논리곱, 논리합, 부정, 동치(`iff`), 존재 명제를 다룬다. |
| [`Arithmetic.lol`](example/Arithmetic.lol) | `Basics.lol`에서 정의한 자연수를 가져와 덧셈의 교환·결합법칙과 곱셈의 분배법칙을 귀납법으로 증명한다. |
| [`Equality.lol`](example/Equality.lol) | 등식을 다루는 `injection`, `discriminate`, `symmetry`, `transitivity`, `rewrite <- e in h`, `f_equal`을 쓴다. |
| [`Tacticals.lol`](example/Tacticals.lol) | `;`, `repeat`, `all:`, `first`, `try`로 전술을 조합하고 `constructor 2`, `assert`, `specialize`, `unfold`, `change`, `simpl in`을 쓴다. |
| [`Library.lol`](example/Library.lol) | 표준 라이브러리를 가져와 숫자 표기를 쓰고 라이브러리 보조정리로 식을 다시 쓴다. |
| [`Lists.lol`](example/Lists.lol) | 리스트 함수를 다루고 두 보조정리에서 `rev (rev l) = l`을 증명한다. |
| [`Vectors.lol`](example/Vectors.lol) | 길이를 인덱스로 갖는 벡터, `return` 절을 둔 `match`, 인덱스가 있는 귀납형에 대한 귀납법을 다룬다. |
| [`Mutual.lol`](example/Mutual.lol) | 상호 귀납적 술어와 타입을 정의하고 상호 재귀를 쓴다. 한 번의 귀납법으로 두 명제를 증명한다. |
| [`Decisions.lol`](example/Decisions.lol) | 판정 결과에 증명을 담고, 판정 가능한 명제에 대해 배중률을 증명한다. |
| [`Numbers.lol`](example/Numbers.lol) | 표준 라이브러리의 나눗셈, 최대공약수, 소수를 다룬다. |
| [`Sorting.lol`](example/Sorting.lol) | 삽입 정렬과 병합 정렬의 정확성을 증명한다. |
| [`STLC.lol`](example/STLC.lol) | 단순 타입 람다 계산에서 타이핑 유도와 한 단계 환원을 살펴보고 타입 보존을 증명한다. |
| [`Records.lol`](example/Records.lol) | 템플릿 우주와 원시 투영을 갖는 레코드를 정의하고 레코드의 정의적 η 법칙을 쓴다. |
| [`Universes.lol`](example/Universes.lol) | `Prop`, `Set`, `Type@{i}`, 우주의 누적성, 우주 다형적인 정의를 다룬다. |
| [`V1Scopes.lol`](example/V1Scopes.lol), [`V1.lol`](example/V1.lol) | 스코프가 바뀌면 같은 식에서 다른 값이 나오는 예, 사용자 정의 문법, 절 변수와 Search. |
| [`Notations.lol`](example/Notations.lol), [`Syntax.lol`](example/Syntax.lol) | 한 모듈에서 항 표기와 전술 표기를 공개하고 다른 모듈에서 사용한다. |
| [`UserTactics.lol`](example/UserTactics.lol), [`UserTactics.hol`](example/UserTactics.hol) | Hol로 전술 두 개를 작성하고 `Load Tactics`로 불러온다. |
| [`Axioms.lol`](example/Axioms.lol) | 공리를 하나 선언하고, 그 공리를 쓰는 정리와 쓰지 않는 정리에 각각 `Print Assumptions`를 실행한다. |

다음은 LoL의 각 검사가 어떤 입력을 거부하는지 보여 주는 예제다. [거부 예제 디렉터리](example/rejected)

| 파일 | 거부 사유 |
| --- | --- |
| [`Positivity.lol`](example/rejected/Positivity.lol) | `[I-Pos]` 생성자 필드에 담는 함수의 화살표 왼쪽에 정의 중인 귀납형이 나타난다. |
| [`Guard.lol`](example/rejected/Guard.lol) | `[F-Guard]` 더 큰 인자로 재귀 호출한다. |
| [`Universe.lol`](example/rejected/Universe.lol) | `[T-Conv]` `Type@{0}`을 자기 자신의 원소로 쓴다. |
| [`Elimination.lol`](example/rejected/Elimination.lol) | `[I-Elim-Prop]` 논리합의 증명을 분해해 `bool` 값을 결정한다. |
| [`Proof.lol`](example/rejected/Proof.lol) | `[P-StepFailed]` `1 + 1 = 3`에 `reflexivity`를 적용한다. |

## 실행 옵션

```text
lol [OPTIONS] FILE.lol
lol --check-only [--no-axioms] FILE.lolo
lol --interactive [FILE.lol]
lol --server
```

| 옵션 | 동작 |
| --- | --- |
| `--explicit` | 검사한 선언을 모든 인자와 함께 출력한다. 정리는 증명 항까지 보여 준다. |
| `--statements` | `--explicit`과 같은 방식으로 출력하되 정리는 문장만 보여 준다. |
| `--rocq` | 주 모듈의 Rocq 소스를 표준 출력에 쓴다. |
| `--rocq-dir=DIR` | 주 모듈과 그 모듈이 가져온 모듈의 Rocq 소스를 `DIR` 아래에 쓴다. |
| `--emit-object=FILE.lolo` | 검사한 모듈을 객체로 저장한다. 의존 객체는 그 옆의 숨김 디렉터리 `.lolo/`에 저장한다. |
| `--check-only` | 객체와 의존 모듈을 다시 검사하고 각 선언과 정리별 가정을 출력한다. |
| `--no-axioms` | `--check-only`와 함께 쓰며 검사 대상 어느 모듈에든 공리가 선언되어 있으면 실패한다. |
| `--work-limit=N` | 엔진을 한 번 실행할 때 허용하는 작업량을 제한한다. |
| `--timeout-ms=N` | 엔진 한 번의 실행 시간을 밀리초 단위로 제한한다. |
| `--memory-mib=N` | 엔진의 메모리 사용량을 MiB 단위로 제한한다. |
| `--host-allocation-mib=N` | 엔진 실행 중 호스트의 메모리 할당량을 MiB 단위로 제한한다. |
| `--help` | 사용법을 출력한다. |

예를 들어 `cabal run -v0 lol -- --rocq example/Arithmetic.lol`을 실행하면 `example.Basics`를 가져오는 `Arithmetic.lol`의 Rocq 소스가 나온다.

## 터미널에서 증명하기

```bash
cabal run -v0 lol -- --interactive example/Universes.lol
```

`LoL>` 프롬프트에 다음 명령을 한 줄씩 입력한다.

```text
:next
:next
:run
:quit
```

두 번의 `:next`는 각각 `Check Prop.`과 `Check Set.`을 실행한다. 두 명령 모두 `Type@{1}`을 출력한다. `:run`은 오류를 만나거나 파일이 끝날 때까지 남은 명령을 실행한다.

직접 증명을 입력하려면 파일을 지정하지 않고 세션을 연다.

```bash
cabal run -v0 lol -- --interactive
```

```text
Theorem keep : forall P : Prop, P -> P.
Proof.
intros P p.
exact p.
Undo.
Show.
exact p.
Qed.
:save Keep.lol
:quit
```

첫 `exact p.`에서 목표가 닫힌다. `Undo.`를 입력하면 가정 `p : P`와 목표 `P`가 돌아온다. `Show.`로 이 상태를 보고 `exact p.`를 다시 입력해 목표를 닫는다. `Qed.`는 완성된 증명을 검사한다. `:save Keep.lol`은 지금까지의 문서를 파일로 저장한다. 증명하는 도중에 우주 제약을 보려면 `Show Universes.`를, 진행 중인 정리를 포기하려면 `Abort.`를 쓴다.

파일 중간에서 다른 전술을 써 보려면 `:discard`로 읽지 않은 뒷부분을 지운 뒤 입력한다. 이때 현재 목표는 그대로다. 읽지 않은 부분까지 보관하려면 먼저 `:save PATH`로 다른 파일에 저장한다. `:discard` 다음에는 `:next`가 읽을 명령이 없다. 취소한 전술을 다시 쓰려면 그 전술을 직접 입력한다.

## 편집기 서버

`--server`는 프로토콜 버전 2를 사용한다. 표준 입력에서 요청을 한 줄에 하나의 JSON 객체로 읽고, 표준 출력에 같은 형식으로 응답한다. 요청 메서드는 `open`, `append`, `replace`, `next`, `show`, `undo`, `cancel`, `close`, `shutdown`이다. 문서 참조에는 `open` 응답이 돌려준 `incarnation`이 들어간다. 문서를 닫았다가 같은 이름으로 다시 열어도 이전 참조는 효력을 잃는다.

```json
{"protocol":2,"id":1,"method":"open","document":"demo","revision":1,"path":"example/Demo.lol","source":"Theorem id : forall P : Prop, P -> P.\nProof.\nintros P h.\nexact h.\nQed.\n"}
{"protocol":2,"id":2,"method":"shutdown"}
```

요청과 응답의 정의는 [프로토콜 소스](src/LoL/Proof/Protocol.hs)에 있다. [편집기 연동 안내](docs/editor.ko.md)에는 한 명령씩 진행하고 목표를 읽은 뒤 이전 위치로 되돌아가는 Python 클라이언트가 있다.

## 언어

**명령**

- 선언에는 `Inductive`(상호 귀납 블록은 `with`), `Record`, `Definition`, `Fixpoint`, `Theorem`, `Lemma`, `Axiom`, `Polymorphic`를 쓴다.
- 조회에는 `Check`, `Compute`, `Print Assumptions`, `Search`를 쓴다.
- 모듈을 가져올 때는 `Import`, 공통 가정을 묶을 때는 `Section`, `Context`, `End`를 쓴다.
- 표기와 인자 선언에는 `Infix`, `Notation`, `Reserved Notation`, `Declare Scope`, `Open Scope`, `Declare Custom Entry`, `Tactic Notation`, `Arguments`, `Numerals`를 쓴다.
- 증명 문서에서 `Proof`, `Qed`, `Show`, `Show Universes`, `Undo`, `Abort`, `Load Tactics`를 쓸 수 있다.

**전술**

- `intro`, `intros`, `exact`, `apply`, `refine`, `assumption`
- `reflexivity`, `symmetry`, `transitivity`, `rewrite`
- `simpl`, `unfold`, `change`
- `destruct`, `induction`, `injection`, `discriminate`
- `constructor`, `split`, `left`, `right`, `exists`, `exfalso`
- `assert`, `specialize`
- `first`, `try`, `repeat`, `all:`, `;`와 분기 기호(bullet)

`destruct h as a b`와 `induction n as p IHp`는 분기 순서에 맞춰 새 가정에 이름을 붙인다. 예를 들어 `or A B`의 증명을 분해하면 첫 분기의 가정 이름이 `a`, 둘째 분기의 가정 이름이 `b`가 된다.

`Load Tactics "file.hol".`로 Hol 프로그램을 읽어 전술을 추가하고 `tactic name (argument).`로 호출할 수 있다. 전술은 증명 항을 제안하고 커널은 `Qed.`에서 완성된 증명을 검사한다. [Hol로 작성한 전술 두 가지](example/UserTactics.hol)

**속성.** `#[universes(template)]`을 붙인 귀납형이나 레코드는 인자에 따라 결과 우주가 정해진다. `#[projections(primitive)]`를 붙인 레코드의 원시 투영은 `r.(field)`로 쓴다.

**모듈.** `Import M.`을 쓰면 `M`이 직접 선언한 이름을 쓸 수 있다. `M`이 가져온 다른 모듈의 이름까지 쓰려면 해당 모듈을 직접 가져온다. 표기는 그 표기가 가리키는 상수를 선언한 모듈에 속한다. 가져올 모듈의 경로는 프로젝트 루트 안에 있어야 한다.

## 표준 라이브러리

[lol/theories](lol/theories)에는 공리를 쓰지 않는 모듈 29개가 있다. `Import lol.theories.Name.`으로 가져온다.

| 모듈 | 내용 |
| --- | --- |
| `Logic`, `LogicProperties` | 논리 연결사, 양화사, 등식, `prod`, `sum`, `option` |
| `Bool`, `BoolOrder`, `Decidable` | 불리언, 비교, 증명을 동반한 판정 |
| `Nat`, `NatProperties`, `NatSearch`, `Order`, `OrderLattice` | 0과 후속자로 표현한 자연수, 산술, 유한 탐색, 순서 |
| `Division`, `Divisibility`, `Gcd`, `Primes` | 정초 재귀에 의한 나눗셈, 유클리드 알고리즘, 소수의 무한성 |
| `List`, `ListProperties`, `ListAlgorithms`, `ListDecidable`, `ListRelations`, `Sorting` | 리스트, 순열, 삽입 정렬과 병합 정렬의 정확성 증명 |
| `Vec`, `Sigma`, `ProductProperties`, `SumProperties`, `OptionProperties`, `RelationProperties` | 길이가 인덱스인 벡터, 의존쌍, 자료형과 관계의 성질 |
| `Wf`, `WfNat` | 접근 가능성(accessibility)과 정초 재귀 |
| `STLC` | 단순 타입 람다 계산의 진행과 보존 정리 |

## 선언이 검사되는 과정

1. 호스트가 현재 범위에 있는 표기로 명령을 파싱하고 정교화 전의 항으로 옮긴다.
2. 정교화기가 암시적 인자와 구멍을 채운다. 증명 중에는 `lol/hol/tactics*.hol`의 전술과 증명 엔진이 증명 항을 만든다. 풀리지 않은 구멍이 있으면 엔진이 디버거에서 멈추며, 각 디버거 상태가 하나의 증명 상태에 대응한다. [정교화기](lol/hol/elab.hol) · [증명 엔진](lol/hol/proof.hol)
3. 커널이 미결 변수가 없는 완성된 항을 검사한다. `Qed`에서는 새 커널로 증명 전체를 다시 검사한다.
4. 커널은 엄격 양성(strict positivity)과 `fix`의 재귀 호출에 대한 가드 조건을 호스트의 오라클에 묻는다. 오라클은 Rocq의 `kernel/indtypes.ml`과 `kernel/inductive.ml`에 있는 알고리즘에 건전성 수정을 반영한 것이다. 검사에 약한 머리 정규형(WHNF)이 필요할 때마다 커널에 환원을 요청한다.

## 저장소 구조

| 경로 | 내용 |
| --- | --- |
| `src/Main.hs` | 실행 파일의 진입점 |
| `src/LoL/` | Haskell 호스트. 문법과 표기(`Front/`), 명령, 모듈과 객체, 오라클(`Oracle/`), 증명 문서와 터미널·서버(`Proof/`), Rocq 내보내기(`Export/`) |
| `src/Hol/BETA/` | Hol의 λProlog 프런트엔드. 렉서, 파서, 타입 검사기, 모듈 로더, 디버거 |
| `src/Hol/V1/` | Hol 바이트코드 컴파일러와 런타임 서비스 |
| `src/Hol/V2/` | LoL이 사용하는 임베딩 API. 실행을 준비한 프로그램, 캐시, 직렬화 형식 |
| `src/X/` | C 바이트코드 실행기와 Haskell 바인딩 |
| `src/Json/` | 서버 프로토콜의 JSON 처리 |
| `src/Calc/`, `src/Y/`, `src/Z/` | Hol의 프레스버거 산술과 보조 함수 |
| `lol/hol/` | Hol로 작성한 커널, 정교화기, 전술 |
| `lol/theories/` | 표준 라이브러리 |
| `example/` | 위에서 소개한 예제 |

`src/Hol/BETA/PlanHol{Lexer,Parser}.hs`와 `src/Json/Json{Lexer,Parser}.hs`는 생성기가 만드는 렉서와 파서다. 이 파일들은 생성기를 통해 갱신한다.

## 저장소 밖에 생성되는 파일

LoL은 컴파일한 Hol 프로그램을 `$XDG_CACHE_HOME/lol/hol-v2` 아래에 저장한다. 기본 경로는 `~/.cache/lol/hol-v2`다. 캐시를 끄려면 환경 변수 `LOL_HOL_CACHE=off`를 설정한다.

## 라이선스

BSD 3-Clause. [라이선스 원문](LICENSE)

## 검사한 모듈 다시 불러오기

POSIX 환경에서 이미 수락한 소스 모듈은
`$XDG_CACHE_HOME/lord-of-logic/imports` 아래의 전용 캐시에서 정교화된
선언을 다시 쓸 수 있다. 기본 위치는 `~/.cache/lord-of-logic/imports`다.
로더는 소스와 Hol 입력을 확인하고 의존 모듈을 찾은 뒤 저장된 선언을
커널로 다시 검사한다. 캐시를 사용할 수 없으면 소스를 처리한다.
`LOL_IMPORT_CACHE=off`는 소스로만 검사하며, `LOL_IMPORT_CACHE_TRACE=1`은
캐시를 실제 사용한 모듈 이름을 표준 오류에 남긴다. Hol 프로그램을
컴파일한 캐시는 별도의 `LOL_HOL_CACHE` 설정을 쓴다.
