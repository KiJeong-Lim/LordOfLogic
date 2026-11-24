# Visual Studio Code에서 LoL 증명하기

[English](README.md)

검사할 명령에 커서를 놓고 **LoL: Check to Cursor**를 실행한다. 탐색기의
**LoL Proof** 창에 서버가 보낸 가정과 목표가 표시된다. WSL이나 SSH로 연
프로젝트에서는 해당 원격 환경의 실행 파일이 증명을 검사한다.

## 설치하기

`lol.cabal`이 있는 루트에서 검사기를 빌드하고 실행 파일의 경로를 확인한다.

```sh
cabal build exe:lol
cabal list-bin exe:lol
```

Node.js 22 이상을 사용해 확장 디렉터리에서 VSIX를 만든다.

```sh
cd editors/vscode
npx --yes --package @vscode/vsce@3.7.1 vsce package --no-dependencies --out lord-of-logic.vsix
```

증명을 작성할 VS Code 창에서 **Extensions: Install from VSIX…**를 실행해
`lord-of-logic.vsix`를 선택한다. 원격 작업 공간에서는 해당 환경에
설치한다. 신뢰하는 프로젝트의 `lol/hol`이 보이는 루트를 연 뒤 **Settings**의
`lordOfLogic.executable`에 Cabal이 출력한 절대 경로를 넣는다. `lol`이 PATH에
있으면 기본값을 쓸 수 있다. 기본 인자는 `["--server"]`다. 하위 명령을
받는 실행기를 쓸 때는 `lordOfLogic.arguments`에 하위 명령과 `--server`를
차례로 적는다.

## 전술을 실행하고 바꿔 보기

프로젝트에 `Demo.lol`을 만들고 다음 증명을 적는다.

```text
Theorem demo : forall P Q : Prop, (P -> Q) -> P -> Q.
Proof.
    intros P Q f p.
    apply f.
    exact p.
Qed.
```

1. `apply f.`에 커서를 놓고 명령 팔레트의 **LoL: Check to Cursor**나
   편집기 제목 표시줄의 실행 버튼을 누른다. 목표는 `P`다. 증명 명령을
   처음 실행할 때 서버가 뜬다.
2. **LoL: Previous Command**를 누르면 커서가 `intros P Q f p.` 끝으로
   돌아가고 목표는 `Q`가 된다. **LoL: Next Command**로 `apply f.`를
   다시 실행하면 목표 `P`가 보인다.
3. `apply f.`를 `exact p.`로 바꾸고 커서를 그 명령에 놓는다. 이 단계의
   목표는 `Q`이므로 가정 `p : P`로는 증명할 수 없다. 실패한 전술에
   밑줄이 생기고 **Problems**에 진단이 표시된다. `apply f.`로 고친 뒤
   `Qed.`까지 진행하면 `The theorem was accepted.`가 나온다.
4. **LoL: Cancel Checking**으로 오래 걸리는 단계를 중단한 뒤 입력을
   고쳐 계속 검사할 수 있다. **LoL: Stop Proof Session**은 서버를 끝내고
   세션의 메모리를 반환한다.

세션을 시작하면 커서 이동과 저장 전 수정 사항을 자동으로 반영한다. 명령
뒤의 공백에서는 앞 명령까지의 상태를 보여 준다. 전술을 바꾸면 처음
고친 위치 앞의 보관된 상태로 되돌아가 커서까지 다시 실행한다. 이력이
만료됐으면 더 앞의 상태나 파일 처음부터 진행한다. 뒤로 가기는 실행
커서만 옮기므로 문서에 `Undo.`가 추가되지 않는다.

창 한 개에서 증명 세션 하나를 쓴다. 두 번째 파일에서 명령을 실행하면
세션이 그 파일로 바뀐다. 가져오는 모듈의 수정 사항을 쓰려면 그 모듈을
저장한다. 검사 중인 버퍼를 닫으면 세션이 끝난다. 서버가 뜨지 않으면
**Output → LoL Server**에서 메시지를 보고 실행 파일 경로와 인자,
`lol/hol`이 있는 프로젝트 루트를 확인한다.
