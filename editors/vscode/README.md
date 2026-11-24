# Lord of Logic for Visual Studio Code

[한국어](README.ko.md)

Check a command by placing the cursor in it and running **LoL: Check to Cursor**.
The **LoL Proof** view in the Explorer shows the local hypotheses and the goal
reported by the LoL server. All proof checking runs in the workspace, including
when the editor connects to a WSL or SSH workspace.

## Install from source

First build the proof checker. In the directory containing `lol.cabal`, run:

```sh
cabal build exe:lol
cabal list-bin exe:lol
```

Package the extension from its own directory with Node.js 22 or later:

```sh
cd editors/vscode
npx --yes --package @vscode/vsce@3.7.1 vsce package --no-dependencies --out lord-of-logic.vsix
```

Use **Extensions: Install from VSIX…** to select `lord-of-logic.vsix` in the
VS Code window where you will edit proofs. For a remote workspace, install in
that workspace's extension host. Open the trusted project folder containing
`lol/hol`. In **Settings**, set `lordOfLogic.executable` to the absolute path
printed by Cabal, or put `lol` on PATH. The server arguments default to
`["--server"]`. A launcher that accepts a subcommand can use
`lordOfLogic.arguments` to supply the subcommand followed by `--server`.

## Try a proof

Save the following as `Demo.lol` in your project.

```text
Theorem demo : forall P Q : Prop, (P -> Q) -> P -> Q.
Proof.
    intros P Q f p.
    apply f.
    exact p.
Qed.
```

1. Put the cursor on `apply f.` and choose **LoL: Check to Cursor** from the
   Command Palette (or the play button on the editor title bar). The goal is
   `P`. Opening the file alone starts no proof server.
2. Choose **LoL: Previous Command**. The goal becomes `Q` and the cursor
   moves to the end of `intros P Q f p.`. **LoL: Next Command** executes
   `apply f.` again and brings back `P`.
3. In that same buffer, replace `apply f.` with `exact p.` and put the cursor
   on it. The goal is `Q` at this step, so `p : P` has the wrong type. The
   failing tactic is underlined and its diagnostic appears in **Problems**.
   Restore `apply f.` to continue. After `Qed.` the server reports `The theorem was accepted.`
4. Use **LoL: Cancel Checking** to interrupt a long proof step. Edit the
   failed or cancelled step and check again. **LoL: Stop Proof Session**
   closes the server and releases the session's memory.

Once started, the session follows cursor movements and unsaved edits in its
file. Whitespace after a command shows the state at the preceding command.
The editor rewinds to a retained checkpoint before the first change and
rechecks to the cursor. If that part of the history has expired, it replays
from an earlier checkpoint or reopens the buffer. Moving backwards controls
the execution cursor without adding a source-level `Undo.` to the proof.

A window runs one proof session at a time. Start a command in a second file
to switch. Save imported modules before using their new declarations.
Closing the checked buffer ends the session. For launch errors, inspect
**Output → LoL Server** and check the executable, arguments and project root.
