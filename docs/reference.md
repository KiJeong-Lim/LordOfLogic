# Lord of Logic repository reference

[V1 language additions and the proof editor](v1.md)

Lord of Logic (LoL) checks definitions and proofs written in `.lol` files.
Use batch mode to check a whole file, the terminal to try one proof step at a
time, or the editor server to drive a proof from an application.

| I want to… | Start here |
| --- | --- |
| Open a proof, inspect its goal, undo a tactic and try another | [Terminal proof walkthrough](proofs.md) |
| Define a datatype, write a recursive function or declare notation | [Language and notation](language.md) |
| Import a module, inspect a proof term, share a checked object or export to Rocq | [Modules and artifacts](modules.md) |
| Implement **Next**, **Show goal** and **Undo** in an editor | [Editor protocol and runnable client](editor.md) |
| Find the kernel, tactic implementations or standard library | [Repository map](#repository-map) |

## Build and check a file

Run these commands from the checkout root, where `lol.cabal` and `lol/hol/`
are visible. The program looks up its kernel and module tree relative to the
working directory. The Linux build uses GHC, Cabal and a C11 compiler.

```bash
cabal build exe:lol
LOL=$(cabal list-bin exe:lol)
"$LOL" example/Basics.lol
```

```text
Nat -> Nat -> Nat
Succ (Succ (Succ (Succ Zero)))
The theorem was accepted.
(* No assumptions. *)
```

The first two lines come from `Check` and `Compute`. `Qed.` prints the third
line when the kernel accepts the finished proof. `Print Assumptions` prints the
axioms the named theorem relies on. Try [Axioms.lol](../example/Axioms.lol)
to see the difference between a theorem that uses an axiom and one that has
no assumptions.

Keep using `"$LOL"` in the same shell or substitute `cabal run -v0 lol --`
in the commands below.

## Terminal quick reference

```bash
"$LOL" --interactive example/Universes.lol
```

The file opens before its first command. Type the following lines at `LoL>`.
The first `:next` checks `Prop`, the second checks `Set`, and each prints
`Type@{1}`. `:run` executes the remaining commands.

```text
:next
:next
:run
:quit
```

| Input | What it does |
| --- | --- |
| `:next` | Read one complete command at the file cursor. At the end, the current state stays in place. |
| `:run` | Read to the end of the file or stop at the first failure. |
| `Show.` | Display the hypotheses and current goal of an open proof. |
| `Show Universes.` | Display the proof's universe variables and constraints. |
| `Undo.` | Restore the state before the last command that changed it. A query such as `Show.` adds no undo step. |
| `:discard` | Drop the unread source from the in-memory document. The current proof state is preserved. You can now type a replacement tactic. |
| `Qed.` / `Abort.` | Check and register a completed theorem, or abandon the open theorem. |
| `:save PATH` | Write the current document, including any unread source, to `PATH`. Use a fresh name to keep the original. |
| `:quit` | Close the session. Save first if you want to keep your edits. |

**To try `Undo.`**, start `"$LOL" --interactive` with no file and enter these
lines individually. After the first `exact p.` the terminal reports
`No goals remain.`. `Undo.` reopens goal `P` with hypothesis `p : P`.
`Show.` lets you inspect it before you finish the proof.

```text
Theorem keep : forall P : Prop, P -> P.
Proof.
intros P p.
exact p.
Undo.
Show.
exact p.
Qed.
:quit
```

Colon commands take a line of their own. Source commands such as `Undo.`
and `exact p.` end with a period. If you type a source command while a file
still has pending commands, the terminal reports `[P-PendingSource]`. Use
`:next` to execute the saved continuation, or `:discard` to start writing a
different one. Once the tail is gone, reapply an undone tactic by typing it.
The [proof walkthrough](proofs.md) shows the goals and the exact sequence for
branching midway through a file.

## Executable and file formats

| Invocation | Use it for |
| --- | --- |
| `lol FILE.lol` | Check the file and print query results as they are reached. On failure, read the location and diagnostic and check the exit status. |
| `lol --interactive [FILE.lol]` | Create an empty document or open a file for stepping. |
| `lol --server` | Exchange protocol version 2 JSON messages over standard input and output. |
| `lol --statements FILE.lol` | Read checked declarations with theorem signatures. |
| `lol --explicit FILE.lol` | Inspect checked declarations with explicit arguments and proof terms. |
| `lol --emit-object=FILE.lolo FILE.lol` | Write an object and its dependency objects. |
| `lol --check-only [--no-axioms] FILE.lolo` | Recheck the object closure, list declarations and transitive theorem assumptions, and optionally reject any declared axiom. |
| `lol --rocq FILE.lol` | Write the main module's Rocq source to standard output. |
| `lol --rocq-dir=DIR FILE.lol` | Write the main module and its imports as a Rocq source tree. |
| `lol --help` | Print the installed executable's usage. |

To put a budget on an engine run, use `--work-limit=N` for work units,
`--timeout-ms=N` for milliseconds, `--memory-mib=N` for engine memory or
`--host-allocation-mib=N` for host allocation during the run. A file can
start many engine runs. Use a shell timeout if you also need a deadline for
the entire process. The [module walkthrough](modules.md) builds, transfers
and rechecks an object, then compiles its exported source with Rocq.

## Find a runnable example

Every link in the table opens a complete input file. To run one, pass its
path to `"$LOL"`, or insert `--interactive` to step through it.

| Task | Example | What to inspect |
| --- | --- | --- |
| Prove an equality by induction | [Basics.lol](../example/Basics.lol) | Compare the term proof with the tactic proof of addition by zero. |
| Replace an expression using an equality | [Equality.lol](../example/Equality.lol) | `rewrite <- e in pb.` rewrites a hypothesis using the equality backwards. |
| Work on several goals | [Tacticals.lol](../example/Tacticals.lol) | Follow a split with bullets, or apply the same tactic to all resulting goals. |
| Use arithmetic and lists from the library | [Library.lol](../example/Library.lol) | Import the modules, enable numerals, then compute a length and reverse a list. |
| Define a family indexed by length | [Vectors.lol](../example/Vectors.lol) | Read the `return` clause of a dependent `match`. |
| Use projections or universe levels | [Records.lol](../example/Records.lol), [Universes.lol](../example/Universes.lol) | Inspect `p.(first)`, record η, and universe instances. |
| Add a tactic written in Hol | [UserTactics.lol](../example/UserTactics.lol), [UserTactics.hol](../example/UserTactics.hol) | Load the file, invoke a named tactic and solve the goal it leaves. |
| Follow a larger development | [Sorting.lol](../example/Sorting.lol), [STLC.lol](../example/STLC.lol) | Use established library proofs about sorting or simply typed terms. |

## Read a diagnostic

```bash
"$LOL" example/rejected/Proof.lol
```

This file checks its first theorem and exits with status 1 at the failing
`reflexivity.` in the second. The location identifies the failed tactic and the
message includes `[P-StepFailed]`. Open the file with `--interactive` and type
`:run` to inspect the goal at the failure. Use `:discard` before typing a
replacement or `Abort.`. A failed tactic typed in an empty session can be
replaced immediately at the same goal.

The [rejected examples](../example/rejected) also illustrate kernel diagnostics.
`[I-Pos]` identifies an occurrence that violates strict positivity, and
`[F-Guard]` a recursive call that fails the guard condition. Compare the
offending constructor or recursive argument with the accepted definitions in
the [language walkthrough](language.md).

## Repository map

| Path | Where to look |
| --- | --- |
| [example/](../example), [lol/theories/](../lol/theories) | Runnable examples and importable standard-library sources. For example, `Import lol.theories.Nat.` reads `lol/theories/Nat.lol`. |
| [lol/hol/kernel.hol](../lol/hol/kernel.hol) | The typing, conversion and reduction rules used to check completed terms. |
| [lol/hol/elab.hol](../lol/hol/elab.hol), [lol/hol/proof.hol](../lol/hol/proof.hol), [lol/hol/tactics.hol](../lol/hol/tactics.hol) | Elaboration of surface terms, proof goals and the tactics that propose proof terms. |
| [src/LoL/Main.hs](../src/LoL/Main.hs), [src/LoL/Front/](../src/LoL/Front) | Command-line options and the reader for declarations, terms and notation. |
| [src/LoL/Module.hs](../src/LoL/Module.hs), [src/LoL/Object.hs](../src/LoL/Object.hs), [src/LoL/Export/Rocq.hs](../src/LoL/Export/Rocq.hs) | Import resolution, checked objects and Rocq output. |
| [src/LoL/Proof/](../src/LoL/Proof) | Proof documents, undo history, terminal commands and the editor protocol. |
| [src/LoL/Hol/](../src/LoL/Hol), [src/LoL/Oracle.hs](../src/LoL/Oracle.hs), [src/LoL/Oracle/](../src/LoL/Oracle) | The host's interface to the kernel and its strict positivity and guardedness checks. |
| [src/Hol/BETA/](../src/Hol/BETA), [src/Hol/V1/](../src/Hol/V1), [src/Hol/V2/](../src/Hol/V2), [src/X/](../src/X) | Hol's front end, bytecode compiler and runtime, embedding interface, and native executor and bindings. |
| [lol.cabal](../lol.cabal) | Build target, dependencies, and the files shipped with the source distribution. |

The Hol program cache is under `$XDG_CACHE_HOME/lol/hol-v2` (by default
`~/.cache/lol/hol-v2`). Set `LOL_HOL_CACHE=off` for a run that should bypass it.

## Checked imports

On POSIX a previously admitted source module can reuse its elaborated
declarations from a private cache under `$XDG_CACHE_HOME/lord-of-logic/imports`
(default `~/.cache/lord-of-logic/imports`). The loader verifies the source and
Hol inputs, resolves its dependencies, and runs the kernel over the cached
declarations. An unusable entry falls back to the source loader. Set
`LOL_IMPORT_CACHE=off` for a source-only run, or `LOL_IMPORT_CACHE_TRACE=1` to
show successful hits on standard error. Compiled Hol programs use their own
`LOL_HOL_CACHE` setting.
