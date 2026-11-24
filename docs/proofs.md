# Proving a theorem in the terminal

**English** · [한국어](proofs.ko.md)

## Read a goal, try a tactic, and undo it

From the repository root, start an empty session.

```sh
cabal run -v0 lol -- --interactive
```

At the `LoL>` prompt, enter these commands. The theorem says that given a function from `P` to `Q` and a proof of `P`, you can prove `Q`.

```text
Theorem compose : forall P Q : Prop, (P -> Q) -> P -> Q.
Proof.
intros P Q f p.
Show.
```

`intros` brings the propositions and assumptions into the local context. `Show.` displays the current state again.

```text
Proof compose - Step 1

P : Prop
Q : Prop
f : P -> Q
p : P
--------------------
Q
```

Above the line are the names you can use. Below it is the goal. Enter the next commands **one line at a time** so you can see how each one affects that goal.

```text
exact p.
apply f.
Undo.
Show.
exact (f p).
Qed.
Print Assumptions compose.
```

| Command | What you should see |
| --- | --- |
| `exact p.` | `[P-StepFailed]`. The term `p` has type `P`, so the goal `Q` stays open. You can try another tactic immediately. |
| `apply f.` | The new goal is `P`, the input that `f` needs to produce a `Q`. |
| `Undo.` | `The previous document state was restored.` The goal is `Q` again. |
| `Show.` | The local context and the restored goal `Q`. The proof state number in the prompt has advanced even though you went back. |
| `exact (f p).` | `No goals remain.` The term `f p` has type `Q`. |
| `Qed.` | The kernel checks the completed proof, registers `compose`, and returns to `LoL>`. |
| `Print Assumptions compose.` | `(* No assumptions. *)` |

At this point, save the transcript under a fresh filename and quit.

```text
:save Compose.lol
:quit
```

`Compose.lol` includes successful source commands, including `apply f.` and `Undo.`. The failed attempt you typed is left out. To replay the transcript in batch mode, run the following at the shell.

```sh
cabal run -v0 lol -- Compose.lol
```

## Step through a file and change the proof

Reopen the transcript from the first exercise.

```sh
cabal run -v0 lol -- --interactive Compose.lol
```

The file opens **before its first command**. Type `:next` to execute one source command, or `:run` to execute the remaining commands up to the first error or the end of the file. Enter terminal controls on their own line without a period. Source commands such as `Show.` and `Undo.` end with a period. If you see `...>`, finish the source command you started.

| What to type | What happens |
| --- | --- |
| `:next` | Reads the theorem header. The prompt changes to `compose[0]>`. |
| `:next` | Reads `Proof.`. The goal stays the same. |
| `:next` | Runs `intros P Q f p.`. The goal becomes `Q`. |
| `:next` | Reads the saved `Show.` and displays the same goal and assumptions. |
| `:next` | Runs `apply f.`. The goal becomes `P`. |
| `Undo.` | Reports `[P-PendingSource]` because more source commands are waiting in the file. The goal is still `P`. |
| `:discard` | Drops the unread part of the file from this session. The goal is still `P`. |
| `Undo.` | Restores the state just before `apply f.`. The goal is `Q`. |
| `:next` | The unread portion is empty, so the goal stays `Q`. To try `apply f.` again you would type it yourself. |
| `exact (f p).` | Solves the goal using the new command you supplied. |
| `Qed.` | Registers the theorem. Enter `:save Edited.lol` and then `:quit` to keep this version. |

`:save PATH` writes the **entire current document**, including any unread commands. To keep a copy of those commands, save under a separate name **before** `:discard`. Saving to an existing name replaces its contents. Until you save to the original filename, stepping and discarding affect only the open session.

### How far can I undo?

`Undo.` takes one step back through **changes to the document**. Reading the goal with `Show.` adds no change to undo. Undoing `Qed.` reopens the completed proof; undoing `Abort.` reopens the proof you abandoned. A fresh session reports `[P-NoHistory]` on its first `Undo.`.

History is bounded. The terminal keeps up to 15 previous document states and gives priority to the last seven undo targets. An older state can expire (`[P-ExpiredState]`), and a proof also needs its saved worker state to be restorable. Save your source if you may want to revisit an early step. You can reopen that file with `--interactive` and use `:next` to reach the step again.

### Recover from a failing file

Open the [example with a false equality](../example/rejected/Proof.lol).

```sh
cabal run -v0 lol -- --interactive example/rejected/Proof.lol
```

1. Enter `:run`. The first theorem, `right`, succeeds. In the second theorem, `wrong`, the tactic `reflexivity.` fails on `1 + 1 = 3`.
2. Enter `:discard`. The unread text includes the failed `reflexivity.` and the `Qed.` after it. You can now type a replacement tactic at the current goal.
3. For this false equality, enter `Abort.` to abandon `wrong`. The earlier theorem `right` remains available. Enter `:quit` to leave the example as you found it.

## Work on more than one goal

Save the following as `Branches.lol` and run `cabal run -v0 lol -- Branches.lol`. The import makes the conjunction `and` available.

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

In the first proof, `split.` opens two goals, `Q` and then `P`. Each bullet (`-`) starts the proof of one branch. In the second proof, both goals have type `P`. The semicolon applies `exact p` to **each** goal produced by `split`.

## Inspect the universes of an open proof

Enter the following in an empty interactive session.

```text
Polymorphic Theorem poly@{u} : forall A : Type@{u}, A -> A.
Proof.
intros A x.
Show Universes.
exact x.
Qed.
```

In this example `Show Universes.` prints `Universes of the proof: @{u}` and leaves the goal unchanged. In general it shows the current universe names, including levels still open, and the declared and recorded constraints. In the earlier proof of `compose` it prints `This proof has no universe.`. Enter it during a proof; at `LoL>` it reports `[P-NoProof]`.

## Rewrite an equality or load a tactic

- **Rewrite a hypothesis.** In `transport`, the assumptions include `e : a = b` and `pb : P b`. The command `rewrite <- e in pb.` changes the type of `pb` to `P a`, and `exact pb.` closes the goal. To rewrite in the goal from left to right, use `rewrite e.`. [Equality.lol](../example/Equality.lol)
- **Use an induction hypothesis.** In `plus_zero_tactics`, `induction n.` produces a base case and a successor case. The successor case uses `simpl.` to unfold addition, then `rewrite IHn.` to apply the induction hypothesis. [Basics.lol](../example/Basics.lol)
- **Use a tactic written in Hol.** From the repository root, load `Load Tactics "example/UserTactics.hol".` before starting the theorem. The tactic `give` takes a candidate proof term. In the example, `tactic give (conj P Q p _).` leaves the missing second component as a goal. Then `tactic hypothesis.` finds the assumption that fills it, and `Qed.` checks the completed proof. [Proof script](../example/UserTactics.lol) · [Tactic definitions](../example/UserTactics.hol)

```sh
cabal run -v0 lol -- example/Equality.lol
cabal run -v0 lol -- example/UserTactics.lol
```

[Repository reference](reference.md)
