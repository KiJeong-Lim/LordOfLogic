# LoL

[V1 scopes, custom notation, Search, sections and the VS Code proof editor](docs/v1.md)

**English** · [한국어](README.ko.md)

LoL is a proof assistant for a calculus of inductive constructions. Its kernel
is a λProlog program, [`lol/hol/kernel.hol`](lol/hol/kernel.hol), and Hol runs
it. Hol is the λProlog engine in this repository. The Haskell host reads
commands, keeps modules and objects, and drives the engine. It implements no
rule of reduction, conversion or typing.

The kernel runs on the Hol compiler and C virtual machine. Their unifier, garbage
collector and FFI, the positivity and guardedness oracles, the universe solver
and the translations of terms and environments all contribute to the trust base.
The local release checks compile the exported library and examples with Rocq
9.2.0 and run the native examples under ASan and UBSan.
[Reproduce the release checks](docs/verification.md)

The surface language follows Rocq: `Inductive`, `Record`, `Fixpoint`,
`match`, `Theorem … Proof. … Qed.`, notations and tactics. A checked module
can be exported as Rocq source.

Start with the **[repository reference](docs/reference.md)**. Use the
[terminal walkthrough](docs/proofs.md) to learn `:next` and `Undo.`, or
go directly to [the language](docs/language.md), [modules and Rocq
export](docs/modules.md), or [editor integration](docs/editor.md).

## Building

The package accepts `filepath >= 1.4`. The local sanitizer build tests the
1.4 lower bound. V1 supports sections and contexts. Its sorts are
`Prop`, `Set` and `Type`. Coinduction, cofixpoints and `SProp` typing
are outside this release. The language has no `Admitted` command and no
option to disable universe checking.

The repository was tested on Linux with GHC 9.6.7 and cabal-install 3.14.2.
The C part of the engine needs a C11 compiler.

```bash
cabal build lol
```

`stack.yaml` pins the Stackage snapshot `lts-24.41`, but only the Cabal build
was tested.

## Running a file

Run LoL from the root of the repository. The kernel, the elaborator and the
tactics are read from `lol/hol` under the current directory, and
`Import a.b.C.` reads `a/b/C.lol` under it.

```bash
cabal run -v0 lol -- example/Basics.lol
```

The run prints the result of each command as it is checked:

```text
Nat -> Nat -> Nat
Succ (Succ (Succ (Succ Zero)))
The theorem was accepted.
(* No assumptions. *)
```

When a command fails, LoL prints the output of the commands before it, then
the diagnostic, and exits with status 1.

```text
example/rejected/Positivity.lol:10:1-10:55: error: [LoL-KernelError]
    |
 10 | Inductive Bad : Type := | wrap : (Bad -> Empty) -> Bad.
    | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
[I-Pos] the oracle rejected this command
  the oracle says: a family of the block occurs where it is not strictly positive
```

`cabal list-bin lol` prints the path of the executable, which can also be run
directly.

## Examples

Each example says at its top how to run it. The examples that prove a theorem
end with `Print Assumptions`, which lists the axioms that the theorem depends
on.

| File | What it shows |
|---|---|
| [`Basics.lol`](example/Basics.lol) | an inductive type, a recursive function, `Check` and `Compute`, and one theorem proved by a term and by tactics |
| [`Logic.lol`](example/Logic.lol) | conjunction, disjunction, negation, `iff` and existentials in proof mode |
| [`Arithmetic.lol`](example/Arithmetic.lol) | induction: commutativity and associativity of addition and distributivity of multiplication, for the numbers of `Basics.lol` imported as a module |
| [`Equality.lol`](example/Equality.lol) | `injection`, `discriminate`, `symmetry`, `transitivity`, `rewrite <- e in h` and `f_equal` |
| [`Tacticals.lol`](example/Tacticals.lol) | `;`, `repeat`, `all:`, `first`, `try`, `constructor 2`, `assert`, `specialize`, `unfold`, `change` and `simpl in` |
| [`Library.lol`](example/Library.lol) | the standard library, numerals and rewriting with library lemmas |
| [`Lists.lol`](example/Lists.lol) | list functions, and `rev (rev l) = l` from two lemmas |
| [`Vectors.lol`](example/Vectors.lol) | vectors indexed by their length, `match` with a return clause and induction on an indexed family |
| [`Mutual.lol`](example/Mutual.lol) | mutual inductive predicates and types, mutual recursion, and one induction for two statements |
| [`Decisions.lol`](example/Decisions.lol) | decisions that carry proofs, and the excluded middle for a decidable proposition |
| [`Numbers.lol`](example/Numbers.lol) | division, greatest common divisors and primes from the standard library |
| [`Sorting.lol`](example/Sorting.lol) | verified insertion sort and merge sort |
| [`STLC.lol`](example/STLC.lol) | a typing derivation, a reduction step and preservation for the simply typed lambda calculus |
| [`Records.lol`](example/Records.lol) | a template record with primitive projections and definitional eta |
| [`Universes.lol`](example/Universes.lol) | `Prop`, `Set` and `Type@{i}`, cumulativity and a universe-polymorphic definition |
| [`V1Scopes.lol`](example/V1Scopes.lol), [`V1.lol`](example/V1.lol) | two meanings of one symbol, a custom grammar, section parameters and Search |
| [`Notations.lol`](example/Notations.lol), [`Syntax.lol`](example/Syntax.lol) | a module that exports a notation and a tactic notation, and a module that uses them |
| [`UserTactics.lol`](example/UserTactics.lol), [`UserTactics.hol`](example/UserTactics.hol) | two tactics written in Hol and loaded with `Load Tactics` |
| [`Axioms.lol`](example/Axioms.lol) | an axiom, and `Print Assumptions` for a theorem that uses it and one that does not |

The files in [`example/rejected`](example/rejected) are rejected on purpose.

| File | Diagnostic |
|---|---|
| [`Positivity.lol`](example/rejected/Positivity.lol) | `[I-Pos]`: a type occurs to the left of an arrow in its own constructor |
| [`Guard.lol`](example/rejected/Guard.lol) | `[F-Guard]`: a recursive call on a larger argument |
| [`Universe.lol`](example/rejected/Universe.lol) | `[T-Conv]`: `Type@{0}` as a member of itself |
| [`Elimination.lol`](example/rejected/Elimination.lol) | `[I-Elim-Prop]`: a proof of a disjunction decides a `bool` |
| [`Proof.lol`](example/rejected/Proof.lol) | `[P-StepFailed]`: `reflexivity` on `1 + 1 = 3` |

## Options

```text
lol [OPTIONS] FILE.lol
lol --check-only [--no-axioms] FILE.lolo
lol --interactive [FILE.lol]
lol --server
```

| Option | Effect |
|---|---|
| `--explicit` | print every checked declaration with all its arguments, theorems with their proofs |
| `--statements` | as `--explicit`, but print theorems without their proofs |
| `--rocq` | print the main module as Rocq source |
| `--rocq-dir=DIR` | write the Rocq source of the main module and its imports under `DIR` |
| `--emit-object=FILE.lolo` | write a checked object of the module; its imports go to `.lolo/` beside it |
| `--check-only` | recheck an object and its dependencies and report declarations and theorem assumptions |
| `--no-axioms` | with `--check-only`, fail if any checked module declares an axiom |
| `--work-limit=N` | bound the work of each run of the engine |
| `--timeout-ms=N` | bound the time of each run of the engine, in milliseconds |
| `--memory-mib=N` | bound the memory of the engine, in MiB |
| `--host-allocation-mib=N` | bound the allocation of the host during a run, in MiB |
| `--help` | print the usage |

For example, `cabal run -v0 lol -- --rocq example/Arithmetic.lol` prints
`Arithmetic.lol` as a Rocq module that requires `example.Basics`.

## Interactive mode

```bash
cabal run -v0 lol -- --interactive example/Universes.lol
```

At the `LoL>` prompt, enter these lines one at a time.

```text
:next
:next
:run
:quit
```

The two `:next` commands execute `Check Prop.` and `Check Set.`. Each prints
`Type@{1}`. `:run` reads the rest of the file up to the first error or the end.

To write a proof by hand, start with an empty document.

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

The first `exact p.` closes the goal. `Undo.` brings back the goal `P` with
hypothesis `p : P`. `Show.` displays it, and entering `exact p.` again solves it.
`Qed.` checks the finished proof. `:save Keep.lol` writes the session to disk.
Inside an open proof, use `Show Universes.` to inspect universe constraints or
`Abort.` to abandon that theorem.

When working from a file, use `:discard` to drop its unread tail before typing a
different proof command. This keeps the current goal. If you want a copy of the
unread commands, use `:save PATH` first. After `:discard`, `:next` has no source
left to execute. To reapply a tactic you undid, type the tactic again.

## Editor server

`--server` reads requests and writes replies as JSON lines on standard input
and output, with protocol version 2. The methods are `open`, `append`,
`replace`, `next`, `show`, `undo`, `cancel`, `close` and `shutdown`. A
document reference carries the `incarnation` that its `open` returned, so a
closed and reopened document cannot revive an old reference.

```json
{"protocol":2,"id":1,"method":"open","document":"demo","revision":1,"path":"example/Demo.lol","source":"Theorem id : forall P : Prop, P -> P.\nProof.\nintros P h.\nexact h.\nQed.\n"}
{"protocol":2,"id":2,"method":"shutdown"}
```

[`src/LoL/Proof/Protocol.hs`](src/LoL/Proof/Protocol.hs) defines the
requests and replies. The [editor guide](docs/editor.md) includes a working
Python client that steps through a proof, reads the goal and rewinds the cursor.

## The language

**Commands.**

- Declarations: `Inductive` (mutual blocks with `with`), `Record`,
  `Definition`, `Fixpoint`, `Theorem`, `Lemma`, `Axiom`, `Polymorphic`.
- Queries: `Check`, `Compute`, `Print Assumptions`, `Search`.
- Modules and sections: `Import`, `Section`, `Context`, `End`.
- Syntax: `Infix`, `Notation`, `Reserved Notation`, `Declare Scope`, `Open Scope`,
  `Declare Custom Entry`, `Tactic Notation`, `Arguments`, `Numerals`.
- Proofs: `Proof`, `Qed`, `Show`, `Show Universes`, `Undo`, `Abort`,
  `Load Tactics`.

**Tactics.**

- `intro`, `intros`, `exact`, `apply`, `refine`, `assumption`.
- `reflexivity`, `symmetry`, `transitivity`, `rewrite`.
- `simpl`, `unfold`, `change`.
- `destruct`, `induction`, `injection`, `discriminate`.
- `constructor`, `split`, `left`, `right`, `exists`, `exfalso`.
- `assert`, `specialize`.
- `first`, `try`, `repeat`, `all:`, `;` and bullets.

`destruct h as a b` and `induction n as p IHp` name the new hypotheses in the
order of the cases: for `or A B`, `a` in the first case and `b` in the second.

A Hol program loaded with `Load Tactics "file.hol".` can add tactics, called
as `tactic name (argument).` A tactic only proposes a term; the kernel checks
the proof at `Qed` as usual. [`example/UserTactics.hol`](example/UserTactics.hol)
defines two.

**Attributes.** `#[universes(template)]` lets an inductive type or a record
take its sort from its arguments. `#[projections(primitive)]` gives a record
primitive projections, written `r.(field)`.

**Modules.** `Import M.` brings into scope what `M` itself declares, and
passes on nothing that `M` imported. A notation belongs to the module that
declares its constant. An imported module must resolve inside the project
root.

## Standard library

[`lol/theories`](lol/theories) holds 29 modules with no axioms. Import them as
`lol.theories.Name`.

| Modules | Contents |
|---|---|
| `Logic`, `LogicProperties` | connectives, quantifiers, equality, `prod`, `sum`, `option` |
| `Bool`, `BoolOrder`, `Decidable` | booleans, comparisons and decisions that carry proofs |
| `Nat`, `NatProperties`, `NatSearch`, `Order`, `OrderLattice` | unary naturals, arithmetic, finite search, order |
| `Division`, `Divisibility`, `Gcd`, `Primes` | division by well-founded recursion, Euclid's algorithm, unbounded primes |
| `List`, `ListProperties`, `ListAlgorithms`, `ListDecidable`, `ListRelations`, `Sorting` | lists, permutations, verified insertion and merge sorts |
| `Vec`, `Sigma`, `ProductProperties`, `SumProperties`, `OptionProperties`, `RelationProperties` | indexed vectors, dependent pairs, data and relation laws |
| `Wf`, `WfNat` | accessibility and well-founded recursion |
| `STLC` | progress and preservation for a simply typed lambda calculus |

## How a declaration is checked

1. The host parses the command with the notations in scope and translates it to
   a raw term.
2. The elaborator, [`lol/hol/elab.hol`](lol/hol/elab.hol), fills implicit
   arguments and holes. In a proof, the tactics in
   [`lol/hol/proof.hol`](lol/hol/proof.hol) and `lol/hol/tactics*.hol` build
   the proof term. Unsolved holes stop the engine in its debugger, and each
   debugger state is a proof state.
3. A ground run of the kernel checks the completed term. At `Qed`, a fresh
   kernel checks the whole proof again.
4. The kernel leaves two judgments to an oracle in the host: strict positivity
   and the guard condition of `fix`. The oracle follows the algorithms of
   Rocq's `kernel/indtypes.ml` and `kernel/inductive.ml`, with soundness
   repairs. It reduces nothing itself; it asks the kernel for every weak head
   normal form.

## Layout

| Path | Contents |
|---|---|
| `src/Main.hs` | the executable |
| `src/LoL/` | the host: syntax and notation (`Front/`), commands, modules and objects, the oracle (`Oracle/`), proof documents, terminal and server (`Proof/`), Rocq export (`Export/`) |
| `src/Hol/BETA/` | the λProlog front end of Hol: lexer, parser, type checker, module loader, debugger |
| `src/Hol/V1/` | the compiler of Hol to bytecode and its runtime services |
| `src/Hol/V2/` | the embedding API that LoL uses: prepared programs, their cache and wire format |
| `src/X/` | the C executor of the bytecode and its Haskell bindings |
| `src/Json/` | JSON for the server protocol |
| `src/Calc/`, `src/Y/`, `src/Z/` | Presburger arithmetic for Hol, and utilities |
| `lol/hol/` | the kernel, the elaborator and the tactics, in Hol |
| `lol/theories/` | the standard library |
| `example/` | the examples above |

The lexers and parsers `src/Hol/BETA/PlanHol{Lexer,Parser}.hs` and
`src/Json/Json{Lexer,Parser}.hs` are generated files and are not edited by
hand.

## Files outside the repository

LoL keeps the compiled Hol programs under `$XDG_CACHE_HOME/lol/hol-v2` (by
default `~/.cache/lol/hol-v2`). Set `LOL_HOL_CACHE=off` to turn this off.

## License

BSD 3-Clause. See [LICENSE](LICENSE).

## Checked imports

On POSIX a previously admitted source module can reuse its elaborated
declarations from a private cache under `$XDG_CACHE_HOME/lord-of-logic/imports`
(default `~/.cache/lord-of-logic/imports`). The loader verifies the source and
Hol inputs, resolves its dependencies, and runs the kernel over the cached
declarations. An unusable entry falls back to the source loader. Set
`LOL_IMPORT_CACHE=off` for a source-only run, or `LOL_IMPORT_CACHE_TRACE=1` to
show successful hits on standard error. Compiled Hol programs use their own
`LOL_HOL_CACHE` setting.
