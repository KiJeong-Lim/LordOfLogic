# Modules, checked objects and Rocq export

**English** · [한국어](modules.ko.md)

This walkthrough uses one small module in three ways. You can import its
function, send someone its checked object, or check its proof in Rocq.
Run the shell commands from the directory containing `lol.cabal`.

## Write and check a module

Run `mkdir -p Workshop` and save this as `Workshop/Double.lol`.

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

The run prints four lines.

```text
nat -> nat
S (S (S (S O)))
The theorem was accepted.
(* No assumptions. *)
```

`Check` prints the type of `twice`. `Compute` prints four applications of
successor `S` to zero `O`. Both sides of the theorem compute to this value, so
`reflexivity.` closes its goal. The third line is the success message from
`Qed.` after the proof term has passed the kernel. `Print Assumptions` lists
the axioms the theorem depends on. Here the list is empty.

## Use the function from another module

Save this as `Workshop/Use.lol` and run `"$LOL" Workshop/Use.lol`. It prints
`S (S O)`.

```lol
Import Workshop.Double.
Import lol.theories.Nat.

Compute twice (S O).
```

`Workshop.Double` resolves to `Workshop/Double.lol` under the project root.
The first import brings `twice` into scope. To use `S` and `O` in this file,
import their defining module directly. A module's own declarations and public
notations are available to its importers. `Local Notation` and
`Local Tactic Notation` stay in the module that declares them. If two direct
imports introduce the same short constant name, use its qualified name.
Set implicit argument positions with `Arguments` in the defining module.
See [language and notation](language.md) for a two-file notation example.

## Read the statements or the proof terms

```bash
mkdir -p build
"$LOL" --statements Workshop/Double.lol
"$LOL" --explicit Workshop/Double.lol > build/DoubleExplicit.lol
"$LOL" build/DoubleExplicit.lol
```

`--statements` prints theorem signatures for inspection. `--explicit` also
prints their proof terms. Look for `@eq_refl` in the explicit version of
`twice_two`. Checking `DoubleExplicit.lol` from the same root succeeds silently.

## Send a checked object

```bash
mkdir -p build/objects
"$LOL" --emit-object=build/objects/Double.lolo Workshop/Double.lol
"$LOL" --check-only build/objects/Double.lolo
```

Send the whole `build/objects` directory, including its hidden `.lolo/`
subdirectory. `Double.lolo` refers to its dependencies by digest in that
subdirectory. The recipient runs `--check-only` on the copied main object from
a project root containing this release's `lol/hol`. The kernel rechecks the
object and its dependencies without the original `Workshop/*.lol` sources.
On success, the report starts with `Checked object Workshop.Double.` and lists
the declarations, each theorem’s transitive `Assumptions:` and the axioms in
the checked modules. Add `--no-axioms` to require that every checked module
declares no axioms, including axioms unused by a theorem.

## Export to Rocq

`"$LOL" --rocq Workshop/Double.lol` prints the main module as Rocq source.
For a module with imports, write the whole source tree and compile its files
in dependency order. These commands use Rocq 9.2.0.

```bash
"$LOL" --rocq-dir=build/rocq Workshop/Double.lol
rocq compile -noinit -Q build/rocq '' build/rocq/lol/theories/Logic.v
rocq compile -noinit -Q build/rocq '' build/rocq/lol/theories/Nat.v
rocq compile -noinit -Q build/rocq '' build/rocq/Workshop/Double.v
```

The empty argument to `-Q` maps `build/rocq` to the root of the logical module
tree. A generated import of `lol.theories.Nat` then resolves to the compiled
file under `build/rocq/lol/theories/`.

[Repository reference](reference.md)

## Checked imports

On POSIX a previously admitted source module can reuse its elaborated
declarations from a private cache under `$XDG_CACHE_HOME/lord-of-logic/imports`
(default `~/.cache/lord-of-logic/imports`). The loader verifies the source and
Hol inputs, resolves its dependencies, and runs the kernel over the cached
declarations. An unusable entry falls back to the source loader. Set
`LOL_IMPORT_CACHE=off` for a source-only run, or `LOL_IMPORT_CACHE_TRACE=1` to
show successful hits on standard error. Compiled Hol programs use their own
`LOL_HOL_CACHE` setting.
