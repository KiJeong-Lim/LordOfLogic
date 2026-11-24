# Checking a LoL release

A proof passes through an elaborator and tactics before its completed term reaches
the kernel in a separate Hol session. Acceptance depends on the kernel rules,
the Haskell positivity and guardedness oracles, the Presburger solver, the
translation of terms and environments, and the Hol compiler and executor.
This includes the native C machine, its garbage collector, its unifier and
the FFI bindings. Clause order, cut and unification affect the meaning of the
kernel program. An explicit `Axiom` is an assumption. Inspect the report from
`lol --check-only FILE.lolo` before relying on a received object. To require
that its checked modules declare no axioms, use
`lol --check-only --no-axioms FILE.lolo`.

In the standalone project, `cabal test release-examples` builds the checker
and compares exit status, standard output and standard error with the recorded
version of every example. The test runner uses Linux `/proc` to measure
resident memory of the whole subprocess tree. The positive collection includes complete proofs.
The rejection collection covers type conversion, elimination, positivity,
guardedness and a failed tactic. The kernel checks a closed computation theorem
with ordinary structurally decreasing recursion and a nested positive datatype.

Run the release checks locally from the repository root on Linux.

```sh
python3 ci/lol-release.py proofs
python3 ci/lol-release.py sanitizers
```

The `proofs` command needs GHC, Cabal, Python 3, Node and Rocq 9.2.0. `ROCQ` may
point at the reference executable. The reference opam switch uses
`rocq-core.9.2.0` and `rocq-stdlib.9.1.0`. The command checks the editor protocol and V1 language cases, exports every
positive example and standard-library module into a new temporary directory,
then runs `rocq compile -noinit` on every exported module in dependency order.
This supplies an independent kernel verdict for those declarations. Both
systems can still accept a theorem that depends on a declared axiom. The
comparison covers the tested corpus.

The `sanitizers` command pins `filepath < 1.5` to check the supported 1.4 API, builds
with `-fsanitizers`, checks that the executable loads
ASan and UBSan, and checks all positive example transcripts plus the computation
theorem. It disables the compiled Hol bootstrap cache. Leak detection is
disabled for the GHC runtime. The sanitizers detect memory and undefined
behaviour errors reached by this collection. Both commands cap elapsed time and
sample process-tree resident memory.

The V1 surface includes `Section`, `Context` and `End`. Its sorts are
`Prop`, `Set` and the predicative `Type` hierarchy. Coinductive declarations,
cofixpoints and strict-proposition `SProp` typing have no V1 implementation.
The checker has no `Admitted` command or option to bypass universe checking.

The permanent regression inputs exercise an ordinary nested positive datatype,
recursion on an immediate subtree, conversion of its computed value, structural
mutual recursion, dependent records and an impredicative elimination boundary.
Six closed theorems cover these computations, including a recursive tree size
passed through a global map, transport and congruence along reflexivity, and
mutual recursion with a shared type parameter.
The suite does not map each historical guardedness advisory to its own input.
Its results describe these checked programs. The audit's separate historical
probe results were not reproduced by these release checks.
