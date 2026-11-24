# Defining types and functions in LoL

**English** · [한국어](language.ko.md)

Create `Walkthrough.lol` in the project root. Add the LoL examples below in order, except for the short example marked `ReadPublic.lol`, which goes in a second file. From the project root, run the following command after each step. `Check` prints the type of an expression and `Compute` prints its computed value.

```sh
cabal run -v0 lol -- Walkthrough.lol
```

## An inductive type and a recursive function

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

Each value of `Height` starts at `base` and has some number of `up` constructors around it. With `Numerals base up.`, LoL reads `2` as `up (up base)`. The `Infix` declaration lets you write `2 + 1` for `addHeight 2 1`.

`{struct n}` names the argument that must get smaller at every recursive call. In the `up p` branch, `p` is the immediate subterm of `n`. The two queries print these lines in order.

```text
Height -> Height -> Height
up (up (up base))
```

## Implicit arguments and explicit application

```lol
Definition keep (A : Set) (x y : A) : A := x.
Arguments keep {A} x y.
Check @keep.
Compute keep three 1.
Compute @keep Height three 1.
```

The first argument of `keep` is a type. After `Arguments keep {A} x y.`, LoL infers `A` from the type of `three` in `keep three 1`. Use `@keep` to supply the type yourself. Both calls to `Compute` print `up (up (up base))`.

You can also declare the argument implicit from the start by writing `{A : Set}` in place of `(A : Set)`. To change how an existing constant is called, put the `Arguments` declaration in the module that defines it. The last such declaration in that module determines what its importers see.

## Term and tactic notation

```lol
Local Notation "taller $term" := up (at level 9, right associativity).
Local Tactic Notation "closewith $term" := exact.

Compute taller base.

Theorem retain : forall P : Prop, P -> P.
Proof.
    intros P h.
    closewith h.
Qed.
Print Assumptions retain.
```

In a term, `taller base` computes to `up base`. In a proof, `closewith h.` runs `exact h.`. After `Qed.`, the assumptions report for `retain` reads `(* No assumptions. *)`.

To use the addition operation from a second module, put the next two lines **in a separate file named `ReadPublic.lol`** beside `Walkthrough.lol`. Run `cabal run -v0 lol -- ReadPublic.lol` to see `up (up (up base))`. The `Local` declarations keep `taller` and `closewith` private to `Walkthrough.lol`.

```lol
Import Walkthrough.
Compute 2 + 1.
```

Declare a `Notation` or `Tactic Notation` without `Local` to make it available to direct importers. The `example.Notations` module exports the term notation `~~` and the tactic `finish`. Run `example/Syntax.lol` to see `Compute ~~ Low.` print `High` and `Compute ~~ ~~ Low.` print `Low`. [Notation declarations](../example/Notations.lol) · [Using imported notation](../example/Syntax.lol)

## A record with a dependent field

Return to `Walkthrough.lol` and append the declarations below. A `Package` stores a type and a value of that type.

```lol
#[projections(primitive)]
Record Package : Type@{1} := pack { carrier : Set ; point : carrier }.

Definition unpack (p : Package) : p.(carrier) := p.(point).
Definition sample : Package := pack Height three.
Check unpack.
Compute unpack sample.
```

In `pack Height three`, the `carrier` field is `Height`, so the `point` field must hold a value of type `Height`. For an arbitrary package `p`, the type of `p.(point)` is `p.(carrier)`. Here `Check unpack.` prints `forall x : Package, x.(carrier)` and `Compute unpack sample.` prints `up (up (up base))`.

`#[projections(primitive)]` selects primitive projections for this record. Rebuilding a value from all its projections yields a definitionally equal record, a property called record η (eta). In the `swap_swap` example, this lets `reflexivity.` finish the proof after `intros`. [Records and projections](../example/Records.lol)

## Using a definition at different universes

```lol
Polymorphic Definition ident@{u} (A : Type@{u}) (x : A) : A := x.
Check ident@{0}.
Compute ident@{1} Set Height.
```

`Set` is `Type@{0}`. You can apply `ident@{0}` to a small type such as `Height` and a value of that type. To pass `Set` itself, use `ident@{1}`. The `Compute` above prints `Height`. [Universe polymorphism and cumulativity](../example/Universes.lol)

Use `#[universes(template)]` on an inductive declaration whose result universe should depend on its argument.

```lol
#[universes(template)]
Inductive Box (A : Type) : Type := | box : A -> Box A.

Check (Box Height).
Check (Box Set).
```

`Box Height` has type `Type@{0}` and `Box Set` has type `Type@{1}`. In each application the argument to `Box` determines the universe.

## When an inductive or recursive definition is rejected

- **`[I-Pos]` (strict positivity).** The constructor `wrap : (Bad -> Empty) -> Bad` would store a function with `Bad` as its input. This occurrence of `Bad` fails the strict positivity check. To represent recursive data, store the smaller value directly, as in `up : Height -> Height`. You can define a separate function such as `addHeight` to process that value. [Rejected constructor](../example/rejected/Positivity.lol)
- **`[F-Guard]` (structural recursion).** The recursive call `forever (S n)` makes the argument larger. Match on the argument named by `{struct n}` and check that each recursive branch calls the function on a subterm, as `addHeight p m` does in the `up p` branch. [Rejected recursive call](../example/rejected/Guard.lol)

## Working with the standard library

The library example imports `lol.theories.Nat` and `lol.theories.List` to use `nat`, `list`, `length` and `rev`. Its first `Compute` prints the length of a three-element list as `S (S (S O))`. Run it from the project root. [Standard library example](../example/Library.lol)

```sh
cabal run -v0 lol -- example/Library.lol
```

An indexed type can carry the length of a sequence in its type. For `vec`, the clause `match v in vec _ k return ...` lets the result type depend on the length index `k`. [Length-indexed vectors](../example/Vectors.lol) · [Mutual inductives and recursion](../example/Mutual.lol)

[Repository reference](reference.md)
