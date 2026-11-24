(* A template record with a primitive projection.
   Run from the root of the repository:

       cabal run -v0 lol -- example/Records.lol
*)

Import lol.theories.Logic.
Import lol.theories.Nat.

#[universes(template)] #[projections(primitive)]
Record Pair (A B : Type) : Type := mkPair { first : A ; second : B }.

Definition swap (A B : Type) (p : Pair A B) : Pair B A :=
    mkPair B A p.(second) p.(first).

Definition sample : Pair nat (Pair nat nat) := mkPair nat (Pair nat nat) O (mkPair nat nat (S O) (S (S O))).

Compute sample.(second).(first).
Compute (swap nat (Pair nat nat) sample).(second).

(* The record has definitional eta: any p is mkPair of its two projections. *)
Theorem swap_swap : forall (A B : Type) (p : Pair A B), swap B A (swap A B p) = p.
Proof.
    intros A B p.
    reflexivity.
Qed.

Print Assumptions swap_swap.
