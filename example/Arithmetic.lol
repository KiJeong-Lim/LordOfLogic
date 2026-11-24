(* Induction over the natural numbers of example/Basics.lol: the laws of
   addition and multiplication, each proved from the ones before it.
   Run from the root of the repository:

       cabal run -v0 lol -- example/Arithmetic.lol
*)

Import lol.theories.Logic.
Import example.Basics.

(* induction n as p IHp names the predecessor p and the induction hypothesis IHp. *)
Theorem plus_succ : forall n m : Nat, n + Succ m = Succ (n + m).
Proof.
    intros n m.
    induction n as p IHp.
    - reflexivity.
    - simpl.
      rewrite IHp.
      reflexivity.
Qed.

(* plus_zero_tactics comes from example/Basics.lol. *)
Theorem plus_comm : forall n m : Nat, n + m = m + n.
Proof.
    intros n m.
    induction n as p IHp.
    - simpl.
      rewrite (plus_zero_tactics m).
      reflexivity.
    - simpl.
      rewrite IHp.
      rewrite (plus_succ m p).
      reflexivity.
Qed.

Theorem plus_assoc : forall n m k : Nat, n + m + k = n + (m + k).
Proof.
    intros n m k.
    induction n as p IHp.
    - reflexivity.
    - simpl.
      rewrite IHp.
      reflexivity.
Qed.

Fixpoint times (n m : Nat) : Nat :=
    match n with
    | Zero => Zero
    | Succ p => m + times p m
    end.

Infix "*" := times (at level 40, left associativity).

Compute two * (two + two).

Theorem times_zero : forall n : Nat, n * Zero = Zero.
Proof.
    intro n.
    induction n as p IHp.
    - reflexivity.
    - simpl.
      exact IHp.
Qed.

Theorem times_plus : forall n m k : Nat, (n + m) * k = n * k + m * k.
Proof.
    intros n m k.
    induction n as p IHp.
    - reflexivity.
    - simpl.
      rewrite IHp.
      rewrite (plus_assoc k (p * k) (m * k)).
      reflexivity.
Qed.

Print Assumptions times_plus.
