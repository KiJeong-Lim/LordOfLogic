(* Tactics for equality.
   Run from the root of the repository:

       cabal run -v0 lol -- example/Equality.lol
*)

Import lol.theories.Logic.
Import lol.theories.Nat.

(* injection: a constructor is injective. It leaves the equation of the arguments as a premise. *)
Theorem succ_injective : forall n m : nat, S n = S m -> n = m.
Proof.
    intros n m h.
    injection h.
    intro e.
    exact e.
Qed.

(* discriminate: two different constructors are never equal. *)
Theorem zero_not_succ : forall n : nat, not (O = S n).
Proof.
    intros n h.
    discriminate h.
Qed.

(* transitivity b splits a = c into a = b and b = c. symmetry turns the goal around. *)
Theorem meet : forall a b c : nat, a = b -> c = b -> a = c.
Proof.
    intros a b c ab cb.
    transitivity b.
    - exact ab.
    - symmetry.
      exact cb.
Qed.

(* rewrite <- e in h replaces the right side of e by its left side in h. *)
Theorem transport : forall (P : nat -> Prop) (a b : nat), a = b -> P b -> P a.
Proof.
    intros P a b e pb.
    rewrite <- e in pb.
    exact pb.
Qed.

(* f_equal of lol.theories.Logic applies a function to both sides of an equation. *)
Theorem successors : forall n m : nat, n = m -> S (S n) = S (S m).
Proof.
    intros n m e.
    apply (f_equal S).
    apply (f_equal S).
    exact e.
Qed.

Print Assumptions successors.
