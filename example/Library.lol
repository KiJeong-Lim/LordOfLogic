(* Using the standard library in lol/theories.
   Run from the root of the repository:

       cabal run -v0 lol -- example/Library.lol
*)

Import lol.theories.Logic.
Import lol.theories.Nat.
Import lol.theories.List.

(* Numerals 0, 1, 2, ... are read with O and S. *)
Numerals O S.

Definition sample : list nat := cons 3 (cons 1 (cons 2 (nil nat))).

Compute length sample.
Compute rev sample.
Compute map (fun n : nat => n * n) sample.

(* Library lemmas rewrite the goal. *)
Theorem add_swap : forall n m : nat, n + (m + 0) = m + n.
Proof.
    intros n m.
    rewrite (add_n_O m).
    apply add_comm.
Qed.

(* Induction over lists. *)
Theorem length_app_nil : forall (A : Set) (l : list A), length (app l (nil A)) = length l.
Proof.
    intros A l.
    induction l.
    - reflexivity.
    - simpl.
      rewrite IHl.
      reflexivity.
Qed.

Print Assumptions add_swap.
Print Assumptions length_app_nil.
