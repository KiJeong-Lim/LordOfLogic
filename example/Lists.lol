(* Lists from the standard library: computation and induction.
   Run from the root of the repository:

       cabal run -v0 lol -- example/Lists.lol
*)

Import lol.theories.Logic.
Import lol.theories.Nat.
Import lol.theories.List.

Numerals O S.

Definition digits : list nat := cons 1 (cons 2 (cons 3 (nil nat))).

Compute app digits (rev digits).
Compute map (fun n : nat => n * 2) digits.
Compute fold_right add 0 digits.

Theorem map_app : forall (A B : Set) (f : A -> B) (l m : list A),
    map f (app l m) = app (map f l) (map f m).
Proof.
    intros A B f l m.
    induction l as x t IHt.
    - reflexivity.
    - simpl.
      rewrite IHt.
      reflexivity.
Qed.

(* app_nil_right and app_assoc are lemmas of lol.theories.List. *)
Theorem rev_app : forall (A : Set) (l m : list A), rev (app l m) = app (rev m) (rev l).
Proof.
    intros A l m.
    induction l as x t IHt.
    - simpl.
      rewrite (app_nil_right A (rev m)).
      reflexivity.
    - simpl.
      rewrite IHt.
      apply app_assoc.
Qed.

Theorem rev_rev : forall (A : Set) (l : list A), rev (rev l) = l.
Proof.
    intros A l.
    induction l as x t IHt.
    - reflexivity.
    - simpl.
      rewrite (rev_app A (rev t) (cons x (nil A))).
      simpl.
      rewrite IHt.
      reflexivity.
Qed.

Print Assumptions rev_rev.
