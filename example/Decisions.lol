(* Decisions that carry proofs, from lol.theories.Decidable.
   Run from the root of the repository:

       cabal run -v0 lol -- example/Decisions.lol
*)

Import lol.theories.Logic.
Import lol.theories.Nat.
Import lol.theories.Bool.
Import lol.theories.Decidable.

Numerals O S.

(* Decidable P is sumbool P (not P): yes with a proof of P, or no with a proof of not P. *)
Check nat_eq_dec.

Definition same (n m : nat) : bool :=
    match nat_eq_dec n m with
    | yes _ _ p => true
    | no _ _ q => false
    end.

Compute same 3 3.
Compute same 3 4.

(* destruct on the decision splits the proof into its two answers. *)
Theorem same_sound : forall n m : nat, same n m = true -> n = m.
Proof.
    intros n m.
    unfold same.
    destruct (nat_eq_dec n m) as p q.
    - intro h.
      exact p.
    - intro h.
      discriminate h.
Qed.

Theorem same_complete : forall n : nat, same n n = true.
Proof.
    intro n.
    unfold same.
    destruct (nat_eq_dec n n) as p q.
    - reflexivity.
    - exfalso.
      apply q.
      reflexivity.
Qed.

(* A decidable proposition satisfies the excluded middle without an axiom. *)
Theorem equal_or_not : forall n m : nat, or (n = m) (not (n = m)).
Proof.
    intros n m.
    apply decidable_excluded_middle.
    exact (nat_eq_dec n m).
Qed.

Print Assumptions equal_or_not.
