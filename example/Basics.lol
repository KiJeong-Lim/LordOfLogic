(* Natural numbers, addition and one fact proved twice: by a term and by tactics.
   Run from the root of the repository:

       cabal run -v0 lol -- example/Basics.lol
*)

Import lol.theories.Logic.

Inductive Nat : Set := | Zero : Nat | Succ : Nat -> Nat.

Fixpoint plus (n m : Nat) : Nat :=
    match n with
    | Zero => m
    | Succ p => Succ (plus p m)
    end.

Infix "+" := plus (at level 50, left associativity).

Definition two : Nat := Succ (Succ Zero).

Check plus.
Compute two + two.

(* A proof term: structural recursion on n. *)
Theorem plus_zero_term : forall n : Nat, n + Zero = n :=
    fix go (n : Nat) : n + Zero = n :=
        match n with
        | Zero => eq_refl Zero
        | Succ p => f_equal Succ (p + Zero) p (go p)
        end.

(* The same statement in proof mode. The kernel checks the finished term at Qed. *)
Theorem plus_zero_tactics : forall n : Nat, n + Zero = n.
Proof.
    intro n.
    induction n.
    - reflexivity.
    - simpl.
      rewrite IHn.
      reflexivity.
Qed.

Print Assumptions plus_zero_tactics.
