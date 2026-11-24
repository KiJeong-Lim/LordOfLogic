(* Propositional and predicate logic in proof mode.
   Run from the root of the repository:

       cabal run -v0 lol -- example/Logic.lol
*)

Import lol.theories.Logic.
Import lol.theories.Nat.

(* destruct names the parts of a hypothesis. split proves a conjunction,
   and each bullet proves one of the goals that it leaves. *)
Theorem and_swap : forall A B : Prop, and A B -> and B A.
Proof.
    intros A B h.
    destruct h as a b.
    split.
    - exact b.
    - exact a.
Qed.

(* For a disjunction, each case receives its own name: a in the first, b in the second. *)
Theorem or_swap : forall A B : Prop, or A B -> or B A.
Proof.
    intros A B h.
    destruct h as a b.
    - right.
      exact a.
    - left.
      exact b.
Qed.

(* not A is A -> False, so intros reads past it. *)
Theorem double_negation : forall A : Prop, A -> not (not A).
Proof.
    intros A a n.
    apply n.
    exact a.
Qed.

Theorem contrapositive : forall A B : Prop, (A -> B) -> not B -> not A.
Proof.
    intros A B f nb a.
    apply nb.
    apply f.
    exact a.
Qed.

(* exfalso replaces the goal with False. *)
Theorem absurd : forall A B : Prop, A -> not A -> B.
Proof.
    intros A B a na.
    exfalso.
    apply na.
    exact a.
Qed.

(* A theorem is used like any other constant. *)
Theorem and_comm_iff : forall A B : Prop, iff (and A B) (and B A).
Proof.
    intros A B.
    split.
    - exact (and_swap A B).
    - exact (and_swap B A).
Qed.

(* exists gives the witness of an existential statement. *)
Theorem four_is_a_double : ex nat (fun n => n + n = S (S (S (S O)))).
Proof.
    exists (S (S O)).
    reflexivity.
Qed.

(* destruct opens an existential hypothesis into its witness and its proof. *)
Theorem exists_map : forall P Q : nat -> Prop,
    (forall n : nat, P n -> Q n) -> ex nat P -> ex nat Q.
Proof.
    intros P Q f h.
    destruct h as x px.
    exists x.
    apply f.
    exact px.
Qed.

Print Assumptions exists_map.
