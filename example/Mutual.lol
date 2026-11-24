(* Mutual inductive definitions and mutual recursion.
   Run from the root of the repository:

       cabal run -v0 lol -- example/Mutual.lol
*)

Import lol.theories.Logic.
Import lol.theories.Nat.
Import lol.theories.Bool.

Numerals O S.

(* Two predicates, each defined with the other. *)
Inductive Even : nat -> Prop :=
    | even_zero : Even O
    | even_succ : forall n : nat, Odd n -> Even (S n)
with Odd : nat -> Prop :=
    | odd_succ : forall n : nat, Even n -> Odd (S n).

Theorem four_even : Even 4.
Proof.
    apply even_succ.
    apply odd_succ.
    apply even_succ.
    apply odd_succ.
    apply even_zero.
Qed.

(* repeat constructor tries the constructors until none applies. *)
Theorem seven_odd : Odd 7.
Proof.
    repeat constructor.
Qed.

(* Two functions, each defined with the other. *)
Fixpoint is_even (n : nat) : bool :=
    match n with
    | O => true
    | S p => is_odd p
    end
with is_odd (n : nat) : bool :=
    match n with
    | O => false
    | S p => is_even p
    end.

Compute is_even 10.
Compute is_odd 10.

(* One induction proves a statement about both functions at once. *)
Theorem parity_sound : forall n : nat,
    and (is_even n = true -> Even n) (is_odd n = true -> Odd n).
Proof.
    intro n.
    induction n as p IHp.
    - split.
      + intro h.
        exact even_zero.
      + intro h.
        discriminate h.
    - destruct IHp as even_p odd_p.
      split.
      + intro h.
        apply even_succ.
        apply odd_p.
        exact h.
      + intro h.
        apply odd_succ.
        apply even_p.
        exact h.
Qed.

(* Trees whose children form a forest, and a forest is a list of trees. *)
Inductive tree : Set :=
    | node : nat -> forest -> tree
with forest : Set :=
    | leaf : forest
    | grow : tree -> forest -> forest.

Fixpoint tree_sum (t : tree) : nat :=
    match t with
    | node n f => n + forest_sum f
    end
with forest_sum (f : forest) : nat :=
    match f with
    | leaf => 0
    | grow t rest => tree_sum t + forest_sum rest
    end.

Definition example_tree : tree :=
    node 1 (grow (node 2 leaf) (grow (node 3 (grow (node 4 leaf) leaf)) leaf)).

Compute tree_sum example_tree.

Print Assumptions parity_sound.
