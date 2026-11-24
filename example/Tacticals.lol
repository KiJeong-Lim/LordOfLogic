(* Tactics that combine tactics, and tactics that restate goals and hypotheses.
   Run from the root of the repository:

       cabal run -v0 lol -- example/Tacticals.lol
*)

Import lol.theories.Logic.
Import lol.theories.Nat.

Numerals O S.

(* t1; t2 runs t2 on every goal that t1 leaves. *)
Theorem both_sides : and (2 + 2 = 4) (3 * 3 = 9).
Proof.
    split; reflexivity.
Qed.

(* repeat runs a tactic until it fails. *)
Theorem all_three : forall A B C : Prop, A -> B -> C -> and A (and B C).
Proof.
    intros A B C a b c.
    repeat split.
    - exact a.
    - exact b.
    - exact c.
Qed.

(* all: runs a tactic on every goal; first runs the first alternative that succeeds. *)
Theorem either_way : forall A B : Prop, A -> B -> and A B.
Proof.
    intros A B a b.
    split.
    all: first [ exact a | exact b ].
Qed.

(* try runs a tactic and ignores its failure. *)
Theorem with_truth : forall A : Prop, A -> and A True.
Proof.
    intros A a.
    split.
    - try exact I.
      exact a.
    - exact I.
Qed.

(* constructor 2 applies the second constructor. *)
Theorem second_choice : or False True.
Proof.
    constructor 2.
    exact I.
Qed.

(* assert proves an intermediate statement first. specialize applies a hypothesis. *)
Theorem two_steps : forall P : nat -> Prop, (forall n : nat, P n -> P (S n)) -> P 0 -> P 2.
Proof.
    intros P step zero.
    assert (h1 : P 1).
    - apply step.
      exact zero.
    - specialize (step 1 h1).
      exact step.
Qed.

Definition twice (n : nat) : nat := n + n.

(* unfold replaces a constant by its definition. *)
Theorem twice_two : twice 2 = 4.
Proof.
    unfold twice.
    reflexivity.
Qed.

(* change replaces the goal by a convertible one. *)
Theorem twice_three : twice 3 = 6.
Proof.
    change (3 + 3 = 6).
    reflexivity.
Qed.

(* unfold and simpl also work in a hypothesis. *)
Theorem twice_positive : forall n : nat, not (twice (S n) = 0).
Proof.
    intros n h.
    unfold twice in h.
    simpl in h.
    discriminate h.
Qed.

Print Assumptions two_steps.
