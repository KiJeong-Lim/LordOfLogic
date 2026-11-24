(* An axiom is assumed, not proved. Print Assumptions lists the axioms that
   a declaration depends on.
   Run from the root of the repository:

       cabal run -v0 lol -- example/Axioms.lol
*)

Import lol.theories.Logic.

Axiom excluded_middle : forall P : Prop, or P (not P).

Theorem double_negation_elimination : forall P : Prop, not (not P) -> P.
Proof.
    intros P nn.
    destruct (excluded_middle P) as p np.
    - exact p.
    - exfalso.
      apply nn.
      exact np.
Qed.

(* The converse needs no axiom. *)
Theorem double_negation_introduction : forall P : Prop, P -> not (not P).
Proof.
    intros P p n.
    apply n.
    exact p.
Qed.

Print Assumptions double_negation_elimination.
Print Assumptions double_negation_introduction.
