(* Tactics written in Hol, in example/UserTactics.hol. The tactic only
   proposes a term: the kernel still checks the whole proof at Qed.
   Run from the root of the repository:

       cabal run -v0 lol -- example/UserTactics.lol
*)

Import lol.theories.Logic.

Load Tactics "example/UserTactics.hol".

Theorem by_hypothesis : forall P Q : Prop, P -> Q -> P.
Proof.
    intros P Q p q.
    tactic hypothesis.
Qed.

Theorem by_term : forall P Q : Prop, P -> Q -> and P Q.
Proof.
    intros P Q p q.
    tactic give (conj P Q p _).
    tactic hypothesis.
Qed.

Print Assumptions by_term.
