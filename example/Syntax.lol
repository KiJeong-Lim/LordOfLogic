(* Notation from an imported module.
   Run from the root of the repository:

       cabal run -v0 lol -- example/Syntax.lol
*)

Import lol.theories.Logic.
Import example.Notations.

Compute ~~ Low.
Compute ~~ ~~ Low.

Theorem toggle_twice : forall b : Bit, ~~ ~~ b = b.
Proof.
    intro b.
    destruct b.
    - finish (eq_refl Low).
    - finish (eq_refl High).
Qed.

Print Assumptions toggle_twice.
