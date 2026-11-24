(* A tactic that does not apply stops the file with a diagnostic of the
   proof. Earlier commands are kept: the first theorem is admitted.

       cabal run -v0 lol -- example/rejected/Proof.lol
*)

Import lol.theories.Logic.
Import lol.theories.Nat.

Numerals O S.

Theorem right : 1 + 1 = 2.
Proof.
    reflexivity.
Qed.

Theorem wrong : 1 + 1 = 3.
Proof.
    reflexivity.
Qed.
