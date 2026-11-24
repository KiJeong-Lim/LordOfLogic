(* A recursive call must be on a structurally smaller argument. Here the
   argument grows, so the guard condition rejects the definition.

       cabal run -v0 lol -- example/rejected/Guard.lol
*)

Import lol.theories.Nat.

Fixpoint forever (n : nat) : nat := forever (S n).
