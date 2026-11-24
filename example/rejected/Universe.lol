(* Type@{0} is a member of Type@{1}, not of itself. A type of all types
   would make the logic inconsistent.

       cabal run -v0 lol -- example/rejected/Universe.lol
*)

Definition Everything : Type@{0} := Type@{0}.
