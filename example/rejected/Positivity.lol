(* An inductive type may not occur to the left of an arrow in the type of
   one of its own constructors. From Bad one could derive Empty, so strict
   positivity rejects it.

       cabal run -v0 lol -- example/rejected/Positivity.lol
*)

Inductive Empty : Prop := .

Inductive Bad : Type := | wrap : (Bad -> Empty) -> Bad.
