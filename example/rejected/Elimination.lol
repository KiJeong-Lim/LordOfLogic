(* A proof of a proposition cannot decide a value of a data type: which
   side of an or holds is not data.

       cabal run -v0 lol -- example/rejected/Elimination.lol
*)

Import lol.theories.Logic.
Import lol.theories.Bool.

Definition which (h : or True True) : bool :=
    match h with
    | or_introl _ _ a => true
    | or_intror _ _ b => false
    end.
