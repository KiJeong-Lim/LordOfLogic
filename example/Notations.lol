(* A module that exports notation and a tactic notation.
   Syntax.lol imports this module. It can also be checked by itself:

       cabal run -v0 lol -- example/Notations.lol
*)

Import lol.theories.Logic.

Inductive Bit : Set := | Low : Bit | High : Bit.

Definition toggle (b : Bit) : Bit :=
    match b with
    | Low => High
    | High => Low
    end.

(* ~~ b is toggle b, at level 9, right associative. *)
Notation "~~ $term" := toggle (at level 9, right associativity).

(* finish t is exact t. *)
Tactic Notation "finish $term" := exact.
