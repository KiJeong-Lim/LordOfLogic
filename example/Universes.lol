(* Universes. Set is Type@{0}, and Type@{i} is a member of Type@{i+1}.
   Run from the root of the repository:

       cabal run -v0 lol -- example/Universes.lol
*)

Check Prop.
Check Set.
Check Type@{1}.

(* Prop is impredicative: a proposition may quantify over all propositions. *)
Definition Truth : Prop := forall P : Prop, P -> P.

(* Cumulativity: a member of Set is also a member of Type@{1}. *)
Definition raise (A : Set) : Type@{1} := A.

(* A universe-polymorphic definition takes a universe level as an argument. *)
Polymorphic Definition pid@{u} (A : Type@{u}) (x : A) : A := x.

Check pid@{0}.
Check pid@{1}.

Inductive Bit : Set := | b0 : Bit | b1 : Bit.

Compute pid@{0} Bit b1.
Compute pid@{1} Set Bit.
