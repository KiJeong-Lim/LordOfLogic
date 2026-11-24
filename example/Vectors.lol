(* Vectors: lists whose length is part of their type.
   Run from the root of the repository:

       cabal run -v0 lol -- example/Vectors.lol
*)

Import lol.theories.Logic.
Import lol.theories.Nat.
Import lol.theories.List.
Import lol.theories.Vec.

Numerals O S.

(* vcons takes the element type, the length of the tail, the head and the tail. *)
Definition v3 : vec nat 3 := vcons nat 2 1 (vcons nat 1 2 (vcons nat 0 3 (vnil nat))).

(* vhead takes a vector of length S n, so it has no case for the empty vector. *)
Check @vhead.
Compute vhead 2 v3.
Compute vto_list 2 (vtail 2 v3).
Compute vto_list 6 (vappend 3 3 v3 v3).

(* The return clause says how the index of the result follows the index of v. *)
Fixpoint vsnoc {A : Set} (n : nat) (v : vec A n) (x : A) : vec A (S n) :=
    match v in vec _ k return vec A (S k) with
    | vnil _ => vcons A O x (vnil A)
    | vcons _ k y t => vcons A (S k) y (vsnoc k t x)
    end.

Fixpoint vreverse {A : Set} (n : nat) (v : vec A n) : vec A n :=
    match v in vec _ k return vec A k with
    | vnil _ => vnil A
    | vcons _ k y t => vsnoc k (vreverse k t) y
    end.

Compute vto_list 3 (vreverse 3 v3).

(* Induction on a vector also generalizes its length. *)
Theorem vsnoc_list : forall (A : Set) (n : nat) (v : vec A n) (x : A),
    vto_list (S n) (vsnoc n v x) = app (vto_list n v) (cons x (nil A)).
Proof.
    intros A n v x.
    induction v as k y t IHt.
    - reflexivity.
    - simpl.
      rewrite IHt.
      reflexivity.
Qed.

Print Assumptions vsnoc_list.
