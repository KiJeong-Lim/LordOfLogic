(* Ordinary guarded recursion, a nested positive occurrence and universe
   cumulativity. The result equations are closed kernel-checked proof terms. *)
Inductive Nat : Set := | z : Nat | s : Nat -> Nat.
Inductive Seq (A : Set) : Set := | empty : Seq A | add : A -> Seq A -> Seq A.
Inductive Tree : Set := | branch : Seq Tree -> Tree.
Fixpoint drop_one (n : Nat) {struct n} : Nat :=
    match n with | z => z | s p => p end.
Fixpoint double (n : Nat) {struct n} : Nat :=
    match n with | z => z | s p => s (s (double p)) end.
Inductive Same (A : Set) (x : A) : A -> Prop := | same : Same A x x.
Theorem computed : Same Nat (drop_one (double (s z))) (s z) := same Nat (s z).
Definition lifted : Type@{1} := Set.
Check branch (empty Tree).
Print Assumptions computed.

Fixpoint left_depth (t : Tree) {struct t} : Nat :=
    match t with
    | branch children =>
        match children with
        | empty _ => z
        | add _ child _ => s (left_depth child)
        end
    end.
Definition leaf : Tree := branch (empty Tree).
Theorem depth_one :
    Same Nat (left_depth (branch (add Tree leaf (empty Tree)))) (s z)
    := same Nat (s z).
Print Assumptions depth_one.

(* Count every node of a rose tree, including all siblings. The recursive
   function is an argument to the global map over the constructor field. *)
Fixpoint sequence_map (A B : Set) (f : A -> B) (xs : Seq A)
    {struct xs} : Seq B :=
    match xs with
    | empty _ => empty B
    | add _ x rest => add B (f x) (sequence_map A B f rest)
    end.
Fixpoint plus (n m : Nat) {struct n} : Nat :=
    match n with | z => m | s p => s (plus p m) end.
Fixpoint total (xs : Seq Nat) {struct xs} : Nat :=
    match xs with | empty _ => z | add _ x rest => plus x (total rest) end.
Fixpoint tree_size (t : Tree) {struct t} : Nat :=
    match t with
    | branch children => s (total (sequence_map Tree Nat tree_size children))
    end.
Definition forked : Tree := branch (add Tree leaf (add Tree leaf (empty Tree))).
Theorem forked_size : Same Nat (tree_size forked) (s (s (s z))) :=
    same Nat (s (s (s z))).
Print Assumptions forked_size.

(* Equality elimination into an indexed family. At reflexivity the carried
   value and the proof of dependent congruence both compute. *)
Definition eq_refl (A : Set) (x : A) : Same A x x := same A x.
Inductive At (n : Nat) : Set := | mark : At n.
Definition carry (A : Set) (P : A -> Set) (x y : A)
    (e : Same A x y) (v : P x) : P y :=
    match e with | same _ _ => v end.
Definition mark_cong (x y : Nat) (e : Same Nat x y) :
    Same (At y) (carry Nat At x y e (mark x)) (mark y) :=
    match e with | same _ _ => same (At x) (mark x) end.
Theorem carried_mark :
    Same (At (s z)) (carry Nat At (s z) (s z) (eq_refl Nat (s z)) (mark (s z))) (mark (s z)) :=
    same (At (s z)) (mark (s z)).
Print Assumptions carried_mark.
Theorem congruence_computes :
    Same (Same (At (s z)) (mark (s z)) (mark (s z)))
        (mark_cong (s z) (s z) (eq_refl Nat (s z))) (same (At (s z)) (mark (s z))) :=
    same (Same (At (s z)) (mark (s z)) (mark (s z))) (same (At (s z)) (mark (s z))).
Print Assumptions congruence_computes.

(* A uniform payload type is passed through both members of the block.
   The fixture takes both mutual edges and visits the sibling tail. *)
Inductive Node (A : Set) : Set := | node : A -> Grove A -> Node A
with Grove (A : Set) : Set := | clearing : Grove A | plant : Node A -> Grove A -> Grove A.
Fixpoint node_count (A : Set) (t : Node A) {struct t} : Nat :=
    match t with | node _ _ children => s (grove_count A children) end
with grove_count (A : Set) (xs : Grove A) {struct xs} : Nat :=
    match xs with
    | clearing _ => z
    | plant _ t rest => plus (node_count A t) (grove_count A rest)
    end.
Definition twig : Node Nat := node Nat z (clearing Nat).
Definition pair_grove : Grove Nat := plant Nat twig (plant Nat twig (clearing Nat)).
Theorem uniform_count : Same Nat (node_count Nat (node Nat z pair_grove)) (s (s (s z))) :=
    same Nat (s (s (s z))).
Print Assumptions uniform_count.
