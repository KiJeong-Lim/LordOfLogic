(* Indexed vectors and finite indices. Index computations stay in the kernel. *)
Import lol.theories.Logic.
Import lol.theories.Nat.
Import lol.theories.List.
Inductive vec (A : Set) : nat -> Set := | vnil : vec A O | vcons : forall n : nat, A -> vec A n -> vec A (S n).
Inductive fin : nat -> Set := | fzero : forall n : nat, fin (S n) | fsucc : forall n : nat, fin n -> fin (S n).
Definition vlength {A : Set} (n : nat) (v : vec A n) : nat := match v with | vnil _ => O | vcons _ k x t => S k end.
Fixpoint vto_list {A : Set} (n : nat) (v : vec A n) : list A := match v with | vnil _ => nil A | vcons _ k x t => cons x (vto_list k t) end.
Fixpoint vmap {A B : Set} (f : A -> B) (n : nat) (v : vec A n) : vec B n := match v with | vnil _ => vnil B | vcons _ k x t => vcons B k (f x) (vmap f k t) end.
Fixpoint vappend {A : Set} (n m : nat) (v : vec A n) (w : vec A m) : vec A (add n m) := match v with | vnil _ => w | vcons _ k x t => vcons A (add k m) x (vappend k m t w) end.
Fixpoint vrepeat {A : Set} (x : A) (n : nat) : vec A n := match n with | O => vnil A | S k => vcons A k x (vrepeat x k) end.
Fixpoint vfold_right {A B : Set} (f : A -> B -> B) (z : B) (n : nat) (v : vec A n) : B := match v with | vnil _ => z | vcons _ k x t => f x (vfold_right f z k t) end.
Definition vhead {A : Set} (n : nat) (v : vec A (S n)) : A := match v in vec _ k return (match k return Set with | O => True | S p => A end) with | vnil _ => I | vcons _ k x t => x end.
Definition vtail {A : Set} (n : nat) (v : vec A (S n)) : vec A n := match v in vec _ k return (match k return Set with | O => vec A O | S p => vec A p end) with | vnil _ => vnil A | vcons _ k x t => t end.
Fixpoint fin_to_nat (n : nat) (f : fin n) : nat := match f with | fzero k => O | fsucc k p => S (fin_to_nat k p) end.
Fixpoint fin_weaken (n : nat) (f : fin n) : fin (S n) := match f with | fzero k => fzero (S k) | fsucc k p => fsucc (S k) (fin_weaken k p) end.
Definition fin_shift (n : nat) (f : fin n) : fin (S n) := fsucc n f.
Fixpoint vconcat {A : Set} (n m : nat) (v : vec (vec A m) n) : vec A (mul n m) := match v with | vnil _ => vnil A | vcons _ k x t => vappend m (mul k m) x (vconcat k m t) end.
Definition vec_induction {A : Set} (P : forall n : nat, vec A n -> Prop) (z : P O (vnil A)) (s : forall (n : nat) (x : A) (v : vec A n), P n v -> P (S n) (vcons A n x v)) : forall (n : nat) (v : vec A n), P n v := fix go (n : nat) (v : vec A n) : P n v := match v with | vnil _ => z | vcons _ k x t => s k x t (go k t) end.
Definition vsum (n : nat) (v : vec nat n) : nat := vfold_right add O n v.
Definition vproduct (n : nat) (v : vec nat n) : nat := vfold_right mul one n v.
Theorem vhead_cons : forall (A : Set) (n : nat) (x : A) (v : vec A n), ((vhead n (vcons A n x v)) = x) := fun A n x v => eq_refl x.
Theorem vtail_cons : forall (A : Set) (n : nat) (x : A) (v : vec A n), ((vtail n (vcons A n x v)) = v) := fun A n x v => eq_refl v.
Theorem vappend_nil : forall (A : Set) (n : nat) (v : vec A n), ((vappend O n (vnil A) v) = v) := fun A n v => eq_refl v.
Theorem vmap_nil : forall (A B : Set) (f : A -> B), ((vmap f O (vnil A)) = (vnil B)) := fun A B f => eq_refl (vnil B).
Theorem vrepeat_O : forall (A : Set) (x : A), ((vrepeat x O) = (vnil A)) := fun A x => eq_refl (vnil A).
Theorem fin_shift_value : forall (n : nat) (f : fin n), ((fin_to_nat (S n) (fin_shift n f)) = (S (fin_to_nat n f))) := fun n f => eq_refl (S (fin_to_nat n f)).
Theorem vlength_index : forall (A : Set) (n : nat) (v : vec A n), ((vlength n v) = n) := fun A n v => match v with | vnil _ => eq_refl O | vcons _ k x t => eq_refl (S k) end.
Theorem vto_list_length : forall (A : Set) (n : nat) (v : vec A n), ((length (vto_list n v)) = n) := fun A => fix go (n : nat) (v : vec A n) : ((length (vto_list n v)) = n) := match v with | vnil _ => eq_refl O | vcons _ k x t => f_equal S (length (vto_list k t)) k (go k t) end.
Theorem vmap_id : forall (A : Set) (n : nat) (v : vec A n), ((vmap (fun x => x) n v) = v) := fun A => fix go (n : nat) (v : vec A n) : ((vmap (fun x => x) n v) = v) := match v with | vnil _ => eq_refl (vnil A) | vcons _ k x t => f_equal (vcons A k x) (vmap (fun y => y) k t) t (go k t) end.
Theorem fin_weaken_value : forall (n : nat) (f : fin n), ((fin_to_nat (S n) (fin_weaken n f)) = (fin_to_nat n f)) := fix go (n : nat) (f : fin n) : ((fin_to_nat (S n) (fin_weaken n f)) = (fin_to_nat n f)) := match f with | fzero k => eq_refl O | fsucc k p => f_equal S (fin_to_nat (S k) (fin_weaken k p)) (fin_to_nat k p) (go k p) end.
