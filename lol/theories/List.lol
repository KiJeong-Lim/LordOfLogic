(* Lists: folds, transformations, bounded observations and structural laws. *)
Import lol.theories.Logic.
Import lol.theories.Nat.
Import lol.theories.Bool.
Inductive list (A : Set) : Set := | nil : list A | cons : A -> list A -> list A.
Arguments cons {A} x tail.
Fixpoint length {A : Set} (l : list A) : nat := match l with | nil _ => O | cons x t => S (length t) end.
Fixpoint app {A : Set} (l m : list A) : list A := match l with | nil _ => m | cons x t => cons x (app t m) end.
Fixpoint map {A B : Set} (f : A -> B) (l : list A) : list B := match l with | nil _ => nil B | cons x t => cons (f x) (map f t) end.
Fixpoint rev {A : Set} (l : list A) : list A := match l with | nil _ => nil A | cons x t => app (rev t) (cons x (nil A)) end.
Fixpoint fold_right {A B : Set} (f : A -> B -> B) (z : B) (l : list A) : B := match l with | nil _ => z | cons x t => f x (fold_right f z t) end.
Fixpoint fold_left {A B : Set} (f : B -> A -> B) (z : B) (l : list A) : B := match l with | nil _ => z | cons x t => fold_left f (f z x) t end.
Definition hd {A : Set} (d : A) (l : list A) : A := match l with | nil _ => d | cons x t => x end.
Definition head_option {A : Set} (l : list A) : option A := match l with | nil _ => None A | cons x t => Some A x end.
Definition tail {A : Set} (l : list A) : list A := match l with | nil _ => nil A | cons x t => t end.
Fixpoint nth {A : Set} (d : A) (l : list A) (n : nat) : A := match l with | nil _ => d | cons x t => match n with | O => x | S p => nth d t p end end.
Fixpoint nth_error {A : Set} (l : list A) (n : nat) : option A := match l with | nil _ => None A | cons x t => match n with | O => Some A x | S p => nth_error t p end end.
Fixpoint repeat {A : Set} (x : A) (n : nat) : list A := match n with | O => nil A | S p => cons x (repeat x p) end.
Fixpoint filter {A : Set} (p : A -> bool) (l : list A) : list A := match l with | nil _ => nil A | cons x t => match p x with | true => cons x (filter p t) | false => filter p t end end.
Fixpoint existsb {A : Set} (p : A -> bool) (l : list A) : bool := match l with | nil _ => false | cons x t => orb (p x) (existsb p t) end.
Fixpoint forallb {A : Set} (p : A -> bool) (l : list A) : bool := match l with | nil _ => true | cons x t => andb (p x) (forallb p t) end.
Fixpoint concat {A : Set} (ll : list (list A)) : list A := match ll with | nil _ => nil A | cons l rest => app l (concat rest) end.
Definition flat_map {A B : Set} (f : A -> list B) (l : list A) : list B := concat (map f l).
Fixpoint take {A : Set} (n : nat) (l : list A) : list A := match n with | O => nil A | S p => match l with | nil _ => nil A | cons x t => cons x (take p t) end end.
Fixpoint drop {A : Set} (n : nat) (l : list A) : list A := match n with | O => l | S p => match l with | nil _ => nil A | cons x t => drop p t end end.
Fixpoint combine {A B : Set} (l : list A) (r : list B) : list (prod A B) := match l with | nil _ => nil (prod A B) | cons x t => match r with | nil _ => nil (prod A B) | cons y u => cons (pair A B x y) (combine t u) end end.
Definition list_induction {A : Set} (P : list A -> Prop) (z : P (nil A)) (s : forall (x : A) (l : list A), P l -> P (cons x l)) : forall l : list A, P l := fix go (l : list A) : P l := match l with | nil _ => z | cons x t => s x t (go t) end.
Definition list_recursion {A : Set} (P : list A -> Set) (z : P (nil A)) (s : forall (x : A) (l : list A), P l -> P (cons x l)) : forall l : list A, P l := fix go (l : list A) : P l := match l with | nil _ => z | cons x t => s x t (go t) end.
Definition singleton {A : Set} (x : A) : list A := cons x (nil A).
Definition list_sum (l : list nat) : nat := fold_right add O l.
Definition list_product (l : list nat) : nat := fold_right mul one l.
Theorem length_nil : forall A : Set, ((length (nil A)) = O) := fun A => eq_refl O.
Theorem length_cons : forall (A : Set) (x : A) (l : list A), ((length (cons x l)) = (S (length l))) := fun A x l => eq_refl (S (length l)).
Theorem app_nil_left : forall (A : Set) (l : list A), ((app (nil A) l) = l) := fun A l => eq_refl l.
Theorem app_cons : forall (A : Set) (x : A) (l m : list A), ((app (cons x l) m) = (cons x (app l m))) := fun A x l m => eq_refl (cons x (app l m)).
Theorem map_nil : forall (A B : Set) (f : A -> B), ((map f (nil A)) = (nil B)) := fun A B f => eq_refl (nil B).
Theorem map_cons : forall (A B : Set) (f : A -> B) (x : A) (l : list A), ((map f (cons x l)) = (cons (f x) (map f l))) := fun A B f x l => eq_refl (cons (f x) (map f l)).
Theorem rev_nil : forall A : Set, ((rev (nil A)) = (nil A)) := fun A => eq_refl (nil A).
Theorem rev_cons : forall (A : Set) (x : A) (l : list A), ((rev (cons x l)) = (app (rev l) (singleton x))) := fun A x l => eq_refl (app (rev l) (singleton x)).
Theorem hd_cons : forall (A : Set) (d x : A) (l : list A), ((hd d (cons x l)) = x) := fun A d x l => eq_refl x.
Theorem tail_cons : forall (A : Set) (x : A) (l : list A), ((tail (cons x l)) = l) := fun A x l => eq_refl l.
Theorem nth_cons_O : forall (A : Set) (d x : A) (l : list A), ((nth d (cons x l) O) = x) := fun A d x l => eq_refl x.
Theorem nth_cons_S : forall (A : Set) (d x : A) (l : list A) (n : nat), ((nth d (cons x l) (S n)) = (nth d l n)) := fun A d x l n => eq_refl (nth d l n).
Theorem repeat_O : forall (A : Set) (x : A), ((repeat x O) = (nil A)) := fun A x => eq_refl (nil A).
Theorem repeat_S : forall (A : Set) (x : A) (n : nat), ((repeat x (S n)) = (cons x (repeat x n))) := fun A x n => eq_refl (cons x (repeat x n)).
Theorem take_O : forall (A : Set) (l : list A), ((take O l) = (nil A)) := fun A l => eq_refl (nil A).
Theorem drop_O : forall (A : Set) (l : list A), ((drop O l) = l) := fun A l => eq_refl l.
Theorem app_nil_right : forall (A : Set) (l : list A), ((app l (nil A)) = l) := fun A => fix go (l : list A) : ((app l (nil A)) = l) := match l with | nil _ => eq_refl (nil A) | cons x t => f_equal (cons x) (app t (nil A)) t (go t) end.
Theorem app_assoc : forall (A : Set) (l m n : list A), ((app (app l m) n) = (app l (app m n))) := fun A => fix go (l m n : list A) : ((app (app l m) n) = (app l (app m n))) := match l with | nil _ => eq_refl (app m n) | cons x t => f_equal (cons x) (app (app t m) n) (app t (app m n)) (go t m n) end.
Theorem map_id : forall (A : Set) (l : list A), ((map (fun x => x) l) = l) := fun A => fix go (l : list A) : ((map (fun x => x) l) = l) := match l with | nil _ => eq_refl (nil A) | cons x t => f_equal (cons x) (map (fun y => y) t) t (go t) end.
Theorem length_app : forall (A : Set) (l m : list A), ((length (app l m)) = (add (length l) (length m))) := fun A => fix go (l m : list A) : ((length (app l m)) = (add (length l) (length m))) := match l with | nil _ => eq_refl (length m) | cons x t => f_equal S (length (app t m)) (add (length t) (length m)) (go t m) end.
Theorem length_map : forall (A B : Set) (f : A -> B) (l : list A), ((length (map f l)) = (length l)) := fun A B f => fix go (l : list A) : ((length (map f l)) = (length l)) := match l with | nil _ => eq_refl O | cons x t => f_equal S (length (map f t)) (length t) (go t) end.
