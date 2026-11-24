(* Accessibility and well-founded recursion are ordinary inductive proofs. *)
(* Witness builders stay transparent: recursive programs inspect them. *)
Import lol.theories.Logic.
Import lol.theories.Nat.
Definition relation (A : Set) : Type@{1} := A -> A -> Prop.
Inductive Acc (A : Set) (R : relation A) (x : A) : Prop := | Acc_intro : (forall y : A, R y x -> Acc A R y) -> Acc A R x.
Definition well_founded (A : Set) (R : relation A) : Prop := forall x : A, Acc A R x.
Definition subrelation {A : Set} (R S : relation A) : Prop := forall x y : A, R x y -> S x y.
Definition transitive {A : Set} (R : relation A) : Prop := forall x y z : A, R x y -> R y z -> R x z.
Definition reflexive {A : Set} (R : relation A) : Prop := forall x : A, R x x.
Definition symmetric {A : Set} (R : relation A) : Prop := forall x y : A, R x y -> R y x.
Definition irreflexive {A : Set} (R : relation A) : Prop := forall x : A, not (R x x).
Definition asymmetric {A : Set} (R : relation A) : Prop := forall x y : A, R x y -> not (R y x).
Definition inverse_relation {A : Set} (R : relation A) : relation A := fun x y => R y x.
Definition relation_intersection {A : Set} (R S : relation A) : relation A := fun x y => and (R x y) (S x y).
Definition relation_union {A : Set} (R S : relation A) : relation A := fun x y => or (R x y) (S x y).
Definition inverse_image {A B : Set} (R : relation B) (f : A -> B) : relation A := fun x y => R (f x) (f y).
Definition Acc_inv {A : Set} (R : relation A) (x : A) (a : Acc A R x) (y : A) (r : R y x) : Acc A R y := match a with | Acc_intro _ _ _ h => h y r end.
Definition Acc_induction {A : Set} (R : relation A) (P : A -> Prop) (step : forall x : A, (forall y : A, R y x -> P y) -> P x) : forall x : A, Acc A R x -> P x := fix go (x : A) (a : Acc A R x) : P x := match a with | Acc_intro _ _ _ h => step x (fun y r => go y (h y r)) end.
Definition Acc_recursion {A : Set} (R : relation A) (P : A -> Set) (step : forall x : A, (forall y : A, R y x -> P y) -> P x) : forall x : A, Acc A R x -> P x := fix go (x : A) (a : Acc A R x) : P x := match a with | Acc_intro _ _ _ h => step x (fun y r => go y (h y r)) end.
Definition wf_induction {A : Set} (R : relation A) (wf : well_founded A R) (P : A -> Prop) (step : forall x : A, (forall y : A, R y x -> P y) -> P x) (x : A) : P x := Acc_induction R P step x (wf x).
Definition wf_recursion {A : Set} (R : relation A) (wf : well_founded A R) (P : A -> Set) (step : forall x : A, (forall y : A, R y x -> P y) -> P x) (x : A) : P x := Acc_recursion R P step x (wf x).
Definition Acc_subrelation : forall (A : Set) (R S : relation A), subrelation S R -> forall x : A, Acc A R x -> Acc A S x := fun A R S sub => fix go (x : A) (a : Acc A R x) : Acc A S x := match a with | Acc_intro _ _ _ h => Acc_intro A S x (fun y s => go y (h y (sub y x s))) end.
Definition well_founded_subrelation : forall (A : Set) (R S : relation A), subrelation S R -> well_founded A R -> well_founded A S := fun A R S sub wf x => Acc_subrelation A R S sub x (wf x).
Theorem Acc_irreflexive : forall (A : Set) (R : relation A) (x : A), Acc A R x -> not (R x x) := fun A R => fix go (x : A) (a : Acc A R x) : not (R x x) := match a with | Acc_intro _ _ _ h => fun r => go x (h x r) r end.
Theorem well_founded_irreflexive : forall (A : Set) (R : relation A), well_founded A R -> irreflexive R := fun A R wf x => Acc_irreflexive A R x (wf x).
Definition empty_relation {A : Set} : relation A := fun x y => False.
Definition empty_well_founded : forall A : Set, well_founded A (empty_relation) := fun A x => Acc_intro A (empty_relation) x (fun y r => False_rect (Acc A (empty_relation) y) r).
Definition predecessor_relation : relation nat := fun x y => ((S x) = y).
Definition predecessor_well_founded : well_founded nat predecessor_relation := fix go (n : nat) : Acc nat predecessor_relation n := match n with | O => Acc_intro nat predecessor_relation O (fun y e => False_rect (Acc nat predecessor_relation y) (S_not_O y e)) | S p => Acc_intro nat predecessor_relation (S p) (fun y e => eq_transport nat (fun k => Acc nat predecessor_relation k) p y (eq_sym y p (f_equal pred (S y) (S p) e)) (go p)) end.
Theorem intersection_sub_left : forall (A : Set) (R S : relation A), subrelation (relation_intersection R S) R := fun A R S x y h => and_left (R x y) (S x y) h.
Theorem intersection_sub_right : forall (A : Set) (R S : relation A), subrelation (relation_intersection R S) S := fun A R S x y h => and_right (R x y) (S x y) h.
Definition well_founded_intersection : forall (A : Set) (R S : relation A), well_founded A R -> well_founded A (relation_intersection R S) := fun A R S wf => well_founded_subrelation A R (relation_intersection R S) (intersection_sub_left A R S) wf.
(* This accessibility witness is transparent so recursion can compute. *)
Definition wf_nat_recursion (P : nat -> Set) (z : P O) (step : forall n : nat, P n -> P (S n)) : forall n : nat, P n := wf_recursion predecessor_relation predecessor_well_founded P (fun n rec => (match n as k return (forall y : nat, predecessor_relation y k -> P y) -> P k with | O => fun h => z | S p => fun h => step p (h p (eq_refl (S p))) end) rec).
Definition wf_factorial (n : nat) : nat := wf_nat_recursion (fun k => nat) one (fun p result => mul (S p) result) n.
