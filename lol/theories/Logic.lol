(* Logical foundations. No prelude, axioms or generated induction schemes. *)
Inductive False : Prop := .
Inductive True : Prop := | I : True.
Inductive and (A B : Prop) : Prop := | conj : A -> B -> and A B.
Inductive or (A B : Prop) : Prop := | or_introl : A -> or A B | or_intror : B -> or A B.
Inductive ex (A : Set) (P : A -> Prop) : Prop := | ex_intro : forall x : A, P x -> ex A P.
Inductive eq (A : Type@{1}) (x : A) : A -> Prop := | eq_refl : eq A x x.
Arguments eq {A} x y.
Arguments eq_refl {A} x.
Infix "=" := eq (at level 70, no associativity).
Inductive prod (A B : Set) : Set := | pair : A -> B -> prod A B.
Inductive sum (A B : Set) : Set := | inl : A -> sum A B | inr : B -> sum A B.
Inductive option (A : Set) : Set := | None : option A | Some : A -> option A.
Definition not (A : Prop) : Prop := A -> False.
Definition iff (A B : Prop) : Prop := and (A -> B) (B -> A).
Definition id {A : Type@{1}} (x : A) : A := x.
Definition const {A B : Set} (x : A) (y : B) : A := x.
Definition compose {A B C : Set} (f : B -> C) (g : A -> B) (x : A) : C := f (g x).
Definition flip {A B C : Set} (f : A -> B -> C) (y : B) (x : A) : C := f x y.
Definition False_rect (A : Type@{1}) (f : False) : A := match f with end.
Definition and_left (A B : Prop) (h : and A B) : A := match h with | conj _ _ a b => a end.
Definition and_right (A B : Prop) (h : and A B) : B := match h with | conj _ _ a b => b end.
Definition and_map (A B C D : Prop) (f : A -> C) (g : B -> D) (h : and A B) : and C D := conj C D (f (and_left A B h)) (g (and_right A B h)).
Definition or_elim (A B C : Prop) (f : A -> C) (g : B -> C) (h : or A B) : C := match h with | or_introl _ _ a => f a | or_intror _ _ b => g b end.
Definition or_map (A B C D : Prop) (f : A -> C) (g : B -> D) (h : or A B) : or C D := or_elim A B (or C D) (fun a => or_introl C D (f a)) (fun b => or_intror C D (g b)) h.
Definition ex_map (A : Set) (P Q : A -> Prop) (f : forall x : A, P x -> Q x) (h : ex A P) : ex A Q := match h with | ex_intro _ _ x p => ex_intro A Q x (f x p) end.
Definition eq_sym {A : Type@{1}} (x y : A) (e : (x = y)) : (y = x) := match e with | eq_refl _ => eq_refl x end.
Definition eq_trans {A : Type@{1}} (x y z : A) (e : (x = y)) (f : (y = z)) : (x = z) := match f with | eq_refl _ => e end.
Definition f_equal {A B : Type@{1}} (f : A -> B) (x y : A) (e : (x = y)) : ((f x) = (f y)) := match e with | eq_refl _ => eq_refl (f x) end.
Definition eq_transport (A : Set) (P : A -> Type@{1}) (x y : A) (e : (x = y)) (p : P x) : P y := match e with | eq_refl _ => p end.
Definition fst (A B : Set) (p : prod A B) : A := match p with | pair _ _ a b => a end.
Definition snd (A B : Set) (p : prod A B) : B := match p with | pair _ _ a b => b end.
Definition prod_map (A B C D : Set) (f : A -> C) (g : B -> D) (p : prod A B) : prod C D := pair C D (f (fst A B p)) (g (snd A B p)).
Definition prod_swap (A B : Set) (p : prod A B) : prod B A := pair B A (snd A B p) (fst A B p).
Definition curry (A B C : Set) (f : prod A B -> C) (a : A) (b : B) : C := f (pair A B a b).
Definition uncurry (A B C : Set) (f : A -> B -> C) (p : prod A B) : C := f (fst A B p) (snd A B p).
Definition sum_elim (A B C : Set) (f : A -> C) (g : B -> C) (s : sum A B) : C := match s with | inl _ _ a => f a | inr _ _ b => g b end.
Definition sum_map (A B C D : Set) (f : A -> C) (g : B -> D) (s : sum A B) : sum C D := sum_elim A B (sum C D) (fun a => inl C D (f a)) (fun b => inr C D (g b)) s.
Definition option_map (A B : Set) (f : A -> B) (o : option A) : option B := match o with | None _ => None B | Some _ a => Some B (f a) end.
Definition option_default (A : Set) (a : A) (o : option A) : A := match o with | None _ => a | Some _ x => x end.
Definition option_bind (A B : Set) (o : option A) (f : A -> option B) : option B := match o with | None _ => None B | Some _ x => f x end.
Theorem truth : True := I.
Theorem implication_refl : forall A : Prop, A -> A := fun A a => a.
Theorem and_comm : forall A B : Prop, and A B -> and B A := fun A B h => conj B A (and_right A B h) (and_left A B h).
Theorem and_assoc : forall A B C : Prop, and A (and B C) -> and (and A B) C := fun A B C h => conj (and A B) C (conj A B (and_left A (and B C) h) (and_left B C (and_right A (and B C) h))) (and_right B C (and_right A (and B C) h)).
Theorem and_unassoc : forall A B C : Prop, and (and A B) C -> and A (and B C) := fun A B C h => conj A (and B C) (and_left A B (and_left (and A B) C h)) (conj B C (and_right A B (and_left (and A B) C h)) (and_right (and A B) C h)).
Theorem and_idempotent : forall A : Prop, A -> and A A := fun A a => conj A A a a.
Theorem or_comm : forall A B : Prop, or A B -> or B A := fun A B h => or_elim A B (or B A) (fun a => or_intror B A a) (fun b => or_introl B A b) h.
Theorem or_idempotent : forall A : Prop, or A A -> A := fun A h => or_elim A A A (fun a => a) (fun a => a) h.
Theorem iff_refl : forall A : Prop, iff A A := fun A => conj (A -> A) (A -> A) (fun a => a) (fun a => a).
Theorem iff_sym : forall A B : Prop, iff A B -> iff B A := fun A B h => conj (B -> A) (A -> B) (and_right (A -> B) (B -> A) h) (and_left (A -> B) (B -> A) h).
Theorem iff_trans : forall A B C : Prop, iff A B -> iff B C -> iff A C := fun A B C f g => conj (A -> C) (C -> A) (fun a => and_left (B -> C) (C -> B) g (and_left (A -> B) (B -> A) f a)) (fun c => and_right (A -> B) (B -> A) f (and_right (B -> C) (C -> B) g c)).
Theorem not_false : not False := fun f => f.
Theorem not_true_false : not True -> False := fun h => h I.
Theorem contradiction : forall A : Prop, A -> not A -> False := fun A a n => n a.
Theorem double_neg_intro : forall A : Prop, A -> not (not A) := fun A a n => n a.
Theorem contraposition : forall A B : Prop, (A -> B) -> not B -> not A := fun A B f n a => n (f a).
Theorem not_or : forall A B : Prop, not (or A B) -> and (not A) (not B) := fun A B n => conj (not A) (not B) (fun a => n (or_introl A B a)) (fun b => n (or_intror A B b)).
Theorem not_or_intro : forall A B : Prop, and (not A) (not B) -> not (or A B) := fun A B h o => or_elim A B False (and_left (not A) (not B) h) (and_right (not A) (not B) h) o.
Theorem prod_eta : forall (A B : Set) (p : prod A B), ((pair A B (fst A B p) (snd A B p)) = p) := fun A B p => match p with | pair _ _ a b => eq_refl (pair A B a b) end.
Theorem option_map_id : forall (A : Set) (o : option A), ((option_map A A (fun x => x) o) = o) := fun A o => match o with | None _ => eq_refl (None A) | Some _ a => eq_refl (Some A a) end.
